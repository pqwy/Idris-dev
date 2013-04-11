{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor,
             PatternGuards #-}

module Idris.REPL where

import Idris.AbsSyntax
import Idris.REPLParser
import Idris.ElabDecls
import Idris.ElabTerm
import Idris.Error
import Idris.Delaborate
import Idris.Compiler
import Idris.Prover
import Idris.Parser
import Idris.Primitives
import Idris.Coverage
import Idris.UnusedArgs
import Idris.Docs
import Idris.Help
import Idris.Completion
import Idris.IdeSlave

import Paths_idris
import Util.System
import Util.DynamicLinker

import Core.Evaluate
import Core.Execute (execute)
import Core.ProofShell
import Core.TT
import Core.Constraints

import IRTS.Compiler
import IRTS.LParser
import IRTS.CodegenCommon

-- import RTS.SC
-- import RTS.Bytecode
-- import RTS.PreC
-- import RTS.CodegenC

import System.Console.Haskeline as H
import System.FilePath
import System.Exit
import System.Environment
import System.Process
import System.Directory
import System.IO
import Control.Monad
import Control.Monad.Trans.State.Strict ( StateT, execStateT, get, put )
import Control.Monad.Trans ( liftIO, lift )
import Data.Maybe
import Data.List
import Data.Char
import Data.Version

import Debug.Trace

-- | Run the REPL
repl :: IState -- ^ The initial state
     -> [FilePath] -- ^ The loaded modules
     -> InputT Idris ()
repl orig mods
   = H.catch
      (do let quiet = opt_quiet (idris_options orig)
          let prompt = if quiet
                          then ""
                          else mkPrompt mods ++ "> "
          x <- getInputLine prompt
          case x of
              Nothing -> do lift $ when (not quiet) (iputStrLn "Bye bye")
                            return ()
              Just input -> H.catch 
                              (do ms <- lift $ processInput input orig mods
                                  case ms of
                                      Just mods -> repl orig mods
                                      Nothing -> return ())
                              ctrlC)
      ctrlC
   where ctrlC :: SomeException -> InputT Idris ()
         ctrlC e = do lift $ iputStrLn (show e)
                      repl orig mods

-- | Run the IdeSlave
ideslave :: IState -> [FilePath] -> Idris ()
ideslave orig mods
  = do idrisCatch (do x <- liftIO $ receiveMessage
                      case x of
                           Nothing -> do liftIO $ sendMessage (Just "did not understand")
                           Just (Interpret cmd) -> do i <- getIState
                                                      let fn = case mods of
                                                                    (f:_) -> f
                                                                    _ -> ""
                                                      case parseCmd i cmd of
                                                           Left err -> do liftIO $ sendMessage (show err)
                                                           Right cmd -> do idrisCatch (do xs <- process fn cmd
                                                                                          liftIO $ sendMessage xs)
                                                                                      (\e -> do liftIO $ sendMessage (show e))
                           Just y -> do liftIO $ sendMessage (Just "understood you!")
                      liftIO $ sendMessage (Just "Hello world"))
                   (\e -> do liftIO $ sendMessage (show e))
       ideslave orig mods

-- | The prompt consists of the currently loaded modules, or "Idris" if there are none
mkPrompt [] = "Idris"
mkPrompt [x] = "*" ++ dropExtension x
mkPrompt (x:xs) = "*" ++ dropExtension x ++ " " ++ mkPrompt xs

-- | Determine whether a file uses literate syntax
lit f = case splitExtension f of
            (_, ".lidr") -> True
            _ -> False

processInput :: String -> IState -> [FilePath] -> Idris (Maybe [FilePath])
processInput cmd orig inputs
    = do i <- getIState
         let opts = idris_options i
         let quiet = opt_quiet opts
         let fn = case inputs of
                        (f:_) -> f
                        _ -> ""
         case parseCmd i cmd of
            Left err ->   do liftIO $ print err
                             return (Just inputs)
            Right Reload -> 
                do putIState (orig { idris_options = idris_options i })
                   clearErr
                   mods <- mapM loadModule inputs  
                   return (Just inputs)
            Right (Load f) -> 
                do putIState (orig { idris_options = idris_options i })
                   clearErr
                   mod <- loadModule f
                   return (Just [f])
            Right (ModImport f) -> 
                do clearErr
                   fmod <- loadModule f
                   return (Just (inputs ++ [fmod]))
            Right Edit -> do edit fn orig
                             return (Just inputs)
            Right Proofs -> do proofs orig
                               return (Just inputs)
            Right Quit -> do when (not quiet) (iputStrLn "Bye bye")
                             return Nothing
            Right cmd  -> do idrisCatch (do xs <- process fn cmd
                                            mapM_ iputStrLn xs)
                                        (\e -> iputStrLn (show e))
                             return (Just inputs)

resolveProof :: Name -> Idris Name
resolveProof n'
  = do i <- getIState
       ctxt <- getContext
       n <- case lookupNames n' ctxt of
                 [x] -> return x
                 [] -> return n'
                 ns -> fail $ pshow i (CantResolveAlts (map show ns))
       return n

removeProof :: Name -> Idris ()
removeProof n =
  do i <- getIState
     let proofs = proof_list i
     let ps = filter ((/= n) . fst) proofs
     putIState $ i { proof_list = ps }

edit :: FilePath -> IState -> Idris ()
edit "" orig = iputStrLn "Nothing to edit"
edit f orig
    = do i <- getIState
         env <- liftIO $ getEnvironment
         let editor = getEditor env
         let line = case errLine i of
                        Just l -> " +" ++ show l ++ " "
                        Nothing -> " "
         let cmd = editor ++ line ++ f
         liftIO $ system cmd
         clearErr
         putIState (orig { idris_options = idris_options i })
         loadModule f
         iucheck
         return ()
   where getEditor env | Just ed <- lookup "EDITOR" env = ed
                       | Just ed <- lookup "VISUAL" env = ed
                       | otherwise = "vi"


proofs :: IState -> Idris ()
proofs orig
  = do i <- getIState
       let ps = proof_list i
       case ps of
            [] -> iputStrLn "No proofs available"
            _  -> iputStrLn $ "Proofs:\n\t" ++ (show $ map fst ps)

insertScript :: String -> [String] -> [String]
insertScript prf [] = "\n---------- Proofs ----------" : "" : [prf]
insertScript prf (p@"---------- Proofs ----------" : "" : xs)
    = p : "" : prf : xs
insertScript prf (x : xs) = x : insertScript prf xs

process :: FilePath -> Command -> Idris ([String])
process fn Help = return [displayHelp]
process fn (ChangeDirectory f)
                 = do liftIO $ setCurrentDirectory f
                      return ([])
process fn (Eval t)
                 = do (tm, ty) <- elabVal toplevel False t
                      ctxt <- getContext
                      ist <- getIState
                      let tm' = normaliseAll ctxt [] tm
                      let ty' = normaliseAll ctxt [] ty
                      logLvl 3 $ "Raw: " ++ show (tm', ty')
                      imp <- impShow
                      return [showImp imp (delab ist tm') ++ " : " ++
                              showImp imp (delab ist ty')]
process fn (ExecVal t)
                  = do ctxt <- getContext
                       ist <- getIState
                       (tm, ty) <- elabVal toplevel False t
--                       let tm' = normaliseAll ctxt [] tm
                       let ty' = normaliseAll ctxt [] ty
                       res <- execute tm
                       imp <- impShow
                       return [showImp imp (delab ist res) ++ " : " ++
                               showImp imp (delab ist ty')]
process fn (Check (PRef _ n))
   = do ctxt <- getContext
        ist <- getIState
        imp <- impShow
        case lookupNames n ctxt of
             ts@(_:_) -> return (map (\t -> show n ++ " : " ++
                                            showImp imp (delabTy ist t)) ts)
             [] -> return ["No such variable " ++ show n]
process fn (Check t) = do (tm, ty) <- elabVal toplevel False t
                          ctxt <- getContext
                          ist <- getIState
                          imp <- impShow
                          let ty' = normaliseC ctxt [] ty
                          return [showImp imp (delab ist tm) ++ " : " ++
                                  showImp imp (delab ist ty)]

process fn (DocStr n) = do i <- getIState
                           case lookupCtxtName n (idris_docstrings i) of
                                [] -> return ["No documentation for " ++ show n]
                                ns -> do docs <- mapM showDoc ns; return docs
    where showDoc (n, d)
             = do doc <- getDocs n
                  return (show doc)
process fn Universes = do i <- getIState
                          let cs = idris_constraints i
--                        iputStrLn $ showSep "\n" (map show cs)
                          let cs' = show (map fst cs)
                          let n = length cs
                          let out = [cs', "(" ++ show n ++ " constraints)"]
                          case ucheck cs of
                            Error e -> return (out ++ [pshow i e])
                            OK _ -> return (out ++ ["Universes OK"])

process fn (Defn n) = do i <- getIState
                         let pre = "Compiled patterns:\n"
                         let out = [pre, show (lookupDef n (tt_ctxt i))]
                         out' <-
                           case lookupCtxt n (idris_patdefs i) of
                             [] -> return out
                             [d] -> return (out ++ ["Original definiton:\n"] ++ (map (printCase i) d))
                         case lookupTotal n (tt_ctxt i) of
                            [t] -> return (out' ++ [showTotal t i])
                            _ -> return (out')
    where printCase i (_, lhs, rhs)
             = showImp True (delab i lhs) ++ " = " ++ showImp True (delab i rhs)

process fn (TotCheck n) = do i <- getIState
                             case lookupTotal n (tt_ctxt i) of
                                [t] -> return ([showTotal t i])
                                _ -> return ([])
process fn (DebugInfo n)
   = do i <- getIState
        let oi = lookupCtxtName n (idris_optimisation i)
        let ois = if (null oi) then [] else [show oi]
        let si = lookupCtxt n (idris_statics i)
        let sis = if (null si) then [] else [show si]
        let di = lookupCtxt n (idris_datatypes i)
        let dis = if (null di) then [] else [show di]
        let d = lookupDef n (tt_ctxt i)
        let ds = if (null d) then [] else [show (head d)]
        let cg = lookupCtxtName n (idris_callgraph i)
        findUnusedArgs (map fst cg)
        i <- getIState
        let cg' = lookupCtxtName n (idris_callgraph i)
        sc <- checkSizeChange n
        let scs = ["Size change: " ++ show sc]
        let cgs = if (null cg') then [] else ["Call graph:", show cg']
        return (ois ++ sis ++ dis ++ ds ++ scs ++ cgs)
process fn (Info n) = do i <- getIState
                         case lookupCtxt n (idris_classes i) of
                              [c] -> do cs <- classInfo c; return cs
                              _ -> return ["Not a class"]
process fn (Search t) = return ["Not implemented"]
process fn (Spec t) = do (tm, ty) <- elabVal toplevel False t
                         ctxt <- getContext
                         ist <- getIState
                         let tm' = simplify ctxt True [] {- (idris_statics ist) -} tm
                         return [(show (delab ist tm'))]

process fn (RmProof n')
  = do i <- getIState
       n <- resolveProof n'
       let proofs = proof_list i
       case lookup n proofs of
            Nothing -> return ["No proof to remove"]
            Just _  -> do removeProof n
                          insertMetavar n
                          return ["Removed proof " ++ show n]
                          where
                            insertMetavar :: Name -> Idris ()
                            insertMetavar n =
                              do i <- getIState
                                 let ms = idris_metavars i
                                 putIState $ i { idris_metavars = n : ms }

process fn' (AddProof prf)
  = do fn <- do
         ex <- liftIO $ doesFileExist fn'
         let fnExt = fn' <.> "idr"
         exExt <- liftIO $ doesFileExist fnExt
         if ex
            then return fn'
            else if exExt
                    then return fnExt
                    else fail $ "Neither \""++fn'++"\" nor \""++fnExt++"\" exist"
       let fb = fn ++ "~"
       liftIO $ copyFile fn fb -- make a backup in case something goes wrong!
       prog <- liftIO $ readFile fb
       i <- getIState
       let proofs = proof_list i
       n' <- case prf of
                Nothing -> case proofs of
                             [] -> fail "No proof to add"
                             ((x, p) : _) -> return x
                Just nm -> return nm
       n <- resolveProof n'
       case lookup n proofs of
            Nothing -> return ["No proof to add"]
            Just p  -> do let prog' = insertScript (showProof (lit fn) n p) ls
                          liftIO $ writeFile fn (unlines prog')
                          removeProof n
                          return ["Added proof " ++ show n]
                          where ls = (lines prog)

process fn (ShowProof n')
  = do i <- getIState
       n <- resolveProof n'
       let proofs = proof_list i
       case lookup n proofs of
            Nothing -> return ["No proof to show"]
            Just p  -> return [showProof False n p]

process fn (Prove n')
     = do ctxt <- getContext
          ist <- getIState
          n <- case lookupNames n' ctxt of
                    [x] -> return x
                    [] -> return n'
                    ns -> fail $ pshow ist (CantResolveAlts (map show ns))
          prover (lit fn) n
          -- recheck totality
          i <- getIState
          totcheck (FC "(input)" 0, n)
          mapM_ (\ (f,n) -> setTotality n Unchecked) (idris_totcheck i)
          mapM_ checkDeclTotality (idris_totcheck i)
          return []

process fn (HNF t)  = do (tm, ty) <- elabVal toplevel False t
                         ctxt <- getContext
                         ist <- getIState
                         let tm' = hnf ctxt [] tm
                         return [show (delab ist tm')]
process fn TTShell  = do ist <- getIState
                         let shst = initState (tt_ctxt ist)
                         runShell shst
                         return []
process fn Execute = do (m, _) <- elabVal toplevel False 
                                        (PApp fc 
                                           (PRef fc (UN "run__IO"))
                                           [pexp $ PRef fc (NS (UN "main") ["Main"])])
--                                      (PRef (FC "main" 0) (NS (UN "main") ["main"]))
                        (tmpn, tmph) <- liftIO tempfile
                        liftIO $ hClose tmph
                        t <- target
                        compile t tmpn m
                        liftIO $ system tmpn
                        return []
  where fc = FC "main" 0
process fn (NewCompile f)
     = do (m, _) <- elabVal toplevel False
                      (PApp fc (PRef fc (UN "run__IO"))
                          [pexp $ PRef fc (NS (UN "main") ["Main"])])
          compileEpic f m
          return []
  where fc = FC "main" 0
process fn (Compile target f)
      = do (m, _) <- elabVal toplevel False
                       (PApp fc (PRef fc (UN "run__IO"))
                       [pexp $ PRef fc (NS (UN "main") ["Main"])])
           compile target f m
           return []
  where fc = FC "main" 0
process fn (LogLvl i) = do setLogLevel i; return []
-- Elaborate as if LHS of a pattern (debug command)
process fn (Pattelab t)
     = do (tm, ty) <- elabVal toplevel True t
          return [show tm ++ "\n\n : " ++ show ty]

process fn (Missing n) = do i <- getIState
                            case lookupDef n (tt_ctxt i) of
                                [CaseOp _ _ _ _ _ args t _ _]
                                    -> do tms <- genMissing n args t
                                          return (map (showImp True) tms)
                                [] -> return [show n ++ " undefined"]
                                _ -> return ["Ambiguous name"]
process fn (DynamicLink l) = do i <- getIState
                                let lib = trim l
                                handle <- lift $ tryLoadLib lib
                                case handle of
                                  Nothing -> return ["Could not load dynamic lib \"" ++ l ++ "\""]
                                  Just x -> do let libs = idris_dynamic_libs i
                                               putIState $ i { idris_dynamic_libs = x:libs }
                                               return []
    where trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace
process fn ListDynamic = do i <- getIState
                            return ("Dynamic libraries:" : showLibs (idris_dynamic_libs i))
    where showLibs []                = []
          showLibs ((Lib name _):ls) = ("\t" ++ name) : showLibs ls
process fn Metavars
                 = do ist <- getIState
                      let mvs = idris_metavars ist \\ primDefs
                      case mvs of
                        [] -> return ["No global metavariables to solve"]
                        _ -> return ["Global metavariables:\n\t" ++ show mvs]

process fn NOP      = do return []

process fn (SetOpt   ErrContext) = do setErrContext True; return []
process fn (UnsetOpt ErrContext) = do setErrContext False; return []
process fn (SetOpt ShowImpl)     = do setImpShow True; return []
process fn (UnsetOpt ShowImpl)   = do setImpShow False; return []

process fn (SetOpt _) = do return ["Not a valid option"]
process fn (UnsetOpt _) = do return ["Not a valid option"]

classInfo :: ClassInfo -> Idris ([String])
classInfo ci = do let out = "Methods:\n" : (map dumpMethod (class_methods ci)) ++ ["", "Instances:\n"]
                  ins <- mapM dumpInstance (class_instances ci)
                  return (out ++ (concat ins))

dumpMethod :: (Name, (FnOpts, PTerm)) -> String
dumpMethod (n, (_, t)) = show n ++ " : " ++ show t

dumpInstance :: Name -> Idris ([String])
dumpInstance n = do i <- getIState
                    ctxt <- getContext
                    imp <- impShow
                    case lookupTy n ctxt of
                         ts -> return (mapM (\t -> showImp imp (delab i t)) ts)

showTotal t@(Partial (Other ns)) i
   = show t ++ "\n\t" ++ showSep "\n\t" (map (showTotalN i) ns)
showTotal t i = show t
showTotalN i n = case lookupTotal n (tt_ctxt i) of
                        [t] -> showTotal t i
                        _ -> ""

displayHelp = let vstr = showVersion version in
              "\nIdris version " ++ vstr ++ "\n" ++
              "--------------" ++ map (\x -> '-') vstr ++ "\n\n" ++
              concatMap cmdInfo helphead ++
              concatMap cmdInfo help
  where cmdInfo (cmds, args, text) = "   " ++ col 16 12 (showSep " " cmds) (show args) text 
        col c1 c2 l m r = 
            l ++ take (c1 - length l) (repeat ' ') ++ 
            m ++ take (c2 - length m) (repeat ' ') ++ r ++ "\n"

parseTarget :: String -> Target
parseTarget "C" = ViaC
parseTarget "Java" = ViaJava
parseTarget "bytecode" = Bytecode
parseTarget "javascript" = ViaJavaScript
parseTarget "node" = ViaNode
parseTarget _ = error "unknown target" -- FIXME: partial function

parseArgs :: [String] -> [Opt]
parseArgs [] = []
parseArgs ("--quiet":ns)         = Quiet : (parseArgs ns)
parseArgs ("--ideslave":ns)      = IdeSlave : (parseArgs ns)
parseArgs ("--log":lvl:ns)       = OLogging (read lvl) : (parseArgs ns)
parseArgs ("--noprelude":ns)     = NoPrelude : (parseArgs ns)
parseArgs ("--check":ns)         = NoREPL : (parseArgs ns)
parseArgs ("-o":n:ns)            = NoREPL : Output n : (parseArgs ns)
parseArgs ("-no":n:ns)           = NoREPL : NewOutput n : (parseArgs ns)
parseArgs ("--typecase":ns)      = TypeCase : (parseArgs ns)
parseArgs ("--typeintype":ns)    = TypeInType : (parseArgs ns)
parseArgs ("--total":ns)         = DefaultTotal : (parseArgs ns)
parseArgs ("--partial":ns)       = DefaultPartial : (parseArgs ns)
parseArgs ("--warnpartial":ns)   = WarnPartial : (parseArgs ns)
parseArgs ("--nocoverage":ns)    = NoCoverage : (parseArgs ns)
parseArgs ("--errorcontext":ns)  = ErrContext : (parseArgs ns)
parseArgs ("--help":ns)          = Usage : (parseArgs ns)
parseArgs ("--link":ns)          = ShowLibs : (parseArgs ns)
parseArgs ("--libdir":ns)        = ShowLibdir : (parseArgs ns)
parseArgs ("--include":ns)       = ShowIncs : (parseArgs ns)
parseArgs ("--version":ns)       = Ver : (parseArgs ns)
parseArgs ("--verbose":ns)       = Verbose : (parseArgs ns)
parseArgs ("--ibcsubdir":n:ns)   = IBCSubDir n : (parseArgs ns)
parseArgs ("-i":n:ns)            = ImportDir n : (parseArgs ns)
parseArgs ("--warn":ns)          = WarnOnly : (parseArgs ns)
parseArgs ("--package":n:ns)     = Pkg n : (parseArgs ns)
parseArgs ("-p":n:ns)            = Pkg n : (parseArgs ns)
parseArgs ("--build":n:ns)       = PkgBuild n : (parseArgs ns)
parseArgs ("--install":n:ns)     = PkgInstall n : (parseArgs ns)
parseArgs ("--clean":n:ns)       = PkgClean n : (parseArgs ns)
parseArgs ("--bytecode":n:ns)    = NoREPL : BCAsm n : (parseArgs ns)
parseArgs ("--fovm":n:ns)        = NoREPL : FOVM n : (parseArgs ns)
parseArgs ("-S":ns)              = OutputTy Raw : (parseArgs ns)
parseArgs ("-c":ns)              = OutputTy Object : (parseArgs ns)
parseArgs ("--dumpdefuns":n:ns)  = DumpDefun n : (parseArgs ns)
parseArgs ("--dumpcases":n:ns)   = DumpCases n : (parseArgs ns)
parseArgs ("--target":n:ns)      = UseTarget (parseTarget n) : (parseArgs ns)
parseArgs ("-XTypeProviders":ns) = Extension TypeProviders : (parseArgs ns)
parseArgs (n:ns)                 = Filename n : (parseArgs ns)

helphead =
  [ (["Command"], SpecialHeaderArg, "Purpose"),
    ([""], NoArg, "")
  ]


replSettings :: Settings Idris
replSettings = setComplete replCompletion defaultSettings

-- invoke as if from command line
idris :: [Opt] -> IO IState
idris opts = execStateT (idrisMain opts) idrisInit

idrisMain :: [Opt] -> Idris ()
idrisMain opts =
    do let inputs = opt getFile opts
       let quiet = Quiet `elem` opts
       let idesl = IdeSlave `elem` opts
       let runrepl = not (NoREPL `elem` opts)
       let output = opt getOutput opts
       let newoutput = opt getNewOutput opts
       let ibcsubdir = opt getIBCSubDir opts
       let importdirs = opt getImportDir opts
       let bcs = opt getBC opts
       let vm = opt getFOVM opts
       let pkgdirs = opt getPkgDir opts
       let outty = case opt getOutputTy opts of
                     [] -> Executable
                     xs -> last xs
       let tgt = case opt getTarget opts of
                   [] -> ViaC
                   xs -> last xs
       when (DefaultTotal `elem` opts) $ do i <- getIState
                                            putIState (i { default_total = True })
       mapM_ addLangExt (opt getLanguageExt opts)
       setREPL runrepl
       setQuiet quiet
       setIdeSlave idesl
       setVerbose runrepl
       setCmdLine opts
       setOutputTy outty
       setTarget tgt
       when (Verbose `elem` opts) $ setVerbose True
       mapM_ makeOption opts
       -- if we have the --fovm flag, drop into the first order VM testing
       case vm of
         [] -> return ()
         xs -> liftIO $ mapM_ (fovm tgt outty) xs 
       -- if we have the --bytecode flag, drop into the bytecode assembler
       case bcs of
         [] -> return ()
         xs -> return () -- liftIO $ mapM_ bcAsm xs 
       case ibcsubdir of
         [] -> setIBCSubDir ""
         (d:_) -> setIBCSubDir d
       setImportDirs importdirs

       addPkgDir "base"
       mapM_ addPkgDir pkgdirs
       elabPrims
       when (not (NoPrelude `elem` opts)) $ do x <- loadModule "Prelude"
                                               return ()
       when (runrepl && not quiet && not idesl) $ iputStrLn banner
       ist <- getIState
       mods <- mapM loadModule inputs
       ok <- noErrors
       when ok $ case output of
                    [] -> return ()
                    (o:_) ->
                      do xs <- process "" (Compile tgt o)
                         mapM_ iputStrLn xs
       when ok $ case newoutput of
                    [] -> return ()
                    (o:_) ->
                      do xs <- process "" (NewCompile o)
                         mapM_ iputStrLn xs
       when (runrepl && not idesl) $ runInputT replSettings $ repl ist inputs
       when (idesl) $ ideslave ist inputs
       ok <- noErrors
       when (not ok) $ liftIO (exitWith (ExitFailure 1))
  where
    makeOption (OLogging i) = setLogLevel i
    makeOption TypeCase = setTypeCase True
    makeOption TypeInType = setTypeInType True
    makeOption NoCoverage = setCoverage False
    makeOption ErrContext = setErrContext True
    makeOption _ = return ()

    addPkgDir :: String -> Idris ()
    addPkgDir p = do ddir <- liftIO $ getDataDir 
                     addImportDir (ddir </> p)

getFile :: Opt -> Maybe String
getFile (Filename str) = Just str
getFile _ = Nothing

getBC :: Opt -> Maybe String
getBC (BCAsm str) = Just str
getBC _ = Nothing

getFOVM :: Opt -> Maybe String
getFOVM (FOVM str) = Just str
getFOVM _ = Nothing

getOutput :: Opt -> Maybe String
getOutput (Output str) = Just str
getOutput _ = Nothing

getNewOutput :: Opt -> Maybe String
getNewOutput (NewOutput str) = Just str
getNewOutput _ = Nothing

getIBCSubDir :: Opt -> Maybe String
getIBCSubDir (IBCSubDir str) = Just str
getIBCSubDir _ = Nothing

getImportDir :: Opt -> Maybe String
getImportDir (ImportDir str) = Just str
getImportDir _ = Nothing

getPkgDir :: Opt -> Maybe String
getPkgDir (Pkg str) = Just str
getPkgDir _ = Nothing

getPkg :: Opt -> Maybe (Bool, String)
getPkg (PkgBuild str) = Just (False, str)
getPkg (PkgInstall str) = Just (True, str)
getPkg _ = Nothing

getPkgClean :: Opt -> Maybe String
getPkgClean (PkgClean str) = Just str
getPkgClean _ = Nothing

getTarget :: Opt -> Maybe Target
getTarget (UseTarget x) = Just x
getTarget _ = Nothing

getOutputTy :: Opt -> Maybe OutputType
getOutputTy (OutputTy t) = Just t
getOutputTy _ = Nothing

getLanguageExt :: Opt -> Maybe LanguageExt
getLanguageExt (Extension e) = Just e
getLanguageExt _ = Nothing

opt :: (Opt -> Maybe a) -> [Opt] -> [a]
opt = mapMaybe

ver = showVersion version

banner = "     ____    __     _                                          \n" ++     
         "    /  _/___/ /____(_)____                                     \n" ++
         "    / // __  / ___/ / ___/     Version " ++ ver ++ "\n" ++
         "  _/ // /_/ / /  / (__  )      http://www.idris-lang.org/      \n" ++
         " /___/\\__,_/_/  /_/____/       Type :? for help                \n" 


