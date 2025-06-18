module Dynam.Run.Runner

import Dynam.Run.All

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage

import Data.List.Lazy
import Data.Functor.TraverseSt

import System
import System.File
import System.Clock
import System.GetOpts

import Control.Monad.Maybe
import Control.Monad.Either
import Control.Monad.Random

%default total
%hide Text.PrettyPrint.Bernardy.Core.Doc.(>>=)


cliOpts : List $ OptDescr $ Config -> Config
cliOpts = [
      MkOpt [] ["seed"]
        (ReqArg' parseSeed "<seed>,<gamma>")
        "Sets particular random seed to start with."
    , MkOpt ['w'] ["pp-width"]
        (ReqArg' parsePPWidth "<nat>")
        "Sets the max length for the pretty-printer."
    , MkOpt ['n'] ["tests-count"]
        (ReqArg' parseTestsCount "<tests-count>")
        "Sets the count of tests to generate."
    , MkOpt ['f'] ["model-fuel"]
        (ReqArg' parseModelFuel "<fuel>")
        "Sets how much fuel there is for generation of the model."
    , MkOpt [] ["pp-fuel"]
        (ReqArg' parsePPFuel "<fuel>")
        "Sets how much fuel there is for pretty-printing."
    , MkOpt ['p'] ["process"]
        (NoArg parseShowProc)
        "Shows generation process."
    , MkOpt ['m'] ["multi"]
        (NoArg parseMulti)
        "Generate all languages at once."
]


forSeed : Monad f => (seed : s) -> LazyList a -> (s -> a -> f s) -> f ()
forSeed seed []      g = pure ()
forSeed seed (x::xs) g = forSeed !(g seed x) xs g


printLabels : HasIO io => (pp : PP) -> Config -> NamedCtxt -> io ()
printLabels pp cfg ctx = do
    let testFile = \ind : Nat => "tests\{show ind}.info"
    let cnt = cfg.testsCnt
    randGen <- liftIO cfg.usedSeed
    let vals = genStmts cfg.modelFuel ctx.typecasts ctx.functions ctx.variables

    evalRandomT randGen $ Data.List.Lazy.for_ (fromList [1..cnt]) $ \ind => do
        res <- runMaybeT $ unGen {m=MaybeT (RandomT io)} {labels=PrintAllLabels} vals

        putStrLn "Model is built"
        putStrLn "************************"
        case res of
            Just code => do
                putStrLn "Pretty printer is running.."
                let codeGen = pp @{ctx.fvNames} cfg.ppFuel code <&> render cfg.layoutOpts
                str <- runMaybeT $ unGen {m=MaybeT (RandomT io)} {labels=PrintAllLabels} codeGen

                case str of
                    Just nonEmpty => do
                        putStrLn "Success"
                        putStrLn "************************"
                        putStrLn nonEmpty
                    Nothing => putStrLn "Fail"

            Nothing   => putStrLn "empty model"

        putStrLn "---"


saveTestsAndCov : HasIO io => MonadError String io => Config -> CoverageGenInfo g -> Gen MaybeEmpty String -> io Unit
saveTestsAndCov conf cgi gen = do
    randGen <- liftIO conf.usedSeed
    let covFile = "coverage.info"
    let testFile = \ind : Nat => "tests\{show ind}.info"
    let cnt = conf.testsCnt

    forSeed cgi (withIndex $ unGenTryND cnt randGen gen) $ \cgi, (ind, mcov, test) => do
        writeFile (testFile ind) test >>= either (throwError . show) pure

        let cgi = registerCoverage mcov cgi 
        writeFile covFile (show @{Colourful} cgi) >>= either (throwError . show) pure
    
        putStrLn "Done #\{show ind}"

        pure cgi

saveMultiCode : HasIO io => MonadError String io => Config -> 
                ((casts : _) -> (funs : _) -> (vars : _) -> Gen MaybeEmpty (Stmts casts funs vars)) -> io Unit
saveMultiCode cfg gen = do
    let testFile = \lang : String => "multi." ++ lang
    randGen <- liftIO cfg.usedSeed
    
    evalRandomT randGen $ do
        let ctx = shared
        test <- runMaybeT $ unGen {m=MaybeT (RandomT io)} {labels=PrintAllLabels} $ gen ctx.typecasts ctx.functions ctx.variables
    
        putStrLn "Model is built"
        putStrLn "************************"


        Data.List.Lazy.for_ (fromList $ kvList supportedLanguagesShared) $ \(lang, _, pp) => do
            putStrLn "Printing multi.\{ lang }"

            case test of
                Just code => do
                    putStrLn "Pretty printer is running.."
                    let codeGen = pp @{ctx.fvNames} cfg.ppFuel code <&> render cfg.layoutOpts
                    str <- runMaybeT $ unGen {m=MaybeT (RandomT io)} codeGen

                    case str of
                        Just nonEmpty => do
                            putStrLn "Success"
                            putStrLn "************************"
                            writeFile (testFile lang) nonEmpty >>= either (throwError . show) pure
                        Nothing => putStrLn "Fail"

                Nothing => putStrLn "empty model"

            putStrLn "---"

---------------
--- Running ---
---------------
run : HasIO io =>
      MonadError String io =>
      (pp : PP) ->
      Config ->
      NamedCtxt ->
      io ()
run pp conf ctxt = do
    case (conf.multi, conf.showProc) of
        (True, _) => do
            putStrLn "Got M"
            saveMultiCode conf (genStmts conf.modelFuel)

        (_, True) => printLabels pp conf ctxt
        (_, False) => do
            let vals = genStmts conf.modelFuel ctxt.typecasts ctxt.functions ctxt.variables >>=
                            pp @{ctxt.fvNames} conf.ppFuel <&> render conf.layoutOpts
                            
            saveTestsAndCov conf (initCoverageInfo Dynam.Model.Base.Stmts.genStmts) vals


export
main : IO ()
main = do
    args <- getArgs
    let usage : Lazy String := usageInfo "Usage: \{fromMaybe "pil-fun" $ head' args} [options] <language>" cliOpts
    let langs : Lazy String := joinBy ", " $ Prelude.toList $ keySet supportedLanguages

    let MkResult options nonOptions [] [] = getOpt Permute cliOpts $ drop 1 args
        | MkResult {unrecognized=unrecOpts@(_::_), _} => if "help" `elem` unrecOpts
                                                        then putStrLn usage
                                                        else die "unrecodnised options \{show unrecOpts}\n\{usage}"
        | MkResult {errors=es@(_::_), _}              => die "arguments parse errors \{show es}\n\{usage}"
    let [lang] = nonOptions
        | []   => die "no language is given, supported languages: \{langs}\n\{usage}"
        | many => die "too many languages are given\n\{usage}"
    let Just (ctxt, pp) = lookup lang supportedLanguages
        | Nothing => die "unknown language '\{lang}', supported languages: \{langs}\n\{usage}"

    let config = foldl (flip apply) defaultConfig options

    runEitherT {m=IO} (run pp config ctxt) >>= either (die . (++) "Error: ") pure
