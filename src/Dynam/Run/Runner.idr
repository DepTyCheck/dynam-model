module Dynam.Run.Runner

import Data.Fuel
import Data.List.Lazy
import Data.List1
import Data.SortedMap
import Data.String

import Dynam.Run.ExprDerive
import Dynam.Run.NameDerive
import Dynam.Run.StmtsDerive
import Dynam.Run.StdConfig
import Dynam.Run.Labels

import Dynam.Model.Main
import Dynam.Model.Primitives
import Dynam.Pretty.Pretty
import Dynam.Pretty.Utils

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage
-- import Test.DepTyCheck.Gen.Labels
import Text.PrettyPrint.Bernardy
import Data.Functor.TraverseSt

import System
import System.File
import System.Clock
import System.GetOpts
import System.Random.Pure.StdGen

import Control.Monad.Either
import Control.Monad.Random
import Control.Monad.Maybe

%default total

%hide Text.PrettyPrint.Bernardy.Core.Doc.(>>=)

-------------------
--- CLI options ---
-------------------

record Config where
  constructor MkConfig
  usedSeed : IO StdGen
  layoutOpts : LayoutOpts
  testsCnt   : Nat
  modelFuel  : Fuel
  ppFuel     : Fuel

defaultConfig : Config
defaultConfig = MkConfig
  { usedSeed = initSeed
  , layoutOpts = Opts 152
  , testsCnt   = 10
  , modelFuel  = limit 8
  , ppFuel     = limit 1000000
  }

parseSeed : String -> Either String $ Config -> Config
parseSeed str = do
  let n1:::n2::[] = trim <$> split (== ',') str
    | _ => Left "we expect two numbers divided by a comma"
  let Just n1 = parsePositive n1
    | Nothing => Left "expected a positive number at the first component, given `\{n1}`"
  let Just n2 = parsePositive {a=Bits64} n2
    | Nothing => Left "expected a positive number at the second component, given `\{n2}`"
  let Yes prf = decSo $ testBit n2 0
    | No _ => Left "second component must be odd"
  Right {usedSeed := pure $ rawStdGen n1 n2}

parsePPWidth : String -> Either String $ Config -> Config
parsePPWidth str = case parsePositive str of
  Just n  => Right {layoutOpts := Opts n}
  Nothing => Left "can't parse max width for the pretty-printer"

parseTestsCount : String -> Either String $ Config -> Config
parseTestsCount str = case parsePositive str of
  Just n  => Right {testsCnt := n}
  Nothing => Left "can't parse given count of tests"

parseModelFuel : String -> Either String $ Config -> Config
parseModelFuel str = case parsePositive str of
  Just n  => Right {modelFuel := limit n}
  Nothing => Left "can't parse given model fuel"

parsePPFuel : String -> Either String $ Config -> Config
parsePPFuel str = case parsePositive str of
  Just n  => Right {ppFuel := limit n}
  Nothing => Left "can't parse given pretty-printer fuel"

cliOpts : List $ OptDescr $ Config -> Config
cliOpts =
 [ MkOpt [] ["seed"]
     (ReqArg' parseSeed "<seed>,<gamma>")
     "Sets particular random seed to start with."
 , MkOpt ['w'] ["pp-width"]
     (ReqArg' parsePPWidth "<nat>")
     "Sets the max length for the pretty-printer."
 , MkOpt ['n'] ["tests-count"]
     (ReqArg' parseTestsCount "<tests-count>")
     "Sets the count of tests to generate."
 , MkOpt [] ["model-fuel"]
     (ReqArg' parseModelFuel "<fuel>")
    "Sets how much fuel there is for generation of the model."
 , MkOpt [] ["pp-fuel"]
     (ReqArg' parsePPFuel "<fuel>")
     "Sets how much fuel there is for pretty-printing."
 ]

---------------
--- Startup ---
---------------
public export
data SupportedLanguage = Groovy

public export
0 PP : SupportedLanguage -> Type
PP language = {casts : _} -> {funs : _} -> {vars : _} -> {opts : _} ->
              (names : UniqNames funs vars) =>
              Fuel ->
              Stmts casts funs vars -> Gen0 $ Doc opts

supportedLanguages : SortedMap String (l : SupportedLanguage ** (NamedCtxt, PP l))
supportedLanguages = fromList
  [ ("groovy", (Groovy ** (stdLib, printGroovy)))
  ]

forS_ : Monad f => (seed : s) -> LazyList a -> (s -> a -> f s) -> f ()
forS_ seed []      g = pure ()
forS_ seed (x::xs) g = forS_ !(g seed x) xs g

printLabels : HasIO io => Config -> NamedCtxt -> io ()
printLabels cfg ctx = do
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
                let codeGen = printGroovy @{ctx.fvNames} cfg.ppFuel code <&> render cfg.layoutOpts
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

    forS_ cgi (withIndex $ unGenTryND cnt randGen gen) $ \cgi, (ind, mcov, test) => do
        writeFile (testFile ind) test >>= either (throwError . show) pure

        let cgi = registerCoverage mcov cgi 
        writeFile covFile (show @{Colourful} cgi) >>= either (throwError . show) pure
    
        putStrLn "Run #\{show ind}"

        pure cgi


---------------
--- Running ---
---------------
run : HasIO io =>
      MonadError String io =>
      Config ->
      NamedCtxt ->
      io ()
run conf ctxt = do
    -- let vals = genStmts conf.modelFuel ctxt.typecasts ctxt.functions ctxt.variables >>=
    --                  printGroovy @{ctxt.fvNames} conf.ppFuel <&> render conf.layoutOpts
                    
    -- saveTestsAndCov conf (initCoverageInfo genStmts) vals

    printLabels conf ctxt


export
main : IO ()
main = do
  args <- getArgs
  let usage : Lazy String := usageInfo "Usage: \{fromMaybe "pil-fun" $ head' args} [options] <language>" cliOpts
  let MkResult options nonOptions [] [] = getOpt Permute cliOpts $ drop 1 args
    | MkResult {unrecognized=unrecOpts@(_::_), _} => if "help" `elem` unrecOpts
                                                      then putStrLn usage
                                                      else die "unrecodnised options \{show unrecOpts}\n\{usage}"
    | MkResult {errors=es@(_::_), _}              => die "arguments parse errors \{show es}\n\{usage}"
  let [lang] = nonOptions
    | []   => die "no language is given, supported languages: groovy\n\{usage}"
    | many => die "too many languages are given\n\{usage}"
  let Just (_ ** (ctxt, pp)) = lookup lang supportedLanguages
    | Nothing => die "unknown language \{lang}, supported languages groovy\n\{usage}"

  let config = foldl (flip apply) defaultConfig options

  runEitherT {m=IO} (run config ctxt) >>= either (die . (++) "Error: ") pure
