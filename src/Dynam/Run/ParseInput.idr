module Dynam.Run.ParseInput

import Dynam.Run.Config

import Data.String
import Data.List1

public export
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

public export
parsePPWidth : String -> Either String $ Config -> Config
parsePPWidth str = case parsePositive str of
    Just n  => Right {layoutOpts := Opts n}
    Nothing => Left "can't parse max width for the pretty-printer"

public export
parseTestsCount : String -> Either String $ Config -> Config
parseTestsCount str = case parsePositive str of
    Just n  => Right {testsCnt := n}
    Nothing => Left "can't parse given count of tests"

public export
parseModelFuel : String -> Either String $ Config -> Config
parseModelFuel str = case parsePositive str of
    Just n  => Right {modelFuel := limit n}
    Nothing => Left "can't parse given model fuel"

public export
parsePPFuel : String -> Either String $ Config -> Config
parsePPFuel str = case parsePositive str of
    Just n  => Right {ppFuel := limit n}
    Nothing => Left "can't parse given pretty-printer fuel"

public export
parseShowProc : Config -> Config
parseShowProc cfg = MkConfig {
      usedSeed   = cfg.usedSeed
    , layoutOpts = cfg.layoutOpts
    , testsCnt   = cfg.testsCnt
    , modelFuel  = cfg.modelFuel
    , ppFuel     = cfg.ppFuel
    , showProc   = True
    , multi      = cfg.multi
}

public export
parseMulti : Config -> Config
parseMulti cfg = MkConfig {
      usedSeed   = cfg.usedSeed
    , layoutOpts = cfg.layoutOpts
    , testsCnt   = cfg.testsCnt
    , modelFuel  = cfg.modelFuel
    , ppFuel     = cfg.ppFuel
    , showProc   = cfg.showProc
    , multi      = True
}


