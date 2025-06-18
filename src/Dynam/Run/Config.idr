module Dynam.Run.Config

import public Data.Fuel

import public System.Random.Pure.StdGen
import public Text.PrettyPrint.Bernardy

public export
record Config where
    constructor MkConfig
    usedSeed : IO StdGen
    layoutOpts : LayoutOpts
    testsCnt   : Nat
    modelFuel  : Fuel
    ppFuel     : Fuel
    showProc   : Bool
    multi      : Bool

public export
defaultConfig : Config
defaultConfig = MkConfig {
      usedSeed   = initSeed
    , layoutOpts = Opts 152
    , testsCnt   = 10
    , modelFuel  = limit 8
    , ppFuel     = limit 1000000
    , showProc   = False
    , multi      = False
}
