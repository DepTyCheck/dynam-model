module Js.Playground.Usage.Example

import public Js.Playground.Js
import Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 5

Js.Playground.Js.genStmts = deriveGen
