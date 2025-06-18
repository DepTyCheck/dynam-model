module Dynam.Run.Derive.NameDerive

import public Dynam.Model.Base
import Dynam.Pretty.All
import Dynam.Pretty.Utils

import Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 5

Dynam.Pretty.Global.rawNewName = deriveGen
