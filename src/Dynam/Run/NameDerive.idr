module Dynam.Run.NameDerive

import public Dynam.Model.Main
import Dynam.Pretty.Pretty
import Dynam.Pretty.Utils
import Dynam.Model.Primitives

import Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 5

Dynam.Pretty.Pretty.rawNewName = deriveGen
