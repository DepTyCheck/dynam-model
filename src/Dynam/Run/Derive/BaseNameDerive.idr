module Dynam.Run.Derive.BaseNameDerive

import public Dynam.Model.Base
import public Dynam.Pretty.Base

import Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 15
%logging "deptycheck.derive.closuring" 20

Dynam.Pretty.Base.Global.rawNewName = deriveGen
