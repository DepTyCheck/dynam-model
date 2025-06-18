module Dynam.Run.Derive.BaseDerive

import public Dynam.Model.Base

import Deriving.DepTyCheck.Gen
import Data.Fuel


%default total

%logging "deptycheck.derive" 15
%logging "deptycheck.derive.closuring" 20

Dynam.Model.Base.Stmts.genStmts = deriveGen
