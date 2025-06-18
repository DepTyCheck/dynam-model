module Dynam.Run.Derive.StmtsDerive

import public Dynam.Model.Stmts

import Deriving.DepTyCheck.Gen
import Data.Fuel


%default total

%logging "deptycheck.derive" 15
%logging "deptycheck.derive.closuring" 20

Dynam.Model.Stmts.genStmts = deriveGen
