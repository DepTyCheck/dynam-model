module Dynam.Run.StmtsDerive

import public Dynam.Model.Stmts
import Dynam.Model.Primitives

import Deriving.DepTyCheck.Gen
-- import Dynam.Run.CastGens
import Data.Fuel


%default total

%logging "deptycheck.derive" 15
%logging "deptycheck.derive.closuring" 20

Dynam.Model.Stmts.genStmts = deriveGen
