module Dynam.Run.StmtsDerive

import public Dynam.Model.Main
import Dynam.Model.Primitives

import Deriving.DepTyCheck.Gen
import Dynam.Run.CastGens
import Data.Fuel


%default total

%logging "deptycheck.derive" 15
%logging "deptycheck.derive.clojuring" 20

Dynam.Model.Main.genStmts' = deriveGen
