module Dynam.Run.Print

import Deriving.DepTyCheck.Gen
import Dynam.Model.Primitives
import Dynam.Model.Exprs

%default total

%language ElabReflection


%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel ->
          (casts : ListOfSupportedCasts) ->
          (funs  : ListOfFunctions) ->
          (vars  : ListOfBasicTypes) ->
          (resTy : BasicType False) ->
          Gen MaybeEmpty (Expr casts funs vars resTy)
