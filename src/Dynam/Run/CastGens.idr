-- module Dynam.Run.CastGens

-- import public Dynam.Model.Primitives
-- import public Dynam.Model.Exprs

-- import Deriving.DepTyCheck.Gen
-- import Data.Fuel

-- %default total

-- -- data Contains : ListOfBasicTypes -> BasicType -> Type where
-- --     Single : Contains (ty :: other) ty
-- --     Multiple : Contains tys ty -> Contains (new :: tys) ty

-- export
-- genContains : Fuel -> (tys : ListOfBasicTypes) -> (ty : BasicType False) -> Gen MaybeEmpty (Contains tys ty)
-- genContains _ Nil _ = empty
-- genContains _ (this :: other) ty = case decEq this ty of
--                                         Yes Refl => pure $ Single  {ty} {other}
--                                         No  _    => empty


-- -- data IsCastable : SupportedTypecast -> BasicType -> BasicType -> Type where
-- --     MakeCast : {from : BasicType} ->
-- --                 {tos : ListOfBasicTypes} ->
-- --                 {to : BasicType} ->
-- --                 Contains tos to -> IsCastable (from %= tos) from to


-- -- genTypes : Fuel -> BasicType -> Gen MaybeEmpty (ListOfBasicTypes)

-- -- help : Fuel -> (Gen MaybeEmpty (Contains tys ty))
-- -- help fl ty = genTypes fl ty >>= genContains fl ty

-- export
-- genIsCastable : Fuel ->
--                 (cast : SupportedTypecast) ->
--                 (from : BasicType False) ->
--                 (to   : BasicType False) ->
--                 Gen MaybeEmpty (IsCastable cast from to)
-- genIsCastable fl (from' %= tos) from to = case decEq from' from of
--                                               Yes Refl => MakeCast <$> genContains fl tos to
--                                               No _ => empty


-- -- data Castable : ListOfSupportedCasts -> BasicType -> BasicType -> Type where
-- --     ReflCast  : Castable _ ty ty
-- --     FirstCast : IsCastable cst from to -> Castable (cst :: _) from to
-- --     NextCast  : Castable casts from to -> Castable (_ :: casts) from to

-- export
-- genCastable : Fuel ->
--               (casts : ListOfSupportedCasts) ->
--               (from  : BasicType False) ->
--               (to    : BasicType False) ->
--               Gen MaybeEmpty (Castable casts from to)
-- genCastable _ Nil from to = case decEq from to of
--                                 Yes Refl => pure ReflCast
--                                 No _ => empty 
-- genCastable fl ((from' %= tos) :: others) from to = case decEq from to of
--                                             Yes Refl => pure ReflCast
--                                             No _ => case decEq from' from of
--                                                 Yes Refl => FirstCast <$> genIsCastable fl (from' %= tos) from to
--                                                 No _ => NextCast <$> genCastable fl others from to

-- -- data ArgsCastable : ListOfSupportedCasts -> ListOfBasicTypes -> ListOfBasicTypes -> Type where
-- --     ReflListCast : ArgsCastable _ args args
-- --     DistructCast : Castable casts from to ->
-- --                     ArgsCastable casts otherFrom otherTo ->
-- --                     ArgsCastable casts (from :: otherFrom) (to :: otherTo)

-- export
-- genArgsCastable : Fuel ->
--               (casts : ListOfSupportedCasts) ->
--               (froms : ListOfBasicTypes) ->
--               (tos : ListOfBasicTypes) ->
--               Gen MaybeEmpty (ArgsCastable casts froms tos)
-- genArgsCastable _ _ Nil Nil = pure ReflListCast
-- genArgsCastable _ _ Nil (x :: xs) = empty
-- genArgsCastable _ _ (x :: xs) Nil = empty
-- genArgsCastable fl casts (from :: froms) (to :: tos) = [| DestructCast
--                                                             (genCastable fl casts from to)
--                                                             (genArgsCastable fl casts froms tos)
--                                                         |]

-- -- public export
-- -- genArgsCastable' : Fuel ->
-- --               (casts : ListOfSupportedCasts) ->
-- --               {froms : ListOfBasicTypes} ->
-- --               {tos : ListOfBasicTypes} ->
-- --               Gen MaybeEmpty (ArgsCastable casts froms tos) -- ArgsCastable[0]
-- -- genArgsCastable' _ Nil {froms} {tos} = case decEq froms tos of
-- --                                             Yes Refl => pure ReflListCast  
-- --                                             No _     => empty
-- -- genArgsCastable' fl ((from %= to) :: other) {froms} {tos} = DistructCast

-- -- genArgsCastable' _ _ Nil Nil = pure ReflListCast
-- -- genArgsCastable' _ _ Nil (x :: xs) = empty
-- -- genArgsCastable' _ _ (x :: xs) Nil = empty
-- -- genArgsCastable' fl casts (from :: froms) (to :: tos) = (DistructCast <$> genCastable     fl casts from  to)
-- --                                                                      <*> genArgsCastable fl casts froms tos


-- -- public export
-- -- data ExprList : ListOfSupportedCasts -> ListOfFunctions -> ListOfBasicTypes -> ListOfBasicTypes -> Type where
-- --     Nil  : ExprList casts vars funs []
-- --     (::) : Expr casts funs vars ty -> ExprList casts funs vars sx -> ExprList casts funs vars (ty :: sx)
-- export
-- genExpr : Fuel ->
--           (Fuel -> (casts : ListOfSupportedCasts) -> (funs : ListOfFunctions) -> (vars : ListOfBasicTypes) -> (resTys : ListOfBasicTypes) -> Gen MaybeEmpty (ExprList casts funs vars resTys)) =>
--           (casts : ListOfSupportedCasts) ->
--           (funs  : ListOfFunctions) ->
--           (vars  : ListOfBasicTypes) ->
--           (resTy : BasicType False) ->
--           Gen MaybeEmpty (Expr casts funs vars resTy)

-- export
-- genExprList : Fuel ->
--               (casts : ListOfSupportedCasts) ->
--               (funs : ListOfFunctions) ->
--               (vars : ListOfBasicTypes) ->
--               (resTys : ListOfBasicTypes) ->
--               Gen MaybeEmpty (ExprList casts funs vars resTys)

-- export
-- genExpr' : Fuel ->
--           (casts : ListOfSupportedCasts) ->
--           (funs  : ListOfFunctions) ->
--           (vars  : ListOfBasicTypes) ->
--           (resTy : BasicType False) ->
--           Gen MaybeEmpty (Expr casts funs vars resTy)
-- genExpr' Dry casts funs vars resTy = genExpr @{\_, _, _, _, _ => empty} Dry casts funs vars resTy
-- genExpr' (More fl) casts funs vars resTy = genExpr @{\_ => genExprList fl} (More fl) casts funs vars resTy


-- genExprList _ _ _ _ Nil = pure Nil
-- genExprList fl casts funs vars (ty :: tys) = [|
--                                                 genExpr' fl casts funs vars ty
--                                                 ::
--                                                 genExprList fl casts funs vars tys
--                                              |]