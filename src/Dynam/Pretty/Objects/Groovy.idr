module Dynam.Pretty.Objects.Groovy

import Dynam.Pretty.Objects.Global

printExpr : {meths : VectOfFuns dim} ->
            {clss  : ListOfClasses dim} ->
            {objs  : ListOfClasses dim} -> 
            {funs  : ListOfFunctions} ->
            {vars  : ListOfBasicTypes} ->
            {opts  : LayoutOpts} ->
            (names : UniqNames meths clss objs funs vars) =>
            Prec ->
            Expr meths clss objs casts funs vars ty ->
            Gen0 $ Doc opts

printFunCall : {meths : VectOfFuns dim} ->
               {clss  : ListOfClasses dim} ->
               {objs  : ListOfClasses dim} -> 
               {funs  : ListOfFunctions} ->
               {vars  : ListOfBasicTypes} ->
               {opts  : LayoutOpts} ->
               (names : UniqNames meths clss objs funs vars) =>
               Prec ->
               IndexIn funs ->
               ExprList meths clss objs casts funs vars argTys ->
               Gen0 $ Doc opts
printFunCall p name args = do
  let fn = genFunName names name
  let f = line fn
  let args = toList $ getExprs args
  let tupledArgs = \as => map tuple $ for as $ \(Evidence _ e) => printExpr Open e
  
  case (isFunInfix names name, args, !(chooseAnyOf Bool)) of
    -- Call for bitwise infix extension method
    (True, [Evidence _ l, Evidence _ r], True) => pure $ parenthesise (p >= App) $ !(printExpr App l) <++> f <++> !(printExpr App r)
    -- Call for appropriate extension method with 0, 2 or more arguments
    (True, Evidence _ fst :: (Evidence _ snd :: Nil), _) => pure $ parenthesise (p >= App) $ !(printExpr App fst) <+> f <+> !(printExpr App snd)
    (True, Evidence _ head :: args, _) => pure $ parenthesise (p >= App) $ !(printExpr App head) <+> "." <+> f <+> !(tupledArgs args)
    -- Call for normal function
    _ => pure $ parenthesise (p >= App && isUnaryOp fn args) $ hang' 2 f !(tupledArgs args)


printExpr p $ Literal $ B False  = pure "false"
printExpr p $ Literal $ B True   = pure "true"

printExpr p $ Literal $ I num    = pure $ line $ show num
printExpr p $ Literal $ S str    = pure $ line str

printExpr p $ Var var          = pure $ line $ genVarName names var

-- printExpr p $ Invoke name args = assert_total printFunCall p name args


printStmts : {meths : VectOfFuns dim} ->
             {clss  : ListOfClasses dim} ->
             {objs  : ListOfClasses dim} -> 
             {funs  : ListOfFunctions} ->
             {vars  : ListOfBasicTypes} ->
             {opts  : LayoutOpts} ->
             (names : UniqNames meths clss objs funs vars) =>
             (newNames : Gen0 String) =>
             Fuel ->
             (toplevel : Bool) ->
             Stmts meths clss objs casts funs vars -> Gen0 $ Doc opts



printStmts fl tl $ NewV ty initial cont = do
    (nm ** _) <- genNewName fl newNames _ _ names
    rest <- printStmts @{NewVar nm} fl tl cont
    let tyAscr = "def "
    let lhs = tyAscr <+> line nm <++> "="
    rhs <- printExpr Open initial
    pure $ flip vappend rest $ hangSep' 2 lhs rhs

printStmts fl tl $ Ret = wrapMain {hod} {casts} {funs} {vars} fl tl Nothing $ pure empty


printStmts fl tl $ (#=) n v cont = wrapMain fl tl (Just cont) $ do
    pure $ line (genVarName names n) <++> "=" <++> !(printExpr Open v)

-- printStmts fl tl $ If cond th el cont = wrapMain fl tl (Just cont) $ do
--     -- thenBody  <- printStmts fl tl th
--     -- elseBody  <- printStmts fl tl el
--     -- condition <- printExpr Open cond
--     let pre  = "if (" 
--     let post = ") {"
--     let header = pre <+> !(printExpr Open cond) <++> post
--     pure $ vsep $
--         [ header
--         , indent' 4 !(printStmts fl False th)
--         , "} else {"
--         , indent' 4 !(printStmts fl False el)
--         , "}"
--         ]

printStmts fl tl $ While cond body cont = wrapMain fl tl (Just cont) $ do
    let pref = "while ("
    let post = ") {"
    let header = pref <+> !(printExpr Open cond) <++> post
    pure $ vsep $
        [ header
        , indent' 4 !(printStmts fl False body)
        , "}"
        ]

-- printStmts fl tl $ Call name args cont = wrapMain fl tl (Just cont) $ printFunCall Open name args


export
printGroovy : {meths : VectOfFuns dim} ->
              {clss  : ListOfClasses dim} ->
              {objs  : ListOfClasses dim} -> 
              {funs  : ListOfFunctions} ->
              {vars  : ListOfBasicTypes} ->
              {opts  : LayoutOpts} ->
              (names : UniqNames meths clss objs funs vars) =>
              Fuel ->
              Stmts meths clss objs casts funs vars -> Gen0 $ Doc opts
printGroovy fl = printStmts {names} {newNames = namesGen} fl True
