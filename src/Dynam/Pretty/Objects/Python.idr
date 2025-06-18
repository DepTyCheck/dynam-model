module Dynam.Pretty.Python

import Dynam.Pretty.Global
import public Dynam.Model.Stmts

printExpr : {hod : HOData dim} ->
            {funs : ListOfFunctions} ->
            {vars : ListOfBasicTypes} ->
            {opts: LayoutOpts} ->
            (names : UniqNames funs vars) =>
            Prec ->
            Expr hod casts funs vars ty ->
            Gen0 $ Doc opts

printFunCall : {hod : HOData dim} ->
               {funs : ListOfFunctions} ->
               {vars : ListOfBasicTypes} ->
               {opts : LayoutOpts} ->
               (names : UniqNames funs vars) =>
               Prec ->
               IndexIn funs ->
               ExprList hod casts funs vars argTys ->
               Gen0 $ Doc opts
printFunCall p name args = do
    let funName = genFunName names name
    let func = line funName
    let args = toList $ getExprs args
    let tupledArgs = \as => map tuple $ for as $ \(Evidence _ e) => printExpr {opts=opts} Open e

    case (isFunInfix names name, args) of
        (True, [Evidence _ l, Evidence _ r]) => do
            lhs <- printExpr App l
            rhs <- printExpr App r
            pure $ parenthesise (p >= App) $ lhs <++> func <++> rhs

        _ => do
            arguments <- tupledArgs args
            pure $ parenthesise (p >= App && isUnaryOp funName args) $ hang' 2 func arguments


printExpr p $ Literal $ B False  = pure "False"
printExpr p $ Literal $ B True   = pure "True"
printExpr p $ Literal $ I num    = pure $ line $ show num
printExpr p $ Literal $ S str    = pure $ line str

printExpr p $ Var var = pure $ line $ genVarName names var

-- printExpr p $ Invoke name args = assert_total printFunCall p name args


printStmts : {hod : HOData dim} ->
             {funs : ListOfFunctions} ->
             {vars : ListOfBasicTypes} ->
             {opts : LayoutOpts} ->
             (names : UniqNames funs vars) =>
             (newNames : Gen0 String) =>
             Fuel ->
             (toplevel : Bool) ->
             Stmts hod casts funs vars -> Gen0 $ Doc opts


printStmts fl tl $ NewV ty initial cont = do
    (nm ** _) <- genNewName fl newNames _ _ names
    rest      <- printStmts @{NewVar nm} fl tl cont

    let lhs = line nm <+> "="
    rhs <- printExpr Open initial

    pure $ vappend (hangSep' 2 lhs rhs) rest

printStmts fl tl $ Ret = pure empty

printStmts fl tl $ (#=) n v cont = do
    value <- printExpr Open v
    rest  <- printStmts fl tl cont

    pure $ vsep [
          line (genVarName names n) <++> "=" <++> value
        , rest
    ]

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

printStmts fl tl $ While cond body cont = do
    (nm ** _) <- genNewName fl newNames _ _ names
    rest      <- printStmts @{JustNew nm} {opts} fl tl cont
    condExpr  <- printExpr Open cond
    body      <- printStmts @{JustNew nm} fl False body
    let incr  =  line "\{nm} += 1"

    pure $ vsep [ 
          line "\{nm} = 1"
        , "while (" <+> condExpr <++> line ") and (\{nm} < 10000000):"
        , indent' 4 body
        , indent' 4 incr
        , rest
    ]

-- printStmts fl tl $ Call name args cont = wrapMain fl tl (Just cont) $ printFunCall Open name args


export
printPy : {hod : HOData dim} ->
              {funs : ListOfFunctions} ->
              {vars : ListOfBasicTypes} ->
              {opts : LayoutOpts} ->
              (names : UniqNames funs vars) =>
              Fuel ->
              Stmts hod casts funs vars -> Gen0 $ Doc opts
printPy fl = printStmts {names} {newNames = namesGen} fl True
