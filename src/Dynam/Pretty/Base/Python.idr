module Dynam.Pretty.Base.Python

import Dynam.Pretty.Base.Global

%default total

printComment : {opts: LayoutOpts} -> Gen0 $ Doc opts
printComment = do
    linesCnt <- choose (0, 5)

    case linesCnt of
        0 => do
            pure empty
        _ => do
            lines <- traverse id [ pack <$> listOf {length = choose (1, 80)} (choose ('+', '~')) | _ <- (genRange linesCnt) ]
            let lines = lines <&> \ln => line $ "# " ++ ln
            pure $ vsep lines


printExpr : {funs : ListOfFunctions} ->
            {vars : ListOfBasicTypes} ->
            {opts: LayoutOpts} ->
            {default False inFun : Bool} ->
            (names : UniqNames funs vars) =>
            Prec ->
            Expr casts funs vars ty ->
            Gen0 $ Doc opts

printFunCall : {funs : ListOfFunctions} ->
               {vars : ListOfBasicTypes} ->
               {opts : LayoutOpts} ->
               (names : UniqNames funs vars) =>
               Prec ->
               IndexIn funs ->
               ExprList casts funs vars argTys ->
               Gen0 $ Doc opts
printFunCall p name args = do
    let funName = genFunName names name
    let func = line funName
    let args = toList $ getExprs args
    let tupledArgs = \as => map tuple $ for as $ \(Evidence _ e) => printExpr {opts} Open e

    case (isFunInfix names name, args) of
        (True, [Evidence _ l, Evidence _ r]) => do
            lhs <- printExpr App l
            rhs <- printExpr App r
            pure $ parenthesise (p >= App) $ lhs <++> func <++> rhs

        _ => do
            arguments <- tupledArgs args
            pure $ parenthesise (p >= App && isUnaryOp funName args) $ hang' 2 func arguments


printExpr p $ Literal Boolean = do
    value <- chooseAnyOf Bool
    case value of
        False => pure "false"
        True  => pure "true"
printExpr p $ Literal Number = do
    value <- chooseAnyOf Int32
    pure $ line $ show value
printExpr p $ Literal Str = do
    str <- pack <$> listOf {length = choose (1, 6)} (choose ('0', '9'))
    pure $ "\"" <+> line str <+> "\""

printExpr p $ Var var = pure $ line $ genVarName names var

printExpr p $ Invoke name args = assert_total printFunCall p name args


printStmts : {funs : ListOfFunctions} ->
            --  {retFun : Bool} ->
             {vars : ListOfBasicTypes} ->
             {opts : LayoutOpts} ->
             (names : UniqNames funs vars) =>
             (newNames : Gen0 String) =>
             Fuel ->
             (toplevel : Bool) ->
             Stmts casts funs vars -> Gen0 $ Doc opts


printStmts fl tl $ NewV ty initial cont = do
    (nm ** _) <- genNewName fl newNames _ _ names
    rest      <- printStmts @{NewVar nm} fl tl cont

    let lhs = line nm <+> "="
    rhs     <- printExpr Open initial
    comment <- printComment

    pure $ vsep [
          comment  
        , (hangSep' 2 lhs rhs)
        , rest
    ]

printStmts fl tl $ Ret = do
    cmt <- chooseAnyOf Bool
    case cmt of
        True  => printComment
        False => pure empty

printStmts fl tl $ (#=) n v cont = do
    value   <- printExpr Open v
    rest    <- printStmts fl tl cont
    comment <- printComment

    let name = line $ genVarName names n

    pure $ vsep [
          comment
        , name <++> "=" <++> value
        , rest
    ]

printStmts fl tl $ If cond th el cont = do
    let header = "if" <++> !(printExpr Open cond) <+> ":"

    rest    <- printStmts fl tl cont
    comment <- printComment

    pure $ vsep [
          comment
        , header
        , indent' 4 !(printStmts fl False th)
        , "else:"
        , indent' 4 !(printStmts fl False el)
        , rest
    ]

printStmts fl tl $ While cond body cont = do
    (nm ** _) <- genNewName fl newNames _ _ names
    rest      <- printStmts @{JustNew nm} {opts} fl tl cont
    condExpr  <- printExpr Open cond
    body      <- printStmts @{JustNew nm} fl False body
    comment   <- printComment
    let incr  =  line "\{nm} += 1"

    rand <- chooseAnyOf Bool

    case (tl, rand) of
        (True, True) => do
            pure $ vsep [ 
                comment
                , line "\{nm} = 1"
                , "while (" <+> condExpr <+> line ") and (\{nm} < 1000):"
                , indent' 4 body
                , indent' 4 incr
                , rest
            ]
        (False, True) => do
            pure $ vsep [ 
                comment
                , line "\{nm} = 1"
                , "while (" <+> condExpr <+> line ") and (\{nm} < 100):"
                , indent' 4 body
                , indent' 4 incr
                , rest
            ]
        (_, False) => do
            pure $ vsep [ 
                comment
                , line "\{nm} = 1"
                , "if" <++> condExpr <+> ":"
                , indent' 4 body
                , indent' 4 incr
                , rest
            ]

printStmts fl tl $ Call name args cont = do
    func <- printFunCall Open name args
    rest <- printStmts fl tl cont

    comment <- printComment

    pure $ vsep [ 
          comment
        , func
        , rest
    ]

printStmts fl tl $ NewProc args body cont = do
    (nm ** _) <- genNewName fl newNames _ _ names
    rest      <- printStmts fl tl cont

    (unique, argNames) <- genNewVars fl newNames args names
    let names : List String = argNames <&> \(name, ty) => name
    let argString = joinBy ", " names

    body    <- printStmts @{unique} {opts} fl False body
    comment <- printComment

    pure $ vsep [ 
          comment
        , line "def \{nm}(\{argString}):"
        , indent' 4 body
        , rest
    ]

printStmts fl tl $ NewFun ty args body retExpr cont = do
    (nm ** _) <- genNewName fl newNames _ _ names

    retEx <- printExpr {opts} Open retExpr
    rest  <- printStmts {opts} fl tl cont

    (unique, argNames) <- genNewVars fl newNames args names
    let names : List String = argNames <&> \(name, tty) => name
    let argString = joinBy ", " names

    body <- printStmts @{unique} {opts} fl False body

    comment <- printComment

    pure $ vsep [
          comment 
        , line "def \{nm}(\{argString}):"
        , indent' 4 body
        , indent' 4 "return" <++> retEx
        , rest
    ]


export
printPy : {funs : ListOfFunctions} ->
          {vars : ListOfBasicTypes} ->
          {opts : LayoutOpts} ->
          (names : UniqNames funs vars) =>
          Fuel ->
          Stmts casts funs vars -> Gen0 $ Doc opts
printPy fl = printStmts {names} {newNames = namesGen} fl True
