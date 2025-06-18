module Dynam.Pretty.Base.Groovy

import Dynam.Pretty.Base.Global


%default total

            
printComment : {opts: LayoutOpts} -> Gen0 $ Doc opts
printComment = do
    linesCnt    <- choose (0, 5)
    isMultiline <- chooseAnyOf Bool

    case (linesCnt, isMultiline) of
        (0, _) => do
            pure empty
        (_, True) => do
            lines <- traverse id [ pack <$> listOf {length = choose (1, 80)} (choose ('+', '~')) | _ <- (genRange linesCnt) ]
            let lines = lines <&> \ln => line $ " * " ++ ln
            pure $ vsep [
                  line "/*"
                , vsep lines
                , line " */"
            ]
        (_, False) => do
            lines <- traverse id [ pack <$> listOf {length = choose (1, 80)} (choose ('+', '~')) | _ <- (genRange linesCnt) ]
            let lines = lines <&> \ln => line $ "// " ++ ln
            pure $ vsep lines

printInlineComment : {opts: LayoutOpts} -> Gen0 $ Doc opts
printInlineComment = do
    isEmpty <- chooseAnyOf Bool

    case isEmpty of
        False => do
            pure empty
        True  => do
            text <- pack <$> listOf {length = choose (1, 3)} (choose ('+', '~'))
            pure $ "/*" <++> line text <++> "*/"
    


printExpr : {funs : ListOfFunctions} ->
            {vars : ListOfBasicTypes} ->
            {opts: LayoutOpts} ->
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
            pure $ parenthesise (p >= App) $ lhs <++> !(printInlineComment) <++> func <++> !(printInlineComment) <++> rhs

        _ => do
            arguments <- tupledArgs args
            pure $ parenthesise (p >= App && isUnaryOp funName args) $ hang' 2 func arguments


printExpr p $ Literal Boolean  = do
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

    let lhs = "def" <++> !(printInlineComment) <++> line "\{nm}" <++> !(printInlineComment) <++> "=" <++> !(printInlineComment)
    rhs     <- printExpr Open initial
    comment <- printComment

    pure $ vsep [
          comment
        , hangSep' 2 lhs rhs
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
        , name <++> !(printInlineComment) <++> "=" <++> !(printInlineComment) <++> value
        , rest
    ]

printStmts fl tl $ If cond th el cont = do
    let pre    = "if" <++> !(printInlineComment) <++> "(" 
    let post   = ")"  <++> !(printInlineComment) <++> "{"
    let header = pre <++> !(printInlineComment) <++> !(printExpr Open cond) <++> !(printInlineComment) <++> post

    rest    <- printStmts fl tl cont
    comment <- printComment

    pure $ vsep [
          comment
        , header
        , indent' 4 !(printStmts fl False th)
        , "}" <++> !(printInlineComment) <++> "else" <++> !(printInlineComment) <++> "{"
        , indent' 4 !(printStmts fl False el)
        , !(printInlineComment) <++> "}" <++> !(printInlineComment)
        , rest
    ]

printStmts fl tl $ While cond body cont = do
    (nm ** _) <- genNewName fl newNames _ _ names
    rest      <- printStmts @{JustNew nm} {opts} fl tl cont
    condExpr  <- printExpr {opts} Open cond
    body      <- printStmts @{JustNew nm} {opts} fl False body
    comment   <- printComment
    let incr  =  line "\{nm} += 1"

    rand <- chooseAnyOf Bool

    case (tl, rand) of
        (True, True) => do
            pure $ vsep [
                  comment 
                , "def" <++> !(printInlineComment) <++> line "\{nm}" <++> !(printInlineComment) <++> "=" <++> !(printInlineComment) <++> "1"
                , "while" <++> !(printInlineComment) <++> "(" <++> !(printInlineComment)
                          <++> "(" <++> !(printInlineComment) <++> condExpr <++> !(printInlineComment) <++> ")"
                          <++> !(printInlineComment) <++> "&&"
                          <++> !(printInlineComment) <++> "(" <++> !(printInlineComment) <++> line "\{nm}" <++> !(printInlineComment) <++> "<" 
                                                              <++> !(printInlineComment) <++> "1000" <++> !(printInlineComment) <++> ")"
                          <++> !(printInlineComment) <++> ")" <++> !(printInlineComment) <++> "{"
                , indent' 4 body
                , indent' 4 incr 
                , !(printInlineComment) <++> "}" <++> !(printInlineComment)
                , rest
            ]
        (False, True) => do
            pure $ vsep [
                  comment 
                , "def" <++> !(printInlineComment) <++> line "\{nm}" <++> !(printInlineComment) <++> "=" <++> !(printInlineComment) <++> "1"
                , "while" <++> !(printInlineComment) <++> "(" <++> !(printInlineComment)
                          <++> "(" <++> !(printInlineComment) <++> condExpr <++> !(printInlineComment) <++> ")"
                          <++> !(printInlineComment) <++> "&&"
                          <++> !(printInlineComment) <++> "(" <++> !(printInlineComment) <++> line "\{nm}" <++> !(printInlineComment) <++> "<" 
                                                              <++> !(printInlineComment) <++> "100" <++> !(printInlineComment) <++> ")"
                          <++> !(printInlineComment) <++> ")" <++> !(printInlineComment) <++> "{"
                , indent' 4 body
                , indent' 4 incr 
                , !(printInlineComment) <++> "}" <++> !(printInlineComment)
                , rest
            ]
        _ => do
            pure $ vsep [
                  comment
                , "if" <++> !(printInlineComment) <++> "(" <++> !(printInlineComment) <++> condExpr <++> !(printInlineComment) <++> ")" <++> !(printInlineComment) <++> "{"
                , indent' 4 body
                , !(printInlineComment) <++> "}" <++> !(printInlineComment)
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
    rest      <- printStmts {opts} fl tl cont

    (unique, argNames) <- genNewVars fl newNames args names
    let names : List String = argNames <&> \(name, ty) => name
    let argString = joinBy ", " names

    body <- printStmts @{unique} {opts} fl False body
    rand <- chooseAnyOf Bool

    comment <- printComment

    case (tl, rand) of
        (True, True) => do
            pure $ vsep [
                  comment 
                , "def" <++> !(printInlineComment) <++> line "\{nm}" <++> !(printInlineComment) <++> "("
                        <++> !(printInlineComment) <++> line "\{argString}" <++> !(printInlineComment) <++> ")"
                        <++> !(printInlineComment) <++> "{"
                , indent' 4 body
                , !(printInlineComment) <++> "}" <++> !(printInlineComment)
                , rest
            ]
        _ => do
            pure $ vsep [
                  comment
                , "def" <++> !(printInlineComment) <++> line "\{nm}" <++> !(printInlineComment) <++> "="
                        <++> !(printInlineComment) <++> "{" <++> !(printInlineComment) <++> line "\{argString}" 
                        <++> !(printInlineComment) <++> "->"
                , indent' 4 body
                , !(printInlineComment) <++> "}" <++> !(printInlineComment)
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
    rand <- chooseAnyOf Bool

    comment <- printComment {opts}

    case (tl, rand) of
        (True, True) => do
            pure $ vsep [
                  comment 
                , "def" <++> !(printInlineComment) <++> line "\{nm}" <++> !(printInlineComment) <++> "("
                        <++> !(printInlineComment) <++> line "\{argString}" <++> !(printInlineComment) <++> ")"
                        <++> !(printInlineComment) <++> "{"
                , indent' 4 body
                , indent' 4 "return" <++> !(printInlineComment) <++> retEx
                , !(printInlineComment) <++> "}" <++> !(printInlineComment)
                , rest
            ]
        _ => do
            pure $ vsep [
                  comment
                , "def" <++> !(printInlineComment) <++> line "\{nm}" <++> !(printInlineComment) <++> "="
                        <++> !(printInlineComment) <++> "{" <++> !(printInlineComment) <++> line "\{argString}" 
                        <++> !(printInlineComment) <++> "->"
                , indent' 4 body
                , indent' 4 "return" <++> !(printInlineComment) <++> retEx
                , !(printInlineComment) <++> "}" <++> !(printInlineComment)
                , rest
            ]


export
printGroovy : {funs : ListOfFunctions} ->
              {vars : ListOfBasicTypes} ->
              {opts : LayoutOpts} ->
              (names : UniqNames funs vars) =>
              Fuel ->
              Stmts casts funs vars -> Gen0 $ Doc opts
printGroovy fl = printStmts {names} {newNames = namesGen} fl True
