module Dynam.Run.ParserProblem

import Data.String

example : Maybe String
example = do
    rand <- Just True

    let a : List String = ["", "m", "yu"]

    case rand of
        True => do
            pure "67"
        _ => do
            pure $ joinBy ", " [
                 ""
                , ""
            ]
