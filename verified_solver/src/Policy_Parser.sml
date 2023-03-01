structure Policy_Parser = struct
open ParserCombinators
open CharParser

infixr 4 << >>
infixr 3 &&
infix  2 -- ##
infix  2 wth suchthat return guard when
infixr 1 || <|> ??
infixr 5 @

(* auxiliary parsing definitions *)

val whiteSpace     = repeatSkip ((space return ()))
fun lexeme p       = p << whiteSpace

val num = (lexeme ((char #"-" || digit) && (repeat digit)) when
  (fn (x,xs) => Int.fromString (String.implode (x::xs)))) ?? "num expression"

val numinf = num wth IntInf.fromInt

val values = repeat (numinf && numinf)
end
