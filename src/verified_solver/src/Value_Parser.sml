structure Value_Parser = struct
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

val digits = ((char #"-" || digit) && (repeat digit)) wth (fn (x,xs) => x::xs)

val parseWhole = digits wth (fn xs => (Option.valOf (IntInf.fromString (String.implode xs)), 1))

val parseFloat' = digits && (opt (char #"." >> digits)) wth (fn (pre, after) => 
  let 
    val after' = case after of SOME xs => xs | NONE => []
    val enum = Option.valOf (IntInf.fromString (String.implode (pre @ after')))
    val denom = IntInf.pow(10, (length after'))
  in
   (enum, denom)
end
)
val parseExp = (opt (char #"e" >> digits)) wth (fn xs =>
  case xs of SOME xs =>

  let val x = Option.valOf (IntInf.fromString (String.implode xs))
  in
    if x > 0 then (IntInf.pow(10, IntInf.toInt x), 1) else (1, IntInf.pow(10, IntInf.toInt (IntInf.~x)))
  end
  | NONE => (1,1)
)

val float' = lexeme (parseFloat' && parseExp) wth
  (fn ((n1,d1), (n2,d2)) => (n1 * n2, d1 * d2))

val numinf = num wth IntInf.fromInt

val values = repeat float'
end
