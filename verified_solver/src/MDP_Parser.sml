structure MDP_Parser = struct
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
(*
val decimal = (lexeme (repeat1 digit && (opt (char #"." >> repeat1 digit)) &&
(opt (char #"e" ) when
  (fn (pre, after) => Real.fromString (String.implode (
      case after of 
        NONE => pre
      | SOME x => pre @ #"." :: x)))))) ?? "decimal"
      *)
val float = lexeme (repeat1 (digit || oneOf (String.explode ".-e"))) when (fn str => Real.fromString (String.implode str)) ?? "float"

val parseWhole = digits wth (fn xs => (Option.valOf (IntInf.fromString (String.implode xs)), 1))


val parseFloat' = digits && (opt (char #"." >> digits)) wth (fn (pre, after) => 
  let 
    val after' = case after of SOME xs => xs | NONE => []
    val SOME enum = IntInf.fromString (String.implode (pre @ after'))
    val denom = IntInf.pow(10, length after')
  in
   (enum, denom)
end
)

val parseExp = (opt (char #"e" >> digits)) wth (fn xs =>
  case xs of SOME xs =>

  let val SOME x = Int.fromString (String.implode xs)
  in
    if x > 0 then (IntInf.pow(10, x), 1) else (1, IntInf.pow(10, Int.~x))
  end
  | NONE => (1,1)
)

val float' = lexeme (parseFloat' && parseExp) wth
  (fn ((n1,d1), (n2,d2)) => (n1 * n2, d1 * d2))

val number_line = num << newLine

  val lparen = (char #"(" ) ?? "lparen"
  val rparen = (char #")" ) ?? "rparen"

fun in_paren p = spaces >> lparen >> spaces >> p << spaces << rparen << spaces

val numinf = num wth IntInf.fromInt

(* Parsing of MPDs *)
val action = in_paren (numinf && float')

val state = numinf && numinf && (repeat action) && float'
  wth (fn (s,(a,(p,r))) => (s,(a,(r,p))))

val mdp = (numinf && numinf && repeat state) wth (fn (x,(y,z)) => (x,y,z))
end
