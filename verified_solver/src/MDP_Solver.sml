fun parse_wrapper parser file =
  case (CharParser.parseString parser (readFile file)) of
    Sum.INR x => x
  | Sum.INL err => exit_fail err

  fun parse_string parser str =
  case (CharParser.parseString parser str) of
    Sum.INR x => x
  | Sum.INL err => exit_fail err

(* aux *)
(*
fun to_isa_rat (n,d) = (divide_rat (of_int (Int_of_integer n)) (of_int (Int_of_integer d)))
fun from_isa_rat r = case quotient_of r of (Int_of_integer n, Int_of_integer d) => Real./ (Real.fromLargeInt n, Real.fromLargeInt d)
  *)

(* Main program *)

fun print_help () = (
  println("Usage: " ^ CommandLine.name() ^ " <domain> <algorithm> <discount> <epsilon> <mode> <values>")
)

fun show_transition (s, p) = IntInf.toString s ^ ": " ^ Real.toString p 

fun show_sa (s, (a, (transitions, r))) = 
    "(" ^ IntInf.toString s ^ "," ^ IntInf.toString a ^ "): r = " ^ Real.toString r ^ ", " ^ show_list show_transition ", " transitions

fun show_action (a, (r, ps)) = 
    "a"^ IntInf.toString a ^ ": r = " ^ Real.toString r ^ ", " ^ show_list show_transition ", " ps

fun show_mdp mdp = show_list (fn (a) => 
    "s?" ^ ":\n" ^ show_list show_action "\n" a) "\n" mdp

val parse_mdp = parse_wrapper MDP_Parser.mdp
val parse_values = parse_wrapper Value_Parser.values

val args = CommandLine.arguments()

fun print_res res = println (show_list (fn (k, v) => IntInf.toString k ^ ": " ^ IntInf.toString v) ", " res)

val (discNum, epsNum, mdp_assoc, f_algo, init_values, out_file) =
case args of 
  mdp::algo::disc::eps::mode::rest => 
    let 
        val discNum = parse_string MDP_Parser.float' disc
        val epsNum = parse_string MDP_Parser.float' eps

        val (states, actions, mdp_list) = parse_mdp mdp
        val _ = print "parsing done\n"
        val mdp_assoc = mdp_list_to_assoc mdp_list : mdp_assoc_t
        val _ = print "converting done\n"

        val init_values = case rest of 
        value_file::_ => SOME (parse_values value_file)
        | [] => NONE

        val out_file = case rest of
        value_file::out_file::_ => SOME out_file
        | _ => NONE

        val f_algo =
          if mode = "float" then
            if algo = "pi" then PIF.convert_exec
            else if algo = "mpi" then MPIF.convert_exec
            else if algo = "vi" then 
              case init_values of SOME v => VIF.convert_exec_init v | NONE => VIF.convert_exec
            else if algo = "gs" then
              case init_values of SOME v => GSF.convert_exec_init v | NONE => GSF.convert_exec
            else exit_fail("Unknown algorithm!")
          else if mode = "rational" then
            if algo = "pi" then PIR.convert_exec
            else if algo = "mpi" then MPIR.convert_exec
            else if algo = "vi" then
             case init_values of SOME v => VIR.convert_exec_init v | NONE => VIR.convert_exec
            else if algo = "gs" then 
              case init_values of SOME v => GSR.convert_exec_init v | NONE => GSR.convert_exec
            else exit_fail("Unknown algorithm!")
          else exit_fail("Unknown mode!")
    in
    (discNum, epsNum, mdp_assoc, f_algo, init_values, out_file)
    end
| _ => (
    println("Invalid command line arguments");
    print_help();
    exit_fail("Error")
  )

fun str_to_file(outFile: string, txt: string) =
  let
    val outStream = TextIO.openOut outFile
    val _ = TextIO.output(outStream, txt)
    val _ = TextIO.closeOut outStream
  in
    ()
  end


val _ =
  let
  val res = f_algo (discNum, mdp_assoc, epsNum)
  val _ = print "solver done\n"
  val res_str = show_list (fn (k, v) => IntInf.toString k ^ ": " ^ IntInf.toString v) ", " res
  val _ = print res_str
  val _ = case out_file of SOME out_file => str_to_file(out_file, res_str) | _ => ()
    in
    ()
    end

(*
val _ = OS.Process.exit(OS.Process.success)
*)
