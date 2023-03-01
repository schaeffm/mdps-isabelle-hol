fun parse_wrapper parser file =
  case (CharParser.parseString parser (readFile file)) of
    Sum.INR x => x
  | Sum.INL err => exit_fail err

  fun parse_string parser str =
  case (CharParser.parseString parser str) of
    Sum.INR x => x
  | Sum.INL err => exit_fail err

(* Main program *)

fun print_help () = (
  println("Usage: " ^ CommandLine.name() ^ " <domain> <horizon> <mode>")
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

fun print_res (v,d) = (
  (*println (show_list (
    show_list Real.toString ", ") ", " v);*)
  println (show_list ( 
    show_list IntInf.toString ", ") "\n epoch: " d))

val (horizon, mdp_assoc, f_algo, r_N) =
case args of 
  mdp::horizon::mode::rest => 
    let 
        val horizon_num = parse_string MDP_Parser.numinf horizon

        val (states, actions, mdp_list) = parse_mdp mdp
        val _ = print "parsing done\n"
        val mdp_assoc = mdp_list_to_assoc mdp_list : mdp_assoc_t
        val _ = print "converting done\n"

        val r_N_list = case rest of 
        [r_N_file] => (parse_values r_N_file)
        | [] => List.tabulate (IntInf.toInt states, fn i => (0,1))

        val f_algo =
          if mode = "float" then
            FF.convert_exec
          else if mode = "rational" then
            FR.convert_exec
          else exit_fail("Unknown mode!")
    in
    (horizon_num, mdp_assoc, f_algo, r_N_list)
    end
| _ => (
    println("Invalid command line arguments");
    print_help();
    exit_fail("Error")
  )

val _ =
  let
  val res = f_algo (mdp_assoc, horizon, r_N)
  val _ = println "solver done"
        in
        print_res res
    end

(*
val _ = OS.Process.exit(OS.Process.success)
*)
