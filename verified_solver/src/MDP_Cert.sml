fun parse_wrapper parser file =
  case (CharParser.parseString parser (readFile file)) of
    Sum.INR x => x
  | Sum.INL err => exit_fail err

  fun parse_string parser str =
  case (CharParser.parseString parser str) of
    Sum.INR x => x
  | Sum.INL err => exit_fail err

(* Main program *)

structure VIF_CERT : TO_ISA_MDP_CERT =
struct
  open VIF  
  open Float_MDP
  open VI_Code_Float

  fun convert_exec_cert init (disc, mdp, eps) : bool =
    let 
      val init_isa = (v_map_from_list (map to_isa_real init))
      val eps_isa = to_isa_real eps
      val mdp_isa = assoc_to_isa_MDP (disc, mdp)
      val (actual_eps, res_pol) = vi_policy_bound_error_code mdp_isa init_isa
    in
      isa_le actual_eps eps_isa
    end
end

structure GSR_CERT : TO_ISA_MDP_CERT =
struct
  open GSR
  open GS_Code_Rat
  open MDP_GSR

  fun convert_exec_cert init (disc, mdp, eps) : bool =
    let 
      val init_isa = (v_map_from_list (map to_isa_real init))
      val eps_isa = to_isa_real eps
      val mdp_isa = assoc_to_isa_MDP (disc, mdp)
      val (actual_eps, res_pol) = gs_policy_bound_error_code mdp_isa init_isa
    in
      isa_le actual_eps eps_isa
    end
end


structure GSF_CERT : TO_ISA_MDP_CERT =
struct
  open GSF  
  open Float_MDP
  open GS_Code_Float

  fun convert_exec_cert init (disc, mdp, eps) : bool =
    let 
      val init_isa = (v_map_from_list (map to_isa_real init))
      val eps_isa = to_isa_real eps
      val mdp_isa = assoc_to_isa_MDP (disc, mdp)
      val (actual_eps, res_pol) = gs_policy_bound_error_code mdp_isa init_isa
    in
      isa_le actual_eps eps_isa
    end
end

structure VIR_CERT : TO_ISA_MDP_CERT =
struct
  open VIR
  open VI_Code_Rat
  open MDP_VIR

  fun convert_exec_cert init (disc, mdp, eps) : bool =
    let 
      val init_isa = (v_map_from_list (map to_isa_real init))
      val eps_isa = to_isa_real eps
      val mdp_isa = assoc_to_isa_MDP (disc, mdp)
      val (actual_eps, res_pol) = vi_policy_bound_error_code mdp_isa init_isa
    in
      isa_le actual_eps eps_isa
    end
end

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

fun print_cert_res res = println (Bool.toString res)

val (discNum, epsNum, mdp_assoc, f_algo, init_values) =
case args of 
  [mdp,algo,disc,eps,mode,value_file] => 
    let 
        val discNum = parse_string MDP_Parser.float' disc
        val epsNum = parse_string MDP_Parser.float' eps

        val (states, actions, mdp_list) = parse_mdp mdp
        val _ = print "parsing done\n"
        val mdp_assoc = mdp_list_to_assoc mdp_list : mdp_assoc_t
        val _ = print "converting done\n"

        val init_values = parse_values value_file

        val f_algo =
          if mode = "float" then
            if algo = "vi" then VIF_CERT.convert_exec_cert
            else if algo = "gs" then GSF_CERT.convert_exec_cert
            else exit_fail("Unknown algorithm!")
          else if mode = "rational" then
            if algo = "vi" then VIR_CERT.convert_exec_cert
            else if algo = "gs" then GSR_CERT.convert_exec_cert
            else exit_fail("Unknown algorithm!")
          else exit_fail("Unknown mode!")
    in
    (discNum, epsNum, mdp_assoc, f_algo, init_values)
    end
| _ => (
    println("Invalid command line arguments");
    print_help();
    exit_fail("Error")
  )

val _ =
  let
  val res = f_algo init_values (discNum, mdp_assoc, epsNum)
  val _ = print "solver done\n"
        in
        print_cert_res res
    end