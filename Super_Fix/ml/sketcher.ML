(* 
  Mantainers: 
    Chengsong Tan -- c.tan[at]imperial[dot]ac[dot]uk
    Jonathan Julián Huerta y Munive -- huertjon[at]cvut[dot]cz

Main implementation of super_fix's algorithm
*)

signature SKETCHER =
sig
  val set_verbose: Proof.context -> Proof.context
  val sketch_term: Proof.context -> term -> string
  val sketch_typ: Proof.context -> typ -> string
  val coalesce_method_txt: string list -> string
  val sketch_method: (Method.text_range * Token.T list) option -> string
  datatype format_mode = LEMMAS of Path.T * Path.T | SHOW_IFS
  val init_indent_from: format_mode -> int
  val show_ifs_sketcher: int -> (int * (string option * string option * string)) -> string
  val make_proof_qed_skel: string -> string list -> string
  val sketch_goal_as: format_mode -> int -> Toplevel.state 
    -> int * ((bstring * typ) list * term list * term) 
    -> string
  val sketch_as: format_mode -> int -> Toplevel.state 
    -> (int * ((bstring * typ) list * term list * term)) list
    -> string list
  val get_goals_at: Proof.state ->
      ((string * typ) list * term list * term) list
  val get_goals_after: (Method.text_range * Token.T list) option 
    -> Toplevel.state -> bool * (int * ((string * typ) list * term list * term)) list
  val try_method: (Method.text_range * Token.T list) option ->
      Toplevel.state -> int * bool * string * Toplevel.state
end;

structure Sketcher: SKETCHER =
struct

val set_verbose = fold (fn bconf => Config.put bconf false)
  [show_markup, Printer.show_type_emphasis, show_types, show_sorts, show_consts];

fun sketch_term ctxt t = 
  Print.string_of_term ctxt t
  |> Library.enclose "\"" "\"";

fun sketch_typ ctxt T = 
  Print.string_of_type ctxt T
  |> Library.enclose "\"" "\"";

fun coalesce_method_txt [] = ""
  | coalesce_method_txt [s] = s
  | coalesce_method_txt (s1 :: s2 :: ss) =
      if Library.member (op =) ["(", "["] s1
        orelse Library.member (op =) [")", "]", ":", ";"] s2
      then s1 ^ coalesce_method_txt (s2 :: ss)
      else s1 ^ " " ^ coalesce_method_txt (s2 :: ss);

fun sketch_method opt_m = case opt_m of 
  SOME (_,toks) => coalesce_method_txt (map Token.unparse toks)
  | NONE => "-";

(* TODO: add SUBGOAL and ASSMS_SHOW *)
datatype format_mode = 
  LEMMAS of Path.T * Path.T
  | SHOW_IFS

fun init_indent_from format = (case format of LEMMAS _ => 0 | SHOW_IFS => 2);

fun add_ands indent strs = 
  let 
    val sep = "\n" ^ (Symbol.spaces (indent + 2)) ^ "  and ";
  in space_implode sep strs end;

fun prepare_goal_data ctxt indent (fixes, assms, concl) = 
  let
    val opt_assumes = if null assms then NONE
      else SOME (map (sketch_term ctxt) assms);
    val opt_fixes = if null fixes then NONE
      else SOME (map (fn (v, T) => v ^ " :: " ^ sketch_typ ctxt T) fixes);
    val goal = sketch_term ctxt concl;
  in (Option.map (add_ands indent) opt_fixes, 
    Option.map (add_ands indent) opt_assumes, 
    goal)
  end;

fun upd_context_with (var_typs, assms, concl) ctxt =
  let
    val fixes = map (fn (s, T) => (Binding.name s, SOME T, NoSyn)) var_typs
    val ctxt' = ctxt |> Variable.set_body false |> Proof_Context.add_fixes fixes |> snd
      handle ERROR _ =>
      ctxt |> Variable.set_body true |> Proof_Context.add_fixes fixes |> snd
  in ((var_typs, assms, concl), ctxt') end;

fun str_of_goal_data indent st goal_data = 
  let
    val ctxt' = set_verbose (Toplevel.context_of st);
    val ((fixes, assms, concl), ctxt'') = upd_context_with goal_data ctxt';
    val (opt_fixes, opt_assumes, goal) = prepare_goal_data ctxt'' indent (fixes, assms, concl);
  in (opt_fixes, opt_assumes, goal) end;

fun make_proof_qed_skel fst_m_txt = 
  space_implode "\nnext\n" 
  #> (fn skel => "proof" ^ fst_m_txt ^ "\n" ^ skel ^ "\n" ^ "qed");

fun show_ifs_sketcher indent (goal_num, (opt_fixes, opt_assms, goal)) =
  let
    val sep = "\n" ^ (Symbol.spaces (indent + 2));
    val header = "show goal" ^ Value.print_int goal_num ^ ": ";
    val fors = the_default "" (Option.map (curry (op ^) (sep ^ "for ")) opt_fixes);
    val ifs = the_default "" (Option.map (curry (op ^) (sep ^ "if ")) opt_assms);
    val shows = Symbol.spaces indent ^ header ^ goal;
    val sorry = if ifs = ""
      then sep ^ "  sorry" else sep ^ "using that" ^ sep ^ "sorry"
  in shows ^ ifs ^ fors ^ sorry end;

fun get_formatter format indent num =
  (case format of 
    LEMMAS _ => (fn (opt_fixes, opt_assms, goal) => 
    let
      val sep = "\n" ^ (Symbol.spaces (indent + 2));
      val header = "lemma goal" ^ Value.print_int num ^ ": ";
      val fixes = the_default "" (Option.map (curry (op ^) (sep ^ "fixes ")) opt_fixes);
      val assms = the_default "" (Option.map (curry (op ^) (sep ^ "assumes ")) opt_assms);
      val shows = if fixes = "" andalso assms = ""
        then goal else sep ^ "shows " ^ goal;
      val sorry = sep ^ "  sorry"
    in header ^ fixes ^ assms ^ shows ^ sorry end)
    | SHOW_IFS => (fn pass => show_ifs_sketcher indent (num, pass)));

fun sketch_goal_as format indent st (goal_num, goal_data) =
  let
    val (opt_fixes, opt_assumes, goal) = str_of_goal_data indent st goal_data;
    val formatter = get_formatter format indent goal_num;
  in formatter (opt_fixes, opt_assumes, goal) end;

fun sketch_as format indent st goals = 
  Par_List.map (sketch_goal_as format indent st) goals;

fun split_clause t =
  let
    val (fixes, horn) = funpow_yield (length (Term.strip_all_vars t)) Logic.dest_all_global t;
    val assms = Logic.strip_imp_prems horn;
    val concl = Logic.strip_imp_concl horn;
  in (fixes, assms, concl) end;

fun get_goals_at prf_st =
  let
    val {context = _, facts = _, goal} = Proof.goal prf_st;
    val goals = map split_clause (Logic.strip_imp_prems (Thm.prop_of goal))
  in goals end;

(* TODO: analyse efficiency and accuracy changes by working at the top level: 
`val (act', st', err') 
  = Actions.apply (Actions.make_one (Toplevel.theory_of st) ("apply " ^ m_txt)) st;` *)
fun get_goals_after opt_m st =
  let
    val (opt_m', m_txt) = (case opt_m of 
      SOME (m,toks) => (SOME m, coalesce_method_txt (map Token.unparse toks))
      | NONE => (NONE, "-"));
    val apply_m = Toplevel.proof_of #> Proof.proof opt_m' #> Seq.the_result "";
    val (applied_m, prf_st) = if is_some opt_m'
      then (case Ops.apply_with_timeout (Time.fromSeconds 10) apply_m st 
        of Exn.Exn _ => (false, Toplevel.proof_of st) 
        | Exn.Res state => (true, state))
      else (false, Toplevel.proof_of st);
    val clauses = Ops.enumerate (get_goals_at prf_st);
    val _ = if applied_m orelse is_none opt_m' then ()
      else Output.tracing ("Could not apply method " ^ m_txt ^ ". Skipping...");
  in (applied_m, clauses) end;

fun try_method opt_m st =
  let
    val m_txt = sketch_method opt_m;
    val (applied_m, clauses) = get_goals_after opt_m st;
    val num_goals = length clauses;
    val final_str = if num_goals = 0
      then if m_txt = "-" then "done" else "by " ^ m_txt
      else if not applied_m then "sorry" else "apply " ^ m_txt
    val final_st = if not applied_m then st
      else let
        val m_act = Actions.make_one (Toplevel.theory_of st) final_str;
      in fst (Actions.apply m_act st) end;
  in (num_goals, applied_m, final_str, final_st) end;

fun try_methods_sequentially ms st =
  let
    fun apply_next_method m (proved, curr_st, prf_so_far) =
      if proved then (proved, curr_st, prf_so_far)
      else let 
        val (goal_count, applied_m, prf_str, st') = try_method m curr_st;
        val proved' = goal_count = 0;
        val result = if applied_m then (proved', st', prf_so_far @ [prf_str])
          else (proved', curr_st, prf_so_far)
      in result end;
  in fold apply_next_method ms (false, st, []) end;

end;