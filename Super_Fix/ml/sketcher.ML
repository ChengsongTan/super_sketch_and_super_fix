(* 
  Mantainers: 
    Chengsong Tan -- c.tan[at]imperial[dot]ac[dot]uk
    Jonathan Julián Huerta y Munive -- huertjon[at]cvut[dot]cz

Generic sketching operations
*)

signature SKETCHER =
sig
  val set_verbose: Proof.context -> Proof.context
  val sketch_term: Proof.context -> term -> string
  val sketch_typ: Proof.context -> typ -> string
  val sketch_header: string -> string list -> Toplevel.state -> string

  type method = Method.text_range * Token.T list
  val sketch_method: method option -> string

  datatype format = LEMMAS of Path.T * Path.T | SHOW_IFS
  val init_indent_from: format -> int
  val make_skeleton: format -> int -> string -> string list -> string
  val sketch_goals_at: format -> int -> Toplevel.state -> string list
  val try_method: method option -> Toplevel.state -> int * bool * string * Toplevel.state
end;

structure Sketcher: SKETCHER =
struct

(* generally useful *)

val set_verbose = fold (fn bconf => Config.put bconf false)
  [show_markup, Printer.show_type_emphasis, show_types, show_sorts, show_consts];

fun sketch_term ctxt t = 
  Print.string_of_term ctxt t
  |> Library.enclose "\"" "\"";

fun sketch_typ ctxt T = 
  Print.string_of_type ctxt T
  |> Library.enclose "\"" "\"";

fun sketch_header thy_name imports st =
  let
    val thy = Toplevel.theory_of st;
    val merge = Library.union 
      (fn (str1, str2) => Pred.contains str1 str2 
        orelse Pred.contains str2 str1);
    val sep = "\n" ^ (Symbol.spaces 2);
    val imports' = 
      merge imports (map fst (Resources.imports_of thy))
      |> Ops.intersp [sep]
      |> Library.implode_space;
  in "theory " ^ thy_name ^ sep ^ "imports " ^ imports' ^ "\nbegin" end;


(* methods *)

type method = Method.text_range * Token.T list

fun sketch_method opt_m = case opt_m of 
  SOME (_,toks) => Print.coalesce_method_txt (map Token.unparse toks)
  | NONE => "-";


(* formats *)
(* TODO: add SUBGOAL and ASSMS_SHOW *)
datatype format = 
  LEMMAS of Path.T * Path.T
  | SHOW_IFS

fun init_indent_from format = (case format of LEMMAS _ => 0 | SHOW_IFS => 2);

fun make_proof_qed_skel indent fst_m_txt sketches = 
  let
    val sep = "\n" ^ Symbol.spaces indent;
    val skel = sketches
    |> space_implode (sep ^ "next\n")
    |> (fn skel => "proof" ^ fst_m_txt ^ "\n" ^ skel ^ "\n" ^ "qed");
  in skel end;

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

fun make_skeleton format indent m_txt sketches =
  (case format of 
    LEMMAS _ => make_proof_qed_skel indent m_txt sketches
    | SHOW_IFS => make_proof_qed_skel indent m_txt sketches)


(* goals *)

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

fun upd_context_with (var_typs, assms, concl) ctxt =
  let
    val fixes = map (fn (s, T) => (Binding.name s, SOME T, NoSyn)) var_typs
    val ctxt' = ctxt |> Variable.set_body false |> Proof_Context.add_fixes fixes |> snd
      handle ERROR _ =>
      ctxt |> Variable.set_body true |> Proof_Context.add_fixes fixes |> snd
  in ((var_typs, assms, concl), ctxt') end;

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
    val goal = if null fixes 
      then sketch_term (Config.put show_sorts true (Config.put show_types true ctxt)) concl
      else sketch_term ctxt concl;
  in (Option.map (add_ands indent) opt_fixes, 
    Option.map (add_ands indent) opt_assumes, 
    goal)
  end;

fun sketch_goal_as format indent ctxt (goal_num, goal_data) =
  let
    val ((fixes, assms, concl), ctxt') = upd_context_with goal_data ctxt;
    val (opt_fixes, opt_assumes, goal_str) = prepare_goal_data ctxt' indent (fixes, assms, concl);
    val formatter = get_formatter format indent goal_num;
  in formatter (opt_fixes, opt_assumes, goal_str) end;

fun sketch_goals_at format indent st =
  let            
    val ctxt = set_verbose (Toplevel.context_of st);
    val goals = Ops.enumerate (get_goals_at (Toplevel.proof_of st));
  in Par_List.map (sketch_goal_as format indent ctxt) goals end;


(* trying methods *)

fun try_method opt_m st =
  let
    val m_txt = sketch_method opt_m;
    val there_is_method = is_some opt_m;
    val (applied_m, st') = if there_is_method
      then 
        let
          val act = Actions.make_one (Toplevel.theory_of st) ("apply " ^ m_txt);
        in (case Ops.apply_with_timeout (Time.fromSeconds 10) (Actions.apply act) st 
          of Exn.Exn _ => (false, st) 
          | Exn.Res (st', _) => (true, st'))
        end
      else (false, st);
    val final_str = if Pred.no_subgoals st' 
      then if not there_is_method then "done" else "by " ^ m_txt
      else if not applied_m then "sorry" else "apply " ^ m_txt;
  in (length (get_goals_at (Toplevel.proof_of st')), applied_m, final_str, st') end;

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