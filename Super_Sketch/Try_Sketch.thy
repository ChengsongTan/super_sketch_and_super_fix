theory Try_Sketch
  imports "Main"
  keywords "try_sketch" :: diag
begin


declare [[ML_print_depth = 4000000]]
ML_file "../../super_sketch_and_super_fix/Super_Fix/ml/pred.ML"
ML_file "../../super_sketch_and_super_fix/Super_Fix/ml/ops.ML"
ML_file "../../super_sketch_and_super_fix/Super_Fix/ml/print.ML"
ML_file "../../super_sketch_and_super_fix/Super_Fix/ml/imports.ML"
ML_file "../../super_sketch_and_super_fix/Super_Fix/ml/get.ML"
ML_file "../../super_sketch_and_super_fix/Super_Fix/ml/seps.ML"
ML_file "../../super_sketch_and_super_fix/Super_Fix/ml/actions.ML"
ML_file "../../super_sketch_and_super_fix/Super_Fix/ml/client.ML"
ML_file "../../super_sketch_and_super_fix/Super_Fix/ml/fixer.ML"


(* meta-data operations *)

ML \<open>
fun split_clause t =
  let
    val (fixes, horn) = funpow_yield (length (Term.strip_all_vars t)) Logic.dest_all_global t;
    val assms = Logic.strip_imp_prems horn;
    val concl = Logic.strip_imp_concl horn;
  in (fixes, assms, concl) end;

fun upd_context (var_typs, assms, concl) ctxt =
  let
    val fixes = map (fn (s, T) => (Binding.name s, SOME T, NoSyn)) var_typs
    val ctxt' = ctxt |> Variable.set_body false |> Proof_Context.add_fixes fixes |> snd
      handle ERROR _ =>
      ctxt |> Variable.set_body true |> Proof_Context.add_fixes fixes |> snd
  in ((var_typs, assms, concl), ctxt') end;

\<close>


(* generic string operations *)
ML \<open>

fun header_string thy_name imports state =
  let
    val thy = Toplevel.theory_of state;
    val merge = Library.union 
      (fn (str1, str2) => Pred.contains str1 str2 
        orelse Pred.contains str2 str1);
    val sep = "\n" ^ (Symbol.spaces 2);
    val imports' = 
      merge imports (map fst (Resources.imports_of thy))
      |> Ops.intersp [sep]
      |> Library.implode_space;
  in "theory " ^ thy_name ^ sep ^ "imports " ^ imports' ^ "\nbegin" end;

fun print_term ctxt t = 
  Print.string_of_term ctxt t
  |> Library.enclose "\"" "\"";

fun print_typ ctxt T = 
  Print.string_of_type ctxt T
  |> Library.enclose "\"" "\"";

fun add_ands indent strs = 
  let 
    val sep = "\n" ^ (Symbol.spaces (indent + 2)) ^ "  and ";
  in space_implode sep strs end;

fun prepare_data ctxt indent (fixes, assms, concl) = 
  let
    val opt_assumes = if null assms then NONE
      else SOME (map (print_term ctxt) assms);
    val opt_fixes = if null fixes then NONE
      else SOME (map (fn (v, T) => v ^ " :: " ^ print_typ ctxt T) fixes);
    val goal = print_term ctxt concl;
  in (
    Option.map (add_ands indent) opt_fixes, 
    Option.map (add_ands indent) opt_assumes, 
    goal)
  end;

\<close>

(* formatting operations *)
ML \<open>

(* TODO: add SUBGOAL and ASSMS_SHOW *)
datatype format_mode = 
  LEMMAS of Path.T * Path.T
  | SHOW_IFS

fun init_indent_of format = (case format of LEMMAS _ => 0 | SHOW_IFS => 2);

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
    | SHOW_IFS => (fn (opt_fixes, opt_assms, goal) =>
    let
      val sep = "\n" ^ (Symbol.spaces (indent + 2));
      val header = "show goal" ^ Value.print_int num ^ ": ";
      val fors = the_default "" (Option.map (curry (op ^) (sep ^ "for ")) opt_fixes);
      val ifs = the_default "" (Option.map (curry (op ^) (sep ^ "if ")) opt_assms);
      val shows = Symbol.spaces indent ^ header ^ goal;
      val sorry = if ifs = ""
        then sep ^ "  sorry" else sep ^ "using that" ^ sep ^ "sorry"
    in shows ^ ifs ^ fors ^ sorry end));

fun sketch_as format ctxt indent (goal_num, goal_data) =
  let
    val ((fixes, assms, concl), ctxt') = upd_context goal_data ctxt;
    val (opt_fixes, opt_assumes, goal) = prepare_data ctxt' indent (fixes, assms, concl);
    val formatter = get_formatter format indent goal_num;
  in formatter (opt_fixes, opt_assumes, goal) end;

\<close>

ML \<open>

val parse_methods = Parse.$$$ "[" |-- Parse.list1 Method.parse --| Parse.$$$ "]";

datatype sketch_mode = SORRYS | TRY0 | TRY | HAMMER

fun mode_of_str str =
  (case str of 
    "SORRYS" => SORRYS
    | "TRY0" => TRY0
    | "TRY" => TRY
    | "HAMMER" => HAMMER
    | another => raise Fail ("mode_of_str: unknown mode" ^ another));

val parse_mode = Parse.embedded >> mode_of_str;

fun fix_with_try0 st = 
  (case Try0.try0 (SOME (Time.fromSeconds 30)) [] (Toplevel.proof_of st) of 
    [] => "sorry"
    | {command, ...} :: _ => command);

fun fix_with_try st = 
  (case Try.try_tools (Toplevel.proof_of st) of
    SOME (_, outcome) => "by " ^ outcome
    | NONE => "sorry");

fun get_fixer mode =
  (case mode of
    SORRYS => (fn _ => fn _ => "sorry")
    | TRY0 => (fn _ => fix_with_try0)
    | HAMMER => (fn _ => Fixer.fix_with_hammer)
    | TRY => (fn _ => fix_with_try));

fun make_proof_qed_skel format first_mthd ctxt clauses =
  map (sketch_as format ctxt (init_indent_of format)) clauses
  |> space_implode "\nnext\n"
  |> (fn skel => "proof" ^ first_mthd ^ "\n" ^ skel ^ "\n" ^ "qed");

(* TODO: add behaviour of LEMMAS *)
fun print_proof mode format opt_mrange_toks state = 
  let
    val (opt_m, m_txt) = case opt_mrange_toks of 
      SOME (m,toks) => (SOME m, Fixer.coalesce_method_txt (map Token.unparse toks))
      | NONE => (NONE, "-");
    val prf_st = if is_some opt_m
      then state
        |> Toplevel.proof_of
        |> Proof.proof opt_m
        |> Seq.the_result ""
      else Toplevel.proof_of state;
    val {context = ctxt, facts = _, goal} = Proof.goal prf_st;
    val configs = [show_markup, Printer.show_type_emphasis, show_types, show_sorts, show_consts];
    val ctxt' = fold (fn bconf => Config.put bconf false) configs ctxt;
    val _ = Output.tracing "Producing goals to try..."
    val (count, clauses) = map split_clause (Logic.strip_imp_prems (Thm.prop_of goal))
      |> Ops.enum_count_from 1;
    val _ = Output.tracing ("Produced " ^ Value.print_int count ^ " goals.")
    val final_texts = (case format of
      LEMMAS (read_path, write_dir) => 
        (map (sketch_as SHOW_IFS ctxt' (init_indent_of format)) clauses
        |> Ops.intersp ["\nnext\n  "]
        |> (curry (op ::)) ("proof" ^ m_txt ^ "\n")) @ ["\n" ^ "qed"]
      | SHOW_IFS => 
        let
          val _ = Output.tracing "Making proof skeleton..."
          val skel_stacts = 
            make_proof_qed_skel format m_txt ctxt' clauses
            |> Actions.make (Toplevel.theory_of state)
            |> (fn acts => Actions.apply_all acts state);
          val results = if mode = SORRYS 
            then skel_stacts
            else Fixer.generic_repair_sorrys false (fn _ => fn _ => []) (get_fixer mode) skel_stacts;
          val get_texts = map (fn (act, _, _) => Actions.text_of act);
        in get_texts results end
    )
  in Library.space_implode "" final_texts end;

val _ = Outer_Syntax.command \<^command_keyword>\<open>try_sketch\<close>
  "Makes a proof-sketch and attempts intermediate subgoals."
  (parse_mode -- (Scan.option (Scan.trace Method.parse) ) >> 
    (fn (sketch_mode, opt_mrange_toks) =>
      Toplevel.keep_proof (fn st =>
        let
          val final_sketch = print_proof sketch_mode SHOW_IFS opt_mrange_toks st;
          val _ = Output.information (Active.sendback_markup_command final_sketch);
        in () end
      )
   ));
\<close>

(* example *)

lemma 
  assumes "\<forall>x. P x" and "\<forall>x. Q x" and "R"
  shows "\<And>a b. P a \<and> P b \<and> P c \<and> P d \<and> P e"
  using assms
  try_sketch SORRYS (intro conjI)
proof-
  show goal1: "P a \<and> P b \<and> P c \<and> P d \<and> P e"
    if "\<forall>x. P x"
      and "\<forall>x. Q x"
      and "R"
    for a :: "'a"
      and b :: "'a"
    using that
    oops


lemma length_upt: "length ([0 ..< n]) = n"
  (* try_sketch HAMMER (induct n) *)
proof(induct n)
  show goal1: "length [0..<0] = 0"
    by simp
next
  show goal2: "length [0..<Suc n] = Suc n"
    if "length [0..<n] = n"
    for n :: "nat"
    using that
    by fastforce
qed


end