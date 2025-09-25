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

fun upd_context_with (var_typs, assms, concl) ctxt =
  let
    val fixes = map (fn (s, T) => (Binding.name s, SOME T, NoSyn)) var_typs
    val ctxt' = ctxt |> Variable.set_body false |> Proof_Context.add_fixes fixes |> snd
      handle ERROR _ =>
      ctxt |> Variable.set_body true |> Proof_Context.add_fixes fixes |> snd
  in ((var_typs, assms, concl), ctxt') end;

val make_verbose = fold (fn bconf => Config.put bconf false)
  [show_markup, Printer.show_type_emphasis, show_types, show_sorts, show_consts];
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

fun sketch_as format indent st (goal_num, goal_data) =
  let
    val ctxt' = make_verbose (Toplevel.context_of st);
    val ((fixes, assms, concl), ctxt'') = upd_context_with goal_data ctxt';
    val (opt_fixes, opt_assumes, goal) = prepare_data ctxt'' indent (fixes, assms, concl);
    val formatter = get_formatter format indent goal_num;
  in formatter (opt_fixes, opt_assumes, goal) end;

fun make_proof_qed_skel first_mthd = 
  space_implode "\nnext\n" 
  #> (fn skel => "proof" ^ first_mthd ^ "\n" ^ skel ^ "\n" ^ "qed");
\<close>

(* sketching operations *)

ML \<open>

datatype sketch_mode = 
  SORRYS 
  | TRY0 of (Method.text_range * Token.T list) list
  | TRY of (Method.text_range * Token.T list) list
  | HAMMER of (Method.text_range * Token.T list) list

fun mode_of_str str ms =
  (case str of 
    "SORRYS" => SORRYS
    | "TRY0" => TRY0 ms
    | "TRY" => TRY ms
    | "HAMMER" => HAMMER ms
    | another => raise Fail ("mode_of_str: unknown mode" ^ another));

val parse_methods = \<^keyword>\<open>[\<close> |-- Parse.list (Scan.trace Method.parse) --| \<^keyword>\<open>]\<close>;

val parse_mode = (Parse.embedded -- (Scan.option parse_methods))
  >> (fn (mode_txt, opt_ms) => 
    mode_of_str mode_txt (case opt_ms of NONE => [] | SOME ms' => ms')
  );

fun get_fixer mode =
  (case mode of
    SORRYS => (fn _ => fn _ => "sorry")
    | TRY0 _ => (fn _ => Fixer.fix_with_try0)
    | HAMMER _ => (fn _ => Fixer.fix_with_hammer)
    | TRY _ => (fn _ => Fixer.fix_with_try));

fun get_methods mode =
  (case mode of
    SORRYS => []
    | TRY0 ms => ms
    | HAMMER ms => ms
    | TRY ms => ms);

\<close>

(* try_sketch main *)

ML \<open>

(* TODO: add behaviour of LEMMAS *)
fun sketch_prove_all_at st (mode:sketch_mode) format m_txt sketches =
  (case format of
      LEMMAS (read_path, write_dir) => 
        (sketches
        |> Ops.intersp ["\nnext\n  "]
        |> (curry (op ::)) ("proof" ^ m_txt ^ "\n")) @ ["\n" ^ "qed"]
      | SHOW_IFS => 
        let
          val skel_stacts = 
            make_proof_qed_skel m_txt sketches
            |> Actions.make (Toplevel.theory_of st)
            |> (fn acts => Actions.apply_all acts st);
          val results = (case mode of 
            SORRYS => skel_stacts
            | mode => Fixer.generic_repair_sorrys false 
              (fn _ => fn _ => []) (get_fixer mode) (map SOME (get_methods mode)) skel_stacts);
          val get_texts = map (fn (act, _, _) => Actions.text_of act);
        in get_texts results end
    );

fun try_sketch mode format opt_m st = 
  let
    val m_txt = Fixer.get_method_txt opt_m;
    val _ = Output.tracing "Producing goals to try..."
    val (_, goals) = Fixer.get_goals_after opt_m st;
    val final_texts = if null goals 
      then if m_txt = "-" then ["  done"] else ["  by " ^ m_txt]
      else if length goals = 1 then [(get_fixer mode) [] st]
      else let
        val _ = Output.tracing "Making proof skeleton..."
        val sketches = Par_List.map (sketch_as format (init_indent_of format) st) goals;
      in sketch_prove_all_at st mode format m_txt sketches end;
  in Library.space_implode "" final_texts end;

val _ = Outer_Syntax.command \<^command_keyword>\<open>try_sketch\<close>
  "Makes a proof-sketch and attempts intermediate subgoals."
  (parse_mode -- (Scan.option (Scan.trace Method.parse)) >> 
    (fn (sketch_mode, opt_m0) =>
      Toplevel.keep_proof (fn st =>
        let
          val final_sketch = try_sketch sketch_mode SHOW_IFS opt_m0 st;
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
  try_sketch TRY0[-, (intro allI), simp] (intro conjI)
proof-
  show goal1: "P a \<and> P b \<and> P c \<and> P d \<and> P e"
    if "\<forall>x. P x"
      and "\<forall>x. Q x"
      and "R"
    for a :: "'a"
      and b :: "'a"
    using that
    oops

lemma True
  apply simp
  try_sketch TRY
  done

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