(* 
  Mantainers: 
    Chengsong Tan -- c.tan[at]imperial[dot]ac[dot]uk

Note: Adapted from Sketch_and_Explore.thy by Florian Haftmann
*)

chapter \<open>Experimental commands \<^text>\<open>sketch\<close> and \<^text>\<open>explore\<close>\<close>

theory Super_Sketch
  imports Main \<comment> \<open>TODO: generalize existing sledgehammer functions to Pure\<close>
  keywords "sketch" "explore" "sketch_subgoals" "super_sketch" "super_sketch3" "super_sketch2b" "double_sketch" :: diag
begin


ML_file "../Super_Fix/ml/pred.ML"
ML_file "../Super_Fix/ml/ops.ML"
ML_file "../Super_Fix/ml/print.ML"
ML_file "../Super_Fix/ml/imports.ML"
ML_file "../Super_Fix/ml/get.ML"
ML_file "../Super_Fix/ml/seps.ML"
ML_file "../Super_Fix/ml/actions.ML"
ML_file "ml/Sledgehammer_Commands1.ML"
ML_file "../Super_Fix/ml/HammerAlt.ML"



ML \<open>
open ATP_Util
open ATP_Problem_Generate
open ATP_Proof
open ATP_Proof_Reconstruct
open Sledgehammer_Util
open Sledgehammer_Fact
open Sledgehammer_ATP_Systems
open Sledgehammer_Prover
open Sledgehammer_Prover_SMT
open Sledgehammer_Prover_Minimize
open Sledgehammer_MaSh
open Sledgehammer
open Sledgehammer_Commands1

open Subgoal
open Binding
\<close>


(*utility for removing "prefer i" from sledgehammer's generated proofs*)
ML \<open>
(* --- Remove "prefer i" from SH's suggested text --------------------------- *)
(*now moved into sledgehammer_commands.ml*)
\<close>

ML \<open>
val _ = Future.fork
val print_name = Token.print_name o Thy_Header.get_keywords';

fun createList(start, ending) = 
  if start = ending then []
  else start :: createList(start + 1, ending);

fun createList'(ending) =
  createList(1, ending + 1);

fun split_clause t =
  let
    val (fixes, horn) = funpow_yield (length (Term.strip_all_vars t)) Logic.dest_all_global t;
    val assms = Logic.strip_imp_prems horn;
    val concl = Logic.strip_imp_concl horn;
  in (fixes, assms, concl) end;

fun print_typ ctxt T =
  T
  |> Syntax.string_of_typ ctxt
  |> ATP_Util.maybe_quote ctxt;

fun print_term ctxt t =
  t
  |> singleton (Syntax.uncheck_terms ctxt)
  |> Sledgehammer_Isar_Annotate.annotate_types_in_term ctxt
  |> Print_Mode.setmp [] (Syntax.unparse_term ctxt #> Pretty.string_of)
  |> Sledgehammer_Util.simplify_spaces
  |> ATP_Util.maybe_quote ctxt;

fun eigen_context_for_statement (params, assms, concl) ctxt =
  let
    val fixes = map (fn (s, T) => (Binding.name s, SOME T, NoSyn)) params
    val ctxt' = ctxt |> Variable.set_body false |> Proof_Context.add_fixes fixes |> snd
      handle ERROR _ =>
      ctxt |> Variable.set_body true |> Proof_Context.add_fixes fixes |> snd
  in ((params, assms, concl), ctxt') end;

fun print_isar_skeleton ctxt indent keyword stmt =
  let
    val ((fixes, assms, concl), ctxt') = eigen_context_for_statement stmt ctxt;
    val prefix = replicate_string indent " ";
    val prefix_sep = "\n" ^ prefix ^ "    and ";
    val show_s = prefix ^ keyword ^ " " ^ print_term ctxt' concl;
    val if_s = if null assms then NONE
      else SOME (prefix ^ "  if " ^ space_implode prefix_sep
        (map (print_term ctxt') assms));
    val for_s = if null fixes then NONE
      else SOME (prefix ^ "  for " ^ space_implode prefix_sep
        (map (fn (v, T) => v ^ " :: " ^ print_typ ctxt T) fixes));
    val s = cat_lines ([show_s] @ map_filter I [if_s, for_s] @
      [prefix ^ "  " ^ (if is_none if_s then "" else "using that ") ^ "sorry"]);
  in
    s
  end;

fun print_skeleton ctxt indent keyword stmt =
  let
    val ((fixes, assms, concl), ctxt') = eigen_context_for_statement stmt ctxt;
    val prefix = replicate_string indent " ";
    val prefix_sep = "\n" ^ prefix ^ "  and ";
    val show_s = prefix ^ keyword ^ " " ^ print_term ctxt' concl;
    val assumes_s = if null assms then NONE
      else SOME (prefix ^ "assume " ^ space_implode prefix_sep
        (map (print_term ctxt') assms));
    val fixes_s = if null fixes then NONE
      else SOME (prefix ^ "fix " ^ space_implode prefix_sep
        (map (fn (v, T) => v ^ " :: " ^ print_typ ctxt T) fixes));
    val s = cat_lines (map_filter I [fixes_s, assumes_s] @ [show_s] @ [prefix ^ " sorry"]);
  in
    s
  end;

fun print_sketch ctxt method_text clauses =
  "proof" ^ method_text :: separate "next" (map (print_skeleton ctxt 2 "show") clauses) @ ["qed"];




fun print_exploration ctxt method_text [clause] =
    ["proof -", print_isar_skeleton ctxt 2 "have" clause,
      "  then show ?thesis", "    by" ^ method_text, "qed"]
  | print_exploration ctxt method_text (clause :: clauses) =
    "proof -" :: print_isar_skeleton ctxt 2 "have" clause
      :: map (print_isar_skeleton ctxt 2 "moreover have") clauses
      @ ["  ultimately show ?thesis", "    by" ^ method_text, "qed"];

fun print_subgoal apply_line_opt (is_prems, is_for, is_sh) ctxt indent stmt =
  let
    val ((fixes, _, _), ctxt') = eigen_context_for_statement stmt ctxt;
    val prefix = replicate_string indent " ";
    val fixes_s =
      if not is_for orelse null fixes then NONE
      else SOME ("for " ^ space_implode " "
        (map (fn (v, _) => print_name ctxt' v) fixes));
    val premises_s = if is_prems then SOME "premises prems" else NONE;
    val sh_s = if is_sh then SOME "sledgehammer" else NONE;
    val subgoal_s = map_filter I [SOME "subgoal", premises_s, fixes_s]
      |> space_implode " ";
    val using_s = if is_prems then SOME "using prems" else NONE;
    val s = cat_lines (
      [subgoal_s]
      @ map_filter (Option.map (fn s => prefix ^ s)) [using_s, apply_line_opt, sh_s]
      @ [prefix ^ "sorry"]);
  in
    s
  end;

fun coalesce_method_txt [] = ""
  | coalesce_method_txt [s] = s
  | coalesce_method_txt (s1 :: s2 :: ss) =
      if s1 = "(" orelse s1 = "["
        orelse s2 = ")" orelse s2 = "]" orelse s2= ":"
      then s1 ^ coalesce_method_txt (s2 :: ss)
      else s1 ^ " " ^ coalesce_method_txt (s2 :: ss);

fun print_subgoals options apply_line_opt ctxt _ clauses =
  separate "" (map (print_subgoal apply_line_opt options ctxt 2) clauses) @ ["done"];

fun print_proof_text_from_state print (some_method_ref : ((Method.text * Position.range) * Token.T list) option) state =
  let
    val state' = state
      |> Proof.proof (Option.map fst some_method_ref)
      |> Seq.the_result ""

    val { context = ctxt, facts = _, goal } = Proof.goal state';

    val ctxt_print = fold (fn opt => Config.put opt false)
      [show_markup, Printer.show_type_emphasis, show_types, show_sorts, show_consts] ctxt

    val method_text = case some_method_ref of
        NONE => ""
      | SOME (_, toks) => " " ^ coalesce_method_txt (map Token.unparse toks);
        \<comment> \<open>TODO proper printing required\<close>
    val goal_props = Logic.strip_imp_prems (Thm.prop_of goal);
    val clauses = map split_clause goal_props;
    val lines = if null clauses then
      if is_none some_method_ref then ["  .."]
      else ["  by" ^ method_text]
      else print ctxt_print method_text clauses;
    val message = Active.sendback_markup_command (cat_lines lines);
  in
    (state |> tap (fn _ => Output.information message))
  end

fun print_super_isar_skeleton2b ctxt indent keyword stmt i state extra_method_ref extra_method_text  =
  let
    val ((fixes, assms, concl), ctxt') = eigen_context_for_statement stmt ctxt;
    val prefix = replicate_string indent " ";
      \<comment> \<open>TODO consider pre-existing indentation -- how?\<close>
    val prefix_sep = "\n" ^ prefix ^ "    and ";
    val show_s = prefix ^ keyword ^ " goal" ^ Int.toString i ^ ": " ^ print_term ctxt' concl;
(*
    val state_insert = (case m3ref of (SOME m3) =>  (Seq.the_result "" (Proof.apply m3 (Proof.prefer i state)))
                                         | NONE => state )*)
    val ngoals = subgoal_count state
    val state_simp = (case extra_method_ref of (SOME m2) =>  (Seq.the_result "" (Proof.apply m2 (Proof.prefer i state)))
                                         | NONE => Proof.prefer i state )
    val nsgoals = subgoal_count state_simp
    val done_or_nil = (if ngoals = 1 then "" else " done")
    val outcome_messages = (if ngoals > nsgoals then [("success", "apply " ^ extra_method_text ^ " (*good, solved without s/h*)")] else 
      Par_List.map (fn (st, txt) => let val p = my_hammer_away 1 st in (fst p, "apply " ^ txt ^ " " ^ Sledgehammer_Commands1.extract_one_liner_proof (snd p)) end) [(state_simp, extra_method_text) (*, (state_insert, m3txt)*)])
    val (retry_outcome, retry_message) = (find_first (fn ("success", _) => true | _ => false) outcome_messages) |> the_default ("failed", "sorry (*failed to find proof*)")
    val (retry_outcome1, retry_message1) = (if retry_outcome = "failed" then (let val sh = my_hammer_away i state in (fst sh, Sledgehammer_Commands1.extract_one_liner_proof (snd sh)) end) else (retry_outcome, retry_message))


    val message1 = (case retry_outcome1 of
        "success" =>   retry_message1 ^ done_or_nil  | 
        _ => "sorry (*failed to find proof*)")

    val inserted_ctxt = ctxt
    val ((inserted_fixes, inserted_assms, inserted_concl), inserted_ctxt') = eigen_context_for_statement stmt inserted_ctxt;
    val if_s = if null inserted_assms then NONE
      else SOME (prefix ^ "  if " ^ space_implode prefix_sep
        (map (fn t => print_term inserted_ctxt' t ) inserted_assms));
    val for_s = if null inserted_fixes then NONE
      else SOME (prefix ^ "  for " ^ space_implode prefix_sep
        (map (fn (v, T) => v ^ " :: " ^ print_typ inserted_ctxt T) inserted_fixes));

    val s = cat_lines ([show_s] @ map_filter I [if_s, for_s] @
      [ prefix ^  "  " ^ (if is_none if_s then "" else "using that ") ^ message1]);
  in
    s
  end;

fun hammer_maybe_twice i state =
  let
    val statei = Proof.prefer i state
    val (outcome_type_string, message) = my_hammer_away 1 statei;
    val (retry_outcome, retry_message) = (case outcome_type_string of "success" => (outcome_type_string, message) 
      | _ => my_verbose_hammer_away 1 statei 4)
  in (retry_outcome, retry_message) end;

fun generate_multiple_step_solving_text i state msplit_ref msplit_txt mreduce_ref mreduce_txt = 
  let 
    val state_subgoaled = (#2 o Subgoal.subgoal_cmd Binding.empty_atts NONE (false, [])) (Proof.prefer i state);
    val state_splitted = (case msplit_ref of (SOME m) =>  (Seq.the_result "" (Proof.apply m (state_subgoaled)))
                                         | NONE => state_subgoaled );

    val state_reduced = (case mreduce_ref of (SOME m) =>  (Seq.the_result "" (Proof.apply m (state_splitted)))
                                         | NONE => state_splitted );
    val sub_subgoals_num = (subgoal_count state_reduced);

    val _ = writeln ("sub_subgoals_num: " ^ Int.toString sub_subgoals_num);
    val string_pairs_list = (if sub_subgoals_num > 0 then (Par_List.map (fn j => hammer_maybe_twice j state_reduced) (createList(1, sub_subgoals_num + 1))) else []);
    val proof_text_list = map snd string_pairs_list;
    val proof_text_list = map ( Sledgehammer_Commands1.extract_one_liner_proof) proof_text_list
    val outcome_type_list = map fst string_pairs_list;
    val final_outcome = List.foldl (fn (s, acc) => if s = "success" andalso acc then true else false) true outcome_type_list;
    val done_or_nil = (if sub_subgoals_num = 1 then [] else [" done\n"])
    val text = (if final_outcome then cat_lines (([" apply " ^ msplit_txt ^ " apply " ^ mreduce_txt]) @ proof_text_list @ done_or_nil) 
        else cat_lines (([" apply " ^ msplit_txt ^ " apply " ^ mreduce_txt]) @ proof_text_list @ done_or_nil));
  in text end;
    
    

fun print_super_isar_skeleton3 ctxt indent keyword stmt i state extra_method_ref extra_method_text m3ref m3txt msplit_ref msplit_txt mreduce_ref mreduce_txt=
  let
    val ((fixes, assms, concl), ctxt') = eigen_context_for_statement stmt ctxt;
    val prefix = replicate_string indent " ";
      \<comment> \<open>TODO consider pre-existing indentation -- how?\<close>
    val prefix_sep = "\n" ^ prefix ^ "    and ";
    val show_s = prefix ^ keyword ^ " goal" ^ Int.toString i ^ ": " ^ print_term ctxt' concl;
    val if_s = if null assms then NONE
      else SOME (prefix ^ "  if " ^ space_implode prefix_sep
        (map (fn t => print_term ctxt' t ) assms));
    val for_s = if null fixes then NONE
      else SOME (prefix ^ "  for " ^ space_implode prefix_sep
        (map (fn (v, T) => v ^ " :: " ^ print_typ ctxt T) fixes));

    val total_count = subgoal_count state;
    val state_insert = (case m3ref of (SOME m3) =>  (Seq.the_result "" (Proof.apply m3 (Proof.prefer i state)))
                                         | NONE => Proof.prefer i state )
    val insert_count = subgoal_count state_insert;
    val (outcome_type_string, message) = (if insert_count < total_count then ("success", "Try this:        (>1.0s)") else ("failed", "must split subgoal"));
    val done_or_nil = (if insert_count < 2 then "" else "done")
    val message1 = (if outcome_type_string = "success" 
      then "apply " ^ m3txt ^ "(**)" ^  
           Sledgehammer_Commands1.extract_one_liner_proof message ^ done_or_nil 
      else generate_multiple_step_solving_text i state msplit_ref msplit_txt mreduce_ref mreduce_txt);


    val s = cat_lines ([show_s] @ map_filter I [if_s, for_s] @
      [ prefix ^  "  " ^ (if is_none if_s then "" else "using that ") ^ message1]);
  in
    s
  end;
\<close>


ML \<open>



(* remove time tags with second labels *)
fun strip_time_tags (s: string) =
  let
    val n = size s
    fun digit c = Char.isDigit c
    fun rd_digits i =
      if i < n andalso digit (String.sub (s, i)) then rd_digits (i+1) else i
    fun rd_spaces i =
      if i < n andalso Char.isSpace (String.sub (s, i)) then rd_spaces (i+1) else i
    (* 若从位置 i 起是 "(<num>(.<num>)?<space>*s)", 返回匹配结束位置；否则返回 ~1 *)
    fun try_at i =
      if i < n andalso String.sub (s, i) = #"(" then
        let
          val j1 = rd_digits (i+1)
          val j2 =
            if j1 < n andalso String.sub (s, j1) = #"." then rd_digits (j1+1) else j1
          val j3 = rd_spaces j2
          val j4 = if j3 < n andalso String.sub (s, j3) = #"s" then j3+1 else ~1
          val j5 = if j4 <> ~1 andalso j4 < n andalso String.sub (s, j4) = #")"
                   then j4+1 else ~1
        in j5 end
      else ~1
    fun loop i acc =
      if i >= n then String.implode (rev acc)
      else (case try_at i of
              ~1 => loop (i+1) (String.sub (s, i) :: acc)
            | j  => loop j acc)
  in
    loop 0 []
  end


(* 带叶子 solver 的版本：solver_ref / solver_txt 会在叶子与 SH 竞速 *)
fun ppt_simp ms state js indent solver_ref solver_txt adref adtxt =
(case ms of m1::ms_tl =>
  let
    val state'' =
      state |> (fn s =>  Seq.the_result "" (Proof.apply (fst m1) s))

    val { context = ctxt, facts = _, goal } = Proof.goal state''
    val ctxt_print = fold (fn opt => Config.put opt false)
      [show_markup, Printer.show_type_emphasis, show_types, show_sorts, show_consts] ctxt

    val method_text1 = ( " " ^ coalesce_method_txt (map Token.unparse (snd m1)))
    val goal_props = Logic.strip_imp_prems (Thm.prop_of goal)
    val clauses = map split_clause goal_props
    val tl_len = length ms_tl
    val goal_numbers_prefix = String.concatWith "_" (map (fn i => Int.toString i) js) ^ "_"

    fun pisk stmt i ms_tl =
      let
        val ((fixes, assms, concl), ctxt') = eigen_context_for_statement stmt ctxt_print
        val prefix = replicate_string indent " "
        val prefix_sep = "\n" ^ prefix ^ "    and "
        val show_s = prefix ^ "show goal" ^ goal_numbers_prefix ^ Int.toString i ^ ": " ^ print_term ctxt' concl
        val if_s = if null assms then NONE
          else SOME (prefix ^ "  if " ^ space_implode prefix_sep (map (fn t => print_term ctxt' t) assms))
        val for_s = if null fixes then NONE
          else SOME (prefix ^ "  for " ^ space_implode prefix_sep (map (fn (v,T) => v ^ " :: " ^ print_typ ctxt_print T) fixes))

        val state_i_moved_to_1 = Proof.prefer i state''
        val state_subgoaled = (#2 o Subgoal.subgoal_cmd Binding.empty_atts NONE (false, [])) state_i_moved_to_1
        val produced_proof =
          if tl_len > 0
          then ppt_simp ms_tl state_subgoaled (js@[i]) (indent+1) solver_ref solver_txt adref adtxt
          else ppt_simp ms_tl state_i_moved_to_1 (js@[i]) (indent+1) solver_ref solver_txt adref adtxt

        val line_end_if_not_last_layer = (if tl_len > 0 then "\n" else " ")
        val s = cat_lines ([show_s] @ map_filter I [if_s, for_s] @
          [ prefix ^ "  " ^ (if is_none if_s then "" else "using that" ^ line_end_if_not_last_layer) ^ produced_proof ])
      in s end

    val n = subgoal_count state''
    val t_start = Timing.start ()
    val parlist_or_sequential = (if tl_len = 0 orelse n <= 100 then Par_List.map else map)
    val whole =
      "proof" ^ method_text1 ::
      parlist_or_sequential (fn (stmt,i) => pisk stmt i ms_tl) (ListPair.zip (clauses, createList'(n)))
      @ ["qed"]
    val t_end = Timing.result t_start
    val _ = writeln (Timing.message t_end)

    val lines = if null clauses then (if is_none (SOME m1) then ["  .."] else ["  by" ^ method_text1]) else whole
    val raw_str = cat_lines lines
    val message = Active.sendback_markup_properties [] raw_str
  in message end

| [] =>
  (* 叶子：用“最后一个方法”与 SH 竞速；若没有方法则只跑 SH *)
  let
    val (outcome, msg) =
      Sledgehammer_Commands1.my_hammer_or_method_away 1 state solver_ref solver_txt adref adtxt
    val one = Sledgehammer_Commands1.extract_one_liner_proof msg
    val message1 =
      (if outcome = "success"
       then strip_time_tags one ^ " done"
       else "sorry (*failed to find proof*)")
  in message1 end)

fun ppt_main_simp ms state js indent msimp adsimp =
  let
    val solver_ref = fst msimp  (* Method.text_range = Method.text * Position.range *)
    val solver_txt =
      " " ^ coalesce_method_txt (map Token.unparse (snd msimp)) 
    val adref = fst adsimp  (* Method.text_range = Method.text * Position.range *)
    val adtxt =
      " " ^ coalesce_method_txt (map Token.unparse (snd adsimp)) 
  in
    (ppt_simp ms state js indent solver_ref solver_txt adref adtxt )
    |> (fn s => Output.information s)
  end

\<close>







ML \<open>



fun print_super_sketch2b group_size ctxt method_text1 clauses state method2_ref method_text2  =
  let 
    val n = subgoal_count state;
    val t_start = Timing.start ();                                           
    val s = "proof" ^ method_text1 :: Par_List.map (fn (stmt, i) => print_super_isar_skeleton2b ctxt 2 "show" stmt i state method2_ref method_text2) (ListPair.zip (clauses, createList'(n))) @ ["qed"]
    val t_end = Timing.result t_start;
  in
    writeln (Timing.message t_end);
    s
  end;

fun print_super_sketch3 group_size ctxt method_text1 clauses state method2_ref method_text2 m3ref m3txt msplit_ref msplit_txt mreduce_ref mreduce_txt =
  let 
    val n = subgoal_count state;
    val t_start = Timing.start ();
    val s = "proof" ^ method_text1 :: Par_List.map (fn (stmt, i) => print_super_isar_skeleton3 ctxt 2 "show" stmt i state method2_ref method_text2 m3ref m3txt msplit_ref msplit_txt mreduce_ref mreduce_txt) (ListPair.zip (clauses, createList'(n))) @ ["qed"]
    val t_end = Timing.result t_start;
  in
    writeln (Timing.message t_end);
    s
  end;




val sketch = print_proof_text_from_state print_sketch;

fun explore method_ref = print_proof_text_from_state print_exploration (SOME method_ref);

fun subgoals options method_ref =
  let
    val apply_line_opt = case method_ref of
        NONE => NONE
      | SOME (_, toks) => SOME ("apply " ^ coalesce_method_txt (map Token.unparse toks))
    val succeed_method_ref = SOME ((Method.succeed_text, Position.no_range), [])
  in
    print_proof_text_from_state (print_subgoals options apply_line_opt) succeed_method_ref
  end;

fun sketch_cmd some_method_text =
  Toplevel.keep_proof (K () o sketch some_method_text o Toplevel.proof_of)

fun explore_cmd method_text =
  Toplevel.keep_proof (K () o explore method_text o Toplevel.proof_of)

fun subgoals_cmd (modes, method_ref) =
  let
    val is_prems = not (member (op =) modes "noprems")
    val is_for = not (member (op =) modes "nofor")
    val is_sh = member (op =) modes "sh"
  in
    Toplevel.keep_proof (K () o subgoals (is_prems, is_for, is_sh) method_ref o Toplevel.proof_of)
  end





fun ppt ms state js indent =
(case ms of m1::ms_tl =>
  let
    val state'' = state 
          |> (fn s => (Seq.the_result "" (Proof.apply (fst m1) s)))
          
    val { context = ctxt, facts = _, goal } = Proof.goal state'';

    val ctxt_print = fold (fn opt => Config.put opt false)
      [show_markup, Printer.show_type_emphasis, show_types, show_sorts, show_consts] ctxt

    val method_text1 = case m1 of
         (_, toks) => " " ^ coalesce_method_txt (map Token.unparse toks);
    val goal_props = Logic.strip_imp_prems (Thm.prop_of goal);
    val clauses = map split_clause goal_props;
    val tl_len = length ms_tl;
    val goal_numbers_prefix = String.concatWith "_" (map (fn i => Int.toString i) (rev js)) ^ "_";

    fun pisk stmt i ms_tl =
      let
        val ((fixes, assms, concl), ctxt') = eigen_context_for_statement stmt ctxt_print;
        val prefix = replicate_string indent " ";
          \<comment> \<open>TODO consider pre-existing indentation -- how?\<close>
        val prefix_sep = "\n" ^ prefix ^ "    and ";
        val show_s = prefix ^ "show" ^ " goal" ^ goal_numbers_prefix ^ Int.toString i ^ ": " ^ print_term ctxt' concl;
        val if_s = if null assms then NONE
          else SOME (prefix ^ "  if " ^ space_implode prefix_sep
            (map (fn t => print_term ctxt' t ) assms));
        val for_s = if null fixes then NONE
          else SOME (prefix ^ "  for " ^ space_implode prefix_sep
            (map (fn (v, T) => v ^ " :: " ^ print_typ ctxt_print T) fixes));
    
        val state_i_moved_to_1 = Proof.prefer i state''
        val state_subgoaled = (#2 o 
          Subgoal.subgoal_cmd Binding.empty_atts NONE (false, [])) state_i_moved_to_1;
        val produced_proof = (if tl_len > 0 then ppt ms_tl state_subgoaled (i::js) (indent+1) else ppt ms_tl state_i_moved_to_1 (i::js) (indent+1))


        val line_end_if_not_last_layer = (if tl_len > 0 then "\n" else " ")
        val s = cat_lines ([show_s] @ map_filter I [if_s, for_s] @
          [ prefix ^  "  " ^ (if is_none if_s then "" else "using that" ^ line_end_if_not_last_layer) ^ produced_proof]);
      in
        s
      end;

        val n = subgoal_count state'';
        val t_start = Timing.start ();
        val parlist_or_sequential_list = (if tl_len = 0 orelse n <= 100 then Par_List.map else map);
        val whole_proof_of_this_goal = "proof" ^ method_text1 :: parlist_or_sequential_list (fn (stmt, i) => 
          pisk stmt i ms_tl) (ListPair.zip (clauses, createList'(n))) @ ["qed"]
        val t_end = Timing.result t_start;
        val _ = writeln (Timing.message t_end);
  


    val lines = if null clauses then
      if is_none (SOME m1) then ["  .."]
      else ["  by" ^ method_text1]
      else (whole_proof_of_this_goal);


    val lines = lines ;
    val raw_str = cat_lines lines;
    val message = Active.sendback_markup_properties [] (raw_str);
    (*val _ = writeFileln ("C:\\Users\\Chengsong\\Documents\\GitHub\\cxl-formalisation\\Results" ^ Context.theory_name {long=false} (Proof_Context.theory_of ctxt) ) raw_str; *)
  in
     message
  end
| [] => let
          val (outcome_type_string, message) = my_hammer_away (hd js) state;
          (*val done_or_nil = (if subgoal_count state'' < 2 then "" else "\ndone")*)
          val message1 = (if outcome_type_string = "success" 
                          then strip_time_tags (Hammer_Alt.extract_one_liner_proof' message) ^ " done" 
                          else "sorry (*failed to find sledgehammer proof*)");    
        in message1 end
)

(*(state |> tap (fn _ => Output.information message));*)
fun ppt_main ms state js indent = (ppt ms state js indent) |> (fn s => Output.information s)

fun print_proof_text_from_state_generate_oneliners2b print m1 m2  state =
  let
    (*val state' = Seq.the_result "" (Proof.proof (Option.map fst m1) state)*)

  
    val state'' = state 
          |> (fn s => (case Option.map fst m1 of SOME m => Seq.the_result "" (Proof.apply m s) | NONE => s))
          
    val { context = ctxt, facts = _, goal } = Proof.goal state'';

    val ctxt_print = fold (fn opt => Config.put opt false)
      [show_markup, Printer.show_type_emphasis, show_types, show_sorts, show_consts] ctxt

    val method_text1 = case m1 of
        NONE => ""
      | SOME (_, toks) => " " ^ coalesce_method_txt (map Token.unparse toks);
        \<comment> \<open>TODO proper printing required\<close>

    val method_ref2 = Option.map fst m2
    val method_text2 = case m2 of
        NONE => ""
      | SOME (_, toks) => " " ^ coalesce_method_txt (map Token.unparse toks);




    val goal_props = Logic.strip_imp_prems (Thm.prop_of goal);
    val clauses = map split_clause goal_props;

    val lines = if null clauses then
      if is_none m1 then ["  .."]
      else ["  by" ^ method_text1]
      else (print ctxt_print method_text1 clauses state'' method_ref2 method_text2);


    val lines = lines ;
    val raw_str = cat_lines lines;
    val message = Active.sendback_markup_properties [] (raw_str);
    (*val _ = writeFileln ("C:\\Users\\Chengsong\\Documents\\GitHub\\cxl-formalisation\\Results" ^ Context.theory_name {long=false} (Proof_Context.theory_of ctxt) ) raw_str;*)
  in
    (state |> tap (fn _ => Output.information message))
  end

fun print_proof_text_from_state_generate_oneliners3 print m1 m2 m3 msplit mreduce state =
  let
    (*val state' = Seq.the_result "" (Proof.proof (Option.map fst m1) state)*)

  
    val state'' = state 
          |> (fn s => (case Option.map fst m1 of SOME m => Seq.the_result "" (Proof.apply m s) | NONE => s))
          
    val { context = ctxt, facts = _, goal } = Proof.goal state'';

    val ctxt_print = fold (fn opt => Config.put opt false)
      [show_markup, Printer.show_type_emphasis, show_types, show_sorts, show_consts] ctxt

    val method_text1 = case m1 of
        NONE => ""
      | SOME (_, toks) => " " ^ coalesce_method_txt (map Token.unparse toks);
        \<comment> \<open>TODO proper printing required\<close>

    val method_ref2 = Option.map fst m2
    val method_text2 = case m2 of
        NONE => ""
      | SOME (_, toks) => " " ^ coalesce_method_txt (map Token.unparse toks);

    val method_ref3 = Option.map fst m3
    val method_text3 = case m3 of
        NONE => ""
      | SOME (_, toks) => " " ^ coalesce_method_txt (map Token.unparse toks);

    val method_ref4 = Option.map fst msplit
    val method_text4 = case msplit of
        NONE => ""
      | SOME (_, toks) => " " ^ coalesce_method_txt (map Token.unparse toks);

    val method_ref5 = Option.map fst mreduce
    val method_text5 = case mreduce of
        NONE => ""
      | SOME (_, toks) => " " ^ coalesce_method_txt (map Token.unparse toks);

    val goal_props = Logic.strip_imp_prems (Thm.prop_of goal);
    val clauses = map split_clause goal_props;

    val lines = if null clauses then
      if is_none m1 then ["  .."]
      else ["  by" ^ method_text1]
      else (print ctxt_print method_text1 clauses state'' 
        method_ref2 method_text2 
        method_ref3 method_text3 
        method_ref4 method_text4 
        method_ref5 method_text5);


    val lines = lines ;
    val raw_str = cat_lines lines;
    val message = Active.sendback_markup_properties [] (raw_str);
    (*val _ = writeFileln ("C:\\Users\\Chengsong\\Documents\\GitHub\\cxl-formalisation\\Results" ^ Context.theory_name {long=false} (Proof_Context.theory_of ctxt) ) raw_str; *)
  in
    (state |> tap (fn _ => Output.information message))
  end


val _ =
  Outer_Syntax.command \<^command_keyword>\<open>sketch\<close>
    "print sketch of Isar proof text after method application"
    (Scan.option (Scan.trace Method.parse) >> sketch_cmd);


val _ =
  Outer_Syntax.command \<^command_keyword>\<open>explore\<close>
    "explore proof obligations after method application as Isar proof text"
    (Scan.trace Method.parse >> explore_cmd);

val opt_modes =
  Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.!!! (Scan.repeat1 Parse.name --| \<^keyword>\<open>)\<close>)) [];

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>sketch_subgoals\<close>
    "sketch proof obligations as subgoals, applying a method and/or sledgehammer to each"
    (opt_modes -- Scan.option (Scan.trace Method.parse) >> subgoals_cmd);

val _ = 
  Outer_Syntax.command \<^command_keyword>\<open>super_sketch2b\<close>
    "print sketch of Isar proof text after method application, with oneliners auto generated"
    ((Scan.option (Scan.trace Method.parse) -- Scan.option (Scan.trace Method.parse) ) >> 
      (fn (meth1_ref, meth2_ref) =>
        Toplevel.keep_proof (fn state => 
          let 
            val pstate = Toplevel.proof_of state;
          in print_proof_text_from_state_generate_oneliners2b (print_super_sketch2b 1) meth1_ref meth2_ref pstate; () end)));



val _ = 
  Outer_Syntax.command \<^command_keyword>\<open>super_sketch3\<close>
    "print sketch of Isar proof text after method application, with oneliners auto generated"
    ((Scan.option (Scan.trace Method.parse) -- Scan.option (Scan.trace Method.parse) -- Scan.option (Scan.trace Method.parse) -- Scan.option (Scan.trace Method.parse) -- Scan.option (Scan.trace Method.parse)) >> 
      (fn ((((meth1_ref, meth2_ref), meth3_ref), msplit_ref), mreduce_ref) =>
        Toplevel.keep_proof (fn state => 
          let 
            val pstate = Toplevel.proof_of state;
          in print_proof_text_from_state_generate_oneliners3 (print_super_sketch3 1) meth1_ref meth2_ref meth3_ref msplit_ref mreduce_ref pstate; () end)));


val _ = 
  Outer_Syntax.command \<^command_keyword>\<open>super_sketch\<close>
    "print sketch of Isar proof text after method application, with oneliners auto generated"
    ( (Scan.trace Method.parse)  >> 
      (fn meth1_ref =>
        Toplevel.keep_proof (fn state => 
          let 
            val pstate = Toplevel.proof_of state;
          in ppt_main [meth1_ref] pstate [] 2; () end)));


val parse_adsimp = \<^keyword>\<open>[\<close> |-- (Scan.trace Method.parse) --| \<^keyword>\<open>]\<close>;



val _ = 
  Outer_Syntax.command \<^command_keyword>\<open>double_sketch\<close>
    "print sketch of Isar proof text after method application, with oneliners auto generated"
    ((Scan.repeat (Scan.trace Method.parse) -- parse_adsimp -- parse_adsimp) >> 
      (fn ((meths, msimp), adsimp) =>
        Toplevel.keep_proof (fn state => 
          let 
            val pstate = Toplevel.proof_of state;
          in ppt_main_simp meths pstate [] 2 msimp adsimp; () end)));
 


\<close>


end
