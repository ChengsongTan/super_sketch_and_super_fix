(* 
  Mantainers: 
    Chengsong Tan -- c.tan[at]imperial[dot]ac[dot]uk

Note: Adapted from Sketch_and_Explore.thy by Florian Haftmann
*)

chapter \<open>Experimental commands \<^text>\<open>sketch\<close> and \<^text>\<open>explore\<close>\<close>

theory Super_Sketch
  imports Main \<comment> \<open>TODO: generalize existing sledgehammer functions to Pure\<close>
  keywords "sketch" "explore" "sketch_subgoals" "super_sketch" "super_sketch3" "super_sketch2b" "double_sketch" "double_sketch4" "meta_sketch" "meta_sketch2" :: diag
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

\<close>

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
fun writeFileln dir_str msg = 
  let 
    val dir = Path.explode dir_str;
    val file = dir
  in
    File.append file (msg ^ "\n")
  end;

val _ = writeFileln "$USER_HOME/Desktop/double4log/d4res.txt" "firstline"

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
    val parlist_or_sequential = (if tl_len = 0 orelse n <= 4 then Par_List.map else map)
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
    val one =  msg
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


fun ppt_simp4 ms state js indent
               solver_ref solver_txt
               adref adtxt
               rref rtxt
               first_split_add_rescue = 
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
    val gg = "goal" ^ goal_numbers_prefix

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
          then ppt_simp4 ms_tl state_subgoaled (js@[i]) (indent+1) solver_ref solver_txt adref adtxt rref rtxt first_split_add_rescue
          else ppt_simp4 ms_tl state_i_moved_to_1 (js@[i]) (indent+1) solver_ref solver_txt adref adtxt rref rtxt first_split_add_rescue

        val line_end_if_not_last_layer = (if tl_len > 0 then "\n" else " ")
        val s = cat_lines ([show_s] @ map_filter I [if_s, for_s] @
          [ prefix ^ "  " ^ (if is_none if_s then "" else "using that" ^ line_end_if_not_last_layer) ^ produced_proof ])
      in s end

    val n = subgoal_count state''
    val t_start = Timing.start ()
    val parlist_or_sequential = (if tl_len = 0 orelse n <= 1000 then Par_List.map else map)
    val whole =
      "proof" ^ method_text1 ::
      parlist_or_sequential (fn (stmt,i) => pisk stmt i ms_tl) (ListPair.zip (clauses, createList'(n)))
      @ ["qed"]
    val t_end = Timing.result t_start
    val _ = writeln (Timing.message t_end)

    val lines = if null clauses then (if is_none (SOME m1) then ["  .."] else ["  by" ^ method_text1]) else whole
    val raw_str = cat_lines lines
    val message = Active.sendback_markup_properties [] raw_str
    val { context = ctxt, facts = _, goal } = Proof.goal state;
    val _ =    
        writeFileln ("$USER_HOME/Desktop/double4log/d4_" ^ Context.theory_name {long=false} (Proof_Context.theory_of ctxt) ^ gg ^ ".txt" ) message;
  in ( message) end

| [] =>
  let
    (* 大 goal 编号：js 在顶层会变成 [i]，向下递归会扩张为 [i, ...]；取 hd 即可。 *)
    val big_i = (case js of [] => 1 | k :: _ => k)

    (* 从 first_split_add_rescue 里取第 big_i 个方法（1-based）；可能没有。 *)
    val (split_ref_opt, split_txt_opt) =
      if big_i <= length first_split_add_rescue then
        let
          val (mref, txt) = List.nth (first_split_add_rescue, big_i - 1)
        in (SOME ( mref), SOME txt) end
      else (NONE, NONE)

    val (outcome, msg) =
      Sledgehammer_Commands1.my_hammer_or_method_away4
        1 state
        solver_ref solver_txt
        adref adtxt
        (SOME rref) (SOME rtxt)
        split_ref_opt split_txt_opt

    val one = msg
    val message1 =
      (if outcome = "success"
       then strip_time_tags one ^ " done"
       else "sorry (*failed to find proof*)")
  in message1 end)


fun ppt_main_simp4 ms state js indent msimp adsimp rescue first_split_add_rescue =
  let
    val solver_ref = fst msimp
    val solver_txt = " " ^ coalesce_method_txt (map Token.unparse (snd msimp))
    val adref = fst adsimp
    val adtxt = " " ^ coalesce_method_txt (map Token.unparse (snd adsimp))
    val resref = fst rescue
    val restxt = " " ^ coalesce_method_txt (map Token.unparse (snd rescue))
  in
    (ppt_simp4 ms state js indent solver_ref solver_txt adref adtxt resref restxt first_split_add_rescue)
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
        val parlist_or_sequential_list = (if tl_len = 0 orelse n <= 4 then Par_List.map else map);
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




(* a unified type for reference to method
   
*)

fun mref_to_ref_txt (mr: (Method.text * Position.range) * Token.T list) : ((Method.text * Position.range) * string) =
  let
    val (mref, toks) = mr
    val txt = " " ^ coalesce_method_txt (map Token.unparse toks)
  in
    (mref, txt)
  end


fun ppt_main_simp4
      (ms) state js indent
      (msimp) (adsimp) (rescue)
      (first_split_add_rescue) =
  let
    val (solver_ref, solver_txt) = mref_to_ref_txt msimp
    val (adref,     adtxt)      = mref_to_ref_txt adsimp
    val (resref,    restxt)     = mref_to_ref_txt rescue

    (* 关键：列表里每个元素也要先展开成 (ref, txt) *)
    val first_split_add_rescue' =
      map mref_to_ref_txt first_split_add_rescue
    val { context = ctxt, facts = _, goal } = Proof.goal state;
  in
    (ppt_simp4 ms state js indent
               solver_ref solver_txt
               adref      adtxt
               resref     restxt
               first_split_add_rescue')
    |> (fn s =>  writeFileln ("$USER_HOME/Desktop/double4log/d4_" ^ Context.theory_name {long=false} (Proof_Context.theory_of ctxt) ) s)
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

val parse_adsimp_repeat = \<^keyword>\<open>[\<close> |-- (Scan.repeat (Scan.trace Method.parse)) --| \<^keyword>\<open>]\<close>;


val _ = 
  Outer_Syntax.command \<^command_keyword>\<open>double_sketch\<close>
    "print sketch of Isar proof text after method application, with oneliners auto generated"
    ((Scan.repeat (Scan.trace Method.parse) -- parse_adsimp -- parse_adsimp) >> 
      (fn ((meths, msimp), adsimp) =>
        Toplevel.keep_proof (fn state => 
          let 
            val pstate = Toplevel.proof_of state;
          in ppt_main_simp meths pstate [] 2 msimp adsimp; () end)));



val _ =
  Outer_Syntax.command \<^command_keyword>\<open>double_sketch4\<close>
    "print sketch via ppt_main_simp, then run method_away4 at leaf"
    ((Scan.repeat (Scan.trace Method.parse)        (* methods 列表：取第一个当 user method *)
      -- parse_adsimp                               (* msimp   —— 必填 *)
      -- parse_adsimp                               (* adsimp  —— 必填 *)
      -- parse_adsimp                               (* rescue  —— 必填 *)
      -- parse_adsimp_repeat                        (* first_split_add_rescue *)
      -- parse_adsimp_repeat                        (* list_cases_methods —— 新增 *)
      )
     >> (fn (((((meths, msimp), adsimp), rescue), first_split_add_rescue), list_cases_methods) =>
       Toplevel.keep_proof (fn state =>
         let
           val pstate = Toplevel.proof_of state
         in
           (* NOTE: ppt_main_simp 现在多一个必填参数 rescue *)
           ppt_main_simp4 meths pstate [] 2 msimp adsimp rescue first_split_add_rescue;
           ()
         end)))



\<close>

ML \<open>
(* ======== Strategy 解析（与 v5 对应）======== *)
(* parse a method together with its original tokens *)
(* parse a method together with its original tokens *)
val parse_mref : ((Method.text * Position.range) * Token.T list) parser =
  Scan.trace Method.parse

(* 支持两种“有硬终止符”的写法：(...) 或 [...] *)
val parse_mref_paren : ((Method.text * Position.range) * Token.T list) parser =
  \<^keyword>\<open>(\<close> |-- parse_mref --| \<^keyword>\<open>)\<close>

val parse_mref_brack : ((Method.text * Position.range) * Token.T list) parser =
  \<^keyword>\<open>[\<close> |-- parse_mref --| \<^keyword>\<open>]\<close>

(* 与 Sledgehammer_Commands1.ML 中一致 *)
type ms_kind = Sledgehammer_Commands1.ms_kind
type ms_strategy = Sledgehammer_Commands1.ms_strategy

(* 只允许“有界”的 splitter，避免 intro 吞不进 conjI 的歧义 *)

(* 取文本串 *)
fun txt_of_mref (_, toks) =
  " " ^ coalesce_method_txt (map Token.unparse toks)

(* 允许 “(m)” 或直接 “m” *)
val parse_one_mref = parse_mref_paren || parse_mref

(* 策略关键字 *)
fun parse_kind_kw () : ms_kind parser =
  Parse.name >>
    (fn "PLAIN" => MS_PLAIN
      | "SH"    => MS_SH
      | "TRY0"  => MS_TRY0
      | s => error ("Unknown strategy kind: " ^ s))

(* PLAIN m 1 / SH (m args) 2 / TRY0 m 3 *)
(* ===== 强制方法与顺序整数之间有分隔符，避免 Method.parse 吞掉整数 ===== *)

(* 允许用逗号、双冒号或 @ 作为分隔符 *)
val parse_ord_sep : unit parser =
     (Parse.$$$ "," >> K ())
  || (Parse.$$$ "::" >> K ())
  || (Parse.$$$ "@" >> K ())

(* PLAIN m , 1  /  SH (m args) , 2  /  TRY0 m :: 3  /  也可用 @ 3 *)
val parse_strategy : ms_strategy parser =
  parse_kind_kw () -- parse_one_mref -- parse_ord_sep -- Parse.int >>
   (fn (((k, mref), ()), ord) =>
      let val mtxt = txt_of_mref mref
      in (k, fst mref, mtxt, ord) end)

val parse_strategy_list : ms_strategy list parser =
  let
    val item = parse_strategy --| Scan.option (Parse.$$$ ",")
  in
    \<^keyword>\<open>[\<close> |-- Scan.repeat item --| \<^keyword>\<open>]\<close> >> map I
  end

(* ( splitter , [ per-subgoal strategies ... ] ) *)
type compound = ((Method.text * Position.range) * Token.T list) * ms_strategy list

val parse_splitter_in_compound : ((Method.text * Position.range) * Token.T list) parser =
      parse_mref_paren
  ||  parse_mref_brack
  ||  parse_mref   (* 这里安全：后面紧跟 逗号 作为硬终止符 *)

val parse_compound : compound parser =
  Args.parens (parse_splitter_in_compound --| Parse.$$$ "," -- parse_strategy_list)


(* ======== 元驱动：meta_sket ch 的递归求解 ======== *)

(* 叶子：把策略列表丢给 v5，统一做净化并加 done *)
fun leaf_solve (strats : ms_strategy list) (state : Proof.state) : string =
  let
    val (outc, msg) =
      Sledgehammer_Commands1.my_hammer_or_method_away5 1 state strats
    val one = msg
    val msg' =
      (if outc = "success"
       then strip_time_tags one ^ " done"
       else "sorry (*meta_sketch: no proof found*)")
  in msg' end

(* meta 驱动：像 ppt_simp4 一样生成 Isar 骨架，但每层只应用一个 splitter，
   递归下去时按“第 i 个子目标”把该层的第 i 个策略前缀进最终策略列表。 *)
fun ppt_meta (cmps : compound list)
             (final_strats : ms_strategy list)
             (state : Proof.state)
             (js : int list) (* 仅用于编号显示 *)
             (indent : int) : string =
(case cmps of
  [] => leaf_solve final_strats state
| ((splitter_mref, layer_strats) :: tl) =>
  let
    val state' = Seq.the_result "" (Proof.apply (fst splitter_mref) state)
    val { context = ctxt, goal, ... } = Proof.goal state'
    val ctxt_print = fold (fn opt => Config.put opt false)
      [show_markup, Printer.show_type_emphasis, show_types, show_sorts, show_consts] ctxt
    val goal_props = Logic.strip_imp_prems (Thm.prop_of goal)
    val clauses = map split_clause goal_props
    val n = subgoal_count state'

    val method_text =
      " " ^ coalesce_method_txt (map Token.unparse (snd splitter_mref))
    val goal_numbers_prefix =
      String.concatWith "_" (map (fn i => Int.toString i) js) ^ "_"
    val prefix = replicate_string indent " "
    val prefix_sep = "\n" ^ prefix ^ "    and "

    fun pisk (stmt, i) =
      let
        val ((fixes, assms, concl), ctxt') = eigen_context_for_statement stmt ctxt_print
        val show_s = prefix ^ "show goal" ^ goal_numbers_prefix ^ Int.toString i ^ ": " ^
                     print_term ctxt' concl
        val if_s = if null assms then NONE
                   else SOME (prefix ^ "  if " ^
                              space_implode prefix_sep (map (fn t => print_term ctxt' t) assms))
        val for_s = if null fixes then NONE
                    else SOME (prefix ^ "  for " ^
                               space_implode prefix_sep (map (fn (v,T) => v ^ " :: " ^ print_typ ctxt_print T) fixes))

        val state_i = Proof.prefer i state'
        val state_sub = (#2 o Subgoal.subgoal_cmd Binding.empty_atts NONE (false, [])) state_i

        (* 取该层第 i 个策略（若有）做前缀 *)
        val ith_prefix =
          (if i <= length layer_strats then [List.nth (layer_strats, i - 1)] else [])
        val produced =
          ppt_meta tl (ith_prefix @ final_strats) state_sub (js @ [i]) (indent + 1)

        val line_end = (if null tl then " " else "\n")
        val s = cat_lines ([show_s] @ map_filter I [if_s, for_s] @
                [prefix ^ "  " ^ (if is_none if_s then "" else "using that" ^ line_end) ^ produced])
      in s end

    val body =
      "proof" ^ method_text ::
      Par_List.map pisk (ListPair.zip (clauses, createList'(n))) @ ["qed"]
    val raw_str = cat_lines body
    val message = Active.sendback_markup_properties [] raw_str
  in message end)

fun ppt_main_meta (cmps : compound list)
                  (final_strats : ms_strategy list)
                  (state : Proof.state) =
  ppt_meta cmps final_strats state [] 2
  |> (fn s => Output.information s)

(* ======== meta_sketch ======== *)

(* 一个用方括号包起来的 compound 列表 *)
val parse_compound_list : compound list parser =
  \<^keyword>\<open>[\<close> |-- Parse.list1 parse_compound --| \<^keyword>\<open>]\<close>

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>meta_sketch\<close>
    "meta-level sketch: compose splitters and per-subgoal strategies; then race leaf strategies (v5)."
    ((parse_compound_list -- parse_strategy_list) >>
      (fn (cmps, finals) =>
         Toplevel.keep_proof (fn st =>
           let val pstate = Toplevel.proof_of st
           in ppt_main_meta cmps finals pstate end)))

\<close>

ML \<open>

(* === Meta-sketch: generic splitter + per-subgoal strategies + final strategies === *)

open Sledgehammer_Commands1

(* ---------- Parsers ---------- *)

(* ms_kind parser *)
val parse_ms_kind =
  Parse.name >> (fn s =>
    (case s of
       "PLAIN" => MS_PLAIN
     | "SH"    => MS_SH
     | "TRY0"  => MS_TRY0
     | _ => error ("Unknown strategy kind: " ^ s)));

(* Parse a method + remember its pretty text *)
val parse_method_with_text =
  Scan.trace Method.parse >> (fn (mref, toks) =>
    let val mtxt = " " ^ String.concat (map Token.unparse toks)
    in (mref, mtxt) end);

(* One strategy: KIND <method> , <nat> *)
val parse_one_strategy =
  parse_ms_kind -- parse_method_with_text -- (Parse.$$$ "," |-- Parse.nat)
  >> (fn ((k, (mref, mtxt)), ord) => (k, mref, mtxt, ord) : ms_strategy);

(* [ strategy, strategy, ... ]  — 用 enum1 正规的逗号分隔 *)
(* [ strategy, strategy, ... ] — 允许空表 [] *)
val parse_strategy_block =
  Parse.$$$ "[" |--
    Scan.optional (Parse.enum1 "," parse_one_strategy) []
  --| Parse.$$$ "]";


(* ( <splitter> , [ per-subgoal strategies ] )
   注意：这里不要把 <splitter> 再包一层括号！ *)
val parse_compound_entry =
  Parse.$$$ "(" |-- parse_method_with_text --| Parse.$$$ "," -- parse_strategy_block --| Parse.$$$ ")";

(* [ ( ... ), ( ... ), ... ] *)
val parse_compound_list =
  Parse.$$$ "[" |-- Parse.enum1 "," parse_compound_entry --| Parse.$$$ "]";

(* Final strategy list *)
val parse_final_strategies = parse_strategy_block;

(* ---------- Engine ---------- *)

fun nth_strategy i (xs : ms_strategy list) : ms_strategy option =
  if i <= length xs then SOME (List.nth (xs, i - 1)) else NONE

fun meta_worker (compounds : (((Method.text * Position.range) * string) * ms_strategy list) list)
                (finals    : ms_strategy list)
                (state     : Proof.state)
                (js        : int list)
                (indent    : int) : string =
  (case compounds of
     [] =>
       let
         (* 在 Subgoal.subgoal_cmd 聚焦过后，这里总是子目标 1 *)
         val (outc, txt) = my_hammer_or_method_away5 1 state finals
       in
         if outc = "success" then strip_time_tags txt ^ " done"
         else "sorry (*meta_sketch: no proof found*)"
       end
   | (((split_ref, split_txt), per_sub_strats) :: tail) =>
       let
         val state' = Seq.the_result "" (Proof.apply split_ref state)
         val {context = ctxt, goal, ...} = Proof.goal state'
         val ctxt_print = fold (fn opt => Config.put opt false)
           [show_markup, Printer.show_type_emphasis, show_types, show_sorts, show_consts] ctxt

         val goal_props = Logic.strip_imp_prems (Thm.prop_of goal)
         val clauses = map split_clause goal_props
         val n = subgoal_count state'

         val goal_numbers_prefix = String.concatWith "_" (map (fn i => Int.toString i) js) ^ "_"

         fun for_one_subgoal (stmt, i) =
           let
             val ((fixes, assms, concl), ctxt') = eigen_context_for_statement stmt ctxt_print
             val prefix = replicate_string indent " "
             val prefix_sep = "\n" ^ prefix ^ "    and "
             val show_s = prefix ^ "show goal" ^ goal_numbers_prefix ^ Int.toString i ^ ": " ^ print_term ctxt' concl
             val if_s = if null assms then NONE
                        else SOME (prefix ^ "  if " ^ space_implode prefix_sep (map (fn t => print_term ctxt' t) assms))
             val for_s = if null fixes then NONE
                         else SOME (prefix ^ "  for "
                                    ^ space_implode prefix_sep (map (fn (v,T) => v ^ " :: " ^ print_typ ctxt_print T) fixes))

             val st_pref = Proof.prefer i state'
             val st_sub  = (#2 o Subgoal.subgoal_cmd Binding.empty_atts NONE (false, [])) st_pref

             (* 只给第 i 个子目标前缀本层的第 i 条策略（若有） *)
             val finals' =
               (case nth_strategy i per_sub_strats of
                  NONE => finals
                | SOME s => s :: finals)

             val text_leaf = meta_worker tail finals' st_sub (js @ [i]) (indent + 2)

             val line_end_if_not_last_layer = if null tail then " " else "\n"
             val s = cat_lines ([show_s]
                                @ map_filter I [if_s, for_s]
                                @ [prefix ^ "  " ^ (if is_none if_s then "" else "using that" ^ line_end_if_not_last_layer) ^ text_leaf])
           in s end

         val lines =
           if null clauses
           then ["  by" ^ split_txt]
           else "proof" ^ split_txt :: Par_List.map for_one_subgoal (ListPair.zip (clauses, createList'(n))) @ ["qed"]

         val raw_str = cat_lines lines
       in Active.sendback_markup_properties [] raw_str end);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>meta_sketch2\<close>
    "generic meta sketch: (splitter \<times> per-subgoal strategies)* \<Rightarrow> leaf strategies \<Rightarrow> run v5 engine"
    (parse_compound_list -- parse_final_strategies
     >> (fn (compounds, finals) =>
       Toplevel.keep_proof (fn st =>
         let
           val pstate = Toplevel.proof_of st
           val msg = meta_worker compounds finals pstate [] 2
         in
           Output.information msg
         end)))
\<close>
(*
design of meta_sketch2. 
meta_sketch takes two parameters: a list of "compound methods", and a list of final solving strategies.

A solving strategy is a datatype which represents a combination of solvers and methods to prove a theorem.
It currently can have three types: PLAIN, SH, and TRY0. These types mean whether meta_sketch
should try to prove a goal with the method only (PLAIN), apply the method and then sledgehammer it (SH),
or apply the method and invoke try0 on it.  Each type takes two parameters: the method to be used and the relative
order the strategy should be called with. Strategies with the same order should be run concurrently and
raced against each other until one proof is found (in which case the rest of the strategies are cancelled)
or all strategies have failed or timed out.
The tool meta_sketch determines ways it needs to try to solve a goal from a list of solving strategies.
For instance, the strategy list
[SH (insert assms) 1, PLAIN simp 1, SH auto 2, TRY0 (cases "reqs1 T") 3]
tries to solve the goal by first forking two threads, with one running a plain simp method, and the second
running sledgehammer after applying the method "insert assms". Whichever thread returned first with success
will be recorded and cause the other to cancel. If both failed or timed out, the second order strategy is invoked,
which applies auto first and then runs sledgehammer on the remaining goals, if any remaining.
If this failed, then the third set of strategies are run, for our example this involves only the last
strategy TRY0 (cases "reqs1 T") 3.

Each compound method is a pair, the first half of which is a "splitter" method and the second half
a list of solving strategies.
A splitter method splits the current goal into easier to solve subgoals, and for each subgoal assigns
the corresponding strategy from the list. The index of the goal used to take the strategy from the list.
The strategies list can be left empty, meaning that no customised proving strategies are needed for different
subgoals splitted by the current splitter.

In each recursive call of ppt_simp4, the function takes the head of the compound method list,
splits the goal using the splitter of that head, and for each subgoal
prepends the indexed method from the pairing strategy list (if any) to the final solving strategy list.

When the compound method list finally becomes empty, the leaf call to ppt_simp is reached. It
tries to solve the leaf subgoals with the list of final solving strategies by my_hammer_or_method_away5.
It is very similar to version 4, but only accepts a list of strategies rather than quite a few methods.

The previous call to double_sketch4 now becomes:


  meta_sketch 
(intro conjI, [
  SH (cases "reqs1 T") 3
  SH (cases "program1 T") 3
  SH (cases "reqs1 T") 3
  SH (cases "reqs1 T") 3
  SH (cases "reqs1 T") 3
  SH (cases "reqs1 T") 3
  SH (cases "reqs1 T") 3
  SH (cases "snpresps1 T") 3
  SH (cases "snpresps1 T") 3
  SH (cases "htddatas1 T") 3
  ......
] )  
(intro impconjI, []) 
[PLAIN simp 1, SH (insert assms, unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) 1, SH auto 2] 

with meta_sketch.
Implement this for me. This should be done most simply with 2 steps: first developing my_hammer_or_method_away5
Only after my_hammer_or_method_away5 behaves the same as version 4 with the same strategy list should we now
develop meta_sketch and invoke it with my_hammer_or_method_away5.
Note that my...5 must follow the concurrent control flow exactly as that of my_hammer_or_method_away4 so that 
it doesn't get stuck.meta_sketch takes two parameters: a list of "compound methods", and a list of final solving strategies.

A solving strategy is a datatype which represents a combination of solvers and methods to prove a theorem.
It currently can have three types: PLAIN, SH, and TRY0. These types mean whether meta_sketch
should try to prove a goal with the method only (PLAIN), apply the method and then sledgehammer it (SH),
or apply the method and invoke try0 on it.  Each type takes two parameters: the method to be used and the relative
order the strategy should be called with. Strategies with the same order should be run concurrently and
raced against each other until one proof is found (in which case the rest of the strategies are cancelled)
or all strategies have failed or timed out.
The tool meta_sketch determines ways it needs to try to solve a goal from a list of solving strategies.
For instance, the strategy list
[SH (insert assms) 1, PLAIN simp 1, SH auto 2, TRY0 (cases "reqs1 T") 3]
tries to solve the goal by first forking two threads, with one running a plain simp method, and the second
running sledgehammer after applying the method "insert assms". Whichever thread returned first with success
will be recorded and cause the other to cancel. If both failed or timed out, the second order strategy is invoked,
which applies auto first and then runs sledgehammer on the remaining goals, if any remaining.
If this failed, then the third set of strategies are run, for our example this involves only the last
strategy TRY0 (cases "reqs1 T") 3.

Each compound method is a pair, the first half of which is a "splitter" method and the second half
a list of solving strategies.
A splitter method splits the current goal into easier to solve subgoals, and for each subgoal assigns
the corresponding strategy from the list. The index of the goal used to take the strategy from the list.
The strategies list can be left empty, meaning that no customised proving strategies are needed for different
subgoals splitted by the current splitter.

In each recursive call of ppt_simp4, the function takes the head of the compound method list,
splits the goal using the splitter of that head, and for each subgoal
prepends the indexed method from the pairing strategy list (if any) to the final solving strategy list.

When the compound method list finally becomes empty, the leaf call to ppt_simp is reached. It
tries to solve the leaf subgoals with the list of final solving strategies by my_hammer_or_method_away5.
It is very similar to version 4, but only accepts a list of strategies rather than quite a few methods.

The previous call to double_sketch4 now becomes:


  meta_sketch 
(intro conjI, [
  SH (cases "reqs1 T") 3
  SH (cases "program1 T") 3
  SH (cases "reqs1 T") 3
  SH (cases "reqs1 T") 3
  SH (cases "reqs1 T") 3
  SH (cases "reqs1 T") 3
  SH (cases "reqs1 T") 3
  SH (cases "snpresps1 T") 3
  SH (cases "snpresps1 T") 3
  SH (cases "htddatas1 T") 3
  ......
] )  
(intro impconjI, []) 
[PLAIN simp 1, SH (insert assms, unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) 1, SH auto 2] 

with meta_sketch.
Implement this for me. This should be done most simply with 2 steps: first developing my_hammer_or_method_away5
Only after my_hammer_or_method_away5 behaves the same as version 4 with the same strategy list should we now
develop meta_sketch and invoke it with my_hammer_or_method_away5.
Note that my...5 must follow the concurrent control flow exactly as that of my_hammer_or_method_away4 so that 
it doesn't get stuck. *)

end
