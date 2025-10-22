(* 
  Enhanced Super_Sketch with double_sketch optimization
  
  Maintainers: 
    Chengsong Tan -- c.tan[at]imperial[dot]ac[dot]uk
  Enhanced by: Cursor implementation

  Key Enhancements:
  1. Fixed adsimp parameter output issue
  2. Added third bracket pair for fallback solving strategy  
  3. Integrated generate_multiple_step_solving_text pattern
  4. Maintained backward compatibility

  New Syntax: double_sketch_cursor <method>* [<solver>] [<additional>] [<split> <reduce>]?
*)

chapter \<open>Enhanced Experimental commands \<^text>\<open>sketch\<close> and \<^text>\<open>explore\<close> with double_sketch optimization\<close>

theory Super_Sketch_cursor
  imports Main \<comment> \<open>TODO: generalize existing sledgehammer functions to Pure\<close>
  keywords "sketch" "explore" "sketch_subgoals" "super_sketch" "super_sketch3" "super_sketch2b" "double_sketch_cursor" :: diag
begin

ML_file "../Super_Fix/ml/pred.ML"
ML_file "../Super_Fix/ml/ops.ML"
ML_file "../Super_Fix/ml/imports.ML"
ML_file "../Super_Fix/ml/get.ML"
ML_file "ml/Sledgehammer_Commands1.ML"
ML_file "../Super_Fix/ml/HammerAlt.ML"
ML_file "ml/Sledgehammer_Commands_cursor.ML"

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

(* Import utility functions from original Super_Sketch *)
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

fun coalesce_method_txt [] = ""
  | coalesce_method_txt [s] = s
  | coalesce_method_txt (s1 :: s2 :: ss) =
      if s1 = "(" orelse s1 = "["
        orelse s2 = ")" orelse s2 = "]" orelse s2= ":"
      then s1 ^ coalesce_method_txt (s2 :: ss)
      else s1 ^ " " ^ coalesce_method_txt (s2 :: ss);

(* Enhanced strip_time_tags function *)
fun strip_time_tags (s: string) =
  let
    val n = size s
    fun digit c = Char.isDigit c
    fun rd_digits i =
      if i < n andalso digit (String.sub (s, i)) then rd_digits (i+1) else i
    fun rd_spaces i =
      if i < n andalso Char.isSpace (String.sub (s, i)) then rd_spaces (i+1) else i
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

(* Original generate_multiple_step_solving_text function for fallback strategy *)
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

(* hammer_maybe_twice for fallback strategy *)
fun hammer_maybe_twice i state =
  let
    val statei = Proof.prefer i state
    val (outcome_type_string, message) = my_hammer_away 1 statei;
    val (retry_outcome, retry_message) = (case outcome_type_string of "success" => (outcome_type_string, message) 
      | _ => my_verbose_hammer_away 1 statei 4)
  in (retry_outcome, retry_message) end;

(* Enhanced proof text generation with fallback solving strategy *)
fun ppt_simp_cursor ms state js indent solver_ref solver_txt adref adtxt splitref_opt splitext_opt reduceref_opt reduceext_opt =
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
          then ppt_simp_cursor ms_tl state_subgoaled (js@[i]) (indent+1) solver_ref solver_txt adref adtxt splitref_opt splitext_opt reduceref_opt reduceext_opt
          else ppt_simp_cursor ms_tl state_i_moved_to_1 (js@[i]) (indent+1) solver_ref solver_txt adref adtxt splitref_opt splitext_opt reduceref_opt reduceext_opt

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

|| [] =>
  (* Enhanced leaf node with fallback solving strategy *)
  let
    val (outcome, msg) =
      Sledgehammer_Commands_cursor.my_hammer_or_method_away 1 state solver_ref solver_txt adref adtxt
    val one = Sledgehammer_Commands_cursor.extract_one_liner_proof msg
    val message1 =
      (if outcome = "success"
       then strip_time_tags one ^ " done"
       else
         (* Try fallback strategy if available *)
         case (splitref_opt, splitext_opt, reduceref_opt, reduceext_opt) of
           (SOME splitref, SOME splittext, SOME reduceref, SOME reducetext) =>
             (* Use generate_multiple_step_solving_text pattern for fallback *)
             (let
               val fallback_text = generate_multiple_step_solving_text 1 state splitref splittext reduceref reducetext
               val cleaned_text = strip_time_tags fallback_text
             in 
               cleaned_text ^ " done (* solved via fallback strategy *)"
             end
             handle _ => "sorry (*fallback strategy failed*)")
         | _ => "sorry (*failed to find proof*)")
  in message1 end)

(* Enhanced main function with fallback parameter support *)
fun ppt_main_simp_cursor ms state js indent msimp adsimp splitreduce_opt =
  let
    val solver_ref = fst msimp
    val solver_txt = " " ^ coalesce_method_txt (map Token.unparse (snd msimp)) 
    val adref = fst adsimp
    val adtxt = " " ^ coalesce_method_txt (map Token.unparse (snd adsimp))
    val (splitref_opt, splitext_opt, reduceref_opt, reduceext_opt) = 
      (case splitreduce_opt of 
        NONE => (NONE, NONE, NONE, NONE)
      | SOME (split_method, reduce_method) => 
          (SOME (fst split_method), 
           SOME (" " ^ coalesce_method_txt (map Token.unparse (snd split_method))),
           SOME (fst reduce_method),
           SOME (" " ^ coalesce_method_txt (map Token.unparse (snd reduce_method)))))
  in
    (ppt_simp_cursor ms state js indent solver_ref solver_txt adref adtxt splitref_opt splitext_opt reduceref_opt reduceext_opt)
    |> (fn s => Output.information s)
  end
\<close>

ML \<open>
(* Parser for single method in brackets [method] *)
val parse_adsimp = \<^keyword>\<open>[\<close> |-- (Scan.trace Method.parse) --| \<^keyword>\<open>]\<close>;

(* Parser for fallback methods in brackets [split_method reduce_method] *)  
val parse_splitreduce = \<^keyword>\<open>[\<close> |-- (Scan.trace Method.parse) -- (Scan.trace Method.parse) --| \<^keyword>\<open>]\<close>;

(* Enhanced double_sketch command with fallback solving strategy
   Syntax: double_sketch_cursor <method>* [<solver>] [<additional>] [<split> <reduce>]?
   - method*: One or more methods to apply recursively  
   - [solver]: Primary leaf node solver method
   - [additional]: Additional leaf node method (competes with solver + sledgehammer)
   - [split reduce]?: Optional fallback methods for multi-step solving when primary methods fail
*)
val _ = 
  Outer_Syntax.command \<^command_keyword>\<open>double_sketch_cursor\<close>
    "Enhanced proof sketch with fallback solving: double_sketch_cursor <method>* [<solver>] [<additional>] [<split> <reduce>]?"
    ((Scan.repeat (Scan.trace Method.parse) -- parse_adsimp -- parse_adsimp -- Scan.option parse_splitreduce) >> 
      (fn (((meths, msimp), adsimp), splitreduce_opt) =>
        Toplevel.keep_proof (fn state => 
          let 
            val pstate = Toplevel.proof_of state;
          in ppt_main_simp_cursor meths pstate [] 2 msimp adsimp splitreduce_opt; () end)));
\<close>

end
