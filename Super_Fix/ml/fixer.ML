(* 
  Mantainers: 
    Chengsong Tan -- c.tan[at]imperial[dot]ac[dot]uk
    Jonathan Julián Huerta y Munive -- huertjon[at]cvut[dot]cz

Main implementation of super_fix's algorithm
*)

signature FIXER =
sig
  val log_fold_list: ('a -> 'b -> 'b list) -> 'b -> 'a list -> 'b list
  val turn_by_to_apply: Proof.context -> Actions.T -> string
  val fix_with_method: Sketcher.method option -> Toplevel.state -> string
  val fix_with_sketch: Sketcher.format -> int -> (Toplevel.state -> string)
    -> Sketcher.method option -> Toplevel.state -> string
  val fix_with_llm: int -> (int * Actions.stact) list -> Toplevel.state -> string
  val fix_with_hammer: Toplevel.state -> string
  val fix_with_try0: Toplevel.state -> string
  val fix_with_try: Toplevel.state -> string
  val generic_repair_sorrys: bool
    -> ((int * Actions.stact) list -> int -> 'a list) 
    -> Toplevel.state
    -> ('a list -> Toplevel.state -> string) 
    -> Sketcher.method option list
    -> Actions.stact list
    -> Actions.stact list
  datatype T = 
    SORRYS of Sketcher.method list
    | TRY0 of Sketcher.method list
    | TRY of Sketcher.method list
    | HAMMER of Sketcher.method list
    | LLM of Sketcher.method list
  val string_of: T -> string
  val parse: T parser
  val build: T -> (int * Actions.stact) list -> Toplevel.state -> string
  val get_methods: T -> Sketcher.method list
  val repair_sorrys: T -> Actions.stact list -> Actions.stact list
  val process_all: {err_timeout_in_secs: int} -> Actions.T list -> Actions.stact list
  val fix_end_to_end: {fixer: T} -> theory -> string -> unit
end;


structure Fixer: FIXER =
struct


fun log_fold_list _ _ [] = []
  | log_fold_list f s (x :: xs) = 
    let 
      val vs = f x s 
    in vs @ log_fold_list f (List.last vs) xs end;

(* Operations with methods *)

fun fix_with_method opt_m st = #3 (Sketcher.try_method opt_m st)

fun fix_with_some_method_in ms st =
  let
    fun try_next_method m (proved, opt_str_proof) = 
      if proved then (proved, opt_str_proof)
      else let 
        val (goal_count, _, str, _) = Sketcher.try_method m st;
        val proved' = goal_count = 0;
      in if proved' then (proved', SOME str)
        else (proved', opt_str_proof) end;
  in fold try_next_method ms (false, NONE) end;


(* Sketching operations *)

fun fix_with_sketch format indent handler1 opt_m st =
  let
    val sep = Symbol.spaces indent;
    val m_txt = Sketcher.sketch_method opt_m;
    val (num_goals, applied_m, fst_str, st') = Sketcher.try_method opt_m st;
    val final_text = if num_goals = 0
      then sep ^ fst_str
      else if num_goals = 1 
        then if applied_m then fst_str ^ "\n" ^ sep ^ (handler1 st')
        else sep ^ (handler1 st')
      else let
        val sketches = Sketcher.sketch_goals_at format (indent+2) st';
      in Sketcher.make_skeleton format indent m_txt sketches end
  in final_text end;


(* Generic repair *)

local

fun add_next_to_prove 
  more_builder 
  (id, (act', st', _)) 
  ((old_count, old_act, old_st), to_proves) 
  = if Actions.on_kind (Pred.is "sorry") act'
  then
    let
      val latest_relevant_st_act = (old_count + 1, act', st');
      val i' = if null to_proves then 1 else (#2 (hd to_proves)) + 1;
      val more = more_builder id;
    in (latest_relevant_st_act, (id, i', old_act, old_st, more) :: to_proves) end
  else
    let
      val latest_relevant_st_act =
        if Toplevel.is_proof st' 
          andalso not (Actions.does_something (Toplevel.theory_of st') act')
        then (old_count, old_act, old_st)
        else (old_count, act', st')
    in (latest_relevant_st_act, to_proves) end;

fun count_find_sorrys more_builder fst_state id_stacts =
  let
    val _ = Output.tracing "Retrieving sorry-locations...";
    val ((count, _, _), rev_sorry_stacts) = 
      ((0, Actions.void, fst_state), [])
      |> fold (add_next_to_prove (more_builder id_stacts)) id_stacts;
    val count_str = Value.print_int count;
  in (count_str, rev rev_sorry_stacts) end;

(* fun apply_fixer goal_count_str goal_num fixer st =
  let
    val goal_no_str = "goal " ^ Value.print_int i ^ " of " ^ goal_count_str;
    val _ = Output.tracing 
      ("Trying " ^ goal_no_str ^ ": " ^ Actions.text_of act);
    val start_time = Time.now ();
    val (proved, opt_proof) = fix_with_some_method_in ms st;
    val result = if proved then the opt_proof else fixer more st;
    val elapsed = Value.print_int (Time.toMilliseconds (Time.now () - start_time));
    val _ = Output.tracing 
      ("Finished processing " ^ goal_no_str ^ " (" ^ elapsed ^ " ms)");
  in () end; *)

fun apply_fixer sequential count_str fixer ms to_fix_stacts =
  let
    val mmap = if sequential then map else Par_List.map
    val fixed_strs = mmap (fn (id, i, act, st, more) =>
      if not (Toplevel.is_proof st) 
      then (Output.warning ("Found 'sorry' not at proof state: " ^ Actions.text_of act); (id, "sorry"))
      else
      let
        val goal_no_str = "goal " ^ Value.print_int i ^ " of " ^ count_str;
        val _ = Output.tracing 
          ("Trying " ^ goal_no_str ^ ": " ^ Actions.text_of act);
        val start_time = Time.now ();
        val (proved, opt_proof) = fix_with_some_method_in ms st;
        val result = if proved then the opt_proof else fixer more st;
        val elapsed = Value.print_int (Time.toMilliseconds (Time.now () - start_time));
        val _ = Output.tracing 
          ("Finished processing " ^ goal_no_str ^ " (" ^ elapsed ^ " ms)");
      in (id, result) end) to_fix_stacts;
  in fixed_strs end;

fun add_fixes_without_ids fixed_strs fst_state id_stacts =
  let
    val (repaired, unmodified) = fold
      (fn (id, proof_txt) => fn (so_far, remaining) => 
        let
          val (seen, opt_stact, nexts) = Pred.trisect (fn (id',_) => id' = id) remaining;
          val stacts' = (case opt_stact of 
            NONE => []
            | SOME (_, (_, st, _)) => 
              let
                val last_st = if null seen 
                  then fst_state
                  else #2 (snd (Ops.last seen));
              in Actions.make (Toplevel.theory_of st) proof_txt
              |> (fn acts => Actions.timed_apply_all {timeout_in_secs=90} acts last_st)
              end
            )
          val so_far' = so_far @ map snd seen @ stacts';
        in (so_far', nexts) end
      ) fixed_strs ([], id_stacts)
  in repaired @ map snd unmodified end;

in

(* TODO: make more efficient *)
fun generic_repair_sorrys sequential 
  (more_builder: (int * Actions.stact) list -> int -> 'a list)
  fst_state fixer ms act_st_errs =
  let
    val id_stacts = Ops.enumerate act_st_errs;
    val (count_str, pre_sorry_stacts) = count_find_sorrys more_builder fst_state id_stacts;
    val fixed_strs = apply_fixer sequential count_str fixer ms pre_sorry_stacts;
  in add_fixes_without_ids fixed_strs fst_state id_stacts end;

end

(* Operations for LLMs *)

fun make_parseable txt =
  let
    val backslash = "\\";
    val new_line = "\n";
    val quote = "\"";
    val str_quote = backslash ^ quote;
    val isa_quote = backslash ^ "<";
  in Ops.replace_all quote (str_quote) txt
    |> Ops.replace_all isa_quote (backslash ^ isa_quote)
    |> Ops.replace_all new_line "\\n"
    |> Library.enclose quote quote
  end;

fun get_proof_so_far id_stacts id = Pred.take_while (fn (n, _) => n <= id) id_stacts
  |> rev
  |> Pred.take_while (fn (_, (_, st, _)) => Toplevel.is_proof st)
  |> rev;

fun make_llm_text prf_so_far st =
  let
    val prf_so_far_att =
      prf_so_far
      |> map (fn (_:int, (a, _:Toplevel.state, _:Runtime.error list)) => Actions.text_of a)
      |> Library.space_implode "\n"
      |> make_parseable
      |> Pretty.str |> Print.pretty_json_elem "proof_so_far";
    val usr_st_att = 
      Get.user_state {break_lines=false} st
      |> make_parseable
      |> Pretty.str |> Print.pretty_json_elem "user_state";
    val prf_data =
      Print.pretty_json_attribs false "{" "}" 0 [usr_st_att, prf_so_far_att]
      |> Print.string_of_pretty;
  in prf_data end;

fun turn_by_to_apply ctxt act =  
  let
    val mk_toks = Get.tokens {filtered=true} ctxt;
    val untoks = Sketcher.coalesce_method_txt o map Token.unparse;
    val no_by_txt = unprefix "by" (Actions.text_of act);
    (* adding a `by` at the end to make the parers work correctly *)
    val toks_to_parse = mk_toks (no_by_txt ^ " by"); 
    val untoked_txt = untoks toks_to_parse;
    val opt_parsed = try (Method.parse -- Scan.option Method.parse) toks_to_parse;
    val result = (case opt_parsed of 
      SOME ((_, opt_m2), rest_toks) => (case opt_m2 of 
        SOME _ => let
            val m1_rest_txt = untoks (snd (Method.parse toks_to_parse));
            val m2_txt = unsuffix (untoks rest_toks) m1_rest_txt;
            val m1_txt = unsuffix m1_rest_txt untoked_txt;
          in "apply " ^ m1_txt ^ "\n  apply " ^ m2_txt end
        | NONE => "apply " ^ (unsuffix (untoks rest_toks) untoked_txt))
      | NONE => "apply" ^ no_by_txt)
  in result end;

(* decides whether the by-suggestions are (partially) correct *)
fun do_next_from_llm act' (finished, last_st, resp_so_far) =
  if finished then (finished, last_st, resp_so_far)
  else if Actions.on_kind (Pred.is "by") act'
  then let 
    val thy = Toplevel.theory_of last_st;
    val ctxt = Toplevel.context_of last_st;
    val new_acts = Actions.make thy (turn_by_to_apply ctxt act');
    val _ = Output.tracing ("Turned into '" ^ implode (map Actions.text_of new_acts) ^ "'")
    val st_acts = Actions.timed_apply_all {timeout_in_secs=10} new_acts last_st;
    fun build_next (a', s', es') (proved, so_far) =
      if proved then (proved, so_far)
      else if Pred.no_subgoals s' then (true, so_far @ [(a', s', es')])
      else if null es' then (proved, so_far @ [(a', s', es')])
      else (proved, so_far)
    val (proved, pre_stacts) = fold build_next st_acts (false, []);
    fun recover stacts = 
      Actions.make_one thy ("by" ^ (unprefix "apply" (Actions.text_of (#1 (hd stacts)))))
      |> (fn act => Actions.apply_all [act] last_st);
    fun get_last_st stacts = #2 (Ops.last stacts);
    val result = if null pre_stacts 
        then (finished, last_st, resp_so_far)
      else if length pre_stacts < length st_acts
        then if not proved 
          then (finished, get_last_st pre_stacts, resp_so_far @ pre_stacts)
          else (true, get_last_st pre_stacts, resp_so_far @ (recover pre_stacts))
      else if not proved 
        then (finished, get_last_st pre_stacts, resp_so_far @ pre_stacts)
      else (true, get_last_st pre_stacts, resp_so_far @ (Actions.apply_all [act'] last_st))
    in result end
  else let
      val (_, st', errs') = hd (Actions.timed_apply_all {timeout_in_secs=10} [act'] last_st);
    in if null errs' 
      then (Pred.no_subgoals st', st', resp_so_far @ [(act', st', errs')])
      else (finished, last_st, resp_so_far)
    end;

fun mk_sorry_idd_stacts st = 
  Ops.enumerate (Actions.apply_all (Actions.make (Toplevel.theory_of st) "sorry") st)

fun llm_dfs max_depth proved (depth, prf_so_far, last_st) =
  if proved then prf_so_far
  else if depth > max_depth then prf_so_far @ mk_sorry_idd_stacts last_st
  else let
    val prf_data = make_llm_text prf_so_far last_st;
    val _ = Client.communicate prf_data;
    val llm_response = Client.get_last_response ();
    val result = (case llm_response of
      SOME response => 
        let
          val thy = Toplevel.theory_of last_st;
          val depth_report = "at depth " ^ Value.print_int depth;
          val _ = Output.tracing ("Trying suggestion '" ^ response ^ "' " ^ depth_report)
          val response_acts =
            Actions.make thy response
            |> filter (not o Actions.is_malformed)
          val (proved', st', final_stacts) = 
            fold do_next_from_llm response_acts (false, last_st, []);
        in llm_dfs max_depth proved' (depth + 1, prf_so_far @ Ops.enumerate final_stacts, st') end
      | NONE => prf_so_far)
  in result end;

fun fix_with_llm max_depth prf_so_far st =
  let
    val prf_so_far' = llm_dfs max_depth false (1, prf_so_far, st);
  in implode (map (fn (_, (a, _, _)) => Actions.text_of a) prf_so_far') end;

fun repair_sorrys_with_llm ms stacts =
  let
    val _ = Client.connect_to_server 5006;
    val result = generic_repair_sorrys true get_proof_so_far (Toplevel.make_state NONE) (fix_with_llm 1) ms stacts;
    val _ = Client.disconnect ();
  in result end;


(* Operations for Sledgehammer *)

val hammer_silence_state =
  Proof.map_contexts (Try0.silence_methods false #> Config.put SMT_Config.verbose false);

val remove_hammer_time = String.explode
  #> rev 
  #> Pred.drop_until' (fn c => (case Char.fromCString "(" of SOME d => c = d | _ => false))
  #> rev
  #> String.implode;

fun extract_str_proof input_str =
  if Pred.contains "timeout" input_str orelse Pred.contains "timed out" input_str
  then "sorry (*" ^ input_str ^ "*)"
  else (if Pred.contains " ms)" input_str 
    orelse Pred.contains " s)" input_str
    orelse Pred.contains "(> " input_str
    then remove_hammer_time input_str else input_str)
  |> (fn mid_str => if Pred.contains "Try this:" mid_str then Library.unprefix "Try this:" mid_str else mid_str)
  |> Ops.unprefix_unsufix " ";

fun apply_hammer params st =
  Toplevel.proof_of st
  |> hammer_silence_state
  |> (Sledgehammer.run_sledgehammer 
    params 
    Sledgehammer_Prover.Normal 
    NONE
    1
    Sledgehammer_Fact.no_fact_override
  );

(* fun apply_timed_hammer timeout_in_secs params st = 
  Ops.apply_with_timeout 
    (Time.fromSeconds timeout_in_secs) 
    (apply_hammer params); *)

fun fix_with_hammer st =
  let
    val thy = Toplevel.theory_of st;
    val params = Sledgehammer_Commands.default_params thy []
      (* [("max_proofs", "1"),("try0", "false"), ("timeout", "15")] *);
    val (proved, (_, txt)) = apply_hammer params st;
    (* val (proved, (_, txt)) = (case apply_timed_hammer 90 params st of
      Exn.Exn _ => (false, (Sledgehammer.SH_TimeOut, "Timeout"))
      | Exn.Res res => res); *)
    val (output, origin) = if proved 
      then (extract_str_proof (Print.yxml_to_string txt), "hammer proof: ")
      else ("sorry", "no hammer proof: ");
    val _ = Output.tracing ("Adopted " ^ origin ^ "'" ^ output ^ "'")
  in output end;


(* TODO: make all fixers report whether they succeeded with a boolean *)
fun fix_with_try0 st = 
  (case Try0.try0 (SOME (Time.fromSeconds 30)) [] (Toplevel.proof_of st) of 
    [] => "sorry"
    | {command, ...} :: _ => command);

fun fix_with_try st = 
  (case Try.try_tools (Toplevel.proof_of st) of
    SOME (_, outcome) => "by " ^ outcome
    | NONE => "sorry");


(* Fixer operations *)
fun string_all errs = Library.space_implode " " (map (fn ((_, txt), _) => txt) errs);

fun process_all {err_timeout_in_secs=t} acts =
  let
    (* Handling "Failed to refine any pending goal" *)
    fun is_refine_mssg ((_, txt), _) = Pred.contains "Failed to refine any pending goal" txt;
    fun is_refine (act, errs) = exists is_refine_mssg errs
      andalso (member (op =) ["have", "hence", "show", "thus"] (Actions.kind_of act));
    fun fix_refine_goal st act' =
      let
        val thy = Toplevel.theory_of st;
        val ctxt = Toplevel.context_of st;
        val prf = Toplevel.proof_of st;
        val prf_goals = #goal (Proof.goal prf);
        val (objs, _) = Logic.strip_horn (Thm.prop_of prf_goals);
        val fix = if null objs
          then []
          else let
            val nxt_goal = hd objs; (* ideally we would find the objective most similar
              to the original action, and not the head *)
            val splitted = Pred.group_by 
              (fn c => str c = "\"") 
              (String.explode (Actions.text_of act'))
            val _ = if null splitted then Output.error_message "empty splitted" else ();
            val declaration = splitted |> hd |> String.implode;
            val new_act = Actions.make_one thy 
              (declaration ^ " " ^ (Sketcher.sketch_term ctxt nxt_goal));
            val _ = Output.tracing ("Fixed '" ^ Actions.text_of act' ^ "'")
            val _ = Output.tracing ("  to '"  ^ Actions.text_of new_act ^ "'")
            val (new_st, new_err) = Actions.apply new_act st;
          in [(new_act, new_st, new_err)] end
       in fix end

    (* Handling proof timeouts *)
    val timeout = Time.fromSeconds t
    val might_timeout = Actions.on_kind (Pred.is "apply")
      andf Actions.on_text (
        Pred.contains "smt" 
        orf Pred.contains "metis" 
        orf Pred.contains "simp");
    fun is_timeout errs = exists (fn ((_, err_str), _) => Pred.contains "imeout" err_str) errs;
    fun fix_using_sorry st =
      let
        val thy = Toplevel.theory_of st;
        val new_act = Actions.make_one thy "sorry";
        val (new_st, new_err) = Actions.apply new_act st;
      in [(new_act, new_st, new_err)] end

    (* Handling incorrectly placed done's after a by *)
    fun is_illegal_app_mssg ((_, txt), _) 
      = Pred.contains "Illegal application of proof" txt;
    fun is_failed_finished_mssg ((_, txt), _) 
      = Pred.contains "Failed to finish" txt;
    fun is_done_in_bad_ctxt_mssg ((_, txt), _) 
      = Pred.contains "Bad context for command \"done\"" (Print.yxml_to_string txt);
    val wrong_done_cmmnd_cases = [
      is_illegal_app_mssg, 
      is_failed_finished_mssg,
      is_done_in_bad_ctxt_mssg]
    fun is_ill_app_done (act, errs) 
      = exists (Pred.disjunct wrong_done_cmmnd_cases) errs
        andalso (Pred.is "done" (Actions.kind_of act))

    (* Handling non timed-out bad Sledgehammer proofs *)
    fun is_failed_mthd_mssg ((_, txt), _) = 
      Pred.contains "Failed to apply proof method" txt 
      orelse Pred.contains "terminated abnormally" txt
      orelse Pred.contains "Undefined fact:" txt;
    fun is_failed_mthd (act, errs) = exists is_failed_mthd_mssg errs
      andalso Actions.on_text (
        Pred.contains "smt" 
        orf Pred.contains "metis" 
        orf Pred.contains "apply") act;

    (* Handling incomplete proofs calling qed *)
    fun is_failed_qed (act, errs) = 
      exists (is_failed_finished_mssg) errs
      andalso (Pred.is "qed" (Actions.kind_of act))
    fun fix_incomplete_qed st =
      let
        val thy = Toplevel.theory_of st;
        val ctxt = Toplevel.context_of st;
        val prf = Toplevel.proof_of st;
        val prf_goals = #goal (Proof.goal prf);
        val (objs, _) = Logic.strip_horn (Thm.prop_of prf_goals);
        val result = if null objs
          then [(Actions.void, st, [])]
          else let
            fun act_of goal = Actions.make_one thy ("show " ^ Sketcher.sketch_term ctxt goal);
            val sorry_action = Actions.make_one thy ("sorry")
            val qed_action = Actions.make_one thy ("qed")
            val new_acts = (Library.separate sorry_action (map act_of objs)) 
              @ [sorry_action, qed_action];
            val new_acts_text = implode (Library.separate "\n" (map Actions.text_of new_acts));
            val _ = tracing ("Adding missing actions:\n" ^ new_acts_text)
            val to_add = Actions.apply_all new_acts st;
          in to_add end
       in result end

    (* Handling illegal qed's *)
    fun is_oops_qed (act, errs) = 
      exists (is_illegal_app_mssg) errs
      andalso (Pred.is "qed" (Actions.kind_of act))
    fun fix_illegal_qed st = 
      let
        val act = Actions.make (Toplevel.theory_of st) "oops"
      in Actions.apply_all act st end;

    (* Main body: combines all the handlings above *)
    (* fun do_next act' (_:Actions.T, st, _:Runtime.error list) = *)
    fun do_next _ (_, []) = raise Fail "Empty input list to do_next"
      | do_next act' (last_relevant:Actions.T, prevs as (_:Actions.T, st, _:Runtime.error list) :: _) =
      if Toplevel.is_proof st
      then
        let
          val (st', err') = if might_timeout act' then
              (case Ops.apply_with_timeout timeout (Actions.apply act') st of
                Exn.Exn exn => (st, Runtime.exn_messages exn)
                | Exn.Res res => res)
            else Actions.apply act' st
          val result =
            (case err' of
              errs as (_ :: _) =>
                if is_refine (act', errs) then fix_refine_goal st act'
                else if is_timeout errs then
                  let 
                    val errors_mssg = "Errors were: " ^ string_all errs;
                    val act_mssg = "Fixing action: " ^ Actions.text_of act' ^ " with sorry."
                    val _ = Output.tracing (act_mssg ^ " " ^ errors_mssg)
                  in fix_using_sorry st end
                else if is_failed_mthd (act', errs) then fix_using_sorry st
                else if is_ill_app_done (act', errs) then
                  if Actions.on_kind (Pred.is "sorry") last_relevant
                  then (Output.tracing "removing extra 'done'"; [])
                  else (Output.tracing "changing 'done' with 'sorry'"; fix_using_sorry st)
                else if is_failed_qed (act', errs) then fix_incomplete_qed st
                else if is_oops_qed (act', errs) then (Output.tracing "'oops'ing a 'qed'"; fix_illegal_qed st)
                else if exists (is_illegal_app_mssg) errs andalso Actions.on_kind (Pred.is "sorry") last_relevant 
                  then (Output.tracing ("removing illegally applied '" ^ Actions.text_of act' ^ "'"); [])
                else let 
                    val act1_txt = " between actions '" ^ Actions.text_of last_relevant;
                    val act2_txt = "' and '" ^ Actions.text_of act'
                    val _ = warning ("Unexpected error: " ^ string_all errs ^ act1_txt ^ act2_txt) 
                  in [(act', st', err')] end
              | [] => [(act', st', err')]);
           val last_relevant' = if null result then last_relevant
             else let
               val (act'', st', _) = hd result;
             in if Toplevel.is_proof st' 
               andalso not (Actions.does_something (Toplevel.theory_of (#2 (hd result))) act')
               then last_relevant else act''
             end;
        in (last_relevant', (rev result) @ prevs) end
      else let
        val (st', err') = Actions.apply act' st
        val result =
            (case err' of
              errs as (_ :: _) =>
                if is_ill_app_done (act', errs) then []
                else [(act', st', err')]
              | [] => [(act', st', err')])
        in (last_relevant, (rev result) @ prevs) end
  in rev (snd (fold do_next acts (Actions.void, [(Actions.void, Toplevel.make_state NONE, [])]))) end;


(* strategies *)

datatype T = 
  SORRYS of Sketcher.method list
  | TRY0 of Sketcher.method list
  | TRY of Sketcher.method list
  | HAMMER of Sketcher.method list
  | LLM of Sketcher.method list

fun from_str str ms = (case str of 
  "SORRYS" => SORRYS ms
  | "TRY0" => TRY0 ms
  | "TRY" => TRY ms
  | "HAMMER" => HAMMER ms
  | "LLM" => LLM ms
  | another => raise Fail ("strategy_of_str: unknown mode" ^ another));

fun string_of fixer = 
  (case fixer of
    SORRYS _ => "SORRYS"
    | TRY0 _ => "TRY0"
    | TRY _ => "TRY"
    | HAMMER _ => "HAMMER"
    | LLM _ => "LLM"
  );

val parse_methods = \<^keyword>\<open>[\<close> |-- Parse.list (Scan.trace Method.parse) --| \<^keyword>\<open>]\<close>;

val parse = (Parse.embedded -- (Scan.option parse_methods))
  >> (fn (mode_txt, opt_ms) => 
    from_str mode_txt (case opt_ms of NONE => [] | SOME ms' => ms')
  );

fun build fixer =
  (case fixer of
    SORRYS _ => (fn _ => fn _ => "sorry")
    | TRY0 _ => (fn _ => fix_with_try0)
    | TRY _ => (fn _ => fix_with_try)
    | HAMMER _ => (fn _ => fix_with_hammer)
    | LLM _ => fix_with_llm 1
  );

fun get_methods fixer =
  (case fixer of
    SORRYS ms => ms
    | TRY0 ms => ms
    | TRY ms => ms
    | HAMMER ms => ms
    | LLM ms => ms
  );

fun pre_repair_sorrys fixer_fun = 
  generic_repair_sorrys false (fn _ => fn _ => []) (Toplevel.make_state NONE) (fn _ => fixer_fun);

fun repair_sorrys fixer st_act_errs =
  (case fixer of
    SORRYS ms => pre_repair_sorrys (fn _ => "sorry") (map SOME ms) st_act_errs
    | TRY0 ms => pre_repair_sorrys fix_with_try0 (map SOME ms) st_act_errs
    | TRY ms => pre_repair_sorrys fix_with_try (map SOME ms) st_act_errs
    | HAMMER ms =>  pre_repair_sorrys fix_with_hammer (map SOME ms) st_act_errs
    | LLM ms => repair_sorrys_with_llm (map SOME ms) st_act_errs
  )

fun fix_end_to_end {fixer=fixer} thy0 read_thy_file =
  let
    val thy_path = Path.explode (ML_System.standard_path read_thy_file);
    val _ = if File.is_file thy_path andalso (Path.get_ext thy_path = "thy") then ()
      else raise Fail ("Input '" ^ read_thy_file ^ "' is not an existing .thy file");

    val backup = 
      let
        val name = (Library.unsuffix ".thy" (Path.file_name thy_path)) ^ ".backup";
      in Path.append (Path.dir thy_path) (Path.explode name) end;
    val delete_mssg = "Make sure to save it somewhere else and/or delete it to call super_fix again."
    val _ = if not (File.is_file backup) then ()
      else raise Fail ("Existing .backup of '" ^ read_thy_file ^ "'. " ^ delete_mssg);
    val thy_text = File.read thy_path;
    val _ = Output.tracing ("Backing up input to '" ^ File.platform_path backup ^ "'");
    val _ = File.write backup thy_text;

    val actions = Actions.make thy0 (File.read thy_path);
    val sorryed_trace = process_all {err_timeout_in_secs=30} actions;
    
    (* For debugging: *)
    (* val temp_texts = map (fn (act, _, _) => Actions.text_of act) sorryed_trace;
    val temp = 
      let
        val name = (Library.unsuffix ".thy" (Path.file_name thy_path)) ^ ".temp";
      in Path.append (Path.dir thy_path) (Path.explode name) end;
    val _ = File.write temp (implode temp_texts); *)

    val fixed_trace = repair_sorrys fixer sorryed_trace;
    val new_texts = map (fn (act, _, _) => Actions.text_of act) fixed_trace;

    val _ = File.write thy_path (implode new_texts);
  in () end

end;
