(* 
  Mantainers: 
    Chengsong Tan -- c.tan[at]imperial[dot]ac[dot]uk
    Jonathan Julián Huerta y Munive -- huertjon[at]cvut[dot]cz

Main implementation of super_fix's algorithm
*)

signature FIXER =
sig
  val log_fold_list: ('a -> 'b -> 'b list) -> 'b -> 'a list -> 'b list
  val repair_sorrys: string -> (Actions.T * Toplevel.state * (exn * string) option) list 
    -> (Actions.T * Toplevel.state * (exn * string) option) list
  val process_all: {err_timeout_in_secs: int} -> Actions.T list 
    -> (Actions.T * Toplevel.state * (exn * string) option) list
  val fix_end_to_end: {strategy: string} -> theory -> string -> string -> string -> unit
end;


structure Fixer: FIXER =
struct


fun log_fold_list _ _ [] = []
  | log_fold_list f s (x :: xs) = 
    let 
      val vs = f x s 
    in vs @ log_fold_list f (List.last vs) xs end;

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

fun repair_sorrys_with_llm st_act_errs =
  let
    fun update_proof_so_far (act', st') st proof_so_far =
      let
        val was_proof = Toplevel.is_proof st;
        val is_proof = Toplevel.is_proof st';
        val proof_so_far' = if is_proof
          then (act', st') :: proof_so_far 
          else if was_proof then [] else proof_so_far;
      in proof_so_far' end;
    fun try_llm_fix proof_so_far origs st =
      let
        val prf_so_far =
          rev proof_so_far
          |> map (fn (a, _) => Actions.text_of a)
          |> Library.space_implode "\n"
          |> make_parseable
          |> Pretty.str |> Print.pretty_json_elem "proof_so_far";
        val usr_st = 
          Get.user_state {break_lines=false} st
          |> make_parseable
          |> Pretty.str |> Print.pretty_json_elem "user_state";
        val prf_data =
          Print.pretty_json_attribs false "{" "}" 0 [usr_st, prf_so_far]
          |> Print.string_of_pretty;
        val _ = Client.communicate prf_data;
        val llm_response = Client.get_last_response ();
        val result = (case llm_response of
          SOME response => 
            let
              val attempt = Actions.make (Toplevel.theory_of st) response
                |> (fn acts => Actions.apply_all acts st);
              val failed = exists is_some (map (fn (_, _, opt_err) => opt_err) attempt);
              fun warn_failure () =
                let 
                  val suggestions = map (fn (act, _, _) => Actions.text_of act) attempt;
                  val warn_message = "Failed recommendations: " ^ (space_implode "\n" suggestions);
                in Output.warning warn_message end
              val final = if failed then (warn_failure (); [origs]) else attempt
            in final end
          | NONE => [origs])
      in result end;
    fun do_next (act', st', err') (proof_so_far, result_so_far) =
      let
        val st = #2 (Ops.last result_so_far);
        val act_st_errs' = if Actions.on_kind (Pred.is "sorry") act'
          then try_llm_fix proof_so_far (act', st', err') st
          else [(act', st', err')];
        val proof_so_far' = update_proof_so_far (act', st') st proof_so_far;
      in (proof_so_far', result_so_far @ act_st_errs') end;
    val _ = Client.connect_to_server 5006;
    val (_, result) = fold do_next st_act_errs ([], [(Actions.void, Toplevel.make_state NONE, NONE)]);
    val _ = Client.disconnect ();
  in result end;

fun repair_sorrys_with_hammer st_act_errs =
  let
    fun fix_using_sledgehammer st =
      let
        val thy = Toplevel.theory_of st;
        val timeout = Time.fromSeconds 90;
        val timed_hammer = Ops.apply_with_timeout timeout (Hammer_Alt.hammer_away 1)
        val (_, str2) = (case timed_hammer (Toplevel.proof_of st) of
          Exn.Exn _ => ("timed out", "timed out")
          | Exn.Res res => res)
        val sorry_fix = 
          if (Pred.contains "imed out" orf Pred.contains "No proof found") str2 
          then "sorry" else ""
        val actual_fix = if sorry_fix = "" 
          then (Hammer_Alt.extract_one_liner_proof (Get.string_of_yxml str2)) 
          else sorry_fix
        val new_acts = Actions.make thy actual_fix;
        val _ = warning ("Adopted proof: " ^ actual_fix)
        val act_st_err_list = Actions.apply_all new_acts st;
      in act_st_err_list end
    fun do_next (act', st', err') (_:Actions.T, st, _:(exn * string) option) =
      if Actions.on_kind (Pred.is "sorry") act'
      then fix_using_sledgehammer st
      else [(act', st', err')]
  in log_fold_list do_next (Actions.void, Toplevel.make_state NONE, NONE) st_act_errs end;

fun process_all {err_timeout_in_secs=t} acts =
  let
    (* Handling "Failed to refine any pending goal" *)
    fun is_refine_mssg ((_, txt), _) = Pred.contains "Failed to refine any pending goal" txt;
    fun is_refine (act, exn) = exists is_refine_mssg (Runtime.exn_messages exn)
      andalso (member (op =) ["have", "hence", "show", "thus"] (Actions.kind_of act));
    fun fix_refine_goal st act' =
      let
        val thy = Toplevel.theory_of st;
        val ctxt = Toplevel.context_of st;
        val prf = Toplevel.proof_of st;
        val prf_goals = #goal (Proof.goal prf);
        val (objs, _) = Logic.strip_horn (Thm.prop_of prf_goals);
        val (new_act, new_st, new_err) = if null objs
          then (Actions.void, st, NONE)
          else let
            val nxt_goal = hd objs; (* ideally we would find the objective most similar
              to the original action, and not the head *)
            val goal_txt = Print.string_of_pretty (Syntax.pretty_term ctxt nxt_goal);
            val splitted = Pred.split (fn c => str c = "\"") (String.explode (Actions.text_of act'))
            val _ = if null splitted then Output.error_message "empty splitted" else ();
            val declaration =
              Pred.split (fn c => str c = "\"") (String.explode (Actions.text_of act'))
              |> hd |> String.implode;
            val new_act = Actions.make_one thy (declaration ^ " " ^ (enclose "\"" "\"" goal_txt));
            val _ = Output.tracing ("Fixed '" ^ Actions.text_of act' ^ "'")
            val _ = Output.tracing ("  to '"  ^ Actions.text_of new_act ^ "'")
            val (new_st, new_err) = Actions.apply_safe new_act st;
          in (new_act, new_st, new_err) end
       in [(new_act, new_st, new_err)] end

    (* Handling proof timeouts *)
    val timeout = Time.fromSeconds t
    val might_timeout = Actions.on_kind (Pred.is "apply");
    fun is_timeout exn = (case exn of Timeout.TIMEOUT _ => true | _ => false);
    fun fix_using_sorry st =
      let
        val thy = Toplevel.theory_of st;
        val new_act = Actions.make_one thy "sorry";
        val (new_st, new_err) = Actions.apply_safe new_act st;
      in [(new_act, new_st, new_err)] end

    (* Handling incorrectly placed done's after a by *)
    fun is_illegal_app_mssg ((_, txt), _) 
      = Pred.contains "Illegal application of proof" txt;
    fun is_failed_finished_mssg ((_, txt), _) 
      = Pred.contains "Failed to finish" txt;
    fun is_done_in_bad_ctxt_mssg ((_, txt), _) 
      = Pred.contains "Bad context for command \"done\"" (Get.string_of_yxml txt);
    val wrong_done_cmmnd_cases = [
      is_illegal_app_mssg, 
      is_failed_finished_mssg,
      is_done_in_bad_ctxt_mssg]
    fun is_ill_app_done (act, exn) 
      = exists (Pred.disjunct wrong_done_cmmnd_cases) (Runtime.exn_messages exn)
        andalso (Pred.is "done" (Actions.kind_of act))
    fun fix_ill_app_done st = 
      let 
        val _ = Output.tracing "Fixing ill app done at" 
      in [(Actions.void, st, NONE)] end;

    (* Handling non timed-out bad Sledgehammer proofs *)
    fun is_failed_mthd_mssg ((_, txt), _) = 
      Pred.contains "Failed to apply proof method" txt 
      orelse Pred.contains "terminated abnormally" txt
      orelse Pred.contains "Undefined fact:" txt;
    fun is_failed_mthd (act, exn) = exists is_failed_mthd_mssg (Runtime.exn_messages exn)
      andalso Actions.on_text (Pred.contains "smt" orf Pred.contains "metis" orf Pred.contains "apply") act;

    (* Handling incomplete proofs calling qed *)
    fun is_failed_qed (act, exn) = exists (is_failed_finished_mssg) (Runtime.exn_messages exn)
      andalso (Pred.is "qed" (Actions.kind_of act))
    fun fix_incomplete_qed st =
      let
        val thy = Toplevel.theory_of st;
        val ctxt = Toplevel.context_of st;
        val prf = Toplevel.proof_of st;
        val prf_goals = #goal (Proof.goal prf);
        val (objs, _) = Logic.strip_horn (Thm.prop_of prf_goals);
        val result = if null objs
          then [(Actions.void, st, NONE)]
          else let
            fun txt_of goal = Print.string_of_pretty (Syntax.pretty_term ctxt goal);
            fun act_of goal = Actions.make_one thy ("show " ^ enclose "\"" "\"" (txt_of goal));
            val sorry_action = Actions.make_one thy ("sorry")
            val qed_action = Actions.make_one thy ("qed")
            val new_acts = (Library.separate sorry_action (map act_of objs)) @ [sorry_action, qed_action];
            val new_acts_text = implode (Library.separate "\n" (map Actions.text_of new_acts));
            val _ = tracing ("Adding missing actions:\n" ^ new_acts_text)
            val to_add = Actions.apply_all new_acts st;
          in to_add end
       in result end

    (* Main body: combines all the handlings above *)
    (* fun do_next act' (_:Actions.T, st, _:(exn * string) option) = *)
    fun do_next act' (_:Actions.T, st, _:(exn * string) option) =
      if Toplevel.is_proof st
      then
        let
          val (st', err') = if might_timeout act' then
              (case Ops.apply_with_timeout timeout (Actions.apply_safe act') st of
                Exn.Exn exn => (st, SOME (exn, "TIMEOUT"))
                | Exn.Res res => res)
            else Actions.apply_safe act' st
          val result =
            (case err' of
              SOME (exn, _) =>
                if is_refine (act', exn) then fix_refine_goal st act'
                else if is_timeout exn then fix_using_sorry st
                else if is_failed_mthd (act', exn) then fix_using_sorry st
                else if is_ill_app_done (act', exn) then fix_ill_app_done st
                else if is_failed_qed (act', exn) then fix_incomplete_qed st
                else [(act', st', err')]
              | NONE => [(act', st', err')])
        in result end
      else let
        val (st', err') = Actions.apply_safe act' st
        val result =
            (case err' of
              SOME (exn, _) =>
                if is_ill_app_done (act', exn) then fix_ill_app_done st
                else [(act', st', err')]
              | NONE => [(act', st', err')])
        in result end
  in log_fold_list do_next (Actions.void, Toplevel.make_state NONE, NONE) acts end;

fun repair_sorrys fixer st_act_errs =
  if Pred.is fixer "sledgehammer" then repair_sorrys_with_hammer st_act_errs
  else if Pred.is fixer "llm" then repair_sorrys_with_llm st_act_errs
  else raise Fail ("Unrecognized fixing strategy: " ^ fixer)

fun fix_end_to_end {strategy=fixer} thy0 old_name new_name path =
  let 
    val actions = Actions.make' thy0 (File.read (Path.explode old_name));
    val sorryed_trace = process_all {err_timeout_in_secs=45} actions;
    val fixed_trace = repair_sorrys fixer sorryed_trace;
    val new_texts = Library.separate "\n" (map (fn (act, _, _) => Actions.text_of act) fixed_trace);
    val _ = Ops.create_file {force=true} path new_name (implode new_texts)
  in () end

end;
