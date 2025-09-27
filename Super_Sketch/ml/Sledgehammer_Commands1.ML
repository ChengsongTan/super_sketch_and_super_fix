(*  
  Original Author:
    Jasmin Blanchette, TU Muenchen
  Mantainers: 
    Chengsong Tan -- c.tan[at]imperial[dot]ac[dot]uk

Adds "sledgehammer" and related commands to Isabelle/Isar's outer syntax.
Super_sketch tweaked this file to easily call sledgehammer on a proof state, also incuded
utilities for removing comments in generated one-liners.
*)

signature SLEDGEHAMMER_COMMANDS1 =
sig
  type params = Sledgehammer_Prover.params

  val provers : string Unsynchronized.ref
  val default_params : theory -> (string * string) list -> params
  val parse_params: (string * string) list parser
  val my_hammer_away: int -> Proof.state -> (string * string)
  val my_verbose_hammer_away: int -> Proof.state -> int -> (string * string)
  val extract_one_liner_proof: string -> string
  val my_hammer_or_method_away: int -> Proof.state -> (Method.text * Position.range)  -> string -> (Method.text * Position.range)  -> string -> (string * string)
end;

structure Sledgehammer_Commands1 : SLEDGEHAMMER_COMMANDS1 =
struct

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

val runN = "run"

(** Sledgehammer commands **)

fun add_fact_override ns : fact_override = {add = ns, del = [], only = false}
fun del_fact_override ns : fact_override = {add = [], del = ns, only = false}
fun only_fact_override ns : fact_override = {add = ns, del = [], only = true}
fun merge_fact_override_pairwise (r1 : fact_override) (r2 : fact_override) =
  {add = #add r1 @ #add r2, del = #del r1 @ #del r2, only = #only r1 andalso #only r2}
fun merge_fact_overrides rs = fold merge_fact_override_pairwise rs (only_fact_override [])

(*** parameters ***)

val provers = Unsynchronized.ref ""

type raw_param = string * string list

val default_default_params =
  [("debug", "false"),
   ("verbose", "false"),
   ("overlord", "false"),
   ("spy", "false"),
   ("abduce", "0"),
   ("falsify", "false"),
   ("type_enc", "smart"),
   ("strict", "false"),
   ("lam_trans", "smart"),
   ("uncurried_aliases", "smart"),
   ("learn", "true"),
   ("fact_filter", "smart"),
   ("induction_rules", "smart"),
   ("max_facts", "smart"),
   ("fact_thresholds", "0.45 0.85"),
   ("max_mono_iters", "smart"),
   ("max_new_mono_instances", "smart"),
   ("max_proofs", "4"),
   ("isar_proofs", "smart"),
   ("compress", "smart"),
   ("try0", "true"),
   ("smt_proofs", "true"),
   ("minimize", "true"),
   ("slices", string_of_int (12 * Multithreading.max_threads ())),
   ("preplay_timeout", "1")]

val alias_params =
  [("prover", ("provers", [])), (* undocumented *)
   ("dont_abduce", ("abduce", ["0"])),
   ("dont_preplay", ("preplay_timeout", ["0"])),
   ("dont_compress", ("compress", ["1"])),
   ("dont_slice", ("slices", ["1"])),
   ("isar_proof", ("isar_proofs", [])) (* legacy *)]
val negated_alias_params =
  [("no_debug", "debug"),
   ("quiet", "verbose"),
   ("no_overlord", "overlord"),
   ("dont_spy", "spy"),
   ("dont_falsify", "falsify"),
   ("non_strict", "strict"),
   ("no_uncurried_aliases", "uncurried_aliases"),
   ("dont_learn", "learn"),
   ("no_isar_proofs", "isar_proofs"),
   ("dont_minimize", "minimize"),
   ("dont_try0", "try0"),
   ("no_smt_proofs", "smt_proofs")]

val property_dependent_params = ["provers", "timeout"]

fun is_known_raw_param s =
  AList.defined (op =) default_default_params s orelse
  AList.defined (op =) alias_params s orelse
  AList.defined (op =) negated_alias_params s orelse
  member (op =) property_dependent_params s orelse s = "expect"

fun is_prover_list ctxt s =
  (case space_explode " " s of
    ss as _ :: _ => forall (is_prover_supported ctxt) ss
  | _ => false)

fun unalias_raw_param (name, value) =
  (case AList.lookup (op =) alias_params name of
    SOME (name', []) => (name', value)
  | SOME (param' as (name', _)) =>
    if value <> ["false"] then
      param'
    else
      error ("Parameter " ^ quote name ^ " cannot be set to \"false\" (cf. " ^ quote name' ^ ")")
  | NONE =>
    (case AList.lookup (op =) negated_alias_params name of
      SOME name' => (name',
        (case value of
          ["false"] => ["true"]
        | ["true"] => ["false"]
        | [] => ["false"]
        | _ => value))
    | NONE => (name, value)))

val any_type_enc = type_enc_of_string Strict "erased"

(* "provers =", "type_enc =", "lam_trans =", "fact_filter =", and "max_facts ="
   can be omitted. For the last four, this is a secret feature. *)
fun normalize_raw_param ctxt =
  unalias_raw_param
  #> (fn (name, value) =>
         if is_known_raw_param name then
           (name, value)
         else if null value then
           if is_prover_list ctxt name then
             ("provers", [name])
           else if can (type_enc_of_string Strict) name then
             ("type_enc", [name])
           else if can (trans_lams_of_string ctxt any_type_enc) name then
             ("lam_trans", [name])
           else if member (op =) fact_filters name then
             ("fact_filter", [name])
           else if is_some (Int.fromString name) then
             ("max_facts", [name])
           else
             error ("Unknown parameter: " ^ quote name)
         else
           error ("Unknown parameter: " ^ quote name))

(* Ensures that type encodings such as "mono_native?" and "poly_guards!!" are
   read correctly. *)
val implode_param = strip_spaces_except_between_idents o space_implode " "

(* FIXME: use "Generic_Data" *)
structure Data = Theory_Data
(
  type T = raw_param list
  val empty = default_default_params |> map (apsnd single)
  fun merge data : T = AList.merge (op =) (K true) data
)

(* The first ATP of the list is used by Auto Sledgehammer. *)
fun default_provers_param_value ctxt =
  \<comment> \<open>see also \<^system_option>\<open>sledgehammer_provers\<close>\<close>
  filter (is_prover_installed ctxt) (smts ctxt @ local_atps)
  |> implode_param



fun default_raw_params thy =
  let val ctxt = Proof_Context.init_global thy in
    Data.get thy
    |> fold (AList.default (op =))
       [("provers", [(case !provers of "" => default_provers_param_value ctxt | s => s)]),
        ("timeout",
         let val timeout = Options.default_int \<^system_option>\<open>sledgehammer_timeout\<close> in
           [if timeout <= 0 then "none" else string_of_int timeout]
         end)]
  end

fun extract_params mode default_params override_params =
  let
    val raw_params = rev override_params @ rev default_params
    val lookup = Option.map implode_param o AList.lookup (op =) raw_params
    val lookup_string = the_default "" o lookup

    fun general_lookup_bool option default_value name =
      (case lookup name of
        SOME s => parse_bool_option option name s
      | NONE => default_value)
    val lookup_bool = the o general_lookup_bool false (SOME false)
    fun lookup_time name =
      (case lookup name of
        SOME s => parse_time name s
      | NONE => Time.zeroTime)
    fun lookup_int name =
      (case lookup name of
        NONE => 0
      | SOME s =>
        (case Int.fromString s of
          SOME n => n
        | NONE => error ("Parameter " ^ quote name ^ " must be assigned an integer value")))
    fun lookup_real name =
      (case lookup name of
        NONE => 0.0
      | SOME s =>
        (case Real.fromString s of
          SOME n => n
        | NONE => error ("Parameter " ^ quote name ^ " must be assigned a real value")))
    fun lookup_real_pair name =
      (case lookup name of
        NONE => (0.0, 0.0)
      | SOME s =>
        (case s |> space_explode " " |> map Real.fromString of
          [SOME r1, SOME r2] => (r1, r2)
        | _ => error ("Parameter " ^ quote name ^ " must be assigned a pair of floating-point \
                 \values (e.g., \"0.6 0.95\")")))
    fun lookup_option lookup' name =
      (case lookup name of
        SOME "smart" => NONE
      | _ => SOME (lookup' name))
    val debug = mode <> Auto_Try andalso lookup_bool "debug"
    val verbose = debug orelse (mode <> Auto_Try andalso lookup_bool "verbose")
    val overlord = lookup_bool "overlord"
    val spy = getenv "SLEDGEHAMMER_SPY" = "yes" orelse lookup_bool "spy"
    val provers = lookup_string "provers" |> space_explode " " |> mode = Auto_Try ? single o hd
    val abduce =
      if mode = Auto_Try then SOME 0
      else lookup_option lookup_int "abduce"
    val falsify =
      if mode = Auto_Try then SOME false
      else lookup_option lookup_bool "falsify"
    val type_enc =
      if mode = Auto_Try then
        NONE
      else
        (case lookup_string "type_enc" of
          "smart" => NONE
        | s => (type_enc_of_string Strict s; SOME s))
    val strict = mode = Auto_Try orelse lookup_bool "strict"
    val lam_trans = lookup_option lookup_string "lam_trans"
    val uncurried_aliases = lookup_option lookup_bool "uncurried_aliases"
    val learn = lookup_bool "learn"
    val fact_filter =
      lookup_option lookup_string "fact_filter"
      |> mode = Auto_Try ? (fn NONE => SOME mepoN | sf => sf)
    val induction_rules =
      lookup_option (the o induction_rules_of_string o lookup_string) "induction_rules"
    val max_facts = lookup_option lookup_int "max_facts"
    val fact_thresholds = lookup_real_pair "fact_thresholds"
    val max_mono_iters = lookup_option lookup_int "max_mono_iters"
    val max_new_mono_instances =
      lookup_option lookup_int "max_new_mono_instances"
    val max_proofs = lookup_int "max_proofs"
    val isar_proofs = lookup_option lookup_bool "isar_proofs"
    val compress = Option.map (curry Real.max 1.0) (lookup_option lookup_real "compress")
    val try0 = lookup_bool "try0"
    val smt_proofs = lookup_bool "smt_proofs"
    val instantiate = lookup_option lookup_bool "instantiate"
    val minimize = mode <> Auto_Try andalso lookup_bool "minimize"
    val slices = if mode = Auto_Try then 1 else Int.max (1, lookup_int "slices")
    val timeout = lookup_time "timeout"
    val preplay_timeout = lookup_time "preplay_timeout"
    val expect = lookup_string "expect"
    val cache_dir = Option.mapPartial
      (fn str => if str = "" then NONE else SOME (Path.explode str)) (lookup "cache_dir")
  in
    {debug = debug, verbose = verbose, overlord = overlord, spy = spy, provers = provers,
     abduce = abduce, falsify = falsify, type_enc = type_enc, strict = strict,
     lam_trans = lam_trans, uncurried_aliases = uncurried_aliases, learn = learn,
     fact_filter = fact_filter, induction_rules = induction_rules, max_facts = max_facts,
     fact_thresholds = fact_thresholds, max_mono_iters = max_mono_iters,
     max_new_mono_instances = max_new_mono_instances, max_proofs = max_proofs,
     isar_proofs = isar_proofs, compress = compress, try0 = try0, smt_proofs = smt_proofs,
     instantiate = instantiate, minimize = minimize, slices = slices, timeout = timeout, preplay_timeout = preplay_timeout,
     expect = expect, cache_dir = cache_dir}
  end

fun get_params mode = extract_params mode o default_raw_params
fun default_params thy = get_params Normal thy o map (apsnd single)

val silence_state =
  Proof.map_contexts (Try0.silence_methods false #> Config.put SMT_Config.verbose false)

(* Sledgehammer the given subgoal *)


val parse_query_bang = \<^keyword>\<open>?\<close> || \<^keyword>\<open>!\<close> || \<^keyword>\<open>!!\<close>
val parse_key = Scan.repeat1 (Parse.embedded || parse_query_bang) >> implode_param
val parse_value = Scan.repeat1 (Parse.name || Parse.float_number || parse_query_bang)
val parse_param = parse_key -- Scan.optional (\<^keyword>\<open>=\<close> |-- parse_value) []
val parse_raw_params = Scan.optional (Args.bracks (Parse.list parse_param)) []
val parse_params = parse_raw_params >> map (apsnd implode_param)
val parse_fact_refs = Scan.repeat1 (Scan.unless (Parse.name -- Args.colon) Parse.thm)
val parse_fact_override_chunk =
  (Args.add |-- Args.colon |-- parse_fact_refs >> add_fact_override)
  || (Args.add |-- Args.colon |-- Scan.succeed [] >> add_fact_override)
  || (Args.del |-- Args.colon |-- parse_fact_refs >> del_fact_override)
  || (Args.del |-- Args.colon |-- Scan.succeed [] >> del_fact_override)
  || (parse_fact_refs >> only_fact_override)
val parse_fact_override =
  Scan.optional (Args.parens (Scan.repeat parse_fact_override_chunk >> merge_fact_overrides))
    no_fact_override


fun remove_all_substrings sub s =
  let
    val n = String.size s
    val m = String.size sub
    fun loop i acc =
      if i > n - m then String.implode (rev acc) ^ String.extract (s, i, NONE)
      else if String.substring (s, i, m) = sub
      then loop (i + m) acc
      else loop (i + 1) (String.sub (s, i) :: acc)
  in loop 0 [] end

fun remove_prefer i s =
  let
    val base = "prefer " ^ Int.toString i
    val s1 = remove_all_substrings base s
    val s2 = remove_all_substrings (base ^ "; ") s1
    val s3 = remove_all_substrings (base ^ "\n") s2
    val s4 = remove_all_substrings (base ^ " ") s3
    val s5 = remove_all_substrings base s4
  in s5 end

fun my_hammer_away i state0 =
  let
    val state = silence_state state0
    val thy = Proof.theory_of state
    val ctxt = Proof.context_of state

    val override_params = [("max_proofs", ["1"])] |> map (normalize_raw_param ctxt)
    val subcommand = runN
  in
    if subcommand = runN then
      let val i = the_default i NONE in
         (run_sledgehammer
          (get_params Normal thy override_params) Normal NONE i Sledgehammer_Fact.no_fact_override state) |> (fn (bres, (_, msg)) => if bres then ("success", (remove_prefer i) msg) else ("fail", msg))
      end
    else
      error ("Unknown subcommand: " ^ quote subcommand)
  end



fun my_verbose_hammer_away i state0 n_proofs =
  let                            
    val state = silence_state state0
    val thy = Proof.theory_of state
    val ctxt = Proof.context_of state

    val override_params = [("max_proofs", [Int.toString n_proofs])] |> map (normalize_raw_param ctxt)
    val subcommand = runN
  in
    if subcommand = runN then
      let val i = the_default i NONE in
         (run_sledgehammer
          (get_params Normal thy override_params) Normal NONE i Sledgehammer_Fact.no_fact_override state) |> (fn (bres, (_, msg)) => if bres then ("success", (remove_prefer i) msg) else ("fail", msg))
      end
    else
      error ("Unknown subcommand: " ^ quote subcommand)
  end


fun extract_one_liner_proof (input: string) =
  let
    (* -------- helpers -------- *)
    fun is_space c = Char.isSpace c
    fun trim_left s =
      let
        val n = String.size s
        fun go i = if i < n andalso is_space (String.sub (s, i)) then go (i+1) else i
      in String.extract (s, go 0, NONE) end
    fun trim_right s =
      let
        fun go i = if i > 0 andalso is_space (String.sub (s, i-1)) then go (i-1) else i
        val k = go (String.size s)
      in String.extract (s, 0, SOME k) end
    fun squeeze_spaces s =
      let
        val n = String.size s
        fun loop i seen acc =
          if i = n then String.implode (rev acc)
          else
            let val c = String.sub (s, i) in
              if is_space c then
                loop (i+1) true (if seen then acc else #" " :: acc)
              else loop (i+1) false (c :: acc)
            end
      in trim_right (trim_left (loop 0 false [])) end

    fun find_sub (s, sub) =
      let
        val n = String.size s
        val m = String.size sub
        fun ok i = i + m <= n andalso String.substring (s, i, m) = sub
        fun go i = if i + m > n then NONE else if ok i then SOME i else go (i+1)
      in go 0 end

    fun find_last_sub (s, sub) =
      let
        val n = String.size s
        val m = String.size sub
        fun ok i = i - m >= 0 andalso String.substring (s, i - m, m) = sub
        fun go i = if i - m < 0 then NONE else if ok i then SOME (i - m) else go (i-1)
      in go n end

    (* looks like a trailing time tag starting exactly at position i (i.e. s[i] = '(') *)
    fun looks_like_time_from s i =
      let
        val n = String.size s
        fun digit j = j < n andalso Char.isDigit (String.sub (s, j))
        fun skip_spaces j = if j < n andalso is_space (String.sub (s, j)) then skip_spaces (j+1) else j
        val i1 = i + 1
        val i2 = if i1 < n andalso String.sub (s, i1) = #">" then i1 + 1 else i1
        fun read_digits j = if digit j then read_digits (j+1) else j
        val j1 = read_digits i2
        val j2 =
          if j1 < n andalso String.sub (s, j1) = #"."
          then read_digits (j1 + 1) else j1
        val j3 = skip_spaces j2
        val (j4, ok_unit) =
          if j3 + 1 < n andalso String.sub (s, j3) = #"m" andalso String.sub (s, j3+1) = #"s"
          then (j3 + 2, true)
          else if j3 < n andalso String.sub (s, j3) = #"s"
          then (j3 + 1, true)
          else (j3, false)
        val j5 = skip_spaces j4
      in
        if ok_unit andalso j5 < n andalso String.sub (s, j5) = #")"
        then SOME (j5 + 1) else NONE
      end

    (* cut off a trailing time tag "(... ms|s)" if it ends the string *)
    fun drop_trailing_time s =
      let
        val n = String.size s
        fun rskip_spaces i = if i > 0 andalso is_space (String.sub (s, i-1)) then rskip_spaces (i-1) else i
        val end0 = rskip_spaces n
        fun find_last_open i =
          if i = 0 then NONE
          else if String.sub (s, i-1) = #"(" then SOME (i-1) else find_last_open (i-1)
      in
        case find_last_open end0 of
          NONE => trim_right s
        | SOME p =>
            (case looks_like_time_from s p of
               SOME endpos =>
                 if endpos = end0
                 then trim_right (String.extract (s, 0, SOME p))
                 else trim_right s
             | NONE => trim_right s)
      end

    (* -------- main -------- *)
    val try_tag = "Try this:"
    val start =
      (case find_last_sub (input, try_tag) of
         SOME k => k + String.size try_tag
       | NONE => 0)

    val after_tag = trim_left (String.extract (input, start, NONE))
    val without_time = drop_trailing_time after_tag
  in
    squeeze_spaces without_time
  end;

(* Example usage *)
val input_string = "Try this: by (smt (verit) one_le_numeral power2_less_eq_zero_iff power_increasing power_one_right power_zero_numeral) (187 ms)"

val input_string1 = "Try this: by (metis add.commute add_0 add_diff_eq add_increasing2 diff_diff_eq2 diff_ge_0_iff_ge mult.right_neutral mult_1 power2_eq_square right_diff_distrib zero_le_mult_iff zero_le_square) (> 1.0 s, timed out)";
val result = extract_one_liner_proof(input_string);
val _ = writeln result
val _ = writeln (extract_one_liner_proof "cvc5: Try this:\n  apply (metis CSTATE_disj4' CSTATE_starting_transaction_otherside_invariant1 HSTATE_X_Evict_invariant1 H_msg_P_same_def\n    MESI_State.distinct(11) SharedSnpInv'_CSTATE_invariant5 i23) (343 ms) ")


(* ---------------- leaf: try user method once on subgoal i ------------------- *)
(* m_ref_opt : (Method.text * Position.range) option 与你当前 Proof.apply 的类型一致 *)

fun solved_by_method_message i state0 (m_ref : (Method.text * Position.range)) (method_text : string) =
  (let
       val st1 = Proof.prefer i (silence_state state0)
       val n0  = subgoal_count st1
       (* 注意：元素是 Proof.state Seq.result，而不是 Proof.state *)
       val step_opt = Seq.pull (Proof.apply m_ref st1)
     in
       (case step_opt of
          SOME (res, _) =>
            (case res of
               Seq.Result st' =>
                 if subgoal_count st' = n0 - 1
                 then let val _ = writeln "user method successfully solved goal"; in ("success", "cvc5: Try this: apply " ^ method_text ^ " (0 ms)") end
                 else let val _ = writeln "user method didnt solve goal"; in ("fail", "user method did not close the subgoal") end
             | Seq.Error _ =>
                 ("fail", "user method raised error"))
        | NONE =>
            ("fail", "user method produced no state"))
     end)




(* --------------- race: Sledgehammer ⟂ user method on subgoal i ------------- *)
(* 不引入新 API，只用 Future/Synchronized 进行“先成者胜并取消另一方” *)
fun my_hammer_or_method_away i state0 (m_ref : (Method.text * Position.range)) (method_text : string) adref adtxt =
  let
    val done_flag   = Synchronized.var "race_done" false
    val winner_slot = Synchronized.var "race_winner" (("","") : string * string)
    val sh_ref = Unsynchronized.ref (NONE : (string * string) future option)
    val um_ref = Unsynchronized.ref (NONE : (string * string) future option)

    fun win res other_ref =
      if #1 res = "success" then
        (case Synchronized.change_result done_flag (fn d => if d then (false, d) else (true, true)) of
           true => (Synchronized.change winner_slot (fn _ => res);
                    (case !other_ref of SOME fut => Future.cancel fut | NONE => ());
                    res)
         | false => res)
      else res

    (* SH my_hammer_away i state0 *)
    val sh_fut =
      Future.fork (fn () =>
        let val (outc, msg) = my_hammer_away i (Seq.the_result "" (Proof.apply adref state0))
            val msg' = if outc = "success" then remove_prefer i msg else msg
        in win (outc, "apply " ^ adtxt ^ " " ^ msg') um_ref end)
    val _ = sh_ref := SOME sh_fut

    (* *)
    val um_fut =
      Future.fork (fn () => win (solved_by_method_message i state0 m_ref method_text) sh_ref)
    val _ = um_ref := SOME um_fut

    fun wait () =
      if Synchronized.value done_flag then Synchronized.value winner_slot
      else if Future.is_finished sh_fut andalso Future.is_finished um_fut then
             (case Synchronized.value winner_slot of
                ("","") => ("fail", "no proof found")
              | res => res)
      else (OS.Process.sleep (Time.fromMilliseconds 10); wait ())
  in wait () end


end;
