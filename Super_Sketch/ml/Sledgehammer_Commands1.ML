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
(* 竞速分支的种类 *)
  datatype ms_kind = MS_PLAIN | MS_SH | MS_TRY0

(* 一个策略：种类 + 方法 m_ref + 打印文本 m_txt + 组序 order *)
  type ms_strategy = ms_kind * (Method.text * Position.range) * string * int
  val provers : string Unsynchronized.ref
  val default_params : theory -> (string * string) list -> params
  val parse_params: (string * string) list parser
  val my_hammer_away: int -> Proof.state -> (string * string)
  val my_verbose_hammer_away: int -> Proof.state -> int -> (string * string)
  val extract_one_liner_proof: string -> string
  val my_hammer_or_method_away: int -> Proof.state -> (Method.text * Position.range)  -> string -> (Method.text * Position.range)  -> string -> (string * string)
  val my_hammer_or_method_away4:
    int -> Proof.state
    -> (Method.text * Position.range) -> string     (* user method (e.g. simp)  *)
    -> (Method.text * Position.range) -> string     (* ad method: (e.g. insert assms, unfold ...) *)
    -> (Method.text * Position.range) option -> string option  (* rescue: e.g. auto *)
    -> (Method.text * Position.range) option -> string option (*NEW: split_rescue *)
    -> (string * string)
  val my_hammer_or_method_away5:
    int -> Proof.state -> ms_strategy list -> (string * string)
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
datatype ms_kind = MS_PLAIN | MS_SH | MS_TRY0

type ms_strategy = ms_kind * (Method.text * Position.range) * string * int

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
   ("isar_proofs", "false"),
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

    val override_params =
      [ ("max_proofs", ["1"])
      , ("isar_proofs", ["false"])
      , ("minimize", ["false"])
      , ("preplay_timeout", ["0"])
      , ("try0", ["false"])
      , ("slices", ["300"])
      , ("timeout", ["20"])       (* 12~20 *)
      ]
      |> map (normalize_raw_param ctxt)
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


(* 在 extract_one_liner_proof's helper*)
fun contains_sorry s =
  String.isSubstring "sorry" s

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




(* Timeout utilities for method execution *)
fun apply_method_with_timeout timeout_seconds m_ref state =
  let
    val timeout = Time.fromSeconds timeout_seconds
    val start_time = Time.now()
    val result_ref = Unsynchronized.ref NONE
    
    val method_future = Future.fork (fn () =>
      let val res = Seq.pull (Proof.apply m_ref state)
      in result_ref := SOME res; res end)
    
    fun wait_with_timeout () =
      if Time.- (Time.now(), start_time) > timeout then
        (Future.cancel method_future; NONE) (* timeout *)
      else case !result_ref of
        SOME res => SOME res
      | NONE => (OS.Process.sleep (Time.fromMilliseconds 100); wait_with_timeout ())
  in
    wait_with_timeout ()
  end


fun solved_by_method_message i state0 (m_ref : (Method.text * Position.range)) (method_text : string) =
  let
    val timeout_seconds = 2  (* 可以调整timeout时间 *)
    val st1 = Proof.prefer i (silence_state state0)
    val n0 = subgoal_count st1
  in
    case apply_method_with_timeout timeout_seconds m_ref st1 of
      SOME (SOME (res, _)) =>
        (case res of
           Seq.Result st' =>
             if subgoal_count st' = n0 - 1
             then (writeln "user method successfully solved goal"; 
                   ("success", "apply " ^ method_text ^ ""))
             else (writeln "user method didnt solve goal"; 
                   ("fail", "user method did not close the subgoal"))
         | Seq.Error _ =>
             ("fail", "user method raised error"))
    | SOME NONE =>
        ("fail", "user method produced no state")
    | NONE => 
        ("timeout", "user method timed out after " ^ Int.toString timeout_seconds ^ "s" ) 
  end

(* 对当前 state 上的“第 i 个子目标”跑 SH，成功则返回 one-liner（by/apply ...）文本，否则 NONE *)
fun try_sh_one_liner_on_subgoal i st : string option =
  let
    val (outc, msg) = my_hammer_away i st
  in
    if outc = "success" then SOME (extract_one_liner_proof msg) else NONE
  end



(* 将 rescue 方法应用到 state 上，返回新 state（可能 0/多个子目标） *)
fun apply_rescue_state (rescue_ref: (Method.text * Position.range)) (state0: Proof.state) : Proof.state =
  Seq.the_result "" (Proof.apply rescue_ref state0)

(* --- NEW: run rescue method with a hard wall-clock timeout --- *)
fun apply_rescue_with_timeout timeout_seconds
    (rescue_ref: (Method.text * Position.range))
    (state0: Proof.state) : Proof.state option =
  let
    val timeout = Time.fromSeconds timeout_seconds
    val t0 = Time.now ()
    (* box: NONE = 未完成；SOME(true, st) = 成功拿到新 state；SOME(false, _) = 失败/异常 *)
    val box = Unsynchronized.ref (NONE : (bool * Proof.state) option)

    val fut =
      Future.fork (fn () =>
        (let
           val st1 = Seq.the_result "" (Proof.apply rescue_ref state0)
         in box := SOME (true, st1); st1 end)
      )

    fun wait () =
      (case !box of
         SOME (true, st1) => SOME st1
       | SOME (false, _)  => NONE
       | NONE =>
           if Time.> (Time.- (Time.now (), t0), timeout)
           then (Future.cancel fut; NONE)
           else (OS.Process.sleep (Time.fromMilliseconds 50); wait ()))
  in
    wait ()
  end


(* ==== DEBUG 开关与工具 ==== *)
val rescue_debug = Unsynchronized.ref true
fun ms_of_time t = Real.round (Time.toReal t * 1000.0)
fun fmt_time t = Int.toString (ms_of_time t) ^ " ms"
fun rlog s = if !rescue_debug then writeln ("[rescue] " ^ s) else ()

(* ==== 结构化 rescue 结果 ==== *)
datatype rescue_status =
   RS_Timeout of {before:int, elapsed: Time.time}
 | RS_NoState of {before:int, elapsed: Time.time}
 | RS_Error   of {before:int, elapsed: Time.time, err: string}
 | RS_Ok      of {before:int, after:int, elapsed: Time.time, state: Proof.state}

(* ==== 带硬超时、可区分结果的 rescue 执行 ==== *)
fun apply_rescue_with_timeout_ex timeout_seconds
    (rescue_ref: (Method.text * Position.range))
    (state0: Proof.state) : rescue_status =
  let
    val timeout = Time.fromSeconds timeout_seconds
    val t0 = Time.now ()
    val n0 = subgoal_count state0
    val box = Unsynchronized.ref (NONE : rescue_status option)

    val fut =
      Future.fork (fn () =>
        let
          val res = Exn.capture (fn () => Seq.pull (Proof.apply rescue_ref state0)) ()
          val elapsed = Time.- (Time.now (), t0)
        in
          (case res of
             Exn.Res (SOME (Seq.Result st1, _)) =>
               box := SOME (RS_Ok {before=n0, after=subgoal_count st1, elapsed=elapsed, state=st1})
           | Exn.Res (SOME (Seq.Error _, _)) =>
               box := SOME (RS_NoState {before=n0, elapsed=elapsed})
           | Exn.Res NONE =>
               box := SOME (RS_NoState {before=n0, elapsed=elapsed})
           | Exn.Exn _ =>
               box := SOME (RS_Error {before=n0, elapsed=elapsed, err = "<exception>"}));
          ()
        end)

    fun poll () =
      (case !box of
         SOME ro => ro
       | NONE =>
           if Time.> (Time.- (Time.now (), t0), timeout)
           then (Future.cancel fut; RS_Timeout {before=n0, elapsed=Time.-(Time.now (), t0)})
           else (OS.Process.sleep (Time.fromMilliseconds 50); poll ()))
  in
    poll ()
  end


(* similar to rescue_then_sh_text, but focuses on split method and shorter timeout (1s) *)
fun split_then_sh_text
    (split_ref: (Method.text * Position.range)) (split_txt: string)
    (state0: Proof.state) : (string * string) =
  let
    val split_timeout_seconds = 13
    val n_before = subgoal_count state0
    val _ = rlog ("[split] START method=\"" ^ split_txt ^ "\" timeout=" ^
                  Int.toString split_timeout_seconds ^ "s before=" ^ Int.toString n_before)
  in
    case apply_rescue_with_timeout_ex split_timeout_seconds split_ref state0 of
      RS_Timeout {before = b1, elapsed = e1} =>
        (rlog ("[split] TIMEOUT " ^ fmt_time e1 ^ " before=" ^ Int.toString b1);
         ("fail", "split timeout (" ^ Int.toString split_timeout_seconds ^ "s)"))
    | RS_NoState {before = b2, elapsed = e2} =>
        (rlog ("[split] NO_STATE " ^ fmt_time e2 ^ " before=" ^ Int.toString b2);
         ("fail", "split produced no state"))
    | RS_Error {before = b3, elapsed = e3, err = err_msg} =>
        (rlog ("[split] ERROR " ^ err_msg ^ " " ^ fmt_time e3 ^
               " before=" ^ Int.toString b3);
         ("fail", "split raised error"))
    | RS_Ok {state = st1, before = b4, after = a4, elapsed = e4} =>
        let
          val _ = rlog ("[split] OK " ^ fmt_time e4 ^ " before=" ^ Int.toString b4 ^
                        " after=" ^ Int.toString a4 ^
                        (if a4 < b4 then " (progress)" else " (no progress)"))
        in
          if a4 = 0 then
            (rlog "[split] SOLVED_BY_SPLIT"; ("success", "by " ^ split_txt))
          else
            let
              val idxs = List.tabulate (a4, fn k => k + 1)
              fun try_sh j =
                let
                  val t0 = Time.now ()
                  val (outc, msg) = my_hammer_away j st1
                  val elapsed_sh = Time.- (Time.now (), t0)
                  val _ = rlog ("[split] SH subgoal " ^ Int.toString j ^ " -> " ^ outc ^
                                 " in " ^ fmt_time elapsed_sh)
                  val line =
                    if outc = "success" then extract_one_liner_proof msg
                    else "sorry (*split: sledgehammer failed*)"
                in line end
              val lines = Par_List.map try_sh idxs
              val text = String.concatWith "\n" (("apply " ^ split_txt) :: lines)
            in
              (rlog "[split] DONE_WITH_RESIDUALS"; ("success", text))
            end
        end
  end



fun rescue_then_sh_text
    (rescue_ref: (Method.text * Position.range)) (rescue_txt: string)
    (state0: Proof.state) : (string * string) =
  let
    val rescue_timeout_seconds = 10
    val n_before = subgoal_count state0
    val _ = rlog ("START method=\"" ^ rescue_txt ^ "\" timeout=" ^
                  Int.toString rescue_timeout_seconds ^ "s before=" ^ Int.toString n_before)
  in
    case apply_rescue_with_timeout_ex rescue_timeout_seconds rescue_ref state0 of
      RS_Timeout {before = b1, elapsed = e1} =>
        let 
          val _ = rlog ("TIMEOUT " ^ fmt_time e1 ^ " before=" ^ (Int.toString b1)) 
        in
          ("fail", "rescue timeout (" ^ Int.toString rescue_timeout_seconds ^ "s)")
        end
    | RS_NoState {before = b2, elapsed = e2} =>
        (rlog ("NO_STATE " ^ fmt_time e2 ^ " before=" ^ Int.toString b2);
         ("fail", "rescue produced no state"))
    | RS_Error {before = b3, elapsed = e3, err = err_msg} =>
        (rlog ("ERROR " ^ err_msg ^ " " ^ fmt_time e3 ^ " before=" ^ Int.toString b3);
         ("fail", "rescue raised error"))
    | RS_Ok {state = st1, before = b4, after = a4, elapsed = e4} =>
        let
          val _ = rlog ("OK " ^ fmt_time e4 ^ " before=" ^ Int.toString b4 ^
                        " after=" ^ Int.toString a4 ^
                        (if a4 < b4 then " (progress)" else " (no progress)"))
        in
          if a4 = 0 then
            (rlog "SOLVED_BY_RESCUE"; ("success", "by " ^ rescue_txt))
          else
            let
              val idxs = List.tabulate (a4, fn k => k + 1)
              fun try_sh j =
                let
                  val t0 = Time.now ()
                  val (outc, msg) = my_hammer_away j st1
                  val elapsed_sh = Time.- (Time.now (), t0)
                  val _ = rlog ("SH subgoal " ^ Int.toString j ^ " -> " ^ outc ^
                                 " in " ^ fmt_time elapsed_sh)
                  val line =
                    if outc = "success" then extract_one_liner_proof msg
                    else "sorry (*rescue: sledgehammer failed*)"
                in line end
              val lines = Par_List.map try_sh idxs
              val text = String.concatWith "\n" (("apply " ^ rescue_txt) :: lines)
            in
              (rlog "RESCUE_DONE_WITH_RESIDUALS"; ("success", text))
            end
        end
  end


fun my_hammer_or_method_away4
  i state0 (m_ref : (Method.text * Position.range)) (method_text : string)
  adref adtxt
  (rescue_opt: (Method.text * Position.range) option) (rescue_txt_opt: string option)
  split_opt split_txt_opt
  : (string * string) =
let
  (* === fast race: METHOD vs SH === *)

  (* 赢家槽：只在 success 时写入 *)
  val winner_slot = Synchronized.var "race_winner" (NONE : (string * string) option)

  (* 屏障：保证两边句柄已就绪，避免取消丢失 *)
  val started = Synchronized.var "race_started" 0
  fun wait_until_both_started () =
    if Synchronized.value started = 2 then ()
    else (OS.Process.sleep (Time.fromMilliseconds 1); wait_until_both_started ())

  (* 句柄 ref *)
  val sh_ref = Unsynchronized.ref (NONE : (string * string) future option)
  val um_ref = Unsynchronized.ref (NONE : (string * string) future option)

  (* 发布赢家：只有 success 才能赢 *)
  fun publish_if_success (res: string * string) : bool =
    if #1 res = "success" then
      Synchronized.change_result winner_slot
        (fn NONE => (true, SOME res) | SOME w => (false, SOME w))
    else false

  (* 方法分支：建议 10~15s 快速超时 *)
  val method_fast_timeout = 12

  val um_fut =
    Future.fork (fn () =>
      let
        val _ = Synchronized.change started (fn n => n + 1)
        val res = solved_by_method_message i state0 m_ref method_text
        val won = publish_if_success res
        val _ =
          if won then
            (wait_until_both_started ();
             (case !sh_ref of SOME fut => let val _ = writeln "cancelling sh" in Future.cancel fut end | NONE => ()))
          else ()
      in
        res
      end)

  val _ = um_ref := SOME um_fut

  (* Sledgehammer 分支（快速配置） *)
  val sh_fut =
    Future.fork (fn () =>
      let
        val _ = "sh future started"
        val _ = Synchronized.change started (fn n => n + 1)
        val (outc, msg) =
          my_hammer_away i (Seq.the_result "" (Proof.apply adref state0))
        val msg' =
          if outc = "success"
          then "apply " ^ adtxt ^ " " ^ extract_one_liner_proof (remove_prefer i msg)
          else msg
        val res = (outc, msg')
        val won = publish_if_success res
        val _ =
          if won then
            (wait_until_both_started ();
             (case !um_ref of SOME fut => Future.cancel fut | NONE => ()))
          else ()
      in
        res
      end)

  val _ = sh_ref := SOME sh_fut

  (* 等待赢家；若两边都结束仍无赢家 \<rightarrow> 视为 fail(fast) *)
  fun wait_fast () =
    (case Synchronized.value winner_slot of
       SOME res => res
     | NONE =>
         if Future.is_finished sh_fut andalso Future.is_finished um_fut
         then ("fail", "no proof found (fast)")
         else (OS.Process.sleep (Time.fromMilliseconds 10); wait_fast ()))

  val fast_result = wait_fast ()
  (* === fast race end === *)

  (* 资源回收 *)
  val _ = (ignore (Exn.capture Future.join sh_fut);
           ignore (Exn.capture Future.join um_fut));

  (* 兜底：仅当 fast_result 失败 且 给了 rescue 方法 *)
  val _ = writeln "get final result"
  val final_result =
    (case fast_result of
       ("success", _) => fast_result
     | _ =>
        (case (rescue_opt, rescue_txt_opt) of
           (SOME rescue_ref, SOME rescue_txt) =>
             (* 在  if both a vanilla sledgehammer and the user's simp method failed, apply a more heavyweight
                    "rescue" method which tries to solve the goal and ask for help for residual subgoals from sledgehammer*)
             let
               
               val state_subgoaled = (#2 o Subgoal.subgoal_cmd Binding.empty_atts NONE (false, [])) state0;
               val (r, m) = rescue_then_sh_text rescue_ref rescue_txt state_subgoaled
             in
               if r = "success" andalso not (contains_sorry m) then
                 (r, m)  (* rescue 完全收拢 *)
               else
                 (* rescue 失败、超时、报错，或者只部分收拢（含 sorry）——> 尝试 split *)
                 (case (split_opt, split_txt_opt) of
                    (SOME split_ref, SOME split_txt) =>
                      split_then_sh_text split_ref split_txt state_subgoaled
                      | _ => (r, m)) end
                        
         | _ =>
             (* 没有 rescue；如果有 split 就用之，否则返回 fast_result *)
             (case (split_opt, split_txt_opt) of
                (SOME split_ref, SOME split_txt) =>
                  split_then_sh_text split_ref split_txt state0
              | _ => fast_result)))
in
  final_result
end

(* 兼容旧名：不传 rescue *)
fun my_hammer_or_method_away i st m_ref method_text adref adtxt =
  my_hammer_or_method_away4 i st m_ref method_text adref adtxt NONE NONE

(* Example usage *)
val input_string = "Try this: by (smt (verit) one_le_numeral power2_less_eq_zero_iff power_increasing power_one_right power_zero_numeral) (187 ms)"

val input_string1 = "Try this: by (metis add.commute add_0 add_diff_eq add_increasing2 diff_diff_eq2 diff_ge_0_iff_ge mult.right_neutral mult_1 power2_eq_square right_diff_distrib zero_le_mult_iff zero_le_square) (> 1.0 s, timed out)";
val result = extract_one_liner_proof(input_string);
val _ = writeln result
val _ = writeln (extract_one_liner_proof "cvc5: Try this:\n  apply (metis CSTATE_disj4' CSTATE_starting_transaction_otherside_invariant1 HSTATE_X_Evict_invariant1 H_msg_P_same_def\n    MESI_State.distinct(11) SharedSnpInv'_CSTATE_invariant5 i23) (343 ms) ")







fun my_hammer_or_method_away
  i state0 (m_ref : (Method.text * Position.range)) (method_text : string) adref adtxt =
let
  val _ = writeln ("=== ENTER my_hammer_or_method_away for subgoal " ^ Int.toString i ^ " ===")

  (* 赢家：只在 success 时写入；否则保持 NONE *)
  val winner_slot = Synchronized.var "race_winner" (NONE : (string * string) option)

  (* “两边句柄都就绪”的屏障；避免取消丢失 *)
  val started = Synchronized.var "race_started" 0

  (* 保存两边的 future 句柄 *)
  val sh_ref = Unsynchronized.ref (NONE : (string * string) future option)
  val um_ref = Unsynchronized.ref (NONE : (string * string) future option)

  fun publish_if_success (res: string * string) : bool =
    if #1 res = "success" then
      Synchronized.change_result winner_slot
        (fn NONE => (true, SOME res) | SOME w => (false, SOME w))
    else false

  fun wait_until_both_started () =
    if Synchronized.value started = 2 then ()
    else (OS.Process.sleep (Time.fromMilliseconds 1); wait_until_both_started ())

  (* Method 分支 *)
  val um_fut =
    Future.fork (fn () =>
      let
        val _ = writeln ("METHOD Future: starting")
        (* 先计数，保证“另一边赢时可见我” *)
        val _ = Synchronized.change started (fn n => n + 1)
        val res = solved_by_method_message i state0 m_ref method_text
        val _ = writeln ("METHOD Future: result = " ^ #1 res)
        val won = publish_if_success res
        val _ =
          if won then
            (wait_until_both_started ();
             (case !sh_ref of SOME fut => (writeln "METHOD won -> cancel SH"; Future.cancel fut)
                            | NONE => writeln "METHOD won but SH handle not ready"))
          else ()
      in
        res
      end)

  val _ = um_ref := SOME um_fut

  (* Sledgehammer 分支 *)
  val sh_fut =
    Future.fork (fn () =>
      let
        val _ = writeln ("SH Future: starting")
        (* 先计数，保证“另一边赢时可见我” *)
        val _ = Synchronized.change started (fn n => n + 1)
        val (outc, msg) =
          my_hammer_away i (Seq.the_result "" (Proof.apply adref state0))
        val _ = writeln ("SH Future: sledgehammer returned: " ^ outc)
        val msg' =
          if outc = "success"
          then  "apply " ^ adtxt ^ " " ^ extract_one_liner_proof (remove_prefer i msg)
          else msg
        val res = (outc, msg')
        val won = publish_if_success res
        val _ =
          if won then
            (wait_until_both_started ();
             (case !um_ref of SOME fut => (writeln "SH won -> cancel METHOD"; Future.cancel fut)
                            | NONE => writeln "SH won but METHOD handle not ready"))
          else ()
      in
        res
      end)

  val _ = sh_ref := SOME sh_fut

  fun wait () =
    (case Synchronized.value winner_slot of
       SOME res => res
     | NONE =>
         if Future.is_finished sh_fut andalso Future.is_finished um_fut
         then ("fail", "no proof found")
         else (OS.Process.sleep (Time.fromMilliseconds 10); wait ()))

  val result = wait ()

  (* 无论结果如何，务必回收 *)
  val _ = (ignore (Exn.capture Future.join sh_fut);
           ignore (Exn.capture Future.join um_fut))

  val _ = writeln ("=== EXIT my_hammer_or_method_away with result: " ^ #1 result ^ " ===")
in
  result
end


(* ========= NEW: Strategy kind & v5 runner ========= *)
(* ---------- v5 tuning knobs & logging ---------- *)

(* 打开/关闭调试输出 *)
val v5_debug = Unsynchronized.ref true;
fun V5_LOG s = ( if !v5_debug then Output.information s else ());

(* 超时（秒）——可以按需调小/调大再观察 *)
val v5_timeout_plain_secs    = 2;   (* PLAIN 的方法执行超时 *)
val v5_timeout_sh_method_secs = 6;  (* SH/TRY0 预处理方法超时 *)
(* Sledgehammer 自身的超时通常在 my_hammer_away 里设置，若你那边 expose 了参数可在那边调 *)


(* PLAIN：仅方法，带硬超时 + 耗时记录 *)
fun run_plain i (m_ref : (Method.text * Position.range)) (m_txt : string) state0 : (string * string) =
  let
    val t0 = Time.now ()
    val st_pref = Proof.prefer i (silence_state state0)
    val st_sub  = (#2 o Subgoal.subgoal_cmd Binding.empty_atts NONE (false, [])) st_pref
  in
    (case apply_method_with_timeout v5_timeout_plain_secs m_ref st_sub of
       SOME (SOME (Seq.Result st_after, _)) =>
         let
           (* ★ 完全应用：state + method + text *)
           val (ok, msg) = solved_by_method_message i st_after m_ref m_txt
           val dt = Time.- (Time.now (), t0)
           val _ = V5_LOG ("v5[PLAIN] " ^ m_txt ^ " -> " ^ (if ok = "success" then "success" else "no-close")
                           ^ " in " ^ Time.toString dt)
         in
           if ok = "success" then ("success", "apply " ^ m_txt ^ "\n" ^ msg)
           else ("fail", "plain method did not close: " ^ m_txt)
         end
     | SOME (SOME (Seq.Error _, _)) => ("fail", "plain method error: " ^ m_txt)
     | SOME NONE => ("fail", "plain method produced no state: " ^ m_txt)
     | NONE => ("fail", "plain method timeout (" ^ Int.toString v5_timeout_plain_secs ^ "s): " ^ m_txt))
  end

(* SH：方法（硬超时） + sledgehammer *)
fun run_sh i (m_ref : (Method.text * Position.range)) (m_txt : string) state0 : (string * string) =
  let
    val t0 = Time.now ()
    val st_pref   = Proof.prefer i (silence_state state0)
    val st_sub    = (#2 o Subgoal.subgoal_cmd Binding.empty_atts NONE (false, [])) st_pref
  in
    (case apply_method_with_timeout v5_timeout_sh_method_secs m_ref st_sub of
       SOME (SOME (Seq.Result st_after, _)) =>
         let
           (* ★ 参数顺序：先 state 后 subgoal index *)
           val (outc, msg) = my_hammer_away 1 st_after
           val dt = Time.- (Time.now (), t0)
           val _ = V5_LOG ("v5[SH] " ^ m_txt ^ " -> " ^ outc ^ " in " ^ Time.toString dt)
         in
           if outc = "success"
           then ("success", "apply " ^ m_txt ^ "\n" ^ extract_one_liner_proof (remove_prefer 1 msg))
           else ("fail", msg)
         end
     | SOME (SOME (Seq.Error _, _)) =>
         ("fail", "pre-method error: " ^ m_txt)
     | SOME NONE =>
         ("fail", "pre-method produced no state: " ^ m_txt)
     | NONE =>
         ("fail", "pre-method timeout (" ^ Int.toString v5_timeout_sh_method_secs ^ "s): " ^ m_txt))
  end

(* TRY0：目前直接复用 SH 的流程；如需严格等同 v4，可在此改为真正 try0 的实现 *)
fun run_try0 i (m_ref : (Method.text * Position.range)) (m_txt : string) state0 : (string * string) =
  run_sh i m_ref m_txt state0


fun group_strategies (ss : ms_strategy list) : ms_strategy list list =
  let
    fun ord_of (_, _, _, k) = k
    (* sort 需要 'a ord = 'a * 'a -> order *)
    val sorted = sort (fn (a, b) => Int.compare (ord_of a, ord_of b)) ss

    fun go ([], NONE, cur, acc) = rev (if null cur then acc else cur :: acc)
      | go ([], SOME _, cur, acc) = rev (cur :: acc)
      | go (x :: xs, NONE, cur, acc) = go (xs, SOME (ord_of x), [x], acc)
      | go (x :: xs, SOME k, cur, acc) =
          let val k' = ord_of x in
            if k' = k then go (xs, SOME k, x :: cur, acc)
            else go (xs, SOME k', [x], cur :: acc)
          end
  in
    go (sorted, NONE, [], [])
  end
fun group_strategies (ss : ms_strategy list) : ms_strategy list list =
  let
    fun ord_of (_, _, _, k) = k
    (* sort 需要 'a ord = 'a * 'a -> order *)
    val sorted = sort (fn (a, b) => Int.compare (ord_of a, ord_of b)) ss

    fun go ([], NONE, cur, acc) = rev (if null cur then acc else cur :: acc)
      | go ([], SOME _, cur, acc) = rev (cur :: acc)
      | go (x :: xs, NONE, cur, acc) = go (xs, SOME (ord_of x), [x], acc)
      | go (x :: xs, SOME k, cur, acc) =
          let val k' = ord_of x in
            if k' = k then go (xs, SOME k, x :: cur, acc)
            else go (xs, SOME k', [x], cur :: acc)
          end
  in
    go (sorted, NONE, [], [])
  end


(* 把同一 order 的策略放在一个 Future group 里并发跑；
   第一个成功者通过 promise 发布结果，同时 cancel_group 取消其它；
   主线程 join 这个 promise，立刻返回；不再 join 其它 worker。 *)
fun race_one_group i (state0: Proof.state) (bucket: ms_strategy list) : (string * string) =
  let
    val grp = Future.worker_subgroup ()
    val t_group0 = Time.now ()

    (* 用 promise 承接“第一个成功结果” *)
    val res_promise : (string * string) Future.future =
      Future.promise (fn () => ())   (* abort 不需要做事 *)

    fun publish_success (pair: string * string) =
      (* 可能会有并发 fulfill；捕获并忽略“Concurrent attempt to fulfill promise” *)
      ignore (Exn.capture (fn () => Future.fulfill res_promise pair) ());

    fun spawn_one strat () =
      let
        val t0 = Time.now ()
        val (outc, msg) =
          (case strat of
             (MS_PLAIN, m_ref, m_txt, _) => run_plain i m_ref m_txt state0
           | (MS_SH,    m_ref, m_txt, _) => run_sh    i m_ref m_txt state0
           | (MS_TRY0,  m_ref, m_txt, _) => run_try0  i m_ref m_txt state0)
        val dt = Time.- (Time.now (), t0)
        val tag =
          (case strat of
              (MS_PLAIN, _, _, _) => "PLAIN"
              | (MS_SH,    _, _, _) => "SH"
              | (MS_TRY0,  _, _, _) => "TRY0")

        val _ = V5_LOG ("v5[race:" ^ tag ^ "] finished in " ^ Time.toString dt ^ " -> " ^ outc)
        val _ =
          (case outc of
             "success" => (publish_success (outc, msg); Future.cancel_group grp)
           | _ => ())
      in () end

    val futs =
      Future.forks {name = "v5/race", group = SOME grp, deps = [], pri = 0, interrupts = true}
        (map (fn s => fn () => spawn_one s ()) bucket)

    (* 看门狗：所有 worker 全部结束且尚无成功时，发布一个失败结果，避免主线程一直等 *)
    val _ = Future.fork (fn () =>
              (ignore (Future.join_results futs);
               (case Future.peek res_promise of
                  NONE =>
                    Future.fulfill res_promise ("fail",
                      "all strategies failed in " ^
                      Time.toString (Time.- (Time.now (), t_group0)))
                | SOME _ => ());
               ()))

    val (outc, txt) = Future.join res_promise
    val dt_group = Time.- (Time.now (), t_group0)
    val _ = V5_LOG ("v5[race] result=" ^ outc ^ " in " ^ Time.toString dt_group)

    (* 已发布结果；为了保险，再次取消同组任务（若还没被取消） *)
    val _ = Future.cancel_group grp

    (* 不 join 其它 futs：让 scheduler 清理它们的取消；这与 v4 的体感一致 *)
  in (outc, txt) end


(* =========== 对外主入口：v5 只吃“策略列表” =========== *)
fun my_hammer_or_method_away5 i (state0: Proof.state) (strats: ms_strategy list) : (string * string) =
  let
    val t0 = Time.now ()
    val buckets = group_strategies strats   (* 你现有的分桶函数：按 order 排序再分组 *)
    val _ = V5_LOG ("v5/start: " ^ Int.toString (length buckets) ^ " orders")

    fun step ([], _) = ("fail", "no proof found by v5")
      | step (bucket :: more, ord) =
          let
            val b0 = Time.now ()
            val _ = V5_LOG ("v5/order " ^ Int.toString ord ^ " size=" ^ Int.toString (length bucket))
            val (outc, txt) = race_one_group i state0 bucket
            val bd = Time.- (Time.now (), b0)
            val _ = V5_LOG ("v5/order " ^ Int.toString ord ^ " -> " ^ outc ^ " in " ^ Time.toString bd)
          in
            if outc = "success" then (outc, txt) else step (more, ord + 1)
          end



    val res as (rc, _) = step (buckets, 1)
    val dt = Time.- (Time.now (), t0)
    val _ = V5_LOG ("v5/total " ^ Time.toString dt ^ " result=" ^ rc)
  in res end




end;
