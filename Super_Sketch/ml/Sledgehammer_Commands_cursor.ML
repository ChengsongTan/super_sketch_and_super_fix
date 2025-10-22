(*  
  Enhanced version for double_sketch optimization - SIMPLIFIED VERSION
  Critical fix: Line 538 corrected to include adtxt parameter properly
  
  This is a minimal version that fixes the adsimp parameter issue without breaking compatibility
*)

signature SLEDGEHAMMER_COMMANDS_CURSOR =
sig
  val my_hammer_or_method_away: int -> Proof.state -> (Method.text * Position.range) -> string -> (Method.text * Position.range) -> string -> (string * string)
  val extract_one_liner_proof: string -> string
end;

structure Sledgehammer_Commands_cursor : SLEDGEHAMMER_COMMANDS_CURSOR =
struct

(* Import everything we need from the original structure and Isabelle libraries *)
open Sledgehammer_Commands1

(* Define subgoal_count if not available - standard Isabelle function *)
fun subgoal_count state = 
  let val {goal, ...} = Proof.goal state
  in Thm.nprems_of goal end
  handle _ => 0

(* Helper functions for text processing - moved from end of file *)
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

(* 
  CRITICAL FIX: Enhanced my_hammer_or_method_away with corrected adtxt parameter inclusion
  This fixes the missing adsimp method issue in proof output
*)
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

    (* Method solving utilities from original *)
    fun solved_by_method_message i state0 (m_ref : (Method.text * Position.range)) method_text =
      let
        val state_after = Seq.the_result "" (Proof.apply m_ref state0)
        val goals_before = subgoal_count state0
        val goals_after = subgoal_count state_after
      in
        if goals_after = 0 then ("success", "apply " ^ method_text ^ " done")
        else if goals_after < goals_before then ("partial", "apply " ^ method_text ^ " (* partial *)")
        else ("fail", "apply " ^ method_text ^ " (* failed *)")
      end
      handle _ => ("fail", "apply " ^ method_text ^ " (* error *)")

    (* SH my_hammer_away i state0 *)
    val sh_fut =
      Future.fork (fn () =>
        let val (outc, msg) = my_hammer_away i (Seq.the_result "" (Proof.apply adref state0))
            (* CRITICAL FIX: Properly include adtxt parameter in success case *)
            val msg' = if outc = "success" then "apply " ^ adtxt ^ " " ^ remove_prefer i msg else msg
        in win (outc, msg') um_ref end)
    val _ = sh_ref := SOME sh_fut

    (* Method competition *)
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

(* Use the original extract_one_liner_proof from Sledgehammer_Commands1 *)
val extract_one_liner_proof = Sledgehammer_Commands1.extract_one_liner_proof

end;