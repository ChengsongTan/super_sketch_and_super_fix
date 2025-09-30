theory Try_Sketch
  imports "Super_Fix.Super_Fix"
  keywords "try_sketch" :: diag
begin

ML \<open>

fun try_sketch fixer format opt_m st = 
  let
    val _ = Output.tracing "Producing goals to try..."
    val sorryed_str = Fixer.fix_with_sketch format 0 (fn _ => "sorry") opt_m st;
    val result = 
      let 
        val acts = Actions.make (Toplevel.theory_of st) sorryed_str;
        val fixed = Actions.apply_all acts st
          |> Fixer.generic_repair_sorrys false 
            (fn _ => fn _ => []) st (Fixer.build fixer) (map SOME (Fixer.get_methods fixer))
          |> map (fn (act, _, _) => Actions.text_of act)
          |> Library.space_implode ""
      in fixed end
  in result end;

val _ = Outer_Syntax.command \<^command_keyword>\<open>try_sketch\<close>
  "Makes a proof-sketch and attempts intermediate subgoals."
  (Fixer.parse -- (Scan.option (Scan.trace Method.parse)) >> 
    (fn (sketch_mode, opt_m0) =>
      Toplevel.keep_proof (fn st =>
        let
          val final_sketch = try_sketch sketch_mode Sketcher.SHOW_IFS opt_m0 st;
          val _ = Output.information (Active.sendback_markup_command final_sketch);
        in () end
      )
   ));

\<close>

(* example *)

(* declare [[ML_print_depth = 4000000]] *)
(* sledgehammer_params [dont_minimize, dont_try0, timeout = 15, max_proofs=1] *)
lemma 
  assumes "\<forall>x. P x" and "\<forall>x. Q x" and "R"
  shows "\<And>a b. P a \<and> P b \<and> P c \<and> P d \<and> P e"
  using assms
  try_sketch SORRYS[simp] (intro conjI)
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
  try_sketch HAMMER[simp] (induct n)
proof(induct n)
  show goal0: "length [0..<0] = 0"
    by simp
next
  show goal1: "length [0..<Suc n] = Suc n"
    if "length [0..<n] = n"
    for n :: "nat"
    using that
    by simp
qed

end