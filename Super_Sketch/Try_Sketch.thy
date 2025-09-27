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
ML_file "../../super_sketch_and_super_fix/Super_Fix/ml/sketcher.ML"
ML_file "../../super_sketch_and_super_fix/Super_Fix/ml/fixer.ML"

(* sketching operations *)

ML \<open>

datatype strategy = 
  SORRYS 
  | TRY0 of (Method.text_range * Token.T list) list
  | TRY of (Method.text_range * Token.T list) list
  | HAMMER of (Method.text_range * Token.T list) list

fun strategy_of_str str ms =
  (case str of 
    "SORRYS" => SORRYS
    | "TRY0" => TRY0 ms
    | "TRY" => TRY ms
    | "HAMMER" => HAMMER ms
    | another => raise Fail ("mode_of_str: unknown mode" ^ another));

val parse_methods = \<^keyword>\<open>[\<close> |-- Parse.list (Scan.trace Method.parse) --| \<^keyword>\<open>]\<close>;

val parse_strategy = (Parse.embedded -- (Scan.option parse_methods))
  >> (fn (mode_txt, opt_ms) => 
    strategy_of_str mode_txt (case opt_ms of NONE => [] | SOME ms' => ms')
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

fun try_sketch strategy format opt_m st = 
  let
    val _ = Output.tracing "Producing goals to try..."
    val sorryed_str = Fixer.fix_with_sketch format 0 (get_fixer strategy []) opt_m st;
    val result = (case strategy of
      SORRYS => sorryed_str
      | mode =>
        let 
           val acts = Actions.make (Toplevel.theory_of st) sorryed_str
           val fixed = Actions.apply_all acts st
            |> Fixer.generic_repair_sorrys false 
              (fn _ => fn _ => []) (get_fixer mode) (map SOME (get_methods mode))
            |> map (fn (act, _, _) => Actions.text_of act)
            |> Library.space_implode ""
        in fixed end)
  in result end;

val _ = Outer_Syntax.command \<^command_keyword>\<open>try_sketch\<close>
  "Makes a proof-sketch and attempts intermediate subgoals."
  (parse_strategy -- (Scan.option (Scan.trace Method.parse)) >> 
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

lemma 
  assumes "\<forall>x. P x" and "\<forall>x. Q x" and "R"
  shows "\<And>a b. P a \<and> P b \<and> P c \<and> P d \<and> P e"
  using assms
  try_sketch TRY0[simp] (intro conjI)
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