theory Super_Fix
  imports Main
  keywords "super_fix" :: diag
begin

ML_file "./ml/pred.ML"
ML_file "./ml/ops.ML"
ML_file "./ml/print.ML"
ML_file "./ml/imports.ML"
ML_file "./ml/get.ML"
ML_file "./ml/seps.ML"
ML_file "./ml/actions.ML"
ML_file "./ml/client.ML"
ML_file "./ml/llm.ML"
ML_file "./ml/HammerAlt.ML"
ML_file "./ml/sketcher.ML"
ML_file "./ml/fixer.ML"

ML \<open>

val _ = Outer_Syntax.command \<^command_keyword>\<open>super_fix\<close>
  ("Takes an input .thy file and attempts to fix it "
  ^ "according to the supplied strategy writing the "
  ^ "result to the second input directory. It assumes "
  ^ "that the imports from where it is called coincide "
  ^ "with that of the input .thy file.")
  ((Fixer.parse -- Parse.path) >>
    (fn (fixer, read_thy_file) => 
        Toplevel.keep (fn st => 
          Fixer.fix_end_to_end {fixer=fixer} (Toplevel.theory_of st) read_thy_file
        )
    )
  );
\<close>

end