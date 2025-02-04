
theory Sketch_Example
  imports Super_Sketch.Super_Sketch
begin


lemma "\<forall>x. P x \<longrightarrow> Q x \<or> P x"
  sketch(intro allI impI disjI2)
proof (intro allI impI disjI2)
  fix x :: 'a
  assume "P x"
  show "P x"
    using \<open>P x\<close> by auto
qed


end