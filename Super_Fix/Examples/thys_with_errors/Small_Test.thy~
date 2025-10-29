theory Small_Test
  imports Complex_Main

begin


lemma real_sqrt_le_iff': "x \<ge> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> sqrt x \<le> y \<longleftrightarrow> x \<le> y ^ 2"
  using real_le_lsqrt sqrt_le_D by blast
  

lemma sqrt_le_itself: "1 \<le> x \<Longrightarrow> sqrt x \<le> x"
  by (metis linorder_linear mult_cancel_right1 mult_le_cancel_left1 mult_le_cancel_left2 not_one_le_zero order_trans real_sqrt_abs real_sqrt_abs2 real_sqrt_eq_iff real_sqrt_pow2_iff)

lemma sin_cos_squared_add3:
  fixes x:: "'a:: {banach,real_normed_field}"
  shows "x * (sin t)\<^sup>2 + x * (cos t)\<^sup>2 = x"
  by (metis distrib_left mult.right_neutral sin_cos_squared_add)
  

lemma "\<bar>\<bar>a\<bar> - \<bar>b\<bar>\<bar> \<le> \<bar>a - b\<bar>" for a::real
  by simp
  

lemma "{a,b} \<inter> {b,c} = (if a=c then {a,b} else {b})"
  by auto

lemma binomial_suc:"Suc (n\<^sup>2 + 2 * n) = (Suc n)\<^sup>2"
  apply(induct n)
  apply simp
  by (simp add: power2_eq_square)
  

lemma "((\<forall> x. \<phi> x) \<and> (\<forall> x. \<psi> x)) = (\<forall> x. (\<phi> x \<and> \<psi> x))"  
  by blast

lemma "(\<Sum>i\<le>n. 2*i - 1) = n\<^sup>2" for n::nat
  apply(induct n)
  apply simp
  by (simp add: power2_eq_square)
  

lemma 
  assumes "y \<in> {f x |x. P x}"
  obtains x where "y = f x" and "P x"
  using assms by blast
  

end