theory Small_Test
  imports Complex_Main

begin


lemma real_sqrt_le_iff': "x \<ge> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> sqrt x \<le> y \<longleftrightarrow> x \<le> y ^ 2"
  apply blast
  done

lemma sqrt_le_itself: "1 \<le> x \<Longrightarrow> sqrt x \<le> x"
  sorry

lemma sin_cos_squared_add3:
  fixes x:: "'a:: {banach,real_normed_field}"
  shows "x * (sin t)\<^sup>2 + x * (cos t)\<^sup>2 = x"
  apply simp
  done

lemma "\<bar>\<bar>a\<bar> - \<bar>b\<bar>\<bar> \<le> \<bar>a - b\<bar>" for a::real
  apply rule
  done

lemma "{a,b} \<inter> {b,c} = (if a=c then {a,b} else {b})"
  sorry

lemma binomial_suc:"Suc (n\<^sup>2 + 2 * n) = (Suc n)\<^sup>2"
  apply(induct n)
  apply simp
  apply rule
  done

lemma "((\<forall> x. \<phi> x) \<and> (\<forall> x. \<psi> x)) = (\<forall> x. (\<phi> x \<and> \<psi> x))"  
  sorry

lemma "(\<Sum>i\<le>n. 2*i - 1) = n\<^sup>2" for n::nat
  apply(induct n)
  apply simp
  apply rule
  done

lemma 
  assumes "y \<in> {f x |x. P x}"
  obtains x where "y = f x" and "P x"
  apply auto
  done

end