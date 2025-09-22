theory Example
  imports Complex_Main

begin


lemma real_sqrt_le_iff': "x \<ge> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> sqrt x \<le> y \<longleftrightarrow> x \<le> y ^ 2"
  apply blast
  done

lemma sqrt_le_itself: "1 \<le> x \<Longrightarrow> sqrt x \<le> x"
  sorry

lemma sqrt_real_nat_le:"sqrt (real n) \<le> real n"
  apply simp
  done

lemma semiring_factor_left:
  fixes b:: "'a::semiring"
  shows "a * b + a * c = a * (b + c)"
  apply simp
  done

lemma sin_cos_squared_add3:
  fixes x:: "'a:: {banach,real_normed_field}"
  shows "x * (sin t)\<^sup>2 + x * (cos t)\<^sup>2 = x"
  apply simp
  done

lemma sin_cos_squared_add4:
  fixes x:: "'a:: {banach,real_normed_field}"
  shows "x * (cos t)\<^sup>2 + x * (sin t)\<^sup>2 = x"
  apply simp
  done

lemma "\<phi> \<longrightarrow> (\<psi> \<longrightarrow> \<phi>)"
  sorry

lemma "(\<phi> \<or> \<phi>) = (\<phi> \<and> \<phi>)" 
  sorry

lemma "\<bar>\<bar>a\<bar> - \<bar>b\<bar>\<bar> \<le> \<bar>a - b\<bar>" for a::real
  apply rule
  done

lemma "(\<phi> \<longrightarrow> \<not> \<psi>) = (\<psi> \<longrightarrow> \<not> \<phi>)" 
  sorry

lemma "{a,b} \<inter> {b,c} = (if a=c then {a,b} else {b})"
  sorry

lemma "(\<exists>x. \<forall>y. \<phi> x y) \<longrightarrow> (\<forall>y. \<exists>x. \<phi> x y)"  
  sorry

lemma "(\<forall>x. \<phi> x \<longrightarrow> \<psi>) = ((\<exists>x. \<phi> x) \<longrightarrow> \<psi>)"  
  sorry

lemma binomial_suc:"Suc (n\<^sup>2 + 2 * n) = (Suc n)\<^sup>2"
  apply(induct n)
  apply simp
  apply rule
  done

lemma "((\<forall> x. \<phi> x) \<and> (\<forall> x. \<psi> x)) = (\<forall> x. (\<phi> x \<and> \<psi> x))"  
  sorry

lemma "((\<phi> \<or> \<psi>) \<or> \<gamma>) \<longrightarrow> \<phi> \<or> (\<psi> \<or> \<gamma>)"  
  sorry

lemma "1 \<in> {x. x < (2::int)}"
  sorry

lemma "(1,3) \<in> {(x::int,3) |x. x< 2}"
  sorry

lemma "(\<phi> \<longrightarrow> \<psi> \<longrightarrow> \<gamma>) \<longrightarrow> (\<phi> \<longrightarrow> \<psi>) \<longrightarrow> \<phi> \<longrightarrow> \<gamma>" 
  sorry

lemma "((\<exists> x. \<phi> x) \<or> (\<exists> x. \<psi> x)) = (\<exists> x. (\<phi> x \<or> \<psi> x))"  
  apply linarith
  done

lemma "(\<Sum>i\<le>n. 2*i - 1) = n\<^sup>2" for n::nat
  apply(induct n)
  apply simp
  apply rule
  done

lemma "(\<phi> \<longrightarrow> (\<psi> \<and> \<gamma>)) \<longrightarrow> (\<psi> \<longrightarrow> \<not> \<gamma>) \<longrightarrow> \<not> \<phi>" 
  sorry

lemma "(\<not> (\<forall> x. \<phi> x)) = (\<exists> x. \<not> \<phi> x)"  
  apply linarith
  done

lemma "(\<xi> \<longrightarrow> \<phi>) \<longrightarrow> (\<phi> \<longrightarrow> (\<psi> \<and> \<gamma>)) \<longrightarrow> (\<psi> \<longrightarrow> \<not> \<gamma>) \<longrightarrow> \<not> \<xi>" 
  sorry

lemma 
  assumes "y \<in> {f x |x. P x}"
  obtains x where "y = f x" and "P x"
  apply auto
  done

lemma 
  assumes "x \<in> {x. P x}"
  shows "P x"
  apply rule
  done

end