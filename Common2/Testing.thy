theory Testing imports BasicInvariants begin

thm allTransitions'_def

lemma my_map_concat: shows "List.concat (List.map (\<lambda>f. f T 0) ([t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, 
    t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, 
    t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, t48, t49, t50, t51, t52, 
    t53, t54, t55, t56, t57, t58, t59, t60, t61, t62, t63, t64, t65, t66, t67, t68] )) =
   t1 T 0 @ t2 T 0 @ t3 T 0 @ t4 T 0 @ t5 T 0 @ t6 T 0 @ t7 T 0 @ t8 T 0 @ t9 T 0 @ t10 T 0 @ t11 T 0 
    @ t12 T 0 @ t13 T 0 @ t14 T 0 @ t15 T 0 @ t16 T 0 @ t17 T 0 @ t18 T 0 
    @ t19 T 0 @ t20 T 0 @ t21 T 0 @ t22 T 0 @ t23 T 0 @ t24 T 0 @ t25 T 0 @ t26 T 0 @ t27 T 0 @ t28 T 0 
    @ t29 T 0 @ t30 T 0 @ t31 T 0 @ t32 T 0 @ t33 T 0 @ t34 T 0 @ t35 T 0 @ t36 T 0 @ t37 T 0 @ t38 T 0 
    @ t39 T 0 @ t40 T 0 @ t41 T 0 @ 
    t42 T 0 @ t43 T 0 @ t44 T 0 @ t45 T 0 @ t46 T 0 @ t47 T 0 @ t48 T 0 @ t49 T 0 @ t50 T 0 @ t51 T 0 
    @ t52 T 0 @ t53 T 0 @ t54 T 0 @ t55 T 0 @ t56 T 0 @ t57 T 0 @ t58 T 0 @ t59 T 0 @ t60 T 0 @ t61 T 0 
    @ t62 T 0 @ t63 T 0 @ t64 T 0 @ t65 T 0 @ t66 T 0 @ t67 T 0 @ t68 T 0"
  by simp




lemma my_set_concat_split_68elems : shows "(\<forall> T' \<in> set (l1 @ l2 @ l3 @ l4 @ l5 @ l6 @ l7 @ l8 @ l9 @ l10 @ l11 @ l12 @ l13 @ l14 @ l15 @ l16 @ l17 @ l18 @ l19 @ l20 @ l21 @ l22 @ l23 @ l24 @ l25 @ l26 @ l27 @ l28 @ l29 @ l30 @ l31 @ l32 @ l33 @ l34 @ l35 @ l36 @ l37 @ l38 @ l39 @ l40 @ l41 @ l42 @ l43 @ l44 @ l45 @ l46 @ l47 @ l48 @ l49 @ l50 @ l51 @ l52 @ l53 @ l54 @ l55 @ l56 @ l57 @ l58 @ l59 @ l60 @ l61 @ l62 @ l63 @ l64 @ l65 @ l66 @ l67 @ l68). P T') =
  ((\<forall> T' \<in> set l1. P T') \<and> (\<forall> T' \<in> set l2. P T') \<and> (\<forall> T' \<in> set l3. P T') \<and> (\<forall> T' \<in> set l4. P T') \<and> (\<forall> T' \<in> set l5. P T') \<and> (\<forall> T' \<in> set l6. P T') \<and> (\<forall> T' \<in> set l7. P T') \<and> (\<forall> T' \<in> set l8. P T') \<and> (\<forall> T' \<in> set l9. P T') \<and> (\<forall> T' \<in> set l10. P T') \<and> (\<forall> T' \<in> set l11. P T') \<and> (\<forall> T' \<in> set l12. P T') \<and> (\<forall> T' \<in> set l13. P T') \<and> (\<forall> T' \<in> set l14. P T') \<and> (\<forall> T' \<in> set l15. P T') \<and> (\<forall> T' \<in> set l16. P T') \<and> (\<forall> T' \<in> set l17. P T') \<and> (\<forall> T' \<in> set l18. P T') \<and> (\<forall> T' \<in> set l19. P T') \<and> (\<forall> T' \<in> set l20. P T') \<and> (\<forall> T' \<in> set l21. P T') \<and> (\<forall> T' \<in> set l22. P T') \<and> (\<forall> T' \<in> set l23. P T') \<and> (\<forall> T' \<in> set l24. P T') \<and> (\<forall> T' \<in> set l25. P T') \<and> (\<forall> T' \<in> set l26. P T') \<and> (\<forall> T' \<in> set l27. P T') \<and> (\<forall> T' \<in> set l28. P T') \<and> (\<forall> T' \<in> set l29. P T') \<and> (\<forall> T' \<in> set l30. P T') \<and> (\<forall> T' \<in> set l31. P T') \<and> (\<forall> T' \<in> set l32. P T') \<and> (\<forall> T' \<in> set l33. P T') \<and> (\<forall> T' \<in> set l34. P T') \<and> (\<forall> T' \<in> set l35. P T') \<and> (\<forall> T' \<in> set l36. P T') \<and> (\<forall> T' \<in> set l37. P T') \<and> (\<forall> T' \<in> set l38. P T') \<and> (\<forall> T' \<in> set l39. P T') \<and> (\<forall> T' \<in> set l40. P T') \<and> (\<forall> T' \<in> set l41. P T') \<and> (\<forall> T' \<in> set l42. P T') \<and> (\<forall> T' \<in> set l43. P T') \<and> (\<forall> T' \<in> set l44. P T') \<and> (\<forall> T' \<in> set l45. P T') \<and> (\<forall> T' \<in> set l46. P T') \<and> (\<forall> T' \<in> set l47. P T') \<and> (\<forall> T' \<in> set l48. P T') \<and> (\<forall> T' \<in> set l49. P T') \<and> (\<forall> T' \<in> set l50. P T') \<and> (\<forall> T' \<in> set l51. P T') \<and> (\<forall> T' \<in> set l52. P T') \<and> (\<forall> T' \<in> set l53. P T') \<and> (\<forall> T' \<in> set l54. P T') \<and> (\<forall> T' \<in> set l55. P T') \<and> (\<forall> T' \<in> set l56. P T') \<and> (\<forall> T' \<in> set l57. P T') \<and> (\<forall> T' \<in> set l58. P T') \<and> (\<forall> T' \<in> set l59. P T') \<and> (\<forall> T' \<in> set l60. P T') \<and> (\<forall> T' \<in> set l61. P T') \<and> (\<forall> T' \<in> set l62. P T') \<and> (\<forall> T' \<in> set l63. P T') \<and> (\<forall> T' \<in> set l64. P T') \<and> (\<forall> T' \<in> set l65. P T') \<and> (\<forall> T' \<in> set l66. P T') \<and> (\<forall> T' \<in> set l67. P T') \<and> (\<forall> T' \<in> set l68. P T'))"
proof (-)
  show goal1: "(\<forall>T'\<in>set (l1 @ l2 @ l3 @ l4 @ l5 @ l6 @ l7 @ l8 @ l9 @ l10 @ l11 @ l12 @ l13 @ l14 @ l15 @ l16 @ l17 @ l18 @ l19 @ l20 @ l21 @ l22 @ l23 @ l24 @ l25 @ l26 @ l27 @ l28 @ l29 @ l30 @ l31 @ l32 @ l33 @ l34 @ l35 @ l36 @ l37 @ l38 @ l39 @ l40 @ l41 @ l42 @ l43 @ l44 @ l45 @ l46 @ l47 @ l48 @ l49 @ l50 @ l51 @ l52 @ l53 @ l54 @ l55 @ l56 @ l57 @ l58 @ l59 @ l60 @ l61 @ l62 @ l63 @ l64 @ l65 @ l66 @ l67 @ l68). P T') = ((\<forall>T'\<in>set l1. P T') \<and> (\<forall>T'\<in>set l2. P T') \<and> (\<forall>T'\<in>set l3. P T') \<and> (\<forall>T'\<in>set l4. P T') \<and> (\<forall>T'\<in>set l5. P T') \<and> (\<forall>T'\<in>set l6. P T') \<and> (\<forall>T'\<in>set l7. P T') \<and> (\<forall>T'\<in>set l8. P T') \<and> (\<forall>T'\<in>set l9. P T') \<and> (\<forall>T'\<in>set l10. P T') \<and> (\<forall>T'\<in>set l11. P T') \<and> (\<forall>T'\<in>set l12. P T') \<and> (\<forall>T'\<in>set l13. P T') \<and> (\<forall>T'\<in>set l14. P T') \<and> (\<forall>T'\<in>set l15. P T') \<and> (\<forall>T'\<in>set l16. P T') \<and> (\<forall>T'\<in>set l17. P T') \<and> (\<forall>T'\<in>set l18. P T') \<and> (\<forall>T'\<in>set l19. P T') \<and> (\<forall>T'\<in>set l20. P T') \<and> (\<forall>T'\<in>set l21. P T') \<and> (\<forall>T'\<in>set l22. P T') \<and> (\<forall>T'\<in>set l23. P T') \<and> (\<forall>T'\<in>set l24. P T') \<and> (\<forall>T'\<in>set l25. P T') \<and> (\<forall>T'\<in>set l26. P T') \<and> (\<forall>T'\<in>set l27. P T') \<and> (\<forall>T'\<in>set l28. P T') \<and> (\<forall>T'\<in>set l29. P T') \<and> (\<forall>T'\<in>set l30. P T') \<and> (\<forall>T'\<in>set l31. P T') \<and> (\<forall>T'\<in>set l32. P T') \<and> (\<forall>T'\<in>set l33. P T') \<and> (\<forall>T'\<in>set l34. P T') \<and> (\<forall>T'\<in>set l35. P T') \<and> (\<forall>T'\<in>set l36. P T') \<and> (\<forall>T'\<in>set l37. P T') \<and> (\<forall>T'\<in>set l38. P T') \<and> (\<forall>T'\<in>set l39. P T') \<and> (\<forall>T'\<in>set l40. P T') \<and> (\<forall>T'\<in>set l41. P T') \<and> (\<forall>T'\<in>set l42. P T') \<and> (\<forall>T'\<in>set l43. P T') \<and> (\<forall>T'\<in>set l44. P T') \<and> (\<forall>T'\<in>set l45. P T') \<and> (\<forall>T'\<in>set l46. P T') \<and> (\<forall>T'\<in>set l47. P T') \<and> (\<forall>T'\<in>set l48. P T') \<and> (\<forall>T'\<in>set l49. P T') \<and> (\<forall>T'\<in>set l50. P T') \<and> (\<forall>T'\<in>set l51. P T') \<and> (\<forall>T'\<in>set l52. P T') \<and> (\<forall>T'\<in>set l53. P T') \<and> (\<forall>T'\<in>set l54. P T') \<and> (\<forall>T'\<in>set l55. P T') \<and> (\<forall>T'\<in>set l56. P T') \<and> (\<forall>T'\<in>set l57. P T') \<and> (\<forall>T'\<in>set l58. P T') \<and> (\<forall>T'\<in>set l59. P T') \<and> (\<forall>T'\<in>set l60. P T') \<and> (\<forall>T'\<in>set l61. P T') \<and> (\<forall>T'\<in>set l62. P T') \<and> (\<forall>T'\<in>set l63. P T') \<and> (\<forall>T'\<in>set l64. P T') \<and> (\<forall>T'\<in>set l65. P T') \<and> (\<forall>T'\<in>set l66. P T') \<and> (\<forall>T'\<in>set l67. P T') \<and> (\<forall>T'\<in>set l68. P T'))" apply  (auto)
 done
qed

(*
lemma my_set_concat_Lall: shows "(\<forall> T' \<in> set (l1 @ l2 @ l3). P T') = ((Lall l1 P) \<and> (Lall  l2 P) \<and> (Lall l3 P))"
  sorry
*)

lemma Ball_Lall: shows "Ball (set ls) P = Lall ls P"
  apply(induct ls)
   apply simp
  by (smt (verit) Lall.elims(1) Lall.simps(2) Lall.simps(3) list.set_cases list.set_intros(1) list.set_intros(2) set_ConsD)



theorem all_transitions_preserve_P  : assumes
  "testing_P T" shows " \<forall>T' \<in> set (concat (map (\<lambda> transition. transition T 0) allTransitions' )).  testing_P T'"
proof -
  have i0: "SWMR T" by (insert assms, unfold testing_P_def, elim conjE, assumption)
have i3: "C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T" by (insert assms, unfold testing_P_def, elim conjE, assumption)
have i4: "H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T" by (insert assms, unfold testing_P_def, elim conjE, assumption)
have i5: "H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T" by (insert assms, unfold testing_P_def, elim conjE, assumption)
  show ?thesis
  unfolding testing_P_def
  unfolding allTransitions'_def my_map_concat my_set_concat_split_68elems 
proof(intro conjI)
(** replace the above line with mega_sketch(intro conjI) **)

qed

end