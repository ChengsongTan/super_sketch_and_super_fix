theory Testing3 imports BasicInvariants "../Super_Sketch/Super_Sketch" "Try_Sketch"  begin

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


lemma forall_conjI: "(\<forall>x \<in> S. P x) \<and> (\<forall>x \<in> S. Q x) \<Longrightarrow> \<forall>x \<in> S. (P x \<and> Q x)"
  by simp

lemma Lall_unfold: "(B  \<Longrightarrow> b T \<Longrightarrow> P (f T) ) \<Longrightarrow> (B  \<Longrightarrow> T' \<in> set (if b T then [f T] else []) \<Longrightarrow> P T')"
  by simp
  

lemma prove_simpler_goal1: "( SWMR T \<Longrightarrow>
          C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T \<Longrightarrow>
          H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T \<Longrightarrow>
          H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T \<Longrightarrow> 
          CSTATE Invalid T 0 \<and> nextLoad T 0 \<Longrightarrow> SWMR (clearBuffer (sendReq RdShared ISAD 0 T))
          ) \<Longrightarrow> (\<And>T'. SWMR T \<Longrightarrow>
          C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T \<Longrightarrow>
          H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T \<Longrightarrow>
          H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T \<Longrightarrow>
          T' \<in> set (if CSTATE Invalid T 0 \<and> nextLoad T 0 then [clearBuffer (sendReq RdShared ISAD 0 T)]
                     else []) \<Longrightarrow>
          SWMR T')"
  by simp
find_theorems "_ \<in> set _ \<Longrightarrow> _ = _"


named_theorems thms_to_unfold "A list of thoerems to unfold"
declare InvalidLoad'_def [thms_to_unfold]
    and SharedLoad'_def [thms_to_unfold]
    and InvalidStore'_def [thms_to_unfold]
    and SharedStore'_def [thms_to_unfold] and
SharedEvict'_def [thms_to_unfold] and
SharedEvictData'_def [thms_to_unfold] and
ModifiedEvict'_def [thms_to_unfold] and
SharedSnpInv'_def [thms_to_unfold] and
ISDSnpInv'_def [thms_to_unfold] and
ISDData'_def [thms_to_unfold] and
ISDIData'_def [thms_to_unfold] and
IMADData'_def [thms_to_unfold] and
SMADData'_def [thms_to_unfold] and
IMADGO'_def [thms_to_unfold] and
ISADGO'_def [thms_to_unfold] and
ISADData'_def [thms_to_unfold] and
SMADGO'_def [thms_to_unfold] and
SMAGO'_def [thms_to_unfold] and
SMADSnpInv'_def [thms_to_unfold] and
SMDData'_def [thms_to_unfold] and
IMAGO'_def [thms_to_unfold] and
ISAGO'_def [thms_to_unfold] and
ModifiedStore'_def [thms_to_unfold] and
ModifiedLoad'_def [thms_to_unfold] and
SIAGO_WritePull'_def [thms_to_unfold] and
SIAGO_WritePullDrop'_def [thms_to_unfold] and
IIAGO_WritePullDrop'_def [thms_to_unfold] and
IIAGO_WritePull'_def [thms_to_unfold] and
IMDData'_def [thms_to_unfold] and
MIASnpDataInvalid'_def [thms_to_unfold] and
MIASnpDataShared'_def [thms_to_unfold] and
MIASnpInv'_def [thms_to_unfold] and
MIAGO_WritePull'_def [thms_to_unfold] and
SIASnpInv'_def [thms_to_unfold] and
ModifiedSnpInv'_def [thms_to_unfold] and
ModifiedSnpDataShared'_def [thms_to_unfold] and
ModifiedSnpDataInvalid'_def [thms_to_unfold] and
HostInvalidRdShared'_def [thms_to_unfold] and
HostInvalidRdOwn'_def [thms_to_unfold] and
HostSharedRdShared'_def [thms_to_unfold] and
HostShared_CleanEvict_NotLastDrop'_def [thms_to_unfold] and
HostShared_CleanEvict_NotLastData'_def [thms_to_unfold] and
HostShared_CleanEvict_Last'_def [thms_to_unfold] and
HostShared_CleanEvictNoData_NotLast'_def [thms_to_unfold] and
HostShared_CleanEvictNoData_Last'_def [thms_to_unfold] and
HostShared_DirtyEvict'_def [thms_to_unfold] and
HostModifiedDirtyEvict'_def [thms_to_unfold] and
HostModifiedRdShared'_def [thms_to_unfold] and
HostModifiedRdOwn'_def [thms_to_unfold] and
HostSharedRdOwn'_def [thms_to_unfold] and
HostSharedRdOwnSelf'_def [thms_to_unfold] and
HostSDData'_def [thms_to_unfold] and
HostSADData'_def [thms_to_unfold] and
HostMDData'_def [thms_to_unfold] and
HostIDData'_def [thms_to_unfold] and
HostMADData'_def [thms_to_unfold] and
HostSADRspIFwdM'_def [thms_to_unfold] and
HostSADRspSFwdM'_def [thms_to_unfold] and
HostMADRspIFwdM'_def [thms_to_unfold] and
HostMARspIFwdM'_def [thms_to_unfold] and
HostSARspIFwdM'_def [thms_to_unfold] and
HostSARspSFwdM'_def [thms_to_unfold] and
HostIBDataPrevious'_def [thms_to_unfold] and
HostSBData'_def [thms_to_unfold] and
HostMBData'_def [thms_to_unfold] and
HostInvalidDirtyEvict'_def [thms_to_unfold] and
HostMARspIHitSE'_def [thms_to_unfold] and
SIACGO'_def [thms_to_unfold]

named_theorems actions_to_unfold "a list of actions to unfold"
declare sendReq_def [actions_to_unfold] and
clearBuffer_def [actions_to_unfold] and
sendReqPerformInstruction_def [actions_to_unfold] and
sendSnpResp_def [actions_to_unfold] and
copyInDataPerformInstr_def [actions_to_unfold] and
sendSnpRespAndData_def [actions_to_unfold] and 
sendHostDataGO_def [actions_to_unfold] and
copyInData_def [actions_to_unfold] and
consumeGO_def [actions_to_unfold] and
consumeGOSendDataPerformEvict_def [actions_to_unfold] and
consumeGOPerform_def [actions_to_unfold] and
sendGOFromSnpResp_def [actions_to_unfold] and
sendEvictResp_def [actions_to_unfold] and
discardDataHost_def [actions_to_unfold] and
copyInAndForwardData_def [actions_to_unfold] and
noInvalidateSharers_def[actions_to_unfold] and
invalidateSharers_def [actions_to_unfold] and
sendSnoop_def [actions_to_unfold] and
copyInDataHost_def [actions_to_unfold] and
consumeGODiscard_def [actions_to_unfold] 

lemma zero0_simp: "(if ((0::nat) = 0) then x else y) = x"
  by simp
lemma in_singleton: "x \<in> set [a] \<Longrightarrow> x = a"
  by simp

lemma Ball_set_nil: "(\<forall>x\<in>set ([]::'a list). P x) \<longleftrightarrow> True" by simp
lemma Ball_set_singleton: "(\<forall>x\<in>set [a]. P x) \<longleftrightarrow> P a" by simp
lemma Ball_set_if_singleton:
  "(\<forall>x\<in>set (if b then [a] else []). P x) \<longleftrightarrow> (b \<longrightarrow> P a)"
  by (cases b) simp_all


find_theorems "(_ \<longrightarrow> _) \<and> (_ \<longrightarrow> _) \<Longrightarrow> _ \<and> _ "
thm testing_P_def
find_theorems "(if (0 = 0) then _ else _ )"
(*800 conjuncts * 70 rules*)
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
(*
  apply(insert assms)
  apply( intro conjI)
  apply (unfold thms_to_unfold actions_to_unfold)
  apply (simp (no_asm) only: Ball_set_if_singleton Ball_set_singleton Ball_set_nil Let_def)
  apply (simp (no_asm) only: zero0_simp if_True if_False)?
  apply(intro impI, conjI)
*)

  apply (unfold thms_to_unfold actions_to_unfold)
  apply (simp (no_asm) only: Ball_set_if_singleton Ball_set_singleton Ball_set_nil Let_def)
  apply (simp (no_asm) only: zero0_simp if_True if_False)?

  double_sketch (intro conjI) (intro impconjI) 
  
  show goal1: "CSTATE Invalid T 0 \<and> nextLoad T 0 \<longrightarrow> SWMR ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD])"
    if "testing_P T"   (intro conjI)
proof(intro conjI)
  show goal1: "CSTATE Invalid T 0 \<and> nextLoad T 0 \<longrightarrow> SWMR ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD])"
    if "testing_P T"
    using that
    by auto
next
  show goal2: "CSTATE Shared T 0 \<and> nextLoad T 0 \<longrightarrow> SWMR (T [ -=i 0]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (T [ -=i 0]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (T [ -=i 0]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (T [ -=i 0])"
    if "testing_P T"
    using that
    sorry
next
  show goal3: "CSTATE Invalid T 0 \<and> nextStore T 0 \<longrightarrow> SWMR ( T [ 0 +=rdreq RdOwn] [ 0 s= IMAD]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=rdreq RdOwn] [ 0 s= IMAD]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=rdreq RdOwn] [ 0 s= IMAD]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=rdreq RdOwn] [ 0 s= IMAD])"
    if "testing_P T"
    using that
    by simp
next
  show goal4: "CSTATE Shared T 0 \<and> nextStore T 0 \<longrightarrow> SWMR ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD])"
    if "testing_P T"
    using that
    by simp
next
  show goal5: "CSTATE Shared T 0 \<and> nextEvict T 0 \<longrightarrow> SWMR ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIAC]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIAC]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIAC]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIAC])"
    if "testing_P T"
    using that
    by simp
next
  show goal6: "CSTATE Shared T 0 \<and> nextEvict T 0 \<longrightarrow> SWMR ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA])"
    if "testing_P T"
    using that
    by auto
next
  show goal7: "CSTATE Modified T 0 \<and> nextEvict T 0 \<longrightarrow> SWMR ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA])"
    if "testing_P T"
    using that
    by force
next
  show goal8: "CXL_SPG_used T 0 \<and> CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> SWMR (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIHitSE getTid (getSnoopOrMakeup (getSnoops 0 T))] [0 -=snp ] [ 0 s= Invalid]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIHitSE getTid (getSnoopOrMakeup (getSnoops 0 T))] [0 -=snp ] [ 0 s= Invalid]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIHitSE getTid (getSnoopOrMakeup (getSnoops 0 T))] [0 -=snp ] [ 0 s= Invalid]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIHitSE getTid (getSnoopOrMakeup (getSnoops 0 T))] [0 -=snp ] [ 0 s= Invalid])"
    if "testing_P T"
    using that
    by simp
next
  show goal9: "CXL_SPG_used T 0 \<and> CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> SWMR (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIHitSE getTid (getSnoopOrMakeup (getSnoops 0 T))] [0 -=snp ] [ 0 s= ISDI]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIHitSE getTid (getSnoopOrMakeup (getSnoops 0 T))] [0 -=snp ] [ 0 s= ISDI]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIHitSE getTid (getSnoopOrMakeup (getSnoops 0 T))] [0 -=snp ] [ 0 s= ISDI]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIHitSE getTid (getSnoopOrMakeup (getSnoops 0 T))] [0 -=snp ] [ 0 s= ISDI])"
    if "testing_P T"
    using that
    by simp
next
  show goal10: "CSTATE ISD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> SWMR ( T [ 0 s= Shared] [ 0 :=dd getHTDDataOrMakeup T 0] [ -=i 0] [ 0 -=devd ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 s= Shared] [ 0 :=dd getHTDDataOrMakeup T 0] [ -=i 0] [ 0 -=devd ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 s= Shared] [ 0 :=dd getHTDDataOrMakeup T 0] [ -=i 0] [ 0 -=devd ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 s= Shared] [ 0 :=dd getHTDDataOrMakeup T 0] [ -=i 0] [ 0 -=devd ])"
    if "testing_P T"
    using that
    sorry
next
  show goal11: "CSTATE ISDI T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> SWMR ( T [ 0 s= Invalid] [ 0 :=dd getHTDDataOrMakeup T 0] [ -=i 0] [ 0 -=devd ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 s= Invalid] [ 0 :=dd getHTDDataOrMakeup T 0] [ -=i 0] [ 0 -=devd ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 s= Invalid] [ 0 :=dd getHTDDataOrMakeup T 0] [ -=i 0] [ 0 -=devd ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 s= Invalid] [ 0 :=dd getHTDDataOrMakeup T 0] [ -=i 0] [ 0 -=devd ])"
    if "testing_P T"
    using that
    sorry
next
  show goal12: "CSTATE IMAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> SWMR ( T [ 0 s= IMA] [ 0 :=dd getHTDDataOrMakeup T 0] [ 0 -=devd ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 s= IMA] [ 0 :=dd getHTDDataOrMakeup T 0] [ 0 -=devd ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 s= IMA] [ 0 :=dd getHTDDataOrMakeup T 0] [ 0 -=devd ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 s= IMA] [ 0 :=dd getHTDDataOrMakeup T 0] [ 0 -=devd ])"
    if "testing_P T"
    using that
    by auto
next
  show goal13: "CSTATE SMAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> SWMR ( T [ 0 s= SMA] [ 0 :=dd getHTDDataOrMakeup T 0] [ 0 -=devd ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 s= SMA] [ 0 :=dd getHTDDataOrMakeup T 0] [ 0 -=devd ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 s= SMA] [ 0 :=dd getHTDDataOrMakeup T 0] [ 0 -=devd ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 s= SMA] [ 0 :=dd getHTDDataOrMakeup T 0] [ 0 -=devd ])"
    if "testing_P T"
    using that
    by simp
next
  show goal14: "CSTATE IMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> SWMR ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
    if "testing_P T"
    using that
    by auto
next
  show goal15: "CSTATE ISAD T 0 \<and> nextGOPending T 0 \<longrightarrow> SWMR ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= ISD] [ 0 -=reqresp ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= ISD] [ 0 -=reqresp ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= ISD] [ 0 -=reqresp ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= ISD] [ 0 -=reqresp ])"
    if "testing_P T"
    using that
    sorry
next
  show goal16: "CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> SWMR ( T [ 0 s= ISA] [ 0 :=dd getHTDDataOrMakeup T 0] [ 0 -=devd ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 s= ISA] [ 0 :=dd getHTDDataOrMakeup T 0] [ 0 -=devd ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 s= ISA] [ 0 :=dd getHTDDataOrMakeup T 0] [ 0 -=devd ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 s= ISA] [ 0 :=dd getHTDDataOrMakeup T 0] [ 0 -=devd ])"
    if "testing_P T"
    using that
    by simp
next
  show goal17: "CSTATE SMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> SWMR ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= SMD] [ 0 -=reqresp ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= SMD] [ 0 -=reqresp ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= SMD] [ 0 -=reqresp ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= SMD] [ 0 -=reqresp ])"
    if "testing_P T"
    using that
    by simp
next
  show goal18: "CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> SWMR ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0])"
    if "testing_P T"
    using that
    sorry
next
  show goal19: "CXL_SPG_used T 0 \<and> CSTATE SMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> SWMR (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIHitSE getTid (getSnoopOrMakeup (getSnoops 0 T))] [0 -=snp ] [ 0 s= IMAD]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIHitSE getTid (getSnoopOrMakeup (getSnoops 0 T))] [0 -=snp ] [ 0 s= IMAD]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIHitSE getTid (getSnoopOrMakeup (getSnoops 0 T))] [0 -=snp ] [ 0 s= IMAD]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIHitSE getTid (getSnoopOrMakeup (getSnoops 0 T))] [0 -=snp ] [ 0 s= IMAD])"
    if "testing_P T"
    using that
    by auto
next
  show goal20: "CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> SWMR ( T [ 0 s= Modified] [ 0 :=dd getHTDDataOrMakeup T 0] [ -=i 0] [ 0 -=devd ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 s= Modified] [ 0 :=dd getHTDDataOrMakeup T 0] [ -=i 0] [ 0 -=devd ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 s= Modified] [ 0 :=dd getHTDDataOrMakeup T 0] [ -=i 0] [ 0 -=devd ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 s= Modified] [ 0 :=dd getHTDDataOrMakeup T 0] [ -=i 0] [ 0 -=devd ])"
    if "testing_P T"
    using that
    sorry
next
  show goal21: "CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> SWMR ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0])"
    if "testing_P T"
    using that
    sorry
next
  show goal22: "CSTATE ISA T 0 \<and> nextGOPending T 0 \<longrightarrow> SWMR ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0])"
    if "testing_P T"
    using that
    sorry
next
  show goal23: "CSTATE Modified T 0 \<and> nextStore T 0 \<longrightarrow> SWMR (T [ -=i 0]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (T [ -=i 0]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (T [ -=i 0]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (T [ -=i 0])"
    if "testing_P T"
    using that
    sorry
next
  show goal24: "CSTATE Modified T 0 \<and> nextLoad T 0 \<longrightarrow> SWMR (T [ -=i 0]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (T [ -=i 0]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (T [ -=i 0]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (T [ -=i 0])"
    if "testing_P T"
    using that
    sorry
next
  show goal25: "CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> SWMR (consumeGOSendData 0 Invalid T) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (consumeGOSendData 0 Invalid T) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (consumeGOSendData 0 Invalid T) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (consumeGOSendData 0 Invalid T)"
    if "testing_P T"
    using that
    sorry
next
  show goal26: "CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0 \<longrightarrow> SWMR ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
    if "testing_P T"
    using that
    sorry
next
  show goal27: "CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0 \<longrightarrow> SWMR ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
    if "testing_P T"
    using that
    sorry
next
  show goal28: "CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> SWMR (consumeGOSendData 0 Invalid T) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (consumeGOSendData 0 Invalid T) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (consumeGOSendData 0 Invalid T) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (consumeGOSendData 0 Invalid T)"
    if "testing_P T"
    using that
    sorry
next
  show goal29: "CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> SWMR ( T [ 0 s= Modified] [ 0 :=dd getHTDDataOrMakeup T 0] [ -=i 0] [ 0 -=devd ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 s= Modified] [ 0 :=dd getHTDDataOrMakeup T 0] [ -=i 0] [ 0 -=devd ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 s= Modified] [ 0 :=dd getHTDDataOrMakeup T 0] [ -=i 0] [ 0 -=devd ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 s= Modified] [ 0 :=dd getHTDDataOrMakeup T 0] [ -=i 0] [ 0 -=devd ])"
    if "testing_P T"
    using that
    sorry
next
  show goal30: "CXL_SPG_used T 0 \<and> CSTATE MIA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> SWMR (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIFwdM nextSnoopID T 0] [0 -=snp ] [ 0 s= IIA] [ nat_to_id 0 +=d2hd D2HData (nextSnoopID T 0) (read_dev_value 0 T) (clock T)]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIFwdM nextSnoopID T 0] [0 -=snp ] [ 0 s= IIA] [ nat_to_id 0 +=d2hd D2HData (nextSnoopID T 0) (read_dev_value 0 T) (clock T)]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIFwdM nextSnoopID T 0] [0 -=snp ] [ 0 s= IIA] [ nat_to_id 0 +=d2hd D2HData (nextSnoopID T 0) (read_dev_value 0 T) (clock T)]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIFwdM nextSnoopID T 0] [0 -=snp ] [ 0 s= IIA] [ nat_to_id 0 +=d2hd D2HData (nextSnoopID T 0) (read_dev_value 0 T) (clock T)])"
    if "testing_P T"
    using that
    by auto
next
  show goal31: "CXL_SPG_used T 0 \<and> CSTATE MIA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> SWMR (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspSFwdM nextSnoopID T 0] [0 -=snp ] [ 0 s= SIA] [ nat_to_id 0 +=d2hd D2HData (nextSnoopID T 0) (read_dev_value 0 T) (clock T)]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspSFwdM nextSnoopID T 0] [0 -=snp ] [ 0 s= SIA] [ nat_to_id 0 +=d2hd D2HData (nextSnoopID T 0) (read_dev_value 0 T) (clock T)]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspSFwdM nextSnoopID T 0] [0 -=snp ] [ 0 s= SIA] [ nat_to_id 0 +=d2hd D2HData (nextSnoopID T 0) (read_dev_value 0 T) (clock T)]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspSFwdM nextSnoopID T 0] [0 -=snp ] [ 0 s= SIA] [ nat_to_id 0 +=d2hd D2HData (nextSnoopID T 0) (read_dev_value 0 T) (clock T)])"
    if "testing_P T"
    using that
    by simp
next
  show goal32: "CXL_SPG_used T 0 \<and> CSTATE MIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> SWMR (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIFwdM nextSnoopID T 0] [0 -=snp ] [ 0 s= IIA] [ nat_to_id 0 +=d2hd D2HData (nextSnoopID T 0) (read_dev_value 0 T) (clock T)]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIFwdM nextSnoopID T 0] [0 -=snp ] [ 0 s= IIA] [ nat_to_id 0 +=d2hd D2HData (nextSnoopID T 0) (read_dev_value 0 T) (clock T)]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIFwdM nextSnoopID T 0] [0 -=snp ] [ 0 s= IIA] [ nat_to_id 0 +=d2hd D2HData (nextSnoopID T 0) (read_dev_value 0 T) (clock T)]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIFwdM nextSnoopID T 0] [0 -=snp ] [ 0 s= IIA] [ nat_to_id 0 +=d2hd D2HData (nextSnoopID T 0) (read_dev_value 0 T) (clock T)])"
    if "testing_P T"
    using that
    by force
next
  show goal33: "CSTATE MIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> SWMR ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ nat_to_id 0 +=d2hd D2HData (nextGOID T 0) (read_dev_value 0 T) (clock T)] [ -=i 0]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ nat_to_id 0 +=d2hd D2HData (nextGOID T 0) (read_dev_value 0 T) (clock T)] [ -=i 0]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ nat_to_id 0 +=d2hd D2HData (nextGOID T 0) (read_dev_value 0 T) (clock T)] [ -=i 0]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ nat_to_id 0 +=d2hd D2HData (nextGOID T 0) (read_dev_value 0 T) (clock T)] [ -=i 0])"
    if "testing_P T"
    using that
    sorry
next
  show goal34: "CXL_SPG_used T 0 \<and> CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<and> \<not> nextReqIs DirtyEvict T 0 \<longrightarrow> SWMR (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIHitSE getTid (getSnoopOrMakeup (getSnoops 0 T))] [0 -=snp ] [ 0 s= IIA]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIHitSE getTid (getSnoopOrMakeup (getSnoops 0 T))] [0 -=snp ] [ 0 s= IIA]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIHitSE getTid (getSnoopOrMakeup (getSnoops 0 T))] [0 -=snp ] [ 0 s= IIA]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIHitSE getTid (getSnoopOrMakeup (getSnoops 0 T))] [0 -=snp ] [ 0 s= IIA])"
    if "testing_P T"
    using that
    by force
next
  show goal35: "CXL_SPG_used T 0 \<and> CSTATE Modified T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> SWMR (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIFwdM nextSnoopID T 0] [0 -=snp ] [ 0 s= Invalid] [ nat_to_id 0 +=d2hd D2HData (nextSnoopID T 0) (read_dev_value 0 T) (clock T)]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIFwdM nextSnoopID T 0] [0 -=snp ] [ 0 s= Invalid] [ nat_to_id 0 +=d2hd D2HData (nextSnoopID T 0) (read_dev_value 0 T) (clock T)]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIFwdM nextSnoopID T 0] [0 -=snp ] [ 0 s= Invalid] [ nat_to_id 0 +=d2hd D2HData (nextSnoopID T 0) (read_dev_value 0 T) (clock T)]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIFwdM nextSnoopID T 0] [0 -=snp ] [ 0 s= Invalid] [ nat_to_id 0 +=d2hd D2HData (nextSnoopID T 0) (read_dev_value 0 T) (clock T)])"
    if "testing_P T"
    using that
    by force
next
  show goal36: "CXL_SPG_used T 0 \<and> CSTATE Modified T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> SWMR (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspSFwdM nextSnoopID T 0] [0 -=snp ] [ 0 s= Shared] [ nat_to_id 0 +=d2hd D2HData (nextSnoopID T 0) (read_dev_value 0 T) (clock T)]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspSFwdM nextSnoopID T 0] [0 -=snp ] [ 0 s= Shared] [ nat_to_id 0 +=d2hd D2HData (nextSnoopID T 0) (read_dev_value 0 T) (clock T)]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspSFwdM nextSnoopID T 0] [0 -=snp ] [ 0 s= Shared] [ nat_to_id 0 +=d2hd D2HData (nextSnoopID T 0) (read_dev_value 0 T) (clock T)]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspSFwdM nextSnoopID T 0] [0 -=snp ] [ 0 s= Shared] [ nat_to_id 0 +=d2hd D2HData (nextSnoopID T 0) (read_dev_value 0 T) (clock T)])"
    if "testing_P T"
    using that
    sorry
next
  show goal37: "CXL_SPG_used T 0 \<and> CSTATE Modified T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> SWMR (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIFwdM nextSnoopID T 0] [0 -=snp ] [ 0 s= Invalid] [ nat_to_id 0 +=d2hd D2HData (nextSnoopID T 0) (read_dev_value 0 T) (clock T)]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIFwdM nextSnoopID T 0] [0 -=snp ] [ 0 s= Invalid] [ nat_to_id 0 +=d2hd D2HData (nextSnoopID T 0) (read_dev_value 0 T) (clock T)]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIFwdM nextSnoopID T 0] [0 -=snp ] [ 0 s= Invalid] [ nat_to_id 0 +=d2hd D2HData (nextSnoopID T 0) (read_dev_value 0 T) (clock T)]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (   T\<lparr>buffer1 := Some (nextSnoop T 0)\<rparr> [0 +=snpresp RspIFwdM nextSnoopID T 0] [0 -=snp ] [ 0 s= Invalid] [ nat_to_id 0 +=d2hd D2HData (nextSnoopID T 0) (read_dev_value 0 T) (clock T)])"
    if "testing_P T"
    using that
    by simp
next
  show goal38: "HSTATE InvalidM T \<and> nextReqIs RdShared T 0 \<and> GTS T ((0 + 1) mod 2) \<longrightarrow> SWMR ( T [ 0 +=hostdata  nextReqID T 0] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared nextReqID T 0] [ 0 -=req ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=hostdata  nextReqID T 0] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared nextReqID T 0] [ 0 -=req ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=hostdata  nextReqID T 0] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared nextReqID T 0] [ 0 -=req ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=hostdata  nextReqID T 0] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared nextReqID T 0] [ 0 -=req ])"
    if "testing_P T"
    using that
    sorry
next
  show goal39: "HSTATE InvalidM T \<and> nextReqIs RdOwn T 0 \<and> GTS T ((0 + 1) mod 2) \<longrightarrow> SWMR ( T [ 0 +=hostdata  nextReqID T 0] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified nextReqID T 0] [ 0 -=req ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=hostdata  nextReqID T 0] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified nextReqID T 0] [ 0 -=req ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=hostdata  nextReqID T 0] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified nextReqID T 0] [ 0 -=req ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=hostdata  nextReqID T 0] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified nextReqID T 0] [ 0 -=req ])"
    if "testing_P T"
    using that
    sorry
next
  show goal40: "HSTATE SharedM T \<and> nextReqIs RdShared T 0 \<and> GTS T ((0 + 1) mod 2) \<longrightarrow> SWMR ( T [ 0 +=hostdata  nextReqID T 0] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared nextReqID T 0] [ 0 -=req ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=hostdata  nextReqID T 0] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared nextReqID T 0] [ 0 -=req ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=hostdata  nextReqID T 0] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared nextReqID T 0] [ 0 -=req ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=hostdata  nextReqID T 0] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared nextReqID T 0] [ 0 -=req ])"
    if "testing_P T"
    using that
    sorry
next
  show goal41: "HSTATE SharedM T \<and> nextReqIs CleanEvict T 0 \<and> \<not> lastSharer T \<and> GTS T ((0 + 1) mod 2) \<and> \<not> CSTATE IIA T ((0 + 1) mod 2) \<longrightarrow> SWMR ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO_WritePullDrop Invalid nextReqID T 0] [ 0 -=req ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO_WritePullDrop Invalid nextReqID T 0] [ 0 -=req ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO_WritePullDrop Invalid nextReqID T 0] [ 0 -=req ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO_WritePullDrop Invalid nextReqID T 0] [ 0 -=req ])"
    if "testing_P T"
    using that
    by auto
next
  show goal42: "HSTATE SharedM T \<and> nextReqIs CleanEvict T 0 \<and> \<not> lastSharer T \<and> GTS T ((0 + 1) mod 2) \<and> \<not> CSTATE IIA T ((0 + 1) mod 2) \<longrightarrow> SWMR ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid nextReqID T 0] [ 0 -=req ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid nextReqID T 0] [ 0 -=req ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid nextReqID T 0] [ 0 -=req ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid nextReqID T 0] [ 0 -=req ])"
    if "testing_P T"
    using that
    by auto
next
  show goal43: "HSTATE SharedM T \<and> nextReqIs CleanEvict T 0 \<and> lastSharer T \<and> GTS T ((0 + 1) mod 2) \<longrightarrow> SWMR ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid nextReqID T 0] [ 0 -=req ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid nextReqID T 0] [ 0 -=req ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid nextReqID T 0] [ 0 -=req ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid nextReqID T 0] [ 0 -=req ])"
    if "testing_P T"
    using that
    by auto
next
  show goal44: "HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<and> \<not> lastSharer T \<and> GTS T ((0 + 1) mod 2) \<and> \<not> CSTATE IIA T 1 \<longrightarrow> SWMR ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO Invalid nextReqID T 0] [ 0 -=req ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO Invalid nextReqID T 0] [ 0 -=req ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO Invalid nextReqID T 0] [ 0 -=req ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO Invalid nextReqID T 0] [ 0 -=req ])"
    if "testing_P T"
    using that
    by simp
next
  show goal45: "HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<and> lastSharer T \<and> GTS T ((0 + 1) mod 2) \<longrightarrow> SWMR ( T [ 5 sHost= InvalidM] [ 0 +=reqresp GO Invalid nextReqID T 0] [ 0 -=req ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= InvalidM] [ 0 +=reqresp GO Invalid nextReqID T 0] [ 0 -=req ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= InvalidM] [ 0 +=reqresp GO Invalid nextReqID T 0] [ 0 -=req ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= InvalidM] [ 0 +=reqresp GO Invalid nextReqID T 0] [ 0 -=req ])"
    if "testing_P T"
    using that
    by force
next
  show goal46: "HSTATE SharedM T \<and> nextReqIs DirtyEvict T 0 \<and> GTS T ((0 + 1) mod 2) \<and> CSTATE IIA T 0 \<longrightarrow> SWMR ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid nextReqID T 0] [ 0 -=req ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid nextReqID T 0] [ 0 -=req ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid nextReqID T 0] [ 0 -=req ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid nextReqID T 0] [ 0 -=req ])"
    if "testing_P T"
    using that
    by simp
next
  show goal47: "HSTATE ModifiedM T \<and> nextReqIs DirtyEvict T 0 \<and> GTS T ((0 + 1) mod 2) \<and> CSTATE MIA T 0 \<longrightarrow> SWMR ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid nextReqID T 0] [ 0 -=req ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid nextReqID T 0] [ 0 -=req ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid nextReqID T 0] [ 0 -=req ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid nextReqID T 0] [ 0 -=req ])"
    if "testing_P T"
    using that
    by simp
next
  show goal48: "HSTATE ModifiedM T \<and> nextReqIs RdShared T 0 \<longrightarrow> SWMR ( T [ (0 + 1) mod 2 +=snp SnpData nextReqID T 0]  [ 5 sHost= SAD] [ 0 -=req ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ (0 + 1) mod 2 +=snp SnpData nextReqID T 0]  [ 5 sHost= SAD] [ 0 -=req ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ (0 + 1) mod 2 +=snp SnpData nextReqID T 0]  [ 5 sHost= SAD] [ 0 -=req ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ (0 + 1) mod 2 +=snp SnpData nextReqID T 0]  [ 5 sHost= SAD] [ 0 -=req ])"
    if "testing_P T"
    using that
    sorry
next
  show goal49: "HSTATE ModifiedM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> SWMR ( T [ (0 + 1) mod 2 +=snp SnpInv nextReqID T 0]  [ 5 sHost= MAD] [ 0 -=req ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ (0 + 1) mod 2 +=snp SnpInv nextReqID T 0]  [ 5 sHost= MAD] [ 0 -=req ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ (0 + 1) mod 2 +=snp SnpInv nextReqID T 0]  [ 5 sHost= MAD] [ 0 -=req ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ (0 + 1) mod 2 +=snp SnpInv nextReqID T 0]  [ 5 sHost= MAD] [ 0 -=req ])"
    if "testing_P T"
    using that
    by force
next
  show goal50: "HSTATE SharedM T \<and> nextReqIs RdOwn T 0 \<and> CSTATE Shared T ((0 + 1) mod 2) \<longrightarrow> SWMR (sendHostData 0 MA T [ (0 + 1) mod 2 +=snp SnpInv nextReqID T 0]  [ 0 -=req ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (sendHostData 0 MA T [ (0 + 1) mod 2 +=snp SnpInv nextReqID T 0]  [ 0 -=req ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (sendHostData 0 MA T [ (0 + 1) mod 2 +=snp SnpInv nextReqID T 0]  [ 0 -=req ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (sendHostData 0 MA T [ (0 + 1) mod 2 +=snp SnpInv nextReqID T 0]  [ 0 -=req ])"
    if "testing_P T"
    using that
    by force
next
  show goal51: "HSTATE SharedM T \<and> nextReqIs RdOwn T 0 \<and> CSTATE Invalid T ((0 + 1) mod 2) \<longrightarrow> SWMR ( T [ 0 +=hostdata  nextReqID T 0] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified nextReqID T 0] [ 0 -=req ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=hostdata  nextReqID T 0] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified nextReqID T 0] [ 0 -=req ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=hostdata  nextReqID T 0] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified nextReqID T 0] [ 0 -=req ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 +=hostdata  nextReqID T 0] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified nextReqID T 0] [ 0 -=req ])"
    if "testing_P T"
    using that
    by auto
next
  show goal52: "HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> SWMR (  T [ nat_to_id ((0 + 1) mod 2) +=h2dd DTH_HTD (getDTHDataOrMakeup (dthdatas1 T))] [    =hv getSpecificValD2H (getDTHDataOrMakeup (dthdatas1 T))] [ 5 sHost= SharedM] [ nat_to_id 0 -=d2hdHead ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (  T [ nat_to_id ((0 + 1) mod 2) +=h2dd DTH_HTD (getDTHDataOrMakeup (dthdatas1 T))] [    =hv getSpecificValD2H (getDTHDataOrMakeup (dthdatas1 T))] [ 5 sHost= SharedM] [ nat_to_id 0 -=d2hdHead ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (  T [ nat_to_id ((0 + 1) mod 2) +=h2dd DTH_HTD (getDTHDataOrMakeup (dthdatas1 T))] [    =hv getSpecificValD2H (getDTHDataOrMakeup (dthdatas1 T))] [ 5 sHost= SharedM] [ nat_to_id 0 -=d2hdHead ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (  T [ nat_to_id ((0 + 1) mod 2) +=h2dd DTH_HTD (getDTHDataOrMakeup (dthdatas1 T))] [    =hv getSpecificValD2H (getDTHDataOrMakeup (dthdatas1 T))] [ 5 sHost= SharedM] [ nat_to_id 0 -=d2hdHead ])"
    if "testing_P T"
    using that
    by auto
next
  show goal53: "HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> SWMR (  T [ nat_to_id ((0 + 1) mod 2) +=h2dd DTH_HTD (getDTHDataOrMakeup (dthdatas1 T))] [    =hv getSpecificValD2H (getDTHDataOrMakeup (dthdatas1 T))] [ 5 sHost= SA] [ nat_to_id 0 -=d2hdHead ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (  T [ nat_to_id ((0 + 1) mod 2) +=h2dd DTH_HTD (getDTHDataOrMakeup (dthdatas1 T))] [    =hv getSpecificValD2H (getDTHDataOrMakeup (dthdatas1 T))] [ 5 sHost= SA] [ nat_to_id 0 -=d2hdHead ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (  T [ nat_to_id ((0 + 1) mod 2) +=h2dd DTH_HTD (getDTHDataOrMakeup (dthdatas1 T))] [    =hv getSpecificValD2H (getDTHDataOrMakeup (dthdatas1 T))] [ 5 sHost= SA] [ nat_to_id 0 -=d2hdHead ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (  T [ nat_to_id ((0 + 1) mod 2) +=h2dd DTH_HTD (getDTHDataOrMakeup (dthdatas1 T))] [    =hv getSpecificValD2H (getDTHDataOrMakeup (dthdatas1 T))] [ 5 sHost= SA] [ nat_to_id 0 -=d2hdHead ])"
    if "testing_P T"
    using that
    by auto
next
  show goal54: "HSTATE MD T \<and> nextDTHDataFrom 0 T \<longrightarrow> SWMR (  T [ nat_to_id ((0 + 1) mod 2) +=h2dd DTH_HTD (getDTHDataOrMakeup (dthdatas1 T))] [    =hv getSpecificValD2H (getDTHDataOrMakeup (dthdatas1 T))] [ 5 sHost= ModifiedM] [ nat_to_id 0 -=d2hdHead ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (  T [ nat_to_id ((0 + 1) mod 2) +=h2dd DTH_HTD (getDTHDataOrMakeup (dthdatas1 T))] [    =hv getSpecificValD2H (getDTHDataOrMakeup (dthdatas1 T))] [ 5 sHost= ModifiedM] [ nat_to_id 0 -=d2hdHead ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (  T [ nat_to_id ((0 + 1) mod 2) +=h2dd DTH_HTD (getDTHDataOrMakeup (dthdatas1 T))] [    =hv getSpecificValD2H (getDTHDataOrMakeup (dthdatas1 T))] [ 5 sHost= ModifiedM] [ nat_to_id 0 -=d2hdHead ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (  T [ nat_to_id ((0 + 1) mod 2) +=h2dd DTH_HTD (getDTHDataOrMakeup (dthdatas1 T))] [    =hv getSpecificValD2H (getDTHDataOrMakeup (dthdatas1 T))] [ 5 sHost= ModifiedM] [ nat_to_id 0 -=d2hdHead ])"
    if "testing_P T"
    using that
    sorry
next
  show goal55: "HSTATE ID T \<and> nextDTHDataFrom 0 T \<and> CSTATE Invalid T 0 \<and> (CSTATE IIA T ((0 + 1) mod 2) \<or> CSTATE Invalid T ((0 + 1) mod 2) \<or> CSTATE SIA T ((0 + 1) mod 2)) \<longrightarrow> SWMR (  T [    =hv getSpecificValD2H (getDTHDataOrMakeup (dthdatas1 T))] [ 5 sHost= InvalidM] [ nat_to_id 0 -=d2hdHead ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (  T [    =hv getSpecificValD2H (getDTHDataOrMakeup (dthdatas1 T))] [ 5 sHost= InvalidM] [ nat_to_id 0 -=d2hdHead ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (  T [    =hv getSpecificValD2H (getDTHDataOrMakeup (dthdatas1 T))] [ 5 sHost= InvalidM] [ nat_to_id 0 -=d2hdHead ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (  T [    =hv getSpecificValD2H (getDTHDataOrMakeup (dthdatas1 T))] [ 5 sHost= InvalidM] [ nat_to_id 0 -=d2hdHead ])"
    if "testing_P T"
    using that
    by simp
next
  show goal56: "HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> SWMR (  T [ nat_to_id ((0 + 1) mod 2) +=h2dd DTH_HTD (getDTHDataOrMakeup (dthdatas1 T))] [    =hv getSpecificValD2H (getDTHDataOrMakeup (dthdatas1 T))] [ 5 sHost= MA] [ nat_to_id 0 -=d2hdHead ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (  T [ nat_to_id ((0 + 1) mod 2) +=h2dd DTH_HTD (getDTHDataOrMakeup (dthdatas1 T))] [    =hv getSpecificValD2H (getDTHDataOrMakeup (dthdatas1 T))] [ 5 sHost= MA] [ nat_to_id 0 -=d2hdHead ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (  T [ nat_to_id ((0 + 1) mod 2) +=h2dd DTH_HTD (getDTHDataOrMakeup (dthdatas1 T))] [    =hv getSpecificValD2H (getDTHDataOrMakeup (dthdatas1 T))] [ 5 sHost= MA] [ nat_to_id 0 -=d2hdHead ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (  T [ nat_to_id ((0 + 1) mod 2) +=h2dd DTH_HTD (getDTHDataOrMakeup (dthdatas1 T))] [    =hv getSpecificValD2H (getDTHDataOrMakeup (dthdatas1 T))] [ 5 sHost= MA] [ nat_to_id 0 -=d2hdHead ])"
    if "testing_P T"
    using that
    sorry
next
  show goal57: "HSTATE SAD T \<and> nextSnpRespIs RspIFwdM T 0 \<and> GTS T 0 \<longrightarrow> SWMR ( T [ (0 + 1) mod 2 +=reqresp GO Shared nextSnoopRespID T 0] [ 5 sHost= SD] [ 0 -=snpresp  ] ) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ (0 + 1) mod 2 +=reqresp GO Shared nextSnoopRespID T 0] [ 5 sHost= SD] [ 0 -=snpresp  ] ) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ (0 + 1) mod 2 +=reqresp GO Shared nextSnoopRespID T 0] [ 5 sHost= SD] [ 0 -=snpresp  ] ) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ (0 + 1) mod 2 +=reqresp GO Shared nextSnoopRespID T 0] [ 5 sHost= SD] [ 0 -=snpresp  ] )"
    if "testing_P T"
    using that
    by simp
next
  show goal58: "HSTATE SAD T \<and> nextSnpRespIs RspSFwdM T 0 \<and> GTS T 0 \<longrightarrow> SWMR ( T [ (0 + 1) mod 2 +=reqresp GO Shared nextSnoopRespID T 0] [ 5 sHost= SD] [ 0 -=snpresp  ] ) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ (0 + 1) mod 2 +=reqresp GO Shared nextSnoopRespID T 0] [ 5 sHost= SD] [ 0 -=snpresp  ] ) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ (0 + 1) mod 2 +=reqresp GO Shared nextSnoopRespID T 0] [ 5 sHost= SD] [ 0 -=snpresp  ] ) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ (0 + 1) mod 2 +=reqresp GO Shared nextSnoopRespID T 0] [ 5 sHost= SD] [ 0 -=snpresp  ] )"
    if "testing_P T"
    using that
    by auto
next
  show goal59: "HSTATE MAD T \<and> nextSnpRespIs RspIFwdM T 0 \<and> GTS T 0 \<longrightarrow> SWMR ( T [ (0 + 1) mod 2 +=reqresp GO Modified nextSnoopRespID T 0] [ 5 sHost= MD] [ 0 -=snpresp  ] ) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ (0 + 1) mod 2 +=reqresp GO Modified nextSnoopRespID T 0] [ 5 sHost= MD] [ 0 -=snpresp  ] ) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ (0 + 1) mod 2 +=reqresp GO Modified nextSnoopRespID T 0] [ 5 sHost= MD] [ 0 -=snpresp  ] ) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ (0 + 1) mod 2 +=reqresp GO Modified nextSnoopRespID T 0] [ 5 sHost= MD] [ 0 -=snpresp  ] )"
    if "testing_P T"
    using that
    by simp
next
  show goal60: "HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 0 \<and> GTS T 0 \<longrightarrow> SWMR ( T [ (0 + 1) mod 2 +=reqresp GO Modified nextSnoopRespID T 0] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ] ) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ (0 + 1) mod 2 +=reqresp GO Modified nextSnoopRespID T 0] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ] ) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ (0 + 1) mod 2 +=reqresp GO Modified nextSnoopRespID T 0] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ] ) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ (0 + 1) mod 2 +=reqresp GO Modified nextSnoopRespID T 0] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ] )"
    if "testing_P T"
    using that
    by simp
next
  show goal61: "HSTATE SA T \<and> nextSnpRespIs RspIFwdM T 0 \<and> GTS T 0 \<longrightarrow> SWMR ( T [ (0 + 1) mod 2 +=reqresp GO Shared nextSnoopRespID T 0] [ 5 sHost= SharedM] [ 0 -=snpresp  ] ) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ (0 + 1) mod 2 +=reqresp GO Shared nextSnoopRespID T 0] [ 5 sHost= SharedM] [ 0 -=snpresp  ] ) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ (0 + 1) mod 2 +=reqresp GO Shared nextSnoopRespID T 0] [ 5 sHost= SharedM] [ 0 -=snpresp  ] ) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ (0 + 1) mod 2 +=reqresp GO Shared nextSnoopRespID T 0] [ 5 sHost= SharedM] [ 0 -=snpresp  ] )"
    if "testing_P T"
    using that
    by auto
next
  show goal62: "HSTATE SA T \<and> nextSnpRespIs RspSFwdM T 0 \<and> GTS T 0 \<longrightarrow> SWMR ( T [ (0 + 1) mod 2 +=reqresp GO Shared nextSnoopRespID T 0] [ 5 sHost= SharedM] [ 0 -=snpresp  ] ) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ (0 + 1) mod 2 +=reqresp GO Shared nextSnoopRespID T 0] [ 5 sHost= SharedM] [ 0 -=snpresp  ] ) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ (0 + 1) mod 2 +=reqresp GO Shared nextSnoopRespID T 0] [ 5 sHost= SharedM] [ 0 -=snpresp  ] ) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ (0 + 1) mod 2 +=reqresp GO Shared nextSnoopRespID T 0] [ 5 sHost= SharedM] [ 0 -=snpresp  ] )"
    if "testing_P T"
    using that
    by simp
next
  show goal63: "HSTATE IB T \<and> nextDTHDataFrom 0 T \<and> CSTATE Invalid T 0 \<and> CSTATE Invalid T ((0 + 1) mod 2) \<longrightarrow> SWMR ( T [ 5 sHost= InvalidM] [ nat_to_id 0 -=d2hdHead ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= InvalidM] [ nat_to_id 0 -=d2hdHead ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= InvalidM] [ nat_to_id 0 -=d2hdHead ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= InvalidM] [ nat_to_id 0 -=d2hdHead ])"
    if "testing_P T"
    using that
    by auto
next
  show goal64: "HSTATE SB T \<and> nextDTHDataFrom 0 T \<and> CSTATE Invalid T 0 \<longrightarrow> SWMR ( T [ 5 sHost= SharedM] [ nat_to_id 0 -=d2hdHead ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= SharedM] [ nat_to_id 0 -=d2hdHead ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= SharedM] [ nat_to_id 0 -=d2hdHead ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= SharedM] [ nat_to_id 0 -=d2hdHead ])"
    if "testing_P T"
    using that
    by simp
next
  show goal65: "HSTATE MB T \<and> nextDTHDataFrom 0 T \<and> CSTATE Invalid T 0 \<longrightarrow> SWMR ( T [ 5 sHost= ModifiedM] [ nat_to_id 0 -=d2hdHead ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= ModifiedM] [ nat_to_id 0 -=d2hdHead ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= ModifiedM] [ nat_to_id 0 -=d2hdHead ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= ModifiedM] [ nat_to_id 0 -=d2hdHead ])"
    if "testing_P T"
    using that
    by auto
next
  show goal66: "HSTATE InvalidM T \<and> nextReqIs DirtyEvict T 0 \<and> GTS T ((0 + 1) mod 2) \<and> CSTATE IIA T 0 \<longrightarrow> SWMR ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid nextReqID T 0] [ 0 -=req ]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid nextReqID T 0] [ 0 -=req ]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid nextReqID T 0] [ 0 -=req ]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid nextReqID T 0] [ 0 -=req ])"
    if "testing_P T"
    using that
    by simp
next
  show goal67: "HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 0 \<and> GTS T 0 \<and> htddatas1 T = [] \<longrightarrow> SWMR ( T [ (0 + 1) mod 2 +=reqresp GO Modified nextSnoopRespID T 0] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ] ) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ (0 + 1) mod 2 +=reqresp GO Modified nextSnoopRespID T 0] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ] ) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ (0 + 1) mod 2 +=reqresp GO Modified nextSnoopRespID T 0] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ] ) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ (0 + 1) mod 2 +=reqresp GO Modified nextSnoopRespID T 0] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ] )"
    if "testing_P T"
    using that
    by simp
next
  show goal68: "CSTATE SIAC T 0 \<and> nextGOPendingIs GO T 0 \<and> nextGOPendingState Invalid T 0 \<and> GTS T ((0 + 1) mod 2) \<and> saneSIACGO T 0 \<longrightarrow> SWMR ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) \<and> C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) \<and> H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) \<and> H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
    if "testing_P T"
    using that
    sorry
qed

  
  
  
  
  
  

(* 
(intro conjI;
       unfold thms_to_unfold actions_to_unfold;
       simp (no_asm) only: Let_def if_distrib;
       split if_splits;
       (drule in_singleton)?)
not used for now
ML_val \<open>Proof.goal (Toplevel.proof_of@{Isar.state}) \<close>
apply (insert assms , intro ballI conjI; 
    (unfold testing_P_def    InvalidLoad'_def , (split if_splits)?))
proof (insert assms , intro ballI conjI ; (unfold testing_P_def InvalidLoad'_def , (split if_splits) ?))
 \<close>
*)

qed

end