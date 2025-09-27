
theory AllBackgroundInvariants imports BasicInvariants begin
sledgehammer_params[timeout=10, dont_minimize, "try0" = false]

(* Consolidated background invariants from all Fix*Filled.thy files *)
(* Content extracted up to coherent_aux_simpler lemmas *)


(* ========================================= *)
(* Content from FixIBDataFilled.thy *)
(* Lines 1-119 extracted *)
(* ========================================= *)

lemma HostIBDataPrevious'_devcache_invariant1: shows "(CLEntry.block_state (devcache1 ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]))) = CLEntry.block_state (devcache1 T)"
by simp
lemma HostIBDataPrevious'_devcache_invariant2: shows "(CLEntry.block_state (devcache2 ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]))) = CLEntry.block_state (devcache2 T)"
by simp
lemma HostIBDataPrevious_nextLoad: shows "nextLoad T 1 = nextLoad ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) 1"
by simp
lemma snps1_HostIBDataPrevious: shows "snps1 ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) = snps1 T"
by simp
lemma snps2_HostIBDataPrevious: shows "snps2 ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) = snps2 T"
by simp
lemma reqs2_HostIBDataPrevious: shows "reqs2 ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) = reqs2 T"
by simp
lemma reqs1_HostIBDataPrevious: shows "reqs1 ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) = reqs1 T"
by simp
lemma htddatas2_HostIBDataPrevious: shows "htddatas2 ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) = htddatas2 T"
by simp
lemma nextSnoopIs_HostIBDataPrevious: shows "nextSnoopIs X ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) i = nextSnoopIs X T i"
by simp
lemma snpresps2_HostIBDataPrevious: shows "snpresps2 ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) = snpresps2 T"
by simp
lemma snpresps1_HostIBDataPrevious: shows "snpresps1 ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) = snpresps1 T"
by simp
lemma reqresps2_HostIBDataPrevious: shows "reqresps2 ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) = reqresps2 T"
by simp
lemma reqresps1_HostIBDataPrevious: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ])) \<le> 1"
by simp
lemma reqresps1_HostIBDataPrevious2: shows "reqresps1 T =  (reqresps1 ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]))"
by simp
lemma dthdatas1_HostIBDataPrevious_aux: shows "length (dthdatas1 T) \<le> 1 \<Longrightarrow> (dthdatas1 (T [ Dev1 -=d2hdHead ])) = []"
apply simp
apply(case_tac "dthdatas1 T")
by simp+
lemma dthdatas1_HostIBDataPrevious: shows "length (dthdatas1 T) \<le> 1 \<Longrightarrow> dthdatas1 ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) = []"
apply(subgoal_tac "dthdatas1 ( T [ 5 sHost= InvalidM] ) = dthdatas1 T")
apply(subgoal_tac "length (dthdatas1 ( T [ 5 sHost= InvalidM] )) \<le> 1")
using dthdatas1_HostIBDataPrevious_aux
apply blast
apply presburger
by simp
lemma dthdatas2_HostIBDataPrevious: shows "dthdatas2 ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_HostIBDataPrevious: shows "htddatas1 ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) = htddatas1 T"
apply simp
done
lemma reqresps1_HostIBDataPrevious_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostIBDataPrevious_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostIBDataPrevious_invariant: shows"nextEvict T 0 = nextEvict ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) 0"
by simp
lemma nextReqIs_HostIBDataPrevious_IMAD_invariant2: shows 
  "nextReqIs X ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) 1 = nextReqIs X T 1"
by simp
lemma nextReqIs_HostIBDataPrevious_IMAD_invariant1: shows 
  "nextReqIs X ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) 0 = nextReqIs X T 0"
by simp
lemma CSTATE_HostIBDataPrevious_otherside_invariant2: shows
" CSTATE X ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostIBDataPrevious_otherside_invariant3: shows
" CSTATE X ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) 0 = CSTATE X T 0"
by simp
lemma HostIBDataPrevious_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) i = nextGOPendingIs X T i"
by simp
lemma HostIBDataPrevious_nextEvict_otherside: shows 
"nextEvict  ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) i = nextEvict T i"
by simp
lemma HostIBDataPrevious_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostIBDataPrevious_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostIBDataPrevious_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) 0 = nextSnpRespIs X T 0"
by simp
lemma HostIBDataPrevious_HSTATE: shows "HSTATE InvalidM ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) "
by simp
lemma nextStore_nextEvict_exclusive: shows "nextEvict T i \<Longrightarrow> \<not>nextStore T i"
apply(induct "program1 T")
apply simp
apply (metis One_nat_def startsEvict.elims(2) startsStore.simps(4) zero_neq_one)
apply(case_tac a)
apply (metis nextEvict_def nextStore_def startsEvict.elims(2) startsStore.simps(4))
apply (metis nextEvict_def nextStore_def startsEvict.elims(2) startsStore.simps(4))
by (metis nextEvict_def nextStore_def startsEvict.elims(2) startsStore.simps(4))
lemma nextStore_HostIBDataPrevious: shows "nextStore T = nextStore ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ])"
unfolding nextStore_def
by simp
lemma nextLoad_HostIBDataPrevious: shows "nextLoad T = nextLoad ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ])"
unfolding nextLoad_def
by simp
lemma reqlength1_minus: shows "length (reqs1 T) \<le> 1 \<Longrightarrow> reqs1 (T [ 0 -=req]) = []"
apply(cases "reqs1 T") apply simp+ done
lemma empty_reqs_nextReqIs: shows "reqs1 T  = [] \<Longrightarrow> \<not> nextReqIs X T 0"
by simp
lemma HostIBDataPrevious_empty_reqs1_aux: shows " reqs1 T = reqs1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD])"
by simp
lemma reqs1_HostShareRdOwn_aux: shows "reqs1 ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid] ) = reqs1 T"
by simp
lemma HostIBDataPrevious_one_msg_htddatas1: shows "htddatas1 T = (htddatas1 ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]))"
by simp+
lemma HostIBDataPrevious_nextGOPending: shows "nextGOPending T i = nextGOPending ( T [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) i"
by simp
lemma nextReqIs_nonempty_reqs1:shows "nextReqIs X T 0 \<Longrightarrow> reqs1 T \<noteq> []"
using empty_reqs_nextReqIs
by blast
lemma HostIBDataPrevious_htddatas2_aux: shows "htddatas2 T = [] \<Longrightarrow> length (htddatas2 (T [Dev2 +=h2dd msg])) \<le> 1"
apply simp
done
lemma nextGOPending_HostIBDataPrevious: "nextGOPending (  T[ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ] ) i = nextGOPending T i"
apply(case_tac i) apply simp+ done

(* ========================================= *)
(* Content from FixIDDataFilled.thy *)
(* Lines 1-127 extracted *)
(* ========================================= *)

lemma HostIDData'_CSTATE_invariant1: shows "CSTATE X (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= InvalidM] [ 0 -=snpresp  ]) 0 = CSTATE X T 0"
by simp
lemma HostIDData'_CSTATE_invariant2: shows "CSTATE X (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= InvalidM] [ 0 -=snpresp  ]) 1 = CSTATE X T 1"
by simp
lemma HostIDData'_devcache_invariant1: shows "(CLEntry.block_state (devcache1 ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]))) = CLEntry.block_state (devcache1 T)"
by simp
lemma HostIDData'_devcache_invariant2: shows "(CLEntry.block_state (devcache2 ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]))) = CLEntry.block_state (devcache2 T)"
by simp
lemma HostIDData_nextLoad: shows "nextLoad T 1 = nextLoad ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) 1"
by simp
lemma snps1_HostIDData: shows "snps1 ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) = snps1 T"
by simp
lemma snps2_HostIDData: shows "snps2 ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) = snps2 T"
by simp
lemma reqs2_HostIDData: shows "reqs2 ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) = reqs2 T"
by simp
lemma reqs1_HostIDData: shows "reqs1 ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) = reqs1 T"
by simp
lemma htddatas2_HostIDData: shows "htddatas2 ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) = htddatas2 T"
by simp
lemma nextSnoopIs_HostIDData: shows "nextSnoopIs X ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) i = nextSnoopIs X T i"
by simp
lemma snpresps2_HostIDData: shows "snpresps2 ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) = snpresps2 T"
by simp
lemma snpresps1_HostIDData: shows "snpresps1 ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) = snpresps1 T"
by simp
lemma reqresps2_HostIDData: shows "reqresps2 ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) = reqresps2 T"
by simp
lemma reqresps1_HostIDData: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ])) \<le> 1"
by simp
lemma reqresps1_HostIDData2: shows "reqresps1 T =  (reqresps1 ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]))"
by simp
lemma dthdatas1_HostIDData_aux: shows "length (dthdatas1 T) \<le> 1 \<Longrightarrow> (dthdatas1 (T [ Dev1 -=d2hdHead ])) = []"
apply simp
apply(case_tac "dthdatas1 T")
by simp+
lemma dthdatas1_HostIDData: shows "length (dthdatas1 T) \<le> 1 \<Longrightarrow> dthdatas1 ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) = []"
apply(subgoal_tac "dthdatas1 ( T   [ =hv v] [ 5 sHost= InvalidM] ) = dthdatas1 T")
apply(subgoal_tac "length (dthdatas1 ( T [ =hv v] [ 5 sHost= InvalidM] )) \<le> 1")
using dthdatas1_HostIDData_aux
apply blast
apply presburger
by simp
lemma dthdatas2_HostIDData: shows "dthdatas2 ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_HostIDData: shows "htddatas1 ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) = htddatas1 T"
apply simp
done
lemma reqresps1_HostIDData_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostIDData_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostIDData_invariant: shows"nextEvict T 0 = nextEvict ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) 0"
by simp
lemma nextReqIs_HostIDData_IMAD_invariant2: shows 
  "nextReqIs X ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) 1 = nextReqIs X T 1"
by simp
lemma nextReqIs_HostIDData_IMAD_invariant1: shows 
  "nextReqIs X ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) 0 = nextReqIs X T 0"
by simp
lemma CSTATE_HostIDData_otherside_invariant2: shows
" CSTATE X ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostIDData_otherside_invariant3: shows
" CSTATE X ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) 0 = CSTATE X T 0"
by simp
lemma HostIDData_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) i = nextGOPendingIs X T i"
by simp
lemma HostIDData_nextEvict_otherside: shows 
"nextEvict  ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) i = nextEvict T i"
by simp
lemma HostIDData_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostIDData_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostIDData_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) 0 = nextSnpRespIs X T 0"
by simp
lemma HostIDData_HSTATE: shows "HSTATE InvalidM ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) "
by simp
lemma nextStore_HostIDData: shows "nextStore T = nextStore ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ])"
unfolding nextStore_def
by simp
lemma nextLoad_HostIDData: shows "nextLoad T = nextLoad ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ])"
unfolding nextLoad_def
by simp
lemma HostIDData_empty_reqs1_aux: shows " reqs1 T = reqs1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD])"
by simp
lemma HostIDData_one_msg_htddatas1: shows "htddatas1 T = (htddatas1 ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]))"
by simp+
lemma HostIDData_nextGOPending: shows "nextGOPending T i = nextGOPending ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) i"
by simp
lemma HostIDData_htddatas2_aux: shows "htddatas2 T = [] \<Longrightarrow> length (htddatas2 (T [Dev2 +=h2dd msg])) \<le> 1"
apply simp
done
lemma nextGOPending_HostIDData: "nextGOPending (  T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ] ) i = nextGOPending T i"
apply(case_tac i)
apply simp+
done

(* ========================================= *)
(* Content from FixIIAGO_WritePullDropFilled.thy *)
(* Lines 1-263 extracted *)
(* ========================================= *)

lemma nextEvict_IIAGO_WritePullDrop_CSTATE_invariant: shows "CSTATE X T i = CSTATE X (T [ -=i 0])  i"
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp+
done
lemma nextEvict_IIAGO_WritePullDrop_invariant: shows"nextEvict T 0 = nextEvict ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] ) 0"
by simp
lemma HSTATE_IIAGO_WritePullDrop_invariant: shows "HSTATE X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = 
  HSTATE X T"
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp+
done
lemma nextReqIs_IIAGO_WritePullDrop_IMAD_invariant2: shows 
  "nextReqIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 1 = nextReqIs X T 1"
by(cases "program1 T", simp+)
lemma nextReqIs_IIAGO_WritePullDrop_IMAD_invariant1: shows 
  "nextReqIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 0 = nextReqIs X T 0"
by(cases "program1 T", simp+)
lemma CSTATE_IIAGO_WritePullDrop_otherside_invariant2: shows
" CSTATE X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 1 = CSTATE X T 1"
by(cases "program1 T", simp+)
lemma IIAGO_WritePullDrop_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 1 = nextGOPendingIs X T 1"
by(cases "program1 T", simp+)
lemma IIAGO_WritePullDrop_nextEvict_otherside: shows 
"nextEvict  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 1 = nextEvict T 1"
by(cases "program1 T", simp+)
lemma IIAGO_WritePullDrop_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 1 = nextDTHDataPending T 1"
by (metis nextDTHDataPending_general_rule_1_0)
lemma IIAGO_WritePullDrop_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 1 = nextSnpRespIs X T 1"
proof (-)
show goal1: "nextSnpRespIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 1 = nextSnpRespIs X T 1"
apply  (cases "program1 T")
apply  (auto)
done
qed
lemma IIAGO_WritePullDrop_nextHTDDataPending_sameside: shows 
"nextDTHDataPending  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 0 = nextDTHDataPending T 0"
apply  (cases "program1 T")
apply  (auto)
done
lemma IIAGO_WritePullDrop_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 0 = nextSnpRespIs X T 0"
apply  (cases "program1 T")
apply  (auto)
done
lemma devcache2_buffer1_invariant: shows "devcache2 ( T \<lparr>buffer1 := Some m\<rparr> ) = devcache2 T"
by simp
lemma devcache2_sequals1_invariant: shows "devcache2 ( T [ 0 s= ISD] ) = devcache2 T"
by simp
lemma devcache2_consume_reqresps1_invariant: shows "devcache2 ( T [ 0 -=reqresp ] ) = devcache2 T"
apply simp
done
lemma devcache1_consume_reqresps1_invariant: shows "CLEntry.block_state  (devcache1 T) = CLEntry.block_state  (devcache1 ( T  [ 0 -=reqresp ] ))"
by simp
lemma devcache1_IIAGO_WritePullDrop_invariant_aux1: shows "CLEntry.block_state  (devcache1 T) = ISD \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ 0 -=reqresp ] )) \<noteq> Modified"
using MESI_State.distinct(7) devcache1_consume_reqresps1_invariant
by presburger
lemma devcache1_IIAGO_WritePullDrop_invariant_aux: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ 0 -=reqresp ] [ 0 -=devd ])) \<noteq> Modified"
using devcache1_IIAGO_WritePullDrop_invariant_aux1
by auto
lemma devcache1_IIAGO_WritePullDrop_invariant: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T [ 0 :=dd msg ] [ 0 -=reqresp ] [ 0 -=devd ])) \<noteq> Modified"
apply(subgoal_tac "CLEntry.block_state  (devcache1 (T  [ 0 :=dd msg ])) = Shared")
using devcache1_IIAGO_WritePullDrop_invariant_aux
apply blast
by simp
lemma CSTATE_IIAGO_WritePullDrop_IMAD_invariant: shows "
CSTATE Invalid (T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ]  [ -=i 0]) 0"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
by simp+
lemma nextSnoopIs_IIAGO_WritePullDrop: shows 
  "nextSnoopIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) i = nextSnoopIs X T i"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp
by simp+
lemma CSTATE_IIAGO_WritePullDrop_otherside: shows "CSTATE X T 1 = CSTATE X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 1"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp
by simp+
lemma nextReqIs_IIAGO_WritePullDrop: shows "nextReqIs X T i = nextReqIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) i"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp
by simp+
lemma IIAGO_WritePullDrop_snps2:   " snps2  T  = snps2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma IIAGO_WritePullDrop_snps1:   " snps1  T  = snps1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma IIAGO_WritePullDrop_reqs1:   " reqs1  T  = reqs1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma IIAGO_WritePullDrop_reqs2:   " reqs2  T  = reqs2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma IIAGO_WritePullDrop_reqresps2:   " reqresps2  T  = reqresps2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma IIAGO_WritePullDrop_snpresps1:   " snpresps1  T  = snpresps1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma IIAGO_WritePullDrop_snpresps2:   " snpresps2  T  = snpresps2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma IIAGO_WritePullDrop_dthdatas1:   " dthdatas1  T = [] \<Longrightarrow> 
  length (dthdatas1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])) \<le> 1"
apply (cases "program1 T")
apply simp
apply simp
done
lemma IIAGO_WritePullDrop_dthdatas2:   " dthdatas2  T  = dthdatas2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma IIAGO_WritePullDrop_htddatas1:   "htddatas1 T =  (htddatas1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]))"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
using Type1State.update_convs(12) Type1State.update_convs(2) Type1State.update_convs(8) change_state_def config_differ_dev_mapping_def config_differ_dthdata_def consumeReqresp_def device_perform_op_htddatas1
apply force
by simp+
lemma IIAGO_WritePullDrop_htddatas2:   " htddatas2  T  = htddatas2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma IIAGO_WritePullDrop_nextHTDDataPending: "nextHTDDataPending T i = 
  nextHTDDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])  i"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp+
done
lemma IIAGO_nextGOPending_otherside: "nextGOPending T 1 = nextGOPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 1"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp
by simp+
lemma snps2_IIAGO_WritePullDrop: shows "snps2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = snps2 T"
apply(case_tac "program1 T")
by simp+
lemma snps1_IIAGO_WritePullDrop: shows "snps1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_IIAGO_WritePullDrop: shows "reqs2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma reqs1_IIAGO_WritePullDrop: shows "reqs1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = reqs1 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_IIAGO_WritePullDrop: shows "snpresps2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_IIAGO_WritePullDrop: shows "snpresps1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = snpresps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_IIAGO_WritePullDrop: shows "reqresps2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_IIAGO_WritePullDrop: shows "dthdatas2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_IIAGO_WritePullDrop: shows "htddatas1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = htddatas1 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_IIAGO_WritePullDrop: shows "htddatas2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_IIAGO_WritePullDrop_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_IIAGO_WritePullDrop_aux1: shows "reqresps1 T = reqresps1 (T [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_IIAGO_WritePullDrop: assumes "length (reqresps1 T) \<le> 1" shows "reqresps1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = []"
proof -
have half_same: " (reqresps1  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid])) = reqresps1 T" by simp
have quarter_reduce: "reqresps1 (T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ]) = []"
proof -
have half_l1: "length (reqresps1  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] )) \<le> 1"
using assms half_same
by presburger
show ?thesis
using half_l1 reqresps1_IIAGO_WritePullDrop_aux
by presburger
qed
have quarter_same: "reqresps1  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ]) = reqresps1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
using reqresps1_IIAGO_WritePullDrop_aux1
by blast
show ?thesis
using quarter_reduce quarter_same
by presburger
qed
lemma reqresps1_HostModifiedRdShared_aux1: shows "reqresps1 T = reqresps1 (T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid])"
by simp
lemma IIAGO_WritePullDrop_CSTATE_aux: shows "CSTATE X T 0 = CSTATE X ( T [ 0 -=reqresp ]  [ -=i 0]) 0"
apply(case_tac "program1 T")
by simp+
lemma dthdatas1_perform_instr: shows "dthdatas1 T = dthdatas1 (T [ -=i m])"
apply(case_tac m)
apply(case_tac "program1 T")
apply simp
apply simp
apply(case_tac "program2 T")
apply simp+
done
lemma nextGOPending_DeviceIIAGO_WritePullDrop_other: "nextGOPending (  T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0] ) 1 = nextGOPending T 1"
apply(case_tac "program1 T")
apply simp+
done
lemma nextLoad_DeviceIIAGO_WritePullDrop: "nextLoad (  T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0] ) 1 = nextLoad T 1"
apply(case_tac "program1 T")
apply simp+
done
lemma nextGOPending_DeviceIIAGO_WritePullDrop: "nextGOPending (  T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0] ) 1 = nextGOPending T 1"
using nextGOPending_DeviceIIAGO_WritePullDrop_other
by blast

(* ========================================= *)
(* Content from FixIIAGO_WritePullFilled.thy *)
(* Lines 1-156 extracted *)
(* ========================================= *)

lemma snps2_IIAGO_WritePull: shows "snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = snps2 T"
apply(case_tac "program1 T")
by simp+
lemma snps1_IIAGO_WritePull: shows "snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_IIAGO_WritePull: shows "reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma reqs1_IIAGO_WritePull: shows "reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = reqs1 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_IIAGO_WritePull: shows "snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_IIAGO_WritePull: shows "snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = snpresps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_IIAGO_WritePull: shows "reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_IIAGO_WritePull: shows "dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_IIAGO_WritePull: shows "htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = htddatas1 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_IIAGO_WritePull: shows "htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_IIAGO_WritePull_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_IIAGO_WritePull_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_IIAGO_WritePull: assumes "length (reqresps1 T) \<le> 1" shows "reqresps1  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
proof -
have half_same: " (reqresps1  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid])) = reqresps1 T" by simp
have quarter_reduce: "reqresps1 (T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ]) = []"
proof -
have half_l1: "length (reqresps1  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] )) \<le> 1"
using assms half_same
by presburger
show ?thesis
using half_l1 reqresps1_IIAGO_WritePull_aux
by presburger
qed
have quarter_same: "reqresps1  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ]) = reqresps1  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
using reqresps1_IIAGO_WritePull_aux1
by blast
show ?thesis
using quarter_reduce quarter_same
by presburger
qed
lemma nextEvict_IIAGO_WritePull_CSTATE_invariant: shows "nextEvict T 0 \<Longrightarrow> CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])  0"
apply(case_tac "program1 T")
apply simp+
done
lemma nextEvict_IIAGO_WritePull_invariant: shows"nextEvict T 0 = nextEvict ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] ) 0"
by simp
lemma HSTATE_IIAGO_WritePull_invariant: shows "HSTATE X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = 
  HSTATE X T"
apply(case_tac "program1 T")
by simp+
lemma CSTATE_IIAGO_WritePull_IMAD_invariant: shows "  CSTATE Invalid (T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd]) 0"
by simp
lemma CSTATE_IIAGO_WritePull_Invalid: shows " CSTATE Invalid (T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd]) 0"
using nextEvict_IIAGO_WritePull_CSTATE_invariant nextEvict_IIAGO_WritePull_invariant
using CSTATE_IIAGO_WritePull_IMAD_invariant
by presburger
lemma nextReqIs_IIAGO_WritePull_IMAD_invariant2: shows 
  "nextReqIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 = nextReqIs X T 1"
apply(case_tac "program1 T")
by simp+
lemma nextReqIs_IIAGO_WritePull_IMAD_invariant1: shows 
  "nextReqIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 = nextReqIs X T 0"
apply(case_tac "program1 T")
by simp+
lemma CSTATE_IIAGO_WritePull_otherside_invariant2: shows
" CSTATE X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 = CSTATE X T 1"
apply(case_tac "program1 T")
by simp+
lemma IIAGO_WritePull_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 = nextGOPendingIs X T 1"
apply(case_tac "program1 T")
by simp+
lemma IIAGO_WritePull_nextEvict_otherside: shows 
"nextEvict  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 = nextEvict T 1"
apply(case_tac "program1 T")
by simp+
lemma IIAGO_WritePull_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 = nextDTHDataPending T 1"
apply(case_tac "program1 T")
apply  simp+
done
lemma IIAGO_WritePull_nextHTDDataPending_real: shows 
"nextHTDDataPending  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) i = nextHTDDataPending T i"
apply(case_tac "program1 T")
apply  simp+
done
lemma IIAGO_WritePull_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 = nextSnpRespIs X T 1"
apply(case_tac "program1 T")
by simp+
lemma IIAGO_WritePull_nextHTDDataPending_sameside: shows 
"nextDTHDataPending  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 = nextDTHDataPending T 1"
apply(case_tac "program1 T")
by simp+
lemma IIAGO_WritePull_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 = nextSnpRespIs X T 0"
apply(case_tac "program1 T")
apply  simp+
done
lemma IIAGO_WritePull_HSTATE: shows "HSTATE X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = 
  HSTATE X T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostModifiedRdShared_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma IIAGO_WritePull_reqresps1_empty: shows 
  "length (reqresps1 T ) \<le> 1 \<Longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
using reqresps1_IIAGO_WritePull
by presburger
lemma IIAGO_WritePull_CSTATE_aux: shows "CSTATE X T 0 = CSTATE X ( T [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply(case_tac "program1 T")
by simp+
lemma nextGOPending_DeviceIIAGO_WritePull: "nextGOPending (  T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0] ) 1 = nextGOPending T 1"
using nextGOPending_def reqresps2_IIAGO_WritePull
by presburger
lemma nextLoad_DeviceIIAGO_WritePull: "nextLoad (  T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0] ) 1 = nextLoad T 1"
apply(case_tac "program1 T")
apply simp+
done

(* ========================================= *)
(* Content from FixIMADDataFilled.thy *)
(* Lines 1-95 extracted *)
(* ========================================= *)

lemma nextSnoopPending_IMADData1: shows "nextSnoopPending ( T [ 0 s= IMA] [ 0 :=dd getHTDDataOrMakeup T 0] [ 0 -=devd ]) 1 = nextSnoopPending T 1"
using DeviceID.simps(3) Type1State.iffs Type1State.surjective Type1State.update_convs(2) change_state_def config_differ_dev_mapping_def device_copy_in_data_def nextSnoopPending_def nextSnoopPending_devConsume_data_invariant
by auto
lemma HSTATE_IMADData: shows "HSTATE X T = HSTATE X (T [ 0 s= IMA] [ 0 :=dd getHTDDataOrMakeup T 0] [ 0 -=devd ])"
using hstate_invariants(17) hstate_invariants(20) hstate_invariants(24)
by presburger
lemma CSTATE_IMADData_otherside: shows "CSTATE X T 1 = CSTATE X ( T [ 0 s= IMA] [ 0 :=dd msg ]  [ 0 -=devd ]) 1"
by simp
lemma nextReqIs_IMADData: shows "nextReqIs X T i = nextReqIs X ( T [ 0 s= IMA] [ 0 :=dd msg ]  [ 0 -=devd ]) i"
by simp
lemma IMADData_nextGOPendingIs: shows "nextGOPendingIs X T i = nextGOPendingIs X ( T [ 0 s= IMA] [ 0 :=dd msg ]  [ 0 -=devd ]) i"
by simp
lemma IMADData_nextEvict: shows "nextEvict T 1 = nextEvict ( T [ 0 s= IMA] [ 0 :=dd msg ]  [ 0 -=devd ]) 1"
by simp
lemma IMADData_nextLoad: shows "nextLoad T 1 = nextLoad ( T [ 0 s= IMA] [ 0 :=dd msg ]  [ 0 -=devd ]) 1"
by simp
lemma IMADData_HSTATE: shows "(HSTATE X ( T [ 0 s= IMA] [ 0 :=dd msg ]  [ 0 -=devd ])) = HSTATE X T"
by simp
lemma IMADData_HSTATES: shows "(HSTATE MAD ( T [ 0 s= IMA] [ 0 :=dd msg ]  [ 0 -=devd ]) \<or>
  HSTATE MA ( T [ 0 s= IMA] [ 0 :=dd msg ]  [ 0 -=devd ]) \<or>
  HSTATE MD ( T [ 0 s= IMA] [ 0 :=dd msg ]  [ 0 -=devd ]) \<or>
  HSTATE ModifiedM ( T [ 0 s= IMA] [ 0 :=dd msg ]  [ 0 -=devd ])) = (HSTATE MAD T \<or> HSTATE MA T \<or> HSTATE MD T \<or> HSTATE ModifiedM T)"
by simp
lemma IMADData_nextSnoopIs: shows "nextSnoopIs  X T i = nextSnoopIs X ( T [ 0 s= IMA] [ 0 :=dd msg ]  [ 0 -=devd ]) i"
by simp
lemma IMADData_nextStore_otherside: shows "nextStore T 1 = nextStore ( T [ 0 s= IMA] [ 0 :=dd msg ]  [ 0 -=devd ]) 1"
by simp
lemma IMADData_snps2:   " snps2  T  = snps2  ( T [ 0 s= IMA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma IMADData_snps1:   " snps1  T  = snps1  ( T [ 0 s= IMA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma IMADData_reqs1:   " reqs1  T  = reqs1  ( T [ 0 s= IMA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma IMADData_reqs2:   " reqs2  T  = reqs2  ( T [ 0 s= IMA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma IMADData_reqresps1:   " reqresps1  T  = reqresps1  ( T [ 0 s= IMA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma IMADData_reqresps2:   " reqresps2  T  = reqresps2  ( T [ 0 s= IMA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma IMADData_snpresps1:   " snpresps1  T  = snpresps1  ( T [ 0 s= IMA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma IMADData_snpresps2:   " snpresps2  T  = snpresps2  ( T [ 0 s= IMA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma IMADData_dthdatas1:   " dthdatas1  T  = dthdatas1  ( T [ 0 s= IMA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma IMADData_dthdatas2:   " dthdatas2  T  = dthdatas2  ( T [ 0 s= IMA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma IMADData_htddatas1:   " length (htddatas1  T) \<le> 1 \<Longrightarrow>   (htddatas1 ( T [ 0 s= IMA] [ 0 :=dd msg ]  [ 0 -=devd ])) = []"
by (metis htddatas1_empty_if_minus_rule_1_0)
lemma IMADData_htddatas2:   " htddatas2  T  = htddatas2  ( T [ 0 s= IMA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma nextGOPending_DeviceIMADData: "nextGOPending (  T [ 0 s= IMA] [ 0 :=dd msg ]  [ 0 -=devd ] ) i = nextGOPending T i"
apply(case_tac i)
apply simp+
done
lemma nextLoad_DeviceIMADData: "nextLoad (  T [ 0 s= IMA] [ 0 :=dd msg ]  [ 0 -=devd ] ) i = nextLoad T i"
apply(case_tac i)
apply simp+
done

(* ========================================= *)
(* Content from FixIMADGOFilled.thy *)
(* Lines 1-85 extracted *)
(* ========================================= *)

lemma devcache1_IMADGO_invariant_aux1: shows "CLEntry.block_state  (devcache1 T) = IMD \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ 0 -=reqresp ] )) \<noteq> Modified"
by simp
lemma devcache1_IMADGO_invariant_aux: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ 0 -=reqresp ] [ 0 -=devd ])) \<noteq> Modified"
by simp
lemma devcache1_IMADGO_invariant: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T [ 0 :=dd msg ] [ 0 -=reqresp ] [ 0 -=devd ])) \<noteq> Modified"
apply(subgoal_tac "CLEntry.block_state  (devcache1 (T  [ 0 :=dd msg ])) = Shared")
using devcache1_IMADGO_invariant_aux
apply blast
by simp
lemma IMADGO'_nextDTHDataPending: "nextDTHDataPending T i = nextDTHDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) i"
by simp
lemma IMADGO'_nextEvict: "nextEvict T i = nextEvict ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) i"
by simp
lemma IMADGO'_nextStore: "nextStore T i = nextStore ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) i"
by simp
lemma IMADGO'_not_nextGOPending: "length (reqresps1 T) \<le> 1 \<Longrightarrow> \<not> nextGOPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
apply(subgoal_tac " reqresps1 (T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD]) = reqresps1 T")
apply(subgoal_tac " length (reqresps1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD])) \<le> 1")
apply(case_tac "reqresps1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD])")
by simp+
lemma IMADGO'_nextGOPending1: "nextGOPending  T 1 = nextGOPending  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
by simp
lemma IMADGO'_nextGOPendingIs: "nextGOPendingIs X T 1 = nextGOPendingIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
by simp
lemma IMADGO'_nextHTDDataPending: "nextHTDDataPending T i = nextHTDDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) i"
apply  simp
done
lemma IMADGO'_HSTATE: "HSTATE X T  = HSTATE X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) "
apply  simp
done
lemma IMADGO'_CSTATE_otherside: "CSTATE X T 1 = CSTATE X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
apply  simp
done
lemma IMADGO'_CSTATE_sameside: "CSTATE IMD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
by simp
lemma IMADGO'_nextSnoopIs: "nextSnoopIs X T i = nextSnoopIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) i"
apply  simp
done
lemma IMADGO'_nextReqIs: "nextReqIs X T i = nextReqIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) i"
apply  simp
done
lemma IMADGO'_nextSnpRespIs: "nextSnpRespIs X T i = nextSnpRespIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) i"
apply  simp
done
lemma IMADGO'_nextReqIs_invariant1: shows "nextReqIs x T i = nextReqIs x ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) i"
apply(case_tac i)
apply simp
apply simp
done
lemma IMADGO'_nextReqIs_invariant_DirtyEvict: shows "nextReqIs DirtyEvict T i = nextReqIs DirtyEvict ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) i"
apply(case_tac i)
apply simp+
done
lemma IMADGO'_nextReqIs_invariant_not_RdOwn: shows "X \<noteq> RdOwn \<Longrightarrow> nextReqIs X T i = nextReqIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) i"
apply(case_tac i)
apply simp+
done
lemma reqs2_IMADGO: shows "reqs2 T = reqs2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
by simp
lemma nextStore_IMADGO: shows "nextLoad ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 = nextLoad T 0"
by simp
lemma nextLoad2_IMADGO: shows "nextLoad ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 = nextLoad T 1"
by simp
lemma nextLoad_DeviceIMADGO: "nextLoad (  T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ] ) i = nextLoad T i"
apply(case_tac i)
apply simp+
done
lemma nextGOPending_DeviceIMADGO: "nextGOPending (  T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ] ) 1 = nextGOPending T 1"
apply simp+
done

(* ========================================= *)
(* Content from FixIMAGOFilled.thy *)
(* Lines 1-258 extracted *)
(* ========================================= *)

lemma nextEvict_IMAGO_CSTATE_invariant: shows "CSTATE X T i = CSTATE X (T [ -=i 0])  i"
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp+
done
lemma nextStore_IMAGO_invariant: shows"nextStore T 0 = nextStore ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] ) 0"
by simp
lemma HSTATE_IMAGO_invariant: shows "HSTATE X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) = 
  HSTATE X T"
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp+
done
lemma nextReqIs_IMAGO_IMAD_invariant2: shows 
  "nextReqIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 1 = nextReqIs X T 1"
by (metis INVALID_ROW_def MEM_RDS_COL_def nextReqIs_general_rule_4_0)
lemma nextReqIs_IMAGO_IMAD_invariant1: shows 
  "nextReqIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 0 = nextReqIs X T 0"
by (metis nextReqIs_general_rule_6_0 nextReqIs_remove_op option.inject)
lemma CSTATE_IMAGO_otherside_invariant2: shows
" CSTATE X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 1 = CSTATE X T 1"
by (metis CSTATE_otherside_rule_7 INVALID_ROW_def MEM_RDS_COL_def)
lemma IMAGO_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 1 = nextGOPendingIs X T 1"
by (metis INVALID_ROW_def MEM_RDS_COL_def nextGOPendingIs_XYAGO_other1)
lemma IMAGO_nextEvict_otherside: shows 
"nextEvict  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 1 = nextEvict T 1"
apply(cases "program1 T")
by simp+
lemma IMAGO_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 1 = nextDTHDataPending T 1"
by (metis INVALID_ROW_def MEM_RDS_COL_def nextDTHDataPending_general_rule_1_0)
lemma IMAGO_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 1 = nextSnpRespIs X T 1"
by (metis nextSnpRespIs_general_rule_4_0)
lemma IMAGO_nextDTHDataPending_sameside: shows 
"nextDTHDataPending  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 0 = nextDTHDataPending T 0"
by (metis nextDTHDataPending_general_rule_1_0)
lemma IMAGO_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 0 = nextSnpRespIs X T 0"
by (metis nextSnpRespIs_general_rule_4_0)
lemma devcache1_IMAGO_invariant_aux1: shows "CLEntry.block_state  (devcache1 T) = ISD \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ 0 -=reqresp ] )) \<noteq> Modified"
using MESI_State.distinct(7) devcache1_consume_reqresps1_invariant
by presburger
lemma devcache1_IMAGO_invariant_aux: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ 0 -=reqresp ] [ 0 -=devd ])) \<noteq> Modified"
using devcache1_IMAGO_invariant_aux1
by auto
lemma devcache1_IMAGO_invariant: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T [ 0 :=dd msg ] [ 0 -=reqresp ] [ 0 -=devd ])) \<noteq> Modified"
apply(subgoal_tac "CLEntry.block_state  (devcache1 (T  [ 0 :=dd msg ])) = Shared")
using devcache1_IMAGO_invariant_aux
apply blast
by simp
lemma CSTATE_IMAGO_IMAD_invariant: shows "
CSTATE Modified (T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ]  [ -=i 0]) 0"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
by simp+
lemma nextSnoopIs_IMAGO: shows 
  "nextSnoopIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) i = nextSnoopIs X T i"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp
by simp+
lemma CSTATE_IMAGO_otherside: shows "CSTATE X T 1 = CSTATE X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 1"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp
by simp+
lemma nextReqIs_IMAGO: shows "nextReqIs X T i = nextReqIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) i"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp
by simp+
lemma IMAGO_snps2:   " snps2  T  = snps2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma IMAGO_snps1:   " snps1  T  = snps1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma IMAGO_reqs1:   " reqs1  T  = reqs1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma IMAGO_reqs2:   " reqs2  T  = reqs2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma IMAGO_reqresps2:   " reqresps2  T  = reqresps2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma IMAGO_snpresps1:   " snpresps1  T  = snpresps1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma IMAGO_snpresps2:   " snpresps2  T  = snpresps2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma IMAGO_dthdatas1:   " dthdatas1  T = [] \<Longrightarrow> 
  length (dthdatas1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0])) \<le> 1"
apply (cases "program1 T")
apply simp
apply simp
done
lemma IMAGO_dthdatas2:   " dthdatas2  T  = dthdatas2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma IMAGO_htddatas1:   "htddatas1 T =  (htddatas1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]))"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
using Type1State.update_convs(12) Type1State.update_convs(2) Type1State.update_convs(8) change_state_def config_differ_dev_mapping_def config_differ_dthdata_def consumeReqresp_def device_perform_op_htddatas1
apply force
by simp+
lemma IMAGO_htddatas2:   " htddatas2  T  = htddatas2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma IMAGO_nextHTDDataPending: "nextHTDDataPending T i = 
  nextHTDDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0])  i"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp+
done
lemma snps2_IMAGO: shows "snps2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) = snps2 T"
apply(case_tac "program1 T")
by simp+
lemma snps1_IMAGO: shows "snps1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_IMAGO: shows "reqs2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma reqs1_IMAGO: shows "reqs1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) = reqs1 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_IMAGO: shows "snpresps2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_IMAGO: shows "snpresps1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) = snpresps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_IMAGO: shows "reqresps2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_IMAGO: shows "dthdatas2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_IMAGO: shows "htddatas1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) = htddatas1 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_IMAGO: shows "htddatas2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_IMAGO_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_IMAGO_aux1: shows "reqresps1 T = reqresps1 (T [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_IMAGO: assumes "length (reqresps1 T) \<le> 1" shows "reqresps1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) = []"
proof -
have half_same: " (reqresps1  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified])) = reqresps1 T" by simp
have quarter_reduce: "reqresps1 (T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ]) = []"
proof -
have half_l1: "length (reqresps1  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] )) \<le> 1"
using assms half_same
by presburger
show ?thesis
using half_l1 reqresps1_IMAGO_aux
by presburger
qed
have quarter_same: "reqresps1  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ]) = reqresps1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0])"
using reqresps1_IMAGO_aux1
by blast
show ?thesis
using quarter_reduce quarter_same
by presburger
qed
lemma IMAGO_CSTATE_aux: shows "CSTATE X T 0 = CSTATE X ( T [ 0 -=reqresp ]  [ -=i 0]) 0"
apply(case_tac "program1 T")
by simp+
lemma nextGOPending_DeviceIMAGO_other: "nextGOPending (  T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0] ) 1 = nextGOPending T 1"
apply(case_tac "program1 T")
apply simp+
done
lemma nextLoad_DeviceIMAGO: "nextLoad (  T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0] ) 1 = nextLoad T 1"
apply(case_tac "program1 T")
apply simp+
done
lemma nextGOPending_DeviceIMAGO: "nextGOPending (  T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0] ) 1 = nextGOPending T 1"
using nextGOPending_DeviceIMAGO_other
by blast
lemma IMAGO_nextHTDDataPending_sameside: shows 
"nextHTDDataPending  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) i = nextHTDDataPending T i"
by (metis IMAGO_nextHTDDataPending nextHTDDataPending_general_rule_4_0)

(* ========================================= *)
(* Content from FixIMDDataFilled.thy *)
(* Lines 1-242 extracted *)
(* ========================================= *)

lemma devcache2_copy_hdata1_invariant: shows "devcache2 ( T [ 0 :=dd msg] ) = devcache2 T"
by simp
lemma devcache2_copy_perform1_invariant: shows "devcache2 ( T [ -=i 0] ) = devcache2 T"
apply simp
apply(case_tac "program1 T")
apply simp
apply simp
done
lemma devcache2_consume_hdata1_invariant: shows "devcache2 ( T [ 0 -=devd ] ) = devcache2 T"
by simp
lemma devcache1_IMDData_invariant_aux1: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ -=i 0] )) \<noteq> Modified"
apply(case_tac "program1 T")
apply simp+
done
lemma devcache1_IMDData_invariant_aux: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ -=i 0] [ 0 -=devd ])) \<noteq> Modified"
using devcache1_IMDData_invariant_aux1
by auto
lemma devcache1_IMDData_invariant: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])) \<noteq> Modified"
apply(subgoal_tac "CLEntry.block_state  (devcache1 (T  [ 0 :=dd msg ])) = Shared")
using devcache1_IMDData_invariant_aux
apply blast
by simp
lemma CSTATE_IMDData_otherside: shows "CSTATE X T 1 = CSTATE X ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1"
using CSTATE_def devcache2_consume_hdata1_invariant devcache2_copy_hdata1_invariant devcache2_copy_perform1_invariant devcache2_sequals1_invariant
  by (metis CSTATE_different2 CSTATE_otherside_rule_5_0)

lemma IMDData_Modified_aux1: shows "nextLoad T 0 \<Longrightarrow> CSTATE X T 0 = CSTATE X (T [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp+
done
lemma nextLoad_devstate: shows "nextLoad T i = nextLoad (T [0 s= mesi]) i"
by simp
lemma IMDData_Modified: shows "CSTATE Modified ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0"
apply(case_tac "program1 T")
apply simp+
done
lemma reqs1_IMDData: shows "reqs1  ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) = reqs1 T"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp+
done
lemma reqs2_IMDData: shows "reqs2  ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) = reqs2 T"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp+
done
lemma nextReqIs_IMDData: shows "nextReqIs X T i = nextReqIs X ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) i"
apply(case_tac i)
using nextReqIs_def reqs1_IMDData
apply presburger
using nextReqIs_def old.nat.distinct(2) reqs2_IMDData
by presburger
lemma IMDData_nextGOPendingIs: shows "nextGOPendingIs X T i = nextGOPendingIs X ( T [ 0 s= mesi] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) i"
apply(case_tac i)
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
apply simp
apply simp
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
by simp+
lemma IMDData_nextEvict: shows "nextEvict T 1 = nextEvict ( T [ 0 s= mesi] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
apply simp
apply simp
apply simp
done
lemma IMDData_nextLoad: shows "nextLoad T 1 = nextLoad ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
apply simp
apply simp
apply simp
done
lemma IMDData_HSTATE: shows "(HSTATE X ( T [ 0 s= Modified] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) = HSTATE X T"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
apply simp
apply simp
apply simp
done
lemma IMDData_HSTATES: shows "(HSTATE MAD ( T [ 0 s= Modified] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or>
  HSTATE MA ( T [ 0 s= Modified] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or>
  HSTATE MD ( T [ 0 s= Modified] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or>
  HSTATE ModifiedM ( T [ 0 s= Modified] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) = (HSTATE MAD T \<or> HSTATE MA T \<or> HSTATE MD T \<or> HSTATE ModifiedM T)"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
apply simp
apply simp
apply simp
done
lemma IMDData_nextSnoopIs: shows "nextSnoopIs  X T i = nextSnoopIs X ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) i"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
apply simp
apply simp
apply simp
done
lemma IMDData_nextStore_otherside: shows "nextStore T 1 = nextStore ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
apply simp
apply simp
apply simp
done
lemma device_perform_op_snps2:   " snps2  T  = snps2  ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma device_perform_op_snps1:   " snps1  T  = snps1  ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma device_perform_op_reqs1:   " reqs1  T  = reqs1  ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma device_perform_op_reqs2:   " reqs2  T  = reqs2  ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma device_perform_op_reqresps1:   " reqresps1  T  = reqresps1  ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma device_perform_op_reqresps2:   " reqresps2  T  = reqresps2  ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma device_perform_op_snpresps1:   " snpresps1  T  = snpresps1  ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma device_perform_op_snpresps2:   " snpresps2  T  = snpresps2  ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma device_perform_op_dthdatas1:   " dthdatas1  T  = dthdatas1  ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma device_perform_op_dthdatas2:   " dthdatas2  T  = dthdatas2  ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma device_perform_op_htddatas1:   " length (htddatas1  T) \<le> 1 \<Longrightarrow>   (htddatas1 ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])) = []"
apply (cases "htddatas1 T", cases "program1 T")
by(simp, simp, cases "program1 T", simp+)
lemma device_perform_op_htddatas2:   " htddatas2  T  = htddatas2  ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma device_perform_op_nextHTDDataPending:   " nextHTDDataPending  T 1 = nextHTDDataPending  ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
apply simp
apply simp
apply simp
done
lemma nextGOPending_DeviceIMDData: "nextGOPending (  T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ] ) i = nextGOPending T i"
apply(case_tac i)
using device_perform_op_reqresps1 nextGOPending_def
apply presburger
using device_perform_op_reqresps2 nextGOPending_def
by presburger

(* ========================================= *)
(* Content from FixInvalidDirtyEvictFilled.thy *)
(* Lines 1-112 extracted *)
(* ========================================= *)

lemma snps2_HostInvalidDirtyEvict: shows "snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = snps2 T"
apply(case_tac "program1 T")
by simp+
lemma snps1_HostInvalidDirtyEvict: shows "snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_HostInvalidDirtyEvict: shows "reqs2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_HostInvalidDirtyEvict: shows "snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_HostInvalidDirtyEvict: shows "snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = snpresps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_HostInvalidDirtyEvict: shows "reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostInvalidDirtyEvict: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) \<le> 1"
by simp
lemma dthdatas1_HostInvalidDirtyEvict: shows "dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = dthdatas1 T"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_HostInvalidDirtyEvict: shows "dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_HostInvalidDirtyEvict: shows "htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = htddatas1 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_HostInvalidDirtyEvict: shows "htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostInvalidDirtyEvict_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostInvalidDirtyEvict_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostInvalidDirtyEvict_invariant: shows"nextEvict T 0 = nextEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
by simp
lemma CSTATE_HostInvalidDirtyEvict_otherside_invariant2: shows
" CSTATE X ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostInvalidDirtyEvict_otherside_invariant3: shows
" CSTATE X ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 = CSTATE X T 0"
by simp
lemma HostInvalidDirtyEvict_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextGOPendingIs X T 1"
by simp
lemma HostInvalidDirtyEvict_nextEvict_otherside: shows 
"nextEvict  ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextEvict T 1"
by simp
lemma HostInvalidDirtyEvict_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostInvalidDirtyEvict_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostInvalidDirtyEvict_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 = nextSnpRespIs X T 0"
by simp
lemma HostInvalidDirtyEvict_HSTATE: shows "HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) "
apply(case_tac "program1 T")
apply  simp+
done
lemma HostInvalidDirtyEvict_nextLoad: shows "nextLoad ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) i = nextLoad T i"
apply(case_tac "program1 T")
by simp+
lemma HostInvalidDirtyEvict': shows "reqs1 (T [ 5 sHost= SharedM] [ 0 +=reqresp GO_WritePullDrop Invalid txid]) = reqs1 T"
by simp
lemma aux_r34_5: "reqresps1 T = [] \<Longrightarrow> nextGOPendingIs y  ( T  [ 0 +=reqresp y x txid]) 0"
apply simp
done
lemma aux_r34_4: "reqresps1 T = [] \<Longrightarrow>   (nextGOPendingIs y  ( T [ z sHost= t] [ 0 +=reqresp y x txid]) 0)"
apply simp
done
lemma aux_r34_3: "reqresps1 T = [] \<Longrightarrow> nextGOPendingIs y  ( T [ z sHost= t] [ 0 +=reqresp y x txid] [ 0 -=req ]) 0"
by simp
lemma nextGOPendingIs_inequality: shows "\<lbrakk>X \<noteq> Y ; nextGOPendingIs X T i \<rbrakk> \<Longrightarrow> \<not> nextGOPendingIs Y T i"
apply(case_tac i)
apply(case_tac "reqresps1 T")
apply force
apply simp
apply(case_tac "reqresps2 T")
apply simp+
done
lemma nextLoad_HostInvalidDirtyEvict: "nextLoad ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) i = nextLoad T i"
apply(case_tac i)
apply simp+
done
lemma nextGOPending_HostInvalidDirtyEvict: "nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextGOPending T 1"
apply simp+
done
lemma nextReqIs_HostInvalidDirtyEvict_otherside_1: "nextReqIs z ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextReqIs z T 1"
by simp

(* ========================================= *)
(* Content from FixInvalidLoadFilled.thy *)
(* Lines 1-74 extracted *)
(* ========================================= *)

lemma snps2_InvalidLoad: shows "snps2 ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) = snps2 T"
by simp
lemma snps1_InvalidLoad: shows "snps1 ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) = snps1 T"
by simp
lemma reqs2_InvalidLoad: shows "reqs2 ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) = reqs2 T"
by simp
lemma reqs1_InvalidLoad: shows " reqs1 T = [] \<Longrightarrow> length (reqs1 ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD])) \<le> 1"
by simp
lemma snpresps2_InvalidLoad: shows "snpresps2 ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) = snpresps2 T"
by simp
lemma snpresps1_InvalidLoad: shows "snpresps1 ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) = snpresps1 T"
by simp
lemma reqresps1_InvalidLoad: shows "reqresps1 ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) = reqresps1 T"
by simp
lemma reqresps2_InvalidLoad: shows "reqresps2 ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) = reqresps2 T"
by simp
lemma dthdatas2_InvalidLoad: shows "dthdatas2 ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) = dthdatas2 T"
by simp
lemma htddatas1_InvalidLoad: shows "htddatas1 ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) = htddatas1 T"
by simp
lemma htddatas2_InvalidLoad: shows "htddatas2 ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) = htddatas2 T"
by simp
lemma reqresps1_InvalidLoad_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma InvalidLoad'_nextDTHDataPending: "nextDTHDataPending T i = nextDTHDataPending ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) i"
by simp
lemma InvalidLoad'_nextEvict: "nextEvict T i = nextEvict ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) i"
by simp
lemma InvalidLoad'_nextStore: "nextStore T i = nextStore ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) i"
by simp
lemma InvalidLoad'_nextGOPending: "nextGOPending T i = nextGOPending ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) i"
by simp
lemma InvalidLoad'_nextGOPendingIs: "nextGOPendingIs X T i = nextGOPendingIs X ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) i"
by simp
lemma InvalidLoad'_nextHTDDataPending: "nextHTDDataPending T i = nextHTDDataPending ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) i"
by simp
lemma InvalidLoad'_HSTATE: "HSTATE X T  = HSTATE X ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) "
by simp
lemma InvalidLoad'_CSTATE_otherside: "CSTATE X T 1 = CSTATE X ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) 1"
by simp
lemma InvalidLoad'_CSTATE_sameside: "CSTATE ISAD ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) 0"
by simp
lemma InvalidLoad'_nextSnoopIs: "nextSnoopIs X T i = nextSnoopIs X ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) i"
by simp
lemma InvalidLoad'_nextReqIs_otherside: "nextReqIs X T 1 = nextReqIs X ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) 1"
by simp
lemma InvalidLoad'_nextSnpRespIs: "nextSnpRespIs X T i = nextSnpRespIs X ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) i"
by simp
lemma InvalidLoad'_nextReqIs_invariant_DirtyEvict: shows "nextReqIs DirtyEvict T i = nextReqIs DirtyEvict ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) i"
apply(case_tac i)
apply simp
apply(induct "reqs1 T")
apply force
apply (metis append_Cons startsWithProp.simps(2))
by simp
lemma InvalidLoad'_nextReqIs_invariant_not_RdOwn: shows "X \<noteq> RdShared \<Longrightarrow> nextReqIs X T i = nextReqIs X ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) i"
apply(case_tac i)
apply simp
apply(induct "reqs1 T")
apply force
apply (metis append_Cons startsWithProp.simps(2))
by simp
lemma nextGOPending_DeviceInvalidLoad: "nextGOPending (  T [ 0 +=rdreq RdShared] [ 0 s= ISAD] ) i = nextGOPending T i"
apply(case_tac i)
apply simp+
done
lemma nextLoad_DeviceInvalidLoad: "nextLoad (  T [ 0 +=rdreq RdShared] [ 0 s= ISAD] ) i = nextLoad T i"
apply(case_tac i)
apply simp+
done

(* ========================================= *)
(* Content from FixInvalidRdOwnFilled.thy *)
(* Lines 1-126 extracted *)
(* ========================================= *)

lemma HostInvalidRdOwn_nextLoad: shows "nextLoad T 1 = nextLoad (  T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified txid] [ 0 -=req ]) 1"
by simp
lemma HostInvalidRdOwn'_devcache_invariant1: shows "(CLEntry.block_state (devcache1 (  T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified txid] [ 0 -=req ]))) = CLEntry.block_state (devcache1 T)"
apply(subgoal_tac "CLEntry.block_state (devcache1 (  T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM])) = CLEntry.block_state (devcache1 (  T ))")
apply(subgoal_tac "CLEntry.block_state (devcache1 (  T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Shared txid])) = CLEntry.block_state (devcache1 (  T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM]))")
by simp+
lemma HostInvalidRdOwn'_devcache_invariant2: shows "(CLEntry.block_state (devcache2 (  T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified txid] [ 0 -=req ]))) = CLEntry.block_state (devcache2 T)"
by simp+
lemma HostInvalidRdOwn'_CSTATE_invariant1: shows "CSTATE X (  T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified txid] [ 0 -=req ]) 0 = CSTATE X T 0"
by simp
lemma HostInvalidRdOwn'_CSTATE_invariant2: shows "CSTATE X (  T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified txid] [ 0 -=req ]) 1 = CSTATE X T 1"
by simp
lemma snps2_HostInvalidRdOwn: shows "snps2 ( T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified txid] [ 0 -=req ]) = snps2 T"
by simp
lemma snps1_HostInvalidRdOwn: shows "snps1 ( T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified txid] [ 0 -=req ]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_HostInvalidRdOwn: shows "reqs2 ( T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified txid] [ 0 -=req ]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_HostInvalidRdOwn: shows "snpresps2 ( T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified txid] [ 0 -=req ]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_HostInvalidRdOwn: shows "snpresps1 ( T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified txid] [ 0 -=req ]) = snpresps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_HostInvalidRdOwn: shows "reqresps2 ( T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified txid] [ 0 -=req ]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostInvalidRdOwn: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 ( T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified txid] [ 0 -=req ])) \<le> 1"
by simp
lemma dthdatas1_HostInvalidRdOwn: shows "dthdatas1 ( T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified txid] [ 0 -=req ]) = dthdatas1 T"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_HostInvalidRdOwn: shows "dthdatas2 ( T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified txid] [ 0 -=req ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_HostInvalidRdOwn: shows "htddatas2 ( T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified txid] [ 0 -=req ]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostInvalidRdOwn_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostInvalidRdOwn_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostInvalidRdOwn_invariant: shows"nextEvict T 0 = nextEvict ( T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified txid] [ 0 -=req ]) 0"
by simp
lemma nextReqIs_HostInvalidRdOwn_IMAD_invariant2: shows 
  "nextReqIs X ( T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified txid] [ 0 -=req ]) 1 = nextReqIs X T 1"
by simp
lemma nextReqIs_HostInvalidRdOwn_IMAD_invariant1: shows 
  "length (reqs1 T) \<le> 1 \<Longrightarrow> reqs1 ( T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified txid] [ 0 -=req ])  = []"
apply(cases "reqs1 T")
by simp+
lemma CSTATE_HostInvalidRdOwn_otherside_invariant2: shows
" CSTATE X ( T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified txid] [ 0 -=req ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostInvalidRdOwn_otherside_invariant3: shows
" CSTATE X ( T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified txid] [ 0 -=req ]) 0 = CSTATE X T 0"
by simp
lemma HostInvalidRdOwn_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified txid] [ 0 -=req ]) 1 = nextGOPendingIs X T 1"
by simp
lemma HostInvalidRdOwn_nextEvict_otherside: shows 
"nextEvict  ( T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified txid] [ 0 -=req ]) 1 = nextEvict T 1"
by simp
lemma HostInvalidRdOwn_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified txid] [ 0 -=req ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostInvalidRdOwn_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified txid] [ 0 -=req ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostInvalidRdOwn_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified txid] [ 0 -=req ]) 0 = nextSnpRespIs X T 0"
by simp
lemma HostInvalidRdOwn_HSTATE: shows "HSTATE ModifiedM ( T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified txid] [ 0 -=req ]) "
apply(case_tac "program1 T")
by simp+
lemma HostInvalidRdOwn_empty_reqs1_aux: shows " reqs1 T = reqs1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD])"
by simp
lemma reqresps2_HostInvalidRdOwn_remains: shows "reqresps2 (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM]) = reqresps2 T"
by simp
lemma snps2_single_HostInvalidRdOwn: shows "reqresps2 T = [] \<Longrightarrow> length (reqresps2 (T [ 0 +=reqresp GO Shared txid])) \<le> 1 "
by simp
lemma snps2_HostInvalidRdOwn_aux1: shows "reqresps2 T = reqresps2 ( T [ 0 -=req])"
by simp
lemma snps2_HostInvalidRdOwn_aux2: shows "reqresps2 T = [] \<Longrightarrow> length (reqresps2  ( T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Shared txid] )) \<le> 1"
using reqresps2_HostInvalidRdOwn_remains snps2_single_HostInvalidRdOwn
by presburger
lemma HostInvalidRdOwn_one_msg_htddatas1: shows "htddatas1 T = [] \<Longrightarrow> length (htddatas1 ( T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified txid] [ 0 -=req ])) \<le> 1"
apply(subgoal_tac "length (htddatas1 ( T [ 0 +=hostdata  txid])) \<le> 1")
apply(subgoal_tac "htddatas1 ( T [ 0 +=hostdata  txid]) = htddatas1 ( T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified txid] [ 0 -=req ])")
apply metis
by simp+
lemma nextLoad_HostInvalidRdOwn: "nextLoad (  T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ] ) i = nextLoad T i"
apply(case_tac i)
apply simp+
done
lemma reqs1_length_HostInvalidRdOwn: "length (reqs1 T) \<le> 1 \<Longrightarrow> reqs1 ( T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Modified txid] [ 0 -=req ]) = []"
apply simp
apply(case_tac "reqs1 T")
apply simp
by simp
lemma nextGOPending_HostInvalidRdOwn: "nextGOPending (  T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ] ) 1 = nextGOPending T 1"
apply simp
done

(* ========================================= *)
(* Content from FixInvalidRdSharedFilled.thy *)
(* Lines 1-119 extracted *)
(* ========================================= *)

lemma HostInvalidRdShared_nextLoad: shows "nextLoad T 1 = nextLoad (  T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) 1"
by simp
lemma HostInvalidRdShared'_devcache_invariant1: shows "(CLEntry.block_state (devcache1 (  T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]))) = CLEntry.block_state (devcache1 T)"
apply(subgoal_tac "CLEntry.block_state (devcache1 (  T [ 0 +=hostdata  txid] [ 5 sHost= SharedM])) = CLEntry.block_state (devcache1 (  T ))")
apply(subgoal_tac "CLEntry.block_state (devcache1 (  T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid])) = CLEntry.block_state (devcache1 (  T [ 0 +=hostdata  txid] [ 5 sHost= SharedM]))")
by simp+
lemma HostInvalidRdShared'_devcache_invariant2: shows "(CLEntry.block_state (devcache2 (  T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]))) = CLEntry.block_state (devcache2 T)"
by simp+
lemma HostInvalidRdShared'_CSTATE_invariant1: shows "CSTATE X (  T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) 0 = CSTATE X T 0"
by simp
lemma HostInvalidRdShared'_CSTATE_invariant2: shows "CSTATE X (  T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) 1 = CSTATE X T 1"
by simp
lemma snps2_HostInvalidRdShared: shows "snps2 ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) = snps2 T"
by simp
lemma snps1_HostInvalidRdShared: shows "snps1 ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_HostInvalidRdShared: shows "reqs2 ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_HostInvalidRdShared: shows "snpresps2 ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_HostInvalidRdShared: shows "snpresps1 ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) = snpresps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_HostInvalidRdShared: shows "reqresps2 ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostInvalidRdShared: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ])) \<le> 1"
by simp
lemma dthdatas1_HostInvalidRdShared: shows "dthdatas1 ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) = dthdatas1 T"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_HostInvalidRdShared: shows "dthdatas2 ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_HostInvalidRdShared: shows "htddatas2 ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostInvalidRdShared_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostInvalidRdShared_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostInvalidRdShared_invariant: shows"nextEvict T 0 = nextEvict ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) 0"
by simp
lemma CSTATE_HostInvalidRdShared_otherside_invariant2: shows
" CSTATE X ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostInvalidRdShared_otherside_invariant3: shows
" CSTATE X ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) 0 = CSTATE X T 0"
by simp
lemma HostInvalidRdShared_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) 1 = nextGOPendingIs X T 1"
by simp
lemma HostInvalidRdShared_nextEvict_otherside: shows 
"nextEvict  ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) 1 = nextEvict T 1"
by simp
lemma HostInvalidRdShared_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostInvalidRdShared_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostInvalidRdShared_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) 0 = nextSnpRespIs X T 0"
by simp
lemma HostInvalidRdShared_HSTATE: shows "HSTATE SharedM ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) "
apply(case_tac "program1 T")
by simp+
lemma HostInvalidRdShared_empty_reqs1_aux: shows " reqs1 T = reqs1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD])"
by simp
lemma reqresps2_HostInvalidRdShared_remains: shows "reqresps2 (T [ 0 +=hostdata  txid] [ 5 sHost= SharedM]) = reqresps2 T"
by simp
lemma snps2_single_HostInvalidRdShared: shows "reqresps2 T = [] \<Longrightarrow> length (reqresps2 (T [ 0 +=reqresp GO Shared txid])) \<le> 1 "
by simp
lemma snps2_HostInvalidRdShared_aux1: shows "reqresps2 T = reqresps2 ( T [ 0 -=req])"
by simp
lemma snps2_HostInvalidRdShared_aux2: shows "reqresps2 T = [] \<Longrightarrow> length (reqresps2  ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] )) \<le> 1"
using reqresps2_HostInvalidRdShared_remains snps2_single_HostInvalidRdShared
by presburger
lemma HostInvalidRdShared_one_msg_htddatas1: shows "htddatas1 T = [] \<Longrightarrow> length (htddatas1 ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ])) \<le> 1"
apply(subgoal_tac "length (htddatas1 ( T [ 0 +=hostdata  txid])) \<le> 1")
apply(subgoal_tac "htddatas1 ( T [ 0 +=hostdata  txid]) = htddatas1 ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ])")
apply metis
by simp+
lemma nextLoad_HostInvalidRdShared: "nextLoad (  T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ] ) i = nextLoad T i"
apply(case_tac i)
apply simp+
done
lemma reqs1_length_HostInvalidRdShared: "length (reqs1 T) \<le> 1 \<Longrightarrow> reqs1 ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) = []"
apply simp
apply(case_tac "reqs1 T")
apply simp
by simp
lemma nextGOPending_HostInvalidRdShared: "nextGOPending (  T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ] ) 1 = nextGOPending T 1"
apply simp
done

(* ========================================= *)
(* Content from FixInvalidStoreFilled.thy *)
(* Lines 1-81 extracted *)
(* ========================================= *)

lemma snps2_InvalidStore: shows "snps2 ( T [ 0 +=rdreq RdOwn] [ 0 s= IMAD]) = snps2 T"
by simp
lemma snps1_InvalidStore: shows "snps1 ( T [ 0 +=rdreq RdOwn] [ 0 s= IMAD]) = snps1 T"
by simp
lemma reqs2_InvalidStore: shows "reqs2 ( T [ 0 +=rdreq RdOwn] [ 0 s= IMAD]) = reqs2 T"
by simp
lemma reqs1_InvalidStore: shows " reqs1 T = [] \<Longrightarrow> length (reqs1 ( T [ 0 +=rdreq RdOwn] [ 0 s= IMAD])) \<le> 1"
by simp
lemma snpresps2_InvalidStore: shows "snpresps2 ( T [ 0 +=rdreq RdOwn] [ 0 s= IMAD]) = snpresps2 T"
by simp
lemma snpresps1_InvalidStore: shows "snpresps1 ( T [ 0 +=rdreq RdOwn] [ 0 s= IMAD]) = snpresps1 T"
by simp
lemma reqresps1_InvalidStore: shows "reqresps1 ( T [ 0 +=rdreq RdOwn] [ 0 s= IMAD]) = reqresps1 T"
by simp
lemma reqresps2_InvalidStore: shows "reqresps2 ( T [ 0 +=rdreq RdOwn] [ 0 s= IMAD]) = reqresps2 T"
by simp
lemma dthdatas2_InvalidStore: shows "dthdatas2 ( T [ 0 +=rdreq RdOwn] [ 0 s= IMAD]) = dthdatas2 T"
by simp
lemma htddatas1_InvalidStore: shows "htddatas1 ( T [ 0 +=rdreq RdOwn] [ 0 s= IMAD]) = htddatas1 T"
by simp
lemma htddatas2_InvalidStore: shows "htddatas2 ( T [ 0 +=rdreq RdOwn] [ 0 s= IMAD]) = htddatas2 T"
by simp
lemma reqresps1_InvalidStore_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma InvalidStore'_nextDTHDataPending: "nextDTHDataPending T i = nextDTHDataPending ( T [ 0 +=rdreq RdOwn] [ 0 s= IMAD]) i"
by simp
lemma InvalidStore'_nextEvict: "nextEvict T i = nextEvict ( T [ 0 +=rdreq RdOwn] [ 0 s= IMAD]) i"
by simp
lemma InvalidStore'_nextStore: "nextStore T i = nextStore ( T [ 0 +=rdreq RdOwn] [ 0 s= IMAD]) i"
by simp
lemma InvalidStore'_nextGOPending: "nextGOPending T i = nextGOPending ( T [ 0 +=rdreq RdOwn] [ 0 s= IMAD]) i"
by simp
lemma InvalidStore'_nextGOPendingIs: "nextGOPendingIs X T i = nextGOPendingIs X ( T [ 0 +=rdreq RdOwn] [ 0 s= IMAD]) i"
by simp
lemma InvalidStore'_nextHTDDataPending: "nextHTDDataPending T i = nextHTDDataPending ( T [ 0 +=rdreq RdOwn] [ 0 s= IMAD]) i"
by simp
lemma InvalidStore'_HSTATE: "HSTATE X T  = HSTATE X ( T [ 0 +=rdreq RdOwn] [ 0 s= IMAD]) "
by simp
lemma InvalidStore'_CSTATE_otherside: "CSTATE X T 1 = CSTATE X ( T [ 0 +=rdreq RdOwn] [ 0 s= IMAD]) 1"
by simp
lemma InvalidStore'_CSTATE_sameside: "CSTATE IMAD ( T [ 0 +=rdreq RdOwn] [ 0 s= IMAD]) 0"
by simp
lemma InvalidStore'_nextSnoopIs: "nextSnoopIs X T i = nextSnoopIs X ( T [ 0 +=rdreq RdOwn] [ 0 s= IMAD]) i"
by simp
lemma InvalidStore'_nextReqIs_otherside: "nextReqIs X T 1 = nextReqIs X ( T [ 0 +=rdreq RdOwn] [ 0 s= IMAD]) 1"
by simp
lemma InvalidStore'_nextSnpRespIs: "nextSnpRespIs X T i = nextSnpRespIs X ( T [ 0 +=rdreq RdOwn] [ 0 s= IMAD]) i"
by simp
lemma InvalidStore'_nextReqIs_invariant1: shows "nextReqIs RdShared T i = nextReqIs RdShared ( T [ 0 +=rdreq RdOwn] [ 0 s= IMAD]) i"
apply(case_tac i)
apply simp
apply(induct "reqs1 T")
apply force
apply (metis append_Cons startsWithProp.simps(2))
by simp
lemma InvalidStore'_nextReqIs_invariant_DirtyEvict: shows "nextReqIs DirtyEvict T i = nextReqIs DirtyEvict ( T [ 0 +=rdreq RdOwn] [ 0 s= IMAD]) i"
apply(case_tac i)
apply simp
apply(induct "reqs1 T")
apply force
apply (metis append_Cons startsWithProp.simps(2))
by simp
lemma InvalidStore'_nextReqIs_invariant_not_RdOwn: shows "X \<noteq> RdOwn \<Longrightarrow> nextReqIs X T i = nextReqIs X ( T [ 0 +=rdreq RdOwn] [ 0 s= IMAD]) i"
apply(case_tac i)
apply simp
apply(induct "reqs1 T")
apply force
apply (metis append_Cons startsWithProp.simps(2))
by simp
lemma nextGOPending_DeviceInvalidStore: "nextGOPending (  T [ 0 +=rdreq RdOwn] [ 0 s= IMAD] ) i = nextGOPending T i"
apply(case_tac i)
apply simp+
done
lemma nextLoad_DeviceInvalidStore: "nextLoad (  T [ 0 +=rdreq RdOwn] [ 0 s= IMAD] ) i = nextLoad T i"
apply(case_tac i)
apply simp+
done

(* ========================================= *)
(* Content from FixISADDataFilled.thy *)
(* Lines 1-98 extracted *)
(* ========================================= *)

lemma nextSnoopPending_ISADData1: shows "nextSnoopPending ( T [ 0 s= ISA] [ 0 :=dd getHTDDataOrMakeup T 0] [ 0 -=devd ]) 1 = nextSnoopPending T 1"
using DeviceID.simps(3) Type1State.iffs Type1State.surjective Type1State.update_convs(2) change_state_def config_differ_dev_mapping_def device_copy_in_data_def nextSnoopPending_def nextSnoopPending_devConsume_data_invariant
by auto
lemma HSTATE_ISADData: shows "HSTATE X T = HSTATE X (T [ 0 s= ISA] [ 0 :=dd getHTDDataOrMakeup T 0] [ 0 -=devd ])"
using hstate_invariants(17) hstate_invariants(20) hstate_invariants(24)
by presburger
lemma CSTATE_ISADData_otherside: shows "CSTATE X T 1 = CSTATE X ( T [ 0 s= ISA] [ 0 :=dd msg ]  [ 0 -=devd ]) 1"
by simp
lemma nextReqIs_ISADData: shows "nextReqIs X T i = nextReqIs X ( T [ 0 s= ISA] [ 0 :=dd msg ]  [ 0 -=devd ]) i"
by simp
lemma ISADData_nextGOPendingIs: shows "nextGOPendingIs X T i = nextGOPendingIs X ( T [ 0 s= ISA] [ 0 :=dd msg ]  [ 0 -=devd ]) i"
by simp
lemma ISADData_nextEvict: shows "nextEvict T 1 = nextEvict ( T [ 0 s= ISA] [ 0 :=dd msg ]  [ 0 -=devd ]) 1"
by simp
lemma ISADData_nextLoad: shows "nextLoad T 1 = nextLoad ( T [ 0 s= ISA] [ 0 :=dd msg ]  [ 0 -=devd ]) 1"
by simp
lemma ISADData_HSTATE: shows "(HSTATE X ( T [ 0 s= ISA] [ 0 :=dd msg ]  [ 0 -=devd ])) = HSTATE X T"
by simp
lemma ISADData_HSTATES: shows "(HSTATE MAD ( T [ 0 s= ISA] [ 0 :=dd msg ]  [ 0 -=devd ]) \<or>
  HSTATE MA ( T [ 0 s= ISA] [ 0 :=dd msg ]  [ 0 -=devd ]) \<or>
  HSTATE MD ( T [ 0 s= ISA] [ 0 :=dd msg ]  [ 0 -=devd ]) \<or>
  HSTATE ModifiedM ( T [ 0 s= ISA] [ 0 :=dd msg ]  [ 0 -=devd ])) = (HSTATE MAD T \<or> HSTATE MA T \<or> HSTATE MD T \<or> HSTATE ModifiedM T)"
by simp
lemma ISADData_nextSnoopIs: shows "nextSnoopIs  X T i = nextSnoopIs X ( T [ 0 s= ISA] [ 0 :=dd msg ]  [ 0 -=devd ]) i"
by simp
lemma ISADData_nextStore_otherside: shows "nextStore T 1 = nextStore ( T [ 0 s= ISA] [ 0 :=dd msg ]  [ 0 -=devd ]) 1"
by simp
lemma ISADData_nextHTDDataPending_otherside: shows "nextHTDDataPending T 1 = nextHTDDataPending ( T [ 0 s= ISA] [ 0 :=dd msg ]  [ 0 -=devd ]) 1"
by simp
lemma ISADData_snps2:   " snps2  T  = snps2  ( T [ 0 s= ISA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma ISADData_snps1:   " snps1  T  = snps1  ( T [ 0 s= ISA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma ISADData_reqs1:   " reqs1  T  = reqs1  ( T [ 0 s= ISA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma ISADData_reqs2:   " reqs2  T  = reqs2  ( T [ 0 s= ISA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma ISADData_reqresps1:   " reqresps1  T  = reqresps1  ( T [ 0 s= ISA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma ISADData_reqresps2:   " reqresps2  T  = reqresps2  ( T [ 0 s= ISA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma ISADData_snpresps1:   " snpresps1  T  = snpresps1  ( T [ 0 s= ISA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma ISADData_snpresps2:   " snpresps2  T  = snpresps2  ( T [ 0 s= ISA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma ISADData_dthdatas1:   " dthdatas1  T  = dthdatas1  ( T [ 0 s= ISA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma ISADData_dthdatas2:   " dthdatas2  T  = dthdatas2  ( T [ 0 s= ISA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma ISADData_htddatas1:   " length (htddatas1  T) \<le> 1 \<Longrightarrow>   (htddatas1 ( T [ 0 s= ISA] [ 0 :=dd msg ]  [ 0 -=devd ])) = []"
apply(cases "htddatas1 T", simp+)
done
lemma ISADData_htddatas2:   " htddatas2  T  = htddatas2  ( T [ 0 s= ISA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma nextGOPending_DeviceISADData: "nextGOPending (  T [ 0 s= ISA] [ 0 :=dd msg ]  [ 0 -=devd ] ) i = nextGOPending T i"
apply(case_tac i)
apply simp+
done
lemma nextLoad_DeviceISADData: "nextLoad (  T [ 0 s= ISA] [ 0 :=dd msg ]  [ 0 -=devd ] ) i = nextLoad T i"
apply(case_tac i)
apply simp+
done

(* ========================================= *)
(* Content from FixISADGOFilled.thy *)
(* Lines 1-92 extracted *)
(* ========================================= *)

lemma devcache1_ISADGO_invariant_aux1: shows "CLEntry.block_state  (devcache1 T) = ISD \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ 0 -=reqresp ] )) \<noteq> Modified"
by simp
lemma devcache1_ISADGO_invariant_aux: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ 0 -=reqresp ] [ 0 -=devd ])) \<noteq> Modified"
by simp
lemma devcache1_ISADGO_invariant: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T [ 0 :=dd msg ] [ 0 -=reqresp ] [ 0 -=devd ])) \<noteq> Modified"
apply(subgoal_tac "CLEntry.block_state  (devcache1 (T  [ 0 :=dd msg ])) = Shared")
using devcache1_ISADGO_invariant_aux
apply blast
by simp
lemma ISADGO'_nextDTHDataPending: "nextDTHDataPending T i = nextDTHDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= ISD] [ 0 -=reqresp ]) i"
by simp
lemma ISADGO'_nextEvict: "nextEvict T i = nextEvict ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= ISD] [ 0 -=reqresp ]) i"
by simp
lemma ISADGO'_nextStore: "nextStore T i = nextStore ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= ISD] [ 0 -=reqresp ]) i"
by simp
lemma ISADGO'_not_nextGOPending: "length (reqresps1 T) \<le> 1 \<Longrightarrow> \<not> nextGOPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= ISD] [ 0 -=reqresp ]) 0"
apply(subgoal_tac " reqresps1 (T \<lparr>buffer1 := Some m\<rparr> [ 0 s= ISD]) = reqresps1 T")
apply(subgoal_tac " length (reqresps1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= ISD])) \<le> 1")
apply(case_tac "reqresps1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= ISD])")
by simp+
lemma ISADGO'_nextGOPending1: "nextGOPending  T 1 = nextGOPending  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= ISD] [ 0 -=reqresp ]) 1"
by simp
lemma ISADGO'_nextGOPendingIs: "nextGOPendingIs X T 1 = nextGOPendingIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= ISD] [ 0 -=reqresp ]) 1"
by simp
lemma ISADGO'_nextHTDDataPending: "nextHTDDataPending T i = nextHTDDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= ISD] [ 0 -=reqresp ]) i"
apply  simp
done
lemma ISADGO'_HSTATE: "HSTATE X T  = HSTATE X ( T \<lparr>buffer1 := OM\<rparr> [ i s= m] [ j -=reqresp ]) "
by simp
lemma ISADGO'_HSTATE_neg: "\<not> (HSTATE X T)  = (\<not> (HSTATE X ( T \<lparr>buffer1 := OM\<rparr> [ i s= m] [ j -=reqresp ]))) "
apply  simp
done
lemma ISADGO'_CSTATE_otherside: "CSTATE X T 1 = CSTATE X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= ISD] [ 0 -=reqresp ]) 1"
apply  simp
done
lemma ISADGO'_CSTATE_sameside: "CSTATE ISD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= ISD] [ 0 -=reqresp ]) 0"
by simp
lemma ISADGO'_nextSnoopIs: "nextSnoopIs X T i = nextSnoopIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= ISD] [ 0 -=reqresp ]) i"
apply  simp
done
lemma ISADGO'_nextReqIs: "nextReqIs X T i = nextReqIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= ISD] [ 0 -=reqresp ]) i"
apply  simp
done
lemma ISADGO'_nextSnpRespIs: "nextSnpRespIs X T i = nextSnpRespIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= ISD] [ 0 -=reqresp ]) i"
apply  simp
done
lemma ISADGO'_nextReqIs_invariant1: shows "nextReqIs x T i = nextReqIs x ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= ISD] [ 0 -=reqresp ]) i"
apply(case_tac i)
apply simp
apply simp
done
lemma ISADGO'_nextReqIs_invariant_DirtyEvict: shows "nextReqIs DirtyEvict T i = nextReqIs DirtyEvict ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= ISD] [ 0 -=reqresp ]) i"
apply(case_tac i)
apply simp+
done
lemma ISADGO'_nextReqIs_invariant_not_RdOwn: shows "X \<noteq> RdOwn \<Longrightarrow> nextReqIs X T i = nextReqIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= ISD] [ 0 -=reqresp ]) i"
apply(case_tac i)
apply simp+
done
lemma reqs2_ISADGO: shows "reqs2 T = reqs2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= ISD] [ 0 -=reqresp ])"
by simp
lemma nextLoad_ISADGO: shows "nextLoad ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= ISD] [ 0 -=reqresp ]) 0 = nextLoad T 0"
by simp
lemma nextLoad2_ISADGO: shows "nextLoad ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= ISD] [ 0 -=reqresp ]) 1 = nextLoad T 1"
by simp
lemma nextLoad_DeviceISADGO: "nextLoad (  T \<lparr>buffer1 := Some m\<rparr> [ 0 s= ISD] [ 0 -=reqresp ] ) i = nextLoad T i"
apply(case_tac i)
apply simp+
done
lemma nextGOPending_DeviceISADGO: "nextGOPending (  T \<lparr>buffer1 := Some m\<rparr> [ 0 s= ISD] [ 0 -=reqresp ] ) 1 = nextGOPending T 1"
apply simp+
done
lemma reqresps1_noGOPending: "reqresps1 T = [] \<Longrightarrow> \<not> nextGOPendingIs X T 0"
apply(cases X)
by simp+
lemma reqresps1_noGOPendingp: "reqresps1 T = [] \<Longrightarrow> \<not> nextGOPending T 0"
by simp+

(* ========================================= *)
(* Content from FixISAGOFilled.thy *)
(* Lines 1-350 extracted *)
(* ========================================= *)

lemma nextStore_ISAGO_invariant: shows"nextStore T 0 = nextStore ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] ) 0"
by simp
lemma HSTATE_ISAGO_invariant: shows "HSTATE X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) = 
  HSTATE X T"
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp+
done
lemma nextReqIs_ISAGO_IMAD_invariant2: shows 
  "nextReqIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) 1 = nextReqIs X T 1"
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac "a")
apply simp
subgoal
subgoal
apply auto
done
done
by simp
lemma nextReqIs_ISAGO_IMAD_invariant1: shows 
  "nextReqIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) 0 = nextReqIs X T 0"
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac "a")
apply simp
subgoal
subgoal
apply auto
done
done
by simp
lemma CSTATE_ISAGO_otherside_invariant2: shows
" CSTATE X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) 1 = CSTATE X T 1"
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac "a")
apply simp
subgoal
subgoal
apply auto
done
done
by simp
lemma ISAGO_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) 1 = nextGOPendingIs X T 1"
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac "a")
apply simp
subgoal
subgoal
apply auto
done
done
by simp
lemma ISAGO_nextEvict_otherside: shows 
"nextEvict  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) 1 = nextEvict T 1"
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac "a")
apply simp
subgoal
subgoal
apply auto
done
done
by simp
lemma ISAGO_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) 1 = nextDTHDataPending T 1"
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac "a")
apply simp
subgoal
subgoal
apply auto
done
done
by simp
lemma ISAGO_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) 1 = nextSnpRespIs X T 1"
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac "a")
apply simp
subgoal
subgoal
apply auto
done
done
by simp
lemma ISAGO_nextDTHDataPending_sameside: shows 
"nextDTHDataPending  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) 0 = nextDTHDataPending T 0"
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac "a")
apply simp
subgoal
subgoal
apply auto
done
done
by simp
lemma ISAGO_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) 0 = nextSnpRespIs X T 0"
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac "a")
apply simp
subgoal
subgoal
apply auto
done
done
by simp
lemma devcache1_ISAGO_invariant_aux1: shows "CLEntry.block_state  (devcache1 T) = ISD \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ 0 -=reqresp ] )) \<noteq> Modified"
using MESI_State.distinct(7) devcache1_consume_reqresps1_invariant
by presburger
lemma devcache1_ISAGO_invariant_aux: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ 0 -=reqresp ] [ 0 -=devd ])) \<noteq> Modified"
using devcache1_ISAGO_invariant_aux1
by auto
lemma devcache1_ISAGO_invariant: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T [ 0 :=dd msg ] [ 0 -=reqresp ] [ 0 -=devd ])) \<noteq> Modified"
apply(subgoal_tac "CLEntry.block_state  (devcache1 (T  [ 0 :=dd msg ])) = Shared")
using devcache1_ISAGO_invariant_aux
apply blast
by simp
lemma CSTATE_ISAGO_IMAD_invariant: shows "
CSTATE Shared (T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ]  [ -=i 0]) 0"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
by simp+
lemma nextSnoopIs_ISAGO: shows 
  "nextSnoopIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) i = nextSnoopIs X T i"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp
by simp+
lemma CSTATE_ISAGO_otherside: shows "CSTATE X T 1 = CSTATE X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) 1"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp
by simp+
lemma nextReqIs_ISAGO: shows "nextReqIs X T i = nextReqIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) i"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp
by simp+
lemma ISAGO_snps2:   " snps2  T  = snps2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma ISAGO_snps1:   " snps1  T  = snps1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma ISAGO_reqs1:   " reqs1  T  = reqs1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma ISAGO_reqs2:   " reqs2  T  = reqs2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma ISAGO_reqresps2:   " reqresps2  T  = reqresps2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma ISAGO_snpresps1:   " snpresps1  T  = snpresps1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma ISAGO_snpresps2:   " snpresps2  T  = snpresps2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma ISAGO_dthdatas1:   " dthdatas1  T = [] \<Longrightarrow> 
  length (dthdatas1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0])) \<le> 1"
apply (cases "program1 T")
apply simp
apply simp
done
lemma ISAGO_dthdatas2:   " dthdatas2  T  = dthdatas2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma ISAGO_htddatas1:   "htddatas1 T =  (htddatas1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]))"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
using Type1State.update_convs(12) Type1State.update_convs(2) Type1State.update_convs(8) change_state_def config_differ_dev_mapping_def config_differ_dthdata_def consumeReqresp_def device_perform_op_htddatas1
apply force
by simp+
lemma ISAGO_htddatas2:   " htddatas2  T  = htddatas2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma ISAGO_nextHTDDataPending: "nextHTDDataPending T i = 
  nextHTDDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0])  i"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp+
done
lemma snps2_ISAGO: shows "snps2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) = snps2 T"
apply(case_tac "program1 T")
by simp+
lemma snps1_ISAGO: shows "snps1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_ISAGO: shows "reqs2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma reqs1_ISAGO: shows "reqs1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) = reqs1 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_ISAGO: shows "snpresps2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_ISAGO: shows "snpresps1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) = snpresps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_ISAGO: shows "reqresps2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_ISAGO: shows "dthdatas2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_ISAGO: shows "htddatas1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) = htddatas1 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_ISAGO: shows "htddatas2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_ISAGO_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_ISAGO_aux1: shows "reqresps1 T = reqresps1 (T [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_ISAGO: assumes "length (reqresps1 T) \<le> 1" shows "reqresps1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) = []"
proof -
have half_same: " (reqresps1  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared])) = reqresps1 T" by simp
have quarter_reduce: "reqresps1 (T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ]) = []"
proof -
have half_l1: "length (reqresps1  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] )) \<le> 1"
using assms half_same
by presburger
show ?thesis
using half_l1 reqresps1_ISAGO_aux
by presburger
qed
have quarter_same: "reqresps1  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ]) = reqresps1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0])"
using reqresps1_ISAGO_aux1
by blast
show ?thesis
using quarter_reduce quarter_same
by presburger
qed
lemma ISAGO_CSTATE_aux: shows "CSTATE X T 0 = CSTATE X ( T [ 0 -=reqresp ]  [ -=i 0]) 0"
apply(case_tac "program1 T")
by simp+
lemma nextGOPending_DeviceISAGO_other: "nextGOPending (  T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0] ) 1 = nextGOPending T 1"
apply(case_tac "program1 T")
apply simp+
done
lemma nextLoad_DeviceISAGO: "nextLoad (  T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0] ) 1 = nextLoad T 1"
apply(case_tac "program1 T")
apply simp+
done
lemma nextGOPending_DeviceISAGO: "nextGOPending (  T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0] ) 1 = nextGOPending T 1"
using nextGOPending_DeviceISAGO_other
by blast
lemma ISAGO_nextHTDDataPending_sameside: shows 
"nextHTDDataPending  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) i = nextHTDDataPending T i"
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac "a")
apply simp
subgoal
subgoal
apply auto
done
done
by simp

(* ========================================= *)
(* Content from FixISDDataFilled.thy *)
(* Lines 1-271 extracted *)
(* ========================================= *)

lemma devcache1_ISDData_invariant_aux1: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ -=i 0] )) \<noteq> Modified"
apply(case_tac "program1 T")
apply simp+
done
lemma devcache1_ISDData_invariant_aux: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ -=i 0] [ 0 -=devd ])) \<noteq> Modified"
using devcache1_ISDData_invariant_aux1
by auto
lemma devcache1_ISDData_invariant: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])) \<noteq> Modified"
apply(subgoal_tac "CLEntry.block_state  (devcache1 (T  [ 0 :=dd msg ])) = Shared")
using devcache1_ISDData_invariant_aux
apply blast
by simp
lemma CSTATE_ISDData_otherside: shows "CSTATE X T 1 = CSTATE X ( T [ 0 s= Shared] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1"
using CSTATE_def devcache2_consume_hdata1_invariant devcache2_copy_hdata1_invariant devcache2_copy_perform1_invariant devcache2_sequals1_invariant

  by (metis CSTATE_different2 CSTATE_otherside_rule_5_0)

lemma ISDData_Shared_aux1: shows "nextLoad T 0 \<Longrightarrow> CSTATE X T 0 = CSTATE X (T [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp+
done
lemma ISDData_Shared: shows "nextLoad T 0 \<Longrightarrow> CSTATE Shared ( T [ 0 s= Shared] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0"
apply(subgoal_tac "CSTATE Shared ( T [ 0 s= Shared]) 0")
apply(subgoal_tac "CSTATE Shared ( T [ 0 s= Shared] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 = CSTATE Shared ( T [ 0 s= Shared]) 0")
apply blast
apply(subgoal_tac "nextLoad (T [0 s= Shared]) 0")
using ISDData_Shared_aux1
apply blast
apply simp+
done
lemma reqs1_ISDData: shows "reqs1  ( T [ 0 s= Shared] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) = reqs1 T"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp+
done
lemma reqs2_ISDData: shows "reqs2  ( T [ 0 s= Shared] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) = reqs2 T"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp+
done
lemma nextReqIs_ISDData: shows "nextReqIs X T i = nextReqIs X ( T [ 0 s= Shared] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) i"
apply(case_tac i)
using nextReqIs_def reqs1_ISDData
apply presburger
using nextReqIs_def old.nat.distinct(2) reqs2_ISDData
by presburger
lemma ISDData_nextGOPendingIs: shows "nextGOPendingIs X T i = nextGOPendingIs X ( T [ 0 s= mesi] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) i"
apply(case_tac i)
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
apply simp
apply simp
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
by simp+
lemma ISDData_nextEvict: shows "nextEvict T 1 = nextEvict ( T [ 0 s= mesi] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
apply simp
apply simp
apply simp
done
lemma ISDData_nextLoad: shows "nextLoad T 1 = nextLoad ( T [ 0 s= Shared] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
apply simp
apply simp
apply simp
done
lemma ISDData_HSTATE: shows "(HSTATE X ( T [ 0 s= Shared] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) = HSTATE X T"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
apply simp
apply simp
apply simp
done
lemma ISDData_HSTATES: shows "(HSTATE MAD ( T [ 0 s= Shared] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or>
  HSTATE MA ( T [ 0 s= Shared] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or>
  HSTATE MD ( T [ 0 s= Shared] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or>
  HSTATE ModifiedM ( T [ 0 s= Shared] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) = (HSTATE MAD T \<or> HSTATE MA T \<or> HSTATE MD T \<or> HSTATE ModifiedM T)"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
apply simp
apply simp
apply simp
done
lemma ISDData_nextSnoopIs: shows "nextSnoopIs  X T i = nextSnoopIs X ( T [ 0 s= Shared] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) i"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
apply simp
apply simp
apply simp
done
lemma ISDData_nextStore_otherside: shows "nextStore T 1 = nextStore ( T [ 0 s= Shared] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
apply simp
apply simp
apply simp
done


lemma nextGOPending_DeviceISDData: "nextGOPending (  T [ 0 s= Shared] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ] ) i = nextGOPending T i"
apply(case_tac i)
using device_perform_op_reqresps1 nextGOPending_def

  apply (metis nextGOPending_General_rule_4_0)

  by (smt (verit, best) INVALID_ROW_def LOAD_COL_def MEM_I_ROW_def MEM_RDS_COL_def One_nat_def SnoopType.size_gen(1)
      nat.distinct(1) nextGOPending_General_rule_4_1 nextGOPending_def nextGOPending_various_forms3
      nextGOPending_various_forms4)

lemma nextLoad_DeviceISDData: "nextLoad (  T [ 0 s= Shared] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ] ) 1 = nextLoad T 1"
using ISDData_nextLoad
by presburger

(* ========================================= *)
(* Content from FixISDIDataFilled.thy *)
(* Lines 1-266 extracted *)
(* ========================================= *)

lemma devcache1_ISDIData_invariant_aux1: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ -=i 0] )) \<noteq> Modified"
apply(case_tac "program1 T")
apply simp+
done
lemma devcache1_ISDIData_invariant_aux: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ -=i 0] [ 0 -=devd ])) \<noteq> Modified"
using devcache1_ISDIData_invariant_aux1
by auto
lemma devcache1_ISDIData_invariant: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])) \<noteq> Modified"
apply(subgoal_tac "CLEntry.block_state  (devcache1 (T  [ 0 :=dd msg ])) = Shared")
using devcache1_ISDIData_invariant_aux
apply blast
by simp
lemma CSTATE_ISDIData_otherside: shows "CSTATE X T 1 = CSTATE X ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1"
using CSTATE_def devcache2_consume_hdata1_invariant devcache2_copy_hdata1_invariant devcache2_copy_perform1_invariant devcache2_sequals1_invariant

  by (metis CSTATE_different2 CSTATE_otherside_rule_5_0)
lemma ISDIData_Shared_aux1: shows "nextLoad T 0 \<Longrightarrow> CSTATE X T 0 = CSTATE X (T [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp+
done
lemma ISDIData_Shared: shows " CSTATE Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0"
apply(case_tac "program1 T")
apply simp+
done
lemma reqs1_ISDIData: shows "reqs1  ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) = reqs1 T"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp+
done
lemma reqs2_ISDIData: shows "reqs2  ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) = reqs2 T"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp+
done
lemma nextReqIs_ISDIData: shows "nextReqIs X T i = nextReqIs X ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) i"
apply(case_tac i)
using nextReqIs_def reqs1_ISDIData
apply presburger
using nextReqIs_def old.nat.distinct(2) reqs2_ISDIData
by presburger
lemma ISDIData_nextGOPendingIs: shows "nextGOPendingIs X T i = nextGOPendingIs X ( T [ 0 s= mesi] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) i"
apply(case_tac i)
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
apply simp
apply simp
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
by simp+
lemma ISDIData_nextEvict: shows "nextEvict T 1 = nextEvict ( T [ 0 s= mesi] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
apply simp
apply simp
apply simp
done
lemma ISDIData_nextLoad: shows "nextLoad T 1 = nextLoad ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
apply simp
apply simp
apply simp
done
lemma ISDIData_HSTATE: shows "(HSTATE X ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) = HSTATE X T"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
apply simp
apply simp
apply simp
done
lemma ISDIData_HSTATES: shows "(HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or>
  HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or>
  HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or>
  HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) = (HSTATE MAD T \<or> HSTATE MA T \<or> HSTATE MD T \<or> HSTATE ModifiedM T)"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
apply simp
apply simp
apply simp
done
lemma ISDIData_nextSnoopIs: shows "nextSnoopIs  X T i = nextSnoopIs X ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) i"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
apply simp
apply simp
apply simp
done
lemma ISDIData_nextStore_otherside: shows "nextStore T 1 = nextStore ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
apply simp
apply simp
apply simp
done
lemma nextGOPending_DeviceISDIData: "nextGOPending (  T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ] ) i = nextGOPending T i"
apply(case_tac i)
  
   apply (metis nextGOPending_General_rule_4_0)
  
  by (smt (verit) INVALID_ROW_def LOAD_COL_def MEM_I_ROW_def MEM_RDS_COL_def One_nat_def SnoopType.size_gen(1)
      nat.distinct(1) nextGOPending_General_rule_4_1 nextGOPending_def nextGOPending_various_forms3
      nextGOPending_various_forms4)


lemma nextLoad_DeviceISDIData: "nextLoad (  T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ] ) 1 = nextLoad T 1"
using ISDIData_nextLoad
by presburger

(* ========================================= *)
(* Content from FixISDSnpInvFilled.thy *)
(* Lines 1-127 extracted *)
(* ========================================= *)

lemma ISDSnpInv_ModifiedM_aux2: shows " reqs1 T = reqs1 ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi])"
apply(case_tac i)
by simp+
lemma HSTATE_invariant_ModifiedSnpInv: shows "HSTATE X T = HSTATE X ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi])"
using hstate_invariants(12) hstate_invariants(2) hstate_invariants(24) hstate_invariants(7) hstate_invariants(9)
by presburger
lemma ISDSnpInv'_reqs2_invariant1_aux1: shows "reqs2 T = reqs2 ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi])"
apply(case_tac i)
by simp+
lemma ISDSnpInv'_snps2_invariant1_aux1: shows "snps2 T = snps2 ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [0 -=snp ] [ i s= mesi])"
apply(case_tac i)
by simp+
lemma ISDSnpInv'_snpresps2_invariant1_aux2: shows "snpresps2 T = snpresps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [i -=snp ] [ i s= mesi])"
apply(case_tac i)
by simp+
lemma ISDSnpInv'_snps2_invariant1 : shows "((snps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [0 -=snp ] [ i s= mesi]) \<noteq> [] \<longrightarrow>
   snpresps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [0 -=snp ] [ i s= mesi]) = []) \<and>
  (snpresps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [0 -=snp ] [ i s= mesi]) \<noteq> [] \<longrightarrow>
   snps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [0 -=snp ] [ i s= mesi]) = [])) = ((snps2 T \<noteq> [] \<longrightarrow> snpresps2 T = []) \<and> (snpresps2 T \<noteq> [] \<longrightarrow> snps2 T = []))"
apply(case_tac i)
using ISDSnpInv'_snps2_invariant1_aux1 ISDSnpInv'_snpresps2_invariant1_aux2
apply presburger
by simp
lemma ISDSnpInv'_reqresps2_invariant: shows 
  "reqresps2 ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi]) = reqresps2 T"
apply(case_tac i)
by simp+
lemma ISDSnpInv'_snoopGORules: shows  "
((snpresps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [i -=snp ] [ i s= mesi]) \<noteq> [] \<longrightarrow> 
  reqresps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [i -=snp ] [ i s= mesi]) = []) \<and> 
(reqresps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [i -=snp ] [ i s= mesi]) \<noteq> [] \<longrightarrow> 
  snpresps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [i -=snp ] [ i s= mesi]) = [])) = (
(snpresps2 T \<noteq> [] \<longrightarrow> reqresps2 T = []) \<and> (reqresps2 T \<noteq> [] \<longrightarrow> snpresps2 T = []))"
apply(subgoal_tac "snpresps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [i -=snp ] [ i s= mesi]) = snpresps2 T")
apply(subgoal_tac "reqresps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [i -=snp ] [ i s= mesi]) = reqresps2 T")
apply simp
apply(case_tac i)
apply simp
apply simp
apply(case_tac i)
by simp+
lemma ISDSnpInv'_reqresps_irrelevant1: shows 
  "reqresps1 ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi]) = reqresps1 T"
apply(case_tac i)
by simp+
lemma ISDSnpInv'_dthdatas1_aux: shows 
  "dthdatas1 (   T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp rtype tid] [0 -=snp ] [ 0 s= Invalid] ) = dthdatas1 T"
by simp
lemma ISDSnpInv'_dthdatas2: shows 
  "dthdatas2 ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi]) = dthdatas2 T"
apply(case_tac i)
by simp+
lemma ISDSnpInv'_htddatas1: shows 
  "htddatas1 ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi]) = htddatas1 T"
apply(case_tac i)
by simp+
lemma ISDSnpInv'_htddatas2: shows 
  "htddatas2 ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi]) = htddatas2 T"
apply(case_tac i)
by simp+
lemma ISDSnpInv_C_msg_not_half: shows "X \<noteq> Y \<Longrightarrow> nextReqIs z ( T [ i s= X]) i \<longrightarrow> \<not> CSTATE Y ( T [ i s= X]) i"
apply(case_tac i)
by simp+
lemma ISDSnpInv_nextReqIs: shows "nextReqIs z T j = nextReqIs z ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp u w] [i -=snp ] [ i s= mesi]) j"
apply(case_tac i)
by simp+
lemma ISDSnpInv_nextGOPendingIs: shows "nextGOPendingIs gotype T i = nextGOPendingIs gotype ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi]) i"
using ISDSnpInv'_reqresps2_invariant ISDSnpInv'_reqresps_irrelevant1 nextGOPendingIs_def
by presburger
lemma ISDSnpInv_CSTATE: shows "CSTATE mesi T 1 = CSTATE mesi (T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp rtype tid] [0 -=snp ] [ 0 s= Invalid]) 1"
apply simp
done
lemma ISDSnpInv_nextEvict: shows "nextEvict T j = nextEvict  ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi]) j"
apply(case_tac i)
by simp+
lemma ISDSnpInv_nextStore: shows "nextStore T j = nextStore  ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi]) j"
apply(case_tac i)
by simp+
lemma ISDSnpInv_nextSnoopIs_otherside: shows "nextSnoopIs X T 1 = nextSnoopIs X  (T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp rtype tid] [0 -=snp ] [ 0 s= Invalid]) 1"
apply simp
done
lemma snpresps1_ISDSnpInv'_aux1: shows "snpresps1 T = snpresps1 (T [i -=snp ] [ i s= X])"
apply(case_tac i)
apply simp+
done
lemma ISDSnpInv'_MA: assumes "SWMR_state_machine T \<and>  CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0" 
  shows "HSTATE MA ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi])"
apply(subgoal_tac "HSTATE MA T")
apply(subgoal_tac "HSTATE MA ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi])")
apply blast
using HSTATE_invariant_ModifiedSnpInv
apply presburger
apply(insert assms)
apply(elim conjE)
unfolding SWMR_state_machine_def
apply(elim conjE)
apply presburger
done
lemma snps1_ISDSnpInv: shows " length (snps1 T) \<le> 1 \<Longrightarrow> \<not>nextSnoopPending ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [0 -=snp ] [ 0 s= mesi]) 0"
apply(case_tac "snps1 T")
apply simp
apply simp
done
lemma nextGOPending_DeviceISDSnpInv: "nextGOPending ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi]) j = nextGOPending T j"
apply(case_tac j)
apply(case_tac i)
apply simp+
apply(case_tac i)
apply simp+
done
lemma nextLoad_DeviceISDSnpInv: "nextLoad ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi]) j = nextLoad T j"
apply(case_tac j)
apply(case_tac i)
apply simp+
apply(case_tac i)
apply simp+
done
lemma CSTATE_d2hd: shows " CSTATE X ( T [ devi +=d2hd msg  ]) i = CSTATE X T i"
apply(case_tac i)
apply(case_tac devi)
apply simp+
apply(case_tac devi)
apply simp+
done

(* ========================================= *)
(* Content from FixMADDataFilled.thy *)
(* Lines 1-140 extracted *)
(* ========================================= *)

lemma nextHTDDataPending_real_MADData: shows "nextHTDDataPending T 0 = nextHTDDataPending ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) 0"
by simp
lemma HostMADData_nextLoad: shows "nextLoad T 1 = nextLoad ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) 1"
by simp
lemma HostMADData'_devcache_invariant1: shows "(CLEntry.block_state (devcache1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]))) = CLEntry.block_state (devcache1 T)"
by simp+
lemma HostMADData'_devcache_invariant2: shows "(CLEntry.block_state (devcache2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]))) = CLEntry.block_state (devcache2 T)"
by simp+
lemma HostMADData'_CSTATE_invariant1: shows "CSTATE X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) 0 = CSTATE X T 0"
by simp
lemma HostMADData'_CSTATE_invariant2: shows "CSTATE X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) 1 = CSTATE X T 1"
by simp
lemma snps2_HostMADData: shows "htddatas2 T = [] \<Longrightarrow> length (htddatas2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ])) \<le> 1"
apply(subgoal_tac "length (htddatas2 (  T [ Dev2 +=h2dd hmsg])) = 1")
apply(subgoal_tac "htddatas2  (  T [ Dev2 +=h2dd hmsg]) = htddatas2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ])")
apply (metis le_numeral_extra(4))
by simp +
lemma snps1_HostMADData: shows "snps1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_HostMADData: shows "reqs2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma reqs1_HostMADData: shows "reqs1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) = reqs1 T"
by simp
lemma nextSnoopIs_HostMADData: shows "nextSnoopIs X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) i = nextSnoopIs X T i"
by simp
lemma snpresps2_HostMADData: shows "snpresps2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_HostMADData: shows "snpresps1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) = snpresps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_HostMADData: shows "reqresps2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostMADData: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ])) \<le> 1"
by simp
lemma reqresps1_HostMADData2: shows "reqresps1 T =  (reqresps1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]))"
by simp
lemma dthdatas1_HostMADData_aux: shows "length (dthdatas1 T) \<le> 1 \<Longrightarrow> (dthdatas1 (T [ Dev1 -=d2hdHead ])) = []"
apply(case_tac "dthdatas1 T")
by simp+
lemma dthdatas1_HostMADData: shows "length (dthdatas1 T) \<le> 1 \<Longrightarrow> dthdatas1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) =[]"
apply(subgoal_tac "dthdatas1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA]) = dthdatas1 T")
apply(subgoal_tac "length (dthdatas1 (( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA]))) \<le> 1")
using dthdatas1_HostMADData_aux
apply presburger
by simp+
lemma dthdatas2_HostMADData: shows "dthdatas2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_HostMADData: shows "htddatas1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) = htddatas1 T"
apply simp
done
lemma htddatas2_HostMADData: shows "htddatas2 T = [] \<Longrightarrow> length (htddatas2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ])) \<le> 1"
apply simp
done
lemma reqresps1_HostMADData_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostMADData_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostMADData_invariant: shows"nextEvict T 0 = nextEvict ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) 0"
by simp
lemma nextReqIs_HostMADData_IMAD_invariant2: shows 
  "nextReqIs X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) 1 = nextReqIs X T 1"
by simp
lemma nextReqIs_HostMADData_IMAD_invariant1: shows 
  "nextReqIs X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) 0 = nextReqIs X T 0"
by simp
lemma CSTATE_HostMADData_otherside_invariant2: shows
" CSTATE X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostMADData_otherside_invariant3: shows
" CSTATE X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) 0 = CSTATE X T 0"
by simp
lemma HostMADData_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) 1 = nextGOPendingIs X T 1"
by simp
lemma HostMADData_nextEvict_otherside: shows 
"nextEvict  ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) 1 = nextEvict T 1"
by simp
lemma HostMADData_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostMADData_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostMADData_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) 0 = nextSnpRespIs X T 0"
by simp
lemma HostMADData_HSTATE: shows "HSTATE MA ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) "
by simp
lemma nextStore_HostMADData: shows "nextStore T = nextStore ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ])"
unfolding nextStore_def
by simp
lemma nextLoad_HostMADData: shows "nextLoad T = nextLoad ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ])"
unfolding nextLoad_def
by simp
lemma HostMADData': shows "reqs1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) = reqs1 T"
by simp
lemma HostMADData_empty_reqs1_aux: shows " reqs1 T = reqs1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD])"
by simp
lemma reqresps2_HostMADData_remains: shows "reqresps2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) = reqresps2 T"
by simp
lemma HostMADData_one_msg_htddatas1: shows "htddatas1 T = (htddatas1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]))"
by simp+
lemma HostMADData_nextGOPending: shows "nextGOPending T i = nextGOPending (T [ 1 +=snp SnpData txid] [5 sHost= SAD] [ 0 -=req]) i"
by simp
lemma HostMADData_htddatas2_aux: shows "htddatas2 T = [] \<Longrightarrow> length (htddatas2 (T [Dev2 +=h2dd msg])) \<le> 1"
apply simp
done
lemma nextGOPending_HostMADData: "nextGOPending ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) i = nextGOPending T i"
apply(case_tac i)
apply simp+
done

(* ========================================= *)
(* Content from FixMADRspIFwdMFilled.thy *)
(* Lines 1-130 extracted *)
(* ========================================= *)

lemma HostMADRspIFwdM'_CSTATE_invariant1: shows "CSTATE X ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ]) 0 = CSTATE X T 0"
by simp
lemma HostMADRspIFwdM'_CSTATE_invariant2: shows "CSTATE X ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ]) 1 = CSTATE X T 1"
by simp
lemma nextLoad_HostMADRspIFwdM: "nextLoad ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ]) i = nextLoad T i"
apply(case_tac i)
apply simp+
done
lemma nextGOPending_HostMADRspIFwdM: "nextGOPending ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ]) 0 = nextGOPending T 0"
apply simp
done
lemma HostMADRspIFwdM'_devcache_invariant1: shows "(CLEntry.block_state (devcache1 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ]))) = CLEntry.block_state (devcache1 T)"
by simp
lemma HostMADRspIFwdM'_devcache_invariant2: shows "(CLEntry.block_state (devcache2 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ]))) = CLEntry.block_state (devcache2 T)"
by simp
lemma HostMADRspIFwdM_nextLoad: shows "nextLoad T 1 = nextLoad ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ]) 1"
by simp
lemma snps2_HostMADRspIFwdM: shows "reqresps2 T = [] \<Longrightarrow> length (reqresps2 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ])) \<le> 1"
apply(subgoal_tac "length (reqresps2 (  T [ 1 +=reqresp GO Modified txid])) = 1")
apply(subgoal_tac "reqresps2  (  T [ 1 +=reqresp GO Modified txid]) = reqresps2 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ])")
apply (metis le_numeral_extra(4))
by simp+
lemma snps1_HostMADRspIFwdM: shows "snps1 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_HostMADRspIFwdM: shows "reqs2 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma reqs1_HostMADRspIFwdM: shows "reqs1 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ]) = reqs1 T"
by simp
lemma nextSnoopIs_HostMADRspIFwdM: shows "nextSnoopIs X ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ]) i = nextSnoopIs X T i"
by simp
lemma snpresps2_HostMADRspIFwdM: shows "snpresps2 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostMADRspIFwdM: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ])) \<le> 1"
by simp
lemma reqresps1_HostMADRspIFwdM2: shows "reqresps1 T =  (reqresps1 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ]))"
by simp
lemma dthdatas1_HostMADRspIFwdM_aux: shows "length (snpresps1 T) \<le> 1 \<Longrightarrow> (snpresps1 (T [ 0 -=snpresp ])) = []"
using emptied_snpresps_aux1
by auto
lemma dthdatas1_HostMADRspIFwdM: shows "length (snpresps1 T) \<le> 1 \<Longrightarrow> snpresps1 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ]) = []"
apply(subgoal_tac "snpresps1 ( T   [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD]) = snpresps1 T")
apply(subgoal_tac "length (snpresps1 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD])) \<le> 1")
using dthdatas1_HostMADRspIFwdM_aux
apply blast
by simp+
lemma dthdatas2_HostMADRspIFwdM: shows "dthdatas2 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_HostMADRspIFwdM: shows "htddatas1 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ]) = htddatas1 T"
apply simp
done
lemma htddatas2_HostMADRspIFwdM: shows "htddatas2 T = [] \<Longrightarrow> length (htddatas2 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ])) \<le> 1"
apply simp
done
lemma reqresps1_HostMADRspIFwdM_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostMADRspIFwdM_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostMADRspIFwdM_invariant: shows"nextEvict T 0 = nextEvict ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ]) 0"
by simp
lemma nextReqIs_HostMADRspIFwdM_IMAD_invariant2: shows 
  "nextReqIs X ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ]) 1 = nextReqIs X T 1"
by simp
lemma nextReqIs_HostMADRspIFwdM_IMAD_invariant1: shows 
  "nextReqIs X ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ]) 0 = nextReqIs X T 0"
by simp
lemma CSTATE_HostMADRspIFwdM_otherside_invariant2: shows
" CSTATE X ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostMADRspIFwdM_otherside_invariant3: shows
" CSTATE X ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ]) 0 = CSTATE X T 0"
by simp
lemma HostMADRspIFwdM_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ]) 0 = nextGOPendingIs X T 0"
by simp
lemma HostMADRspIFwdM_nextEvict_otherside: shows 
"nextEvict  ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ]) 1 = nextEvict T 1"
by simp
lemma HostMADRspIFwdM_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostMADRspIFwdM_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostMADRspIFwdM_HSTATE: shows "HSTATE MD ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ]) "
by simp
lemma nextStore_HostMADRspIFwdM: shows "nextStore T = nextStore ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ])"
unfolding nextStore_def
by simp
lemma nextLoad_HostMADRspIFwdM1: shows "nextLoad T = nextLoad ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ])"
unfolding nextLoad_def
by simp
lemma HostMADRspIFwdM': shows "reqs1 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ]) = reqs1 T"
by simp
lemma HostMADRspIFwdM_empty_reqs1_aux: shows " reqs1 T = reqs1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD])"
by simp
lemma HostMADRspIFwdM_one_msg_htddatas1: shows "htddatas1 T = (htddatas1 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= MD] [ 0 -=snpresp  ]))"
by simp+
lemma HostMADRspIFwdM_nextGOPending: shows "nextGOPending T i = nextGOPending (T [ 1 +=snp SnpData txid] [5 sHost= SAD] [ 0 -=req]) i"
by simp
lemma HostMADRspIFwdM_htddatas2_aux: shows "htddatas2 T = [] \<Longrightarrow> length (htddatas2 (T [Dev2 +=h2dd msg])) \<le> 1"
apply simp
done

(* ========================================= *)
(* Content from FixMARspIFwdMFilled.thy *)
(* Lines 1-130 extracted *)
(* ========================================= *)

lemma HostMARspIFwdM'_CSTATE_invariant1: shows "CSTATE X ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 0 = CSTATE X T 0"
by simp
lemma HostMARspIFwdM'_CSTATE_invariant2: shows "CSTATE X ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 1 = CSTATE X T 1"
by simp
lemma nextLoad_HostMARspIFwdM: "nextLoad (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ] ) i = nextLoad T i"
apply(case_tac i)
apply simp+
done
lemma nextGOPending_HostMARspIFwdM: "nextGOPending (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ] ) 0 = nextGOPending T 0"
apply simp
done
lemma HostMARspIFwdM'_devcache_invariant1: shows "(CLEntry.block_state (devcache1 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]))) = CLEntry.block_state (devcache1 T)"
by simp
lemma HostMARspIFwdM'_devcache_invariant2: shows "(CLEntry.block_state (devcache2 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]))) = CLEntry.block_state (devcache2 T)"
by simp
lemma HostMARspIFwdM_nextLoad: shows "nextLoad T 1 = nextLoad ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 1"
by simp
lemma snps2_HostMARspIFwdM: shows "reqresps2 T = [] \<Longrightarrow> length (reqresps2 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ])) \<le> 1"
apply(subgoal_tac "length (reqresps2 (  T [ 1 +=reqresp GO Modified txid])) = 1")
apply(subgoal_tac "reqresps2  (  T [ 1 +=reqresp GO Modified txid]) = reqresps2 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ])")
apply (metis le_numeral_extra(4))
by simp+
lemma snps1_HostMARspIFwdM: shows "snps1 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_HostMARspIFwdM: shows "reqs2 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma reqs1_HostMARspIFwdM: shows "reqs1 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) = reqs1 T"
by simp
lemma nextSnoopIs_HostMARspIFwdM: shows "nextSnoopIs X ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) i = nextSnoopIs X T i"
by simp
lemma snpresps2_HostMARspIFwdM: shows "snpresps2 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostMARspIFwdM: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ])) \<le> 1"
by simp
lemma reqresps1_HostMARspIFwdM2: shows "reqresps1 T =  (reqresps1 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]))"
by simp
lemma dthdatas1_HostMARspIFwdM_aux: shows "length (snpresps1 T) \<le> 1 \<Longrightarrow> (snpresps1 (T [ 0 -=snpresp ])) = []"
using emptied_snpresps_aux1
by auto
lemma dthdatas1_HostMARspIFwdM: shows "length (snpresps1 T) \<le> 1 \<Longrightarrow> snpresps1 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) = []"
apply(subgoal_tac "snpresps1 ( T   [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM]) = snpresps1 T")
apply(subgoal_tac "length (snpresps1 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM])) \<le> 1")
using dthdatas1_HostMARspIFwdM_aux
apply blast
by simp+
lemma dthdatas2_HostMARspIFwdM: shows "dthdatas2 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_HostMARspIFwdM: shows "htddatas1 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) = htddatas1 T"
apply simp
done
lemma htddatas2_HostMARspIFwdM: shows "htddatas2 T = [] \<Longrightarrow> length (htddatas2 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ])) \<le> 1"
apply simp
done
lemma reqresps1_HostMARspIFwdM_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostMARspIFwdM_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostMARspIFwdM_invariant: shows"nextEvict T 0 = nextEvict ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 0"
by simp
lemma nextReqIs_HostMARspIFwdM_IMAD_invariant2: shows 
  "nextReqIs X ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 1 = nextReqIs X T 1"
by simp
lemma nextReqIs_HostMARspIFwdM_IMAD_invariant1: shows 
  "nextReqIs X ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 0 = nextReqIs X T 0"
by simp
lemma CSTATE_HostMARspIFwdM_otherside_invariant2: shows
" CSTATE X ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostMARspIFwdM_otherside_invariant3: shows
" CSTATE X ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 0 = CSTATE X T 0"
by simp
lemma HostMARspIFwdM_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 0 = nextGOPendingIs X T 0"
by simp
lemma HostMARspIFwdM_nextEvict_otherside: shows 
"nextEvict  ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 1 = nextEvict T 1"
by simp
lemma HostMARspIFwdM_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostMARspIFwdM_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostMARspIFwdM_HSTATE: shows "HSTATE ModifiedM ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) "
by simp
lemma nextStore_HostMARspIFwdM: shows "nextStore T = nextStore ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ])"
unfolding nextStore_def
by simp
lemma nextLoad_HostMARspIFwdM1: shows "nextLoad T = nextLoad ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ])"
unfolding nextLoad_def
by simp
lemma HostMARspIFwdM': shows "reqs1 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) = reqs1 T"
by simp
lemma HostMARspIFwdM_empty_reqs1_aux: shows " reqs1 T = reqs1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD])"
by simp
lemma HostMARspIFwdM_one_msg_htddatas1: shows "htddatas1 T = (htddatas1 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]))"
by simp+
lemma HostMARspIFwdM_nextGOPending: shows "nextGOPending T i = nextGOPending (T [ 1 +=snp SnpData txid] [5 sHost= SAD] [ 0 -=req]) i"
by simp
lemma HostMARspIFwdM_htddatas2_aux: shows "htddatas2 T = [] \<Longrightarrow> length (htddatas2 (T [Dev2 +=h2dd msg])) \<le> 1"
apply simp
done

(* ========================================= *)
(* Content from FixMARspIHitSEFilled.thy *)
(* Lines 1-133 extracted *)
(* ========================================= *)

lemma HostMARspIHitSE'_CSTATE_invariant1: shows "CSTATE X ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 0 = CSTATE X T 0"
by simp
lemma HostMARspIHitSE'_CSTATE_invariant2: shows "CSTATE X ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 1 = CSTATE X T 1"
by simp
lemma nextLoad_HostMARspIHitSE: "nextLoad ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ] ) i = nextLoad T i"
apply(case_tac i)
apply simp+
done
lemma nextGOPending_HostMARspIHitSE: "nextGOPending ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ] ) 0 = nextGOPending T 0"
apply simp
done
lemma HostMARspIHitSE'_devcache_invariant1: shows "(CLEntry.block_state (devcache1 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]))) = CLEntry.block_state (devcache1 T)"
by simp
lemma HostMARspIHitSE'_devcache_invariant2: shows "(CLEntry.block_state (devcache2 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]))) = CLEntry.block_state (devcache2 T)"
by simp
lemma HostMARspIHitSE_nextLoad: shows "nextLoad T 1 = nextLoad ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 1"
by simp
lemma snps2_HostMARspIHitSE: shows "reqresps2 T = [] \<Longrightarrow> length (reqresps2 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ])) \<le> 1"
apply(subgoal_tac "length (reqresps2 (  T [ 1 +=reqresp GO Modified txid])) = 1")
apply(subgoal_tac "reqresps2  (  T [ 1 +=reqresp GO Modified txid]) = reqresps2 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ])")
apply (metis le_numeral_extra(4))
by simp+
lemma snps1_HostMARspIHitSE: shows "snps1 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_HostMARspIHitSE: shows "reqs2 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma reqs1_HostMARspIHitSE: shows "reqs1 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) = reqs1 T"
by simp
lemma nextSnoopIs_HostMARspIHitSE: shows "nextSnoopIs X ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) i = nextSnoopIs X T i"
by simp
lemma snpresps2_HostMARspIHitSE: shows "snpresps2 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostMARspIHitSE: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ])) \<le> 1"
by simp
lemma reqresps1_HostMARspIHitSE2: shows "reqresps1 T =  (reqresps1 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]))"
by simp
lemma dthdatas1_HostMARspIHitSE_aux: shows "length (snpresps1 T) \<le> 1 \<Longrightarrow> (snpresps1 (T [ 0 -=snpresp ])) = []"
using emptied_snpresps_aux1
by auto
lemma dthdatas1_HostMARspIHitSE: shows "length (snpresps1 T) \<le> 1 \<Longrightarrow> snpresps1 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) = []"
apply(subgoal_tac "snpresps1 ( T   [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM]) = snpresps1 T")
apply(subgoal_tac "length (snpresps1 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM])) \<le> 1")
using dthdatas1_HostMARspIHitSE_aux
apply blast
by simp+
lemma dthdatas2_HostMARspIHitSE: shows "dthdatas2 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_HostMARspIHitSE: shows "htddatas1 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) = htddatas1 T"
apply simp
done
lemma htddatas2_HostMARspIHitSE: shows "htddatas2 T = [] \<Longrightarrow> length (htddatas2 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ])) \<le> 1"
apply simp
done
lemma reqresps1_HostMARspIHitSE_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostMARspIHitSE_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostMARspIHitSE_invariant: shows"nextEvict T 0 = nextEvict ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 0"
by simp
lemma nextReqIs_HostMARspIHitSE_IMAD_invariant2: shows 
  "nextReqIs X ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 1 = nextReqIs X T 1"
by simp
lemma nextReqIs_HostMARspIHitSE_IMAD_invariant1: shows 
  "nextReqIs X ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 0 = nextReqIs X T 0"
by simp
lemma CSTATE_HostMARspIHitSE_otherside_invariant2: shows
" CSTATE X ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostMARspIHitSE_otherside_invariant3: shows
" CSTATE X ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 0 = CSTATE X T 0"
by simp
lemma HostMARspIHitSE_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 0 = nextGOPendingIs X T 0"
by simp
lemma HostMARspIHitSE_nextEvict_otherside: shows 
"nextEvict  ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 1 = nextEvict T 1"
by simp
lemma HostMARspIHitSE_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostMARspIHitSE_nextHTDDataPending_real: shows 
"nextHTDDataPending  ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) i = nextHTDDataPending T i"
by simp
lemma HostMARspIHitSE_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostMARspIHitSE_HSTATE: shows "HSTATE ModifiedM ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) "
by simp
lemma nextStore_HostMARspIHitSE: shows "nextStore T = nextStore ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ])"
unfolding nextStore_def
by simp
lemma nextLoad_HostMARspIHitSE1: shows "nextLoad T = nextLoad ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ])"
unfolding nextLoad_def
by simp
lemma HostMARspIHitSE': shows "reqs1 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) = reqs1 T"
by simp
lemma HostMARspIHitSE_empty_reqs1_aux: shows " reqs1 T = reqs1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD])"
by simp
lemma HostMARspIHitSE_one_msg_htddatas1: shows "htddatas1 T = (htddatas1 ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]))"
by simp+
lemma HostMARspIHitSE_nextGOPending: shows "nextGOPending T i = nextGOPending (T [ 1 +=snp SnpData txid] [5 sHost= SAD] [ 0 -=req]) i"
by simp
lemma HostMARspIHitSE_htddatas2_aux: shows "htddatas2 T = [] \<Longrightarrow> length (htddatas2 (T [Dev2 +=h2dd msg])) \<le> 1"
apply simp
done

(* ========================================= *)
(* Content from FixMBDataFilled.thy *)
(* Lines 1-123 extracted *)
(* ========================================= *)

lemma HostMBData'_devcache_invariant1: shows "(CLEntry.block_state (devcache1 ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]))) = CLEntry.block_state (devcache1 T)"
by simp
lemma HostMBData'_devcache_invariant2: shows "(CLEntry.block_state (devcache2 ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]))) = CLEntry.block_state (devcache2 T)"
by simp
lemma HostMBData_nextLoad: shows "nextLoad T 1 = nextLoad ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) 1"
by simp
lemma snps1_HostMBData: shows "snps1 ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) = snps1 T"
by simp
lemma snps2_HostMBData: shows "snps2 ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) = snps2 T"
by simp
lemma reqs2_HostMBData: shows "reqs2 ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) = reqs2 T"
by simp
lemma reqs1_HostMBData: shows "reqs1 ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) = reqs1 T"
by simp
lemma htddatas2_HostMBData: shows "htddatas2 ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) = htddatas2 T"
by simp
lemma nextSnoopIs_HostMBData: shows "nextSnoopIs X ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) i = nextSnoopIs X T i"
by simp
lemma snpresps2_HostMBData: shows "snpresps2 ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) = snpresps2 T"
by simp
lemma snpresps1_HostMBData: shows "snpresps1 ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) = snpresps1 T"
by simp
lemma reqresps2_HostMBData: shows "reqresps2 ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) = reqresps2 T"
by simp
lemma reqresps1_HostMBData: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ])) \<le> 1"
by simp
lemma reqresps1_HostMBData2: shows "reqresps1 T =  (reqresps1 ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]))"
by simp
lemma dthdatas1_HostMBData_aux: shows "length (dthdatas1 T) \<le> 1 \<Longrightarrow> (dthdatas1 (T [ Dev1 -=d2hdHead ])) = []"
apply simp
apply(case_tac "dthdatas1 T")
by simp+
lemma dthdatas1_HostMBData: shows "length (dthdatas1 T) \<le> 1 \<Longrightarrow> dthdatas1 ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) = []"
apply(subgoal_tac "dthdatas1 ( T [ 5 sHost= ModifiedM] ) = dthdatas1 T")
apply(subgoal_tac "length (dthdatas1 ( T [ 5 sHost= ModifiedM] )) \<le> 1")
using dthdatas1_HostMBData_aux
apply metis
apply presburger
by simp
lemma dthdatas2_HostMBData: shows "dthdatas2 ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_HostMBData: shows "htddatas1 ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) = htddatas1 T"
apply simp
done
lemma reqresps1_HostMBData_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostMBData_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostMBData_invariant: shows"nextEvict T 0 = nextEvict ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) 0"
by simp
lemma nextReqIs_HostMBData_IMAD_invariant2: shows 
  "nextReqIs X ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) 1 = nextReqIs X T 1"
by simp
lemma nextReqIs_HostMBData_IMAD_invariant1: shows 
  "nextReqIs X ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) 0 = nextReqIs X T 0"
by simp
lemma CSTATE_HostMBData_otherside_invariant2: shows
" CSTATE X ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostMBData_otherside_invariant3: shows
" CSTATE X ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) 0 = CSTATE X T 0"
by simp
lemma HostMBData_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) i = nextGOPendingIs X T i"
by simp
lemma HostMBData_nextEvict_otherside: shows 
"nextEvict  ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) i = nextEvict T i"
by simp
lemma HostMBData_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostMBData_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostMBData_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) 0 = nextSnpRespIs X T 0"
by simp
lemma HostMBData_HSTATE: shows "HSTATE ModifiedM ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) "
by simp
lemma nextStore_HostMBData: shows "nextStore T = nextStore ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ])"
unfolding nextStore_def
by simp
lemma nextLoad_HostMBData: shows "nextLoad T = nextLoad ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ])"
unfolding nextLoad_def
by simp
lemma HostMBData_empty_reqs1_aux: shows " reqs1 T = reqs1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD])"
by simp
lemma HostMBData_one_msg_htddatas1: shows "htddatas1 T = (htddatas1 ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]))"
by simp+
lemma HostMBData_nextGOPending: shows "nextGOPending T i = nextGOPending ( T [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) i"
by simp
lemma HostMBData_htddatas2_aux: shows "htddatas2 T = [] \<Longrightarrow> length (htddatas2 (T [Dev2 +=h2dd msg])) \<le> 1"
apply simp
done
lemma nextGOPending_HostMBData: "nextGOPending (  T[ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ] ) i = nextGOPending T i"
apply(case_tac i)
apply simp+
done

(* ========================================= *)
(* Content from FixMDDataFilled.thy *)
(* Lines 1-140 extracted *)
(* ========================================= *)

lemma nextHTDDataPending_real_SDData: shows "nextHTDDataPending T 0 = nextHTDDataPending ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) 0"
by simp
lemma HostMDData_nextLoad: shows "nextLoad T 1 = nextLoad ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) 1"
by simp
lemma HostMDData'_devcache_invariant1: shows "(CLEntry.block_state (devcache1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]))) = CLEntry.block_state (devcache1 T)"
by simp+
lemma HostMDData'_devcache_invariant2: shows "(CLEntry.block_state (devcache2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]))) = CLEntry.block_state (devcache2 T)"
by simp+
lemma HostMDData'_CSTATE_invariant1: shows "CSTATE X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) 0 = CSTATE X T 0"
by simp
lemma HostMDData'_CSTATE_invariant2: shows "CSTATE X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) 1 = CSTATE X T 1"
by simp
lemma snps2_HostMDData: shows "htddatas2 T = [] \<Longrightarrow> length (htddatas2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ])) \<le> 1"
apply(subgoal_tac "length (htddatas2 (  T [ Dev2 +=h2dd hmsg])) = 1")
apply(subgoal_tac "htddatas2  (  T [ Dev2 +=h2dd hmsg]) = htddatas2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ])")
apply (metis le_numeral_extra(4))
by simp +
lemma snps1_HostMDData: shows "snps1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_HostMDData: shows "reqs2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma reqs1_HostMDData: shows "reqs1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) = reqs1 T"
by simp
lemma nextSnoopIs_HostMDData: shows "nextSnoopIs X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) i = nextSnoopIs X T i"
by simp
lemma snpresps2_HostMDData: shows "snpresps2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_HostMDData: shows "snpresps1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) = snpresps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_HostMDData: shows "reqresps2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostMDData: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ])) \<le> 1"
by simp
lemma reqresps1_HostMDData2: shows "reqresps1 T =  (reqresps1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]))"
by simp
lemma dthdatas1_HostMDData_aux: shows "length (dthdatas1 T) \<le> 1 \<Longrightarrow> (dthdatas1 (T [ Dev1 -=d2hdHead ])) = []"
apply(case_tac "dthdatas1 T")
by simp+
lemma dthdatas1_HostMDData: shows "length (dthdatas1 T) \<le> 1 \<Longrightarrow> dthdatas1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) =[]"
apply(subgoal_tac "dthdatas1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM]) = dthdatas1 T")
apply(subgoal_tac "length (dthdatas1 (( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM]))) \<le> 1")
using dthdatas1_HostMDData_aux
apply presburger
by simp+
lemma dthdatas2_HostMDData: shows "dthdatas2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_HostMDData: shows "htddatas1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) = htddatas1 T"
apply simp
done
lemma htddatas2_HostMDData: shows "htddatas2 T = [] \<Longrightarrow> length (htddatas2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ])) \<le> 1"
apply simp
done
lemma reqresps1_HostMDData_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostMDData_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostMDData_invariant: shows"nextEvict T 0 = nextEvict ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) 0"
by simp
lemma nextReqIs_HostMDData_IMAD_invariant2: shows 
  "nextReqIs X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) 1 = nextReqIs X T 1"
by simp
lemma nextReqIs_HostMDData_IMAD_invariant1: shows 
  "nextReqIs X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) 0 = nextReqIs X T 0"
by simp
lemma CSTATE_HostMDData_otherside_invariant2: shows
" CSTATE X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostMDData_otherside_invariant3: shows
" CSTATE X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) 0 = CSTATE X T 0"
by simp
lemma HostMDData_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) 1 = nextGOPendingIs X T 1"
by simp
lemma HostMDData_nextEvict_otherside: shows 
"nextEvict  ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) 1 = nextEvict T 1"
by simp
lemma HostMDData_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostMDData_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostMDData_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) 0 = nextSnpRespIs X T 0"
by simp
lemma HostMDData_HSTATE: shows "HSTATE ModifiedM ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) "
by simp
lemma nextStore_HostMDData: shows "nextStore T = nextStore ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ])"
unfolding nextStore_def
by simp
lemma nextLoad_HostMDData: shows "nextLoad T = nextLoad ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ])"
unfolding nextLoad_def
by simp
lemma HostMDData': shows "reqs1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) = reqs1 T"
by simp
lemma HostMDData_empty_reqs1_aux: shows " reqs1 T = reqs1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD])"
by simp
lemma reqresps2_HostMDData_remains: shows "reqresps2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) = reqresps2 T"
by simp
lemma HostMDData_one_msg_htddatas1: shows "htddatas1 T = (htddatas1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]))"
by simp+
lemma HostMDData_nextGOPending: shows "nextGOPending T i = nextGOPending (T [ 1 +=snp SnpData txid] [5 sHost= SAD] [ 0 -=req]) i"
by simp
lemma HostMDData_htddatas2_aux: shows "htddatas2 T = [] \<Longrightarrow> length (htddatas2 (T [Dev2 +=h2dd msg])) \<le> 1"
apply simp
done
lemma nextGOPending_HostMDData: "nextGOPending ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) i = nextGOPending T i"
apply(case_tac i)
apply simp+
done

(* ========================================= *)
(* Content from FixMIAGO_WritePullFilled.thy *)
(* Lines 1-205 extracted *)
(* ========================================= *)

lemma devcache1_MIAGO_WritePull_invariant_aux1: shows "CLEntry.block_state  (devcache1 T) = ISD \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ 0 -=reqresp ] )) \<noteq> Modified"
using MESI_State.distinct(7) devcache1_consume_reqresps1_invariant
by presburger
lemma devcache1_MIAGO_WritePull_invariant_aux: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ 0 -=reqresp ] [ 0 -=devd ])) \<noteq> Modified"
using devcache1_MIAGO_WritePull_invariant_aux1
by auto
lemma devcache1_MIAGO_WritePull_invariant: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T [ 0 :=dd msg ] [ 0 -=reqresp ] [ 0 -=devd ])) \<noteq> Modified"
apply(subgoal_tac "CLEntry.block_state  (devcache1 (T  [ 0 :=dd msg ])) = Shared")
using devcache1_MIAGO_WritePull_invariant_aux
apply blast
by simp
lemma nextEvict_MIAGO_WritePull_CSTATE_invariant: shows "nextEvict T 0 \<Longrightarrow> CSTATE Invalid ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd])  0"
apply simp
done
lemma nextStore_MIAGO_WritePull: shows "nextStore T i = nextStore  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd]) i"
apply simp
done
lemma nextEvict_MIAGO_WritePull_invariant: shows"nextEvict T 0 = nextEvict ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd]) 0"
by simp
lemma HSTATE_MIAGO_WritePull_invariant: shows "HSTATE X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = 
  HSTATE X T"
using hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) remove_instr_HSTATE
by presburger
lemma CSTATE_MIAGO_WritePull_IMAD_invariant: shows "nextEvict T 0 \<Longrightarrow>  CSTATE Invalid (T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
by simp+
lemma nextSnoopIs_MIAGO_WritePull: shows 
  "nextSnoopIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) i = nextSnoopIs X T i"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp
by simp+
lemma nextReqIs_MIAGO_WritePull_IMAD_invariant2: shows 
  "nextReqIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) i = nextReqIs X T i"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp
by simp+
lemma nextReqIs_MIAGO_WritePull_IMAD_invariant1: shows 
  "nextReqIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 = nextReqIs X T 0"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp
by simp+
lemma CSTATE_MIAGO_WritePull_otherside_invariant2: shows
" CSTATE X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 = CSTATE X T 1"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp
by simp+
lemma MIAGO_WritePull_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 = nextGOPendingIs X T 1"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp
by simp+
lemma MIAGO_WritePull_nextEvict_otherside: shows 
"nextEvict  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 = nextEvict T 1"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp
by simp+
lemma CSTATE_MIAGO_WritePull_otherside: shows "CSTATE X T 1 = CSTATE X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp
by simp+
lemma nextReqIs_MIAGO_WritePull: shows "nextReqIs X T i = nextReqIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) i"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp
by simp+
lemma MIAGO_WritePull_snps2:   " snps2  T  = snps2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd][ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma MIAGO_WritePull_snps1:   " snps1  T  = snps1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd][ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma MIAGO_WritePull_reqs1:   " reqs1  T  = reqs1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd][ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma MIAGO_WritePull_reqs2:   " reqs2  T  = reqs2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd][ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma MIAGO_WritePull_reqresps2:   " reqresps2  T  = reqresps2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd][ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma MIAGO_WritePull_snpresps1:   " snpresps1  T  = snpresps1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd][ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma MIAGO_WritePull_snpresps2:   " snpresps2  T  = snpresps2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd][ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma MIAGO_WritePull_dthdatas1:   " dthdatas1  T = [] \<Longrightarrow> 
  length (dthdatas1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd][ -=i 0])) \<le> 1"
apply (cases "program1 T")
apply simp
apply simp
done
lemma MIAGO_WritePull_dthdatas2:   " dthdatas2  T  = dthdatas2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd][ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma MIAGO_WritePull_htddatas1:   "htddatas1 T =  (htddatas1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd][ -=i 0]))"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
using Type1State.update_convs(12) Type1State.update_convs(2) Type1State.update_convs(8) change_state_def config_differ_dev_mapping_def config_differ_dthdata_def consumeReqresp_def device_perform_op_htddatas1
apply force
by simp+
lemma MIAGO_WritePull_htddatas2:   " htddatas2  T  = htddatas2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd][ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma MIAGO_WritePull_nextHTDDataPending: "nextHTDDataPending T i = 
  nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])  i"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp
by simp+
lemma MIAGO_nextGOPending_otherside: "nextGOPending T 1 = nextGOPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp
by simp+
find_theorems "_ \<and> _  \<Longrightarrow> _"
lemma MIAGO_WritePull_reqresps1_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp]) = []"
apply(cases "reqresps1 T")
by simp+
lemma MIAGO_WritePull_reqresps1_aux2: shows "reqresps1 T = reqresps1 ( T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp
apply simp
done
lemma nextGOPending_DeviceMIAGO_WritePull: "nextGOPending (  T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd][ -=i 0] ) 1 = nextGOPending T 1"
using MIAGO_nextGOPending_otherside
by blast
lemma nextLoad_DeviceMIAGO_WritePull: "nextLoad (  T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd][ -=i 0] ) 1 = nextLoad T 1"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp
apply simp
done

(* ========================================= *)
(* Content from FixMIASnpDataInvalidFilled.thy *)
(* Lines 1-105 extracted *)
(* ========================================= *)

lemma reqresps1_MIASnpDataInvalid: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 
(T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd])) \<le> 1"
by simp
lemma snps1_MIASnpDataInvalid: shows "length (snps1 T) \<le> 1 \<Longrightarrow> snps1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) = []"
apply(case_tac "snps1 T")
apply simp+
done
lemma reqs2_MIASnpDataInvalid: shows "reqs2 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_MIASnpDataInvalid: shows "snpresps2 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_MIASnpDataInvalid: shows "snpresps1 T = [] \<Longrightarrow> length (snpresps1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd])) \<le> 1"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_MIASnpDataInvalid: shows "reqresps2 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_MIASnpDataInvalid2: shows "reqresps1 T =  (reqresps1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]))"
by simp
lemma dthdatas1_MIASnpDataInvalid: shows "dthdatas1 T = [] \<Longrightarrow> length (dthdatas1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd])) \<le> 1"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_MIASnpDataInvalid: shows "dthdatas2 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_MIASnpDataInvalid: shows "htddatas1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) = htddatas1 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_MIASnpDataInvalid: shows "htddatas2 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_MIASnpDataInvalid_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_MIASnpDataInvalid_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_MIASnpDataInvalid_invariant: shows"nextEvict T 0 = nextEvict (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) 0"
by simp
lemma CSTATE_MIASnpDataInvalid_otherside_invariant2: shows
" CSTATE X (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_MIASnpDataInvalid_otherside_invariant3: shows
" CSTATE IIA (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) 0"
by simp
lemma MIASnpDataInvalid_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) 1 = nextGOPendingIs X T 1"
by simp
lemma MIASnpDataInvalid_nextEvict_otherside: shows 
"nextEvict  (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) 1 = nextEvict T 1"
by simp
lemma MIASnpDataInvalid_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) 1 = nextDTHDataPending T 1"
by simp
lemma MIASnpDataInvalid_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) 1 = nextSnpRespIs X T 1"
by simp
lemma MIASnpDataInvalid_nextHTDDataPending_sameside: shows 
"nextDTHDataPending  (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) 0 "
by simp
lemma MIASnpDataInvalid_nextSnpRespIs_sameside: shows 
"snpresps1 T = [] \<Longrightarrow> nextSnpRespIs RspIFwdM  (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) 0"
by simp
lemma MIASnpDataInvalid_empty_reqs1_aux: shows " reqs1 T = reqs1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD])"
by simp
lemma snps2_MIASnpDataInvalid: shows "snps2 (T [ 0 +=hostdata  txid] [ 5 sHost= MA]) = snps2 T"
by simp
lemma snps2_single_MIASnpDataInvalid: shows "snps2 T = [] \<Longrightarrow> length (snps2 (T [ 1 +=snp SnpInv txid])) \<le> 1 "
by simp
lemma snps2_MIASnpDataInvalid_aux1: shows "snps2 T = snps2 ( T [ 0 -=req])"
by simp
lemma snps2_MIASnpDataInvalid_aux2: shows "snps2 T = [] \<Longrightarrow> length (snps2  ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid] )) \<le> 1"
using snps2_MIASnpDataInvalid snps2_single_MIASnpDataInvalid
by presburger
lemma MIASnpDataInvalid_one_msg_htddatas1: shows "htddatas1 T = [] \<Longrightarrow> length (htddatas1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd])) \<le> 1"
by simp
lemma nextLoad_MIASnpDataInvalid: "nextLoad (  T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ] ) i = nextLoad T i"
apply(case_tac i)
apply simp+
done
lemma nextGOPending_MIASnpDataInvalid: "nextGOPending (  T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ] ) i = nextGOPending T i"
apply(case_tac i)
apply simp+
done

(* ========================================= *)
(* Content from FixMIASnpDataSharedFilled.thy *)
(* Lines 1-105 extracted *)
(* ========================================= *)

lemma reqresps1_MIASnpDataShared: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 
(T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd])) \<le> 1"
by simp
lemma snps1_MIASnpDataShared: shows "length (snps1 T) \<le> 1 \<Longrightarrow> snps1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd]) = []"
apply(case_tac "snps1 T")
apply simp+
done
lemma reqs2_MIASnpDataShared: shows "reqs2 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_MIASnpDataShared: shows "snpresps2 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_MIASnpDataShared: shows "snpresps1 T = [] \<Longrightarrow> length (snpresps1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd])) \<le> 1"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_MIASnpDataShared: shows "reqresps2 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_MIASnpDataShared2: shows "reqresps1 T =  (reqresps1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd]))"
by simp
lemma dthdatas1_MIASnpDataShared: shows "dthdatas1 T = [] \<Longrightarrow> length (dthdatas1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd])) \<le> 1"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_MIASnpDataShared: shows "dthdatas2 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_MIASnpDataShared: shows "htddatas1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd]) = htddatas1 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_MIASnpDataShared: shows "htddatas2 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_MIASnpDataShared_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_MIASnpDataShared_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_MIASnpDataShared_invariant: shows"nextEvict T 0 = nextEvict (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd]) 0"
by simp
lemma CSTATE_MIASnpDataShared_otherside_invariant2: shows
" CSTATE X (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_MIASnpDataShared_otherside_invariant3: shows
" CSTATE SIA (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd]) 0"
by simp
lemma MIASnpDataShared_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd]) 1 = nextGOPendingIs X T 1"
by simp
lemma MIASnpDataShared_nextEvict_otherside: shows 
"nextEvict  (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd]) 1 = nextEvict T 1"
by simp
lemma MIASnpDataShared_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd]) 1 = nextDTHDataPending T 1"
by simp
lemma MIASnpDataShared_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd]) 1 = nextSnpRespIs X T 1"
by simp
lemma MIASnpDataShared_nextHTDDataPending_sameside: shows 
"nextDTHDataPending  (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd]) 0 "
by simp
lemma MIASnpDataShared_nextSnpRespIs_sameside: shows 
"snpresps1 T = [] \<Longrightarrow> nextSnpRespIs RspSFwdM  (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd]) 0"
by simp
lemma MIASnpDataShared_empty_reqs1_aux: shows " reqs1 T = reqs1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD])"
by simp
lemma snps2_MIASnpDataShared: shows "snps2 (T [ 0 +=hostdata  txid] [ 5 sHost= MA]) = snps2 T"
by simp
lemma snps2_single_MIASnpDataShared: shows "snps2 T = [] \<Longrightarrow> length (snps2 (T [ 1 +=snp SnpInv txid])) \<le> 1 "
by simp
lemma snps2_MIASnpDataShared_aux1: shows "snps2 T = snps2 ( T [ 0 -=req])"
by simp
lemma snps2_MIASnpDataShared_aux2: shows "snps2 T = [] \<Longrightarrow> length (snps2  ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid] )) \<le> 1"
using snps2_MIASnpDataShared snps2_single_MIASnpDataShared
by presburger
lemma MIASnpDataShared_one_msg_htddatas1: shows "htddatas1 T = [] \<Longrightarrow> length (htddatas1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd])) \<le> 1"
by simp
lemma nextLoad_MIASnpDataShared: "nextLoad (  T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ] ) i = nextLoad T i"
apply(case_tac i)
apply simp+
done
lemma nextGOPending_MIASnpDataShared: "nextGOPending (  T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ] ) i = nextGOPending T i"
apply(case_tac i)
apply simp+
done

(* ========================================= *)
(* Content from FixMIASnpInvFilled.thy *)
(* Lines 1-105 extracted *)
(* ========================================= *)

lemma reqresps1_MIASnpInv: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 
(T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd])) \<le> 1"
by simp
lemma snps1_MIASnpInv: shows "length (snps1 T) \<le> 1 \<Longrightarrow> snps1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) = []"
apply(case_tac "snps1 T")
apply simp+
done
lemma reqs2_MIASnpInv: shows "reqs2 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_MIASnpInv: shows "snpresps2 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_MIASnpInv: shows "snpresps1 T = [] \<Longrightarrow> length (snpresps1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd])) \<le> 1"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_MIASnpInv: shows "reqresps2 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_MIASnpInv2: shows "reqresps1 T =  (reqresps1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]))"
by simp
lemma dthdatas1_MIASnpInv: shows "dthdatas1 T = [] \<Longrightarrow> length (dthdatas1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd])) \<le> 1"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_MIASnpInv: shows "dthdatas2 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_MIASnpInv: shows "htddatas1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) = htddatas1 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_MIASnpInv: shows "htddatas2 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_MIASnpInv_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_MIASnpInv_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_MIASnpInv_invariant: shows"nextEvict T 0 = nextEvict (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) 0"
by simp
lemma CSTATE_MIASnpInv_otherside_invariant2: shows
" CSTATE X (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_MIASnpInv_otherside_invariant3: shows
" CSTATE IIA (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) 0"
by simp
lemma MIASnpInv_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) 1 = nextGOPendingIs X T 1"
by simp
lemma MIASnpInv_nextEvict_otherside: shows 
"nextEvict  (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) 1 = nextEvict T 1"
by simp
lemma MIASnpInv_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) 1 = nextDTHDataPending T 1"
by simp
lemma MIASnpInv_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) 1 = nextSnpRespIs X T 1"
by simp
lemma MIASnpInv_nextHTDDataPending_sameside: shows 
"nextDTHDataPending  (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) 0 "
by simp
lemma MIASnpInv_nextSnpRespIs_sameside: shows 
"snpresps1 T = [] \<Longrightarrow> nextSnpRespIs RspIFwdM  (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) 0"
by simp
lemma MIASnpInv_empty_reqs1_aux: shows " reqs1 T = reqs1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD])"
by simp
lemma snps2_MIASnpInv: shows "snps2 (T [ 0 +=hostdata  txid] [ 5 sHost= MA]) = snps2 T"
by simp
lemma snps2_single_MIASnpInv: shows "snps2 T = [] \<Longrightarrow> length (snps2 (T [ 1 +=snp SnpInv txid])) \<le> 1 "
by simp
lemma snps2_MIASnpInv_aux1: shows "snps2 T = snps2 ( T [ 0 -=req])"
by simp
lemma snps2_MIASnpInv_aux2: shows "snps2 T = [] \<Longrightarrow> length (snps2  ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid] )) \<le> 1"
using snps2_MIASnpInv snps2_single_MIASnpInv
by presburger
lemma MIASnpInv_one_msg_htddatas1: shows "htddatas1 T = [] \<Longrightarrow> length (htddatas1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd])) \<le> 1"
by simp
lemma nextLoad_MIASnpInv: "nextLoad (  T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ] ) i = nextLoad T i"
apply(case_tac i)
apply simp+
done
lemma nextGOPending_MIASnpInv: "nextGOPending (  T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ] ) i = nextGOPending T i"
apply(case_tac i)
apply simp+
done

(* ========================================= *)
(* Content from FixModifiedDirtyEvictFilled.thy *)
(* Lines 1-115 extracted *)
(* ========================================= *)

lemma snps2_HostModified_DirtyEvict: shows "snps2 ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = snps2 T"
apply(case_tac "program1 T")
by simp+
lemma snps1_HostModified_DirtyEvict: shows "snps1 ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_HostModified_DirtyEvict: shows "reqs2 ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_HostModified_DirtyEvict: shows "snpresps2 ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_HostModified_DirtyEvict: shows "snpresps1 ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = snpresps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_HostModified_DirtyEvict: shows "reqresps2 ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostModified_DirtyEvict: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) \<le> 1"
by simp
lemma dthdatas1_HostModified_DirtyEvict: shows "dthdatas1 ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = dthdatas1 T"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_HostModified_DirtyEvict: shows "dthdatas2 ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_HostModified_DirtyEvict: shows "htddatas1 ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = htddatas1 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_HostModified_DirtyEvict: shows "htddatas2 ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostModified_DirtyEvict_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostModified_DirtyEvict_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostModified_DirtyEvict_invariant: shows"nextEvict T 0 = nextEvict ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
by simp
lemma nextReqIs_HostModified_DirtyEvict_IMAD_invariant2: shows 
  "nextReqIs X ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextReqIs X T 1"
by simp
lemma nextReqIs_HostModified_DirtyEvict_IMAD_invariant1: shows 
  "length (reqs1 T) \<le> 1 \<Longrightarrow> reqs1 ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply(cases "reqs1 T") apply simp+ done
lemma CSTATE_HostModified_DirtyEvict_otherside_invariant2: shows
" CSTATE X ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostModified_DirtyEvict_otherside_invariant3: shows
" CSTATE X ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 = CSTATE X T 0"
by simp
lemma HostModified_DirtyEvict_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextGOPendingIs X T 1"
by simp
lemma HostModified_DirtyEvict_nextEvict_otherside: shows 
"nextEvict  ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextEvict T 1"
by simp
lemma HostModified_DirtyEvict_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostModified_DirtyEvict_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostModified_DirtyEvict_nextDTHDataPending_sameside: shows 
"nextDTHDataPending  ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 = nextDTHDataPending T 0"
by simp
lemma HostModified_DirtyEvict_nextHTDDataPending_sameside: shows 
"nextHTDDataPending  ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 = nextHTDDataPending T 0"
by simp
lemma HostModified_DirtyEvict_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 = nextSnpRespIs X T 0"
by simp
lemma HostModified_DirtyEvict_HSTATE: shows "HSTATE ID ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) "
apply(case_tac "program1 T")
by simp+
lemma HostModified_DirtyEvict_nextLoad: shows "nextLoad ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) i = nextLoad T i"
apply(case_tac "program1 T")
by simp+
lemma HostModified_DirtyEvict': shows "reqs1 (T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid]) = reqs1 T"
by simp
lemma nextLoad_HostModifiedDirtyEvict: "nextLoad (  T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ] ) i = nextLoad T i"
apply(case_tac i) apply simp+ done
lemma nextGOPending_HostModifiedDirtyEvict: "nextGOPending (  T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ] ) 1 = nextGOPending T 1"
apply simp+
done

(* ========================================= *)
(* Content from FixModifiedDirtyEvictPreviousFilled.thy *)
(* Lines 1-115 extracted *)
(* ========================================= *)

lemma snps2_HostModified_DirtyEvictPrevious: shows "snps2 ( T [ 5 sHost= MB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = snps2 T"
apply(case_tac "program1 T")
by simp+
lemma snps1_HostModified_DirtyEvictPrevious: shows "snps1 ( T [ 5 sHost= MB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_HostModified_DirtyEvictPrevious: shows "reqs2 ( T [ 5 sHost= MB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_HostModified_DirtyEvictPrevious: shows "snpresps2 ( T [ 5 sHost= MB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_HostModified_DirtyEvictPrevious: shows "snpresps1 ( T [ 5 sHost= MB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = snpresps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_HostModified_DirtyEvictPrevious: shows "reqresps2 ( T [ 5 sHost= MB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostModified_DirtyEvictPrevious: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 ( T [ 5 sHost= MB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) \<le> 1"
by simp
lemma dthdatas1_HostModified_DirtyEvictPrevious: shows "dthdatas1 ( T [ 5 sHost= MB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = dthdatas1 T"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_HostModified_DirtyEvictPrevious: shows "dthdatas2 ( T [ 5 sHost= MB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_HostModified_DirtyEvictPrevious: shows "htddatas1 ( T [ 5 sHost= MB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = htddatas1 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_HostModified_DirtyEvictPrevious: shows "htddatas2 ( T [ 5 sHost= MB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostModified_DirtyEvictPrevious_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostModified_DirtyEvictPrevious_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostModified_DirtyEvictPrevious_invariant: shows"nextEvict T 0 = nextEvict ( T [ 5 sHost= MB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
by simp
lemma nextReqIs_HostModified_DirtyEvictPrevious_IMAD_invariant2: shows 
  "nextReqIs X ( T [ 5 sHost= MB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextReqIs X T 1"
by simp
lemma nextReqIs_HostModified_DirtyEvictPrevious_IMAD_invariant1: shows 
  "length (reqs1 T) \<le> 1 \<Longrightarrow> reqs1 ( T [ 5 sHost= MB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = []"
apply(cases "reqs1 T") apply simp+ done
lemma CSTATE_HostModified_DirtyEvictPrevious_otherside_invariant2: shows
" CSTATE X ( T [ 5 sHost= MB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostModified_DirtyEvictPrevious_otherside_invariant3: shows
" CSTATE X ( T [ 5 sHost= MB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 = CSTATE X T 0"
by simp
lemma HostModified_DirtyEvictPrevious_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T [ 5 sHost= MB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextGOPendingIs X T 1"
by simp
lemma HostModified_DirtyEvictPrevious_nextEvict_otherside: shows 
"nextEvict  ( T [ 5 sHost= MB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextEvict T 1"
by simp
lemma HostModified_DirtyEvictPrevious_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T [ 5 sHost= MB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostModified_DirtyEvictPrevious_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T [ 5 sHost= MB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostModified_DirtyEvictPrevious_nextDTHDataPending_sameside: shows 
"nextDTHDataPending  ( T [ 5 sHost= MB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 = nextDTHDataPending T 0"
by simp
lemma HostModified_DirtyEvictPrevious_nextHTDDataPending_sameside: shows 
"nextHTDDataPending  ( T [ 5 sHost= MB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 = nextHTDDataPending T 0"
by simp
lemma HostModified_DirtyEvictPrevious_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T [ 5 sHost= MB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 = nextSnpRespIs X T 0"
by simp
lemma HostModified_DirtyEvictPrevious_HSTATE: shows "HSTATE MB ( T [ 5 sHost= MB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) "
apply(case_tac "program1 T")
by simp+
lemma HostModified_DirtyEvictPrevious_nextLoad: shows "nextLoad ( T [ 5 sHost= MB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) i = nextLoad T i"
apply(case_tac "program1 T")
by simp+
lemma HostModified_DirtyEvictPrevious': shows "reqs1 (T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid]) = reqs1 T"
by simp

(* ========================================= *)
(* Content from FixModifiedEvictFilled.thy *)
(* Lines 1-73 extracted *)
(* ========================================= *)

lemma snps2_ModifiedEvict: shows "snps2 ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA]) = snps2 T"
by simp
lemma snps1_ModifiedEvict: shows "snps1 ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA]) = snps1 T"
by simp
lemma reqs2_ModifiedEvict: shows "reqs2 ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA]) = reqs2 T"
by simp
lemma reqs1_ModifiedEvict: shows " reqs1 T = [] \<Longrightarrow> length (reqs1 ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA])) \<le> 1"
by simp
lemma snpresps2_ModifiedEvict: shows "snpresps2 ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA]) = snpresps2 T"
by simp
lemma snpresps1_ModifiedEvict: shows "snpresps1 ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA]) = snpresps1 T"
by simp
lemma reqresps1_ModifiedEvict: shows "reqresps1 ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA]) = reqresps1 T"
by simp
lemma reqresps2_ModifiedEvict: shows "reqresps2 ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA]) = reqresps2 T"
by simp
lemma dthdatas2_ModifiedEvict: shows "dthdatas2 ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA]) = dthdatas2 T"
by simp
lemma htddatas1_ModifiedEvict: shows "htddatas1 ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA]) = htddatas1 T"
by simp
lemma htddatas2_ModifiedEvict: shows "htddatas2 ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA]) = htddatas2 T"
by simp
lemma reqresps1_ModifiedEvict_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma ModifiedEvict'_nextDTHDataPending: "nextDTHDataPending T i = nextDTHDataPending ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA]) i"
by simp
lemma ModifiedEvict'_nextEvict: "nextEvict T i = nextEvict ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA]) i"
by simp
lemma ModifiedEvict'_nextStore: "nextStore T i = nextStore ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA]) i"
by simp
lemma ModifiedEvict'_nextGOPending: "nextGOPending T i = nextGOPending ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA]) i"
by simp
lemma ModifiedEvict'_nextGOPendingIs: "nextGOPendingIs X T i = nextGOPendingIs X ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA]) i"
by simp
lemma ModifiedEvict'_nextHTDDataPending: "nextHTDDataPending T i = nextHTDDataPending ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA]) i"
by simp
lemma ModifiedEvict'_HSTATE: "HSTATE X T  = HSTATE X ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA]) "
by simp
lemma ModifiedEvict'_CSTATE_otherside: "CSTATE X T 1 = CSTATE X ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA]) 1"
by simp
lemma ModifiedEvict'_CSTATE_sameside: "CSTATE MIA ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA]) 0"
by simp
lemma ModifiedEvict'_nextSnoopIs: "nextSnoopIs X T i = nextSnoopIs X ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA]) i"
by simp
lemma ModifiedEvict'_nextReqIs_otherside: "nextReqIs X T 1 = nextReqIs X ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA]) 1"
by simp
lemma ModifiedEvict'_nextSnpRespIs: "nextSnpRespIs X T i = nextSnpRespIs X ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA]) i"
by simp
lemma ModifiedEvict'_nextReqIs_invariant1: shows "reqs1 T = [] \<Longrightarrow> nextReqIs DirtyEvict ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA]) 0"
by simp
lemma ModifiedEvict'_nextReqIs_invariant_not_RdOwn: shows "X \<noteq> DirtyEvict \<Longrightarrow> nextReqIs X T i = nextReqIs X ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA]) i"
apply(case_tac i)
apply simp
apply(induct "reqs1 T")
apply force
apply (metis append_Cons startsWithProp.simps(2))
by simp
lemma nextGOPending_DeviceModifiedEvict: "nextGOPending ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA]) i = nextGOPending T i"
apply(case_tac i)
apply simp+
done
lemma nextLoad_DeviceModifiedEvict: "nextLoad ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA]) i = nextLoad T i"
apply(case_tac i)
apply simp+
done
lemma nextEvict_DeviceModifiedEvict: "nextEvict ( T [ 0 +=rdreq DirtyEvict] [ 0 s= MIA]) i = nextEvict T i"
apply(case_tac i)
apply simp+
done

(* ========================================= *)
(* Content from FixModifiedRdOwnFilled.thy *)
(* Lines 1-127 extracted *)
(* ========================================= *)





\<comment>\<open>
lemma HostModifiedRdOwn'_devcache_invariant1: shows "(CLEntry.block_state (devcache1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]))) = CLEntry.block_state (devcache1 T)" 
  apply(subgoal_tac "CLEntry.block_state (devcache1 (  T [ 0 +=hostdata  txid] [ 5 sHost= SharedM])) = CLEntry.block_state (devcache1 (  T ))")
  apply(subgoal_tac "CLEntry.block_state (devcache1 (  T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid])) = CLEntry.block_state (devcache1 (  T [ 0 +=hostdata  txid] [ 5 sHost= SharedM]))")
  by simp+  
  

lemma HostModifiedRdOwn'_devcache_invariant2: shows "(CLEntry.block_state (devcache2 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]))) = CLEntry.block_state (devcache2 T)" 
  by simp+

lemma HostModifiedRdOwn'_CSTATE_invariant1: shows "CSTATE X (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 = CSTATE X T 0" 
  by simp

lemma HostModifiedRdOwn'_CSTATE_invariant2: shows "CSTATE X (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 = CSTATE X T 1" 
  by simp

  

lemma nextGOPending_HostModifiedRdOwn: "nextGOPending (   T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ] ) i = nextGOPending T i"
apply(case_tac i)
apply simp+
done

lemma nextLoad_HostModifiedRdOwn: "nextLoad (   T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ] ) i = nextLoad T i"
apply(case_tac i)
apply simp+
done



\<close>
lemma snps1_HostsModifiedRdOwn: shows "snps1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_HostsModifiedRdOwn: shows "reqs2 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_HostsModifiedRdOwn: shows "snpresps2 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_HostsModifiedRdOwn: shows "snpresps1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) = snpresps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_HostsModifiedRdOwn: shows "reqresps2 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostsModifiedRdOwn: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ])) \<le> 1"
by simp
lemma reqresps1_HostsModifiedRdOwn2: shows "reqresps1 T =  (reqresps1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]))"
by simp
lemma dthdatas1_HostsModifiedRdOwn: shows "dthdatas1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) = dthdatas1 T"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_HostsModifiedRdOwn: shows "dthdatas2 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_HostsModifiedRdOwn: shows "htddatas1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) = htddatas1 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_HostsModifiedRdOwn: shows "htddatas2 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostsModifiedRdOwn_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostsModifiedRdOwn_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostsModifiedRdOwn_invariant: shows"nextEvict T 0 = nextEvict (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0"
by simp
lemma CSTATE_HostsModifiedRdOwn_otherside_invariant2: shows
" CSTATE X (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostsModifiedRdOwn_otherside_invariant3: shows
" CSTATE X (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 = CSTATE X T 0"
by simp
lemma HostsModifiedRdOwn_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 = nextGOPendingIs X T 1"
by simp
lemma HostsModifiedRdOwn_nextEvict_otherside: shows 
"nextEvict  (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 = nextEvict T 1"
by simp
lemma HostsModifiedRdOwn_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostsModifiedRdOwn_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostsModifiedRdOwn_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 = nextSnpRespIs X T 0"
by simp
lemma HostModifiedRdOwn_HSTATE: shows "HSTATE MAD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) "
apply(case_tac "program1 T")
by simp+
lemma HostModifiedRdOwn_empty_reqs1_aux: shows " reqs1 T = reqs1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD])"
by simp
lemma snps2_HostModifiedRdOwn: shows "snps2 (T [ 5 sHost= MAD] [ 0 -=req ]) = snps2 T"
by simp

(* ========================================= *)
(* Content from FixModifiedRdSharedFilled.thy *)
(* Lines 1-180 extracted *)
(* ========================================= *)

lemma nextGOPending_HostModifiedRdShared: "nextGOPending (  T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ] ) i = nextGOPending T i"
apply(case_tac i)
apply simp+
done
lemma nextLoad_HostModifiedRdShared: "nextLoad (  T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ] ) i = nextLoad T i"
apply(case_tac i)
apply simp+
done
lemma HostModifiedRdShared_nextLoad: shows "nextLoad T 1 = nextLoad ( T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ]) 1"
by simp
lemma HostModifiedRdShared'_devcache_invariant1: shows "(CLEntry.block_state (devcache1 ( T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ]))) = CLEntry.block_state (devcache1 T)"
by simp+
lemma HostModifiedRdShared'_devcache_invariant2: shows "(CLEntry.block_state (devcache2 ( T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ]))) = CLEntry.block_state (devcache2 T)"
by simp+
lemma HostModifiedRdShared'_CSTATE_invariant1: shows "CSTATE X ( T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ]) 0 = CSTATE X T 0"
by simp
lemma HostModifiedRdShared'_CSTATE_invariant2: shows "CSTATE X ( T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ]) 1 = CSTATE X T 1"
by simp
lemma snps2_HostModifiedRdShared: shows "snps2 T = [] \<Longrightarrow> length (snps2 ( T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ])) \<le> 1"
apply(subgoal_tac "length (snps2 ( T [1 +=snp SnpData txid])) = 1")
apply(subgoal_tac "snps2  ( T [1 +=snp SnpData txid]) = snps2 ( T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ])")
apply (metis le_numeral_extra(4))
by simp +
lemma snps1_HostModifiedRdShared: shows "snps1 ( T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_HostModifiedRdShared: shows "reqs2 ( T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_HostModifiedRdShared: shows "snpresps2 ( T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_HostModifiedRdShared: shows "snpresps1 ( T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ]) = snpresps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_HostModifiedRdShared: shows "reqresps2 ( T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostModifiedRdShared: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 ( T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ])) \<le> 1"
by simp
lemma reqresps1_HostModifiedRdShared2: shows "reqresps1 T =  (reqresps1 ( T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ]))"
by simp
lemma dthdatas1_HostModifiedRdShared: shows "dthdatas1 ( T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ]) = dthdatas1 T"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_HostModifiedRdShared: shows "dthdatas2 ( T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_HostModifiedRdShared: shows "htddatas1 ( T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ]) = htddatas1 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_HostModifiedRdShared: shows "htddatas2 ( T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostModifiedRdShared_invariant: shows"nextEvict T 0 = nextEvict ( T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ]) 0"
by simp
lemma CSTATE_HostModifiedRdShared_otherside_invariant2: shows
" CSTATE X ( T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostModifiedRdShared_otherside_invariant3: shows
" CSTATE X ( T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ]) 0 = CSTATE X T 0"
by simp
lemma HostModifiedRdShared_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ]) 1 = nextGOPendingIs X T 1"
by simp
lemma HostModifiedRdShared_nextEvict_otherside: shows 
"nextEvict  ( T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ]) 1 = nextEvict T 1"
by simp
lemma HostModifiedRdShared_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostModifiedRdShared_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostModifiedRdShared_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ]) 0 = nextSnpRespIs X T 0"
by simp
lemma HostModifiedRdShared_HSTATE: shows "HSTATE SAD ( T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ]) "
by simp+
lemma HostModifiedRdShared_empty_reqs1_aux: shows " reqs1 T = reqs1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD])"
by simp
lemma reqresps2_HostModifiedRdShared_remains: shows "reqresps2 (T [ 0 +=hostdata  txid] [ 5 sHost= SharedM]) = reqresps2 T"
by simp
lemma snps2_single_HostModifiedRdShared: shows "reqresps2 T = [] \<Longrightarrow> length (reqresps2 (T [ 0 +=reqresp GO Shared txid])) \<le> 1 "
by simp
lemma snps2_HostModifiedRdShared_aux1: shows "reqresps2 T = reqresps2 ( T [ 0 -=req])"
by simp
lemma snps2_HostModifiedRdShared_aux2: shows "reqresps2 T = [] \<Longrightarrow> length (reqresps2  ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] )) \<le> 1"
using reqresps2_HostModifiedRdShared_remains snps2_single_HostModifiedRdShared
by presburger
lemma HostModifiedRdShared_one_msg_htddatas1: shows "htddatas1 T = (htddatas1 ( T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ]))"
by simp+
lemma HostModifiedRdShared_nextGOPending: shows "nextGOPending T i = nextGOPending (T [ 1 +=snp SnpData txid] [5 sHost= SAD] [ 0 -=req]) i"
by simp
lemma ModifiedRdShared_reqs1: assumes "length (reqs1 T) \<le> 1" shows "reqs1 ( T [ 1 +=snp snpt txid]  [ 5 sHost= hstate] [ 0 -=req ]) = []"
apply(case_tac "reqs1 T")
apply simp+
by (metis assms dual_order.refl getEventToIssueOrMakeup.cases impossible_Cons int_one_le_iff_zero_less length_greater_0_conv length_rotate1 less_nat_zero_code less_one linorder_le_less_linear list.distinct(1) list.inject nle_le nonneg_int_cases of_nat_1 of_nat_1_eq_iff of_nat_le_0_iff of_nat_le_iff of_nat_less_iff rotate1_length01)
lemma ModifiedRdShared_aux3_r149: assumes "snps2 T = []" shows "nextSnoopIs SnpData ( T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ]) 1"
proof -
have "nextSnoopIs SnpData (T [1 +=snp SnpData txid]) 1" by(insert assms; simp)
have "snps2 (T [1 +=snp SnpData txid]) = snps2 (T [1 +=snp SnpData txid] [5 sHost= SAD] [ 0 -=req])" by simp
show ?thesis
using \<open>nextSnoopIs SnpData (T [ 1 +=snp SnpData txid] ) 1\<close>
by force
qed
lemma nextSnoopIs_inequality: assumes "nextSnoopIs X T i" and "X \<noteq> Y" shows "\<not>nextSnoopIs Y T i"
proof (cases i)
case 0
then
show ?thesis
proof(cases "snps1 T")
case Nil
then
show ?thesis
using "0" empty_no_snoop
by presburger
next
case (Cons a list)
then
show ?thesis
using "0" assms(1) assms(2)
by auto
qed
next
case (Suc nat)
then
show ?thesis
proof(cases "snps2 T")
case Nil
then
show ?thesis
using Suc nat.simps(3) nextSnoopIs_def startsSnp.simps(1)
by presburger
next
case (Cons a list)
then
show ?thesis
using Suc assms(1) assms(2)
by auto
qed
qed
lemma ModifiedRdShared_aux_r149: assumes "snps2 T = []" shows "\<not>nextSnoopIs SnpInv ( T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ]) 1"
proof -
have "nextSnoopIs SnpData ( T [ 1 +=snp SnpData txid]  [ 5 sHost= SAD] [ 0 -=req ]) 1"
using ModifiedRdShared_aux3_r149 assms
by presburger
show ?thesis
using nextSnoopIs_inequality
using \<open>nextSnoopIs SnpData ( T [ 1 +=snp SnpData txid] [ 5 sHost= SAD] [ 0 -=req ]) 1\<close>
by blast
qed

(* ========================================= *)
(* Content from FixModifiedSnpDataInvalidFilled.thy *)
(* Lines 1-105 extracted *)
(* ========================================= *)

lemma reqresps1_ModifiedSnpDataInvalid: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 
(T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd])) \<le> 1"
by simp
lemma snps1_ModifiedSnpDataInvalid: shows "length (snps1 T) \<le> 1 \<Longrightarrow> snps1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) = []"
apply(case_tac "snps1 T")
apply simp+
done
lemma reqs2_ModifiedSnpDataInvalid: shows "reqs2 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_ModifiedSnpDataInvalid: shows "snpresps2 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_ModifiedSnpDataInvalid: shows "snpresps1 T = [] \<Longrightarrow> length (snpresps1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd])) \<le> 1"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_ModifiedSnpDataInvalid: shows "reqresps2 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_ModifiedSnpDataInvalid2: shows "reqresps1 T =  (reqresps1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]))"
by simp
lemma dthdatas1_ModifiedSnpDataInvalid: shows "dthdatas1 T = [] \<Longrightarrow> length (dthdatas1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd])) \<le> 1"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_ModifiedSnpDataInvalid: shows "dthdatas2 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_ModifiedSnpDataInvalid: shows "htddatas1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) = htddatas1 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_ModifiedSnpDataInvalid: shows "htddatas2 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_ModifiedSnpDataInvalid_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_ModifiedSnpDataInvalid_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_ModifiedSnpDataInvalid_invariant: shows"nextEvict T 0 = nextEvict (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) 0"
by simp
lemma CSTATE_ModifiedSnpDataInvalid_otherside_invariant2: shows
" CSTATE X (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_ModifiedSnpDataInvalid_otherside_invariant3: shows
" CSTATE Invalid (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) 0"
by simp
lemma ModifiedSnpDataInvalid_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) 1 = nextGOPendingIs X T 1"
by simp
lemma ModifiedSnpDataInvalid_nextEvict_otherside: shows 
"nextEvict  (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) 1 = nextEvict T 1"
by simp
lemma ModifiedSnpDataInvalid_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) 1 = nextDTHDataPending T 1"
by simp
lemma ModifiedSnpDataInvalid_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) 1 = nextSnpRespIs X T 1"
by simp
lemma ModifiedSnpDataInvalid_nextHTDDataPending_sameside: shows 
"nextDTHDataPending  (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) 0 "
by simp
lemma ModifiedSnpDataInvalid_nextSnpRespIs_sameside: shows 
"snpresps1 T = [] \<Longrightarrow> nextSnpRespIs RspIFwdM  (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) 0"
by simp
lemma ModifiedSnpDataInvalid_empty_reqs1_aux: shows " reqs1 T = reqs1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD])"
by simp
lemma snps2_ModifiedSnpDataInvalid: shows "snps2 (T [ 0 +=hostdata  txid] [ 5 sHost= MA]) = snps2 T"
by simp
lemma snps2_single_ModifiedSnpDataInvalid: shows "snps2 T = [] \<Longrightarrow> length (snps2 (T [ 1 +=snp SnpInv txid])) \<le> 1 "
by simp
lemma snps2_ModifiedSnpDataInvalid_aux1: shows "snps2 T = snps2 ( T [ 0 -=req])"
by simp
lemma snps2_ModifiedSnpDataInvalid_aux2: shows "snps2 T = [] \<Longrightarrow> length (snps2  ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid] )) \<le> 1"
using snps2_ModifiedSnpDataInvalid snps2_single_ModifiedSnpDataInvalid
by presburger
lemma ModifiedSnpDataInvalid_one_msg_htddatas1: shows "htddatas1 T = [] \<Longrightarrow> length (htddatas1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd])) \<le> 1"
by simp
lemma nextLoad_ModifiedSnpDataInvalid: "nextLoad (  T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ] ) i = nextLoad T i"
apply(case_tac i)
apply simp+
done
lemma nextGOPending_ModifiedSnpDataInvalid: "nextGOPending (  T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ] ) i = nextGOPending T i"
apply(case_tac i)
apply simp+
done

(* ========================================= *)
(* Content from FixModifiedSnpDataSharedFilled.thy *)
(* Lines 1-105 extracted *)
(* ========================================= *)

lemma reqresps1_ModifiedSnpDataShared: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 
(T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= Shared] [ Dev1 +=d2hd dthd])) \<le> 1"
by simp
lemma snps1_ModifiedSnpDataShared: shows "length (snps1 T) \<le> 1 \<Longrightarrow> snps1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= Shared] [ Dev1 +=d2hd dthd]) = []"
apply(case_tac "snps1 T")
apply simp+
done
lemma reqs2_ModifiedSnpDataShared: shows "reqs2 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= Shared] [ Dev1 +=d2hd dthd]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_ModifiedSnpDataShared: shows "snpresps2 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= Shared] [ Dev1 +=d2hd dthd]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_ModifiedSnpDataShared: shows "snpresps1 T = [] \<Longrightarrow> length (snpresps1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= Shared] [ Dev1 +=d2hd dthd])) \<le> 1"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_ModifiedSnpDataShared: shows "reqresps2 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= Shared] [ Dev1 +=d2hd dthd]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_ModifiedSnpDataShared2: shows "reqresps1 T =  (reqresps1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= Shared] [ Dev1 +=d2hd dthd]))"
by simp
lemma dthdatas1_ModifiedSnpDataShared: shows "dthdatas1 T = [] \<Longrightarrow> length (dthdatas1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= Shared] [ Dev1 +=d2hd dthd])) \<le> 1"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_ModifiedSnpDataShared: shows "dthdatas2 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= Shared] [ Dev1 +=d2hd dthd]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_ModifiedSnpDataShared: shows "htddatas1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= Shared] [ Dev1 +=d2hd dthd]) = htddatas1 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_ModifiedSnpDataShared: shows "htddatas2 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= Shared] [ Dev1 +=d2hd dthd]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_ModifiedSnpDataShared_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_ModifiedSnpDataShared_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_ModifiedSnpDataShared_invariant: shows"nextEvict T 0 = nextEvict (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= Shared] [ Dev1 +=d2hd dthd]) 0"
by simp
lemma CSTATE_ModifiedSnpDataShared_otherside_invariant2: shows
" CSTATE X (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= Shared] [ Dev1 +=d2hd dthd]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_ModifiedSnpDataShared_otherside_invariant3: shows
" CSTATE Shared (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= Shared] [ Dev1 +=d2hd dthd]) 0"
by simp
lemma ModifiedSnpDataShared_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= Shared] [ Dev1 +=d2hd dthd]) 1 = nextGOPendingIs X T 1"
by simp
lemma ModifiedSnpDataShared_nextEvict_otherside: shows 
"nextEvict  (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= Shared] [ Dev1 +=d2hd dthd]) 1 = nextEvict T 1"
by simp
lemma ModifiedSnpDataShared_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= Shared] [ Dev1 +=d2hd dthd]) 1 = nextDTHDataPending T 1"
by simp
lemma ModifiedSnpDataShared_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= Shared] [ Dev1 +=d2hd dthd]) 1 = nextSnpRespIs X T 1"
by simp
lemma ModifiedSnpDataShared_nextHTDDataPending_sameside: shows 
"nextDTHDataPending  (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= Shared] [ Dev1 +=d2hd dthd]) 0 "
by simp
lemma ModifiedSnpDataShared_nextSnpRespIs_sameside: shows 
"snpresps1 T = [] \<Longrightarrow> nextSnpRespIs RspSFwdM  (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= Shared] [ Dev1 +=d2hd dthd]) 0"
by simp
lemma ModifiedSnpDataShared_empty_reqs1_aux: shows " reqs1 T = reqs1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD])"
by simp
lemma snps2_ModifiedSnpDataShared: shows "snps2 (T [ 0 +=hostdata  txid] [ 5 sHost= MA]) = snps2 T"
by simp
lemma snps2_single_ModifiedSnpDataShared: shows "snps2 T = [] \<Longrightarrow> length (snps2 (T [ 1 +=snp SnpInv txid])) \<le> 1 "
by simp
lemma snps2_ModifiedSnpDataShared_aux1: shows "snps2 T = snps2 ( T [ 0 -=req])"
by simp
lemma snps2_ModifiedSnpDataShared_aux2: shows "snps2 T = [] \<Longrightarrow> length (snps2  ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid] )) \<le> 1"
using snps2_ModifiedSnpDataShared snps2_single_ModifiedSnpDataShared
by presburger
lemma ModifiedSnpDataShared_one_msg_htddatas1: shows "htddatas1 T = [] \<Longrightarrow> length (htddatas1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= Shared] [ Dev1 +=d2hd dthd])) \<le> 1"
by simp
lemma nextLoad_ModifiedSnpDataShared: "nextLoad (  T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ] ) i = nextLoad T i"
apply(case_tac i)
apply simp+
done
lemma nextGOPending_ModifiedSnpDataShared: "nextGOPending (  T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ] ) i = nextGOPending T i"
apply(case_tac i)
apply simp+
done

(* ========================================= *)
(* Content from FixModifiedSnpInvFilled.thy *)
(* Lines 1-104 extracted *)
(* ========================================= *)

lemma reqresps1_ModifiedSnpInv: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd])) \<le> 1"
by simp
lemma snps1_ModifiedSnpInv: shows "length (snps1 T) \<le> 1 \<Longrightarrow> snps1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) = []"
apply(case_tac "snps1 T")
apply simp+
done
lemma reqs2_ModifiedSnpInv: shows "reqs2 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_ModifiedSnpInv: shows "snpresps2 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_ModifiedSnpInv: shows "snpresps1 T = [] \<Longrightarrow> length (snpresps1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd])) \<le> 1"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_ModifiedSnpInv: shows "reqresps2 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_ModifiedSnpInv2: shows "reqresps1 T =  (reqresps1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]))"
by simp
lemma dthdatas1_ModifiedSnpInv: shows "dthdatas1 T = [] \<Longrightarrow> length (dthdatas1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd])) \<le> 1"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_ModifiedSnpInv: shows "dthdatas2 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_ModifiedSnpInv: shows "htddatas1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) = htddatas1 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_ModifiedSnpInv: shows "htddatas2 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_ModifiedSnpInv_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_ModifiedSnpInv_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_ModifiedSnpInv_invariant: shows"nextEvict T 0 = nextEvict (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) 0"
by simp
lemma CSTATE_ModifiedSnpInv_otherside_invariant2: shows
" CSTATE X (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_ModifiedSnpInv_otherside_invariant3: shows
" CSTATE Invalid (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) 0"
by simp
lemma ModifiedSnpInv_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) 1 = nextGOPendingIs X T 1"
by simp
lemma ModifiedSnpInv_nextEvict_otherside: shows 
"nextEvict  (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) 1 = nextEvict T 1"
by simp
lemma ModifiedSnpInv_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) 1 = nextDTHDataPending T 1"
by simp
lemma ModifiedSnpInv_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) 1 = nextSnpRespIs X T 1"
by simp
lemma ModifiedSnpInv_nextHTDDataPending_sameside: shows 
"nextDTHDataPending  (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) 0 "
by simp
lemma ModifiedSnpInv_nextSnpRespIs_sameside: shows 
"snpresps1 T = [] \<Longrightarrow> nextSnpRespIs RspIFwdM  (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) 0"
by simp
lemma ModifiedSnpInv_empty_reqs1_aux: shows " reqs1 T = reqs1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD])"
by simp
lemma snps2_ModifiedSnpInv: shows "snps2 (T [ 0 +=hostdata  txid] [ 5 sHost= MA]) = snps2 T"
by simp
lemma snps2_single_ModifiedSnpInv: shows "snps2 T = [] \<Longrightarrow> length (snps2 (T [ 1 +=snp SnpInv txid])) \<le> 1 "
by simp
lemma snps2_ModifiedSnpInv_aux1: shows "snps2 T = snps2 ( T [ 0 -=req])"
by simp
lemma snps2_ModifiedSnpInv_aux2: shows "snps2 T = [] \<Longrightarrow> length (snps2  ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid] )) \<le> 1"
using snps2_ModifiedSnpInv snps2_single_ModifiedSnpInv
by presburger
lemma ModifiedSnpInv_one_msg_htddatas1: shows "htddatas1 T = [] \<Longrightarrow> length (htddatas1 (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd])) \<le> 1"
by simp
lemma nextLoad_ModifiedSnpInv: "nextLoad (  T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ] ) i = nextLoad T i"
apply(case_tac i)
apply simp+
done
lemma nextGOPending_ModifiedSnpInv: "nextGOPending (  T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ] ) i = nextGOPending T i"
apply(case_tac i)
apply simp+
done

(* ========================================= *)
(* Content from FixSADDataFilled.thy *)
(* Lines 1-124 extracted *)
(* ========================================= *)

lemma nextLoad_HostSADData: "nextLoad (  T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ] ) i = nextLoad T i"
apply(case_tac i) apply simp+ done
lemma nextGOPending_HostSADData: "nextGOPending (  T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ] ) i = nextGOPending T i"
apply(case_tac i) apply simp+ done
lemma HostSADData_nextDataFrom_other: shows "nextDTHDataFrom 1 T = nextDTHDataFrom 1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ]) "
by simp
lemma HostSADData_nextLoad: shows "nextLoad T 1 = nextLoad ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ]) 1"
by simp
lemma HostSADData'_devcache_invariant1: shows "(CLEntry.block_state (devcache1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ]))) = CLEntry.block_state (devcache1 T)"
by simp+
lemma HostSADData'_devcache_invariant2: shows "(CLEntry.block_state (devcache2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ]))) = CLEntry.block_state (devcache2 T)"
by simp+
lemma HostSADData'_CSTATE_invariant1: shows "CSTATE X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ]) 0 = CSTATE X T 0"
by simp
lemma HostSADData'_CSTATE_invariant2: shows "CSTATE X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ]) 1 = CSTATE X T 1"
by simp
lemma snps2_HostSADData: shows "snps2 T =  (snps2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ]))"
by simp+
lemma snps1_HostSADData: shows "snps1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_HostSADData: shows "reqs2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_HostSADData: shows "snpresps2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_HostSADData: shows "snpresps1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ]) = snpresps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_HostSADData: shows "reqresps2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostSADData: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ])) \<le> 1"
by simp
lemma dthdatas1_HostSADData: shows "dthdatas1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] ) = dthdatas1 T"
apply(case_tac "program1 T")
by simp+
lemma dthdatas1_empty_HostSADData: shows "length (dthdatas1 T) \<le> 1 \<Longrightarrow> dthdatas1 ( ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ])) = []"
by(cases "dthdatas1 T", simp+)
lemma dthdatas2_HostSADData: shows "dthdatas2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostSADData_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostSADData_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostSADData_invariant: shows"nextEvict T 0 = nextEvict ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ]) 0"
by simp
lemma nextReqIs_HostSADData_IMAD_invariant2: shows 
  "nextReqIs X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ]) 1 = nextReqIs X T 1"
by simp
lemma nextReqIs_HostSADData_IMAD_invariant1: shows 
  "nextReqIs X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ]) 0 = nextReqIs X T 0"
by simp
lemma CSTATE_HostSADData_otherside_invariant2: shows
" CSTATE X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostSADData_otherside_invariant3: shows
" CSTATE X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ]) 0 = CSTATE X T 0"
by simp
lemma HostSADData_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ]) 1 = nextGOPendingIs X T 1"
by simp
lemma HostSADData_nextGOPendingIs_general: shows 
"nextGOPendingIs X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ]) i = nextGOPendingIs X T i"
by simp
lemma HostSADData_nextGOPending: shows 
"nextGOPendingIs X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ]) i = nextGOPendingIs X T i"
by simp
lemma HostSADData_nextEvict_otherside: shows 
"nextEvict  ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ]) 1 = nextEvict T 1"
by simp
lemma HostSADData_nextDTHDataPending_otherside: shows 
"nextDTHDataPending  ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostSADData_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostSADData_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ]) 0 = nextSnpRespIs X T 0"
by simp
lemma HostSADData_HSTATE: shows "HSTATE SA ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ]) "
by simp+
lemma HostSADData_empty_reqs1_aux: shows " reqs1 T = reqs1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD])"
by simp
lemma reqresps2_HostSADData_remains: shows "reqresps2 (T [ 0 +=hostdata  txid] [ 5 sHost= SharedM]) = reqresps2 T"
by simp
lemma snps2_single_HostSADData: shows "reqresps2 T = [] \<Longrightarrow> length (reqresps2 (T [ 0 +=reqresp GO Shared txid])) \<le> 1 "
by simp
lemma snps2_HostSADData_aux1: shows "reqresps2 T = reqresps2 ( T [ 0 -=req])"
by simp
lemma snps2_HostSADData_aux2: shows "reqresps2 T = [] \<Longrightarrow> length (reqresps2  ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] )) \<le> 1"
using reqresps2_HostSADData_remains snps2_single_HostSADData
by presburger
lemma HostSADData_one_msg_htddatas1: shows "htddatas1 T = (htddatas1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ]))"
by simp+
lemma nextHTDDataPending_SADData: shows "nextHTDDataPending T 0 = nextHTDDataPending ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ]) 0"
by simp
lemma reqs1_HostSADData: "reqs1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ]) = reqs1 T"
by simp
lemma reqreps1_HostSADData: "reqresps1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ]) = reqresps1 T"
by simp
lemma htddatas2_HostSADData: "htddatas2 T = [] \<Longrightarrow> length (htddatas2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SA] [ Dev1 -=d2hdHead ])) \<le> 1"
by simp

(* ========================================= *)
(* Content from FixSADRspIFwdMFilled.thy *)
(* Lines 1-132 extracted *)
(* ========================================= *)

lemma HostSADRspIFwdM'_CSTATE_invariant1: shows "CSTATE X (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) 0 = CSTATE X T 0"
by simp
lemma HostSADRspIFwdM'_CSTATE_invariant2: shows "CSTATE X (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) 1 = CSTATE X T 1"
by simp
lemma nextLoad_HostSADRspIFwdM: "nextLoad (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ] ) i = nextLoad T i"
apply(case_tac i)
apply simp+
done
lemma nextGOPending_HostSADRspIFwdM: "nextGOPending (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ] ) 0 = nextGOPending T 0"
apply simp
done
lemma HostSADRspIFwdM'_devcache_invariant1: shows "(CLEntry.block_state (devcache1 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]))) = CLEntry.block_state (devcache1 T)"
by simp
lemma HostSADRspIFwdM'_devcache_invariant2: shows "(CLEntry.block_state (devcache2 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]))) = CLEntry.block_state (devcache2 T)"
by simp
lemma HostSADRspIFwdM_nextLoad: shows "nextLoad T 1 = nextLoad ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) 1"
by simp
lemma snps2_HostSADRspIFwdM: shows "reqresps2 T = [] \<Longrightarrow> length (reqresps2 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ])) \<le> 1"
apply(subgoal_tac "length (reqresps2 (  T [ 1 +=reqresp GO Shared txid])) = 1")
apply(subgoal_tac "reqresps2  (  T [ 1 +=reqresp GO Shared txid]) = reqresps2 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ])")
apply (metis le_numeral_extra(4))
apply simp
apply simp
done
lemma snps1_HostSADRspIFwdM: shows "snps1 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_HostSADRspIFwdM: shows "reqs2 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma reqs1_HostSADRspIFwdM: shows "reqs1 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) = reqs1 T"
by simp
lemma nextSnoopIs_HostSADRspIFwdM: shows "nextSnoopIs X ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) i = nextSnoopIs X T i"
by simp
lemma snpresps2_HostSADRspIFwdM: shows "snpresps2 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostSADRspIFwdM: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ])) \<le> 1"
by simp
lemma reqresps1_HostSADRspIFwdM2: shows "reqresps1 T =  (reqresps1 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]))"
by simp
lemma dthdatas1_HostSADRspIFwdM_aux: shows "length (snpresps1 T) \<le> 1 \<Longrightarrow> (snpresps1 (T [ 0 -=snpresp ])) = []"
using emptied_snpresps_aux1
by auto
lemma dthdatas1_HostSADRspIFwdM: shows "length (snpresps1 T) \<le> 1 \<Longrightarrow> snpresps1 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) = []"
apply(subgoal_tac "snpresps1 ( T   [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD]) = snpresps1 T")
apply(subgoal_tac "length (snpresps1 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD])) \<le> 1")
using dthdatas1_HostSADRspIFwdM_aux
apply blast
by simp+
lemma dthdatas2_HostSADRspIFwdM: shows "dthdatas2 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_HostSADRspIFwdM: shows "htddatas1 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) = htddatas1 T"
apply simp
done
lemma htddatas2_HostSADRspIFwdM: shows "htddatas2 T = [] \<Longrightarrow> length (htddatas2 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ])) \<le> 1"
apply simp
done
lemma reqresps1_HostSADRspIFwdM_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostSADRspIFwdM_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostSADRspIFwdM_invariant: shows"nextEvict T 0 = nextEvict ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) 0"
by simp
lemma nextReqIs_HostSADRspIFwdM_IMAD_invariant2: shows 
  "nextReqIs X ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) 1 = nextReqIs X T 1"
by simp
lemma nextReqIs_HostSADRspIFwdM_IMAD_invariant1: shows 
  "nextReqIs X ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) 0 = nextReqIs X T 0"
by simp
lemma CSTATE_HostSADRspIFwdM_otherside_invariant2: shows
" CSTATE X ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostSADRspIFwdM_otherside_invariant3: shows
" CSTATE X ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) 0 = CSTATE X T 0"
by simp
lemma HostSADRspIFwdM_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) 0 = nextGOPendingIs X T 0"
by simp
lemma HostSADRspIFwdM_nextEvict_otherside: shows 
"nextEvict  ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) 1 = nextEvict T 1"
by simp
lemma HostSADRspIFwdM_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostSADRspIFwdM_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostSADRspIFwdM_HSTATE: shows "HSTATE SD ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) "
by simp
lemma nextStore_HostSADRspIFwdM: shows "nextStore T = nextStore ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ])"
unfolding nextStore_def
by simp
lemma nextLoad_HostSADRspIFwdM1: shows "nextLoad T = nextLoad ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ])"
unfolding nextLoad_def
by simp
lemma HostSADRspIFwdM': shows "reqs1 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) = reqs1 T"
by simp
lemma HostSADRspIFwdM_empty_reqs1_aux: shows " reqs1 T = reqs1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD])"
by simp
lemma HostSADRspIFwdM_one_msg_htddatas1: shows "htddatas1 T = (htddatas1 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]))"
by simp+
lemma HostSADRspIFwdM_nextGOPending: shows "nextGOPending T i = nextGOPending (T [ 1 +=snp SnpData txid] [5 sHost= SAD] [ 0 -=req]) i"
by simp
lemma HostSADRspIFwdM_htddatas2_aux: shows "htddatas2 T = [] \<Longrightarrow> length (htddatas2 (T [Dev2 +=h2dd msg])) \<le> 1"
apply simp
done

(* ========================================= *)
(* Content from FixSADRspSFwdMFilled.thy *)
(* Lines 1-132 extracted *)
(* ========================================= *)

lemma HostSADRspSFwdM'_CSTATE_invariant1: shows "CSTATE X (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) 0 = CSTATE X T 0"
by simp
lemma HostSADRspSFwdM'_CSTATE_invariant2: shows "CSTATE X (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) 1 = CSTATE X T 1"
by simp
lemma nextLoad_HostSADRspSFwdM: "nextLoad (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ] ) i = nextLoad T i"
apply(case_tac i)
apply simp+
done
lemma nextGOPending_HostSADRspSFwdM: "nextGOPending (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ] ) 0 = nextGOPending T 0"
apply simp
done
lemma HostSADRspSFwdM'_devcache_invariant1: shows "(CLEntry.block_state (devcache1 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]))) = CLEntry.block_state (devcache1 T)"
by simp
lemma HostSADRspSFwdM'_devcache_invariant2: shows "(CLEntry.block_state (devcache2 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]))) = CLEntry.block_state (devcache2 T)"
by simp
lemma HostSADRspSFwdM_nextLoad: shows "nextLoad T 1 = nextLoad ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) 1"
by simp
lemma snps2_HostSADRspSFwdM: shows "reqresps2 T = [] \<Longrightarrow> length (reqresps2 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ])) \<le> 1"
apply(subgoal_tac "length (reqresps2 (  T [ 1 +=reqresp GO Shared txid])) = 1")
apply(subgoal_tac "reqresps2  (  T [ 1 +=reqresp GO Shared txid]) = reqresps2 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ])")
apply (metis le_numeral_extra(4))
apply simp
apply simp
done
lemma snps1_HostSADRspSFwdM: shows "snps1 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_HostSADRspSFwdM: shows "reqs2 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma reqs1_HostSADRspSFwdM: shows "reqs1 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) = reqs1 T"
by simp
lemma nextSnoopIs_HostSADRspSFwdM: shows "nextSnoopIs X ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) i = nextSnoopIs X T i"
by simp
lemma snpresps2_HostSADRspSFwdM: shows "snpresps2 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostSADRspSFwdM: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ])) \<le> 1"
by simp
lemma reqresps1_HostSADRspSFwdM2: shows "reqresps1 T =  (reqresps1 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]))"
by simp
lemma dthdatas1_HostSADRspSFwdM_aux: shows "length (snpresps1 T) \<le> 1 \<Longrightarrow> (snpresps1 (T [ 0 -=snpresp ])) = []"
using emptied_snpresps_aux1
by auto
lemma dthdatas1_HostSADRspSFwdM: shows "length (snpresps1 T) \<le> 1 \<Longrightarrow> snpresps1 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) = []"
apply(subgoal_tac "snpresps1 ( T   [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD]) = snpresps1 T")
apply(subgoal_tac "length (snpresps1 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD])) \<le> 1")
using dthdatas1_HostSADRspSFwdM_aux
apply blast
by simp+
lemma dthdatas2_HostSADRspSFwdM: shows "dthdatas2 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_HostSADRspSFwdM: shows "htddatas1 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) = htddatas1 T"
apply simp
done
lemma htddatas2_HostSADRspSFwdM: shows "htddatas2 T = [] \<Longrightarrow> length (htddatas2 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ])) \<le> 1"
apply simp
done
lemma reqresps1_HostSADRspSFwdM_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostSADRspSFwdM_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostSADRspSFwdM_invariant: shows"nextEvict T 0 = nextEvict ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) 0"
by simp
lemma nextReqIs_HostSADRspSFwdM_IMAD_invariant2: shows 
  "nextReqIs X ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) 1 = nextReqIs X T 1"
by simp
lemma nextReqIs_HostSADRspSFwdM_IMAD_invariant1: shows 
  "nextReqIs X ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) 0 = nextReqIs X T 0"
by simp
lemma CSTATE_HostSADRspSFwdM_otherside_invariant2: shows
" CSTATE X ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostSADRspSFwdM_otherside_invariant3: shows
" CSTATE X ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) 0 = CSTATE X T 0"
by simp
lemma HostSADRspSFwdM_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) 0 = nextGOPendingIs X T 0"
by simp
lemma HostSADRspSFwdM_nextEvict_otherside: shows 
"nextEvict  ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) 1 = nextEvict T 1"
by simp
lemma HostSADRspSFwdM_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostSADRspSFwdM_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostSADRspSFwdM_HSTATE: shows "HSTATE SD ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) "
by simp
lemma nextStore_HostSADRspSFwdM: shows "nextStore T = nextStore ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ])"
unfolding nextStore_def
by simp
lemma nextLoad_HostSADRspSFwdM1: shows "nextLoad T = nextLoad ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ])"
unfolding nextLoad_def
by simp
lemma HostSADRspSFwdM': shows "reqs1 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]) = reqs1 T"
by simp
lemma HostSADRspSFwdM_empty_reqs1_aux: shows " reqs1 T = reqs1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD])"
by simp
lemma HostSADRspSFwdM_one_msg_htddatas1: shows "htddatas1 T = (htddatas1 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SD] [ 0 -=snpresp  ]))"
by simp+
lemma HostSADRspSFwdM_nextGOPending: shows "nextGOPending T i = nextGOPending (T [ 1 +=snp SnpData txid] [5 sHost= SAD] [ 0 -=req]) i"
by simp
lemma HostSADRspSFwdM_htddatas2_aux: shows "htddatas2 T = [] \<Longrightarrow> length (htddatas2 (T [Dev2 +=h2dd msg])) \<le> 1"
apply simp
done

(* ========================================= *)
(* Content from FixSARspIFwdMFilled.thy *)
(* Lines 1-135 extracted *)
(* ========================================= *)

lemma HostSARspIFwdM'_devcache_invariant1: shows "(CLEntry.block_state (devcache1 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]))) = CLEntry.block_state (devcache1 T)"
by simp
lemma HostSARspIFwdM'_devcache_invariant2: shows "(CLEntry.block_state (devcache2 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]))) = CLEntry.block_state (devcache2 T)"
by simp
lemma HostSARspIFwdM'_CSTATE_invariant1: shows "CSTATE X (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) 0 = CSTATE X T 0"
by simp
lemma HostSARspIFwdM'_CSTATE_invariant2: shows "CSTATE X (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) 1 = CSTATE X T 1"
by simp
lemma nextLoad_HostSARspIFwdM: "nextLoad (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ] ) i = nextLoad T i"
apply(case_tac i)
apply simp+
done
lemma nextGOPending_HostSARspIFwdM_1: "nextGOPending (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ] ) 0 = nextGOPending T 0"
apply simp+
done
lemma HostSARspIFwdM_nextLoad: shows "nextLoad T 1 = nextLoad (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) 1"
by simp
lemma snps2_HostSARspIFwdM: shows "reqresps2 T = [] \<Longrightarrow> length (reqresps2 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ])) \<le> 1"
apply(subgoal_tac "length (reqresps2 (  T [ 1 +=reqresp GO Shared txid])) = 1")
apply(subgoal_tac "reqresps2  (  T [ 1 +=reqresp GO Shared txid]) = reqresps2 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ])")
apply (metis le_numeral_extra(4))
apply simp
apply simp
done
lemma snps1_HostSARspIFwdM: shows "snps1 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_HostSARspIFwdM: shows "reqs2 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma reqs1_HostSARspIFwdM: shows "reqs1 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) = reqs1 T"
by simp
lemma nextSnoopIs_HostSARspIFwdM: shows "nextSnoopIs X (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) i = nextSnoopIs X T i"
by simp
lemma snpresps2_HostSARspIFwdM: shows "snpresps2 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostSARspIFwdM: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ])) \<le> 1"
by simp
lemma reqresps1_HostSARspIFwdM2: shows "reqresps1 T =  (reqresps1 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]))"
by simp
lemma dthdatas1_HostSARspIFwdM_aux: shows "length (snpresps1 T) \<le> 1 \<Longrightarrow> (snpresps1 (T [ 0 -=snpresp ])) = []"
using emptied_snpresps_aux1
by auto
lemma dthdatas1_HostSARspIFwdM: shows "length (snpresps1 T) \<le> 1 \<Longrightarrow> snpresps1 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) = []"
apply(subgoal_tac "snpresps1 ( T   [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM]) = snpresps1 T")
apply(subgoal_tac "length (snpresps1 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM])) \<le> 1")
using dthdatas1_HostSARspIFwdM_aux
apply blast
by simp+
lemma dthdatas2_HostSARspIFwdM: shows "dthdatas2 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_HostSARspIFwdM: shows "htddatas1 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) = htddatas1 T"
apply simp
done
lemma htddatas2_HostSARspIFwdM: shows "htddatas2 T = [] \<Longrightarrow> length (htddatas2 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ])) \<le> 1"
apply simp
done
lemma reqresps1_HostSARspIFwdM_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostSARspIFwdM_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostSARspIFwdM_invariant: shows"nextEvict T 0 = nextEvict (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) 0"
by simp
lemma nextReqIs_HostSARspIFwdM_IMAD_invariant2: shows 
  "nextReqIs X (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) 1 = nextReqIs X T 1"
by simp
lemma nextReqIs_HostSARspIFwdM_IMAD_invariant1: shows 
  "nextReqIs X (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) 0 = nextReqIs X T 0"
by simp
lemma CSTATE_HostSARspIFwdM_otherside_invariant2: shows
" CSTATE X (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostSARspIFwdM_otherside_invariant3: shows
" CSTATE X (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) 0 = CSTATE X T 0"
by simp
lemma HostSARspIFwdM_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) 0 = nextGOPendingIs X T 0"
by simp
lemma HostSARspIFwdM_nextEvict_otherside: shows 
"nextEvict  (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) 1 = nextEvict T 1"
by simp
lemma HostSARspIFwdM_nextDTHDataPending_otherside: shows 
"nextDTHDataPending  (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostSARspIFwdM_nextHTDDataPending: shows 
"nextHTDDataPending  (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) i = nextHTDDataPending T i"
by simp
lemma HostSARspIFwdM_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostSARspIFwdM_nextDTHDataPending_sameside: shows 
"nextDTHDataPending  (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) 0 = nextDTHDataPending T 0"
by simp
lemma HostSARspIFwdM_HSTATE: shows "HSTATE SharedM (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) "
by simp
lemma nextStore_HostSARspIFwdM: shows "nextStore T = nextStore (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ])"
unfolding nextStore_def
by simp
lemma HostSARspIFwdM': shows "reqs1 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) = reqs1 T"
by simp
lemma HostSARspIFwdM_empty_reqs1_aux: shows " reqs1 T = reqs1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD])"
by simp
lemma HostSARspIFwdM_one_msg_htddatas1: shows "htddatas1 T = (htddatas1 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]))"
by simp+
lemma HostSARspIFwdM_nextGOPending: shows "nextGOPending T i = nextGOPending (T [ 1 +=snp SnpData txid] [5 sHost= SAD] [ 0 -=req]) i"
by simp
lemma HostSARspIFwdM_htddatas2_aux: shows "htddatas2 T = [] \<Longrightarrow> length (htddatas2 (T [Dev2 +=h2dd msg])) \<le> 1"
apply simp
done

(* ========================================= *)
(* Content from FixSARspSFwdMFilled.thy *)
(* Lines 1-132 extracted *)
(* ========================================= *)

lemma HostSARspSFwdM'_devcache_invariant1: shows "(CLEntry.block_state (devcache1 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]))) = CLEntry.block_state (devcache1 T)"
by simp
lemma HostSARspSFwdM'_devcache_invariant2: shows "(CLEntry.block_state (devcache2 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]))) = CLEntry.block_state (devcache2 T)"
by simp
lemma HostSARspSFwdM'_CSTATE_invariant1: shows "CSTATE X (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) 0 = CSTATE X T 0"
by simp
lemma HostSARspSFwdM'_CSTATE_invariant2: shows "CSTATE X (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) 1 = CSTATE X T 1"
by simp
lemma nextLoad_HostSARspSFwdM: "nextLoad (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ] ) i = nextLoad T i"
apply(case_tac i)
apply simp+
done
lemma nextGOPending_HostSARspSFwdM_1: "nextGOPending (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ] ) 0 = nextGOPending T 0"
apply simp+
done
lemma HostSARspSFwdM_nextLoad: shows "nextLoad T 1 = nextLoad (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) 1"
by simp
lemma snps2_HostSARspSFwdM: shows "reqresps2 T = [] \<Longrightarrow> length (reqresps2 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ])) \<le> 1"
apply(subgoal_tac "length (reqresps2 (  T [ 1 +=reqresp GO Shared txid])) = 1")
apply(subgoal_tac "reqresps2  (  T [ 1 +=reqresp GO Shared txid]) = reqresps2 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ])")
apply (metis le_numeral_extra(4))
apply simp
apply simp
done
lemma snps1_HostSARspSFwdM: shows "snps1 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_HostSARspSFwdM: shows "reqs2 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma reqs1_HostSARspSFwdM: shows "reqs1 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) = reqs1 T"
by simp
lemma nextSnoopIs_HostSARspSFwdM: shows "nextSnoopIs X (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) i = nextSnoopIs X T i"
by simp
lemma snpresps2_HostSARspSFwdM: shows "snpresps2 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostSARspSFwdM: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ])) \<le> 1"
by simp
lemma reqresps1_HostSARspSFwdM2: shows "reqresps1 T =  (reqresps1 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]))"
by simp
lemma dthdatas1_HostSARspSFwdM_aux: shows "length (snpresps1 T) \<le> 1 \<Longrightarrow> (snpresps1 (T [ 0 -=snpresp ])) = []"
using emptied_snpresps_aux1
by auto
lemma dthdatas1_HostSARspSFwdM: shows "length (snpresps1 T) \<le> 1 \<Longrightarrow> snpresps1 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) = []"
apply(subgoal_tac "snpresps1 ( T   [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM]) = snpresps1 T")
apply(subgoal_tac "length (snpresps1 ( T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM])) \<le> 1")
using dthdatas1_HostSARspSFwdM_aux
apply blast
by simp+
lemma dthdatas2_HostSARspSFwdM: shows "dthdatas2 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_HostSARspSFwdM: shows "htddatas1 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) = htddatas1 T"
apply simp
done
lemma htddatas2_HostSARspSFwdM: shows "htddatas2 T = [] \<Longrightarrow> length (htddatas2 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ])) \<le> 1"
apply simp
done
lemma reqresps1_HostSARspSFwdM_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostSARspSFwdM_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostSARspSFwdM_invariant: shows"nextEvict T 0 = nextEvict (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) 0"
by simp
lemma nextReqIs_HostSARspSFwdM_IMAD_invariant2: shows 
  "nextReqIs X (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) 1 = nextReqIs X T 1"
by simp
lemma nextReqIs_HostSARspSFwdM_IMAD_invariant1: shows 
  "nextReqIs X (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) 0 = nextReqIs X T 0"
by simp
lemma CSTATE_HostSARspSFwdM_otherside_invariant2: shows
" CSTATE X (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostSARspSFwdM_otherside_invariant3: shows
" CSTATE X (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) 0 = CSTATE X T 0"
by simp
lemma HostSARspSFwdM_nextEvict_otherside: shows 
"nextEvict  (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) 1 = nextEvict T 1"
by simp
lemma HostSARspSFwdM_nextDTHDataPending_otherside: shows 
"nextDTHDataPending  (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostSARspSFwdM_nextHTDDataPending: shows 
"nextHTDDataPending  (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) i = nextHTDDataPending T i"
by simp
lemma HostSARspSFwdM_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostSARspSFwdM_nextDTHDataPending_sameside: shows 
"nextDTHDataPending  (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) 0 = nextDTHDataPending T 0"
by simp
lemma HostSARspSFwdM_HSTATE: shows "HSTATE SharedM (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) "
by simp
lemma nextStore_HostSARspSFwdM: shows "nextStore T = nextStore (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ])"
unfolding nextStore_def
by simp
lemma HostSARspSFwdM': shows "reqs1 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]) = reqs1 T"
by simp
lemma HostSARspSFwdM_empty_reqs1_aux: shows " reqs1 T = reqs1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD])"
by simp
lemma HostSARspSFwdM_one_msg_htddatas1: shows "htddatas1 T = (htddatas1 (  T [ 1 +=reqresp GO Shared txid] [ 5 sHost= SharedM] [ 0 -=snpresp  ]))"
by simp+
lemma HostSARspSFwdM_nextGOPending: shows "nextGOPending T i = nextGOPending (T [ 1 +=snp SnpData txid] [5 sHost= SAD] [ 0 -=req]) i"
by simp
lemma HostSARspSFwdM_htddatas2_aux: shows "htddatas2 T = [] \<Longrightarrow> length (htddatas2 (T [Dev2 +=h2dd msg])) \<le> 1"
apply simp
done

(* ========================================= *)
(* Content from FixSBDataFilled.thy *)
(* Lines 1-125 extracted *)
(* ========================================= *)

lemma HostSBData'_devcache_invariant1: shows "(CLEntry.block_state (devcache1 ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]))) = CLEntry.block_state (devcache1 T)"
by simp
lemma HostSBData'_devcache_invariant2: shows "(CLEntry.block_state (devcache2 ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]))) = CLEntry.block_state (devcache2 T)"
by simp
lemma HostSBData_nextLoad: shows "nextLoad T 1 = nextLoad ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) 1"
by simp
lemma snps1_HostSBData: shows "snps1 ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) = snps1 T"
by simp
lemma snps2_HostSBData: shows "snps2 ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) = snps2 T"
by simp
lemma reqs2_HostSBData: shows "reqs2 ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) = reqs2 T"
by simp
lemma reqs1_HostSBData: shows "reqs1 ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) = reqs1 T"
by simp
lemma htddatas2_HostSBData: shows "htddatas2 ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) = htddatas2 T"
by simp
lemma nextSnoopIs_HostSBData: shows "nextSnoopIs X ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) i = nextSnoopIs X T i"
by simp
lemma snpresps2_HostSBData: shows "snpresps2 ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) = snpresps2 T"
by simp
lemma snpresps1_HostSBData: shows "snpresps1 ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) = snpresps1 T"
by simp
lemma reqresps2_HostSBData: shows "reqresps2 ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) = reqresps2 T"
by simp
lemma reqresps1_HostSBData: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ])) \<le> 1"
by simp
lemma reqresps1_HostSBData2: shows "reqresps1 T =  (reqresps1 ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]))"
by simp
lemma dthdatas1_HostSBData_aux: shows "length (dthdatas1 T) \<le> 1 \<Longrightarrow> (dthdatas1 (T [ Dev1 -=d2hdHead ])) = []"
apply simp
apply(case_tac "dthdatas1 T")
by simp+
lemma dthdatas1_HostSBData: shows "length (dthdatas1 T) \<le> 1 \<Longrightarrow> dthdatas1 ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) = []"
apply(subgoal_tac "dthdatas1 ( T [ 5 sHost= SharedM] ) = dthdatas1 T")
apply(subgoal_tac "length (dthdatas1 ( T [ 5 sHost= SharedM] )) \<le> 1")
using dthdatas1_HostSBData_aux
apply metis
apply presburger
by simp
lemma dthdatas2_HostSBData: shows "dthdatas2 ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_HostSBData: shows "htddatas1 ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) = htddatas1 T"
apply simp
done
lemma reqresps1_HostSBData_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostSBData_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostSBData_invariant: shows"nextEvict T 0 = nextEvict ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) 0"
by simp
lemma nextReqIs_HostSBData_IMAD_invariant2: shows 
  "nextReqIs X ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) 1 = nextReqIs X T 1"
by simp
lemma nextReqIs_HostSBData_IMAD_invariant1: shows 
  "nextReqIs X ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) 0 = nextReqIs X T 0"
by simp
lemma CSTATE_HostSBData_otherside_invariant2: shows
" CSTATE X ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostSBData_otherside_invariant3: shows
" CSTATE X ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) 0 = CSTATE X T 0"
by simp
lemma HostSBData_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) i = nextGOPendingIs X T i"
by simp
lemma HostSBData_nextEvict_otherside: shows 
"nextEvict  ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) i = nextEvict T i"
by simp
lemma HostSBData_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostSBData_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostSBData_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) 0 = nextSnpRespIs X T 0"
by simp
lemma HostSBData_HSTATE: shows "HSTATE SharedM ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) "
by simp
lemma nextStore_HostSBData: shows "nextStore T = nextStore ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ])"
unfolding nextStore_def
by simp
lemma nextLoad_HostSBData: shows "nextLoad T = nextLoad ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ])"
unfolding nextLoad_def
by simp
lemma HostSBData_empty_reqs1_aux: shows " reqs1 T = reqs1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD])"
by simp
lemma HostSBData_one_msg_htddatas1: shows "htddatas1 T = (htddatas1 ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]))"
by simp+
lemma HostSBData_nextGOPending: shows "nextGOPending T i = nextGOPending ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) i"
by simp
lemma HostSBData_htddatas2_aux: shows "htddatas2 T = [] \<Longrightarrow> length (htddatas2 (T [Dev2 +=h2dd msg])) \<le> 1"
apply simp
done
lemma nextGOPending_HostSBData: "nextGOPending (  T[ 5 sHost= SharedM] [ Dev1 -=d2hdHead ] ) i = nextGOPending T i"
apply(case_tac i)
apply simp+
done
lemma HostSBData_nextSnoopIs: "nextSnoopIs SnpData ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) 1  = nextSnoopIs SnpData T 1"
by simp

(* ========================================= *)
(* Content from FixSDDataFilled.thy *)
(* Lines 1-140 extracted *)
(* ========================================= *)

lemma HostSDData_nextLoad: shows "nextLoad T 1 = nextLoad ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) 1"
by simp
lemma HostSDData'_devcache_invariant1: shows "(CLEntry.block_state (devcache1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]))) = CLEntry.block_state (devcache1 T)"
by simp+
lemma HostSDData'_devcache_invariant2: shows "(CLEntry.block_state (devcache2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]))) = CLEntry.block_state (devcache2 T)"
by simp+
lemma HostSDData'_CSTATE_invariant1: shows "CSTATE X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) 0 = CSTATE X T 0"
by simp
lemma HostSDData'_CSTATE_invariant2: shows "CSTATE X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) 1 = CSTATE X T 1"
by simp
lemma snps2_HostSDData: shows "htddatas2 T = [] \<Longrightarrow> length (htddatas2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ])) \<le> 1"
apply(subgoal_tac "length (htddatas2 (  T [ Dev2 +=h2dd hmsg])) = 1")
apply(subgoal_tac "htddatas2  (  T [ Dev2 +=h2dd hmsg]) = htddatas2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ])")
apply (metis le_numeral_extra(4))
by simp +
lemma snps1_HostSDData: shows "snps1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_HostSDData: shows "reqs2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma reqs1_HostSDData: shows "reqs1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) = reqs1 T"
by simp
lemma nextSnoopIs_HostSDData: shows "nextSnoopIs X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) i = nextSnoopIs X T i"
by simp
lemma snpresps2_HostSDData: shows "snpresps2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_HostSDData: shows "snpresps1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) = snpresps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_HostSDData: shows "reqresps2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostSDData: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ])) \<le> 1"
by simp
lemma reqresps1_HostSDData2: shows "reqresps1 T =  (reqresps1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]))"
by simp
lemma dthdatas1_HostSDData_aux: shows "length (dthdatas1 T) \<le> 1 \<Longrightarrow> (dthdatas1 (T [ Dev1 -=d2hdHead ])) = []"
apply(case_tac "dthdatas1 T")
by simp+
lemma dthdatas1_HostSDData: shows "length (dthdatas1 T) \<le> 1 \<Longrightarrow> dthdatas1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) =[]"
apply(subgoal_tac "dthdatas1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM]) = dthdatas1 T")
apply(subgoal_tac "length (dthdatas1 (( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM]))) \<le> 1")
using dthdatas1_HostSDData_aux
apply presburger
by simp+
lemma dthdatas2_HostSDData: shows "dthdatas2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_HostSDData: shows "htddatas1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) = htddatas1 T"
apply simp
done
lemma htddatas2_HostSDData: shows "htddatas2 T = [] \<Longrightarrow> length (htddatas2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ])) \<le> 1"
apply simp
done
lemma reqresps1_HostSDData_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostSDData_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostSDData_invariant: shows"nextEvict T 0 = nextEvict ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) 0"
by simp
lemma nextReqIs_HostSDData_IMAD_invariant2: shows 
  "nextReqIs X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) 1 = nextReqIs X T 1"
by simp
lemma nextReqIs_HostSDData_IMAD_invariant1: shows 
  "nextReqIs X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) 0 = nextReqIs X T 0"
by simp
lemma CSTATE_HostSDData_otherside_invariant2: shows
" CSTATE X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostSDData_otherside_invariant3: shows
" CSTATE X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) 0 = CSTATE X T 0"
by simp
lemma HostSDData_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) 1 = nextGOPendingIs X T 1"
by simp
lemma HostSDData_nextEvict_otherside: shows 
"nextEvict  ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) 1 = nextEvict T 1"
by simp
lemma HostSDData_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostSDData_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostSDData_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) 0 = nextSnpRespIs X T 0"
by simp
lemma HostSDData_HSTATE: shows "HSTATE SharedM ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) "
by simp
lemma nextStore_HostSDData: shows "nextStore T = nextStore ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ])"
unfolding nextStore_def
by simp
lemma nextLoad_HostSDData: shows "nextLoad T = nextLoad ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ])"
unfolding nextLoad_def
by simp
lemma HostSDData': shows "reqs1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) = reqs1 T"
by simp
lemma HostSDData_empty_reqs1_aux: shows " reqs1 T = reqs1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD])"
by simp
lemma reqresps2_HostSDData_remains: shows "reqresps2 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) = reqresps2 T"
by simp
lemma HostSDData_one_msg_htddatas1: shows "htddatas1 T = (htddatas1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]))"
by simp+
lemma HostSDData_nextGOPending: shows "nextGOPending T i = nextGOPending (T [ 1 +=snp SnpData txid] [5 sHost= SAD] [ 0 -=req]) i"
by simp
lemma HostSDData_htddatas2_aux: shows "htddatas2 T = [] \<Longrightarrow> length (htddatas2 (T [Dev2 +=h2dd msg])) \<le> 1"
apply simp
done
lemma nextGOPending_HostSDData: "nextGOPending (  T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ] ) i = nextGOPending T i"
apply(case_tac i)
apply simp+
done

(* ========================================= *)
(* Content from FixShared_CleanEvict_LastFilled.thy *)
(* Lines 1-102 extracted *)
(* ========================================= *)

lemma snps2_HostShared_CleanEvict_Last: shows "snps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = snps2 T"
apply(case_tac "program1 T")
by simp+
lemma snps1_HostShared_CleanEvict_Last: shows "snps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_HostShared_CleanEvict_Last: shows "reqs2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_HostShared_CleanEvict_Last: shows "snpresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_HostShared_CleanEvict_Last: shows "snpresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = snpresps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_HostShared_CleanEvict_Last: shows "reqresps2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostShared_CleanEvict_Last: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) \<le> 1"
by simp
lemma dthdatas1_HostShared_CleanEvict_Last: shows "dthdatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = dthdatas1 T"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_HostShared_CleanEvict_Last: shows "dthdatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_HostShared_CleanEvict_Last: shows "htddatas1 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = htddatas1 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_HostShared_CleanEvict_Last: shows "htddatas2 ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostShared_CleanEvict_Last_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostShared_CleanEvict_Last_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostShared_CleanEvict_Last_invariant: shows"nextEvict T 0 = nextEvict ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
by simp
lemma CSTATE_HostShared_CleanEvict_Last_otherside_invariant2: shows
" CSTATE X ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostShared_CleanEvict_Last_otherside_invariant3: shows
" CSTATE X ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 = CSTATE X T 0"
by simp
lemma HostShared_CleanEvict_Last_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextGOPendingIs X T 1"
by simp
lemma HostShared_CleanEvict_Last_nextEvict_otherside: shows 
"nextEvict  ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextEvict T 1"
by simp
lemma HostShared_CleanEvict_Last_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostShared_CleanEvict_Last_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostShared_CleanEvict_Last_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 = nextSnpRespIs X T 0"
by simp
lemma HostShared_CleanEvict_Last_HSTATE: shows "HSTATE IB ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) "
apply(case_tac "program1 T") apply  simp+ done
lemma HostShared_CleanEvict_Last_nextLoad: shows "nextLoad ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) i = nextLoad T i"
apply(case_tac "program1 T")
by simp+
lemma HostShared_CleanEvict_Last': shows "reqs1 (T [ 5 sHost= SharedM] [ 0 +=reqresp GO_WritePullDrop Invalid txid]) = reqs1 T"
by simp
lemma nextLoad_HostShared_CleanEvict_Last: "nextLoad ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) i = nextLoad T i"
apply(case_tac i) apply simp+ done
lemma nextGOPending_HostShared_CleanEvict_Last: "nextGOPending ( T [ 5 sHost= IB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextGOPending T 1"
apply simp+
done

(* ========================================= *)
(* Content from FixShared_CleanEvict_NotLastDataFilled.thy *)
(* Lines 1-104 extracted *)
(* ========================================= *)

lemma snps2_HostShared_CleanEvict_NotLastData: shows "snps2 ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = snps2 T"
apply(case_tac "program1 T")
by simp+
lemma snps1_HostShared_CleanEvict_NotLastData: shows "snps1 ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_HostShared_CleanEvict_NotLastData: shows "reqs2 ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_HostShared_CleanEvict_NotLastData: shows "snpresps2 ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_HostShared_CleanEvict_NotLastData: shows "snpresps1 ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = snpresps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_HostShared_CleanEvict_NotLastData: shows "reqresps2 ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostShared_CleanEvict_NotLastData: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) \<le> 1"
by simp
lemma dthdatas1_HostShared_CleanEvict_NotLastData: shows "dthdatas1 ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = dthdatas1 T"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_HostShared_CleanEvict_NotLastData: shows "dthdatas2 ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_HostShared_CleanEvict_NotLastData: shows "htddatas1 ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = htddatas1 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_HostShared_CleanEvict_NotLastData: shows "htddatas2 ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostShared_CleanEvict_NotLastData_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostShared_CleanEvict_NotLastData_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostShared_CleanEvict_NotLastData_invariant: shows"nextEvict T 0 = nextEvict ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
by simp
lemma CSTATE_HostShared_CleanEvict_NotLastData_otherside_invariant2: shows
" CSTATE X ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostShared_CleanEvict_NotLastData_otherside_invariant3: shows
" CSTATE X ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 = CSTATE X T 0"
by simp
lemma HostShared_CleanEvict_NotLastData_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextGOPendingIs X T 1"
by simp
lemma HostShared_CleanEvict_NotLastData_nextEvict_otherside: shows 
"nextEvict  ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextEvict T 1"
by simp
lemma HostShared_CleanEvict_NotLastData_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostShared_CleanEvict_NotLastData_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostShared_CleanEvict_NotLastData_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 = nextSnpRespIs X T 0"
by simp
lemma HostShared_CleanEvict_NotLastData_HSTATE: shows "HSTATE SB ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) "
apply(case_tac "program1 T") apply  simp+ done
lemma HostShared_CleanEvict_NotLastData_nextLoad: shows "nextLoad ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) i = nextLoad T i"
apply(case_tac "program1 T")
by simp+
lemma HostShared_CleanEvict_NotLastData': shows "reqs1 (T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid]) = reqs1 T"
by simp
lemma nextLoad_HostShared_CleanEvict_NotLastData: "nextLoad ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) i = nextLoad T i"
apply(case_tac i) apply simp+ done
lemma nextGOPending_HostShared_CleanEvict_NotLastData: "nextGOPending ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextGOPending T 1"
apply simp+
done
lemma nextReqIs_otherside1: "nextReqIs X ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextReqIs X T 1"
by simp

(* ========================================= *)
(* Content from FixShared_CleanEvict_NotLastDropFilled.thy *)
(* Lines 1-104 extracted *)
(* ========================================= *)

lemma snps2_HostShared_CleanEvict_NotLastDrop: shows "snps2 ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO_WritePullDrop Invalid txid] [ 0 -=req ]) = snps2 T"
apply(case_tac "program1 T")
by simp+
lemma snps1_HostShared_CleanEvict_NotLastDrop: shows "snps1 ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO_WritePullDrop Invalid txid] [ 0 -=req ]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_HostShared_CleanEvict_NotLastDrop: shows "reqs2 ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO_WritePullDrop Invalid txid] [ 0 -=req ]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_HostShared_CleanEvict_NotLastDrop: shows "snpresps2 ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO_WritePullDrop Invalid txid] [ 0 -=req ]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_HostShared_CleanEvict_NotLastDrop: shows "snpresps1 ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO_WritePullDrop Invalid txid] [ 0 -=req ]) = snpresps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_HostShared_CleanEvict_NotLastDrop: shows "reqresps2 ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO_WritePullDrop Invalid txid] [ 0 -=req ]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostShared_CleanEvict_NotLastDrop: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO_WritePullDrop Invalid txid] [ 0 -=req ])) \<le> 1"
by simp
lemma dthdatas1_HostShared_CleanEvict_NotLastDrop: shows "dthdatas1 ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO_WritePullDrop Invalid txid] [ 0 -=req ]) = dthdatas1 T"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_HostShared_CleanEvict_NotLastDrop: shows "dthdatas2 ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO_WritePullDrop Invalid txid] [ 0 -=req ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_HostShared_CleanEvict_NotLastDrop: shows "htddatas1 ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO_WritePullDrop Invalid txid] [ 0 -=req ]) = htddatas1 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_HostShared_CleanEvict_NotLastDrop: shows "htddatas2 ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO_WritePullDrop Invalid txid] [ 0 -=req ]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostShared_CleanEvict_NotLastDrop_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostShared_CleanEvict_NotLastDrop_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostShared_CleanEvict_NotLastDrop_invariant: shows"nextEvict T 0 = nextEvict ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO_WritePullDrop Invalid txid] [ 0 -=req ]) 0"
by simp
lemma CSTATE_HostShared_CleanEvict_NotLastDrop_otherside_invariant2: shows
" CSTATE X ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO_WritePullDrop Invalid txid] [ 0 -=req ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostShared_CleanEvict_NotLastDrop_otherside_invariant3: shows
" CSTATE X ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO_WritePullDrop Invalid txid] [ 0 -=req ]) 0 = CSTATE X T 0"
by simp
lemma HostShared_CleanEvict_NotLastDrop_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO_WritePullDrop Invalid txid] [ 0 -=req ]) 1 = nextGOPendingIs X T 1"
by simp
lemma HostShared_CleanEvict_NotLastDrop_nextEvict_otherside: shows 
"nextEvict  ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO_WritePullDrop Invalid txid] [ 0 -=req ]) 1 = nextEvict T 1"
by simp
lemma HostShared_CleanEvict_NotLastDrop_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO_WritePullDrop Invalid txid] [ 0 -=req ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostShared_CleanEvict_NotLastDrop_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO_WritePullDrop Invalid txid] [ 0 -=req ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostShared_CleanEvict_NotLastDrop_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO_WritePullDrop Invalid txid] [ 0 -=req ]) 0 = nextSnpRespIs X T 0"
by simp
lemma HostShared_CleanEvict_NotLastDrop_HSTATE: shows "HSTATE SharedM ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO_WritePullDrop Invalid txid] [ 0 -=req ]) "
apply(case_tac "program1 T") apply  simp+ done
lemma HostShared_CleanEvict_NotLastDrop_nextLoad: shows "nextLoad ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO_WritePullDrop Invalid txid] [ 0 -=req ]) i = nextLoad T i"
apply(case_tac "program1 T")
by simp+
lemma HostShared_CleanEvict_NotLastDrop': shows "reqs1 (T [ 5 sHost= SharedM] [ 0 +=reqresp GO_WritePullDrop Invalid txid]) = reqs1 T"
by simp
lemma nextLoad_HostShared_CleanEvict_NotLastDrop: "nextLoad ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO_WritePullDrop Invalid txid] [ 0 -=req ]) i = nextLoad T i"
apply(case_tac i) apply simp+ done
lemma nextGOPending_HostShared_CleanEvict_NotLastDrop: "nextGOPending ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO_WritePullDrop Invalid txid] [ 0 -=req ]) 1 = nextGOPending T 1"
apply simp+
done

(* ========================================= *)
(* Content from FixShared_CleanEvictNoData_LastFilled.thy *)
(* Lines 1-104 extracted *)
(* ========================================= *)

lemma snps2_HostShared_CleanEvictNoData_Last: shows "snps2 ( T [ 5 sHost= InvalidM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) = snps2 T"
apply(case_tac "program1 T")
by simp+
lemma snps1_HostShared_CleanEvictNoData_Last: shows "snps1 ( T [ 5 sHost= InvalidM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_HostShared_CleanEvictNoData_Last: shows "reqs2 ( T [ 5 sHost= InvalidM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_HostShared_CleanEvictNoData_Last: shows "snpresps2 ( T [ 5 sHost= InvalidM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_HostShared_CleanEvictNoData_Last: shows "snpresps1 ( T [ 5 sHost= InvalidM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) = snpresps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_HostShared_CleanEvictNoData_Last: shows "reqresps2 ( T [ 5 sHost= InvalidM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostShared_CleanEvictNoData_Last: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 ( T [ 5 sHost= InvalidM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ])) \<le> 1"
by simp
lemma dthdatas1_HostShared_CleanEvictNoData_Last: shows "dthdatas1 ( T [ 5 sHost= InvalidM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) = dthdatas1 T"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_HostShared_CleanEvictNoData_Last: shows "dthdatas2 ( T [ 5 sHost= InvalidM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_HostShared_CleanEvictNoData_Last: shows "htddatas1 ( T [ 5 sHost= InvalidM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) = htddatas1 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_HostShared_CleanEvictNoData_Last: shows "htddatas2 ( T [ 5 sHost= InvalidM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostShared_CleanEvictNoData_Last_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostShared_CleanEvictNoData_Last_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostShared_CleanEvictNoData_Last_invariant: shows"nextEvict T 0 = nextEvict ( T [ 5 sHost= InvalidM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) 0"
by simp
lemma CSTATE_HostShared_CleanEvictNoData_Last_otherside_invariant2: shows
" CSTATE X ( T [ 5 sHost= InvalidM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostShared_CleanEvictNoData_Last_otherside_invariant3: shows
" CSTATE X ( T [ 5 sHost= InvalidM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) 0 = CSTATE X T 0"
by simp
lemma HostShared_CleanEvictNoData_Last_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T [ 5 sHost= InvalidM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) 1 = nextGOPendingIs X T 1"
by simp
lemma HostShared_CleanEvictNoData_Last_nextEvict_otherside: shows 
"nextEvict  ( T [ 5 sHost= InvalidM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) 1 = nextEvict T 1"
by simp
lemma HostShared_CleanEvictNoData_Last_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T [ 5 sHost= InvalidM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostShared_CleanEvictNoData_Last_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T [ 5 sHost= InvalidM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostShared_CleanEvictNoData_Last_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T [ 5 sHost= InvalidM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) 0 = nextSnpRespIs X T 0"
by simp
lemma HostShared_CleanEvictNoData_Last_HSTATE: shows "HSTATE InvalidM ( T [ 5 sHost= InvalidM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) "
apply(case_tac "program1 T") apply  simp+ done
lemma HostShared_CleanEvictNoData_Last_nextLoad: shows "nextLoad ( T [ 5 sHost= InvalidM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) i = nextLoad T i"
apply(case_tac "program1 T")
by simp+
lemma HostShared_CleanEvictNoData_Last': shows "reqs1 (T [ 5 sHost= InvalidM] [ 0 +=reqresp GO Invalid txid]) = reqs1 T"
by simp
lemma nextLoad_HostShared_CleanEvictNoData_Last: "nextLoad ( T [ 5 sHost= InvalidM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) i = nextLoad T i"
apply(case_tac i) apply simp+ done
lemma nextGOPending_HostShared_CleanEvictNoData_Last: "nextGOPending ( T [ 5 sHost= InvalidM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) 1 = nextGOPending T 1"
apply simp+
done
lemma nextReqIs_Shared_CleanEvictNoData_Last_otherside: "nextReqIs X T 1 = nextReqIs X ( T [ 5 sHost= InvalidM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) 1"
by simp

(* ========================================= *)
(* Content from FixShared_CleanEvictNoData_NotLastFilled.thy *)
(* Lines 1-105 extracted *)
(* ========================================= *)

lemma snps2_HostShared_CleanEvictNoData_NotLast: shows "snps2 ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) = snps2 T"
apply(case_tac "program1 T")
by simp+
lemma snps1_HostShared_CleanEvictNoData_NotLast: shows "snps1 ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_HostShared_CleanEvictNoData_NotLast: shows "reqs2 ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_HostShared_CleanEvictNoData_NotLast: shows "snpresps2 ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_HostShared_CleanEvictNoData_NotLast: shows "snpresps1 ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) = snpresps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_HostShared_CleanEvictNoData_NotLast: shows "reqresps2 ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostShared_CleanEvictNoData_NotLast: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ])) \<le> 1"
by simp
lemma dthdatas1_HostShared_CleanEvictNoData_NotLast: shows "dthdatas1 ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) = dthdatas1 T"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_HostShared_CleanEvictNoData_NotLast: shows "dthdatas2 ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_HostShared_CleanEvictNoData_NotLast: shows "htddatas1 ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) = htddatas1 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_HostShared_CleanEvictNoData_NotLast: shows "htddatas2 ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostShared_CleanEvictNoData_NotLast_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostShared_CleanEvictNoData_NotLast_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostShared_CleanEvictNoData_NotLast_invariant: shows"nextEvict T 0 = nextEvict ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) 0"
by simp
lemma CSTATE_HostShared_CleanEvictNoData_NotLast_otherside_invariant2: shows
" CSTATE X ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostShared_CleanEvictNoData_NotLast_otherside_invariant3: shows
" CSTATE X ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) 0 = CSTATE X T 0"
by simp
lemma HostShared_CleanEvictNoData_NotLast_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) 1 = nextGOPendingIs X T 1"
by simp
lemma HostShared_CleanEvictNoData_NotLast_nextEvict_otherside: shows 
"nextEvict  ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) 1 = nextEvict T 1"
by simp
lemma HostShared_CleanEvictNoData_NotLast_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostShared_CleanEvictNoData_NotLast_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostShared_CleanEvictNoData_NotLast_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) 0 = nextSnpRespIs X T 0"
by simp
lemma HostShared_CleanEvictNoData_NotLast_HSTATE: shows "HSTATE SharedM ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) "
apply(case_tac "program1 T") apply  simp+ done
lemma HostShared_CleanEvictNoData_NotLast_nextLoad: shows "nextLoad ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) i = nextLoad T i"
apply(case_tac "program1 T")
by simp+
lemma HostShared_CleanEvictNoData_NotLast': shows "reqs1 (T [ 5 sHost= SharedM] [ 0 +=reqresp GO Invalid txid]) = reqs1 T"
by simp
lemma nextLoad_HostShared_CleanEvictNoData_NotLast: "nextLoad ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) i = nextLoad T i"
apply(case_tac i) apply simp+ done
lemma nextGOPending_HostShared_CleanEvictNoData_NotLast: "nextGOPending ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) 1 = nextGOPending T 1"
apply simp+
done
lemma Shared_CleanEvictNoData_NotLast_otherside_nextReqIs: "nextReqIs X T 1 = nextReqIs X ( T [ 5 sHost= SharedM] [ 0 +=reqresp GO Invalid txid] [ 0 -=req ]) 1"
apply  simp
done

(* ========================================= *)
(* Content from FixSharedDirtyEvictFilled.thy *)
(* Lines 1-110 extracted *)
(* ========================================= *)

lemma snps2_HostShared_DirtyEvict: shows "snps2 ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = snps2 T"
apply(case_tac "program1 T")
by simp+
lemma snps1_HostShared_DirtyEvict: shows "snps1 ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_HostShared_DirtyEvict: shows "reqs2 ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_HostShared_DirtyEvict: shows "snpresps2 ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_HostShared_DirtyEvict: shows "snpresps1 ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = snpresps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_HostShared_DirtyEvict: shows "reqresps2 ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostShared_DirtyEvict: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])) \<le> 1"
by simp
lemma dthdatas1_HostShared_DirtyEvict: shows "dthdatas1 ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = dthdatas1 T"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_HostShared_DirtyEvict: shows "dthdatas2 ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_HostShared_DirtyEvict: shows "htddatas1 ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = htddatas1 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_HostShared_DirtyEvict: shows "htddatas2 ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostShared_DirtyEvict_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostShared_DirtyEvict_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostShared_DirtyEvict_invariant: shows"nextEvict T 0 = nextEvict ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
by simp
lemma CSTATE_HostShared_DirtyEvict_otherside_invariant2: shows
" CSTATE X ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostShared_DirtyEvict_otherside_invariant3: shows
" CSTATE X ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 = CSTATE X T 0"
by simp
lemma HostShared_DirtyEvict_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextGOPendingIs X T 1"
by simp
lemma HostShared_DirtyEvict_nextEvict_otherside: shows 
"nextEvict  ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextEvict T 1"
by simp
lemma HostShared_DirtyEvict_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostShared_DirtyEvict_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostShared_DirtyEvict_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 = nextSnpRespIs X T 0"
by simp
lemma HostShared_DirtyEvict_HSTATE: shows "HSTATE SB ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) "
apply(case_tac "program1 T")
apply  simp+
done
lemma HostShared_DirtyEvict_nextLoad: shows "nextLoad ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) i = nextLoad T i"
apply(case_tac "program1 T")
by simp+
lemma HostShared_DirtyEvict': shows "reqs1 (T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid]) = reqs1 T"
by simp
lemma nextLoad_HostShared_DirtyEvict: "nextLoad ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) i = nextLoad T i"
apply(case_tac i)
apply simp+
done
lemma nextGOPending_HostShared_DirtyEvict: "nextGOPending ( T [ 5 sHost= SB] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 = nextGOPending T 1"
apply simp+
done

(* ========================================= *)
(* Content from FixSharedEvictDataFilled.thy *)
(* Lines 1-80 extracted *)
(* ========================================= *)

lemma snps2_SharedEvictData: shows "snps2 ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA]) = snps2 T"
by simp
lemma snps1_SharedEvictData: shows "snps1 ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA]) = snps1 T"
by simp
lemma reqs2_SharedEvictData: shows "reqs2 ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA]) = reqs2 T"
by simp
lemma reqs1_SharedEvictData: shows " reqs1 T = [] \<Longrightarrow> length (reqs1 ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA])) \<le> 1"
by simp
lemma snpresps2_SharedEvictData: shows "snpresps2 ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA]) = snpresps2 T"
by simp
lemma snpresps1_SharedEvictData: shows "snpresps1 ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA]) = snpresps1 T"
by simp
lemma reqresps1_SharedEvictData: shows "reqresps1 ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA]) = reqresps1 T"
by simp
lemma reqresps2_SharedEvictData: shows "reqresps2 ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA]) = reqresps2 T"
by simp
lemma dthdatas2_SharedEvictData: shows "dthdatas2 ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA]) = dthdatas2 T"
by simp
lemma htddatas1_SharedEvictData: shows "htddatas1 ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA]) = htddatas1 T"
by simp
lemma htddatas2_SharedEvictData: shows "htddatas2 ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA]) = htddatas2 T"
by simp
lemma reqresps1_SharedEvictData_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma SharedEvictData'_nextDTHDataPending: "nextDTHDataPending T i = nextDTHDataPending ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA]) i"
by simp
lemma SharedEvictData'_nextEvict: "nextEvict T i = nextEvict ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA]) i"
by simp
lemma SharedEvictData'_nextStore: "nextStore T i = nextStore ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA]) i"
by simp
lemma SharedEvictData'_nextGOPending: "nextGOPending T i = nextGOPending ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA]) i"
by simp
lemma SharedEvictData'_nextGOPendingIs: "nextGOPendingIs X T i = nextGOPendingIs X ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA]) i"
by simp
lemma SharedEvictData'_nextHTDDataPending: "nextHTDDataPending T i = nextHTDDataPending ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA]) i"
by simp
lemma SharedEvictData'_HSTATE: "HSTATE X T  = HSTATE X ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA]) "
by simp
lemma SharedEvictData'_CSTATE_otherside: "CSTATE X T 1 = CSTATE X ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA]) 1"
by simp
lemma SharedEvictData'_CSTATE_sameside: "CSTATE SIA ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA]) 0"
by simp
lemma SharedEvictData'_nextSnoopIs: "nextSnoopIs X T i = nextSnoopIs X ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA]) i"
by simp
lemma SharedEvictData'_nextReqIs_otherside: "nextReqIs X T 1 = nextReqIs X ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA]) 1"
by simp
lemma SharedEvictData'_nextSnpRespIs: "nextSnpRespIs X T i = nextSnpRespIs X ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA]) i"
by simp
lemma SharedEvictData'_nextReqIs_invariant1: shows "reqs1 T = [] \<Longrightarrow> nextReqIs CleanEvict ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA]) 0"
by simp
lemma SharedEvictData'_nextReqIs_invariant_DirtyEvict: shows "nextReqIs DirtyEvict T i = nextReqIs DirtyEvict ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA]) i"
apply(case_tac i)
apply simp
apply(induct "reqs1 T")
apply force
apply (metis append_Cons startsWithProp.simps(2))
by simp
lemma SharedEvictData'_nextReqIs_invariant_not_RdOwn: shows "X \<noteq> CleanEvict \<Longrightarrow> nextReqIs X T i = nextReqIs X ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA]) i"
apply(case_tac i)
apply simp
apply(induct "reqs1 T")
apply force
apply (metis append_Cons startsWithProp.simps(2))
by simp
lemma nextGOPending_DeviceSharedEvictData: "nextGOPending ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA]) i = nextGOPending T i"
apply(case_tac i)
apply simp+
done
lemma nextLoad_DeviceSharedEvictData: "nextLoad ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA]) i = nextLoad T i"
apply(case_tac i)
apply simp+
done
lemma nextEvict_DeviceSharedEvictData: "nextEvict ( T [ 0 +=rdreq CleanEvict] [ 0 s= SIA]) i = nextEvict T i"
apply(case_tac i)
apply simp+
done

(* ========================================= *)
(* Content from FixSharedEvictFilled.thy *)
(* Lines 1-80 extracted *)
(* ========================================= *)

lemma snps2_SharedEvict: shows "snps2 ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIA]) = snps2 T"
by simp
lemma snps1_SharedEvict: shows "snps1 ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIA]) = snps1 T"
by simp
lemma reqs2_SharedEvict: shows "reqs2 ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIA]) = reqs2 T"
by simp
lemma reqs1_SharedEvict: shows " reqs1 T = [] \<Longrightarrow> length (reqs1 ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIA])) \<le> 1"
by simp
lemma snpresps2_SharedEvict: shows "snpresps2 ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIA]) = snpresps2 T"
by simp
lemma snpresps1_SharedEvict: shows "snpresps1 ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIA]) = snpresps1 T"
by simp
lemma reqresps1_SharedEvict: shows "reqresps1 ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIA]) = reqresps1 T"
by simp
lemma reqresps2_SharedEvict: shows "reqresps2 ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIA]) = reqresps2 T"
by simp
lemma dthdatas2_SharedEvict: shows "dthdatas2 ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIA]) = dthdatas2 T"
by simp
lemma htddatas1_SharedEvict: shows "htddatas1 ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIA]) = htddatas1 T"
by simp
lemma htddatas2_SharedEvict: shows "htddatas2 ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIA]) = htddatas2 T"
by simp
lemma reqresps1_SharedEvict_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma SharedEvict'_nextDTHDataPending: "nextDTHDataPending T i = nextDTHDataPending ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIA]) i"
by simp
lemma SharedEvict'_nextEvict: "nextEvict T i = nextEvict ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIA]) i"
by simp
lemma SharedEvict'_nextStore: "nextStore T i = nextStore ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIA]) i"
by simp
lemma SharedEvict'_nextGOPending: "nextGOPending T i = nextGOPending ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIA]) i"
by simp
lemma SharedEvict'_nextGOPendingIs: "nextGOPendingIs X T i = nextGOPendingIs X ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIA]) i"
by simp
lemma SharedEvict'_nextHTDDataPending: "nextHTDDataPending T i = nextHTDDataPending ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIA]) i"
by simp
lemma SharedEvict'_HSTATE: "HSTATE X T  = HSTATE X ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIA]) "
by simp
lemma SharedEvict'_CSTATE_otherside: "CSTATE X T 1 = CSTATE X ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIA]) 1"
by simp
lemma SharedEvict'_CSTATE_sameside: "CSTATE SIA ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIA]) 0"
by simp
lemma SharedEvict'_nextSnoopIs: "nextSnoopIs X T i = nextSnoopIs X ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIA]) i"
by simp
lemma SharedEvict'_nextReqIs_otherside: "nextReqIs X T 1 = nextReqIs X ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIA]) 1"
by simp
lemma SharedEvict'_nextSnpRespIs: "nextSnpRespIs X T i = nextSnpRespIs X ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIA]) i"
by simp
lemma SharedEvict'_nextReqIs_invariant1: shows "reqs1 T = [] \<Longrightarrow> nextReqIs CleanEvictNoData ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIA]) 0"
by simp
lemma SharedEvict'_nextReqIs_invariant_DirtyEvict: shows "nextReqIs DirtyEvict T i = nextReqIs DirtyEvict ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIA]) i"
apply(case_tac i)
apply simp
apply(induct "reqs1 T")
apply force
apply (metis append_Cons startsWithProp.simps(2))
by simp
lemma SharedEvict'_nextReqIs_invariant_not_RdOwn: shows "X \<noteq> CleanEvictNoData \<Longrightarrow> nextReqIs X T i = nextReqIs X ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIA]) i"
apply(case_tac i)
apply simp
apply(induct "reqs1 T")
apply force
apply (metis append_Cons startsWithProp.simps(2))
by simp
lemma nextGOPending_DeviceSharedEvict: "nextGOPending ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIA]) i = nextGOPending T i"
apply(case_tac i)
apply simp+
done
lemma nextLoad_DeviceSharedEvict: "nextLoad ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIA]) i = nextLoad T i"
apply(case_tac i)
apply simp+
done
lemma nextEvict_DeviceSharedEvict: "nextEvict ( T [ 0 +=rdreq CleanEvictNoData] [ 0 s= SIA]) i = nextEvict T i"
apply(case_tac i)
apply simp+
done

(* ========================================= *)
(* Content from FixSharedRdOwnFilled.thy *)
(* Lines 1-100 extracted *)
(* ========================================= *)

lemma reqresps1_HostSharedRdOwn: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ])) \<le> 1"
by simp
lemma snps1_HostSharedRdOwn: shows "snps1 ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_HostSharedRdOwn: shows "reqs2 ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_HostSharedRdOwn: shows "snpresps2 ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_HostSharedRdOwn: shows "snpresps1 ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ]) = snpresps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_HostSharedRdOwn: shows "reqresps2 ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostSharedRdOwn2: shows "reqresps1 T =  (reqresps1 ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ]))"
by simp
lemma dthdatas1_HostSharedRdOwn: shows "dthdatas1 ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ]) = dthdatas1 T"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_HostSharedRdOwn: shows "dthdatas2 ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_HostSharedRdOwn: shows "htddatas2 ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostSharedRdOwn_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostSharedRdOwn_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostSharedRdOwn_invariant: shows"nextEvict T 0 = nextEvict ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ]) 0"
by simp
lemma CSTATE_HostSharedRdOwn_otherside_invariant2: shows
" CSTATE X ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostSharedRdOwn_otherside_invariant3: shows
" CSTATE X ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ]) 0 = CSTATE X T 0"
by simp
lemma HostSharedRdOwn_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ]) 1 = nextGOPendingIs X T 1"
by simp
lemma HostSharedRdOwn_nextEvict_otherside: shows 
"nextEvict  ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ]) 1 = nextEvict T 1"
by simp
lemma HostSharedRdOwn_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostSharedRdOwn_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostSharedRdOwn_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ]) 0 = nextSnpRespIs X T 0"
by simp
lemma HostSharedRdOwn_HSTATE: shows "HSTATE MA ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ]) "
apply(case_tac "program1 T")
by simp+
lemma HostSharedRdOwn_empty_reqs1_aux: shows " reqs1 T = reqs1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD])"
by simp
lemma snps2_HostSharedRdOwn: shows "snps2 (T [ 0 +=hostdata  txid] [ 5 sHost= MA]) = snps2 T"
by simp
lemma snps2_single_HostSharedRdOwn: shows "snps2 T = [] \<Longrightarrow> length (snps2 (T [ 1 +=snp SnpInv txid])) \<le> 1 "
by simp
lemma snps2_HostSharedRdOwn_aux1: shows "snps2 T = snps2 ( T [ 0 -=req])"
by simp
lemma snps2_HostSharedRdOwn_aux2: shows "snps2 T = [] \<Longrightarrow> length (snps2  ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid] )) \<le> 1"
using snps2_HostSharedRdOwn snps2_single_HostSharedRdOwn
by presburger
lemma HostSharedRdOwn_one_msg_htddatas1: shows "htddatas1 T = [] \<Longrightarrow> length (htddatas1 ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ])) \<le> 1"
by simp
lemma nextLoad_HostSharedRdOwn: "nextLoad (  T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ] ) i = nextLoad T i"
apply(case_tac i)
apply simp+
done
lemma nextGOPending_HostSharedRdOwn: "nextGOPending (  T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ] ) i = nextGOPending T i"
apply(case_tac i)
apply simp+
done

(* ========================================= *)
(* Content from FixSharedRdOwnNoDataFilled.thy *)
(* Lines 1-101 extracted *)
(* ========================================= *)



(* ========================================= *)
(* Content from FixSharedRdOwnSelfFilled.thy *)
(* Lines 1-98 extracted *)
(* ========================================= *)

sledgehammer_params[timeout = 15]
lemma reqresps1_HostSharedRdOwnSelf: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ])) \<le> 1"
by simp
lemma snps1_HostSharedRdOwnSelf: shows "snps1 (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_HostSharedRdOwnSelf: shows "reqs2 (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_HostSharedRdOwnSelf: shows "snpresps2 (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_HostSharedRdOwnSelf: shows "snpresps1 (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ]) = snpresps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_HostSharedRdOwnSelf: shows "reqresps2 (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma dthdatas1_HostSharedRdOwnSelf: shows "dthdatas1 (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ]) = dthdatas1 T"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_HostSharedRdOwnSelf: shows "dthdatas2 (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_HostSharedRdOwnSelf: shows "htddatas2 (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostSharedRdOwnSelf_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostSharedRdOwnSelf_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostSharedRdOwnSelf_invariant: shows"nextEvict T 0 = nextEvict (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ]) 0"
by simp
lemma CSTATE_HostSharedRdOwnSelf_otherside_invariant2: shows
" CSTATE X (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostSharedRdOwnSelf_otherside_invariant3: shows
" CSTATE X (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ]) 0 = CSTATE X T 0"
by simp
lemma HostSharedRdOwnSelf_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ]) 1 = nextGOPendingIs X T 1"
by simp
lemma HostSharedRdOwnSelf_nextEvict_otherside: shows 
"nextEvict  (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ]) 1 = nextEvict T 1"
by simp
lemma HostSharedRdOwnSelf_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostSharedRdOwnSelf_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostSharedRdOwnSelf_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ]) 0 = nextSnpRespIs X T 0"
by simp
lemma HostSharedRdOwnSelf_HSTATE: shows "HSTATE ModifiedM (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ]) "
apply(case_tac "program1 T")
by simp+
lemma HostSharedRdOwnSelf_empty_reqs1_aux: shows " reqs1 T = reqs1 (  T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid])"
by simp
lemma snps2_HostSharedRdOwnSelf: shows "snps2 (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM]) = snps2 T"
by simp
lemma snps2_single_HostSharedRdOwnSelf: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 (T [ 0 +=reqresp GO mesi txid])) \<le> 1 "
by simp
lemma snps2_HostSharedRdOwnSelf_aux1: shows "snps2 T = snps2 ( T [ 0 -=req])"
by simp
lemma snps2_HostSharedRdOwnSelf_aux2: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1  ( T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid][ 0 -=req ] )) \<le> 1"
by simp
lemma HostSharedRdOwnSelf_one_msg_htddatas1: shows "htddatas1 T = [] \<Longrightarrow> length (htddatas1 (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ])) \<le> 1"
by simp
lemma nextLoad_HostSharedRdOwnSelf: "nextLoad (  T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid]  [ 0 -=req ] ) i = nextLoad T i"
apply(case_tac i)
apply simp+
done
lemma nextGOPending_HostSharedRdOwnSelf: "reqresps1 T = [] \<Longrightarrow> nextGOPending (  T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid]  [ 0 -=req ] ) 0 "
apply(case_tac "reqresps1 T")
apply simp+
done

(* ========================================= *)
(* Content from FixSharedRdSharedFilled.thy *)
(* Lines 1-132 extracted *)
(* ========================================= *)

lemma HostSharedRdShared_nextLoad: shows "nextLoad T 1 = nextLoad (  T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) 1"
by simp
lemma HostSharedRdShared'_devcache_invariant1: shows "(CLEntry.block_state (devcache1 (  T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]))) = CLEntry.block_state (devcache1 T)"
apply(subgoal_tac "CLEntry.block_state (devcache1 (  T [ 0 +=hostdata  txid] [ 5 sHost= SharedM])) = CLEntry.block_state (devcache1 (  T ))")
apply(subgoal_tac "CLEntry.block_state (devcache1 (  T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid])) = CLEntry.block_state (devcache1 (  T [ 0 +=hostdata  txid] [ 5 sHost= SharedM]))")
by simp+
lemma HostSharedRdShared'_devcache_invariant2: shows "(CLEntry.block_state (devcache2 (  T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]))) = CLEntry.block_state (devcache2 T)"
by simp+
lemma HostSharedRdShared'_CSTATE_invariant1: shows "CSTATE X (  T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) 0 = CSTATE X T 0"
by simp
lemma HostSharedRdShared'_CSTATE_invariant2: shows "CSTATE X (  T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) 1 = CSTATE X T 1"
by simp
lemma snps2_HostSharedRdShared: shows "snps2 ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) = snps2 T"
by simp
lemma snps1_HostSharedRdShared: shows "snps1 ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_HostSharedRdShared: shows "reqs2 ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma reqs1_HostSharedRdShared: shows "length (reqs1 T ) \<le> 1 \<Longrightarrow> reqs1 ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) = []"
apply(case_tac "reqs1 T")
apply simp+
done
lemma snpresps2_HostSharedRdShared: shows "snpresps2 ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_HostSharedRdShared: shows "snpresps1 ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) = snpresps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_HostSharedRdShared: shows "reqresps2 ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostSharedRdShared: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ])) \<le> 1"
by simp
lemma dthdatas1_HostSharedRdShared: shows "dthdatas1 ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) = dthdatas1 T"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_HostSharedRdShared: shows "dthdatas2 ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_HostSharedRdShared: shows "htddatas2 ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_HostSharedRdShared_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_HostSharedRdShared_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma nextEvict_HostSharedRdShared_invariant: shows"nextEvict T 0 = nextEvict ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) 0"
by simp
lemma nextReqIs_HostSharedRdShared_IMAD_invariant2: shows 
  "nextReqIs X ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) 1 = nextReqIs X T 1"
by simp
lemma CSTATE_HostSharedRdShared_otherside_invariant2: shows
" CSTATE X ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) 1 = CSTATE X T 1"
by simp
lemma CSTATE_HostSharedRdShared_otherside_invariant3: shows
" CSTATE X ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) 0 = CSTATE X T 0"
by simp
lemma HostSharedRdShared_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) 1 = nextGOPendingIs X T 1"
by simp
lemma HostSharedRdShared_nextEvict_otherside: shows 
"nextEvict  ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) 1 = nextEvict T 1"
by simp
lemma HostSharedRdShared_nextDTHDataPending_otherside: shows 
"nextDTHDataPending  ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) 1 = nextDTHDataPending T 1"
by simp
lemma HostSharedRdShared_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) 1 = nextSnpRespIs X T 1"
by simp
lemma HostSharedRdShared_nextDTHDataPending_sameside: shows 
"nextDTHDataPending  ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) 0 = nextDTHDataPending T 0"
by simp
lemma HostSharedRdShared_nextHTDDataPending_otherside: shows 
"nextHTDDataPending  ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) 1 = nextHTDDataPending T 1"
by simp
lemma HostSharedRdShared_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) 0 = nextSnpRespIs X T 0"
by simp
lemma HostSharedRdShared_HSTATE: shows "HSTATE SharedM ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) "
apply(case_tac "program1 T")
by simp+
lemma HostSharedRdShared_empty_reqs1_aux: shows " reqs1 T = reqs1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD])"
by simp
lemma reqresps2_HostSharedRdShared_remains: shows "reqresps2 (T [ 0 +=hostdata  txid] [ 5 sHost= SharedM]) = reqresps2 T"
by simp
lemma snps2_single_HostSharedRdShared: shows "reqresps2 T = [] \<Longrightarrow> length (reqresps2 (T [ 0 +=reqresp GO Shared txid])) \<le> 1 "
by simp
lemma snps2_HostSharedRdShared_aux1: shows "reqresps2 T = reqresps2 ( T [ 0 -=req])"
by simp
lemma snps2_HostSharedRdShared_aux2: shows "reqresps2 T = [] \<Longrightarrow> length (reqresps2  ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] )) \<le> 1"
using reqresps2_HostSharedRdShared_remains snps2_single_HostSharedRdShared
by presburger
lemma HostSharedRdShared_one_msg_htddatas1: shows "htddatas1 T = [] \<Longrightarrow> length (htddatas1 ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ])) \<le> 1"
apply(subgoal_tac "length (htddatas1 ( T [ 0 +=hostdata  txid])) \<le> 1")
apply(subgoal_tac "htddatas1 ( T [ 0 +=hostdata  txid]) = htddatas1 ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ])")
apply metis
by simp+
lemma nextLoad_HostSharedRdShared: "nextLoad (  T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ] ) i = nextLoad T i"
apply(case_tac i)
apply simp+
done
lemma reqs1_length_HostSharedRdShared: "length (reqs1 T) \<le> 1 \<Longrightarrow> reqs1 ( T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ]) = []"
apply simp
apply(case_tac "reqs1 T")
apply simp
by simp
lemma nextGOPending_HostSharedRdShared: "nextGOPending (  T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid] [ 0 -=req ] ) 1 = nextGOPending T 1"
apply simp
done

(* ========================================= *)
(* Content from FixSharedSnpInvFilled.thy *)
(* Lines 1-101 extracted *)
(* ========================================= *)

lemma SharedSnpInv_ModifiedM_aux2: shows " reqs1 T = reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid])"
by simp
lemma SharedSnpInv'_reqs2_invariant1_aux1: shows "reqs2 T = reqs2 (   T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid])"
by simp
lemma SharedSnpInv'_snps2_invariant1_aux1: shows "snps2 T = snps2 (   T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid])"
by simp
lemma SharedSnpInv'_snps2_invariant1_aux2: shows "snpresps2 T = snpresps2 (   T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid])"
by simp
lemma SharedSnpInv'_snps2_invariant1 : shows "((snps2 (   T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) \<noteq> [] \<longrightarrow>
   snpresps2 (   T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) = []) \<and>
  (snpresps2 (   T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) \<noteq> [] \<longrightarrow>
   snps2 (   T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) = [])) = ((snps2 T \<noteq> [] \<longrightarrow> snpresps2 T = []) \<and> (snpresps2 T \<noteq> [] \<longrightarrow> snps2 T = []))"
using SharedSnpInv'_snps2_invariant1_aux1 SharedSnpInv'_snps2_invariant1_aux2
by presburger
lemma SharedSnpInv'_snpresps1_invariant7: shows "length (snpresps1 (T  [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd])) = 
  length (snpresps1 T)"
by simp
lemma SharedSnpInv'_reqresps2_value_invariant: shows 
  "reqresps2 (   T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) = reqresps2 T"
by simp
lemma SharedSnpInv'_snoopGORules: shows  "
((snpresps2 (   T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) \<noteq> [] \<longrightarrow> 
  reqresps2 (   T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) = []) \<and> 
(reqresps2 (   T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) \<noteq> [] \<longrightarrow> 
  snpresps2 (   T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) = [])) = (
(snpresps2 T \<noteq> [] \<longrightarrow> reqresps2 T = []) \<and> (reqresps2 T \<noteq> [] \<longrightarrow> snpresps2 T = []))"
apply(subgoal_tac "snpresps2 (   T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) = snpresps2 T")
apply(subgoal_tac "reqresps2 (   T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) = reqresps2 T")
apply presburger
using SharedSnpInv'_reqresps2_value_invariant
apply blast
using SharedSnpInv'_snps2_invariant1_aux2
by presburger
lemma SharedSnpInv'_reqresps_irrelevant1: shows 
  "reqresps1 (   T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) = reqresps1 T"
by simp
lemma SharedSnpInv'_reqresps2_invariant: shows "reqresps2 (   T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) = reqresps2 T"
by simp
lemma SharedSnpInv'_dthdatas1_aux: shows 
  "dthdatas1 (   T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid] ) = dthdatas1 T"
by simp
lemma SharedSnpInv'_dthdatas2: shows 
  "dthdatas2 (   T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) = dthdatas2 T"
by simp
lemma SharedSnpInv'_htddatas1: shows 
  "htddatas1 (   T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) = htddatas1 T"
by simp
lemma SharedSnpInv'_htddatas2: shows 
  "htddatas2 (   T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) = htddatas2 T"
by simp
lemma SharedSnpInv_C_msg_not_half: shows "X \<noteq> Y \<Longrightarrow> nextReqIs z ( T [ 0 s= X]) 0 \<longrightarrow> \<not> CSTATE Y ( T [ 0 s= X]) 0"
using CSTATE_def SharedSnpInv'_CSTATE_invariant5
by presburger
lemma SharedSnpInv_nextReqIs: shows "nextReqIs z T i = nextReqIs z (T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) i"
apply simp
done
lemma SharedSnpInv_nextGOPendingIs: shows "nextGOPendingIs gotype T i = nextGOPendingIs gotype (T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) i"
using SharedSnpInv'_reqresps2_value_invariant SharedSnpInv'_reqresps_irrelevant1 nextGOPendingIs_def
by presburger
lemma SharedSnpInv_CSTATE: shows "CSTATE mesi T 1 = CSTATE mesi (T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) 1"
apply simp
done
lemma SharedSnpInv_nextEvict: shows "nextEvict T i = nextEvict  (T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) i"
apply simp
done
lemma SharedSnpInv_nextStore: shows "nextStore T i = nextStore  (T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) i"
apply simp
done
lemma SharedSnpInv_nextSnoopIs_otherside: shows "nextSnoopIs X T 1 = nextSnoopIs X  (T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) 1"
apply simp
done
lemma SharedSnpInv_HSTATE: "HSTATE X T = HSTATE X (T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid])"
by simp
lemma SharedSnpInv_C_msg_not_half2: shows " nextReqIs z T 1 \<longrightarrow> \<not> CSTATE Y T 1 \<Longrightarrow> 
  nextReqIs z (T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) 1 \<longrightarrow> \<not> CSTATE Y (T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) 1"
using ModifiedSnpInv'_CSTATE SharedSnpInv_nextReqIs
by blast
lemma snpresps1_SharedSnpInv'_aux1: shows "snpresps1 T = snpresps1 (T [0 -=snp ] [ 0 s= Invalid])"
by simp
lemma SharedSnpInv'_MA: assumes "SWMR_state_machine T \<and>  CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0" 
  shows "HSTATE MA (   T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid])"
apply(subgoal_tac "HSTATE MA T")
apply(subgoal_tac "HSTATE MA (   T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid])")
apply blast
using HSTATE_invariant_ModifiedSnpInv
apply presburger
using C_msg_P_host_def SWMR_state_machine_def assms
  using INVALID_ROW_def LOAD_COL_def MEM_I_ROW_def MEM_RDS_COL_def SnoopType.size_gen(1)
  
  by (smt (verit))

lemma snps1_SharedSnpInv: shows " length (snps1 T) \<le> 1 \<Longrightarrow> \<not>nextSnoopPending (T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [0 s= Invalid]) 0"
apply(case_tac "snps1 T")
apply simp apply simp done
lemma nextGOPending_DeviceSharedSnpInv: "nextGOPending (  T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid] ) i = nextGOPending T i"
apply(case_tac i) apply simp+ done
lemma nextLoad_DeviceSharedSnpInv: "nextLoad (  T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid] ) i = nextLoad T i"
apply(case_tac i) apply simp+ done

(* ========================================= *)
(* Content from FixSharedStoreFilled.thy *)
(* Lines 1-74 extracted *)
(* ========================================= *)

lemma snps2_SharedStore: shows "snps2 ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD]) = snps2 T"
by simp
lemma snps1_SharedStore: shows "snps1 ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD]) = snps1 T"
by simp
lemma reqs2_SharedStore: shows "reqs2 ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD]) = reqs2 T"
by simp
lemma reqs1_SharedStore: shows " reqs1 T = [] \<Longrightarrow> length (reqs1 ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD])) \<le> 1"
by simp
lemma snpresps2_SharedStore: shows "snpresps2 ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD]) = snpresps2 T"
by simp
lemma snpresps1_SharedStore: shows "snpresps1 ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD]) = snpresps1 T"
by simp
lemma reqresps1_SharedStore: shows "reqresps1 ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD]) = reqresps1 T"
by simp
lemma reqresps2_SharedStore: shows "reqresps2 ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD]) = reqresps2 T"
by simp
lemma dthdatas2_SharedStore: shows "dthdatas2 ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD]) = dthdatas2 T"
by simp
lemma htddatas1_SharedStore: shows "htddatas1 ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD]) = htddatas1 T"
by simp
lemma htddatas2_SharedStore: shows "htddatas2 ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD]) = htddatas2 T"
by simp
lemma reqresps1_SharedStore_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma SharedStore'_nextDTHDataPending: "nextDTHDataPending T i = nextDTHDataPending ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD]) i"
by simp
lemma SharedStore'_nextEvict: "nextEvict T i = nextEvict ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD]) i"
by simp
lemma SharedStore'_nextStore: "nextStore T i = nextStore ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD]) i"
by simp
lemma SharedStore'_nextGOPending: "nextGOPending T i = nextGOPending ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD]) i"
by simp
lemma SharedStore'_nextGOPendingIs: "nextGOPendingIs X T i = nextGOPendingIs X ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD]) i"
by simp
lemma SharedStore'_nextHTDDataPending: "nextHTDDataPending T i = nextHTDDataPending ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD]) i"
by simp
lemma SharedStore'_HSTATE: "HSTATE X T  = HSTATE X ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD]) "
by simp
lemma SharedStore'_CSTATE_otherside: "CSTATE X T 1 = CSTATE X ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD]) 1"
by simp
lemma SharedStore'_CSTATE_sameside: "CSTATE SMAD ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD]) 0"
by simp
lemma SharedStore'_nextSnoopIs: "nextSnoopIs X T i = nextSnoopIs X ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD]) i"
by simp
lemma SharedStore'_nextReqIs_otherside: "nextReqIs X T 1 = nextReqIs X ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD]) 1"
by simp
lemma SharedStore'_nextSnpRespIs: "nextSnpRespIs X T i = nextSnpRespIs X ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD]) i"
by simp
lemma SharedStore'_nextReqIs_invariant1: shows "reqs1 T = [] \<Longrightarrow> nextReqIs RdOwn ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD]) 0"
by simp
lemma SharedStore'_nextReqIs_invariant_DirtyEvict: shows "nextReqIs DirtyEvict T i = nextReqIs DirtyEvict ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD]) i"
apply(case_tac i)
apply simp
apply(induct "reqs1 T")
apply force
apply (metis append_Cons startsWithProp.simps(2))
by simp
lemma SharedStore'_nextReqIs_invariant_not_RdOwn: shows "X \<noteq> RdOwn \<Longrightarrow> nextReqIs X T i = nextReqIs X ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD]) i"
apply(case_tac i)
apply simp
apply(induct "reqs1 T")
apply force
apply (metis append_Cons startsWithProp.simps(2))
by simp
lemma nextGOPending_DeviceSharedStore: "nextGOPending ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD]) i = nextGOPending T i"
apply(case_tac i) apply simp+ done
lemma nextLoad_DeviceSharedStore: "nextLoad ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD]) i = nextLoad T i"
apply(case_tac i) apply simp+ done
lemma nextEvict_DeviceSharedStore: "nextEvict ( T [ 0 +=rdreq RdOwn] [ 0 s= SMAD]) i = nextEvict T i"
apply(case_tac i) apply simp+ done

(* ========================================= *)
(* Content from FixSharedStoreNewFilled.thy *)
(* Lines 1-74 extracted *)
(* ========================================= *)


(* ========================================= *)
(* Content from FixSIACGOFilled.thy *)
(* Lines 1-179 extracted *)
(* ========================================= *)

lemma nextEvict_SIACGO_invariant: shows"nextEvict T 0 = nextEvict ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] ) 0"
by simp
lemma nextReqIs_SIACGO_IMAD_invariant2: shows 
  "nextReqIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 1 = nextReqIs X T 1"
by(case_tac "program1 T", simp+)
lemma nextReqIs_SIACGO_IMAD_invariant1: shows 
  "nextReqIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 0 = nextReqIs X T 0"
by(case_tac "program1 T", simp+)
lemma CSTATE_SIACGO_otherside_invariant2: shows
" CSTATE X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 1 = CSTATE X T 1"
by(case_tac "program1 T", simp+)
lemma SIACGO_nextEvict_otherside: shows 
"nextEvict  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 1 = nextEvict T 1"
by(case_tac "program1 T", simp+)
lemma SIACGO_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 1 = nextDTHDataPending T 1"
by(case_tac "program1 T", simp+)
lemma SIACGO_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 1 = nextSnpRespIs X T 1"
by(case_tac "program1 T", simp+)
lemma SIACGO_nextHTDDataPending_sameside: shows 
"nextDTHDataPending  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 0 = nextDTHDataPending T 0"
by(case_tac "program1 T", simp+)
lemma SIACGO_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 0 = nextSnpRespIs X T 0"
by(case_tac "program1 T", simp+)
lemma devcache1_SIACGO_invariant_aux1: shows "CLEntry.block_state  (devcache1 T) = ISD \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ 0 -=reqresp ] )) \<noteq> Modified"
using MESI_State.distinct(7) devcache1_consume_reqresps1_invariant
by presburger
lemma devcache1_SIACGO_invariant_aux: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ 0 -=reqresp ] [ 0 -=devd ])) \<noteq> Modified"
using devcache1_SIACGO_invariant_aux1
by auto
lemma devcache1_SIACGO_invariant: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T [ 0 :=dd msg ] [ 0 -=reqresp ] [ 0 -=devd ])) \<noteq> Modified"
apply(subgoal_tac "CLEntry.block_state  (devcache1 (T  [ 0 :=dd msg ])) = Shared")
using devcache1_SIACGO_invariant_aux
apply blast
by simp
lemma CSTATE_SIACGO_IMAD_invariant: shows "
CSTATE Invalid (T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ]  [ -=i 0]) 0"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
by simp+
lemma nextSnoopIs_SIACGO: shows 
  "nextSnoopIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) i = nextSnoopIs X T i"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp
by simp+
lemma nextReqIs_SIACGO: shows "nextReqIs X T i = nextReqIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) i"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp
by simp+
lemma SIACGO_snps2:   " snps2  T  = snps2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp apply simp done
lemma SIACGO_snps1:   " snps1  T  = snps1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp apply simp done
lemma SIACGO_reqs1:   " reqs1  T  = reqs1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp apply simp done
lemma SIACGO_reqs2:   " reqs2  T  = reqs2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp apply simp done
lemma SIACGO_reqresps2:   " reqresps2  T  = reqresps2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp apply simp done
lemma SIACGO_snpresps1:   " snpresps1  T  = snpresps1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp apply simp done
lemma SIACGO_snpresps2:   " snpresps2  T  = snpresps2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp apply simp done
lemma SIACGO_dthdatas1:   " dthdatas1  T = [] \<Longrightarrow> 
  length (dthdatas1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])) \<le> 1"
apply (cases "program1 T")
apply simp apply simp done
lemma SIACGO_dthdatas2:   " dthdatas2  T  = dthdatas2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp apply simp done
lemma SIACGO_htddatas1:   "htddatas1 T =  (htddatas1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]))"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
using Type1State.update_convs(12) Type1State.update_convs(2) Type1State.update_convs(8) change_state_def config_differ_dev_mapping_def config_differ_dthdata_def consumeReqresp_def device_perform_op_htddatas1
apply force
by simp+
lemma SIACGO_htddatas2:   " htddatas2  T  = htddatas2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp apply simp done
lemma SIACGO_nextHTDDataPending: "nextHTDDataPending T i = 
  nextHTDDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])  i"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp apply simp+ done
lemma snps2_SIACGO: shows "snps2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = snps2 T"
apply(case_tac "program1 T")
by simp+
lemma snps1_SIACGO: shows "snps1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_SIACGO: shows "reqs2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma reqs1_SIACGO: shows "reqs1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = reqs1 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_SIACGO: shows "snpresps2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_SIACGO: shows "snpresps1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = snpresps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_SIACGO: shows "reqresps2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_SIACGO: shows "dthdatas2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_SIACGO: shows "htddatas1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = htddatas1 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_SIACGO: shows "htddatas2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_SIACGO_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma SIACGO_CSTATE_aux: shows "CSTATE X T 0 = CSTATE X ( T [ 0 -=reqresp ]  [ -=i 0]) 0"
apply(case_tac "program1 T")
by simp+
lemma nextGOPending_DeviceSIACGO_other: "nextGOPending (  T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0] ) 1 = nextGOPending T 1"
apply(case_tac "program1 T") apply simp+ done
lemma nextLoad_DeviceSIACGO: "nextLoad (  T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0] ) 1 = nextLoad T 1"
apply(case_tac "program1 T") apply simp+ done
lemma nextGOPending_DeviceSIACGO: "nextGOPending (  T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0] ) 1 = nextGOPending T 1"
using nextGOPending_DeviceSIACGO_other
by blast

(* ========================================= *)
(* Content from FixSIAGO_WritePullDropFilled.thy *)
(* Lines 1-249 extracted *)
(* ========================================= *)

lemma nextEvict_SIAGO_WritePullDrop_invariant: shows"nextEvict T 0 = nextEvict ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] ) 0"
by simp
lemma HSTATE_SIAGO_WritePullDrop_invariant: shows "HSTATE X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = 
  HSTATE X T"
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp+
done
lemma nextReqIs_SIAGO_WritePullDrop_IMAD_invariant2: shows 
  "nextReqIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 1 = nextReqIs X T 1"
by(case_tac "program1 T", simp+)
lemma nextReqIs_SIAGO_WritePullDrop_IMAD_invariant1: shows 
  "nextReqIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 0 = nextReqIs X T 0"
by(case_tac "program1 T", simp+)
lemma CSTATE_SIAGO_WritePullDrop_otherside_invariant2: shows
" CSTATE X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 1 = CSTATE X T 1"
by(case_tac "program1 T", simp+)
lemma SIAGO_WritePullDrop_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 1 = nextGOPendingIs X T 1"
by(case_tac "program1 T", simp+)
lemma SIAGO_WritePullDrop_nextEvict_otherside: shows 
"nextEvict  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 1 = nextEvict T 1"
by(case_tac "program1 T", simp+)
lemma SIAGO_WritePullDrop_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 1 = nextDTHDataPending T 1"
by(case_tac "program1 T", simp+)
lemma SIAGO_WritePullDrop_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 1 = nextSnpRespIs X T 1"
by(case_tac "program1 T", simp+)
lemma SIAGO_WritePullDrop_nextHTDDataPending_sameside: shows 
"nextDTHDataPending  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 0 = nextDTHDataPending T 0"
by(case_tac "program1 T", simp+)
lemma SIAGO_WritePullDrop_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 0 = nextSnpRespIs X T 0"
by(case_tac "program1 T", simp+)
lemma devcache1_SIAGO_WritePullDrop_invariant_aux1: shows "CLEntry.block_state  (devcache1 T) = ISD \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ 0 -=reqresp ] )) \<noteq> Modified"
using MESI_State.distinct(7) devcache1_consume_reqresps1_invariant
by presburger
lemma devcache1_SIAGO_WritePullDrop_invariant_aux: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ 0 -=reqresp ] [ 0 -=devd ])) \<noteq> Modified"
using devcache1_SIAGO_WritePullDrop_invariant_aux1
by auto
lemma devcache1_SIAGO_WritePullDrop_invariant: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T [ 0 :=dd msg ] [ 0 -=reqresp ] [ 0 -=devd ])) \<noteq> Modified"
apply(subgoal_tac "CLEntry.block_state  (devcache1 (T  [ 0 :=dd msg ])) = Shared")
using devcache1_SIAGO_WritePullDrop_invariant_aux
apply blast
by simp
lemma CSTATE_SIAGO_WritePullDrop_IMAD_invariant: shows "
CSTATE Invalid (T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ]  [ -=i 0]) 0"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
by simp+
lemma nextSnoopIs_SIAGO_WritePullDrop: shows 
  "nextSnoopIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) i = nextSnoopIs X T i"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp
by simp+
lemma CSTATE_SIAGO_WritePullDrop_otherside: shows "CSTATE X T 1 = CSTATE X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 1"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp
by simp+
lemma nextReqIs_SIAGO_WritePullDrop: shows "nextReqIs X T i = nextReqIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) i"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp
by simp+
lemma SIAGO_WritePullDrop_snps2:   " snps2  T  = snps2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma SIAGO_WritePullDrop_snps1:   " snps1  T  = snps1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma SIAGO_WritePullDrop_reqs1:   " reqs1  T  = reqs1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma SIAGO_WritePullDrop_reqs2:   " reqs2  T  = reqs2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma SIAGO_WritePullDrop_reqresps2:   " reqresps2  T  = reqresps2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma SIAGO_WritePullDrop_snpresps1:   " snpresps1  T  = snpresps1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma SIAGO_WritePullDrop_snpresps2:   " snpresps2  T  = snpresps2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma SIAGO_WritePullDrop_dthdatas1:   " dthdatas1  T = [] \<Longrightarrow> 
  length (dthdatas1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])) \<le> 1"
apply (cases "program1 T")
apply simp
apply simp
done
lemma SIAGO_WritePullDrop_dthdatas2:   " dthdatas2  T  = dthdatas2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma SIAGO_WritePullDrop_htddatas1:   "htddatas1 T =  (htddatas1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]))"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
using Type1State.update_convs(12) Type1State.update_convs(2) Type1State.update_convs(8) change_state_def config_differ_dev_mapping_def config_differ_dthdata_def consumeReqresp_def device_perform_op_htddatas1
apply force
by simp+
lemma SIAGO_WritePullDrop_htddatas2:   " htddatas2  T  = htddatas2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp
apply simp
done
lemma SIAGO_WritePullDrop_nextHTDDataPending: "nextHTDDataPending T i = 
  nextHTDDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])  i"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp+
done
lemma snps2_SIAGO_WritePullDrop: shows "snps2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = snps2 T"
apply(case_tac "program1 T")
by simp+
lemma snps1_SIAGO_WritePullDrop: shows "snps1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_SIAGO_WritePullDrop: shows "reqs2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma reqs1_SIAGO_WritePullDrop: shows "reqs1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = reqs1 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_SIAGO_WritePullDrop: shows "snpresps2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_SIAGO_WritePullDrop: shows "snpresps1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = snpresps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_SIAGO_WritePullDrop: shows "reqresps2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_SIAGO_WritePullDrop: shows "dthdatas2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_SIAGO_WritePullDrop: shows "htddatas1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = htddatas1 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_SIAGO_WritePullDrop: shows "htddatas2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_SIAGO_WritePullDrop_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_SIAGO_WritePullDrop_aux1: shows "reqresps1 T = reqresps1 (T [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_SIAGO_WritePullDrop: assumes "length (reqresps1 T) \<le> 1" shows "reqresps1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = []"
proof -
have half_same: " (reqresps1  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid])) = reqresps1 T" by simp
have quarter_reduce: "reqresps1 (T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ]) = []"
proof -
have half_l1: "length (reqresps1  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] )) \<le> 1"
using assms half_same
by presburger
show ?thesis
using half_l1 reqresps1_SIAGO_WritePullDrop_aux
by presburger
qed
have quarter_same: "reqresps1  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ]) = reqresps1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
using reqresps1_SIAGO_WritePullDrop_aux1
by blast
show ?thesis
using quarter_reduce quarter_same
by presburger
qed
lemma SIAGO_WritePullDrop_CSTATE_aux: shows "CSTATE X T 0 = CSTATE X ( T [ 0 -=reqresp ]  [ -=i 0]) 0"
apply(case_tac "program1 T")
by simp+
lemma nextGOPending_DeviceSIAGO_WritePullDrop_other: "nextGOPending (  T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0] ) 1 = nextGOPending T 1"
apply(case_tac "program1 T")
apply simp+
done
lemma nextLoad_DeviceSIAGO_WritePullDrop: "nextLoad (  T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0] ) 1 = nextLoad T 1"
apply(case_tac "program1 T")
apply simp+
done
lemma nextGOPending_DeviceSIAGO_WritePullDrop: "nextGOPending (  T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0] ) 1 = nextGOPending T 1"
using nextGOPending_DeviceSIAGO_WritePullDrop_other
by blast
lemma impconjI: "\<lbrakk>A  \<longrightarrow> C; A \<longrightarrow> D \<rbrakk> \<Longrightarrow> A \<longrightarrow>  (C \<and> D)"
by metis

(* ========================================= *)
(* Content from FixSIAGO_WritePullFilled.thy *)
(* Lines 1-147 extracted *)
(* ========================================= *)

lemma snps2_SIAGO_WritePull: shows "snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = snps2 T"
apply(case_tac "program1 T")
by simp+
lemma snps1_SIAGO_WritePull: shows "snps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_SIAGO_WritePull: shows "reqs2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma reqs1_SIAGO_WritePull: shows "reqs1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = reqs1 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_SIAGO_WritePull: shows "snpresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_SIAGO_WritePull: shows "snpresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = snpresps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_SIAGO_WritePull: shows "reqresps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_SIAGO_WritePull: shows "dthdatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_SIAGO_WritePull: shows "htddatas1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = htddatas1 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_SIAGO_WritePull: shows "htddatas2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_SIAGO_WritePull_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_SIAGO_WritePull_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_SIAGO_WritePull: assumes "length (reqresps1 T) \<le> 1" shows "reqresps1  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
proof -
have half_same: " (reqresps1  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid])) = reqresps1 T" by simp
have quarter_reduce: "reqresps1 (T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ]) = []"
proof -
have half_l1: "length (reqresps1  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] )) \<le> 1"
using assms half_same
by presburger
show ?thesis
using half_l1 reqresps1_SIAGO_WritePull_aux
by presburger
qed
have quarter_same: "reqresps1  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ]) = reqresps1  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
using reqresps1_SIAGO_WritePull_aux1
by blast
show ?thesis
using quarter_reduce quarter_same
by presburger
qed
lemma nextEvict_SIAGO_WritePull_CSTATE_invariant: shows "nextEvict T 0 \<Longrightarrow> CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])  0"
apply(case_tac "program1 T") apply simp+ done
lemma nextEvict_SIAGO_WritePull_invariant: shows"nextEvict T 0 = nextEvict ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] ) 0"
by simp
lemma HSTATE_SIAGO_WritePull_invariant: shows "HSTATE X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = 
  HSTATE X T"
apply(case_tac "program1 T")
by simp+
lemma CSTATE_SIAGO_WritePull_IMAD_invariant: shows "  CSTATE Invalid (T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd]) 0"
by simp
lemma CSTATE_SIAGO_WritePull_Invalid: shows " CSTATE Invalid (T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd]) 0"
using nextEvict_SIAGO_WritePull_CSTATE_invariant nextEvict_SIAGO_WritePull_invariant
using CSTATE_SIAGO_WritePull_IMAD_invariant
by presburger
lemma nextReqIs_SIAGO_WritePull_IMAD_invariant2: shows 
  "nextReqIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 = nextReqIs X T 1"
apply(case_tac "program1 T")
by simp+
lemma nextReqIs_SIAGO_WritePull_IMAD_invariant1: shows 
  "nextReqIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 = nextReqIs X T 0"
apply(case_tac "program1 T")
by simp+
lemma CSTATE_SIAGO_WritePull_otherside_invariant2: shows
" CSTATE X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 = CSTATE X T 1"
apply(case_tac "program1 T")
by simp+
lemma SIAGO_WritePull_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 = nextGOPendingIs X T 1"
apply(case_tac "program1 T")
by simp+
lemma SIAGO_WritePull_nextEvict_otherside: shows 
"nextEvict  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 = nextEvict T 1"
apply(case_tac "program1 T")
by simp+
lemma SIAGO_WritePull_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 = nextDTHDataPending T 1"
apply(case_tac "program1 T") apply  simp+ done
lemma SIAGO_WritePull_nextHTDDataPending_real: shows 
"nextHTDDataPending  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) i = nextHTDDataPending T i"
apply(case_tac "program1 T") apply  simp+ done
lemma SIAGO_WritePull_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 = nextSnpRespIs X T 1"
apply(case_tac "program1 T")
by simp+
lemma SIAGO_WritePull_nextHTDDataPending_sameside: shows 
"nextDTHDataPending  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 = nextDTHDataPending T 1"
apply(case_tac "program1 T")
by simp+
lemma SIAGO_WritePull_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 = nextSnpRespIs X T 0"
apply(case_tac "program1 T") apply  simp+ done
lemma SIAGO_WritePull_HSTATE: shows "HSTATE X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = 
  HSTATE X T"
apply(case_tac "program1 T")
by simp+
lemma SIAGO_WritePull_reqresps1_empty: shows 
  "length (reqresps1 T ) \<le> 1 \<Longrightarrow> reqresps1 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
using reqresps1_SIAGO_WritePull
by presburger
lemma SIAGO_WritePull_CSTATE_aux: shows "CSTATE X T 0 = CSTATE X ( T [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
apply(case_tac "program1 T")
by simp+

  
\<comment>\<open>_params[minimize=true,preplay_timeout=50,timeout=200]
\<close>
lemma nextGOPending_DeviceSIAGO_WritePull: "nextGOPending (  T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0] ) 1 = nextGOPending T 1"
by (metis nextGOPending_def option.inject reqresps2_SIAGO_WritePull reqresps2_remove_op zero_neq_one)
lemma nextLoad_DeviceSIAGO_WritePull: "nextLoad (  T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0] ) 1 = nextLoad T 1"
apply(case_tac "program1 T") apply simp+ done

(* ========================================= *)
(* Content from FixSIASnpInvFilled.thy *)
(* Lines 1-104 extracted *)
(* ========================================= *)

lemma SIASnpInv_ModifiedM_aux2: shows " reqs1 T = reqs1 ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi])"
apply(case_tac i)
by simp+
lemma SIASnpInv'_reqs2_invariant1_aux1: shows "reqs2 T = reqs2 ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi])"
apply(case_tac i)
by simp+
lemma SIASnpInv'_snps2_invariant1_aux1: shows "snps2 T = snps2 ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [0 -=snp ] [ i s= mesi])"
apply(case_tac i)
by simp+
lemma SIASnpInv'_snpresps2_invariant1_aux2: shows "snpresps2 T = snpresps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [i -=snp ] [ i s= mesi])"
apply(case_tac i)
by simp+
lemma SIASnpInv'_snps2_invariant1 : shows "((snps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [0 -=snp ] [ i s= mesi]) \<noteq> [] \<longrightarrow>
   snpresps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [0 -=snp ] [ i s= mesi]) = []) \<and>
  (snpresps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [0 -=snp ] [ i s= mesi]) \<noteq> [] \<longrightarrow>
   snps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [0 -=snp ] [ i s= mesi]) = [])) = ((snps2 T \<noteq> [] \<longrightarrow> snpresps2 T = []) \<and> (snpresps2 T \<noteq> [] \<longrightarrow> snps2 T = []))"
apply(case_tac i)
using SIASnpInv'_snps2_invariant1_aux1 SIASnpInv'_snpresps2_invariant1_aux2
apply presburger
by simp
lemma SIASnpInv'_reqresps2_invariant: shows 
  "reqresps2 ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi]) = reqresps2 T"
apply(case_tac i)
by simp+
lemma SIASnpInv'_snoopGORules: shows  "
((snpresps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [i -=snp ] [ i s= mesi]) \<noteq> [] \<longrightarrow> 
  reqresps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [i -=snp ] [ i s= mesi]) = []) \<and> 
(reqresps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [i -=snp ] [ i s= mesi]) \<noteq> [] \<longrightarrow> 
  snpresps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [i -=snp ] [ i s= mesi]) = [])) = (
(snpresps2 T \<noteq> [] \<longrightarrow> reqresps2 T = []) \<and> (reqresps2 T \<noteq> [] \<longrightarrow> snpresps2 T = []))"
apply(subgoal_tac "snpresps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [i -=snp ] [ i s= mesi]) = snpresps2 T")
apply(subgoal_tac "reqresps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [i -=snp ] [ i s= mesi]) = reqresps2 T")
apply simp
apply(case_tac i)
apply simp
apply simp
apply(case_tac i)
by simp+
lemma SIASnpInv'_reqresps_irrelevant1: shows 
  "reqresps1 ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi]) = reqresps1 T"
apply(case_tac i)
by simp+
lemma SIASnpInv'_dthdatas1_aux: shows 
  "dthdatas1 (   T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp rtype tid] [0 -=snp ] [ 0 s= Invalid] ) = dthdatas1 T"
by simp
lemma SIASnpInv'_dthdatas2: shows 
  "dthdatas2 ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi]) = dthdatas2 T"
apply(case_tac i)
by simp+
lemma SIASnpInv'_htddatas1: shows 
  "htddatas1 ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi]) = htddatas1 T"
apply(case_tac i)
by simp+
lemma SIASnpInv'_htddatas2: shows 
  "htddatas2 ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi]) = htddatas2 T"
apply(case_tac i)
by simp+
lemma SIASnpInv_C_msg_not_half: shows "X \<noteq> Y \<Longrightarrow> nextReqIs z ( T [ i s= X]) i \<longrightarrow> \<not> CSTATE Y ( T [ i s= X]) i"
apply(case_tac i)
by simp+
lemma SIASnpInv_nextReqIs: shows "nextReqIs z T j = nextReqIs z ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp u w] [i -=snp ] [ i s= mesi]) j"
apply(case_tac i)
by simp+
lemma SIASnpInv_nextGOPendingIs: shows "nextGOPendingIs gotype T i = nextGOPendingIs gotype ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi]) i"
using SIASnpInv'_reqresps2_invariant SIASnpInv'_reqresps_irrelevant1 nextGOPendingIs_def
by presburger
lemma SIASnpInv_CSTATE: shows "CSTATE mesi T 1 = CSTATE mesi (T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp rtype tid] [0 -=snp ] [ 0 s= Invalid]) 1"
apply simp
done
lemma SIASnpInv_nextEvict: shows "nextEvict T j = nextEvict  ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi]) j"
apply(case_tac i)
by simp+
lemma SIASnpInv_nextStore: shows "nextStore T j = nextStore  ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi]) j"
apply(case_tac i)
by simp+
lemma SIASnpInv_nextSnoopIs_otherside: shows "nextSnoopIs X T 1 = nextSnoopIs X  (T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp rtype tid] [0 -=snp ] [ 0 s= Invalid]) 1"
apply simp
done
lemma snpresps1_SIASnpInv'_aux1: shows "snpresps1 T = snpresps1 (T [i -=snp ] [ i s= X])"
apply(case_tac i) apply simp+ done
lemma snps1_SIASnpInv: shows " length (snps1 T) \<le> 1 \<Longrightarrow> \<not>nextSnoopPending ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [0 -=snp ] [ 0 s= mesi]) 0"
apply(case_tac "snps1 T")
apply simp apply simp done
lemma nextGOPending_DeviceSIASnpInv: "nextGOPending ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi]) j = nextGOPending T j"
apply(case_tac j)
apply(case_tac i)
apply simp+
apply(case_tac i) apply simp+ done
lemma nextLoad_DeviceSIASnpInv: "nextLoad ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi]) j = nextLoad T j"
apply(case_tac j)
apply(case_tac i)
apply simp+
apply(case_tac i) apply simp+ done

(* ========================================= *)
(* Content from FixSMADDataFilled.thy *)
(* Lines 1-70 extracted *)
(* ========================================= *)

lemma nextSnoopPending_SMADData1: shows "nextSnoopPending ( T [ 0 s= SMA] [ 0 :=dd getHTDDataOrMakeup T 0] [ 0 -=devd ]) 1 = nextSnoopPending T 1"
using DeviceID.simps(3) Type1State.iffs Type1State.surjective Type1State.update_convs(2) change_state_def config_differ_dev_mapping_def device_copy_in_data_def nextSnoopPending_def nextSnoopPending_devConsume_data_invariant
by auto
lemma HSTATE_SMADData: shows "HSTATE X T = HSTATE X (T [ 0 s= SMA] [ 0 :=dd getHTDDataOrMakeup T 0] [ 0 -=devd ])"
using hstate_invariants(17) hstate_invariants(20) hstate_invariants(24)
by presburger
lemma CSTATE_SMADData_otherside: shows "CSTATE X T 1 = CSTATE X ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ]) 1"
by simp
lemma nextReqIs_SMADData: shows "nextReqIs X T i = nextReqIs X ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ]) i"
by simp
lemma SMADData_nextGOPendingIs: shows "nextGOPendingIs X T i = nextGOPendingIs X ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ]) i"
by simp
lemma SMADData_nextEvict: shows "nextEvict T 1 = nextEvict ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ]) 1"
by simp
lemma SMADData_nextLoad: shows "nextLoad T 1 = nextLoad ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ]) 1"
by simp
lemma SMADData_HSTATE: shows "(HSTATE X ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ])) = HSTATE X T"
by simp
lemma SMADData_HSTATES: shows "(HSTATE MAD ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ]) \<or>
  HSTATE MA ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ]) \<or>
  HSTATE MD ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ]) \<or>
  HSTATE ModifiedM ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ])) = (HSTATE MAD T \<or> HSTATE MA T \<or> HSTATE MD T \<or> HSTATE ModifiedM T)"
by simp
lemma SMADData_nextSnoopIs: shows "nextSnoopIs  X T i = nextSnoopIs X ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ]) i"
by simp
lemma SMADData_nextStore_otherside: shows "nextStore T 1 = nextStore ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ]) 1"
by simp
lemma SMADData_snps2:   " snps2  T  = snps2  ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp apply simp done
lemma SMADData_snps1:   " snps1  T  = snps1  ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp apply simp done
lemma SMADData_reqs1:   " reqs1  T  = reqs1  ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp apply simp done
lemma SMADData_reqs2:   " reqs2  T  = reqs2  ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp apply simp done
lemma SMADData_reqresps1:   " reqresps1  T  = reqresps1  ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp apply simp done
lemma SMADData_reqresps2:   " reqresps2  T  = reqresps2  ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp apply simp done
lemma SMADData_snpresps1:   " snpresps1  T  = snpresps1  ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp apply simp done
lemma SMADData_snpresps2:   " snpresps2  T  = snpresps2  ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp apply simp done
lemma SMADData_dthdatas1:   " dthdatas1  T  = dthdatas1  ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp apply simp done
lemma SMADData_dthdatas2:   " dthdatas2  T  = dthdatas2  ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp apply simp done
lemma SMADData_htddatas1:   " length (htddatas1  T) \<le> 1 \<Longrightarrow>   (htddatas1 ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ])) = []"
apply (cases "htddatas1 T", simp+)
done
lemma SMADData_htddatas2:   " htddatas2  T  = htddatas2  ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ])"
apply (cases "program1 T")
apply simp apply simp done
lemma nextGOPending_DeviceSMADData: "nextGOPending (  T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ] ) i = nextGOPending T i"
apply(case_tac i) apply simp+ done
lemma nextLoad_DeviceSMADData: "nextLoad (  T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ] ) i = nextLoad T i"
apply(case_tac i) apply simp+ done

(* ========================================= *)
(* Content from FixSMADGOFilled.thy *)
(* Lines 1-79 extracted *)
(* ========================================= *)

lemma devcache1_SMADGO_invariant_aux1: shows "CLEntry.block_state  (devcache1 T) = SMD \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ 0 -=reqresp ] )) \<noteq> Modified"
by simp
lemma devcache1_SMADGO_invariant_aux: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ 0 -=reqresp ] [ 0 -=devd ])) \<noteq> Modified"
by simp
lemma devcache1_SMADGO_invariant: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T [ 0 :=dd msg ] [ 0 -=reqresp ] [ 0 -=devd ])) \<noteq> Modified"
apply(subgoal_tac "CLEntry.block_state  (devcache1 (T  [ 0 :=dd msg ])) = Shared")
using devcache1_SMADGO_invariant_aux
apply blast
by simp
lemma SMADGO'_nextDTHDataPending: "nextDTHDataPending T i = nextDTHDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= SMD] [ 0 -=reqresp ]) i"
by simp
lemma SMADGO'_nextEvict: "nextEvict T i = nextEvict ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= SMD] [ 0 -=reqresp ]) i"
by simp
lemma SMADGO'_nextStore: "nextStore T i = nextStore ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= SMD] [ 0 -=reqresp ]) i"
by simp
lemma SMADGO'_not_nextGOPending: "length (reqresps1 T) \<le> 1 \<Longrightarrow> \<not> nextGOPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= SMD] [ 0 -=reqresp ]) 0"
apply(subgoal_tac " reqresps1 (T \<lparr>buffer1 := Some m\<rparr> [ 0 s= SMD]) = reqresps1 T")
apply(subgoal_tac " length (reqresps1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= SMD])) \<le> 1")
apply(case_tac "reqresps1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= SMD])")
by simp+
lemma SMADGO'_not_nextGOPending1: "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= SMD] [ 0 -=reqresp ]) = []"
apply(cases "reqresps1 T") apply simp+ done
lemma SMADGO'_nextGOPending1: "nextGOPending  T 1 = nextGOPending  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= SMD] [ 0 -=reqresp ]) 1"
by simp
lemma SMADGO'_nextGOPendingIs: "nextGOPendingIs X T 1 = nextGOPendingIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= SMD] [ 0 -=reqresp ]) 1"
by simp
lemma SMADGO'_nextHTDDataPending: "nextHTDDataPending T i = nextHTDDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= SMD] [ 0 -=reqresp ]) i"
apply  simp
done
lemma SMADGO'_HSTATE: "HSTATE X T  = HSTATE X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= SMD] [ 0 -=reqresp ]) "
apply  simp
done
lemma SMADGO'_CSTATE_otherside: "CSTATE X T 1 = CSTATE X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= SMD] [ 0 -=reqresp ]) 1"
apply  simp
done
lemma SMADGO'_CSTATE_sameside: "CSTATE SMD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= SMD] [ 0 -=reqresp ]) 0"
by simp
lemma SMADGO'_nextSnoopIs: "nextSnoopIs X T i = nextSnoopIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= SMD] [ 0 -=reqresp ]) i"
apply  simp
done
lemma SMADGO'_nextReqIs: "nextReqIs X T i = nextReqIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= SMD] [ 0 -=reqresp ]) i"
apply  simp
done
lemma SMADGO'_nextSnpRespIs: "nextSnpRespIs X T i = nextSnpRespIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= SMD] [ 0 -=reqresp ]) i"
apply  simp
done
lemma SMADGO'_nextReqIs_invariant1: shows "nextReqIs x T i = nextReqIs x ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= SMD] [ 0 -=reqresp ]) i"
apply(case_tac i)
apply simp apply simp done
lemma SMADGO'_nextReqIs_invariant_DirtyEvict: shows "nextReqIs DirtyEvict T i = nextReqIs DirtyEvict ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= SMD] [ 0 -=reqresp ]) i"
apply(case_tac i) apply simp+ done
lemma SMADGO'_nextReqIs_invariant_not_RdOwn: shows "X \<noteq> RdOwn \<Longrightarrow> nextReqIs X T i = nextReqIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= SMD] [ 0 -=reqresp ]) i"
apply(case_tac i) apply simp+ done
lemma reqs2_SMADGO: shows "reqs2 T = reqs2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= SMD] [ 0 -=reqresp ])"
by simp
lemma nextStore_SMADGO: shows "nextLoad ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= SMD] [ 0 -=reqresp ]) 0 = nextLoad T 0"
by simp
lemma nextLoad2_SMADGO: shows "nextLoad ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= SMD] [ 0 -=reqresp ]) 1 = nextLoad T 1"
by simp
lemma nextLoad_DeviceSMADGO: "nextLoad (  T \<lparr>buffer1 := Some m\<rparr> [ 0 s= SMD] [ 0 -=reqresp ] ) i = nextLoad T i"
apply(case_tac i) apply simp+ done
lemma nextGOPending_DeviceSMADGO: "nextGOPending (  T \<lparr>buffer1 := Some m\<rparr> [ 0 s= SMD] [ 0 -=reqresp ] ) 1 = nextGOPending T 1"
apply simp+
done

(* ========================================= *)
(* Content from FixSMADSnpInvFilled.thy *)
(* Lines 1-104 extracted *)
(* ========================================= *)

lemma SMADSnpInv_ModifiedM_aux2: shows " reqs1 T = reqs1 ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi])"
apply(case_tac i)
by simp+
lemma SMADSnpInv'_reqs2_invariant1_aux1: shows "reqs2 T = reqs2 ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi])"
apply(case_tac i)
by simp+
lemma SMADSnpInv'_snps2_invariant1_aux1: shows "snps2 T = snps2 ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [0 -=snp ] [ i s= mesi])"
apply(case_tac i)
by simp+
lemma SMADSnpInv'_snpresps2_invariant1_aux2: shows "snpresps2 T = snpresps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [i -=snp ] [ i s= mesi])"
apply(case_tac i)
by simp+
lemma SMADSnpInv'_snps2_invariant1 : shows "((snps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [0 -=snp ] [ i s= mesi]) \<noteq> [] \<longrightarrow>
   snpresps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [0 -=snp ] [ i s= mesi]) = []) \<and>
  (snpresps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [0 -=snp ] [ i s= mesi]) \<noteq> [] \<longrightarrow>
   snps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [0 -=snp ] [ i s= mesi]) = [])) = ((snps2 T \<noteq> [] \<longrightarrow> snpresps2 T = []) \<and> (snpresps2 T \<noteq> [] \<longrightarrow> snps2 T = []))"
apply(case_tac i)
using SMADSnpInv'_snps2_invariant1_aux1 SMADSnpInv'_snpresps2_invariant1_aux2
apply presburger
by simp
lemma SMADSnpInv'_reqresps2_invariant: shows 
  "reqresps2 ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi]) = reqresps2 T"
apply(case_tac i)
by simp+
lemma SMADSnpInv'_snoopGORules: shows  "
((snpresps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [i -=snp ] [ i s= mesi]) \<noteq> [] \<longrightarrow> 
  reqresps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [i -=snp ] [ i s= mesi]) = []) \<and> 
(reqresps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [i -=snp ] [ i s= mesi]) \<noteq> [] \<longrightarrow> 
  snpresps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [i -=snp ] [ i s= mesi]) = [])) = (
(snpresps2 T \<noteq> [] \<longrightarrow> reqresps2 T = []) \<and> (reqresps2 T \<noteq> [] \<longrightarrow> snpresps2 T = []))"
apply(subgoal_tac "snpresps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [i -=snp ] [ i s= mesi]) = snpresps2 T")
apply(subgoal_tac "reqresps2 ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [i -=snp ] [ i s= mesi]) = reqresps2 T")
apply simp
apply(case_tac i)
apply simp
apply simp
apply(case_tac i)
by simp+
lemma SMADSnpInv'_reqresps_irrelevant1: shows 
  "reqresps1 ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi]) = reqresps1 T"
apply(case_tac i)
by simp+
lemma SMADSnpInv'_dthdatas1_aux: shows 
  "dthdatas1 (   T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp rtype tid] [0 -=snp ] [ 0 s= Invalid] ) = dthdatas1 T"
by simp
lemma SMADSnpInv'_dthdatas2: shows 
  "dthdatas2 ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi]) = dthdatas2 T"
apply(case_tac i)
by simp+
lemma SMADSnpInv'_htddatas1: shows 
  "htddatas1 ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi]) = htddatas1 T"
apply(case_tac i)
by simp+
lemma SMADSnpInv'_htddatas2: shows 
  "htddatas2 ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi]) = htddatas2 T"
apply(case_tac i)
by simp+
lemma SMADSnpInv_C_msg_not_half: shows "X \<noteq> Y \<Longrightarrow> nextReqIs z ( T [ i s= X]) i \<longrightarrow> \<not> CSTATE Y ( T [ i s= X]) i"
apply(case_tac i)
by simp+
lemma SMADSnpInv_nextReqIs: shows "nextReqIs z T j = nextReqIs z ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp u w] [i -=snp ] [ i s= mesi]) j"
apply(case_tac i)
by simp+
lemma SMADSnpInv_nextGOPendingIs: shows "nextGOPendingIs gotype T i = nextGOPendingIs gotype ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi]) i"
using SMADSnpInv'_reqresps2_invariant SMADSnpInv'_reqresps_irrelevant1 nextGOPendingIs_def
by presburger
lemma SMADSnpInv_CSTATE: shows "CSTATE mesi T 1 = CSTATE mesi (T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp rtype tid] [0 -=snp ] [ 0 s= Invalid]) 1"
apply simp
done
lemma SMADSnpInv_nextEvict: shows "nextEvict T j = nextEvict  ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi]) j"
apply(case_tac i)
by simp+
lemma SMADSnpInv_nextStore: shows "nextStore T j = nextStore  ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi]) j"
apply(case_tac i)
by simp+
lemma SMADSnpInv_nextSnoopIs_otherside: shows "nextSnoopIs X T 1 = nextSnoopIs X  (T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp rtype tid] [0 -=snp ] [ 0 s= Invalid]) 1"
apply simp
done
lemma snpresps1_SMADSnpInv'_aux1: shows "snpresps1 T = snpresps1 (T [i -=snp ] [ i s= X])"
apply(case_tac i) apply simp+ done
lemma snps1_SMADSnpInv: shows " length (snps1 T) \<le> 1 \<Longrightarrow> \<not>nextSnoopPending ( T\<lparr>buffer1 := x\<rparr> [0 +=snpresp y z] [0 -=snp ] [ 0 s= mesi]) 0"
apply(case_tac "snps1 T")
apply simp apply simp done
lemma nextGOPending_DeviceSMADSnpInv: "nextGOPending ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi]) j = nextGOPending T j"
apply(case_tac j)
apply(case_tac i)
apply simp+
apply(case_tac i) apply simp+ done
lemma nextLoad_DeviceSMADSnpInv: "nextLoad ( T\<lparr>buffer1 := x\<rparr> [i +=snpresp y z] [i -=snp ] [ i s= mesi]) j = nextLoad T j"
apply(case_tac j)
apply(case_tac i)
apply simp+
apply(case_tac i) apply simp+ done

(* ========================================= *)
(* Content from FixSMAGOFilled.thy *)
(* Lines 1-337 extracted *)
(* ========================================= *)

lemma nextEvict_SMAGO_CSTATE_invariant: shows "CSTATE X T i = CSTATE X (T [ -=i 0])  i"
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac a) apply simp+ done
lemma nextStore_SMAGO_invariant_otherside: shows"nextStore T 1 = nextStore ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] ) 1"
by simp
lemma nextStore_SMAGO_invariant: shows"nextStore T 0 = nextStore ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] ) 0"
by simp
lemma HSTATE_SMAGO_invariant: shows "HSTATE X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) = 
  HSTATE X T"
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac a) apply simp+ done
lemma nextReqIs_SMAGO_IMAD_invariant2: shows 
  "nextReqIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 1 = nextReqIs X T 1"
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac "a")
apply simp
subgoal
subgoal
apply auto
done
done
by simp
lemma nextReqIs_SMAGO_IMAD_invariant1: shows 
  "nextReqIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 0 = nextReqIs X T 0"
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac "a")
apply simp
subgoal
subgoal
apply auto
done
done
by simp
lemma CSTATE_SMAGO_otherside_invariant2: shows
" CSTATE X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 1 = CSTATE X T 1"
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac "a")
apply simp
subgoal
subgoal
apply auto
done
done
by simp
lemma SMAGO_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 1 = nextGOPendingIs X T 1"
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac "a")
apply simp
subgoal
subgoal
apply auto
done
done
by simp
lemma SMAGO_nextEvict_otherside: shows 
"nextEvict  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 1 = nextEvict T 1"
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac "a")
apply simp
subgoal
subgoal
apply auto
done
done
by simp
lemma SMAGO_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 1 = nextDTHDataPending T 1"
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac "a")
apply simp
subgoal
subgoal
apply auto
done
done
by simp
lemma SMAGO_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 1 = nextSnpRespIs X T 1"
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac "a")
apply simp
subgoal
subgoal
apply auto
done
done
by simp
lemma SMAGO_nextDTHDataPending_sameside: shows 
"nextDTHDataPending  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 0 = nextDTHDataPending T 0"
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac "a")
apply simp
subgoal
subgoal
apply auto
done
done
by simp
lemma SMAGO_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 0 = nextSnpRespIs X T 0"
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac "a")
apply simp
subgoal
subgoal
apply auto
done
done
by simp
lemma devcache1_SMAGO_invariant_aux1: shows "CLEntry.block_state  (devcache1 T) = ISD \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ 0 -=reqresp ] )) \<noteq> Modified"
using MESI_State.distinct(7) devcache1_consume_reqresps1_invariant
by presburger
lemma devcache1_SMAGO_invariant_aux: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ 0 -=reqresp ] [ 0 -=devd ])) \<noteq> Modified"
using devcache1_SMAGO_invariant_aux1
by auto
lemma devcache1_SMAGO_invariant: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T [ 0 :=dd msg ] [ 0 -=reqresp ] [ 0 -=devd ])) \<noteq> Modified"
apply(subgoal_tac "CLEntry.block_state  (devcache1 (T  [ 0 :=dd msg ])) = Shared")
using devcache1_SMAGO_invariant_aux
apply blast
by simp
lemma CSTATE_SMAGO_IMAD_invariant: shows "
CSTATE Modified (T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ]  [ -=i 0]) 0"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
by simp+
lemma nextSnoopIs_SMAGO: shows 
  "nextSnoopIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) i = nextSnoopIs X T i"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp
by simp+
lemma CSTATE_SMAGO_otherside: shows "CSTATE X T 1 = CSTATE X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 1"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp
by simp+
lemma nextReqIs_SMAGO: shows "nextReqIs X T i = nextReqIs X ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) i"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply simp
by simp+
lemma SMAGO_snps2:   " snps2  T  = snps2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp apply simp done
lemma SMAGO_snps1:   " snps1  T  = snps1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp apply simp done
lemma SMAGO_reqs1:   " reqs1  T  = reqs1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp apply simp done
lemma SMAGO_reqs2:   " reqs2  T  = reqs2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp apply simp done
lemma SMAGO_reqresps2:   " reqresps2  T  = reqresps2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp apply simp done
lemma SMAGO_snpresps1:   " snpresps1  T  = snpresps1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp apply simp done
lemma SMAGO_snpresps2:   " snpresps2  T  = snpresps2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp apply simp done
lemma SMAGO_dthdatas1:   " dthdatas1  T = [] \<Longrightarrow> 
  length (dthdatas1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0])) \<le> 1"
apply (cases "program1 T")
apply simp apply simp done
lemma SMAGO_dthdatas2:   " dthdatas2  T  = dthdatas2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp apply simp done
lemma SMAGO_htddatas1:   "htddatas1 T =  (htddatas1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]))"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
using Type1State.update_convs(12) Type1State.update_convs(2) Type1State.update_convs(8) change_state_def config_differ_dev_mapping_def config_differ_dthdata_def consumeReqresp_def device_perform_op_htddatas1
apply force
by simp+
lemma SMAGO_htddatas2:   " htddatas2  T  = htddatas2  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0])"
apply (cases "program1 T")
apply simp apply simp done
lemma SMAGO_nextHTDDataPending: "nextHTDDataPending T i = 
  nextHTDDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0])  i"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp apply simp+ done
lemma snps2_SMAGO: shows "snps2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) = snps2 T"
apply(case_tac "program1 T")
by simp+
lemma snps1_SMAGO: shows "snps1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) = snps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqs2_SMAGO: shows "reqs2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) = reqs2 T"
apply(case_tac "program1 T")
by simp+
lemma reqs1_SMAGO: shows "reqs1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) = reqs1 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps2_SMAGO: shows "snpresps2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) = snpresps2 T"
apply(case_tac "program1 T")
by simp+
lemma snpresps1_SMAGO: shows "snpresps1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) = snpresps1 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps2_SMAGO: shows "reqresps2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) = reqresps2 T"
apply(case_tac "program1 T")
by simp+
lemma dthdatas2_SMAGO: shows "dthdatas2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) = dthdatas2 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas1_SMAGO: shows "htddatas1 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) = htddatas1 T"
apply(case_tac "program1 T")
by simp+
lemma htddatas2_SMAGO: shows "htddatas2 ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) = htddatas2 T"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_SMAGO_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
apply(case_tac "reqresps1 T")
by simp+
lemma reqresps1_SMAGO_aux1: shows "reqresps1 T = reqresps1 (T [ -=i 0])"
apply(case_tac "program1 T")
by simp+
lemma reqresps1_SMAGO: assumes "length (reqresps1 T) \<le> 1" shows "reqresps1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) = []"
proof -
have half_same: " (reqresps1  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified])) = reqresps1 T" by simp
have quarter_reduce: "reqresps1 (T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ]) = []"
proof -
have half_l1: "length (reqresps1  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] )) \<le> 1"
using assms half_same
by presburger
show ?thesis
using half_l1 reqresps1_SMAGO_aux
by presburger
qed
have quarter_same: "reqresps1  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ]) = reqresps1  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0])"
using reqresps1_SMAGO_aux1
by blast
show ?thesis
using quarter_reduce quarter_same
by presburger
qed
lemma SMAGO_CSTATE_aux: shows "CSTATE X T 0 = CSTATE X ( T [ 0 -=reqresp ]  [ -=i 0]) 0"
apply(case_tac "program1 T")
by simp+
lemma nextGOPending_DeviceSMAGO_other: "nextGOPending (  T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0] ) 1 = nextGOPending T 1"
apply(case_tac "program1 T") apply simp+ done
lemma nextLoad_DeviceSMAGO: "nextLoad (  T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0] ) 1 = nextLoad T 1"
apply(case_tac "program1 T") apply simp+ done
lemma nextGOPending_DeviceSMAGO: "nextGOPending (  T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0] ) 1 = nextGOPending T 1"
using nextGOPending_DeviceSMAGO_other
by blast
lemma SMAGO_nextHTDDataPending_sameside: shows 
"nextHTDDataPending  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) i = nextHTDDataPending T i"
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac "a")
apply simp
subgoal
subgoal
apply auto
done
done
by simp
lemma aux_r371: "(CSTATE IMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 1 \<or>
 CSTATE IMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 1 \<or>
 CSTATE IMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 1 \<or>
 CSTATE SMD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 1 \<or>
 CSTATE SMAD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 1 \<or>
 CSTATE SMA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 1 \<longrightarrow>
 nextStore ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 1) = 
 (CSTATE IMD T 1 \<or> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMD T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1  \<longrightarrow> nextStore T 1) "
using CSTATE_SMAGO_otherside nextStore_SMAGO_invariant_otherside nextStore_remove_op
by presburger

(* ========================================= *)
(* Content from FixSMDDataFilled.thy *)
(* Lines 1-247 extracted *)
(* ========================================= *)

lemma devcache1_SMDData_invariant_aux1: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ -=i 0] )) \<noteq> Modified"
apply(case_tac "program1 T")
apply simp+
done
lemma devcache1_SMDData_invariant_aux: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ -=i 0] [ 0 -=devd ])) \<noteq> Modified"
using devcache1_SMDData_invariant_aux1
by auto
lemma devcache1_SMDData_invariant: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])) \<noteq> Modified"
apply(subgoal_tac "CLEntry.block_state  (devcache1 (T  [ 0 :=dd msg ])) = Shared")
using devcache1_SMDData_invariant_aux
apply blast
by simp
lemma CSTATE_SMDData_otherside: shows "CSTATE X T 1 = CSTATE X ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1"
using CSTATE_def devcache2_consume_hdata1_invariant devcache2_copy_hdata1_invariant devcache2_copy_perform1_invariant devcache2_sequals1_invariant

  by (metis CSTATE_IMDData_otherside CSTATE_otherside_rule_8 INVALID_ROW_def MEM_RDS_COL_def)

lemma SMDData_Modified_aux1: shows "nextLoad T 0 \<Longrightarrow> CSTATE X T 0 = CSTATE X (T [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp+
done
lemma SMDData_Modified: shows "CSTATE Modified ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0"
apply(case_tac "program1 T")
apply simp+
done
lemma reqs1_SMDData: shows "reqs1  ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) = reqs1 T"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp+
done
lemma reqs2_SMDData: shows "reqs2  ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) = reqs2 T"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp+
done
lemma nextReqIs_SMDData: shows "nextReqIs X T i = nextReqIs X ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) i"
apply(case_tac i)
using nextReqIs_def reqs1_SMDData
apply presburger
using nextReqIs_def old.nat.distinct(2) reqs2_SMDData
by presburger
lemma SMDData_nextGOPendingIs: shows "nextGOPendingIs X T i = nextGOPendingIs X ( T [ 0 s= mesi] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) i"
apply(case_tac i)
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
apply simp
apply simp
apply simp
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
by simp+
lemma SMDData_nextEvict: shows "nextEvict T 1 = nextEvict ( T [ 0 s= mesi] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
apply simp
apply simp
apply simp
done
lemma SMDData_nextLoad: shows "nextLoad T 1 = nextLoad ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
apply simp
apply simp
apply simp
done
lemma SMDData_HSTATE: shows "(HSTATE X ( T [ 0 s= Modified] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) = HSTATE X T"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
apply simp
apply simp
apply simp
done
lemma SMDData_HSTATES: shows "(HSTATE MAD ( T [ 0 s= Modified] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or>
  HSTATE MA ( T [ 0 s= Modified] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or>
  HSTATE MD ( T [ 0 s= Modified] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or>
  HSTATE ModifiedM ( T [ 0 s= Modified] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) = (HSTATE MAD T \<or> HSTATE MA T \<or> HSTATE MD T \<or> HSTATE ModifiedM T)"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
apply simp
apply simp
apply simp
done
lemma SMDData_nextSnoopIs: shows "nextSnoopIs  X T i = nextSnoopIs X ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) i"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
apply simp
apply simp
apply simp
done
lemma SMDData_nextStore_otherside: shows "nextStore T 1 = nextStore ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1"
apply(case_tac "program1 T")
apply simp
apply(case_tac a)
apply simp
apply(case_tac x2)
apply(case_tac n)
apply simp
apply simp
apply simp
apply simp
done
lemma nextGOPending_DeviceSMDData: "nextGOPending (  T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ] ) i = nextGOPending T i"
apply(case_tac i)
using device_perform_op_reqresps1 nextGOPending_def
apply presburger
using device_perform_op_reqresps2 nextGOPending_def
by presburger
lemma nextLoad_DeviceSMDData: "nextLoad (  T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ] ) 1 = nextLoad T 1"
apply(case_tac "program1 T")
apply simp+
done

end
