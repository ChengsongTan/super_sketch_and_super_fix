theory Testing_cursor 
  imports  "../Super_Sketch/Super_Sketch_cursor"  AllBackgroundInvariants  
begin

sledgehammer_params [dont_minimize, dont_try0, timeout = 5]

(* ==========================================
   CONTRACT TESTS for Double_Sketch Enhancement
   ========================================== *)

(* T004: Contract test for FR-001 (adsimp parameter output fix) *)
lemma test_adsimp_parameter_inclusion:
  "CSTATE Invalid T 0 \<and> nextLoad T 0 \<longrightarrow> 
   SWMR (T [0 +=rdreq RdShared] [0 s= ISAD]) \<and>
   C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (T [0 +=rdreq RdShared] [0 s= ISAD]) \<and>
   H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (T [0 +=rdreq RdShared] [0 s= ISAD])"
proof -
  (* This test should show that adsimp method appears in ALL relevant subgoals *)
  (* Expected: Currently will show missing blast method in some subgoals *)
  (* After fix: blast should appear in all relevant subgoals *)
  double_sketch simp [auto] [blast]
  (* This test demonstrates the current bug where blast is missing in some subgoals *)

(* T005: Contract test for FR-002 (third bracket pair acceptance) *)
(* This test should now PASS with enhanced parser *)
lemma test_third_bracket_parsing:
  "True"
proof -
  (* This should parse without error with enhanced parser *)
  double_sketch_cursor simp [auto] [blast] [intro_locales clarsimp]
  sorry (* Proof content not important, just testing parsing *)
qed

(* T006: Contract test for FR-003 (fallback solving strategy) *)  
lemma test_fallback_solving_strategy:
  "(\<forall>i. HSTATE MA T i \<longrightarrow> \<not>HSTATE MD T i) \<and> 
   (\<forall>i. CSTATE Modified T i \<longrightarrow> \<not>CSTATE Invalid T i) \<longrightarrow>
   SWMR T"
proof -
  (* This goal is designed to potentially fail with simp+sledgehammer *)
  (* But should succeed with intro_locales+clarsimp fallback *)
  (* Now enhanced with fallback strategy implemented *)
  double_sketch_cursor auto [simp] [blast] [intro_locales clarsimp]
  (* Should show fallback solving attempt when primary methods fail *)
  sorry (* Expected to show improved solving with fallback strategy *)

(* T007: Integration test for backward compatibility *)
lemma test_backward_compatibility:
  "CSTATE Invalid T 0 \<and> nextLoad T 0 \<longrightarrow> SWMR (T [0 +=rdreq RdShared] [0 s= ISAD])"
proof -
  (* This test verifies existing double_sketch continues working *)
  (* Should PASS both before and after implementation - regression baseline *)  
  double_sketch simp [auto] [blast]
  (* This should work correctly and continue working after enhancements *)

(* Additional comprehensive tests for enhanced functionality *)

(* T015: Performance validation *)
lemma test_performance_baseline:
  "CSTATE Invalid T 0 \<and> nextLoad T 0 \<longrightarrow> SWMR (T [0 +=rdreq RdShared] [0 s= ISAD])"
proof -
  (* Test both original and enhanced versions for timing comparison *)
  (* Original version: *)
  double_sketch simp [auto] [blast]
  (* Enhanced version should maintain similar performance *)
  (* double_sketch_cursor simp [auto] [blast] *)

(* T016: Integration workflow validation *)  
lemma test_integration_workflow:
  "CSTATE Invalid T 0 \<and> nextLoad T 0 \<longrightarrow> 
   SWMR (T [0 +=rdreq RdShared] [0 s= ISAD]) \<and>
   C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (T [0 +=rdreq RdShared] [0 s= ISAD])"
proof -
  (* Test enhanced double_sketch in realistic proof context *)
  double_sketch_cursor simp [auto] [blast] [intro_locales clarsimp]
  (* Should integrate properly with existing Super_Fix workflow *)

(* Enhanced adsimp parameter inclusion test *)
lemma test_enhanced_adsimp_inclusion:
  "CSTATE Invalid T 0 \<and> nextLoad T 0 \<longrightarrow> 
   SWMR (T [0 +=rdreq RdShared] [0 s= ISAD]) \<and>
   C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (T [0 +=rdreq RdShared] [0 s= ISAD]) \<and>
   H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (T [0 +=rdreq RdShared] [0 s= ISAD])"
proof -
  (* This should now show blast method in ALL relevant subgoals with fixed implementation *)
  double_sketch_cursor simp [auto] [blast]
  (* Expected: blast appears in all relevant subgoals, no missing methods *)

(* Fallback strategy comprehensive test *)
lemma test_comprehensive_fallback:
  "(\<forall>i. HSTATE MA T i \<longrightarrow> \<not>HSTATE MD T i) \<and> 
   (\<forall>i. CSTATE Modified T i \<longrightarrow> \<not>CSTATE Invalid T i) \<and>
   (\<forall>i. nextLoad T i \<longrightarrow> CSTATE Invalid T i) \<longrightarrow>
   SWMR T \<and> (\<forall>i. \<not>CSTATE Modified T i)"
proof -
  (* Complex goal designed to require fallback strategy *)
  double_sketch_cursor auto [simp] [blast] [intro_locales clarsimp]
  (* Should demonstrate fallback solving when primary methods insufficient *)

end
