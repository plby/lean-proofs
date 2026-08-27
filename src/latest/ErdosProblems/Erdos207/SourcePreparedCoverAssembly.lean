/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourcePreparedReserveData
import ErdosProblems.Erdos207.SourceInternalStageBudget
import ErdosProblems.Erdos207.SourceInternalStageAssembly
import ErdosProblems.Erdos207.SourceLinkStageBudget

/-! # Compose the actual prepared preliminary, internal and final link kernels -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem SourcePreparedReserveData.exists_completed_cover
    {Omega Xi V : Type*} [Fintype Omega] [DecidableEq Omega] [Fintype Xi] [DecidableEq Xi]
    [Fintype V] [DecidableEq V] {ell q h : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell} {i : Fin ell}
    {Gamma : SimpleGraph V} {bank ambient : TripleSystemOn V}
    {G : Omega → SimpleGraph V} {A I D B : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool} {p eta xi xi' r C beta eta0 Cout : ℝ≥0}
    {epsilon theta : ℝ}
    (data : SourcePreparedReserveData L W i (absorberErdosForbiddenConfigurationsOn q bank)
      Gamma ambient G A I D B bits p eta xi r C beta eta0 epsilon theta
      ⌊r^2*p^2*eta*(W.U i.succ).card/8⌋₊ h)
    (Kpre : Omega → FiniteLaw Xi) (pre : Omega → Xi → TripleSystemOn V)
    (survival point constant delta : ℝ≥0)
    (internal : SourceInternalStageBudget W i q bank p eta r C beta survival point constant delta Cout)
    (link : SourceLinkStageBudget q h W i bank p r Cout (beta+delta) eta xi xi')
    (hdegreeCut : link.d = ⌊r^2*p^2*eta*(W.U i.succ).card/256⌋₊)
    (hdegreeError : internal.degreeError ≤ link.degreeError)
    (hreference : epsilon = (link.referenceTolerance : ℝ))
    (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1)
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hC : 1 ≤ C) (hconstant : 1 ≤ constant) (hh : 1 ≤ h)
    (hnonempty : ∀ a, (W.U a).Nonempty) (hsource : HasAbsorberSourcePrefixBounds q bank W)
    (hmixed : ∀ omega, IsGraphMixedProductBound (Kpre omega) (pre omega)
      (reserveProtectedOuterGraph (G omega) (W.U i.succ)
        (reserveEdges (G omega) (W.U i.succ) (bits omega))) survival point constant delta)
    (hpre : ∀ omega, (Kpre omega).SupportedOn fun z ↦
      pre omega z ⊆ A omega ∧ IsPackingOn ((I omega ∪ D omega) ∪ pre omega z) ∧
        Disjoint (I omega ∪ D omega) (pre omega z) ∧
        AvoidsForbidden ((I omega ∪ D omega) ∪ pre omega z) (absorberSourceFamily q bank) ∧
        pre omega z ⊆ reserveProtectedAvailable (reserveEdges (G omega) (W.U i.succ) (bits omega)) (A omega) ∧
        TrianglesMeetAtMostOne (W.U i.succ) (pre omega z)) :
    ∃ law : FiniteLaw (MasterStateOn V),
      IsResidualCompressedMasterLaw law W i.succ (absorberErdosForbiddenConfigurationsOn q bank)
        Gamma ambient p eta xi' (4*max (Cout^5) 1) (beta+delta) h := by
  let F := fun j ↦ absorberInducedConfigurationsOn q j bank
  let old := fun omega ↦ I omega ∪ D omega
  let mu := r^2*p^2*eta*(W.U i.succ).card
  let Kint := correlatedRawInternalKernel W i (absorberSourceFamily q bank) G A old pre bits ⌊mu/32⌋₊
  let intAdded := correlatedRawInternalAdded old pre
  let kernel := fun omega ↦ (Kpre omega).jointBind (Kint omega)
  let added := fun omega sample ↦ preliminaryInternalCombinedAdded (pre omega) (intAdded omega) sample
  let joint := L.jointBind kernel
  let reserve := fun sample : Omega × (Xi × InternalEdgeGreedyStateOn V) ↦
    preliminaryAugmentedReserve (G sample.1) (W.U i.succ)
      (reserveEdges (G sample.1) (W.U i.succ) (bits sample.1)) (added sample.1 sample.2)
  let Success := fun sample : Omega × (Xi × InternalEdgeGreedyStateOn V) ↦ sample.2.2.failed = false
  have hpreBase : ∀ omega, (Kpre omega).SupportedOn fun z ↦ pre omega z ⊆ A omega ∧
      IsPackingOn (old omega ∪ pre omega z) ∧ Disjoint (old omega) (pre omega z) ∧
      AvoidsForbidden (old omega ∪ pre omega z) (absorberSourceFamily q bank) := by
    intro omega z hz
    have hg := hpre omega z hz
    exact ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1⟩
  have hinitial : ∀ omega, 0 < L.mass omega → ∀ T ∈ A omega,
      ¬ CompletesForbidden ((Icc 4 q).biUnion F) (I omega) T := by
    intro omega _ T hT hc
    obtain ⟨S, hS, hTS, hrest⟩ := hc
    exact (data.frame.stage omega).to_absorberSource.2.2.2.2.2.2 T hT
      ⟨S, hS, hTS, hrest.trans subset_union_left⟩
  obtain ⟨hpos, hlower, hreserved, hdegree, links, hlinks⟩ :=
    data.distribution.exists_source_internal_preparation i (Icc 4 q) F G A I D bits Gamma Kpre pre
      survival point constant delta internal.rate mu internal.alpha internal.factor internal.epsilon internal.error
      internal.degreeMoment (fun _ ↦ internal.leftMoment) (fun _ ↦ sourcePrefixY q i.val)
      (sourcePrefixZ q bank i.val) (fun _ ↦ internal.leftError) hp hp1 hr hr1 hC hconstant
      internal.factor_one internal.mu_large internal.alpha_le_one internal.rate_le_reserve internal.epsilon_pos
      hnonempty internal.point_charge internal.combined_point internal.combined_rate internal.left_cap
      internal.degree_moment (fun j hj ↦ hsource.at_stage i.castSucc j (mem_Icc.mp hj).1 (mem_Icc.mp hj).2)
      internal.source_scale internal.left_scalar (fun omega _ ↦ hmixed omega)
      (fun omega _ ↦ data.frame.support omega) (fun omega _ ↦ data.frame.graph_le omega)
      (fun omega _ ↦ (data.frame.stage omega).2.2.2.2.1)
      (fun omega _ ↦ (data.frame.stage omega).2.2.2.2.2.1)
      (fun omega _ ↦ data.frame.even omega) (fun omega _ ↦ (data.frame.stage omega).1)
      (fun omega _ ↦ hpreBase omega) hinitial
      (fun omega _ z hz ↦ (hpre omega z hz).2.2.2.2.1)
      (fun omega _ z hz ↦ (hpre omega z hz).2.2.2.2.2)
      (fun omega _ ↦ (data.reserve_good omega).1) internal.error_lt_one internal.error_bound
  let goodLaw := joint.conditionOn Success hpos
  have hstrong : IsResidualReserveStronglyWellDistributed goodLaw W i.castSucc Gamma
      (fun sample ↦ I sample.1) (fun sample ↦ D sample.1 ∪ added sample.1 sample.2)
      reserve p r Cout (beta+delta) := hreserved.mono internal.conditioned_constant le_rfl
  have hdegreeFinal : goodLaw.probability (fun sample ↦ ¬ PreliminaryResidualDegreeGood
      (reserveProtectedOuterGraph (G sample.1) (W.U i.succ)
        (reserveEdges (G sample.1) (W.U i.succ) (bits sample.1))) (W.U i.succ)
        (pre sample.1 sample.2.1) link.d) ≤ link.degreeError := by
    rw [hdegreeCut]
    exact hdegree.trans (internal.conditioned_degree.trans hdegreeError)
  have hpositive : joint.SupportedOn fun sample ↦ 0 < joint.mass sample := fun _ hm ↦ hm
  have hpositiveGood := hpositive.conditionOn hpos
  have hstructure : goodLaw.SupportedOn fun sample ↦
      Disjoint (pre sample.1 sample.2.1) (intAdded sample.1 sample.2.1 sample.2.2) ∧
      NewTrianglesUseScheduledOuterEdges (W.U i.succ)
        (preliminaryResidualInternalEdges (G sample.1) (W.U i.succ) (pre sample.1 sample.2.1))
        (pre sample.1 sample.2.1) (added sample.1 sample.2) ∧
      pre sample.1 sample.2.1 ⊆ reserveProtectedAvailable
        (reserveEdges (G sample.1) (W.U i.succ) (bits sample.1)) (A sample.1) := by
    intro sample hm
    have hmasses := (L.jointBind_mass_pos_iff kernel sample.1 sample.2).mp (hpositiveGood sample hm)
    have hpreMass := ((Kpre sample.1).jointBind_mass_pos_iff (Kint sample.1) sample.2.1 sample.2.2).mp hmasses.2
    have hs := correlatedRawInternalKernel_supported_structure W i (absorberSourceFamily q bank) G A old pre bits
      ⌊mu/32⌋₊ (internal_cover_rounded_budgets mu internal.mu_large).1 Kpre sample.1
      (data.frame.stage sample.1).2.2.2.2.1 (hpreBase sample.1) sample.2 hmasses.2
    exact ⟨hs.2.2.2.1, hs.2.2.2.2.2, (hpre sample.1 sample.2.1 hpreMass.1).2.2.2.2.1⟩
  apply link.finish (G := fun sample ↦ G sample.1) (A := fun sample ↦ A sample.1)
    (I := fun sample ↦ I sample.1) (D := fun sample ↦ D sample.1)
    (P := fun sample ↦ pre sample.1 sample.2.1)
    (Q := fun sample ↦ intAdded sample.1 sample.2.1 sample.2.2)
    (R := fun sample ↦ added sample.1 sample.2) (bits := fun sample ↦ bits sample.1)
    hp hp1 hr hr1 heta heta1 internal.out_pos hh hnonempty hsource hstrong links
  · intro sample hm
    have hs := hlinks sample hm
    exact ⟨hs.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1⟩
  · exact fun sample _ ↦ data.frame.even sample.1
  · exact fun sample _ ↦ data.frame.stage sample.1
  · intro sample hm
    have hs := hlinks sample hm
    exact ⟨hs.2.2.2.2.2.1, hs.2.2.2.2.2.2.1⟩
  · exact fun sample hm ↦ (hlinks sample hm).2.2.2.2.2.2.2
  · exact fun sample _ ↦ data.frame.graph_le sample.1
  · exact fun sample _ ↦ data.frame.support sample.1
  · exact fun sample _ ↦ data.frame.available sample.1
  · exact fun sample _ ↦ data.frame.selected sample.1
  · exact fun sample _ ↦ data.frame.cover sample.1
  · exact fun sample hm ↦ (hstructure sample hm).2.2
  · exact fun _ _ ↦ rfl
  · exact fun sample hm ↦ (hstructure sample hm).1
  · exact fun sample hm ↦ (hstructure sample hm).2.1
  · intro sample _
    simpa only [hreference] using (data.reserve_good sample.1).2
  · exact hdegreeFinal

end

end Erdos207
