/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CorrelatedRawInternalSourceSuccess
import ErdosProblems.Erdos207.InternalEdgeIntermediateLaw
import ErdosProblems.Erdos207.LocalInnerDegreeLoss

/-! # Successful actual correlated internal laws supply the full intermediate link state -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem condition_correlatedRawInternal_success
    {Omega Xi V : Type*} [Fintype Omega] [DecidableEq Omega] [Fintype Xi] [DecidableEq Xi]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Omega) (W : Vortex V ell) (i : Fin ell) (F : ForbiddenFamilyOn V)
    (G : Omega → SimpleGraph V) (A initial later : Omega → TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool) (Gamma : SimpleGraph V)
    (Kpre : Omega → FiniteLaw Xi) (pre : Omega → Xi → TripleSystemOn V)
    (threshold : ℕ) (hthreshold : 0 < threshold) (p r C beta error : ℝ≥0) (herror : error < 1)
    (heven : ∀ omega, 0 < L.mass omega → ∀ v, Even ((neighborsIn (G omega) univ v).card))
    (hGleave : ∀ omega, 0 < L.mass omega → G omega ≤ leaveGraph (initial omega ∪ later omega))
    (htri : ∀ omega, 0 < L.mass omega → ConsistsOfTriangles (G omega) (A omega))
    (hdisjoint : ∀ omega, 0 < L.mass omega → Disjoint (initial omega) (later omega))
    (hpre : ∀ omega, 0 < L.mass omega → (Kpre omega).SupportedOn fun xi ↦ pre omega xi ⊆ A omega ∧
      IsPackingOn ((initial omega ∪ later omega) ∪ pre omega xi) ∧
      Disjoint (initial omega ∪ later omega) (pre omega xi) ∧
      AvoidsForbidden ((initial omega ∪ later omega) ∪ pre omega xi) F)
    (hmeet : ∀ omega, 0 < L.mass omega → (Kpre omega).SupportedOn fun xi ↦
      TrianglesMeetAtMostOne (W.U i.succ) (pre omega xi)) :
    let old := fun omega ↦ initial omega ∪ later omega
    let Kint := correlatedRawInternalKernel W i F G A old pre bits threshold
    let intAdded := correlatedRawInternalAdded old pre
    let kernel := fun omega ↦ (Kpre omega).jointBind (Kint omega)
    let added := fun omega sample ↦ preliminaryInternalCombinedAdded (pre omega) (intAdded omega) sample
    let joint := L.jointBind kernel
    let reserve := fun sample : Omega × (Xi × InternalEdgeGreedyStateOn V) ↦
      preliminaryAugmentedReserve (G sample.1) (W.U i.succ)
        (reserveEdges (G sample.1) (W.U i.succ) (bits sample.1)) (added sample.1 sample.2)
    let Success := fun sample : Omega × (Xi × InternalEdgeGreedyStateOn V) ↦ sample.2.2.failed = false
    IsResidualReserveStronglyWellDistributed joint W i.castSucc Gamma
      (jointInitial initial) (jointLater later added) reserve p r C beta →
    joint.probability (fun sample ↦ sample.2.2.failed = true) ≤ error →
    ∃ hpos : 0 < joint.probability Success,
      1 - error ≤ joint.probability Success ∧
      IsResidualReserveStronglyWellDistributed (joint.conditionOn Success hpos) W i.castSucc Gamma
        (jointInitial initial) (jointLater later added) reserve p r (C / (1 - error)) beta ∧
      ∃ links : Omega × (Xi × InternalEdgeGreedyStateOn V) → {x : V // x ∉ W.U i.succ} → BipartiteLink V,
        (joint.conditionOn Success hpos).SupportedOn fun sample ↦
          IsIntermediateLinkState (G sample.1) (W.U i.succ) (A sample.1)
            (initial sample.1) (later sample.1) (added sample.1 sample.2) (links sample) ∧
          (∀ o, (links sample o).center = outsideVertexEmbedding (W.U i.succ) o) ∧
          (∀ o, (links sample o).left ⊆ W.U i.succ) ∧
          (∀ o, (links sample o).right ⊆ W.U i.succ) ∧
          (∀ o, (links sample o).SpokesIn (reserve sample)) ∧
          IsPackingOn (initial sample.1 ∪ (later sample.1 ∪ added sample.1 sample.2)) ∧
          AvoidsForbidden (initial sample.1 ∪ (later sample.1 ∪ added sample.1 sample.2)) F ∧
          TrianglesMeetAtMostOne (W.U i.succ) (added sample.1 sample.2) := by
  dsimp only
  let old := fun omega ↦ initial omega ∪ later omega
  let Kint := correlatedRawInternalKernel W i F G A old pre bits threshold
  let intAdded := correlatedRawInternalAdded old pre
  let kernel := fun omega ↦ (Kpre omega).jointBind (Kint omega)
  let added := fun omega sample ↦ preliminaryInternalCombinedAdded (pre omega) (intAdded omega) sample
  let joint := L.jointBind kernel
  let reserve := fun sample : Omega × (Xi × InternalEdgeGreedyStateOn V) ↦
    preliminaryAugmentedReserve (G sample.1) (W.U i.succ)
      (reserveEdges (G sample.1) (W.U i.succ) (bits sample.1)) (added sample.1 sample.2)
  let Success := fun sample : Omega × (Xi × InternalEdgeGreedyStateOn V) ↦ sample.2.2.failed = false
  let Full := fun sample : Omega × (Xi × InternalEdgeGreedyStateOn V) ↦
    initial sample.1 ∪ (later sample.1 ∪ added sample.1 sample.2)
  intro hstrong hfailure
  have hnot : joint.probability (fun sample ↦ ¬ Success sample) ≤ error := by
    simpa only [Success, Bool.not_eq_false] using hfailure
  have hlower : 1 - error ≤ joint.probability Success := by
    rw [joint.probability_not Success] at hnot
    exact tsub_le_iff_tsub_le.mp hnot
  have hden : 0 < 1 - error := tsub_pos_iff_lt.mpr herror
  have hpos : 0 < joint.probability Success := hden.trans_le hlower
  let goodLaw := joint.conditionOn Success hpos
  have hstructure := fun omega hmass ↦ correlatedRawInternalKernel_supported_structure
    W i F G A old pre bits threshold hthreshold Kpre omega (hGleave omega hmass) (hpre omega hmass)
  have hrawSupport : joint.SupportedOn fun sample ↦
      RawResidualInternalStructure W i F (fun z : Omega × Xi ↦ G z.1)
        (fun z ↦ pairSafeAvailable (A z.1) (correlatedRawInternalStart old pre z))
        (correlatedRawInternalStart old pre) (fun z ↦ bits z.1) threshold (sample.1, sample.2.1) sample.2.2 := by
    intro sample hmass
    have hmasses := (L.jointBind_mass_pos_iff kernel sample.1 sample.2).mp hmass
    have hinner := ((Kpre sample.1).jointBind_mass_pos_iff (Kint sample.1)
      sample.2.1 sample.2.2).mp hmasses.2
    exact rawResidualInternalKernel_supported_structure W i F (fun z : Omega × Xi ↦ G z.1)
      (fun z ↦ pairSafeAvailable (A z.1) (correlatedRawInternalStart old pre z))
      (correlatedRawInternalStart old pre) (fun z ↦ bits z.1) threshold hthreshold
      (sample.1, sample.2.1) sample.2.2 hinner.2
  have hpositive : joint.SupportedOn fun sample ↦ 0 < joint.mass sample := fun _ hmass ↦ hmass
  have hpositiveGood := hpositive.conditionOn hpos
  have hsuccess := joint.conditionOn_supported Success hpos
  have hrawGood := hrawSupport.conditionOn hpos
  have hclass : goodLaw.SupportedOn fun sample ↦ sample.2.2.chosen = Full sample := by
    intro sample hmass
    have hraw := hrawGood sample hmass
    dsimp only [Full, added, preliminaryInternalCombinedAdded, intAdded, correlatedRawInternalAdded,
      rawResidualInternalAdded, correlatedRawInternalStart, old]
    rw [← union_assoc, ← union_assoc]
    exact (union_sdiff_of_subset hraw.1.1.initial_subset).symm
  have hready : goodLaw.SupportedOn (InternalOutcomeReady (fun sample ↦ G sample.1) (W.U i.succ)
      reserve F (fun sample ↦ A sample.1) (fun sample ↦ initial sample.1) (fun sample ↦ later sample.1)
      (fun sample ↦ added sample.1 sample.2) Full) := by
    intro sample hmass
    have hmasses := (L.jointBind_mass_pos_iff kernel sample.1 sample.2).mp (hpositiveGood sample hmass)
    have hS := hstructure sample.1 hmasses.1 sample.2 hmasses.2
    have hcover := (hrawGood sample hmass).complete_internalCover (hsuccess sample hmass)
    refine ⟨heven sample.1 hmasses.1, hGleave sample.1 hmasses.1, htri sample.1 hmasses.1,
      hS.1, disjoint_union_right.mpr ⟨hdisjoint sample.1 hmasses.1,
        hS.2.2.1.mono_left subset_union_left⟩, ?_, GreedyReachable.refl, subset_union_left, ?_, ?_⟩
    · simpa only [old, union_assoc] using hS.2.1
    · intro e he
      rw [← hclass sample hmass]
      exact hcover.2.2.2 e he
    · exact coversCrossingOutsideReserve_preliminaryAugmentedReserve (G sample.1) (W.U i.succ)
        (reserveEdges (G sample.1) (W.U i.succ) (bits sample.1)) (added sample.1 sample.2)
  let links := internalOutcomeResidualLinks (fun sample ↦ G sample.1) (W.U i.succ) reserve F
    (fun sample ↦ A sample.1) (fun sample ↦ initial sample.1) (fun sample ↦ later sample.1)
    (fun sample ↦ added sample.1 sample.2) Full
  refine ⟨hpos, hlower, (hstrong.conditionOn Success hpos).mono
    (div_le_div_of_nonneg_left zero_le hden hlower) le_rfl, links, ?_⟩
  intro sample hmass
  have hlink := internalOutcomeResidualLinks_spec (hready sample hmass)
  have hstage : internalStageFamily (initial sample.1) (later sample.1)
      (added sample.1 sample.2) (Full sample) = added sample.1 sample.2 := by
    simp only [internalStageFamily, Full, Finset.sdiff_self, Finset.union_empty]
  rw [hstage] at hlink
  have hmasses := (L.jointBind_mass_pos_iff kernel sample.1 sample.2).mp (hpositiveGood sample hmass)
  have hinner := ((Kpre sample.1).jointBind_mass_pos_iff (Kint sample.1)
    sample.2.1 sample.2.2).mp hmasses.2
  have hS := hstructure sample.1 hmasses.1 sample.2 hmasses.2
  refine ⟨hlink.1, hlink.2.1, hlink.2.2.2.1, hlink.2.2.2.2.1, hlink.2.2.2.2.2,
    ?_, ?_, ?_⟩
  · simpa only [old, union_assoc] using hS.2.1
  · simpa only [old, union_assoc] using hS.2.2.2.2.1
  · apply hS.2.2.2.2.2.meetAtMostOne (hmeet sample.1 hmasses.1 sample.2.1 hinner.1)
    intro e he
    exact (mem_internalOuterEdges_iff.mp
      (preliminaryResidualInternalEdges_subset_internalOuterEdges (G sample.1) (W.U i.succ)
        (pre sample.1 sample.2.1) he)).2

end

end Erdos207
