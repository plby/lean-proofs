/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RawInternalStructureComposition
import ErdosProblems.Erdos207.ResidualReserveRestriction

/-! # Source left moments prove success of the actual correlated raw internal process -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem correlatedRawInternal_failure_probability_le
    {Omega Xi V : Type*} [Fintype Omega] [DecidableEq Omega] [Fintype Xi] [DecidableEq Xi]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Omega) (W : Vortex V ell) (i : Fin ell)
    (orders : Finset ℕ) (F : ℕ → ForbiddenFamilyOn V)
    (G : Omega → SimpleGraph V) (A initial later : Omega → TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool) (Gamma : SimpleGraph V)
    (Kpre : Omega → FiniteLaw Xi) (pre : Omega → Xi → TripleSystemOn V)
    (p r C beta survival point constant preError rate mu epsilon : ℝ≥0)
    (degreeMoment : ℕ) (s : ℕ → ℕ) (y z error : ℕ → ℝ≥0)
    (hmu : 512 ≤ mu) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1) (hC : 1 ≤ C)
    (hepsilon : 0 < epsilon) (hU : (W.U i.succ).Nonempty)
    (hcap : epsilon * p ^ 2 * r ^ 2 * (W.U i.succ).card ≤ ⌈mu / 128⌉₊)
    (hdegreeMoment : 2 * degreeMoment ≤ ⌊mu / 256⌋₊ + 1)
    (hsource : ∀ j ∈ orders, SourceVortexWellSpread (W.prefix i.castSucc) j (F j) (y j) (z j))
    (hscale : ∀ j ∈ orders, z j ≤ y j * r ^ 2 * p ^ 3 * (W.U i.succ).card)
    (hscalar : ∀ j ∈ orders,
      sourceLeftFailureBound i.val j (s j) (Fintype.card V) p r C beta (y j)
        (epsilon / (orders.card + 1 : ℝ≥0)) (W.U i.succ).card ≤ error j)
    (hmixed : ∀ omega, 0 < L.mass omega → IsGraphMixedProductBound (Kpre omega) (pre omega)
      (reserveProtectedOuterGraph (G omega) (W.U i.succ)
        (reserveEdges (G omega) (W.U i.succ) (bits omega))) survival point constant preError)
    (hRate : constant * survival ≤ rate)
    (hGsupport : ∀ omega, 0 < L.mass omega → GraphSupportedOn (G omega) (W.U i.castSucc : Set V))
    (hbase : ∀ omega, 0 < L.mass omega → G omega ≤ Gamma)
    (hGleave : ∀ omega, 0 < L.mass omega → G omega ≤ leaveGraph (initial omega ∪ later omega))
    (hdisjoint : ∀ omega, 0 < L.mass omega → Disjoint (initial omega) (later omega))
    (hpre : ∀ omega, 0 < L.mass omega → (Kpre omega).SupportedOn fun xi ↦ pre omega xi ⊆ A omega ∧
      IsPackingOn ((initial omega ∪ later omega) ∪ pre omega xi) ∧
      Disjoint (initial omega ∪ later omega) (pre omega xi) ∧
      AvoidsForbidden ((initial omega ∪ later omega) ∪ pre omega xi) (orders.biUnion F))
    (hlevel : ∀ omega, 0 < L.mass omega → ∀ T ∈ A omega, (W.prefix i.castSucc).level T = Fin.last i.val)
    (hinitial : ∀ omega, 0 < L.mass omega → ∀ T ∈ A omega,
      ¬ CompletesForbidden (orders.biUnion F) (initial omega) T)
    (hprotected : ∀ omega, 0 < L.mass omega → (Kpre omega).SupportedOn fun xi ↦
      pre omega xi ⊆ reserveProtectedAvailable (reserveEdges (G omega) (W.U i.succ) (bits omega)) (A omega))
    (hreserve : ∀ omega, 0 < L.mass omega →
      InternalReserveSupplyGood (G omega) (A omega) (W.U i.succ) ⌊mu / 8⌋₊ (bits omega)) :
    let old := fun omega ↦ initial omega ∪ later omega
    let Kint := correlatedRawInternalKernel W i (orders.biUnion F) G A old pre bits ⌊mu / 32⌋₊
    let intAdded := correlatedRawInternalAdded old pre
    let kernel := fun omega ↦ (Kpre omega).jointBind (Kint omega)
    let added := fun omega sample ↦ preliminaryInternalCombinedAdded (pre omega) (intAdded omega) sample
    IsResidualReserveStronglyWellDistributed (L.jointBind kernel) W i.castSucc Gamma
      (jointInitial initial) (jointLater later added)
      (fun sample ↦ preliminaryAugmentedReserve (G sample.1) (W.U i.succ)
        (reserveEdges (G sample.1) (W.U i.succ) (bits sample.1)) (added sample.1 sample.2)) p r C beta →
    (L.jointBind kernel).probability (fun sample ↦ sample.2.2.failed = true) ≤
      sourcePreliminaryDegreeFailure (Fintype.card V) (W.U i.castSucc).card ⌊mu / 256⌋₊
        degreeMoment rate constant preError + (Fintype.card V : ℝ≥0) ^ 2 * ∑ j ∈ orders, error j := by
  dsimp only
  let old := fun omega ↦ initial omega ∪ later omega
  let Kint := correlatedRawInternalKernel W i (orders.biUnion F) G A old pre bits ⌊mu / 32⌋₊
  let intAdded := correlatedRawInternalAdded old pre
  let kernel := fun omega ↦ (Kpre omega).jointBind (Kint omega)
  let added := fun omega sample ↦ preliminaryInternalCombinedAdded (pre omega) (intAdded omega) sample
  let joint := L.jointBind kernel
  let finalLater := jointLater later added
  let reserve := fun sample : Omega × (Xi × InternalEdgeGreedyStateOn V) ↦
    reserveEdges (G sample.1) (W.U i.succ) (bits sample.1)
  let DegreeGood := fun sample : Omega × (Xi × InternalEdgeGreedyStateOn V) ↦
    PreliminaryResidualDegreeGood (reserveProtectedOuterGraph (G sample.1) (W.U i.succ) (reserve sample))
      (W.U i.succ) (pre sample.1 sample.2.1) ⌊mu / 256⌋₊
  let LeftGood := fun sample : Omega × (Xi × InternalEdgeGreedyStateOn V) ↦
    SourceLeftCaps (W.prefix i.castSucc) (orders.biUnion F) (W.U i.succ) Gamma
      (initial sample.1) (finalLater sample) (reserve sample) (epsilon * p ^ 2 * r ^ 2 * (W.U i.succ).card)
  intro hstrong
  have hthreshold := (internal_cover_rounded_budgets mu hmu).1
  have hstructure := fun omega hmass ↦ correlatedRawInternalKernel_supported_structure
    W i (orders.biUnion F) G A old pre bits ⌊mu / 32⌋₊ hthreshold Kpre omega
    (hGleave omega hmass) (hpre omega hmass)
  have hdis : joint.SupportedOn fun sample ↦ Disjoint (initial sample.1) (finalLater sample) := by
    intro sample hmass
    have hmasses := (L.jointBind_mass_pos_iff kernel sample.1 sample.2).mp hmass
    have hstruct := hstructure sample.1 hmasses.1 sample.2 hmasses.2
    exact disjoint_union_right.mpr ⟨hdisjoint sample.1 hmasses.1,
      hstruct.2.2.1.mono_left subset_union_left⟩
  have hreserved : IsResidualReserveStronglyWellDistributed joint W i.castSucc Gamma
      (jointInitial initial) finalLater reserve p r C beta := by
    apply hstrong.restrict_reserve
    intro sample _
    exact subset_union_left
  have hleft : joint.probability (fun sample ↦ ¬ LeftGood sample) ≤
      (Fintype.card V : ℝ≥0) ^ 2 * ∑ j ∈ orders, error j :=
    hreserved.sourceLeftCaps_probability_le hdis orders F y z (W.U i.succ) s epsilon error
      hp hp1 hr hr1 hC hepsilon hU hsource hscale hscalar
  have hdegree : joint.probability (fun sample ↦ ¬ DegreeGood sample) ≤
      sourcePreliminaryDegreeFailure (Fintype.card V) (W.U i.castSucc).card ⌊mu / 256⌋₊
        degreeMoment rate constant preError := by
    apply L.jointBind_jointBind_probability_snd_fst_le_on_support Kpre Kint
      (fun omega xi ↦ ¬ PreliminaryResidualDegreeGood
        (reserveProtectedOuterGraph (G omega) (W.U i.succ)
          (reserveEdges (G omega) (W.U i.succ) (bits omega))) (W.U i.succ) (pre omega xi) ⌊mu / 256⌋₊)
    intro omega hmass
    exact (hmixed omega hmass).protected_preliminary_degree_failure_le
      (hGsupport omega hmass) hRate le_rfl degreeMoment ⌊mu / 256⌋₊ hdegreeMoment
  have hbad : joint.probability (fun sample ↦ sample.2.2.failed = true) ≤
      joint.probability (fun sample ↦ ¬ DegreeGood sample ∨ ¬ LeftGood sample) := by
    apply joint.probability_mono_of_supported (fun _ hmass ↦ hmass)
    intro sample hmass hfailed
    by_cases hdeg : DegreeGood sample
    · right
      intro hleftGood
      have hmasses := (L.jointBind_mass_pos_iff kernel sample.1 sample.2).mp hmass
      have hinner := ((Kpre sample.1).jointBind_mass_pos_iff (Kint sample.1)
        sample.2.1 sample.2.2).mp hmasses.2
      have hpreData := hpre sample.1 hmasses.1 sample.2.1 hinner.1
      have hraw := rawResidualInternalKernel_supported_structure W i (orders.biUnion F)
        (fun z : Omega × Xi ↦ G z.1)
        (fun z ↦ pairSafeAvailable (A z.1) (correlatedRawInternalStart old pre z))
        (correlatedRawInternalStart old pre) (fun z ↦ bits z.1) ⌊mu / 32⌋₊ hthreshold
        (sample.1, sample.2.1) sample.2.2 hinner.2
      have hclass : sample.2.2.chosen = initial sample.1 ∪ finalLater sample := by
        dsimp only [finalLater, jointLater, added, preliminaryInternalCombinedAdded, intAdded,
          correlatedRawInternalAdded, rawResidualInternalAdded, correlatedRawInternalStart, old]
        rw [← union_assoc, ← union_assoc]
        exact (union_sdiff_of_subset hraw.1.1.initial_subset).symm
      have hsuccess := hraw.notFailed_of_reserve_degree hmu (initial sample.1) (finalLater sample)
        hclass hpreData.2.1 hpreData.2.2.2 (hbase sample.1 hmasses.1) (hGleave sample.1 hmasses.1)
        (hlevel sample.1 hmasses.1) (hinitial sample.1 hmasses.1)
        (hprotected sample.1 hmasses.1 sample.2.1 hinner.1) (hreserve sample.1 hmasses.1)
        hdeg (hleftGood.mono_cutoff hcap)
      exact Bool.false_ne_true (hsuccess.symm.trans hfailed)
    · exact Or.inl hdeg
  exact hbad.trans ((joint.probability_or_le _ _).trans (add_le_add hdegree hleft))

end

end Erdos207
