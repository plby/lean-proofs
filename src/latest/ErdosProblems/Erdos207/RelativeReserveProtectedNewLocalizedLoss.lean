/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RelativeReserveProtectedNewCorrelatedRooted
import ErdosProblems.Erdos207.RelativeReserveProtectedLocalizedLoss

/-! # Localized loss for the corrected relative rooted output -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem RelativeReserveProtectedNewCappedRootedOutput.localizedLoss
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell n : ℕ}
    {law : FiniteLaw (RelativeReserveProtectedCorrelatedSample Omega V n)}
    {W : Vortex V ell} {next : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V} {i : Fin ell}
    {G : Omega → SimpleGraph V} {A I D : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool} {d Dint R : ℕ}
    {caps : V → ℕ} {p reserveDensity C b : ℝ≥0}
    (hout : RelativeReserveProtectedNewCappedRootedOutput law W next F i
      G A I D bits d Dint R caps p reserveDensity C b) :
    law.SupportedOn fun z ↦
      ∀ o : {x : V // x ∉ W.U i.succ},
        ((coveredGraph (relativeReserveProtectedTotal I D z.1 z.2)).neighborFinset
          o.1 ∩ W.U i.succ).card ≤ caps o.1 + d := by
  intro z hz o
  let U := W.U i.succ
  let pre := relativeReserveProtectedPreliminaryAdded I D z.1 z.2.1
  let P₀ := relativeReserveProtectedP0 I D (z.1, z.2.1)
  let Q := z.2.2.chosen
  let addedInt := Q \ P₀
  have htotal : relativeReserveProtectedTotal I D z.1 z.2 =
      pre ∪ addedInt := by
    rfl
  have hpreLoss :
      ((coveredGraph pre).neighborFinset o.1 ∩ U).card ≤ caps o.1 := by
    calc
      ((coveredGraph pre).neighborFinset o.1 ∩ U).card ≤
          (triplesThrough pre o.1).card :=
        card_coveredNeighborsIn_le_triplesThrough_of_atMostOne
          (hout.preliminaryAtMostOne z hz) o.1
      _ ≤ caps o.1 := by
        exact Nat.le_of_lt (by
          simpa only [ambientTriplesThrough_inter, pre] using
            hout.preliminaryCaps z hz o.1)
  have hraw := hout.outcome z hz
  have hP₀Q : P₀ ⊆ Q := hraw.1.1.initial_subset
  have hpackingAll := (hout.structural z hz).2.2.1
  have hpackingQ : IsPackingOn Q := by
    have h := hpackingAll
    rw [hout.accumulate z hz] at h
    exact h
  let E := preliminaryResidualInternalEdges (G z.1) U P₀
  have houter : ∀ e ∈ E, e.out.1 ∉ U ∧ e.out.2 ∉ U := by
    intro e he
    exact (mem_internalOuterEdges_iff.mp
      (preliminaryResidualInternalEdges_subset_internalOuterEdges
        (G z.1) U P₀ he)).2
  have hinternalLoss :
      ((coveredGraph addedInt).neighborFinset o.1 ∩ U).card ≤ d := by
    apply card_coveredNeighborsIn_newInternalAdded_le_scheduledIncidence
      (P₀ := P₀) (Q := Q) (E := E)
    · exact hP₀Q
    · exact hpackingQ
    · exact houter
    · simpa only [E, P₀, U, Q, relativeReserveProtectedP0,
        relativeReserveProtectedAint] using hraw.2.2.1
    · simpa only [E, P₀, U] using hout.incidence z hz
    · exact o.2
  have hsubset :
      (coveredGraph (relativeReserveProtectedTotal I D z.1 z.2)).neighborFinset
          o.1 ∩ U ⊆
        ((coveredGraph pre).neighborFinset o.1 ∩ U) ∪
          ((coveredGraph addedInt).neighborFinset o.1 ∩ U) := by
    intro v hv
    have hvparts := coveredGraph_union_neighborFinset_subset pre addedInt o.1
      (by
        rw [← htotal]
        exact (mem_inter.mp hv).1)
    have hvU := (mem_inter.mp hv).2
    rcases mem_union.mp hvparts with hvpre | hvint
    · exact mem_union_left _ (mem_inter.mpr ⟨hvpre, hvU⟩)
    · exact mem_union_right _ (mem_inter.mpr ⟨hvint, hvU⟩)
  exact (card_le_card hsubset).trans
    ((card_union_le _ _).trans (Nat.add_le_add hpreLoss hinternalLoss))

end

end Erdos207
