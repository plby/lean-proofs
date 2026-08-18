/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Main
import ErdosProblems.Erdos186.CFP.Stability

/-!
# Removing an auxiliary zero from a CFP witness

The one-dimensional CFP proof is naturally run on a set containing the
distinguished origin.  The source-facing theorem, however, is stated for a
set in the positive interval `[1,n]`.  This file proves the exact finite
transport needed between the two formulations.  Erasing zero from the
reserve does not change its subset sums, and erasing zero simultaneously
from the source and the core preserves the loss inequality.
-/

namespace Erdos186.CFP

noncomputable section

/-- Erasing the additive identity does not change the set of subset sums. -/
theorem subsetSums_erase_zero {d : ℕ}
    (R : Finset (LatticePoint d)) :
    GAP.subsetSums (R.erase 0) = GAP.subsetSums R := by
  apply Finset.Subset.antisymm
  · exact subsetSums_mono (Finset.erase_subset 0 R)
  · intro x hx
    obtain ⟨S, hSR, hsum⟩ := GAP.mem_subsetSums_iff.mp hx
    apply GAP.mem_subsetSums_iff.mpr
    refine ⟨S.erase 0, ?_, ?_⟩
    · intro y hy
      have hyS : y ∈ S := (Finset.mem_erase.mp hy).2
      have hyR : y ∈ R := hSR hyS
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hy).1, hyR⟩
    · rw [← hsum]
      by_cases hzero : 0 ∈ S
      · have herase := Finset.sum_erase_add S (fun y ↦ y) hzero
        simpa using herase
      · rw [Finset.erase_eq_of_notMem hzero]

namespace EnhancedCFPWitness

variable {d s D k loss : ℕ} {H : Finset (LatticePoint d)}

/-- Remove a distinguished zero from the source, core, and reserve of an
enhanced witness.  All geometric data and all quantitative parameters are
unchanged. -/
noncomputable def eraseZero
    (W : EnhancedCFPWitness H s D k loss)
    (hzeroH : 0 ∈ H) :
    EnhancedCFPWitness (H.erase 0) s D k loss where
  core := W.core.erase 0
  reserved := W.reserved.erase 0
  rank := W.rank
  rank_le := W.rank_le
  progression := W.progression
  core_subset := by
    intro x hx
    exact Finset.mem_erase.mpr
      ⟨(Finset.mem_erase.mp hx).1, W.core_subset (Finset.mem_erase.mp hx).2⟩
  reserved_subset_core := by
    intro x hx
    exact Finset.mem_erase.mpr
      ⟨(Finset.mem_erase.mp hx).1,
        W.reserved_subset_core (Finset.mem_erase.mp hx).2⟩
  core_large := by
    have hlarge := W.core_large
    rw [Finset.card_erase_of_mem hzeroH]
    by_cases hzeroCore : 0 ∈ W.core
    · rw [Finset.card_erase_of_mem hzeroCore]
      omega
    · rw [Finset.erase_eq_of_notMem hzeroCore]
      omega
  reserved_small :=
    (Finset.card_le_card (Finset.erase_subset 0 W.reserved)).trans
      W.reserved_small
  core_zero_subset := by
    exact (Finset.insert_subset_insert 0 (Finset.erase_subset 0 W.core)).trans
      W.core_zero_subset
  homogeneous := W.homogeneous
  translatePoint := W.translatePoint
  covered := by
    simpa only [subsetSums_erase_zero] using W.covered
  dilate_proper := W.dilate_proper
  k_pos := W.k_pos
  scaleNum := W.scaleNum
  scaleDen := W.scaleDen
  scaleNum_pos := W.scaleNum_pos
  scaleDen_pos := W.scaleDen_pos
  scale_lower := W.scale_lower
  scale_upper := W.scale_upper
  progression_proper := W.progression_proper
  progression_symmetric := W.progression_symmetric
  progression_nondegenerate := W.progression_nondegenerate
  covered_translate_homogeneous := W.covered_translate_homogeneous

end EnhancedCFPWitness

namespace FixedScaleWitness

variable {d s D k loss scaleNum scaleDen : ℕ}
    {H : Finset (LatticePoint d)}

/-- Fixed-scale packaging of `EnhancedCFPWitness.eraseZero`. -/
noncomputable def eraseZero
    (W : FixedScaleWitness H s D k loss scaleNum scaleDen)
    (hzeroH : 0 ∈ H) :
    FixedScaleWitness (H.erase 0) s D k loss scaleNum scaleDen :=
  ⟨W.enhanced.eraseZero hzeroH, W.2⟩

end FixedScaleWitness

/-- The preprocessing embedding, after adjoining and then erasing the
origin, is exactly the source-facing embedding used by `IntegerTheorem15`.
The hypothesis holds automatically for a set contained in `[1,n]`. -/
theorem erase_zero_stabilityIntegerPoints_insert
    {A : Finset ℤ} (hzero : 0 ∉ A) :
    (Stability.integerPoints (insert 0 A)).erase 0 = integerPoints A := by
  have hpoint (a : ℤ) : Stability.integerPoint a = integerPoint a := by
    rfl
  have hzeroPoint : Stability.integerPoint 0 = (0 : LatticePoint 1) := by
    rfl
  ext x
  constructor
  · intro hx
    have hx' := Finset.mem_erase.mp hx
    obtain ⟨a, ha, hax⟩ := Stability.mem_integerPoints_iff.mp hx'.2
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact False.elim (hx'.1 (hax.symm.trans hzeroPoint))
    · apply Finset.mem_image.mpr
      refine ⟨a, ha, ?_⟩
      exact (hpoint a).symm.trans hax
  · intro hx
    obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hx
    apply Finset.mem_erase.mpr
    constructor
    · intro hxzero
      have ha0 : a = 0 := by
        have hcomponent := congrFun (hax.trans hxzero) (0 : Fin 1)
        simpa [integerPoint] using hcomponent
      exact hzero (ha0 ▸ ha)
    · apply Stability.mem_integerPoints_iff.mpr
      refine ⟨a, Finset.mem_insert_of_mem ha, ?_⟩
      exact (hpoint a).trans hax

/-- Consumer-facing composition of the generic zero erasure with the two
integer embeddings used by preprocessing and by `IntegerTheorem15`. -/
noncomputable def FixedScaleWitness.eraseZero_stabilityIntegerPoints
    {A : Finset ℤ} {s D k loss scaleNum scaleDen : ℕ}
    (W : FixedScaleWitness (Stability.integerPoints (insert 0 A))
      s D k loss scaleNum scaleDen)
    (hzero : 0 ∉ A) :
    FixedScaleWitness (integerPoints A) s D k loss scaleNum scaleDen := by
  have hzeroSource : (0 : LatticePoint 1) ∈
      Stability.integerPoints (insert 0 A) := by
    apply Stability.mem_integerPoints_iff.mpr
    exact ⟨0, Finset.mem_insert_self 0 A, rfl⟩
  have W' := W.eraseZero hzeroSource
  rw [erase_zero_stabilityIntegerPoints_insert hzero] at W'
  exact W'

end


end Erdos186.CFP

#print axioms Erdos186.CFP.subsetSums_erase_zero
#print axioms Erdos186.CFP.EnhancedCFPWitness.eraseZero
#print axioms Erdos186.CFP.FixedScaleWitness.eraseZero
#print axioms Erdos186.CFP.erase_zero_stabilityIntegerPoints_insert
#print axioms
  Erdos186.CFP.FixedScaleWitness.eraseZero_stabilityIntegerPoints
