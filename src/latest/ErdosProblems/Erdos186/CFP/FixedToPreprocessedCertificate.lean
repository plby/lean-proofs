/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.PreprocessedWitness

/-!
# Recover a preprocessed certificate from a source fixed-scale witness

This adapter lets the projected coordinate construction return its natural
`FixedScaleWitness` while preserving the existing centered-coverage
boundary.  The witness's reserved set is regarded as a one-member reserve
family, and its lattice core is pulled back through the injective canonical
integer embedding.
-/

namespace Erdos186.CFP

noncomputable section

/-- Every source fixed-scale witness canonically supplies the corresponding
one-block preprocessed reserve certificate. -/
theorem exists_preprocessedReserveCertificate_of_fixedScaleWitness
    {stableCore : Finset ℤ}
    {s D k extraLoss scaleNum scaleDen : ℕ}
    (W : FixedScaleWitness (Stability.integerPoints stableCore) s D k
      extraLoss scaleNum scaleDen) :
    Nonempty (PreprocessedReserveCertificate stableCore s D extraLoss
      scaleNum scaleDen) := by
  classical
  let integerCore := stableCore.filter fun z ↦
    Stability.integerPoint z ∈ W.enhanced.core
  have hintegerPoints : Stability.integerPoints integerCore =
      W.enhanced.core := by
    ext x
    constructor
    · intro hx
      obtain ⟨z, hz, rfl⟩ := Stability.mem_integerPoints_iff.mp hx
      exact (Finset.mem_filter.mp hz).2
    · intro hx
      have hxSource := W.enhanced.core_subset hx
      obtain ⟨z, hz, hzx⟩ := Stability.mem_integerPoints_iff.mp hxSource
      subst x
      exact Stability.integerPoint_mem_integerPoints_iff.mpr
        (Finset.mem_filter.mpr ⟨hz, hx⟩)
  let reserve : Fin 1 → Finset (LatticePoint 1) :=
    fun _ ↦ W.enhanced.reserved
  refine ⟨{
    integerCore := integerCore
    integerCore_subset := Finset.filter_subset _ _
    stableCore_large := ?_
    ell := 1
    rank := W.enhanced.rank
    k := k
    reserve := reserve
    progression := W.enhanced.progression
    translatePoint := W.enhanced.translatePoint
    reserve_pairwiseDisjoint := ?_
    rank_le := W.enhanced.rank_le
    reserve_subset_core := ?_
    reserve_small := ?_
    core_zero_subset := ?_
    homogeneous := W.enhanced.homogeneous
    covered := ?_
    dilate_proper := W.enhanced.dilate_proper
    k_pos := W.enhanced.k_pos
    scaleNum_pos := by simpa only [W.scaleNum_eq] using
      W.enhanced.scaleNum_pos
    scaleDen_pos := by simpa only [W.scaleDen_eq] using
      W.enhanced.scaleDen_pos
    scale_lower := by simpa only [W.scaleNum_eq, W.scaleDen_eq] using
      W.enhanced.scale_lower
    scale_upper := W.enhanced.scale_upper
    progression_proper := W.enhanced.progression_proper
    progression_symmetric := W.enhanced.progression_symmetric
    progression_nondegenerate := W.enhanced.progression_nondegenerate
    covered_translate_homogeneous :=
      W.enhanced.covered_translate_homogeneous }⟩
  · have hcard : integerCore.card = W.enhanced.core.card := by
      calc
        integerCore.card = (Stability.integerPoints integerCore).card := by
          rw [Stability.card_integerPoints]
        _ = W.enhanced.core.card := congrArg Finset.card hintegerPoints
    simpa only [Stability.card_integerPoints, hcard] using
      W.enhanced.core_large
  · intro i _hi j _hj hij
    exact (hij (Subsingleton.elim i j)).elim
  · intro i
    dsimp only [reserve]
    rw [hintegerPoints]
    exact W.enhanced.reserved_subset_core
  · simpa only [reserve, Fin.sum_univ_one] using W.enhanced.reserved_small
  · rw [hintegerPoints]
    exact W.enhanced.core_zero_subset
  · intro x hx
    rw [mem_heterogeneousSumset]
    refine ⟨fun _ ↦ x, ?_, ?_⟩
    · intro i
      simpa only [reserve] using W.enhanced.covered hx
    · simp

end

end Erdos186.CFP

#print axioms
  Erdos186.CFP.exists_preprocessedReserveCertificate_of_fixedScaleWitness
