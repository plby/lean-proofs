/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.CenteredPreprocessingSource

/-!
# Retained preprocessing from an exact-dyadic source family

The whole-range Bilu package already supplies an approximation for every
nontrivial anchored subset at each admissible exact dyadic fold.  This file
reconstructs the retained preprocessing argument directly from one such
family.  Consequently the terminal finite constants may be chosen before
the preprocessing fold, avoiding a false feedback between the number of
colours and the physical comparison coefficient.
-/

namespace Erdos186.CFP.PreprocessingBilu

open Erdos186.CFP
open Erdos186.CFP.HDimension

noncomputable section

/-- A source-wide exact-fold approximation family contains all information
needed by retained centered preprocessing.  The empty-relevant alternative
is selected exactly when a qualifying accessible subset can be `{0}`. -/
theorem retainedDyadicPreprocessingHApproximationArgument_of_dyadicSourceFamily
    {A : Finset ℤ} {stableBudget D n propernessDenominator fold : ℕ}
    (hzero : 0 ∈ A)
    (hdenominator : 0 < propernessDenominator)
    (hA : A ⊆ Finset.Icc (0 : ℤ) ((n : ℤ) - 1))
    (hfamily : DyadicSourceHApproximationFamily A fold D 1
      (preprocessingScaleDen propernessDenominator))
    (hfoldn : fold ≤ n)
    (hlarge : preprocessingIndexBound D propernessDenominator ≤ fold) :
    RetainedDyadicPreprocessingHApproximationArgument A stableBudget D n
      (preprocessingRobustnessDenominator D propernessDenominator) 1
      (preprocessingScaleDen propernessDenominator) fold := by
  intro W hWA hzeroW _hstable
  let scaleDen := preprocessingScaleDen propernessDenominator
  let indexBound := preprocessingIndexBound D propernessDenominator
  let height := D * Nat.log 2 indexBound
  let C0 := preprocessingRobustnessDenominator D propernessDenominator
  have hC0 : C0 = height + 1 := rfl
  have hspanLoss :
      (stableBudget / C0) * (D * Nat.log 2 indexBound) ≤ stableBudget := by
    rw [hC0]
    exact spanLoss_le_of_height_succ stableBudget height
  let AccessibleNontrivial : Prop :=
    ∀ {B : Finset ℤ}, B ⊆ W →
      W.card ≤ B.card +
        (stableBudget / C0) * (D * Nat.log 2 indexBound + 1) →
      0 ∈ B → B ≠ {0}
  by_cases haccessible : AccessibleNontrivial
  · have hWne : W ≠ {0} := by
      apply haccessible (B := W) Finset.Subset.rfl (by omega) hzeroW
    obtain ⟨rank, hrankPos, hrank, happroxRank⟩ :=
      hfamily hWA hzeroW hWne
    let V : HApproximation W fold rank 1 scaleDen :=
      Classical.choice happroxRank
    have hproperRank :
        (BoundingBox.dBoundingBox W rank hrankPos).progression.Proper := by
      apply boundingBox_proper_of_sourceHApproximation V
        hdenominator
        hrankPos hrank
      simpa only [scaleDen, indexBound, preprocessingScaleDen,
        preprocessingIndexBound] using hlarge
    let relevant : Finset ℕ := {rank}
    let hproper : Stability.RelevantBoxesProper W relevant :=
      { positive := by
          intro d hd
          have hdrank : d = rank := Finset.mem_singleton.mp hd
          simpa only [hdrank] using hrankPos
        proper := by
          intro d hd
          have hdrank : d = rank := Finset.mem_singleton.mp hd
          subst d
          exact hproperRank }
    let hAt : {d // d ∈ relevant} → ℕ := fun _ ↦ fold
    refine ⟨relevant, hproper, hAt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro d
      have hdrank : d.1 = rank := Finset.mem_singleton.mp d.2
      simpa only [hAt, hdrank, scaleDen] using happroxRank
    · intro d
      have hdrank : d.1 = rank := Finset.mem_singleton.mp d.2
      simpa only [hdrank] using hrank
    · intro _d
      exact hfoldn
    · intro _d
      simpa only [hAt, scaleDen, indexBound, preprocessingScaleDen,
        preprocessingIndexBound] using hlarge
    · intro B hBW hcard hzeroB d
      have hBne : B ≠ {0} := by
        apply haccessible hBW _ hzeroB
        simpa only [C0, height, indexBound, preprocessingIndexBound] using hcard
      obtain ⟨rankB, hrankBPos, hrankB, happroxB⟩ :=
        hfamily (hBW.trans hWA) hzeroB hBne
      let VB : HApproximation B fold rankB 1 scaleDen :=
        Classical.choice happroxB
      refine ⟨rankB, hrankBPos, hrankB, VB, ?_⟩
      simpa only [hAt, one_mul, scaleDen, indexBound,
        preprocessingScaleDen, preprocessingIndexBound] using
        approximation_numeric_of_preprocessing_large
          (by
            simpa only [scaleDen, preprocessingScaleDen] using
              Nat.mul_pos (by omega : 0 < 2) hdenominator)
          hrankBPos hrankB
          (by simpa only [indexBound, preprocessingIndexBound,
              preprocessingScaleDen] using hlarge)
    · simpa only [C0, height, indexBound, preprocessingIndexBound] using
        hspanLoss
    · intro _d
      rfl
    · exact Or.inl (by simp [relevant])
  · let relevant : Finset ℕ := ∅
    let hproper : Stability.RelevantBoxesProper W relevant :=
      { positive := by simp [relevant]
        proper := by simp [relevant] }
    let emptyElim : {d // d ∈ relevant} → False := fun d ↦ by
      have hd : d.1 ∈ (∅ : Finset ℕ) := by
        simpa only [relevant] using d.2
      exact Finset.notMem_empty d.1 hd
    let hAt : {d // d ∈ relevant} → ℕ :=
      fun d ↦ False.elim (emptyElim d)
    have hsmall : W.card ≤ 1 +
        (stableBudget / C0) * (D * Nat.log 2 indexBound + 1) := by
      simp only [AccessibleNontrivial] at haccessible
      push_neg at haccessible
      obtain ⟨B, hBW, hcard, hzeroB, hB⟩ := haccessible
      have hBcard : B.card = 1 := by rw [hB]; simp
      omega
    refine ⟨relevant, hproper, hAt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro d
      exact False.elim (emptyElim d)
    · intro d
      exact False.elim (emptyElim d)
    · intro d
      exact False.elim (emptyElim d)
    · intro d
      exact False.elim (emptyElim d)
    · intro B hBW hcard hzeroB d
      exact False.elim (emptyElim d)
    · simpa only [C0, height, indexBound, preprocessingIndexBound] using
        hspanLoss
    · intro d
      exact False.elim (emptyElim d)
    · refine Or.inr ?_
      simpa only [C0, height, indexBound, preprocessingIndexBound] using hsmall

end

end Erdos186.CFP.PreprocessingBilu

namespace Erdos186.CFP.Preprocessing

noncomputable section

/-- Direct data-producing form used by the terminal selector after it has
chosen the compatible exact dyadic fold. -/
theorem exists_dyadicCenteredPreprocessingData_of_dyadicSourceFamily
    {A : Finset ℤ} {stableBudget D n propernessDenominator fold : ℕ}
    (hzero : 0 ∈ A) (hdenominator : 0 < propernessDenominator)
    (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ))
    (hfamily : PreprocessingBilu.DyadicSourceHApproximationFamily A fold D 1
      (PreprocessingBilu.preprocessingScaleDen propernessDenominator))
    (hfoldn : fold ≤ n)
    (hlarge : PreprocessingBilu.preprocessingIndexBound D
      propernessDenominator ≤ fold) :
    Nonempty (DyadicCenteredPreprocessingData A stableBudget D n
      (PreprocessingBilu.preprocessingRobustnessDenominator D
        propernessDenominator) 1
      (PreprocessingBilu.preprocessingScaleDen propernessDenominator)
      fold) := by
  let C0 := PreprocessingBilu.preprocessingRobustnessDenominator D
    propernessDenominator
  have hC0 : 0 < C0 := by
    dsimp only [C0, PreprocessingBilu.preprocessingRobustnessDenominator]
    omega
  apply exists_dyadicCenteredPreprocessingData hzero hC0 hA
  apply PreprocessingBilu.retainedDyadicPreprocessingHApproximationArgument_of_dyadicSourceFamily
    hzero hdenominator
  · intro z hz
    have hzBounds := hA z hz
    exact Finset.mem_Icc.mpr ⟨hzBounds.1, by omega⟩
  · exact hfamily
  · exact hfoldn
  · exact hlarge

end

end Erdos186.CFP.Preprocessing

#print axioms
  Erdos186.CFP.PreprocessingBilu.retainedDyadicPreprocessingHApproximationArgument_of_dyadicSourceFamily
#print axioms
  Erdos186.CFP.Preprocessing.exists_dyadicCenteredPreprocessingData_of_dyadicSourceFamily
