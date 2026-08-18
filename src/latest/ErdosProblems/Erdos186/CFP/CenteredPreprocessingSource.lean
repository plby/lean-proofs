/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.CenteredPreprocessingData

/-!
# Source-retained centered preprocessing at a genuine dyadic fold

The Bilu--Freiman horizon used to bound the ambient rank need not itself be
a power of two.  The later greedy thresholds, however, use the fold
`2^level`.  This file separates those two scales.  The dyadic fold is chosen
inside the same Bilu--Freiman window, while the telescoping horizon continues
to supply the rank bound.

The callback also retains the alternative erased by the original
`PreprocessingHApproximationArgument`: either the relevant family is the
single positive ambient rank and every retained approximation is at the
dyadic fold, or the weak core is already small enough for the terminal
rank-zero branch.
-/

namespace Erdos186.CFP.PreprocessingBilu

open Erdos186.CFP
open Erdos186.CFP.HDimension

noncomputable section

/-- The exact source information needed after centered preprocessing. -/
def RetainedDyadicPreprocessingHApproximationArgument
    (A : Finset ℤ) (stableBudget maxRank n C0 scaleNum scaleDen fold : ℕ) :
    Prop :=
  ∀ {W : Finset ℤ}, W ⊆ A → 0 ∈ W →
    Stability.WeaklyStableMinimalFor W (2 * stableBudget) maxRank n →
    ∃ (relevant : Finset ℕ)
      (hproper : Stability.RelevantBoxesProper W relevant)
      (hAt : {d // d ∈ relevant} → ℕ),
      (∀ d : {d // d ∈ relevant},
        Nonempty (HApproximation W (hAt d) d.1 scaleNum scaleDen)) ∧
      (∀ d : {d // d ∈ relevant}, d.1 ≤ maxRank) ∧
      (∀ d : {d // d ∈ relevant}, hAt d ≤ n) ∧
      (∀ d : {d // d ∈ relevant},
        4 * (6 * scaleDen) ^ maxRank *
            (4 * scaleDen) ^ maxRank ≤ hAt d) ∧
      (∀ {B : Finset ℤ}, B ⊆ W →
        W.card ≤ B.card +
          (stableBudget / C0) *
            (maxRank * Nat.log 2
              (4 * (6 * scaleDen) ^ maxRank *
                (4 * scaleDen) ^ maxRank) + 1) →
        0 ∈ B → ∀ d : {d // d ∈ relevant},
          ∃ e : ℕ, 0 < e ∧ e ≤ maxRank ∧
            ∃ V : HApproximation B (hAt d) e scaleNum scaleDen,
              (2 * scaleDen) ^ e * (hAt d + 1) ^ (e - 1) <
                (scaleNum * hAt d) ^ e) ∧
      (stableBudget / C0) *
        (maxRank * Nat.log 2
          (4 * (6 * scaleDen) ^ maxRank *
            (4 * scaleDen) ^ maxRank)) ≤ stableBudget ∧
      (∀ d : {d // d ∈ relevant}, hAt d = fold) ∧
      (relevant.Nonempty ∨
        W.card ≤ 1 +
          (stableBudget / C0) *
            (maxRank * Nat.log 2
              (4 * (6 * scaleDen) ^ maxRank *
                (4 * scaleDen) ^ maxRank) + 1))

/-- Every positive integer is at most the least power of two above it, and
that power is still strictly below twice the integer. -/
theorem le_two_pow_clog_lt_two_mul {a : ℕ} (ha : 0 < a) :
    a ≤ 2 ^ Nat.clog 2 a ∧ 2 ^ Nat.clog 2 a < 2 * a := by
  constructor
  · exact Nat.le_pow_clog (by omega) a
  · by_cases ha1 : a = 1
    · subst a
      norm_num
    · have haTwo : 2 ≤ a := by omega
      have hclogPos : 0 < Nat.clog 2 a :=
        Nat.clog_pos (by omega) (by omega)
      have hpred : 2 ^ (Nat.clog 2 a - 1) < a := by
        simpa only [Nat.pred_eq_sub_one] using
          Nat.pow_pred_clog_lt_self (by omega : 1 < 2) haTwo
      have hsucc : Nat.clog 2 a - 1 + 1 = Nat.clog 2 a := by omega
      calc
        2 ^ Nat.clog 2 a = 2 ^ (Nat.clog 2 a - 1 + 1) := by rw [hsucc]
        _ = 2 * 2 ^ (Nat.clog 2 a - 1) := by
          rw [pow_succ]
          ring
        _ < 2 * a := Nat.mul_lt_mul_of_pos_left hpred (by omega)

/-- The dyadic fold obtained by shifting the least power of two above the
horizon factor lies in the required Bilu--Freiman window. -/
theorem dyadicFold_window
    {horizonFactor last : ℕ} (hfactor : 0 < horizonFactor) :
    horizonFactor * 2 ^ last ≤
        2 ^ (Nat.clog 2 horizonFactor + last) ∧
      2 ^ (Nat.clog 2 horizonFactor + last) <
        horizonFactor * 2 ^ (last + 1) := by
  obtain ⟨hlower, hupper⟩ := le_two_pow_clog_lt_two_mul hfactor
  constructor
  · rw [pow_add]
    exact Nat.mul_le_mul_right (2 ^ last) hlower
  · rw [pow_add, pow_succ]
    calc
      2 ^ Nat.clog 2 horizonFactor * 2 ^ last <
          (2 * horizonFactor) * 2 ^ last :=
        Nat.mul_lt_mul_of_pos_right hupper (by positivity)
      _ = horizonFactor * (2 ^ last * 2) := by ring

/-- Source preprocessing with a separate dyadic approximation fold.

`horizon` is used only for the slow-growth telescoping argument.  `fold` is
the actual scale passed to Bilu--Freiman and retained for the greedy stage.
The two lie in the same source window. -/
theorem retainedDyadicPreprocessingHApproximationArgument_of_uniform_source
    {blockThreshold horizonFactor propernessDenominator D first : ℕ}
    (horizonFactor_pos : 0 < horizonFactor)
    (hdenominator : 0 < propernessDenominator)
    (hD : 2 ≤ D)
    (hthreshold : blockThreshold ≤ 2 ^ (first + 1))
    (hconsumer :
      ∀ {S : Finset ℤ} {q dimension first' last' : ℕ},
        0 ∈ S → dimension ≤ D →
        IsMinimalDyadicGrowthDimension S dimension first' last' →
        blockThreshold ≤ 2 ^ (first' + 1) →
        horizonFactor * 2 ^ last' ≤ q →
        q < horizonFactor * 2 ^ (last' + 1) →
        propernessDenominator ≤ q →
        ∃ rank, rank ≤ dimension ∧ Nonempty
          (HApproximation S q rank 1
            (preprocessingScaleDen propernessDenominator)))
    {A : Finset ℤ} {n horizon fold last stableBudget : ℕ}
    (hzero : 0 ∈ A)
    (hA : A ⊆ Finset.Icc (0 : ℤ) ((n : ℤ) - 1))
    (hhorizon : horizon = horizonFactor * 2 ^ last)
    (hhorizonFold : horizon ≤ fold)
    (hfoldUpper : fold < horizonFactor * 2 ^ (last + 1))
    (hfoldn : fold ≤ n)
    (hnpower : n ≤ horizon ^ (D - 1))
    (hfirstLast : first < last)
    (hlastLarge :
      (2 * D + 1) * first + 2 * horizonFactor * (D - 1) < last)
    (hlarge : preprocessingIndexBound D propernessDenominator ≤ fold)
    (hdenominatorLarge : propernessDenominator ≤ fold) :
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
  have hhorizonN : horizon ≤ n := hhorizonFold.trans hfoldn
  by_cases haccessible : AccessibleNontrivial
  · have hWne : W ≠ {0} := by
      apply haccessible (B := W) Finset.Subset.rfl (by omega) hzeroW
    have hWinterval : W ⊆ Finset.Icc (0 : ℤ) ((n : ℤ) - 1) :=
      hWA.trans hA
    obtain ⟨dimension, hdimensionD, hminimal⟩ :=
      exists_bounded_minimalDyadicGrowthDimension hzeroW hWinterval
        horizonFactor_pos hD hhorizon hhorizonN hnpower hfirstLast hlastLarge
    obtain ⟨rank, hrankDimension, happroxRank⟩ :=
      hconsumer hzeroW hdimensionD hminimal hthreshold
        (by simpa only [hhorizon] using hhorizonFold)
        hfoldUpper hdenominatorLarge
    let V : HApproximation W fold rank 1 scaleDen :=
      Classical.choice happroxRank
    have hrank : rank ≤ D := hrankDimension.trans hdimensionD
    have hrankPos : 0 < rank :=
      HApproximation.rank_pos_of_ne_singleton_zero V hWne
    have hproperRank :
        (BoundingBox.dBoundingBox W rank hrankPos).progression.Proper := by
      apply boundingBox_proper_of_sourceHApproximation V hdenominator
        hrankPos hrank
      simpa only [scaleDen, indexBound, preprocessingScaleDen,
        preprocessingIndexBound] using hlarge
    let relevant : Finset ℕ := {rank}
    let hproper : Stability.RelevantBoxesProper W relevant :=
      { positive := by
          intro d hd
          simpa only [relevant, Finset.mem_singleton] using
            (show d = rank from Finset.mem_singleton.mp hd) ▸ hrankPos
        proper := by
          intro d hd
          have hdrank : d = rank := by
            simpa only [relevant, Finset.mem_singleton] using hd
          subst d
          exact hproperRank }
    let hAt : {d // d ∈ relevant} → ℕ := fun _ ↦ fold
    refine ⟨relevant, hproper, hAt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro d
      have hdrank : d.1 = rank := by
        simpa only [relevant, Finset.mem_singleton] using d.2
      simpa only [hAt, hdrank] using happroxRank
    · intro d
      have hdrank : d.1 = rank := by
        simpa only [relevant, Finset.mem_singleton] using d.2
      simpa only [hdrank] using hrank
    · intro d
      exact hfoldn
    · intro d
      simpa only [hAt, scaleDen, indexBound, preprocessingScaleDen,
        preprocessingIndexBound] using hlarge
    · intro B hBW hcard hzeroB d
      have hBne : B ≠ {0} := by
        apply haccessible hBW _ hzeroB
        simpa only [C0, height, indexBound, preprocessingIndexBound] using hcard
      have hBinterval : B ⊆ Finset.Icc (0 : ℤ) ((n : ℤ) - 1) :=
        hBW.trans hWinterval
      obtain ⟨dimensionB, hdimensionBD, hminimalB⟩ :=
        exists_bounded_minimalDyadicGrowthDimension hzeroB hBinterval
          horizonFactor_pos hD hhorizon hhorizonN hnpower hfirstLast hlastLarge
      obtain ⟨rankB, hrankBDimension, happroxB⟩ :=
        hconsumer hzeroB hdimensionBD hminimalB hthreshold
          (by simpa only [hhorizon] using hhorizonFold)
          hfoldUpper hdenominatorLarge
      let VB : HApproximation B fold rankB 1 scaleDen :=
        Classical.choice happroxB
      have hrankBD : rankB ≤ D := hrankBDimension.trans hdimensionBD
      have hrankBPos : 0 < rankB :=
        HApproximation.rank_pos_of_ne_singleton_zero VB hBne
      refine ⟨rankB, hrankBPos, hrankBD, VB, ?_⟩
      simpa only [hAt, one_mul, scaleDen, indexBound,
        preprocessingScaleDen, preprocessingIndexBound] using
        approximation_numeric_of_preprocessing_large
          (Nat.mul_pos (by omega) hdenominator) hrankBPos hrankBD
          (by simpa only [indexBound, preprocessingIndexBound,
              preprocessingScaleDen] using hlarge)
    · simpa only [C0, height, indexBound, preprocessingIndexBound] using
        hspanLoss
    · intro d
      rfl
    · exact Or.inl (by simp [relevant])
  · let relevant : Finset ℕ := ∅
    let hproper : Stability.RelevantBoxesProper W relevant :=
      { positive := by simp [relevant]
        proper := by simp [relevant] }
    let emptyElim : {d // d ∈ relevant} → False := fun d ↦ by
      have hpos : 0 < relevant.card := Finset.card_pos.mpr ⟨d.1, d.2⟩
      have hzeroCard : relevant.card = 0 := by simp [relevant]
      omega
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

/-- At the same dyadic fold, every nontrivial anchored subset of the source
has a positive-rank approximation of rank at most `D`.  This is the retained
source fact used for the color classes and their large greedy subsets; it is
strictly stronger than the near-full accessibility callback used inside
preprocessing. -/
def DyadicSourceHApproximationFamily
    (A : Finset ℤ) (fold D scaleNum scaleDen : ℕ) : Prop :=
  ∀ {S : Finset ℤ}, S ⊆ A → 0 ∈ S → S ≠ {0} →
    ∃ rank : ℕ, 0 < rank ∧ rank ≤ D ∧
      Nonempty (HApproximation S fold rank scaleNum scaleDen)

/-- The uniform Bilu--Freiman constants supply both the retained
preprocessing callback and all nontrivial subset approximations at an
arbitrary dyadic fold in the same source window. -/
theorem exists_retainedDyadicPreprocessingPackage_of_biluFreiman
    (hBF : BiluFreiman.BiluFreimanStatement) (D : ℕ) (hD : 2 ≤ D) :
    ∃ first horizonFactor propernessDenominator C0 : ℕ,
      0 < first ∧ 0 < horizonFactor ∧ 0 < propernessDenominator ∧
      0 < C0 ∧
      C0 = preprocessingRobustnessDenominator D propernessDenominator ∧
      ∀ {A : Finset ℤ} {n horizon fold last stableBudget : ℕ},
        0 ∈ A →
        A ⊆ Finset.Icc (0 : ℤ) ((n : ℤ) - 1) →
        horizon = horizonFactor * 2 ^ last →
        horizon ≤ fold →
        fold < horizonFactor * 2 ^ (last + 1) →
        fold ≤ n →
        n ≤ horizon ^ (D - 1) →
        first < last →
        (2 * D + 1) * first +
            2 * horizonFactor * (D - 1) < last →
        preprocessingIndexBound D propernessDenominator ≤ fold →
        RetainedDyadicPreprocessingHApproximationArgument A stableBudget D n
            C0 1 (preprocessingScaleDen propernessDenominator) fold ∧
          DyadicSourceHApproximationFamily A fold D 1
            (preprocessingScaleDen propernessDenominator) := by
  obtain ⟨blockThreshold, _coverExponentBound, _steps, horizonFactor,
      propernessDenominator, hblockThreshold, _hcoverExponentBound,
      _hsteps, hhorizonFactor, hpropernessDenominator, hconsumer⟩ :=
    exists_uniform_sourceHApproximation_of_biluFreiman hBF D
  let first := blockThreshold
  let C0 := preprocessingRobustnessDenominator D propernessDenominator
  have hfirst : 0 < first := by simpa only [first] using hblockThreshold
  have hthreshold : blockThreshold ≤ 2 ^ (first + 1) := by
    calc
      blockThreshold ≤ 2 ^ blockThreshold := self_le_two_pow blockThreshold
      _ ≤ 2 ^ (first + 1) := by
        apply Nat.pow_le_pow_right (by omega)
        simp only [first]
        omega
  have hC0 : 0 < C0 := by
    simp only [C0, preprocessingRobustnessDenominator]
    omega
  refine ⟨first, horizonFactor, propernessDenominator, C0, hfirst,
    hhorizonFactor, hpropernessDenominator, hC0, rfl, ?_⟩
  intro A n horizon fold last stableBudget hzero hA hhorizon hhorizonFold
    hfoldUpper hfoldn hnpower hfirstLast hlastLarge hlarge
  have hdenominatorLarge : propernessDenominator ≤ fold := by
    let scaleDen := preprocessingScaleDen propernessDenominator
    let x := (6 * scaleDen) ^ D
    let y := (4 * scaleDen) ^ D
    have hscaleDen : scaleDen = 2 * propernessDenominator := rfl
    have hxPos : 0 < x := by
      dsimp only [x, scaleDen, preprocessingScaleDen]
      positivity
    have hyPos : 0 < y := by
      dsimp only [y, scaleDen, preprocessingScaleDen]
      positivity
    have hcbase : propernessDenominator ≤ 6 * scaleDen := by
      rw [hscaleDen]
      omega
    have hbasePow : 6 * scaleDen ≤ x := by
      dsimp only [x]
      exact Nat.le_pow (by omega)
    have hxMul : x ≤ x * y := Nat.le_mul_of_pos_right x hyPos
    have hxFour : x * y ≤ 4 * (x * y) := by nlinarith
    have hcindex : propernessDenominator ≤
        preprocessingIndexBound D propernessDenominator := by
      calc
        propernessDenominator ≤ 6 * scaleDen := hcbase
        _ ≤ x := hbasePow
        _ ≤ x * y := hxMul
        _ ≤ 4 * (x * y) := hxFour
        _ = preprocessingIndexBound D propernessDenominator := by
          simp only [preprocessingIndexBound, x, y, scaleDen, mul_assoc]
    exact hcindex.trans hlarge
  have hretained :
      RetainedDyadicPreprocessingHApproximationArgument A stableBudget D n
        (preprocessingRobustnessDenominator D propernessDenominator) 1
        (preprocessingScaleDen propernessDenominator) fold := by
    intro W hWA hzeroW hstableW
    exact retainedDyadicPreprocessingHApproximationArgument_of_uniform_source
      (A := A) (n := n) (horizon := horizon) (fold := fold)
      (last := last) (stableBudget := stableBudget)
      hhorizonFactor hpropernessDenominator hD hthreshold (by
        intro S q dimension first' last' hzeroS hdimension hminimal
          hthreshold' hlower hupper hdenominator'
        simpa only [preprocessingScaleDen] using
          hconsumer hzeroS hdimension hminimal hthreshold' hlower hupper
            hdenominator')
      hzero hA hhorizon hhorizonFold hfoldUpper hfoldn hnpower hfirstLast
      hlastLarge hlarge hdenominatorLarge hWA hzeroW hstableW
  refine ⟨hretained, ?_⟩
  intro S hSA hzeroS hSne
  have hSinterval : S ⊆ Finset.Icc (0 : ℤ) ((n : ℤ) - 1) :=
    hSA.trans hA
  have hhorizonN : horizon ≤ n := hhorizonFold.trans hfoldn
  obtain ⟨dimension, hdimensionD, hminimal⟩ :=
    exists_bounded_minimalDyadicGrowthDimension hzeroS hSinterval
      hhorizonFactor hD hhorizon hhorizonN hnpower hfirstLast hlastLarge
  obtain ⟨rank, hrankDimension, happrox⟩ :=
    hconsumer hzeroS hdimensionD hminimal hthreshold
      (by simpa only [hhorizon] using hhorizonFold)
      hfoldUpper hdenominatorLarge
  let V : HApproximation S fold rank 1
      (preprocessingScaleDen propernessDenominator) := Classical.choice happrox
  have hrankPos : 0 < rank :=
    HApproximation.rank_pos_of_ne_singleton_zero V hSne
  exact ⟨rank, hrankPos, hrankDimension.trans hdimensionD, happrox⟩

/-! ## A whole source dyadic range

The colour-greedy proof uses a different dyadic level for each colour.  The
following range package records the honest pointwise source conditions under
which the same uniform Bilu--Freiman constants provide every one of those
approximations.  The Bilu horizon at `level` is
`horizonFactor * 2^(level - clog 2 horizonFactor)`; it is deliberately kept
separate from the exact greedy fold `2^level`.
-/

/-- Uniform approximations for all nontrivial anchored subsets at every
dyadic fold in a closed range. -/
def DyadicRangeSourceHApproximationFamily
    (A : Finset ℤ) (low high D scaleNum scaleDen : ℕ) : Prop :=
  ∀ level, low ≤ level → level ≤ high →
    DyadicSourceHApproximationFamily A (2 ^ level) D scaleNum scaleDen

/-- The purely numerical window needed to invoke the uniform source
approximation theorem at every exact dyadic fold in a range. -/
structure DyadicRangeWindow
    (n low high first horizonFactor D propernessDenominator : ℕ) : Prop where
  offset_le_low : Nat.clog 2 horizonFactor ≤ low
  fold_le_n : ∀ level, low ≤ level → level ≤ high → 2 ^ level ≤ n
  n_le_horizon_pow : ∀ level, low ≤ level → level ≤ high →
    n ≤ (horizonFactor *
      2 ^ (level - Nat.clog 2 horizonFactor)) ^ (D - 1)
  first_lt_last : ∀ level, low ≤ level → level ≤ high →
    first < level - Nat.clog 2 horizonFactor
  last_large : ∀ level, low ≤ level → level ≤ high →
    (2 * D + 1) * first + 2 * horizonFactor * (D - 1) <
      level - Nat.clog 2 horizonFactor
  index_le_fold : ∀ level, low ≤ level → level ≤ high →
    preprocessingIndexBound D propernessDenominator ≤ 2 ^ level

/-- Bilu--Freiman supplies the full exact-dyadic range used by the
independently run colours.  There is no assumption that the source horizon
itself is a power of two. -/
theorem exists_dyadicRangeSourceHApproximationFamily_of_biluFreiman
    (hBF : BiluFreiman.BiluFreimanStatement) (D : ℕ) (hD : 2 ≤ D) :
    ∃ first horizonFactor propernessDenominator C0 : ℕ,
      0 < first ∧ 0 < horizonFactor ∧ 0 < propernessDenominator ∧
      0 < C0 ∧
      C0 = preprocessingRobustnessDenominator D propernessDenominator ∧
      ∀ {A : Finset ℤ} {n low high : ℕ},
        0 ∈ A →
        A ⊆ Finset.Icc (0 : ℤ) ((n : ℤ) - 1) →
        DyadicRangeWindow n low high first horizonFactor D
          propernessDenominator →
        DyadicRangeSourceHApproximationFamily A low high D 1
          (preprocessingScaleDen propernessDenominator) := by
  obtain ⟨first, horizonFactor, propernessDenominator, C0,
      hfirst, hhorizonFactor, hpropernessDenominator, hC0, hC0eq, hpackage⟩ :=
    exists_retainedDyadicPreprocessingPackage_of_biluFreiman hBF D hD
  refine ⟨first, horizonFactor, propernessDenominator, C0,
    hfirst, hhorizonFactor, hpropernessDenominator, hC0, hC0eq, ?_⟩
  intro A n low high hzero hA hwindow level hlow hhigh
  let offset := Nat.clog 2 horizonFactor
  let last := level - offset
  let horizon := horizonFactor * 2 ^ last
  have hoffsetLevel : offset ≤ level :=
    hwindow.offset_le_low.trans hlow
  have hlevel : offset + last = level := by
    dsimp only [last]
    exact Nat.add_sub_of_le hoffsetLevel
  have hdyadic := dyadicFold_window (last := last) hhorizonFactor
  have hhorizonFold : horizon ≤ 2 ^ level := by
    rw [← hlevel]
    simpa only [pow_add, horizon, offset] using hdyadic.1
  have hfoldUpper : 2 ^ level < horizonFactor * 2 ^ (last + 1) := by
    rw [← hlevel]
    simpa only [pow_add, offset] using hdyadic.2
  have hresult := hpackage (A := A) (n := n) (horizon := horizon)
    (fold := 2 ^ level) (last := last) (stableBudget := 0)
    hzero hA rfl hhorizonFold hfoldUpper
    (hwindow.fold_le_n level hlow hhigh)
    (by simpa only [horizon, last, offset] using
      hwindow.n_le_horizon_pow level hlow hhigh)
    (by simpa only [last, offset] using
      hwindow.first_lt_last level hlow hhigh)
    (by simpa only [last, offset] using
      hwindow.last_large level hlow hhigh)
    (hwindow.index_le_fold level hlow hhigh)
  intro S hSA hzeroS hSne
  exact hresult.2 hSA hzeroS hSne

end

end Erdos186.CFP.PreprocessingBilu

namespace Erdos186.CFP.Preprocessing

open Erdos186.CFP

noncomputable section

/-- Centered preprocessing with the true dyadic fold and the small-core
alternative retained. -/
structure DyadicCenteredPreprocessingData (A : Finset ℤ)
    (stableBudget maxRank n C0 scaleNum scaleDen fold : ℕ)
    extends CenteredPreprocessingData A stableBudget maxRank n C0
      scaleNum scaleDen where
  hAt_eq_fold : ∀ d : {d // d ∈ relevant}, hAt d = fold
  relevant_nonempty_or_weakCore_small :
    relevant.Nonempty ∨
      weakCore.card ≤ 1 +
        (stableBudget / C0) *
          (maxRank * Nat.log 2
            (4 * (6 * scaleDen) ^ maxRank *
              (4 * scaleDen) ^ maxRank) + 1)

/-- Data-preserving centered preprocessing from the retained source
callback.  This is the source-correct replacement for reconstructing an
arbitrary approximation scale after Lemma 2.38. -/
theorem exists_dyadicCenteredPreprocessingData
    {A : Finset ℤ}
    {stableBudget maxRank n C0 scaleNum scaleDen fold : ℕ}
    (hzero : 0 ∈ A) (hC0 : 0 < C0)
    (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ))
    (happrox :
      PreprocessingBilu.RetainedDyadicPreprocessingHApproximationArgument A
        stableBudget maxRank n C0 scaleNum scaleDen fold) :
    Nonempty (DyadicCenteredPreprocessingData A stableBudget maxRank n C0
      scaleNum scaleDen fold) := by
  classical
  obtain ⟨W, hWA, hzeroW, hweakW, hlossW⟩ :=
    exists_weaklyStable_core hzero
  obtain ⟨relevant, hproper, hAt, hambient, hrank_le, hh_le,
      hlarge, haccessible, hspanLoss, hAtFold, hbranch⟩ :=
    happrox hWA hzeroW hweakW
  let hambient' : ∀ d : {d // d ∈ relevant},
      HDimension.HApproximation W (hAt d) d.1 scaleNum scaleDen :=
    fun d ↦ Classical.choice (hambient d)
  let K := 4 * (6 * scaleDen) ^ maxRank * (4 * scaleDen) ^ maxRank
  let height := maxRank * Nat.log 2 K
  let robustBudget := stableBudget / C0
  have hrobust_le : robustBudget ≤ stableBudget :=
    Nat.div_le_self _ _
  have hcap : robustBudget * (height + 1) ≤ 2 * stableBudget := by
    have hspanLoss' : robustBudget * height ≤ stableBudget := by
      simpa only [robustBudget, height, K] using hspanLoss
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have haccessible' : ∀ {B : Finset ℤ}, B ⊆ W →
      W.card ≤ B.card + robustBudget * (height + 1) → 0 ∈ B →
      ∀ d : {d // d ∈ relevant},
        ∃ e : ℕ, 0 < e ∧ e ≤ maxRank ∧
          ∃ V : HDimension.HApproximation B (hAt d) e scaleNum scaleDen,
            (2 * scaleDen) ^ e * (hAt d + 1) ^ (e - 1) <
              (scaleNum * hAt d) ^ e := by
    intro B hBW hcard hzeroB d
    apply haccessible hBW (B := B) ?_ hzeroB d
    simpa only [robustBudget, height, K] using hcard
  obtain ⟨B, hBW, hzeroB, hlossB, hspanB⟩ :=
    span_pruning_lemma232_of_centeredHApproximations
      hzeroW hweakW (fun z hz ↦ hA z (hWA hz)) hproper hAt
      hambient' hrank_le hh_le hlarge haccessible' hcap
  have hweakB : Stability.WeaklyStableFor B
      (Stability.minimalBoxFamily W) stableBudget maxRank (n ^ 2) := by
    apply Stability.WeaklyStableFor.delete hweakW hBW hzeroB hlossB
    have hspanLoss' : robustBudget * height ≤ stableBudget := by
      simpa only [robustBudget, height, K] using hspanLoss
    exact (Nat.add_le_add_right hspanLoss' stableBudget).trans_eq (by omega)
  have hsourceCard : A.card ≤ B.card +
      (2 * stableBudget) * boxPotential A maxRank + stableBudget := by
    have hspanLoss' : robustBudget * height ≤ stableBudget := by
      simpa only [robustBudget, height, K] using hspanLoss
    have hlossB' : W.card ≤ B.card + stableBudget :=
      hlossB.trans (Nat.add_le_add_left hspanLoss' B.card)
    omega
  have hstrong : Stability.StronglyStableFor B
      (Stability.minimalBoxFamily W) stableBudget maxRank (n ^ 2)
      relevant (Stability.centeredMinimalIdentificationFamily hproper) C0 := by
    refine ⟨hweakB, hC0, ?_⟩
    intro d hd B' hB'B hcard hzeroB'
    exact hspanB hd hB'B (by simpa only [robustBudget] using hcard) hzeroB'
  exact ⟨{
    weakCore := W
    core := B
    relevant := relevant
    boxesProper := hproper
    hAt := hAt
    weakCore_subset_source := hWA
    zero_mem_weakCore := hzeroW
    weakCore_stable := hweakW
    approximation := hambient
    rank_le := hrank_le
    horizon_le := hh_le
    horizon_large := hlarge
    accessible := haccessible
    spanLoss := hspanLoss
    core_subset_weakCore := hBW
    zero_mem_core := hzeroB
    source_card_le := hsourceCard
    stable := hstrong
    hAt_eq_fold := hAtFold
    relevant_nonempty_or_weakCore_small := hbranch }⟩

end

end Erdos186.CFP.Preprocessing

#print axioms
  Erdos186.CFP.PreprocessingBilu.retainedDyadicPreprocessingHApproximationArgument_of_uniform_source
#print axioms
  Erdos186.CFP.PreprocessingBilu.exists_retainedDyadicPreprocessingPackage_of_biluFreiman
#print axioms
  Erdos186.CFP.Preprocessing.exists_dyadicCenteredPreprocessingData
