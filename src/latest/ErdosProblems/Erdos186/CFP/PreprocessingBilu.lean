/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Preprocessing

/-!
# The Bilu--Freiman input to CFP preprocessing

This module supplies the source-facing adapter between the uniform
`HDimension` construction and the approximation-family hypothesis of
`Preprocessing.preprocessing_lemma238`.

The first part records the finite telescoping argument implicit in CFP
Lemma 2.22: on a sufficiently long dyadic interval, the interval bound on
iterated sumsets forces the least slow-growth dimension to be uniformly
bounded.  Keeping this argument here means that the final preprocessing API
does not assume a family of dyadic-dimension certificates.
-/

namespace Erdos186.CFP.PreprocessingBilu

open Erdos186.CFP
open Erdos186.CFP.HDimension
open Erdos186.CFP.GrowthLemmas

/-- The elementary exponential bound used to absorb fixed constants into a
dyadic horizon. -/
theorem self_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hone : 1 ≤ 2 ^ n := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
      omega

/-- If the terminal dyadic sumset is smaller than the growth forced at
dimension `D`, the least slow-growth dimension is at most `D`. -/
theorem minimalDyadicGrowthDimension_le_of_terminal_card
    {A : Finset ℤ} {dimension D first last : ℕ}
    (hzero : 0 ∈ A)
    (hfirstLast : first < last)
    (hminimal : IsMinimalDyadicGrowthDimension A dimension first last)
    (hterminal :
      (multifoldSumset (2 ^ last) A).card ^ 2 <
        (2 ^ (2 * D + 1)) ^ (last - first)) :
    dimension ≤ D := by
  by_contra hdimension
  have hDdimension : D < dimension := Nat.lt_of_not_ge hdimension
  have hnotSlow := hminimal.2 D hDdimension
  have hgrowth : DyadicLowerGrowth A (D + 1) first last := by
    intro e hfirst heLast
    have hnotAt : ¬
        (multifoldSumset (2 ^ (e + 1)) A).card ^ 2 ≤
          2 ^ (2 * D + 1) *
            (multifoldSumset (2 ^ e) A).card ^ 2 := by
      intro hslow
      exact hnotSlow ⟨e, hfirst, heLast, hslow⟩
    have hfactor : 2 * (D + 1) - 1 = 2 * D + 1 := by omega
    rw [hfactor]
    exact Nat.lt_of_not_ge hnotAt
  have hsteps : 0 < last - first := Nat.sub_pos_of_lt hfirstLast
  have hlast : first + (last - first) = last :=
    Nat.add_sub_of_le hfirstLast.le
  have hiterate := dyadicLowerGrowth_iterate
    (A := A) (dimension := D + 1) (start := first)
    (steps := last - first) hsteps (by simpa [hlast] using hgrowth)
  have hfactor : 2 * (D + 1) - 1 = 2 * D + 1 := by omega
  rw [hfactor, hlast] at hiterate
  have hbasePos :
      0 < (multifoldSumset (2 ^ first) A).card := by
    exact Finset.card_pos.mpr
      ⟨0, zero_mem_multifoldSumset hzero (2 ^ first)⟩
  have hbaseSqPos :
      0 < (multifoldSumset (2 ^ first) A).card ^ 2 :=
    pow_pos hbasePos _
  have hlower :
      (2 ^ (2 * D + 1)) ^ (last - first) <
        (multifoldSumset (2 ^ last) A).card ^ 2 := by
    exact (Nat.le_mul_of_pos_right _ hbaseSqPos).trans_lt hiterate
  omega

/-- The endpoint estimate in the natural-number parameter regime of CFP
Lemma 2.22.  Here `h = horizonFactor * 2^last`, `n ≤ h^(D-1)`, and the
displayed lower bound on `last` is the finite version of taking `n`
sufficiently large. -/
theorem terminal_card_sq_lt_of_source_horizon
    {A : Finset ℤ} {n h horizonFactor D first last : ℕ}
    (hzero : 0 ∈ A)
    (hA : A ⊆ Finset.Icc (0 : ℤ) ((n : ℤ) - 1))
    (horizonFactor_pos : 0 < horizonFactor)
    (hD : 2 ≤ D)
    (hh : h = horizonFactor * 2 ^ last)
    (hhle : h ≤ n)
    (hnpower : n ≤ h ^ (D - 1))
    (hfirstLast : first < last)
    (hlastLarge :
      (2 * D + 1) * first + 2 * horizonFactor * (D - 1) < last) :
    (multifoldSumset (2 ^ last) A).card ^ 2 <
      (2 ^ (2 * D + 1)) ^ (last - first) := by
  have hhpos : 0 < h := by
    rw [hh]
    exact Nat.mul_pos horizonFactor_pos (by positivity)
  have hnpos : 0 < n := hhpos.trans_le hhle
  have hcard :
      (multifoldSumset (2 ^ last) A).card ≤ 2 ^ last * n :=
    card_multifoldSumset_le_mul_of_subset_Icc (by positivity) hnpos hA
  have hhExp : h ≤ 2 ^ (horizonFactor + last) := by
    rw [hh, pow_add]
    exact Nat.mul_le_mul_right (2 ^ last)
      (self_le_two_pow horizonFactor)
  have hnExp : n ≤ 2 ^ ((horizonFactor + last) * (D - 1)) := by
    calc
      n ≤ h ^ (D - 1) := hnpower
      _ ≤ (2 ^ (horizonFactor + last)) ^ (D - 1) :=
        Nat.pow_le_pow_left hhExp _
      _ = 2 ^ ((horizonFactor + last) * (D - 1)) := by
        rw [pow_mul]
  let upperExponent := last + (horizonFactor + last) * (D - 1)
  have hcardExp :
      (multifoldSumset (2 ^ last) A).card ≤ 2 ^ upperExponent := by
    calc
      (multifoldSumset (2 ^ last) A).card ≤ 2 ^ last * n := hcard
      _ ≤ 2 ^ last * 2 ^ ((horizonFactor + last) * (D - 1)) := by
        gcongr
      _ = 2 ^ upperExponent := by
        rw [← pow_add]
  have hcardSq :
      (multifoldSumset (2 ^ last) A).card ^ 2 ≤
        2 ^ (2 * upperExponent) := by
    calc
      (multifoldSumset (2 ^ last) A).card ^ 2 ≤
          (2 ^ upperExponent) ^ 2 := Nat.pow_le_pow_left hcardExp _
      _ = 2 ^ (2 * upperExponent) := by
        rw [← pow_mul]
        simp [mul_comm]
  have hsub : last - first + first = last := Nat.sub_add_cancel hfirstLast.le
  have hDsub : D - 1 + 1 = D := Nat.sub_add_cancel (by omega)
  have hexponent :
      2 * upperExponent < (2 * D + 1) * (last - first) := by
    dsimp only [upperExponent]
    ring_nf at hlastLarge ⊢
    nlinarith [hsub, hDsub]
  have hpow :
      2 ^ (2 * upperExponent) <
        2 ^ ((2 * D + 1) * (last - first)) :=
    Nat.pow_lt_pow_right (by omega) hexponent
  calc
    (multifoldSumset (2 ^ last) A).card ^ 2 ≤
        2 ^ (2 * upperExponent) := hcardSq
    _ < 2 ^ ((2 * D + 1) * (last - first)) := hpow
    _ = (2 ^ (2 * D + 1)) ^ (last - first) := by rw [pow_mul]

/-- The least slow-growth dimension in every source horizon is uniformly
bounded by `D`; no dimension certificate is an input. -/
theorem exists_bounded_minimalDyadicGrowthDimension
    {A : Finset ℤ} {n h horizonFactor D first last : ℕ}
    (hzero : 0 ∈ A)
    (hA : A ⊆ Finset.Icc (0 : ℤ) ((n : ℤ) - 1))
    (horizonFactor_pos : 0 < horizonFactor)
    (hD : 2 ≤ D)
    (hh : h = horizonFactor * 2 ^ last)
    (hhle : h ≤ n)
    (hnpower : n ≤ h ^ (D - 1))
    (hfirstLast : first < last)
    (hlastLarge :
      (2 * D + 1) * first + 2 * horizonFactor * (D - 1) < last) :
    ∃ dimension ≤ D,
      IsMinimalDyadicGrowthDimension A dimension first last := by
  obtain ⟨dimension, hminimal⟩ :=
    exists_minimalDyadicGrowthDimension hzero hfirstLast
  refine ⟨dimension, ?_, hminimal⟩
  apply minimalDyadicGrowthDimension_le_of_terminal_card hzero hfirstLast hminimal
  exact terminal_card_sq_lt_of_source_horizon hzero hA horizonFactor_pos hD
    hh hhle hnpower hfirstLast hlastLarge

/-! ## Uniform numerical estimates at preprocessing scale -/

/-- The large-`h` hypothesis used by `preprocessing_lemma238` implies its
strict rank-flexible approximation inequality. -/
theorem approximation_numeric_of_preprocessing_large
    {scaleDen D e h : ℕ}
    (hscaleDen : 0 < scaleDen)
    (he : 0 < e) (heD : e ≤ D)
    (hlarge :
      4 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D ≤ h) :
    (2 * scaleDen) ^ e * (h + 1) ^ (e - 1) < h ^ e := by
  let a := 4 * scaleDen
  have haPos : 0 < a := by dsimp [a]; positivity
  have haPowPos : 0 < a ^ D := pow_pos haPos _
  have hleftFactor : 2 ≤ 4 * (6 * scaleDen) ^ D := by
    have : 0 < (6 * scaleDen) ^ D := by positivity
    nlinarith
  have haPowLt : a ^ D < h := by
    have hstrict :
        a ^ D < (4 * (6 * scaleDen) ^ D) * a ^ D := by
      nlinarith
    exact hstrict.trans_le (by simpa [a, mul_assoc] using hlarge)
  have hhPos : 0 < h := haPowPos.trans haPowLt
  have hsucc : h + 1 ≤ 2 * h := by omega
  have htwoPow : 2 ^ (e - 1) ≤ 2 ^ e :=
    Nat.pow_le_pow_right (by omega) (Nat.sub_le e 1)
  have haMono : a ^ e ≤ a ^ D :=
    Nat.pow_le_pow_right haPos heD
  calc
    (2 * scaleDen) ^ e * (h + 1) ^ (e - 1)
        ≤ (2 * scaleDen) ^ e * (2 * h) ^ (e - 1) := by gcongr
    _ = (2 * scaleDen) ^ e *
          (2 ^ (e - 1) * h ^ (e - 1)) := by simp only [mul_pow]
    _ ≤ (2 * scaleDen) ^ e *
          (2 ^ e * h ^ (e - 1)) := by gcongr
    _ = a ^ e * h ^ (e - 1) := by
      rw [show (2 * scaleDen) ^ e * (2 ^ e * h ^ (e - 1)) =
          ((2 * scaleDen) ^ e * 2 ^ e) * h ^ (e - 1) by ring,
        ← mul_pow]
      dsimp [a]
      ring
    _ ≤ a ^ D * h ^ (e - 1) := Nat.mul_le_mul_right _ haMono
    _ < h * h ^ (e - 1) := Nat.mul_lt_mul_of_pos_right haPowLt (by positivity)
    _ = h ^ e := by
      calc
        h * h ^ (e - 1) = h ^ (e - 1 + 1) := (pow_succ' h (e - 1)).symm
        _ = h ^ e := by congr 1; omega

/-- The same source threshold also makes the canonical minimal bounding box
proper at every positive certified rank. -/
theorem boundingBox_proper_numeric_of_preprocessing_large
    {scaleDen D e h : ℕ}
    (hscaleDen : 0 < scaleDen)
    (he : 0 < e) (heD : e ≤ D)
    (hlarge :
      4 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D ≤ h) :
    (2 * scaleDen) ^ e * (e * 1 * (h + 1) ^ (e - 1)) < h ^ e := by
  let a := 4 * scaleDen
  let b := 6 * scaleDen
  have haPos : 0 < a := by dsimp [a]; positivity
  have hbPos : 0 < b := by dsimp [b]; positivity
  have hDPos : 0 < D := he.trans_le heD
  have hDTwo : D ≤ 2 ^ D := self_le_two_pow D
  have htwoB : 2 ≤ b := by dsimp [b]; omega
  have hpowBase : 2 ^ D ≤ b ^ D :=
    Nat.pow_le_pow_left htwoB _
  have hDle : D ≤ b ^ D := hDTwo.trans hpowBase
  have hbPowPos : 0 < b ^ D := pow_pos hbPos _
  have hDlt : D < 4 * b ^ D := by nlinarith
  have haMono : a ^ e ≤ a ^ D := Nat.pow_le_pow_right haPos heD
  have hcoeff : e * a ^ e < 4 * b ^ D * a ^ D := by
    calc
      e * a ^ e ≤ D * a ^ D := Nat.mul_le_mul heD haMono
      _ < (4 * b ^ D) * a ^ D :=
        Nat.mul_lt_mul_of_pos_right hDlt (pow_pos haPos _)
  have hcoeffH : e * a ^ e < h := by
    exact hcoeff.trans_le (by simpa [a, b, mul_assoc] using hlarge)
  have hhPos : 0 < h := (Nat.zero_le _).trans_lt hcoeffH
  have hsucc : h + 1 ≤ 2 * h := by omega
  have htwoPow : 2 ^ (e - 1) ≤ 2 ^ e :=
    Nat.pow_le_pow_right (by omega) (Nat.sub_le e 1)
  calc
    (2 * scaleDen) ^ e *
          (e * 1 * (h + 1) ^ (e - 1))
        ≤ e * ((2 * scaleDen) ^ e * (2 * h) ^ (e - 1)) := by
          have hp := Nat.pow_le_pow_left hsucc (e - 1)
          simp only [mul_one]
          calc
            (2 * scaleDen) ^ e *
                  (e * (h + 1) ^ (e - 1))
                = e * ((2 * scaleDen) ^ e *
                    (h + 1) ^ (e - 1)) := by ring
            _ ≤ e * ((2 * scaleDen) ^ e *
                    (2 * h) ^ (e - 1)) := by gcongr
    _ = e * ((2 * scaleDen) ^ e *
          (2 ^ (e - 1) * h ^ (e - 1))) := by simp only [mul_pow]
    _ ≤ e * ((2 * scaleDen) ^ e *
          (2 ^ e * h ^ (e - 1))) := by gcongr
    _ = (e * a ^ e) * h ^ (e - 1) := by
      rw [show e * ((2 * scaleDen) ^ e * (2 ^ e * h ^ (e - 1))) =
          (e * ((2 * scaleDen) ^ e * 2 ^ e)) * h ^ (e - 1) by ring,
        ← mul_pow]
      dsimp [a]
      ring
    _ < h * h ^ (e - 1) := Nat.mul_lt_mul_of_pos_right hcoeffH (by positivity)
    _ = h ^ e := by
      calc
        h * h ^ (e - 1) = h ^ (e - 1 + 1) := (pow_succ' h (e - 1)).symm
        _ = h ^ e := by congr 1; omega

/-- A positive-rank source approximation certifies properness of the
canonical minimal bounding box used by `RelevantBoxesProper`. -/
theorem boundingBox_proper_of_sourceHApproximation
    {A : Finset ℤ} {h e propernessDenominator D : ℕ}
    (W : HApproximation A h e 1 (2 * propernessDenominator))
    (hdenominator : 0 < propernessDenominator)
    (he : 0 < e) (heD : e ≤ D)
    (hlarge :
      4 * (6 * (2 * propernessDenominator)) ^ D *
          (4 * (2 * propernessDenominator)) ^ D ≤ h) :
    (BoundingBox.dBoundingBox A e he).progression.Proper := by
  have hdilate :
      ((BoundingBox.dBoundingBox A e he).progression.dilate 1).Proper := by
    have hhPos : 0 < h := W.scale_pos.trans_le W.scale_le
    apply W.boundingBox_dilate_proper_of_numeric he (by omega)
    simpa only [one_mul] using
      boundingBox_proper_numeric_of_preprocessing_large
        (Nat.mul_pos (by omega) hdenominator) he heD hlarge
  exact Erdos186.GAP.SProper.proper
    (Erdos186.GAP.sProper_of_dilate_proper
      (BoundingBox.dBoundingBox A e he).progression 1 hdilate) le_rfl

/-! ## The exact preprocessing callback -/

/-- Rank zero can approximate only the exceptional set `{0}`. -/
theorem HApproximation.rank_pos_of_ne_singleton_zero
    {A : Finset ℤ} {h rank scaleNum scaleDen : ℕ}
    (W : HApproximation A h rank scaleNum scaleDen)
    (hne : A ≠ {0}) : 0 < rank := by
  by_contra hrank
  have hrankZero : rank = 0 := Nat.eq_zero_of_not_pos hrank
  subst rank
  apply hne
  ext z
  constructor
  · intro hz
    have hzmem := BiluFreiman.mem_integerCarrier_iff.mp (W.contains hz)
    have hzeromem :=
      BiluFreiman.mem_integerCarrier_iff.mp (W.contains W.zero_mem)
    rw [GAPBuilders.rankZero_carrier] at hzmem hzeromem
    have hzpoint : BiluFreiman.integerPoint z =
        BiluFreiman.integerPoint 0 := by
      exact (Finset.mem_singleton.mp hzmem).trans
        (Finset.mem_singleton.mp hzeromem).symm
    have := congrArg BiluFreiman.pointInteger hzpoint
    simpa only [BiluFreiman.pointInteger_integerPoint,
      Finset.mem_singleton] using this
  · intro hz
    have hzzero : z = 0 := Finset.mem_singleton.mp hz
    simpa only [hzzero] using W.zero_mem

/-- This is definitionally the full `happrox` argument expected by
`Preprocessing.preprocessing_lemma238`.  Naming it avoids any weaker
intermediate interface. -/
def PreprocessingHApproximationArgument
    (A : Finset ℤ) (stableBudget maxRank n C0 scaleNum scaleDen : ℕ) : Prop :=
  ∀ {W : Finset ℤ}, W ⊆ A → 0 ∈ W →
    Stability.WeaklyStableMinimalFor W (2 * stableBudget) maxRank n →
    ∃ (relevant : Finset ℕ)
      (hproper : Stability.RelevantBoxesProper W relevant)
      (hAt : {d // d ∈ relevant} → ℕ),
      (∀ d : {d // d ∈ relevant},
        Nonempty
          (HApproximation W (hAt d) d.1 scaleNum scaleDen)) ∧
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
            (4 * scaleDen) ^ maxRank)) ≤ stableBudget

/-- Choosing the robustness denominator one larger than the logarithmic
index height makes the final pruning-loss inequality automatic. -/
theorem spanLoss_le_of_height_succ
    (stableBudget height : ℕ) :
    (stableBudget / (height + 1)) * height ≤ stableBudget := by
  calc
    (stableBudget / (height + 1)) * height ≤
        (stableBudget / (height + 1)) * (height + 1) := by
      exact Nat.mul_le_mul_left _ (by omega)
    _ ≤ stableBudget := Nat.div_mul_le_self _ _

/-- Common scale denominator supplied to preprocessing by the source
`HApproximation` construction. -/
def preprocessingScaleDen (propernessDenominator : ℕ) : ℕ :=
  2 * propernessDenominator

/-- The quotient-packing bound appearing in CFP Lemma 2.32. -/
def preprocessingIndexBound (D propernessDenominator : ℕ) : ℕ :=
  4 * (6 * preprocessingScaleDen propernessDenominator) ^ D *
    (4 * preprocessingScaleDen propernessDenominator) ^ D

/-- A uniform robustness denominator large enough for the entire subgroup
pruning chain. -/
def preprocessingRobustnessDenominator
    (D propernessDenominator : ℕ) : ℕ :=
  D * Nat.log 2 (preprocessingIndexBound D propernessDenominator) + 1

/-- The uniform source consumer, together with the telescoping horizon
bound, supplies exactly the approximation family requested by CFP
preprocessing.  The relevant set is the certified ambient rank.  In the
degenerate regime where an accessible subset could be `{0}`, the subgroup
pruning family is empty; in the source regime the cardinal loss bound rules
this branch out. -/
theorem preprocessingHApproximationArgument_of_uniform_source
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
    {A : Finset ℤ} {n h last stableBudget : ℕ}
    (hzero : 0 ∈ A)
    (hA : A ⊆ Finset.Icc (0 : ℤ) ((n : ℤ) - 1))
    (hh : h = horizonFactor * 2 ^ last)
    (hhle : h ≤ n)
    (hnpower : n ≤ h ^ (D - 1))
    (hfirstLast : first < last)
    (hlastLarge :
      (2 * D + 1) * first + 2 * horizonFactor * (D - 1) < last)
    (hlarge : preprocessingIndexBound D propernessDenominator ≤ h)
    (hdenominatorLarge : propernessDenominator ≤ h) :
    PreprocessingHApproximationArgument A stableBudget D n
      (preprocessingRobustnessDenominator D propernessDenominator) 1
      (preprocessingScaleDen propernessDenominator) := by
  intro W hWA hzeroW _hstable
  let scaleDen := preprocessingScaleDen propernessDenominator
  let indexBound := preprocessingIndexBound D propernessDenominator
  let height := D * Nat.log 2 indexBound
  let C0 := preprocessingRobustnessDenominator D propernessDenominator
  have hC0 : C0 = height + 1 := by
    rfl
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
    have hWinterval : W ⊆ Finset.Icc (0 : ℤ) ((n : ℤ) - 1) :=
      hWA.trans hA
    obtain ⟨dimension, hdimensionD, hminimal⟩ :=
      exists_bounded_minimalDyadicGrowthDimension hzeroW hWinterval
        horizonFactor_pos hD hh hhle hnpower hfirstLast hlastLarge
    obtain ⟨rank, hrankDimension, happroxRank⟩ :=
      hconsumer hzeroW hdimensionD hminimal hthreshold (by rw [hh])
        (by
          rw [hh]
          exact Nat.mul_lt_mul_of_pos_left
            (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self last))
            horizonFactor_pos)
        hdenominatorLarge
    let V : HApproximation W h rank 1 scaleDen :=
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
    let hAt : {d // d ∈ relevant} → ℕ := fun _ ↦ h
    refine ⟨relevant, hproper, hAt, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro d
      have hdrank : d.1 = rank := by
        simpa only [relevant, Finset.mem_singleton] using d.2
      simpa only [hAt, hdrank] using happroxRank
    · intro d
      have hdrank : d.1 = rank := by
        simpa only [relevant, Finset.mem_singleton] using d.2
      simpa only [hdrank] using hrank
    · intro d
      exact hhle
    · intro d
      simpa only [hAt, scaleDen, indexBound, preprocessingIndexBound,
        preprocessingScaleDen] using hlarge
    · intro B hBW hcard hzeroB d
      have hBne : B ≠ {0} := by
        apply haccessible hBW _ hzeroB
        simpa only [C0, height, indexBound, preprocessingIndexBound] using hcard
      have hBinterval : B ⊆ Finset.Icc (0 : ℤ) ((n : ℤ) - 1) :=
        hBW.trans hWinterval
      obtain ⟨dimensionB, hdimensionBD, hminimalB⟩ :=
        exists_bounded_minimalDyadicGrowthDimension hzeroB hBinterval
          horizonFactor_pos hD hh hhle hnpower hfirstLast hlastLarge
      obtain ⟨rankB, hrankBDimension, happroxB⟩ :=
        hconsumer hzeroB hdimensionBD hminimalB hthreshold (by rw [hh])
          (by
            rw [hh]
            exact Nat.mul_lt_mul_of_pos_left
              (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self last))
              horizonFactor_pos)
          hdenominatorLarge
      let VB : HApproximation B h rankB 1 scaleDen :=
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
    · simpa only [C0, height, indexBound, preprocessingIndexBound] using hspanLoss
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
    refine ⟨relevant, hproper, hAt, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    · simpa only [C0, height, indexBound, preprocessingIndexBound] using hspanLoss

/-- Uniform source-facing form of the full preprocessing approximation
callback.  All Bilu--Freiman constants and both preprocessing denominators
are selected before the input set and its weak core. -/
theorem exists_preprocessingHApproximationArgument_of_biluFreiman
    (hBF : BiluFreiman.BiluFreimanStatement) (D : ℕ) (hD : 2 ≤ D) :
    ∃ first horizonFactor propernessDenominator C0 : ℕ,
      0 < first ∧ 0 < horizonFactor ∧ 0 < propernessDenominator ∧
      0 < C0 ∧
      C0 = preprocessingRobustnessDenominator D propernessDenominator ∧
      ∀ {A : Finset ℤ} {n h last stableBudget : ℕ},
        0 ∈ A →
        A ⊆ Finset.Icc (0 : ℤ) ((n : ℤ) - 1) →
        h = horizonFactor * 2 ^ last →
        h ≤ n →
        n ≤ h ^ (D - 1) →
        first < last →
        (2 * D + 1) * first +
            2 * horizonFactor * (D - 1) < last →
        preprocessingIndexBound D propernessDenominator ≤ h →
        PreprocessingHApproximationArgument A stableBudget D n C0 1
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
  intro A n h last stableBudget hzero hA hh hhle hnpower hfirstLast
    hlastLarge hlarge
  have hdenominatorLarge : propernessDenominator ≤ h := by
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
  intro W hWA hzeroW hstable
  have hresult := preprocessingHApproximationArgument_of_uniform_source
    (stableBudget := stableBudget) hhorizonFactor hpropernessDenominator hD
    hthreshold (by
      intro S q dimension first' last' hzeroS hdimension hminimal
        hthreshold' hlower hupper hdenominator'
      simpa only [preprocessingScaleDen] using
        hconsumer hzeroS hdimension hminimal hthreshold' hlower hupper
          hdenominator')
    hzero hA hh hhle hnpower hfirstLast hlastLarge hlarge
    hdenominatorLarge hWA hzeroW hstable
  simpa only [C0] using hresult

/-! Axiom audit for the terminal handoff. -/

#print axioms exists_bounded_minimalDyadicGrowthDimension
#print axioms preprocessingHApproximationArgument_of_uniform_source
#print axioms exists_preprocessingHApproximationArgument_of_biluFreiman

end Erdos186.CFP.PreprocessingBilu
