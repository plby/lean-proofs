import ErdosProblems.Erdos239.External.Erdos67.ResidueLogPhaseBounds
import ErdosProblems.Erdos239.External.Erdos67.LogBandSelector
import ErdosProblems.Erdos239.External.Erdos67.LogBandDecay

/-!
# A uniform finite-depth residue-prefix estimate

The finitely many logarithmic height bands are combined here.  Short
residue prefixes are bounded trivially; every longer prefix lies either in
the separated second-derivative region or in one of the controlled-Weyl
bands selected at fixed depth.
-/

open scoped BigOperators
open Filter

namespace Erdos67.UniformResidueLogPhase

noncomputable section

open Erdos1149
open Erdos67.LogPhaseSum
open Erdos67.LogPhaseHigherDerivative
open Erdos67.LSeriesLogPhaseBridge
open Erdos67.ResidueLogPhase
open Erdos67.ResidueLogPhaseBounds
open Erdos67.LogBandCoverage
open Erdos67.LogBandSelector
open Erdos67.LogBandDecay
open Erdos67.LogWeylParameters

/-- The unnormalized error which bounds every residue prefix at comparison
scale `X`. -/
def uniformResidueBlockError (R X : ℕ) : ℝ :=
  2 * finiteBandDecay R X * X + rOneLagBudget X + 1

theorem uniformResidueBlockError_nonneg (R X : ℕ) :
    0 ≤ uniformResidueBlockError R X := by
  unfold uniformResidueBlockError
  have hmain : 0 ≤ 2 * finiteBandDecay R X * (X : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) (finiteBandDecay_nonneg R X))
      (Nat.cast_nonneg X)
  positivity

/-- The natural comparison scale is exactly the least progression index. -/
theorem comparisonScale_eq_firstResidueIndex
    {q A : ℕ} [NeZero q] (c : ZMod q) :
    firstResidueAtOrAbove A c / q = firstResidueIndex A c := by
  unfold firstResidueAtOrAbove
  rw [Nat.add_mul_div_left _ _ (Nat.pos_of_ne_zero (NeZero.ne q)),
    Nat.div_eq_of_lt c.val_lt, zero_add]

/-- The least progression index is no larger than the left endpoint. -/
theorem comparisonScale_le_leftEndpoint
    {q A : ℕ} [NeZero q] (c : ZMod q) :
    firstResidueAtOrAbove A c / q ≤ A := by
  rw [comparisonScale_eq_firstResidueIndex]
  apply firstResidueIndex_min c
  have hq : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  exact le_trans (by simpa only [one_mul] using Nat.mul_le_mul_right A hq)
    (Nat.le_add_left (q * A) c.val)

/-- A lower bound divisible by the modulus passes to every residue-class
comparison scale. -/
theorem comparisonScale_ge_of_mul_le
    {q A X₀ : ℕ} [NeZero q] (c : ZMod q) (h : q * X₀ ≤ A) :
    X₀ ≤ firstResidueAtOrAbove A c / q := by
  apply (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero (NeZero.ne q))).2
  simpa only [mul_comm] using h.trans (le_firstResidueAtOrAbove c)

/-- The uniform residue error is little-o of its comparison scale. -/
theorem exists_uniformResidueBlockError_threshold
    (R : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀,
      uniformResidueBlockError R X ≤ η * X := by
  obtain ⟨Xd, hXd⟩ := exists_finiteBandDecay_threshold R
    (show 0 < η / 6 by positivity)
  have ht : Tendsto (fun X : ℕ ↦ (X : ℝ) ^ (15 / 16 : ℝ))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 15 / 16)).comp
      tendsto_natCast_atTop_atTop
  obtain ⟨Xp, hXp⟩ := eventually_atTop.1
    (ht.eventually (eventually_ge_atTop (6 / η)))
  obtain ⟨Xl : ℕ, hXl⟩ := exists_nat_ge (3 / η)
  refine ⟨max 1 (max Xd (max Xp Xl)), ?_⟩
  intro X hX
  have hXone : 1 ≤ X := (Nat.le_max_left 1 _).trans hX
  have hXdX : Xd ≤ X := (Nat.le_max_left Xd (max Xp Xl)).trans
    ((Nat.le_max_right 1 (max Xd (max Xp Xl))).trans hX)
  have hXpX : Xp ≤ X := (Nat.le_max_left Xp Xl).trans
    ((Nat.le_max_right Xd (max Xp Xl)).trans
      ((Nat.le_max_right 1 (max Xd (max Xp Xl))).trans hX))
  have hXlX : Xl ≤ X := (Nat.le_max_right Xp Xl).trans
    ((Nat.le_max_right Xd (max Xp Xl)).trans
      ((Nat.le_max_right 1 (max Xd (max Xp Xl))).trans hX))
  have hdecay := hXd X hXdX
  have hpower := hXp X hXpX
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hXone)
  have hceil : (rOneLagBudget X : ℝ) ≤
      2 * (X : ℝ) ^ (1 / 16 : ℝ) := by
    unfold rOneLagBudget
    exact AnalyticParameters.natCeil_le_two_mul
      (Real.one_le_rpow (by exact_mod_cast hXone) (by norm_num))
  have hbudget : (rOneLagBudget X : ℝ) ≤ (η / 3) * X := by
    have hηnonneg : 0 ≤ η / 3 := by positivity
    have hfactor : (2 : ℝ) ≤
        (η / 3) * (X : ℝ) ^ (15 / 16 : ℝ) := by
      calc
        (2 : ℝ) = (η / 3) * (6 / η) := by field_simp; norm_num
        _ ≤ (η / 3) * (X : ℝ) ^ (15 / 16 : ℝ) :=
          mul_le_mul_of_nonneg_left hpower hηnonneg
    have hroot : 0 ≤ (X : ℝ) ^ (1 / 16 : ℝ) :=
      Real.rpow_nonneg hXpos.le _
    have hmul : 2 * (X : ℝ) ^ (1 / 16 : ℝ) ≤
        (η / 3) * ((X : ℝ) ^ (15 / 16 : ℝ) *
          (X : ℝ) ^ (1 / 16 : ℝ)) := by
      calc
        2 * (X : ℝ) ^ (1 / 16 : ℝ) ≤
            ((η / 3) * (X : ℝ) ^ (15 / 16 : ℝ)) *
              (X : ℝ) ^ (1 / 16 : ℝ) :=
          mul_le_mul_of_nonneg_right hfactor hroot
        _ = (η / 3) * ((X : ℝ) ^ (15 / 16 : ℝ) *
              (X : ℝ) ^ (1 / 16 : ℝ)) := by ring
    calc
      (rOneLagBudget X : ℝ) ≤ 2 * (X : ℝ) ^ (1 / 16 : ℝ) := hceil
      _ ≤ (η / 3) * ((X : ℝ) ^ (15 / 16 : ℝ) *
          (X : ℝ) ^ (1 / 16 : ℝ)) := hmul
      _ = (η / 3) * X := by
        rw [← Real.rpow_add hXpos]
        norm_num
  have hone : (1 : ℝ) ≤ (η / 3) * X := by
    have hcast : (3 / η : ℝ) ≤ X := hXl.trans (by exact_mod_cast hXlX)
    calc
      (1 : ℝ) = (η / 3) * (3 / η) := by field_simp
      _ ≤ (η / 3) * X :=
        mul_le_mul_of_nonneg_left hcast (by positivity)
  unfold uniformResidueBlockError
  have hXnonneg : (0 : ℝ) ≤ X := hXpos.le
  calc
    2 * finiteBandDecay R X * X + rOneLagBudget X + 1 ≤
        2 * (η / 6) * X + (η / 3) * X + (η / 3) * X := by
      gcongr
    _ = η * X := by ring

private theorem rOneTerm_le_decay_mul
    {R X : ℕ} (hX : 1 ≤ X) :
    18 * (X : ℝ) ^ (63 / 64 : ℝ) ≤
      2 * finiteBandDecay R X * X := by
  have hXR : 0 < (X : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hpow : (X : ℝ) ^ (63 / 64 : ℝ) =
      (X : ℝ) ^ (-1 / 64 : ℝ) * X := by
    calc
      (X : ℝ) ^ (63 / 64 : ℝ) =
          (X : ℝ) ^ ((-1 / 64 : ℝ) + 1) := by norm_num
      _ = (X : ℝ) ^ (-1 / 64 : ℝ) * (X : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_add hXR]
      _ = (X : ℝ) ^ (-1 / 64 : ℝ) * X := by rw [Real.rpow_one]
  have hfirst : 9 * (X : ℝ) ^ (-1 / 64 : ℝ) ≤
      finiteBandDecay R X := by
    unfold finiteBandDecay
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun r hr ↦
      mul_nonneg (realStartBandConstant_nonneg r)
        (Real.rpow_nonneg (Nat.cast_nonneg X) _))
  rw [hpow]
  have hdouble : 18 * (X : ℝ) ^ (-1 / 64 : ℝ) ≤
      2 * finiteBandDecay R X := by linarith
  calc
    18 * ((X : ℝ) ^ (-1 / 64 : ℝ) * X) =
        (18 * (X : ℝ) ^ (-1 / 64 : ℝ)) * X := by ring
    _ ≤ (2 * finiteBandDecay R X) * X :=
      mul_le_mul_of_nonneg_right hdouble (Nat.cast_nonneg X)
    _ = 2 * finiteBandDecay R X * X := by ring

private theorem fixedBandTerm_le_decay_mul
    {R X r : ℕ} (hX : 1 ≤ X) (hr : r ∈ Finset.Icc 2 R) :
    realStartBandConstant r *
        (X : ℝ) ^ (1 - savingExponent r) ≤
      2 * finiteBandDecay R X * X := by
  have hXR : 0 < (X : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hpow : (X : ℝ) ^ (1 - savingExponent r) =
      (X : ℝ) ^ (-savingExponent r) * X := by
    calc
      (X : ℝ) ^ (1 - savingExponent r) =
          (X : ℝ) ^ (-savingExponent r + 1) := by congr 1; ring
      _ = (X : ℝ) ^ (-savingExponent r) * (X : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_add hXR]
      _ = (X : ℝ) ^ (-savingExponent r) * X := by rw [Real.rpow_one]
  have htermNonneg : 0 ≤ realStartBandConstant r *
      (X : ℝ) ^ (-savingExponent r) :=
    mul_nonneg (realStartBandConstant_nonneg r)
      (Real.rpow_nonneg (Nat.cast_nonneg X) _)
  have htermSum : realStartBandConstant r *
      (X : ℝ) ^ (-savingExponent r) ≤
      ∑ j ∈ Finset.Icc 2 R,
        realStartBandConstant j * (X : ℝ) ^ (-savingExponent j) := by
    exact Finset.single_le_sum
      (fun j hj ↦ mul_nonneg (realStartBandConstant_nonneg j)
        (Real.rpow_nonneg (Nat.cast_nonneg X) (-savingExponent j))) hr
  have htermDecay : realStartBandConstant r *
      (X : ℝ) ^ (-savingExponent r) ≤ finiteBandDecay R X := by
    unfold finiteBandDecay
    exact htermSum.trans (le_add_of_nonneg_left
      (mul_nonneg (by norm_num)
        (Real.rpow_nonneg (Nat.cast_nonneg X) _)))
  rw [hpow]
  have hdecayNonneg := finiteBandDecay_nonneg R X
  have hdouble : realStartBandConstant r *
      (X : ℝ) ^ (-savingExponent r) ≤ 2 * finiteBandDecay R X := by
    linarith
  calc
    realStartBandConstant r *
        ((X : ℝ) ^ (-savingExponent r) * X) =
        (realStartBandConstant r *
          (X : ℝ) ^ (-savingExponent r)) * X := by ring
    _ ≤ (2 * finiteBandDecay R X) * X :=
      mul_le_mul_of_nonneg_right hdouble (Nat.cast_nonneg X)
    _ = 2 * finiteBandDecay R X * X := by ring

/-- At every sufficiently large comparison scale, all residue-class
prefixes in the first `R` logarithmic height bands obey one uniform bound. -/
theorem exists_uniformResidueBlock_threshold (R : ℕ) (hR : 2 ≤ R) :
    ∃ X₀ : ℕ, ∀ {q A M : ℕ} [NeZero q] (c : ZMod q) {t : ℝ},
      0 < A → M ≤ 2 * A →
      X₀ ≤ firstResidueAtOrAbove A c / q →
      (firstResidueAtOrAbove A c : ℝ) / q ≤
        positiveLogCoefficient t →
      positiveLogCoefficient t <
        ((firstResidueAtOrAbove A c / q : ℕ) : ℝ) ^ (R + 1) →
      ‖residueClassSum (Finset.Icc A M) c
          (fun n ↦ natLogTwist n t)‖ ≤
        uniformResidueBlockError R (firstResidueAtOrAbove A c / q) := by
  obtain ⟨Xselector, hselector⟩ :=
    eventually_atTop.1 (eventually_fixedDepth_selector R hR)
  obtain ⟨Xweyl, hweyl⟩ := exists_residue_fixedDepthRange_threshold R
  refine ⟨max 1 (max Xselector Xweyl), ?_⟩
  intro q A M _ c t hA hM hXlarge hUa hupper
  let X : ℕ := firstResidueAtOrAbove A c / q
  let U : ℝ := (firstResidueAtOrAbove A c : ℝ) / q
  let a : ℝ := positiveLogCoefficient t
  let P : ℕ := residueIntervalLength A M c
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hXone : 1 ≤ X := (Nat.le_max_left 1 _).trans hXlarge
  have hXselector : Xselector ≤ X :=
    (Nat.le_max_left Xselector Xweyl).trans
      ((Nat.le_max_right 1 (max Xselector Xweyl)).trans hXlarge)
  have hXweyl : Xweyl ≤ X :=
    (Nat.le_max_right Xselector Xweyl).trans
      ((Nat.le_max_right 1 (max Xselector Xweyl)).trans hXlarge)
  have hn₀ : 0 < firstResidueAtOrAbove A c :=
    firstResidueAtOrAbove_pos c hA
  have hU : 0 < U := by dsimp only [U]; positivity
  have hXU : (X : ℝ) ≤ U := by
    dsimp only [X, U]
    exact Nat.cast_div_le
  have hUlt : U < (X : ℝ) + 1 := by
    have hnat : firstResidueAtOrAbove A c <
        q * (firstResidueAtOrAbove A c / q + 1) := by
      simpa only [mul_comm] using
        Nat.lt_mul_div_succ (firstResidueAtOrAbove A c) hq
    apply (div_lt_iff₀ (by exact_mod_cast hq : (0 : ℝ) < q)).2
    push_cast
    exact_mod_cast (by simpa only [X, mul_comm] using hnat)
  have hUX : U ≤ 2 * X := by
    have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hXone
    linarith
  have ha : 0 < a := hU.trans_le (by simpa only [U, a] using hUa)
  have ht : t ≠ 0 := by
    intro ht
    subst t
    simp [a, positiveLogCoefficient] at ha
  by_cases hPzero : P = 0
  · rw [norm_residueClassSum_natLogTwist_eq_positiveShifted c t hA]
    simp only [P, hPzero, Finset.range_zero, Finset.sum_empty, norm_zero]
    exact uniformResidueBlockError_nonneg R X
  have hPpos : 0 < P := Nat.pos_of_ne_zero hPzero
  by_cases hPshort : P ≤ rOneLagBudget X
  · rw [norm_residueClassSum_natLogTwist_eq_positiveShifted c t hA]
    have htrivial :
        ‖∑ j ∈ Finset.range P,
            HigherDerivative.phase (shiftedLogPhase a U j)‖ ≤ P := by
      calc
        ‖∑ j ∈ Finset.range P,
            HigherDerivative.phase (shiftedLogPhase a U j)‖ ≤
            ∑ j ∈ Finset.range P,
              ‖HigherDerivative.phase (shiftedLogPhase a U j)‖ :=
          norm_sum_le _ _
        _ = P := by simp
    change ‖∑ j ∈ Finset.range P,
        HigherDerivative.phase (shiftedLogPhase a U j)‖ ≤ _
    calc
      ‖∑ j ∈ Finset.range P,
          HigherDerivative.phase (shiftedLogPhase a U j)‖ ≤ P := htrivial
      _ ≤ rOneLagBudget X := by exact_mod_cast hPshort
      _ ≤ uniformResidueBlockError R X := by
        unfold uniformResidueBlockError
        have hmain : 0 ≤ 2 * finiteBandDecay R X * (X : ℝ) :=
          mul_nonneg (mul_nonneg (by norm_num) (finiteBandDecay_nonneg R X))
            (Nat.cast_nonneg X)
        linarith
  have hPlong : rOneLagBudget X + 1 ≤ P := by omega
  obtain hsecond | ⟨r, hrmem, hrboundary, hrupper⟩ :=
    hselector X hXselector ha hXU hUX
      (by simpa only [U, a] using hUa)
      (by simpa only [X, a] using hupper)
  · have hraw := norm_residueClassSum_natLogTwist_le_rOnePower
      c hA hM (by simpa only [X] using hXone)
      (by simpa only [X, P] using hPlong)
      hUa (by simpa only [X, U, a] using hsecond)
    calc
      ‖residueClassSum (Finset.Icc A M) c
          (fun n ↦ natLogTwist n t)‖ ≤
          18 * (X : ℝ) ^ (63 / 64 : ℝ) + 1 := by
        simpa only [X] using hraw
      _ ≤ uniformResidueBlockError R X := by
        unfold uniformResidueBlockError
        have hterm := rOneTerm_le_decay_mul (R := R) hXone
        have hbudget : (0 : ℝ) ≤ rOneLagBudget X := by positivity
        linarith
  · have hraw := hweyl (q := q) (A := A) (M := M) c (t := t) r
      hrmem hA hM ht hPpos hXweyl
      (by simpa only [X, a] using hrboundary)
      (by simpa only [X, a] using hrupper)
    have hterm := fixedBandTerm_le_decay_mul (X := X) hXone hrmem
    calc
      ‖residueClassSum (Finset.Icc A M) c
          (fun n ↦ natLogTwist n t)‖ ≤
          realStartBandConstant r *
            (X : ℝ) ^ (1 - savingExponent r) + 1 := by
        simpa only [realStartBandConstant, X] using hraw
      _ ≤ uniformResidueBlockError R X := by
        unfold uniformResidueBlockError
        have hbudget : (0 : ℝ) ≤ rOneLagBudget X := by positivity
        linarith

end

end Erdos67.UniformResidueLogPhase
