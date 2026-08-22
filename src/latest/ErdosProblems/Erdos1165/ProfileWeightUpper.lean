/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.GaussianMultiBlockProfile
import ErdosProblems.Erdos1165.ProfileListExponent
import ErdosProblems.Erdos1165.ProfileA11Tail
import ErdosProblems.Erdos1165.AppendixA11A12OnePoint
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.PSeries
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# An upper bound for the complete constrained profile mass

This file proves the upper/comparability half of the HLOZ Appendix-A profile
estimate.  It complements the lower estimates in `ProfileA11Assembly`.
-/

open scoped BigOperators

namespace Erdos1165.ProfileWeightUpper

noncomputable section

open AppendixFirstMoment ProfileSmallBall ProfileTaylor ProfileA11Assembly
  ProfileA11Tail ProfileListExponent GaussianSmallBall GaussianMultiBlockProfile
  AppendixA11A12OnePoint StirlingLocalCLT
open MeasureTheory Set

/-- Total mass of one lattice Gaussian edge. -/
def gaussianStepTotalMass (l : ℕ) : ℝ :=
  ∑' d : ℤ, gaussianStepWeight l d

/-- The normalized lattice Gaussian has total mass at most `exp (1/l)`.
The proof is the integral test on the positive half-line. -/
lemma gaussianStepTotalMass_le_exp_inv {l : ℕ} (hl : 0 < l) :
    gaussianStepTotalMass l ≤ Real.exp (1 / (l : ℝ)) := by
  let b : ℝ := 1 / (8 * (l : ℝ) ^ 2)
  let D : ℝ := 2 * Real.sqrt (2 * Real.pi) * l
  let f : ℝ → ℝ := fun x ↦ Real.exp (-b * x ^ 2)
  have hb : 0 < b := by dsimp [b]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hanti : AntitoneOn f (Set.Ici 0) := by
    intro x hx y hy hxy
    apply Real.exp_le_exp.mpr
    change 0 ≤ x at hx
    change 0 ≤ y at hy
    have hsq : x ^ 2 ≤ y ^ 2 := (sq_le_sq₀ hx hy).2 hxy
    nlinarith
  have hint : IntegrableOn f (Set.Ioi 0) := by
    exact (integrable_exp_neg_mul_sq hb).integrableOn
  have hnonneg : ∀ x ∈ Set.Ioi (0 : ℝ), 0 ≤ f x := by
    intro x hx
    exact Real.exp_nonneg _
  have htail := hanti.tsum_add_one_le_integral hint hnonneg
  have hintEq : (∫ x in Set.Ioi (0 : ℝ), f x) = D / 2 := by
    dsimp only [f]
    rw [integral_gaussian_Ioi b]
    have harg : Real.pi / b = 8 * Real.pi * (l : ℝ) ^ 2 := by
      dsimp only [b]
      field_simp
    rw [harg]
    have hsqD : D ^ 2 = 8 * Real.pi * (l : ℝ) ^ 2 := by
      dsimp only [D]
      rw [mul_pow, mul_pow,
        Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
      ring
    have hsqrt : Real.sqrt (8 * Real.pi * (l : ℝ) ^ 2) = D := by
      apply (sq_eq_sq₀ (Real.sqrt_nonneg _) hD.le).mp
      rw [Real.sq_sqrt (by positivity), hsqD]
    rw [hsqrt]
  rw [hintEq] at htail
  have hsum : Summable (fun d : ℤ ↦ Real.exp (-b * (d : ℝ) ^ 2)) :=
    summable_exp_neg_mul_int_sq hb
  have heven : Function.Even (fun d : ℤ ↦
      Real.exp (-b * (d : ℝ) ^ 2)) := by
    intro d
    simp only [Int.cast_neg, neg_sq]
  have hraw : (∑' d : ℤ, Real.exp (-b * (d : ℝ) ^ 2)) ≤ 1 + D := by
    rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven hsum]
    have hp : (∑' n : ℕ+, Real.exp (-b * ((n : ℕ) : ℝ) ^ 2)) =
        ∑' n : ℕ, Real.exp (-b * ((n + 1 : ℕ) : ℝ) ^ 2) := by
      exact tsum_pnat_eq_tsum_succ
        (f := fun n : ℕ ↦ Real.exp (-b * (n : ℝ) ^ 2))
    simp only [Int.cast_natCast] at *
    rw [hp]
    have htail' : (∑' n : ℕ, Real.exp (-b * ((n + 1 : ℕ) : ℝ) ^ 2)) ≤
        D / 2 := by
      simpa only [f, Nat.cast_add, Nat.cast_one] using htail
    have hz : Real.exp (-b * ((0 : ℤ) : ℝ) ^ 2) = 1 := by norm_num
    rw [hz]
    rw [two_smul]
    calc
      1 + ((∑' n : ℕ, Real.exp (-b * ((n + 1 : ℕ) : ℝ) ^ 2)) +
          ∑' n : ℕ, Real.exp (-b * ((n + 1 : ℕ) : ℝ) ^ 2)) ≤
          1 + (D / 2 + D / 2) := add_le_add (le_refl 1) (add_le_add htail' htail')
      _ = 1 + D := by ring
  have hmass : gaussianStepTotalMass l ≤ 1 + 1 / D := by
    change (∑' d : ℤ, Real.exp (-((d : ℝ) ^ 2) /
      (8 * (l : ℝ) ^ 2)) / D) ≤ 1 + 1 / D
    have heq : (fun d : ℤ ↦ Real.exp (-((d : ℝ) ^ 2) /
        (8 * (l : ℝ) ^ 2)) / D) =
        fun d : ℤ ↦ Real.exp (-b * (d : ℝ) ^ 2) / D := by
      funext d
      congr 2
      dsimp only [b]
      ring
    rw [heq]
    rw [tsum_div_const]
    apply (div_le_iff₀ hD).2
    calc
      (∑' d : ℤ, Real.exp (-b * (d : ℝ) ^ 2)) ≤ 1 + D := hraw
      _ = (1 + 1 / D) * D := by
        field_simp [ne_of_gt hD]
        ring
  have hDlower : (l : ℝ) ≤ D := by
    dsimp only [D]
    have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_three])
    have hl0 : (0 : ℝ) ≤ l := by positivity
    nlinarith
  have hinv : 1 / D ≤ 1 / (l : ℝ) := by
    exact one_div_le_one_div_of_le (by positivity) hDlower
  calc
    gaussianStepTotalMass l ≤ 1 + 1 / D := hmass
    _ ≤ 1 + 1 / (l : ℝ) := by linarith
    _ ≤ Real.exp (1 / (l : ℝ)) := by
      simpa [add_comm] using Real.add_one_le_exp (1 / (l : ℝ))

/-! ## The upper half of shifted A.11 -/

/-- The two absolute-error estimates in `ProfileA11Tail` also give the
upper half of A.11.  This is stated separately because the lower-bound
development only needed the opposite direction. -/
theorem sum_edgeStirlingExponent_add_gaussian_le_from
    (start n : ℕ) (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (m : ℕ → ℕ) (Delta : ℕ → ℝ)
    {delta A B C : ℝ} (hdelta : 0 < delta)
    (hdeltaThird : delta ≤ 1 / 3) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C)
    (hpos : ∀ l ∈ Finset.Ico start n, 2 ≤ m l)
    (hwindow : ∀ l ∈ Finset.Ico start n,
      InEdgeTaylorWindow (m l) (m (l + 1)))
    (hbase : ∀ l ∈ Finset.Ico start n,
      (l : ℝ) ^ 2 ≤ (m l - 1 : ℕ))
    (hclose : ∀ l ∈ Finset.Ico start n,
      |2 * (l : ℝ) ^ 2 - (m l - 1 : ℕ)| ≤
        A * (l : ℝ) * (l : ℝ) ^ delta)
    (hmoderate : ∀ l ∈ Finset.Ico start n,
      A * (l : ℝ) * (l : ℝ) ^ delta ≤ (l : ℝ) ^ 2)
    (hinc : ∀ l ∈ Finset.Ico start n,
      |parabolicTransitionIncrement (m l) (m (l + 1))| ≤
        C * (l : ℝ) * (l : ℝ) ^ delta)
    (hparabolic : ∀ l, (m l : ℝ) = 2 * (l : ℝ) ^ 2 + Delta l)
    (hDelta : ∀ l ∈ Finset.Icc start n,
      |Delta l| ≤ B * (l : ℝ) * (l : ℝ) ^ delta)
    (hDeltaInc : ∀ l ∈ Finset.Ico start n,
      |Delta (l + 1) - Delta l| ≤
        C * (l : ℝ) * (l : ℝ) ^ delta) :
    (∑ l ∈ Finset.Ico start n,
        edgeStirlingExponent (m l) (m (l + 1))) +
        gaussianNormalizerLogSumFrom start n ≤
      -(2 * (n - start : ℕ) : ℝ) - gaussianEnergyFrom start n Delta +
        a11ErrorCoefficient delta A B C * (n : ℝ) ^ (3 * delta) := by
  have htaylor := abs_sum_edgeStirlingExponent_parabolic_le_from
    start n hstart hstartn m hdelta hdeltaThird hA hC hpos hwindow
    hbase hclose hmoderate hinc
  have henergy := abs_parabolicEnergyFrom_sub_reference_le
    start n hstart hstartn Delta hdelta hdeltaThird hB hC hDelta hDeltaInc
  have htaylorUpper := le_of_abs_le htaylor
  have henergyLower := neg_le_of_abs_le henergy
  have href := parabolicReferenceEnergyFrom_eq hstartn Delta
  have hparaEnergy :
      parabolicEnergyFrom start n Delta =
        ∑ l ∈ Finset.Ico start n,
          parabolicTransitionIncrement (m l) (m (l + 1)) ^ 2 /
            (8 * (l : ℝ) ^ 2) := by
    unfold parabolicEnergyFrom parabolicTransitionIncrement
    apply Finset.sum_congr rfl
    intro l hl
    rw [hparabolic (l + 1), hparabolic l]
  rw [hparaEnergy] at henergyLower
  rw [href] at henergyLower
  unfold gaussianNormalizerLogSumFrom
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at htaylorUpper
  have hcast : ((n - start : ℕ) : ℝ) = (n : ℝ) - start := by
    rw [Nat.cast_sub hstartn]
  have herr :
      a11ErrorCoefficient delta A B C * (n : ℝ) ^ (3 * delta) =
        parabolicTaylorCoefficient A C * (n : ℝ) ^ (3 * delta) /
            (3 * delta) +
          (3 + 4 * B + C / 2) * (n : ℝ) ^ (3 * delta) / delta := by
    unfold a11ErrorCoefficient
    ring
  rw [hcast, herr]
  linarith

/-! ## From the exact negative-binomial mass to the Stirling exponent -/

/-- Robbins' upper remainder and the penalty already inserted in the lower
kernel differ by at most two reciprocal base sizes. -/
lemma log_transitionMass_le_edgeStirlingExponent_add {a b : ℕ}
    (ha : 2 ≤ a) (hwindow : InEdgeTaylorWindow a b) :
    Real.log (transitionMass a b) ≤ edgeStirlingExponent a b +
      2 / (a - 1 : ℕ) := by
  have hb : 1 ≤ b := one_le_b_of_taylorWindow ha hwindow
  have hbn : b < a + b - 1 := by omega
  have hrem := (logBinomialRemainder_robbins_bounds (Nat.ne_of_gt hb) hbn).2
  have hremEq := transitionLogRemainder_eq_binomial
    (a := a) (Nat.zero_lt_of_lt ha) b
  have hpen := edgeRobbinsPenalty_le_inv ha hwindow
  have hbasePos : (0 : ℝ) < (a - 1 : ℕ) := edgeBase_pos ha
  have htotalNat : 0 < a + b - 1 := by omega
  have htotalBase : ((a - 1 : ℕ) : ℝ) ≤ (a + b - 1 : ℕ) := by
    exact_mod_cast (show a - 1 ≤ a + b - 1 by omega)
  have hrecip : (1 : ℝ) / (12 * (a + b - 1 : ℕ)) ≤
      1 / (a - 1 : ℕ) := by
    rw [div_le_div_iff₀ (by
        have : (0 : ℝ) < (a + b - 1 : ℕ) := by exact_mod_cast htotalNat
        positivity : (0 : ℝ) < 12 * (a + b - 1 : ℕ))
      hbasePos]
    nlinarith
  rw [transitionLogRemainder] at hremEq
  push_cast at hremEq
  have hremBase : logBinomialRemainder (a + b - 1) b ≤
      1 / (a - 1 : ℕ) := hrem.trans hrecip
  have hsum : logBinomialRemainder (a + b - 1) b +
      edgeRobbinsPenalty a b ≤ (2 : ℝ) / ((a - 1 : ℕ) : ℝ) := by
    calc
      logBinomialRemainder (a + b - 1) b + edgeRobbinsPenalty a b ≤
          (1 : ℝ) / ((a - 1 : ℕ) : ℝ) + 1 / ((a - 1 : ℕ) : ℝ) :=
        add_le_add hremBase hpen
      _ = (2 : ℝ) / ((a - 1 : ℕ) : ℝ) := by ring
  have heq : Real.log (transitionMass a b) =
      edgeStirlingExponent a b +
        (logBinomialRemainder (a + b - 1) b + edgeRobbinsPenalty a b) := by
    rw [edgeStirlingExponent]
    linarith only [hremEq]
  rw [heq]
  exact add_le_add (le_refl (edgeStirlingExponent a b)) hsum

lemma transitionMass_le_exp_edgeStirlingExponent_add {a b : ℕ}
    (ha : 2 ≤ a) (hwindow : InEdgeTaylorWindow a b) :
    transitionMass a b ≤ Real.exp
      (edgeStirlingExponent a b + 2 / (a - 1 : ℕ)) := by
  rw [← Real.exp_log (transitionMass_pos (Nat.zero_lt_of_lt ha) b)]
  exact Real.exp_le_exp.mpr
    (log_transitionMass_le_edgeStirlingExponent_add ha hwindow)

lemma transitionMass_le_one (a b : ℕ) : transitionMass a b ≤ 1 := by
  have h := (summable_transitionMass a).sum_le_tsum
    (s := {b}) (fun i _hi ↦ transitionMass_nonneg a i)
  simpa using h

/-- Exact transition product on a consecutive scale segment. -/
def transitionSegmentProduct (start : ℕ) : ℕ → (ℕ → ℕ) → ℝ
  | 0, _m => 1
  | steps + 1, m =>
      transitionMass (m start) (m (start + 1)) *
        transitionSegmentProduct (start + 1) steps m

lemma transitionSegmentProduct_nonneg (start steps : ℕ) (m : ℕ → ℕ) :
    0 ≤ transitionSegmentProduct start steps m := by
  induction steps generalizing start with
  | zero => simp [transitionSegmentProduct]
  | succ steps ih =>
      rw [transitionSegmentProduct]
      exact mul_nonneg (transitionMass_nonneg _ _) (ih (start + 1))

lemma transitionSegmentProduct_le_one (start steps : ℕ) (m : ℕ → ℕ) :
    transitionSegmentProduct start steps m ≤ 1 := by
  induction steps generalizing start with
  | zero => simp [transitionSegmentProduct]
  | succ steps ih =>
      rw [transitionSegmentProduct]
      nlinarith [transitionMass_nonneg (m start) (m (start + 1)),
        transitionMass_le_one (m start) (m (start + 1)),
        transitionSegmentProduct_nonneg (start + 1) steps m,
        ih (start + 1)]

lemma transitionSegmentProduct_append (start a b : ℕ) (m : ℕ → ℕ) :
    transitionSegmentProduct start (a + b) m =
      transitionSegmentProduct start a m *
        transitionSegmentProduct (start + a) b m := by
  induction a generalizing start with
  | zero => simp [transitionSegmentProduct]
  | succ a ih =>
      rw [Nat.succ_add, transitionSegmentProduct, transitionSegmentProduct, ih]
      rw [show start + (a + 1) = start + 1 + a by omega]
      ring

lemma transitionSegmentProduct_eq_prod_Ico (start steps : ℕ) (m : ℕ → ℕ) :
    transitionSegmentProduct start steps m =
      ∏ l ∈ Finset.Ico start (start + steps),
        transitionMass (m l) (m (l + 1)) := by
  induction steps generalizing start with
  | zero => simp [transitionSegmentProduct]
  | succ steps ih =>
      rw [transitionSegmentProduct, ih]
      have hsplit := Finset.prod_Ico_consecutive
        (fun l ↦ transitionMass (m l) (m (l + 1)))
        (show start ≤ start + 1 by omega)
        (show start + 1 ≤ start + (steps + 1) by omega)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsplit

lemma transitionSegmentProduct_le_exp_sum
    (start steps : ℕ) (m : ℕ → ℕ)
    (hpos : ∀ l ∈ Finset.Ico start (start + steps), 2 ≤ m l)
    (hwindow : ∀ l ∈ Finset.Ico start (start + steps),
      InEdgeTaylorWindow (m l) (m (l + 1))) :
    transitionSegmentProduct start steps m ≤
      Real.exp (∑ l ∈ Finset.Ico start (start + steps),
        (edgeStirlingExponent (m l) (m (l + 1)) +
          2 / (m l - 1 : ℕ))) := by
  rw [transitionSegmentProduct_eq_prod_Ico]
  calc
    (∏ l ∈ Finset.Ico start (start + steps),
        transitionMass (m l) (m (l + 1))) ≤
        ∏ l ∈ Finset.Ico start (start + steps),
          Real.exp (edgeStirlingExponent (m l) (m (l + 1)) +
            2 / (m l - 1 : ℕ)) := by
      apply Finset.prod_le_prod
      · intro l hl
        exact transitionMass_nonneg _ _
      · intro l hl
        exact transitionMass_le_exp_edgeStirlingExponent_add
          (hpos l hl) (hwindow l hl)
    _ = _ := by rw [Real.exp_sum]

lemma sum_two_div_profileBase_le_four
    (start n : ℕ) (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (m : ℕ → ℕ)
    (hbase : ∀ l ∈ Finset.Ico start n,
      (l : ℝ) ^ 2 ≤ (m l - 1 : ℕ)) :
    (∑ l ∈ Finset.Ico start n, (2 : ℝ) / (m l - 1 : ℕ)) ≤ 4 := by
  have hpoint : ∀ l ∈ Finset.Ico start n,
      (2 : ℝ) / (m l - 1 : ℕ) ≤ 2 * ((l : ℝ) ^ 2)⁻¹ := by
    intro l hl
    have hlpos : (0 : ℝ) < (l : ℝ) ^ 2 := by
      have hlNat : 0 < l := by
        have := (Finset.mem_Ico.mp hl).1
        omega
      have : (0 : ℝ) < l := by exact_mod_cast hlNat
      positivity
    have hmbase : (0 : ℝ) < (m l - 1 : ℕ) :=
      lt_of_lt_of_le hlpos (hbase l hl)
    rw [div_eq_mul_inv]
    gcongr
    exact hbase l hl
  have hsubset : Finset.Ico start n ⊆ Finset.Ioo 0 n := by
    intro l hl
    rw [Finset.mem_Ico] at hl
    rw [Finset.mem_Ioo]
    omega
  have hsquares :
      (∑ l ∈ Finset.Ico start n, ((l : ℝ) ^ 2)⁻¹) ≤ 2 := by
    calc
      _ ≤ ∑ l ∈ Finset.Ioo 0 n, ((l : ℝ) ^ 2)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro l _hl _hnot
        positivity
      _ ≤ 2 := by
        simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 n)
  calc
    (∑ l ∈ Finset.Ico start n, (2 : ℝ) / (m l - 1 : ℕ)) ≤
        ∑ l ∈ Finset.Ico start n, 2 * ((l : ℝ) ^ 2)⁻¹ :=
      Finset.sum_le_sum fun l hl ↦ hpoint l hl
    _ = 2 * ∑ l ∈ Finset.Ico start n, ((l : ℝ) ^ 2)⁻¹ := by
      rw [Finset.mul_sum]
    _ ≤ 4 := by nlinarith

/-- Exact transition weights on a certified parabolic tail are bounded by
the corresponding lattice-Gaussian path weight.  The constant `4` is the
entire accumulated Robbins upper-remainder cost. -/
theorem transitionSegmentProduct_le_a11_gaussian_from
    (start n : ℕ) (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (m : ℕ → ℕ) (D : ℕ → ℤ)
    {delta A B C : ℝ} (hdelta : 0 < delta)
    (hdeltaThird : delta ≤ 1 / 3) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C)
    (hpos : ∀ l ∈ Finset.Ico start n, 2 ≤ m l)
    (hwindow : ∀ l ∈ Finset.Ico start n,
      InEdgeTaylorWindow (m l) (m (l + 1)))
    (hbase : ∀ l ∈ Finset.Ico start n,
      (l : ℝ) ^ 2 ≤ (m l - 1 : ℕ))
    (hclose : ∀ l ∈ Finset.Ico start n,
      |2 * (l : ℝ) ^ 2 - (m l - 1 : ℕ)| ≤
        A * (l : ℝ) * (l : ℝ) ^ delta)
    (hmoderate : ∀ l ∈ Finset.Ico start n,
      A * (l : ℝ) * (l : ℝ) ^ delta ≤ (l : ℝ) ^ 2)
    (hinc : ∀ l ∈ Finset.Ico start n,
      |parabolicTransitionIncrement (m l) (m (l + 1))| ≤
        C * (l : ℝ) * (l : ℝ) ^ delta)
    (hparabolic : ∀ l, (m l : ℝ) = 2 * (l : ℝ) ^ 2 + (D l : ℝ))
    (hDelta : ∀ l ∈ Finset.Icc start n,
      |(D l : ℝ)| ≤ B * (l : ℝ) * (l : ℝ) ^ delta)
    (hDeltaInc : ∀ l ∈ Finset.Ico start n,
      |(D (l + 1) : ℝ) - (D l : ℝ)| ≤
        C * (l : ℝ) * (l : ℝ) ^ delta) :
    transitionSegmentProduct start (n - start) m ≤
      Real.exp (-(2 * (n - start : ℕ) : ℝ) +
        a11ErrorCoefficient delta A B C * (n : ℝ) ^ (3 * delta) + 4) *
        gaussianSegmentProduct start (n - start) D := by
  have htop : start + (n - start) = n := Nat.add_sub_of_le hstartn
  have hseg := transitionSegmentProduct_le_exp_sum start (n - start) m
    (by simpa only [htop] using hpos)
    (by simpa only [htop] using hwindow)
  rw [Finset.sum_add_distrib] at hseg
  have ha11 := sum_edgeStirlingExponent_add_gaussian_le_from
    start n hstart hstartn m (fun l ↦ (D l : ℝ)) hdelta hdeltaThird
    hA hB hC hpos hwindow hbase hclose hmoderate hinc hparabolic
    hDelta hDeltaInc
  have hcorr := sum_two_div_profileBase_le_four start n hstart hstartn m hbase
  have hexponent :
      (∑ l ∈ Finset.Ico start n,
          edgeStirlingExponent (m l) (m (l + 1))) +
        ∑ l ∈ Finset.Ico start n, (2 : ℝ) / (m l - 1 : ℕ) ≤
      (-(2 * (n - start : ℕ) : ℝ) +
          a11ErrorCoefficient delta A B C * (n : ℝ) ^ (3 * delta) + 4) +
        (-gaussianEnergyFrom start n (fun l ↦ (D l : ℝ)) -
          gaussianNormalizerLogSumFrom start n) := by
    linarith
  have hexp := Real.exp_le_exp.mpr hexponent
  have hgaussian := gaussianSegmentProduct_eq_exp_from
    (show 1 ≤ start by omega) hstartn D
  rw [htop] at hseg
  calc
    transitionSegmentProduct start (n - start) m ≤
        Real.exp ((∑ l ∈ Finset.Ico start n,
          edgeStirlingExponent (m l) (m (l + 1))) +
          ∑ l ∈ Finset.Ico start n, (2 : ℝ) / (m l - 1 : ℕ)) := hseg
    _ ≤ Real.exp
        ((-(2 * (n - start : ℕ) : ℝ) +
            a11ErrorCoefficient delta A B C * (n : ℝ) ^ (3 * delta) + 4) +
          (-gaussianEnergyFrom start n (fun l ↦ (D l : ℝ)) -
            gaussianNormalizerLogSumFrom start n)) := hexp
    _ = Real.exp (-(2 * (n - start : ℕ) : ℝ) +
          a11ErrorCoefficient delta A B C * (n : ℝ) ^ (3 * delta) + 4) *
        gaussianSegmentProduct start (n - start) D := by
      rw [Real.exp_add, hgaussian]

/-! ## A uniform certificate for every constrained `delta = 1/5` profile -/

/-- Fixed point beyond which the elementary Taylor-window inequalities are
uniform for every profile in the full HLOZ tube. -/
def profileUpperTailStart : ℕ := 32 ^ 5

/-- The HLOZ profile-window exponent, kept local so this analytic module does
not depend on the later Proposition-1.3 assembly. -/
def profileUpperDelta : ℝ := 1 / 5

lemma thirtyTwo_le_rpow_four_fifths {l : ℕ}
    (hl : profileUpperTailStart ≤ l) :
    (32 : ℝ) ≤ (l : ℝ) ^ (4 / 5 : ℝ) := by
  have hlReal : ((32 : ℝ) ^ 5) ≤ (l : ℝ) := by
    exact_mod_cast hl
  have hroot := Real.rpow_le_rpow (by positivity) hlReal
    (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have heq : (((32 : ℝ) ^ 5) : ℝ) ^ (1 / 5 : ℝ) = 32 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 32)]
    norm_num
  rw [profileUpperTailStart] at hl
  rw [heq] at hroot
  exact hroot.trans (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ l by omega) : (1 : ℝ) ≤ l)
    (by norm_num : (1 / 5 : ℝ) ≤ 4 / 5))

lemma rpow_six_fifths_eq {l : ℕ} (hl : 1 ≤ l) :
    (l : ℝ) ^ (1 + (1 / 5 : ℝ)) =
      (l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ) := by
  rw [Real.rpow_add (by positivity), Real.rpow_one]

lemma thirtyTwo_mul_rpow_six_fifths_le_sq {l : ℕ}
    (hl : profileUpperTailStart ≤ l) :
    32 * (l : ℝ) ^ (1 + (1 / 5 : ℝ)) ≤ (l : ℝ) ^ 2 := by
  have hlOne : 1 ≤ l := by
    rw [profileUpperTailStart] at hl
    omega
  have h32 := thirtyTwo_le_rpow_four_fifths hl
  have hnonneg : 0 ≤ (l : ℝ) ^ (1 + (1 / 5 : ℝ)) := by positivity
  calc
    32 * (l : ℝ) ^ (1 + (1 / 5 : ℝ)) ≤
        (l : ℝ) ^ (4 / 5 : ℝ) *
          (l : ℝ) ^ (1 + (1 / 5 : ℝ)) :=
      mul_le_mul_of_nonneg_right h32 hnonneg
    _ = (l : ℝ) ^ 2 := by
      rw [← Real.rpow_add (by positivity)]
      norm_num [Real.rpow_two]

lemma one_le_rpow_six_fifths {l : ℕ} (hl : 1 ≤ l) :
    (1 : ℝ) ≤ (l : ℝ) ^ (1 + (1 / 5 : ℝ)) :=
  Real.one_le_rpow (by exact_mod_cast hl) (by norm_num)

lemma succ_rpow_six_fifths_le_four_mul {l : ℕ} (hl : 1 ≤ l) :
    ((l + 1 : ℕ) : ℝ) ^ (1 + (1 / 5 : ℝ)) ≤
      4 * (l : ℝ) ^ (1 + (1 / 5 : ℝ)) := by
  have hbase : (((l + 1 : ℕ) : ℝ)) ≤ 2 * (l : ℝ) := by
    push_cast
    exact_mod_cast (show l + 1 ≤ 2 * l by omega)
  have hp := Real.rpow_le_rpow (by positivity) hbase
    (by norm_num : (0 : ℝ) ≤ 1 + (1 / 5 : ℝ))
  have htwo : (2 : ℝ) ^ (1 + (1 / 5 : ℝ)) ≤ 4 := by
    calc
      (2 : ℝ) ^ (1 + (1 / 5 : ℝ)) ≤ (2 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := by norm_num [Real.rpow_two]
  calc
    ((l + 1 : ℕ) : ℝ) ^ (1 + (1 / 5 : ℝ)) ≤
        (2 * (l : ℝ)) ^ (1 + (1 / 5 : ℝ)) := hp
    _ = (2 : ℝ) ^ (1 + (1 / 5 : ℝ)) *
        (l : ℝ) ^ (1 + (1 / 5 : ℝ)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity)]
    _ ≤ 4 * (l : ℝ) ^ (1 + (1 / 5 : ℝ)) := by gcongr

lemma constrained_profileAtScale_window {n : ℕ} {m : Profile n}
    (hm : IsConstrainedProfile profileUpperDelta m)
    {l : ℕ} (hlower : 2 ≤ l) (hupper : l ≤ n) :
    InProfileWindow profileUpperDelta l (profileAtScale m l) := by
  unfold profileAtScale
  rw [dif_pos ⟨hlower, hupper⟩]
  let i : Fin (n - 1) := ⟨l - 2, by omega⟩
  change InProfileWindow profileUpperDelta l (m i)
  have hscale : scaleIndex i = l := by
    unfold scaleIndex
    dsimp only [i]
    omega
  rw [← hscale]
  exact hm i

lemma profileAtScale_real_eq_center_add_deviation {n : ℕ}
    (m : Profile n) (l : ℕ) :
    (profileAtScale m l : ℝ) =
      2 * (l : ℝ) ^ 2 + (profileIntegerDeviation m l : ℝ) := by
  unfold profileIntegerDeviation profileCenter
  push_cast
  ring

lemma constrained_profileDeviation_abs_le {n : ℕ} {m : Profile n}
    (hm : IsConstrainedProfile profileUpperDelta m)
    {l : ℕ} (hlower : 2 ≤ l) (hupper : l ≤ n) :
    |(profileIntegerDeviation m l : ℝ)| ≤
      (l : ℝ) ^ (1 + profileUpperDelta) := by
  have hw := constrained_profileAtScale_window hm hlower hupper
  rw [InProfileWindow] at hw
  dsimp only [profileCenter] at hw
  push_cast at hw
  unfold profileIntegerDeviation profileCenter
  push_cast
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hw

/-- All deterministic inputs needed by the upper A.11 comparison, packaged
for a member of the full constrained profile set. -/
structure ConstrainedProfileUpperCertificate {n : ℕ} (m : Profile n) : Prop where
  entry_two_le : ∀ l ∈ Finset.Ico profileUpperTailStart n,
    2 ≤ profileAtScale m l
  taylorWindow : ∀ l ∈ Finset.Ico profileUpperTailStart n,
    InEdgeTaylorWindow (profileAtScale m l) (profileAtScale m (l + 1))
  base : ∀ l ∈ Finset.Ico profileUpperTailStart n,
    (l : ℝ) ^ 2 ≤ (profileAtScale m l - 1 : ℕ)
  close : ∀ l ∈ Finset.Ico profileUpperTailStart n,
    |2 * (l : ℝ) ^ 2 - (profileAtScale m l - 1 : ℕ)| ≤
      2 * (l : ℝ) * (l : ℝ) ^ profileUpperDelta
  moderate : ∀ l ∈ Finset.Ico profileUpperTailStart n,
    2 * (l : ℝ) * (l : ℝ) ^ profileUpperDelta ≤ (l : ℝ) ^ 2
  increment : ∀ l ∈ Finset.Ico profileUpperTailStart n,
    |parabolicTransitionIncrement (profileAtScale m l)
      (profileAtScale m (l + 1))| ≤
      11 * (l : ℝ) * (l : ℝ) ^ profileUpperDelta
  deviation : ∀ l ∈ Finset.Icc profileUpperTailStart n,
    |(profileIntegerDeviation m l : ℝ)| ≤
      (l : ℝ) * (l : ℝ) ^ profileUpperDelta
  deviationIncrement : ∀ l ∈ Finset.Ico profileUpperTailStart n,
    |(profileIntegerDeviation m (l + 1) : ℝ) -
      (profileIntegerDeviation m l : ℝ)| ≤
      11 * (l : ℝ) * (l : ℝ) ^ profileUpperDelta

/-- Every member of the exact HLOZ tube has a uniform tail Taylor
certificate.  No pathwise estimate is assumed. -/
theorem constrainedProfileUpperCertificate {n : ℕ}
    (hn : profileUpperTailStart ≤ n) {m : Profile n}
    (hm : IsConstrainedProfile profileUpperDelta m) :
    ConstrainedProfileUpperCertificate m := by
  have hstartTwo : 2 ≤ profileUpperTailStart := by
    norm_num [profileUpperTailStart]
  have hdev : ∀ l ∈ Finset.Icc profileUpperTailStart n,
      |(profileIntegerDeviation m l : ℝ)| ≤
        (l : ℝ) * (l : ℝ) ^ profileUpperDelta := by
    intro l hl
    have hl' := Finset.mem_Icc.mp hl
    have h := constrained_profileDeviation_abs_le hm
      (hstartTwo.trans hl'.1) hl'.2
    simpa only [profileUpperDelta,
      rpow_six_fifths_eq (show 1 ≤ l by omega)] using h
  have hentry : ∀ l ∈ Finset.Ico profileUpperTailStart n,
      2 ≤ profileAtScale m l := by
    intro l hl
    have hl' := Finset.mem_Ico.mp hl
    exact two_le_of_inProfileWindow (by norm_num [profileUpperDelta])
      (hstartTwo.trans hl'.1)
      (constrained_profileAtScale_window hm (hstartTwo.trans hl'.1) hl'.2.le)
  have hbase : ∀ l ∈ Finset.Ico profileUpperTailStart n,
      (l : ℝ) ^ 2 ≤ (profileAtScale m l - 1 : ℕ) := by
    intro l hl
    have hl' := Finset.mem_Ico.mp hl
    have hd := hdev l (Finset.mem_Icc.mpr ⟨hl'.1, hl'.2.le⟩)
    have hstrong := thirtyTwo_mul_rpow_six_fifths_le_sq hl'.1
    have hpOne := one_le_rpow_six_fifths (show 1 ≤ l by omega)
    have hreal := profileAtScale_real_eq_center_add_deviation m l
    rw [Nat.cast_sub (by have := hentry l hl; omega)]
    push_cast
    rw [hreal]
    simp only [profileUpperDelta] at hd ⊢
    rw [rpow_six_fifths_eq (show 1 ≤ l by omega)] at hstrong hpOne
    have hdLow := neg_le_of_abs_le hd
    have hpadd : (l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ) + 1 ≤
        (l : ℝ) ^ 2 := by
      calc
        _ ≤ 2 * ((l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ)) := by linarith
        _ ≤ 32 * ((l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ)) := by
          have hp : 0 ≤ (l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ) := by positivity
          nlinarith
        _ ≤ _ := hstrong
    linarith
  have hclose : ∀ l ∈ Finset.Ico profileUpperTailStart n,
      |2 * (l : ℝ) ^ 2 - (profileAtScale m l - 1 : ℕ)| ≤
        2 * (l : ℝ) * (l : ℝ) ^ profileUpperDelta := by
    intro l hl
    have hl' := Finset.mem_Ico.mp hl
    have hd := hdev l (Finset.mem_Icc.mpr ⟨hl'.1, hl'.2.le⟩)
    have hpOne := one_le_rpow_six_fifths (show 1 ≤ l by omega)
    have hreal := profileAtScale_real_eq_center_add_deviation m l
    rw [Nat.cast_sub (by have := hentry l hl; omega)]
    push_cast
    rw [hreal]
    simp only [profileUpperDelta] at hd ⊢
    rw [rpow_six_fifths_eq (show 1 ≤ l by omega)] at hpOne
    calc
      |2 * (l : ℝ) ^ 2 -
          (2 * (l : ℝ) ^ 2 + (profileIntegerDeviation m l : ℝ) - 1)| =
          |1 - (profileIntegerDeviation m l : ℝ)| := by congr 1 <;> ring
      _ ≤ 1 + |(profileIntegerDeviation m l : ℝ)| := by
        simpa only [abs_one] using abs_sub 1 (profileIntegerDeviation m l : ℝ)
      _ ≤ 2 * ((l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ)) := by linarith
      _ = 2 * (l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ) := by ring
  have hmoderate : ∀ l ∈ Finset.Ico profileUpperTailStart n,
      2 * (l : ℝ) * (l : ℝ) ^ profileUpperDelta ≤ (l : ℝ) ^ 2 := by
    intro l hl
    have hs := thirtyTwo_mul_rpow_six_fifths_le_sq
      (Finset.mem_Ico.mp hl).1
    simp only [profileUpperDelta]
    calc
      2 * (l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ) =
          2 * (l : ℝ) ^ (1 + (1 / 5 : ℝ)) := by
        rw [rpow_six_fifths_eq (show 1 ≤ l by
          have := (Finset.mem_Ico.mp hl).1
          norm_num [profileUpperTailStart] at this ⊢
          omega)]
        ring
      _ ≤
          32 * (l : ℝ) ^ (1 + (1 / 5 : ℝ)) := by
        have hp : 0 ≤ (l : ℝ) ^ (1 + (1 / 5 : ℝ)) := by positivity
        nlinarith
      _ ≤ _ := hs
  have hdevInc : ∀ l ∈ Finset.Ico profileUpperTailStart n,
      |(profileIntegerDeviation m (l + 1) : ℝ) -
        (profileIntegerDeviation m l : ℝ)| ≤
        5 * (l : ℝ) * (l : ℝ) ^ profileUpperDelta := by
    intro l hl
    have hl' := Finset.mem_Ico.mp hl
    have hd0 := hdev l (Finset.mem_Icc.mpr ⟨hl'.1, hl'.2.le⟩)
    have hd1raw := constrained_profileDeviation_abs_le hm
      (by omega) hl'.2
    have hd1 : |(profileIntegerDeviation m (l + 1) : ℝ)| ≤
        4 * ((l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ)) := by
      have hs := succ_rpow_six_fifths_le_four_mul (show 1 ≤ l by omega)
      have h := hd1raw.trans (by simpa only [profileUpperDelta] using hs)
      simpa only [profileUpperDelta,
        rpow_six_fifths_eq (show 1 ≤ l by omega)] using h
    simp only [profileUpperDelta] at hd0 ⊢
    calc
      _ ≤ |(profileIntegerDeviation m (l + 1) : ℝ)| +
          |(profileIntegerDeviation m l : ℝ)| := abs_sub _ _
      _ ≤ 4 * ((l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ)) +
          (l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ) := add_le_add hd1 hd0
      _ ≤ 5 * (l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ) := by
        ring_nf
        exact le_rfl
  have hinc : ∀ l ∈ Finset.Ico profileUpperTailStart n,
      |parabolicTransitionIncrement (profileAtScale m l)
        (profileAtScale m (l + 1))| ≤
        11 * (l : ℝ) * (l : ℝ) ^ profileUpperDelta := by
    intro l hl
    have hl' := Finset.mem_Ico.mp hl
    have hdi := hdevInc l hl
    have hm0 := profileAtScale_real_eq_center_add_deviation m l
    have hm1 := profileAtScale_real_eq_center_add_deviation m (l + 1)
    have hpOne := one_le_rpow_six_fifths (show 1 ≤ l by omega)
    unfold parabolicTransitionIncrement
    rw [hm0, hm1]
    push_cast
    simp only [profileUpperDelta] at hdi ⊢
    rw [rpow_six_fifths_eq (show 1 ≤ l by omega)] at hpOne
    have hlP : (l : ℝ) ≤ (l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ) := by
      have hpow : (1 : ℝ) ≤ (l : ℝ) ^ (1 / 5 : ℝ) :=
        Real.one_le_rpow (by exact_mod_cast (show 1 ≤ l by omega)) (by norm_num)
      nlinarith
    calc
      |(2 * ((l : ℝ) + 1) ^ 2 +
          (profileIntegerDeviation m (l + 1) : ℝ)) -
        (2 * (l : ℝ) ^ 2 + (profileIntegerDeviation m l : ℝ))| =
          |(4 * (l : ℝ) + 2) +
            ((profileIntegerDeviation m (l + 1) : ℝ) -
              (profileIntegerDeviation m l : ℝ))| := by congr 1 <;> ring
      _ ≤ |4 * (l : ℝ) + 2| +
          |(profileIntegerDeviation m (l + 1) : ℝ) -
            (profileIntegerDeviation m l : ℝ)| := abs_add_le _ _
      _ = (4 * (l : ℝ) + 2) +
          |(profileIntegerDeviation m (l + 1) : ℝ) -
            (profileIntegerDeviation m l : ℝ)| := by
        rw [abs_of_nonneg]
        positivity
      _ ≤ (4 * (l : ℝ) + 2) +
          5 * (l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ) :=
        add_le_add (le_refl _) hdi
      _ ≤ 11 * (l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ) := by
        nlinarith [hpOne, hlP]
  have hwindow : ∀ l ∈ Finset.Ico profileUpperTailStart n,
      InEdgeTaylorWindow (profileAtScale m l) (profileAtScale m (l + 1)) := by
    intro l hl
    have hl' := Finset.mem_Ico.mp hl
    have hlOne : 1 ≤ l := by
      exact (show 1 ≤ profileUpperTailStart by norm_num [profileUpperTailStart]).trans hl'.1
    have hi := hinc l hl
    have hb := hbase l hl
    have hstrong := thirtyTwo_mul_rpow_six_fifths_le_sq
      (Finset.mem_Ico.mp hl).1
    have hpOne := one_le_rpow_six_fifths hlOne
    unfold InEdgeTaylorWindow edgeDeviation
    rw [Nat.cast_sub (by have := hentry l hl; omega)]
    push_cast
    unfold parabolicTransitionIncrement at hi
    simp only [profileUpperDelta] at hi ⊢
    rw [rpow_six_fifths_eq hlOne] at hstrong hpOne
    have hi' : |(profileAtScale m (l + 1) : ℝ) - profileAtScale m l| ≤
        11 * ((l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ)) := by
      simpa [mul_assoc] using hi
    have hedge : |(profileAtScale m (l + 1) : ℝ) -
        ((profileAtScale m l : ℝ) - 1)| ≤
        12 * ((l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ)) := by
      calc
        _ = |((profileAtScale m (l + 1) : ℝ) - profileAtScale m l) + 1| := by
          congr 1 <;> ring
        _ ≤ |(profileAtScale m (l + 1) : ℝ) - profileAtScale m l| + 1 := by
          simpa only [abs_one] using
            abs_add_le ((profileAtScale m (l + 1) : ℝ) - profileAtScale m l) 1
        _ ≤ 11 * ((l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ)) + 1 :=
          add_le_add hi' (le_refl 1)
        _ ≤ 12 * ((l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ)) := by linarith
    have hb' : (l : ℝ) ^ 2 ≤ (profileAtScale m l : ℝ) - 1 := by
      have hml := hentry l hl
      rw [Nat.cast_sub (by omega)] at hb
      norm_num at hb ⊢
      exact hb
    have hhalf : 12 * ((l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ)) ≤
        ((profileAtScale m l : ℝ) - 1) / 2 := by
      have hbaseHalf : (l : ℝ) ^ 2 / 2 ≤
          ((profileAtScale m l : ℝ) - 1) / 2 := by linarith
      have : 12 * ((l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ)) ≤
          (l : ℝ) ^ 2 / 2 := by linarith
      exact this.trans hbaseHalf
    exact hedge.trans hhalf
  refine {
    entry_two_le := hentry
    taylorWindow := hwindow
    base := hbase
    close := hclose
    moderate := hmoderate
    increment := hinc
    deviation := hdev
    deviationIncrement := by
      intro l hl
      have h := hdevInc l hl
      have hp : 0 ≤ (l : ℝ) * (l : ℝ) ^ profileUpperDelta := by positivity
      nlinarith }

/-! ## Finite lattice-Gaussian partition upper bound -/

/-- Gaussian weight of `steps` future profile values, conditional on the
current centered integer deviation `x`. -/
def gaussianFutureTupleWeight (l : ℕ) (x : ℤ) :
    {steps : ℕ} → (Fin steps → ℕ) → ℝ
  | 0, _p => 1
  | steps + 1, p =>
      gaussianStepWeight l
          (((p 0 : ℕ) : ℤ) - profileCenter (l + 1) - x) *
        gaussianFutureTupleWeight (l + 1)
          (((p 0 : ℕ) : ℤ) - profileCenter (l + 1)) (Fin.tail p)

lemma gaussianFutureTupleWeight_nonneg (l : ℕ) (x : ℤ)
    {steps : ℕ} (p : Fin steps → ℕ) :
    0 ≤ gaussianFutureTupleWeight l x p := by
  induction steps generalizing l x with
  | zero => simp [gaussianFutureTupleWeight]
  | succ steps ih =>
      rw [gaussianFutureTupleWeight]
      exact mul_nonneg (gaussianStepWeight_nonneg _ _)
        (ih (l + 1) _ (Fin.tail p))

lemma sum_gaussianStepWeight_image_le_total (l : ℕ) (hl : 0 < l)
    (s : Finset ℕ) (c x : ℤ) :
    (∑ y ∈ s, gaussianStepWeight l ((y : ℤ) - c - x)) ≤
      gaussianStepTotalMass l := by
  let e : ℕ → ℤ := fun y ↦ (y : ℤ) - c - x
  have he : Function.Injective e := by
    intro a b hab
    dsimp only [e] at hab
    exact_mod_cast (show (a : ℤ) = b by omega)
  have hsum := (summable_gaussianStepWeight hl).sum_le_tsum
    (s := s.image e) (fun d _hd ↦ gaussianStepWeight_nonneg l d)
  rw [Finset.sum_image he.injOn] at hsum
  exact hsum

/-- Summing over any finite restrictions on the future values is bounded by
the product of the unrestricted one-step Gaussian masses. -/
theorem sum_gaussianFutureTupleWeight_le
    (steps l : ℕ) (hl : 0 < l) (x : ℤ) (S : ℕ → Finset ℕ) :
    (∑ p ∈ Fintype.piFinset
        (fun i : Fin steps ↦ S (l + 1 + i.1)),
        gaussianFutureTupleWeight l x p) ≤
      Real.exp (∑ j ∈ Finset.Ico l (l + steps), 1 / (j : ℝ)) := by
  induction steps generalizing l x with
  | zero => simp [gaussianFutureTupleWeight]
  | succ steps ih =>
      let T : Fin (steps + 1) → Finset ℕ :=
        fun i ↦ S (l + 1 + i.1)
      have hdecomp : Fintype.piFinset T =
          (T 0 ×ˢ Fintype.piFinset (Fin.tail T)).map
            (Fin.consEquiv (fun _ : Fin (steps + 1) ↦ ℕ)).toEmbedding := by
        have h := Finset.filter_piFinset_eq_map_consEquiv T
          (fun _ : Fin steps → ℕ ↦ True)
        simpa only [Finset.filter_true] using h
      have htailSets : Fin.tail T =
          fun i : Fin steps ↦ S (l + 2 + i.1) := by
        funext i
        change S (l + 1 + (i.1 + 1)) = S (l + 2 + i.1)
        congr 1
        omega
      change (∑ p ∈ Fintype.piFinset T,
        gaussianFutureTupleWeight l x p) ≤ _
      rw [hdecomp, Finset.sum_map]
      simp only [Finset.sum_product, Fin.consEquiv_apply, Fin.cons_zero,
        Fin.tail_cons, gaussianFutureTupleWeight]
      have hinner : ∀ y ∈ T 0,
          (∑ q ∈ Fintype.piFinset (Fin.tail T),
            gaussianStepWeight l ((y : ℤ) - profileCenter (l + 1) - x) *
              gaussianFutureTupleWeight (l + 1)
                ((y : ℤ) - profileCenter (l + 1)) q) ≤
          gaussianStepWeight l ((y : ℤ) - profileCenter (l + 1) - x) *
            Real.exp (∑ j ∈ Finset.Ico (l + 1) (l + 1 + steps),
              1 / (j : ℝ)) := by
        intro y hy
        rw [← Finset.mul_sum]
        apply mul_le_mul_of_nonneg_left
        · rw [htailSets]
          exact ih (l + 1) (Nat.succ_pos l)
            ((y : ℤ) - profileCenter (l + 1))
        · exact gaussianStepWeight_nonneg _ _
      calc
        (∑ y ∈ T 0, ∑ q ∈ Fintype.piFinset (Fin.tail T),
            gaussianStepWeight l ((y : ℤ) - profileCenter (l + 1) - x) *
              gaussianFutureTupleWeight (l + 1)
                ((y : ℤ) - profileCenter (l + 1)) q) ≤
            ∑ y ∈ T 0,
              gaussianStepWeight l ((y : ℤ) - profileCenter (l + 1) - x) *
                Real.exp (∑ j ∈ Finset.Ico (l + 1) (l + 1 + steps),
                  1 / (j : ℝ)) := Finset.sum_le_sum fun y hy ↦ hinner y hy
        _ = (∑ y ∈ T 0,
              gaussianStepWeight l ((y : ℤ) - profileCenter (l + 1) - x)) *
            Real.exp (∑ j ∈ Finset.Ico (l + 1) (l + 1 + steps),
              1 / (j : ℝ)) := by rw [Finset.sum_mul]
        _ ≤ Real.exp (1 / (l : ℝ)) *
            Real.exp (∑ j ∈ Finset.Ico (l + 1) (l + 1 + steps),
              1 / (j : ℝ)) := by
          gcongr
          exact (sum_gaussianStepWeight_image_le_total l hl (T 0)
            (profileCenter (l + 1)) x).trans (gaussianStepTotalMass_le_exp_inv hl)
        _ = Real.exp (∑ j ∈ Finset.Ico l (l + (steps + 1)),
              1 / (j : ℝ)) := by
          rw [← Real.exp_add]
          congr 1
          have hsplit := Finset.sum_Ico_consecutive
            (fun j : ℕ ↦ 1 / (j : ℝ))
            (show l ≤ l + 1 by omega)
            (show l + 1 ≤ l + (steps + 1) by omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsplit

lemma transitionProduct_ofFn_eq_segment (f : ℕ → ℕ)
    (start len : ℕ) :
    transitionProduct (List.ofFn fun i : Fin len ↦ f (start + i.1)) =
      transitionSegmentProduct start (len - 1) f := by
  induction len generalizing start with
  | zero => simp [transitionSegmentProduct]
  | succ len ih =>
      cases len with
      | zero => simp [transitionSegmentProduct]
      | succ k =>
          rw [List.ofFn_succ]
          simp only [Fin.val_zero, Fin.val_succ, Nat.add_zero]
          rw [show (List.ofFn fun i : Fin (k + 1) ↦
                f (start + (i.1 + 1))) =
              List.ofFn fun i : Fin (k + 1) ↦ f (start + 1 + i.1) by
            congr 1
            funext i
            congr 1
            omega]
          rw [List.ofFn_succ, transitionProduct_cons_cons]
          simp only [Fin.val_zero, Fin.val_succ, Nat.add_zero]
          rw [show (f (start + 1) :: List.ofFn
                (fun i : Fin k ↦ f (start + 1 + (i.1 + 1)))) =
              List.ofFn
                (fun i : Fin (k + 1) ↦ f (start + 1 + i.1)) by
            symm
            rw [List.ofFn_succ]
            simp only [Fin.val_zero, Fin.val_succ, Nat.add_zero]]
          rw [ih]
          rfl

lemma profileWeight_eq_transitionSegmentProduct {n : ℕ} (hn : 2 ≤ n)
    (m : Profile n) :
    profileWeight m = transitionSegmentProduct 2 (n - 2) (profileAtScale m) := by
  unfold profileWeight profileList
  have h := transitionProduct_ofFn_eq_segment (profileAtScale m) 2 (n - 1)
  have hlist : (List.ofFn m) =
      List.ofFn (fun i : Fin (n - 1) ↦ profileAtScale m (2 + i.1)) := by
    congr 1
    funext i
    rw [show 2 + i.1 = scaleIndex i by simp [scaleIndex, Nat.add_comm]]
    exact (profileAtScale_scaleIndex m i).symm
  rw [hlist, h]
  congr 1

/-- Discarding the initial segment can only increase the profile weight. -/
lemma profileWeight_le_transitionSegmentProduct_from {n start : ℕ}
    (hn : 2 ≤ n) (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (m : Profile n) :
    profileWeight m ≤
      transitionSegmentProduct start (n - start) (profileAtScale m) := by
  rw [profileWeight_eq_transitionSegmentProduct hn]
  have hsteps : n - 2 = (start - 2) + (n - start) := by omega
  rw [hsteps, transitionSegmentProduct_append]
  rw [show 2 + (start - 2) = start by omega]
  have hpref := transitionSegmentProduct_le_one 2 (start - 2) (profileAtScale m)
  have htail := transitionSegmentProduct_nonneg start (n - start) (profileAtScale m)
  nlinarith

/-- Pointwise exact-weight upper bound for every constrained profile. -/
theorem constrained_profileWeight_le_tailGaussian {n : ℕ}
    (hn : profileUpperTailStart ≤ n) {m : Profile n}
    (hm : IsConstrainedProfile profileUpperDelta m) :
    profileWeight m ≤
      Real.exp (-(2 * (n - profileUpperTailStart : ℕ) : ℝ) +
        a11ErrorCoefficient profileUpperDelta 2 1 11 *
          (n : ℝ) ^ (3 * profileUpperDelta) + 4) *
        gaussianSegmentProduct profileUpperTailStart
          (n - profileUpperTailStart) (profileIntegerDeviation m) := by
  have cert := constrainedProfileUpperCertificate hn hm
  have hstartTwo : 2 ≤ profileUpperTailStart := by
    norm_num [profileUpperTailStart]
  have htail := profileWeight_le_transitionSegmentProduct_from
    (hstartTwo.trans hn) hstartTwo hn m
  have ha11 := transitionSegmentProduct_le_a11_gaussian_from
    profileUpperTailStart n hstartTwo hn (profileAtScale m)
      (profileIntegerDeviation m)
      (delta := profileUpperDelta) (A := 2) (B := 1) (C := 11)
      (by norm_num [profileUpperDelta]) (by norm_num [profileUpperDelta])
      (by norm_num) (by norm_num) (by norm_num)
      cert.entry_two_le cert.taylorWindow cert.base cert.close cert.moderate
      cert.increment (profileAtScale_real_eq_center_add_deviation m)
      (by simpa only [one_mul] using cert.deviation)
      cert.deviationIncrement
  exact htail.trans ha11

/-! ## Splitting a full profile into a fixed prefix and a Gaussian future -/

def profilePrefix {n start : ℕ} (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (m : Profile n) : Profile start :=
  fun i ↦ m ⟨i.1, by have := i.2; omega⟩

def profileFuture {n start : ℕ} (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (m : Profile n) : Fin (n - start) → ℕ :=
  fun i ↦ m ⟨start - 1 + i.1, by have := i.2; omega⟩

lemma profileSplit_injective {n start : ℕ} (hstart : 2 ≤ start)
    (hstartn : start ≤ n) :
    Function.Injective (fun m : Profile n ↦
      (profilePrefix hstart hstartn m, profileFuture hstart hstartn m)) := by
  intro m q hmq
  funext i
  by_cases hi : i.1 < start - 1
  · let j : Fin (start - 1) := ⟨i.1, hi⟩
    have h := congrFun (congrArg Prod.fst hmq) j
    exact h
  · have hjlt : i.1 - (start - 1) < n - start := by
      have := i.2
      omega
    let j : Fin (n - start) := ⟨i.1 - (start - 1), hjlt⟩
    have h := congrFun (congrArg Prod.snd hmq) j
    let k : Fin (n - 1) :=
      ⟨start - 1 + j.1, by have := j.2; omega⟩
    change m k = q k at h
    have hki : k = i := by
      apply Fin.ext
      dsimp only [k, j]
      omega
    rw [hki] at h
    exact h

lemma profilePrefix_mem {n start : ℕ} (hstart : 2 ≤ start)
    (hstartn : start ≤ n) {delta : ℝ} {m : Profile n}
    (hm : m ∈ constrainedProfiles n delta) :
    profilePrefix hstart hstartn m ∈ constrainedProfiles start delta := by
  rw [mem_constrainedProfiles] at hm ⊢
  intro i
  let j : Fin (n - 1) := ⟨i.1, by have := i.2; omega⟩
  have h := hm j
  simpa [profilePrefix, scaleIndex, j] using h

lemma profileFuture_mem {n start : ℕ} (hstart : 2 ≤ start)
    (hstartn : start ≤ n) {delta : ℝ} {m : Profile n}
    (hm : m ∈ constrainedProfiles n delta) :
    profileFuture hstart hstartn m ∈
      Fintype.piFinset (fun i : Fin (n - start) ↦
        allowedValues delta (start + 1 + i.1)) := by
  rw [Fintype.mem_piFinset]
  intro i
  rw [mem_allowedValues]
  rw [mem_constrainedProfiles] at hm
  let j : Fin (n - 1) := ⟨start - 1 + i.1, by have := i.2; omega⟩
  have h := hm j
  have hscale : scaleIndex j = start + 1 + i.1 := by
    unfold scaleIndex
    dsimp only [j]
    omega
  change InProfileWindow delta (start + 1 + i.1)
    (profileFuture hstart hstartn m i)
  unfold profileFuture
  rw [← hscale]
  exact h

lemma profileAtScale_profilePrefix {n start : ℕ} (hstart : 2 ≤ start)
    (hstartn : start ≤ n) (m : Profile n) :
    profileAtScale (profilePrefix hstart hstartn m) start =
      profileAtScale m start := by
  unfold profileAtScale
  rw [dif_pos ⟨hstart, le_rfl⟩, dif_pos ⟨hstart, hstartn⟩]
  rfl

lemma profileIntegerDeviation_profilePrefix {n start : ℕ}
    (hstart : 2 ≤ start) (hstartn : start ≤ n) (m : Profile n) :
    profileIntegerDeviation (profilePrefix hstart hstartn m) start =
      profileIntegerDeviation m start := by
  unfold profileIntegerDeviation
  rw [profileAtScale_profilePrefix hstart hstartn]

lemma profileFuture_eq_profileAtScale {n start : ℕ}
    (hstart : 2 ≤ start) (hstartn : start ≤ n) (m : Profile n)
    (i : Fin (n - start)) :
    profileFuture hstart hstartn m i =
      profileAtScale m (start + 1 + i.1) := by
  unfold profileAtScale
  rw [dif_pos]
  · unfold profileFuture
    congr 1
    apply Fin.ext
    dsimp
    omega
  · constructor <;> omega

lemma gaussianFutureTupleWeight_eq_segment
    (l steps : ℕ) (x : ℤ) (D : ℕ → ℤ) (p : Fin steps → ℕ)
    (hx : x = D l)
    (hp : ∀ i : Fin steps,
      (p i : ℤ) - profileCenter (l + 1 + i.1) = D (l + 1 + i.1)) :
    gaussianFutureTupleWeight l x p = gaussianSegmentProduct l steps D := by
  induction steps generalizing l x with
  | zero => simp [gaussianFutureTupleWeight, gaussianSegmentProduct]
  | succ steps ih =>
      rw [gaussianFutureTupleWeight, gaussianSegmentProduct]
      have hp0 := hp (0 : Fin (steps + 1))
      simp only [Fin.val_zero, Nat.add_zero] at hp0
      rw [hx, hp0]
      congr 1
      apply ih (l + 1) _
      · simpa [Nat.add_assoc] using hp0
      · intro i
        have hs := hp i.succ
        have hidx : l + 1 + (i.1 + 1) = l + 1 + 1 + i.1 := by omega
        change ((p i.succ : ℕ) : ℤ) -
            profileCenter (l + 1 + 1 + i.1) = D (l + 1 + 1 + i.1)
        rw [← hidx]
        exact hs

lemma gaussianSegmentProduct_eq_splitWeight {n start : ℕ}
    (hstart : 2 ≤ start) (hstartn : start ≤ n) (m : Profile n) :
    gaussianSegmentProduct start (n - start) (profileIntegerDeviation m) =
      gaussianFutureTupleWeight start
        (profileIntegerDeviation (profilePrefix hstart hstartn m) start)
        (profileFuture hstart hstartn m) := by
  symm
  apply gaussianFutureTupleWeight_eq_segment
  · exact profileIntegerDeviation_profilePrefix hstart hstartn m
  · intro i
    rw [profileFuture_eq_profileAtScale hstart hstartn]
    unfold profileIntegerDeviation
    congr 2

/-- The entire constrained Gaussian tail sum is bounded by a fixed prefix
multiplicity times the unrestricted lattice-Gaussian partition. -/
theorem sum_constrained_gaussianSegmentProduct_le {n start : ℕ}
    (hstart : 2 ≤ start) (hstartn : start ≤ n) (delta : ℝ) :
    (∑ m ∈ constrainedProfiles n delta,
        gaussianSegmentProduct start (n - start) (profileIntegerDeviation m)) ≤
      ((constrainedProfiles start delta).card : ℝ) *
        Real.exp (∑ j ∈ Finset.Ico start n, 1 / (j : ℝ)) := by
  let P : Finset (Profile start) := constrainedProfiles start delta
  let Q : Finset (Fin (n - start) → ℕ) :=
    Fintype.piFinset (fun i : Fin (n - start) ↦
      allowedValues delta (start + 1 + i.1))
  let e : Profile n → Profile start × (Fin (n - start) → ℕ) :=
    fun m ↦ (profilePrefix hstart hstartn m, profileFuture hstart hstartn m)
  let w : Profile start × (Fin (n - start) → ℕ) → ℝ :=
    fun z ↦ gaussianFutureTupleWeight start
      (profileIntegerDeviation z.1 start) z.2
  have he : Function.Injective e := profileSplit_injective hstart hstartn
  have himage : (constrainedProfiles n delta).image e ⊆ P ×ˢ Q := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨m, hm, rfl⟩ := hz
    rw [Finset.mem_product]
    exact ⟨profilePrefix_mem hstart hstartn hm,
      profileFuture_mem hstart hstartn hm⟩
  have hw0 : ∀ z, 0 ≤ w z := by
    intro z
    exact gaussianFutureTupleWeight_nonneg _ _ _
  calc
    (∑ m ∈ constrainedProfiles n delta,
        gaussianSegmentProduct start (n - start) (profileIntegerDeviation m)) =
        ∑ m ∈ constrainedProfiles n delta, w (e m) := by
      apply Finset.sum_congr rfl
      intro m hm
      dsimp only [w, e]
      exact gaussianSegmentProduct_eq_splitWeight hstart hstartn m
    _ = ∑ z ∈ (constrainedProfiles n delta).image e, w z := by
      symm
      exact Finset.sum_image he.injOn
    _ ≤ ∑ z ∈ P ×ˢ Q, w z := by
      exact Finset.sum_le_sum_of_subset_of_nonneg himage
        (fun z _hz _hnot ↦ hw0 z)
    _ = ∑ p ∈ P, ∑ q ∈ Q, w (p, q) := by
      rw [Finset.sum_product]
    _ ≤ ∑ p ∈ P,
        Real.exp (∑ j ∈ Finset.Ico start n, 1 / (j : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      dsimp only [Q, w]
      have h := sum_gaussianFutureTupleWeight_le (n - start) start
        (show 0 < start by omega) (profileIntegerDeviation p start)
        (allowedValues delta)
      rw [Nat.add_sub_of_le hstartn] at h
      exact h
    _ = ((constrainedProfiles start delta).card : ℝ) *
        Real.exp (∑ j ∈ Finset.Ico start n, 1 / (j : ℝ)) := by
      simp [P, nsmul_eq_mul]

/-- Raw complete-profile upper bound, with the fixed prefix cardinality and
harmonic lattice correction still visible. -/
theorem constrainedProfileWeight_le_raw {n : ℕ}
    (hn : profileUpperTailStart ≤ n) :
    constrainedProfileWeight n profileUpperDelta ≤
      Real.exp (-(2 * (n - profileUpperTailStart : ℕ) : ℝ) +
        a11ErrorCoefficient profileUpperDelta 2 1 11 *
          (n : ℝ) ^ (3 * profileUpperDelta) + 4) *
        ((constrainedProfiles profileUpperTailStart profileUpperDelta).card : ℝ) *
        Real.exp (∑ j ∈ Finset.Ico profileUpperTailStart n, 1 / (j : ℝ)) := by
  have hstartTwo : 2 ≤ profileUpperTailStart := by
    norm_num [profileUpperTailStart]
  have hpoint :
      (∑ m ∈ constrainedProfiles n profileUpperDelta, profileWeight m) ≤
        ∑ m ∈ constrainedProfiles n profileUpperDelta,
          Real.exp (-(2 * (n - profileUpperTailStart : ℕ) : ℝ) +
            a11ErrorCoefficient profileUpperDelta 2 1 11 *
              (n : ℝ) ^ (3 * profileUpperDelta) + 4) *
            gaussianSegmentProduct profileUpperTailStart
              (n - profileUpperTailStart) (profileIntegerDeviation m) := by
    apply Finset.sum_le_sum
    intro m hm
    exact constrained_profileWeight_le_tailGaussian hn
      (mem_constrainedProfiles.mp hm)
  have hgauss := sum_constrained_gaussianSegmentProduct_le
    hstartTwo hn profileUpperDelta
  unfold constrainedProfileWeight
  calc
    (∑ m ∈ constrainedProfiles n profileUpperDelta, profileWeight m) ≤
        ∑ m ∈ constrainedProfiles n profileUpperDelta,
          Real.exp (-(2 * (n - profileUpperTailStart : ℕ) : ℝ) +
            a11ErrorCoefficient profileUpperDelta 2 1 11 *
              (n : ℝ) ^ (3 * profileUpperDelta) + 4) *
            gaussianSegmentProduct profileUpperTailStart
              (n - profileUpperTailStart) (profileIntegerDeviation m) := hpoint
    _ = Real.exp (-(2 * (n - profileUpperTailStart : ℕ) : ℝ) +
            a11ErrorCoefficient profileUpperDelta 2 1 11 *
              (n : ℝ) ^ (3 * profileUpperDelta) + 4) *
          (∑ m ∈ constrainedProfiles n profileUpperDelta,
            gaussianSegmentProduct profileUpperTailStart
              (n - profileUpperTailStart) (profileIntegerDeviation m)) := by
      rw [Finset.mul_sum]
    _ ≤ Real.exp (-(2 * (n - profileUpperTailStart : ℕ) : ℝ) +
            a11ErrorCoefficient profileUpperDelta 2 1 11 *
              (n : ℝ) ^ (3 * profileUpperDelta) + 4) *
          (((constrainedProfiles profileUpperTailStart profileUpperDelta).card : ℝ) *
            Real.exp (∑ j ∈ Finset.Ico profileUpperTailStart n,
              1 / (j : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hgauss (Real.exp_nonneg _)
    _ = _ := by ring

lemma harmonicTail_le_three_rpow {n : ℕ} (hn : 1 ≤ n) :
    (∑ j ∈ Finset.Ico profileUpperTailStart n, 1 / (j : ℝ)) ≤
      3 * (n : ℝ) ^ (3 / 5 : ℝ) := by
  have hsubset : Finset.Ico profileUpperTailStart n ⊆ Finset.Icc 1 n := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    rw [Finset.mem_Icc]
    constructor
    · have hs : 1 ≤ profileUpperTailStart := by norm_num [profileUpperTailStart]
      omega
    · omega
  have hleH : (∑ j ∈ Finset.Ico profileUpperTailStart n, 1 / (j : ℝ)) ≤
      (harmonic n : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    simp only [one_div]
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro j _hj _hnot
    positivity
  have hH := harmonic_le_one_add_log n
  have hlog := Real.log_natCast_le_rpow_div n
    (by norm_num : (0 : ℝ) < 3 / 5)
  have hpowOne : (1 : ℝ) ≤ (n : ℝ) ^ (3 / 5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have hlog' : Real.log (n : ℝ) ≤
      (5 / 3 : ℝ) * (n : ℝ) ^ (3 / 5 : ℝ) := by
    convert hlog using 1
    norm_num [div_eq_mul_inv]
    ring
  exact hleH.trans (hH.trans (by linarith))

/-- The coefficient supplied directly by the one-block A.11 argument. -/
def profileUpperCoreConstant : ℝ :=
  a11ErrorCoefficient profileUpperDelta 2 1 11 +
    2 * profileUpperTailStart + 7 +
      Real.log ((constrainedProfiles profileUpperTailStart profileUpperDelta).card + 1)

/-- The public coefficient also reserves one further conditional A.11
coefficient and the fixed four-step buffered-bridge cost. -/
def profileUpperConstant : ℝ :=
  2 * profileUpperCoreConstant + 400

/-- The sharp core form of the complete constrained-profile upper bound. -/
theorem constrainedProfileWeight_le_exp_core {n : ℕ}
    (hn : profileUpperTailStart ≤ n) :
    constrainedProfileWeight n profileUpperDelta ≤
      Real.exp (-(2 * (n : ℝ)) +
        profileUpperCoreConstant * (n : ℝ) ^ (3 / 5 : ℝ)) := by
  have hnOne : 1 ≤ n :=
    (show 1 ≤ profileUpperTailStart by norm_num [profileUpperTailStart]).trans hn
  have hraw := constrainedProfileWeight_le_raw hn
  have hh := harmonicTail_le_three_rpow hnOne
  let cardR : ℝ :=
    (constrainedProfiles profileUpperTailStart profileUpperDelta).card
  have hcard0 : 0 ≤ cardR := by
    dsimp only [cardR]
    exact Nat.cast_nonneg _
  have hcard1 : 0 < cardR + 1 := by linarith
  have hcard : cardR ≤ Real.exp (Real.log (cardR + 1)) := by
    rw [Real.exp_log hcard1]
    linarith
  have ha : 0 ≤ a11ErrorCoefficient profileUpperDelta 2 1 11 :=
    a11ErrorCoefficient_nonneg (by norm_num [profileUpperDelta])
      (by norm_num) (by norm_num) (by norm_num)
  have hlog0 : 0 ≤ Real.log (cardR + 1) :=
    Real.log_nonneg (by linarith)
  have hpowOne : (1 : ℝ) ≤ (n : ℝ) ^ (3 / 5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hnOne) (by norm_num)
  have hcast : ((n - profileUpperTailStart : ℕ) : ℝ) =
      (n : ℝ) - profileUpperTailStart := by rw [Nat.cast_sub hn]
  have hcardExp : cardR *
      Real.exp (∑ j ∈ Finset.Ico profileUpperTailStart n, 1 / (j : ℝ)) ≤
      Real.exp (Real.log (cardR + 1) +
        3 * (n : ℝ) ^ (3 / 5 : ℝ)) := by
    calc
      cardR * Real.exp (∑ j ∈ Finset.Ico profileUpperTailStart n,
          1 / (j : ℝ)) ≤
          Real.exp (Real.log (cardR + 1)) *
            Real.exp (∑ j ∈ Finset.Ico profileUpperTailStart n,
              1 / (j : ℝ)) := by
        gcongr
      _ ≤ Real.exp (Real.log (cardR + 1)) *
            Real.exp (3 * (n : ℝ) ^ (3 / 5 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hh)
          (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]
  have hmain :
      (-(2 * ((n : ℝ) - profileUpperTailStart)) +
          a11ErrorCoefficient profileUpperDelta 2 1 11 *
            (n : ℝ) ^ (3 * profileUpperDelta) + 4) +
        (Real.log (cardR + 1) + 3 * (n : ℝ) ^ (3 / 5 : ℝ)) ≤
      -(2 * (n : ℝ)) +
        profileUpperCoreConstant * (n : ℝ) ^ (3 / 5 : ℝ) := by
    unfold profileUpperCoreConstant
    dsimp only [cardR]
    simp only [profileUpperDelta] at *
    have hconst : 0 ≤
        2 * (profileUpperTailStart : ℝ) + 4 +
          Real.log ((constrainedProfiles profileUpperTailStart (1 / 5)).card + 1) := by
      have hstart0 : (0 : ℝ) ≤ profileUpperTailStart := Nat.cast_nonneg _
      have hlog0' : 0 ≤
          Real.log ((constrainedProfiles profileUpperTailStart (1 / 5)).card + 1) := by
        dsimp only [cardR] at hlog0
        simpa only [profileUpperDelta] using hlog0
      linarith
    have hexp : (3 * (1 / 5 : ℝ)) = 3 / 5 := by norm_num
    rw [hexp]
    nlinarith
  rw [hcast] at hraw
  change constrainedProfileWeight n profileUpperDelta ≤
      Real.exp (-(2 * ((n : ℝ) - profileUpperTailStart)) +
          a11ErrorCoefficient profileUpperDelta 2 1 11 *
            (n : ℝ) ^ (3 * profileUpperDelta) + 4) * cardR *
        Real.exp (∑ j ∈ Finset.Ico profileUpperTailStart n,
          1 / (j : ℝ)) at hraw
  calc
    constrainedProfileWeight n profileUpperDelta ≤
        Real.exp (-(2 * ((n : ℝ) - profileUpperTailStart)) +
          a11ErrorCoefficient profileUpperDelta 2 1 11 *
            (n : ℝ) ^ (3 * profileUpperDelta) + 4) * cardR *
          Real.exp (∑ j ∈ Finset.Ico profileUpperTailStart n,
            1 / (j : ℝ)) := hraw
    _ ≤ Real.exp (-(2 * ((n : ℝ) - profileUpperTailStart)) +
          a11ErrorCoefficient profileUpperDelta 2 1 11 *
            (n : ℝ) ^ (3 * profileUpperDelta) + 4) *
        Real.exp (Real.log (cardR + 1) +
          3 * (n : ℝ) ^ (3 / 5 : ℝ)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hcardExp (Real.exp_nonneg _)
    _ = Real.exp
        ((-(2 * ((n : ℝ) - profileUpperTailStart)) +
          a11ErrorCoefficient profileUpperDelta 2 1 11 *
            (n : ℝ) ^ (3 * profileUpperDelta) + 4) +
          (Real.log (cardR + 1) +
            3 * (n : ℝ) ^ (3 / 5 : ℝ))) := by
      exact (Real.exp_add _ _).symm
    _ ≤ Real.exp (-(2 * (n : ℝ)) +
        profileUpperCoreConstant * (n : ℝ) ^ (3 / 5 : ℝ)) :=
      Real.exp_le_exp.mpr hmain

/-- **Complete HLOZ constrained-profile upper bound.** -/
theorem constrainedProfileWeight_le_exp {n : ℕ}
    (hn : profileUpperTailStart ≤ n) :
    constrainedProfileWeight n profileUpperDelta ≤
      Real.exp (-(2 * (n : ℝ)) +
        profileUpperConstant * (n : ℝ) ^ (3 / 5 : ℝ)) := by
  have hcore := constrainedProfileWeight_le_exp_core hn
  have hcoreNonneg : 0 ≤ profileUpperCoreConstant := by
    unfold profileUpperCoreConstant
    have ha : 0 ≤ a11ErrorCoefficient profileUpperDelta 2 1 11 :=
      a11ErrorCoefficient_nonneg (by norm_num [profileUpperDelta])
        (by norm_num) (by norm_num) (by norm_num)
    have hlog : 0 ≤ Real.log
        ((constrainedProfiles profileUpperTailStart profileUpperDelta).card + 1) := by
      apply Real.log_nonneg
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega :
        (constrainedProfiles profileUpperTailStart
          profileUpperDelta).card + 1 ≠ 0)
    positivity
  have hpow : 0 ≤ (n : ℝ) ^ (3 / 5 : ℝ) := by positivity
  apply hcore.trans
  apply Real.exp_le_exp.mpr
  unfold profileUpperConstant
  nlinarith

end

end Erdos1165.ProfileWeightUpper
