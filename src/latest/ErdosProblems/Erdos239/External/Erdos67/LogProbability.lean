import ErdosProblems.Erdos239.External.Erdos67.Entropy
import Mathlib.Analysis.PSeries
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic

/-!
# Finite logarithmic probability

This file packages the elementary probability law behind logarithmically averaged
arguments.  On a nonempty interval of positive integers, the point `n` has mass
proportional to `1 / n`.  Everything here is finite and non-asymptotic.

There are two useful ways to express the change-of-variables property of logarithmic
measure.  Pure dilation is exact on the sampled lattice.  An affine change
`n \mapsto q * n + r` differs from pure dilation only by the explicit Radon--Nikodym
factor `q*n/(q*n+r)`, whose distance from one is at most `r/(q*L+r)` on a window
starting at `L`.  Translation is the case `q = 1`.
-/

open scoped BigOperators ENNReal NNReal
open Finset MeasureTheory

namespace Erdos67

noncomputable section

/-! ## The harmonic law on a finite interval -/

/-- The finite integer window on which logarithmic probability is supported. -/
def logProbWindow (L U : ℕ) : Finset ℕ :=
  Finset.Icc L U

@[simp]
theorem mem_logProbWindow {L U n : ℕ} :
    n ∈ logProbWindow L U ↔ L ≤ n ∧ n ≤ U := by
  simp [logProbWindow]

/-- An index bundled with the assertion that it lies in the logarithmic window. -/
abbrev LogProbIndex (L U : ℕ) := {n : ℕ // n ∈ logProbWindow L U}

/-- The nonnegative harmonic weight `1/n`. -/
def logProbHarmonicNN (n : ℕ) : ℝ≥0 :=
  (n : ℝ≥0)⁻¹

@[simp]
theorem logProbHarmonicNN_coe (n : ℕ) :
    (logProbHarmonicNN n : ℝ) = (n : ℝ)⁻¹ := by
  simp [logProbHarmonicNN]

theorem logProbHarmonicNN_pos {n : ℕ} (hn : 0 < n) :
    0 < logProbHarmonicNN n := by
  simp [logProbHarmonicNN, hn]

/-- Total (unnormalized) harmonic mass of the window. -/
def logProbMassNN (L U : ℕ) : ℝ≥0 :=
  ∑ n : LogProbIndex L U, logProbHarmonicNN n.1

theorem logProbMassNN_pos {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U) :
    0 < logProbMassNN L U := by
  let i : LogProbIndex L U := ⟨L, by simp [logProbWindow, hLU]⟩
  apply Finset.sum_pos'
  · exact fun _ _ ↦ bot_le
  · exact ⟨i, Finset.mem_univ i, logProbHarmonicNN_pos hL⟩

theorem logProbMassNN_ne_zero {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U) :
    logProbMassNN L U ≠ 0 :=
  (logProbMassNN_pos hL hLU).ne'

/-- The normalized harmonic weight of a point in the window. -/
def logProbWeightNN (L U : ℕ) (n : LogProbIndex L U) : ℝ≥0 :=
  logProbHarmonicNN n.1 / logProbMassNN L U

theorem sum_logProbWeightNN {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U) :
    ∑ n : LogProbIndex L U, logProbWeightNN L U n = 1 := by
  simp only [logProbWeightNN, ← Finset.sum_div]
  exact div_self (logProbMassNN_ne_zero hL hLU)

/-- The harmonic probability mass function on `L ≤ n ≤ U`. -/
def logProbPMF (L U : ℕ) (hL : 0 < L) (hLU : L ≤ U) :
    PMF (LogProbIndex L U) :=
  PMF.ofFintype (fun n ↦ (logProbWeightNN L U n : ℝ≥0∞)) (by
    exact_mod_cast sum_logProbWeightNN hL hLU)

@[simp]
theorem logProbPMF_apply {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U)
    (n : LogProbIndex L U) :
    logProbPMF L U hL hLU n = logProbWeightNN L U n :=
  rfl

/-- The expectation of a function under finite logarithmic probability, written as a
finite weighted sum.  It is defined for all endpoints; positivity/nonemptiness assumptions
are needed only when identifying the weights with a PMF. -/
def logProbExpectation {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (L U : ℕ) (f : ℕ → E) : E :=
  ∑ n : LogProbIndex L U, (logProbWeightNN L U n : ℝ) • f n.1

theorem logProbExpectation_eq_window_sum {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (L U : ℕ) (f : ℕ → E) :
    logProbExpectation L U f =
      ∑ n ∈ logProbWindow L U,
        ((logProbHarmonicNN n / logProbMassNN L U : ℝ≥0) : ℝ) • f n := by
  unfold logProbExpectation logProbWeightNN
  exact (Finset.sum_subtype (logProbWindow L U) (fun _ ↦ Iff.rfl)
    (fun n ↦ ((logProbHarmonicNN n / logProbMassNN L U : ℝ≥0) : ℝ) • f n)).symm

/-- Integration against the harmonic PMF is exactly the explicit finite weighted sum. -/
theorem integral_logProbPMF {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U) (f : ℕ → E) :
    ∫ n, f n.1 ∂(logProbPMF L U hL hLU).toMeasure =
      logProbExpectation L U f := by
  rw [PMF.integral_eq_sum]
  simp only [logProbPMF_apply, ENNReal.coe_toReal, logProbExpectation]

theorem norm_logProbExpectation_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U)
    (f : ℕ → E) (B : ℝ) (hf : ∀ n ∈ logProbWindow L U, ‖f n‖ ≤ B) :
    ‖logProbExpectation L U f‖ ≤ B := by
  calc
    ‖logProbExpectation L U f‖ ≤
        ∑ n : LogProbIndex L U,
          ‖(logProbWeightNN L U n : ℝ) • f n.1‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ n : LogProbIndex L U, (logProbWeightNN L U n : ℝ) * B := by
      apply Finset.sum_le_sum
      intro n _
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (NNReal.coe_nonneg (logProbWeightNN L U n))]
      exact mul_le_mul_of_nonneg_left (hf n.1 n.2)
        (NNReal.coe_nonneg (logProbWeightNN L U n))
    _ = B := by
      rw [← Finset.sum_mul, ← NNReal.coe_sum, sum_logProbWeightNN hL hLU]
      simp

/-! ## Finite change of variables -/

/-- The logarithmic average after translating the sampled points, with the exact
change-of-variables density `n/(n+h)`. -/
def logProbShiftReweighted {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (L U h : ℕ) (f : ℕ → E) : E :=
  ∑ n : LogProbIndex L U,
    (logProbWeightNN L U n : ℝ) •
      (((n.1 : ℝ) / (n.1 + h : ℕ)) • f (n.1 + h))

/-- The logarithmic average after the affine change `n ↦ q*n+r`, with the exact
change-of-variables density `q*n/(q*n+r)`. -/
def logProbAffineReweighted {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (L U q r : ℕ) (f : ℕ → E) : E :=
  ∑ n : LogProbIndex L U,
    (logProbWeightNN L U n : ℝ) •
      ((((q * n.1 : ℕ) : ℝ) / (q * n.1 + r : ℕ)) • f (q * n.1 + r))

theorem one_sub_nat_div_add (n h : ℕ) (hn : 0 < n) :
    (1 : ℝ) - (n : ℝ) / (n + h : ℕ) = (h : ℝ) / (n + h : ℕ) := by
  have hden : ((n + h : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem one_sub_mul_div_mul_add (q n r : ℕ) (hq : 0 < q) (hn : 0 < n) :
    (1 : ℝ) - (q * n : ℕ) / (q * n + r : ℕ) =
      (r : ℝ) / (q * n + r : ℕ) := by
  have hden : ((q * n + r : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem nat_div_add_nonneg (n h : ℕ) :
    0 ≤ (n : ℝ) / (n + h : ℕ) := by positivity

theorem nat_mul_div_add_nonneg (q n r : ℕ) :
    0 ≤ ((q * n : ℕ) : ℝ) / (q * n + r : ℕ) := by positivity

theorem nat_div_add_le_one (n h : ℕ) :
    (n : ℝ) / (n + h : ℕ) ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  · apply (div_le_one (by positivity)).2
    exact_mod_cast Nat.le_add_right n h

theorem nat_mul_div_add_le_one (q n r : ℕ) :
    ((q * n : ℕ) : ℝ) / (q * n + r : ℕ) ≤ 1 := by
  by_cases hqn : q * n = 0
  · simp [hqn]
  · apply (div_le_one (by positivity)).2
    exact_mod_cast Nat.le_add_right (q * n) r

/-- Pointwise translation error of the logarithmic Radon--Nikodym factor. -/
theorem one_sub_nat_div_add_le {L n h : ℕ} (hL : 0 < L) (hLn : L ≤ n) :
    (1 : ℝ) - (n : ℝ) / (n + h : ℕ) ≤ (h : ℝ) / (L + h : ℕ) := by
  rw [one_sub_nat_div_add n h (hL.trans_le hLn)]
  gcongr

/-- Pointwise affine-dilation error of the logarithmic Radon--Nikodym factor. -/
theorem one_sub_mul_div_mul_add_le {L q n r : ℕ}
    (hL : 0 < L) (hq : 0 < q) (hLn : L ≤ n) :
    (1 : ℝ) - (q * n : ℕ) / (q * n + r : ℕ) ≤
      (r : ℝ) / (q * L + r : ℕ) := by
  rw [one_sub_mul_div_mul_add q n r hq (hL.trans_le hLn)]
  gcongr

/-- Explicit approximate translation invariance on a finite logarithmic window.

The left average uses weight `1/n`; the reweighted average uses `1/(n+h)`.  For an
arbitrary `B`-bounded function, their normalized difference is at most
`B * h/(L+h)`. -/
theorem norm_logProbExpectation_shift_sub_reweighted_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L U h : ℕ} (hL : 0 < L) (hLU : L ≤ U)
    (f : ℕ → E) (B : ℝ)
    (hf : ∀ n ∈ logProbWindow L U, ‖f (n + h)‖ ≤ B) :
    ‖logProbExpectation L U (fun n ↦ f (n + h)) -
        logProbShiftReweighted L U h f‖ ≤
      ((h : ℝ) / (L + h : ℕ)) * B := by
  rw [logProbExpectation, logProbShiftReweighted, ← Finset.sum_sub_distrib]
  calc
    ‖∑ n : LogProbIndex L U,
        ((logProbWeightNN L U n : ℝ) • f (n.1 + h) -
          (logProbWeightNN L U n : ℝ) •
            (((n.1 : ℝ) / (n.1 + h : ℕ)) • f (n.1 + h)))‖ ≤
        ∑ n : LogProbIndex L U,
          ‖(logProbWeightNN L U n : ℝ) • f (n.1 + h) -
            (logProbWeightNN L U n : ℝ) •
              (((n.1 : ℝ) / (n.1 + h : ℕ)) • f (n.1 + h))‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ n : LogProbIndex L U,
        (logProbWeightNN L U n : ℝ) *
          (((h : ℝ) / (L + h : ℕ)) * B) := by
      apply Finset.sum_le_sum
      intro n _
      rw [← smul_sub]
      have hdiff :
          f (n.1 + h) - ((n.1 : ℝ) / (n.1 + h : ℕ)) • f (n.1 + h) =
            ((1 : ℝ) - (n.1 : ℝ) / (n.1 + h : ℕ)) • f (n.1 + h) := by
        rw [sub_smul, one_smul]
      rw [hdiff, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (NNReal.coe_nonneg (logProbWeightNN L U n)),
        norm_smul, Real.norm_eq_abs]
      have hn : L ≤ n.1 := (mem_logProbWindow.mp n.2).1
      have hfac0 : 0 ≤ (1 : ℝ) - (n.1 : ℝ) / (n.1 + h : ℕ) :=
        sub_nonneg.mpr (nat_div_add_le_one n.1 h)
      rw [abs_of_nonneg hfac0]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (one_sub_nat_div_add_le hL hn) (hf n.1 n.2)
          (norm_nonneg _) (by positivity))
        (NNReal.coe_nonneg (logProbWeightNN L U n))
    _ = ((h : ℝ) / (L + h : ℕ)) * B := by
      rw [← Finset.sum_mul, ← NNReal.coe_sum, sum_logProbWeightNN hL hLU]
      simp

/-- Explicit approximate affine-dilation invariance on a finite logarithmic window.

After `n ↦ q*n+r`, changing the harmonic density from `1/n` to the exact affine
density costs at most `B * r/(q*L+r)`. -/
theorem norm_logProbExpectation_affine_sub_reweighted_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L U q r : ℕ} (hL : 0 < L) (hLU : L ≤ U) (hq : 0 < q)
    (f : ℕ → E) (B : ℝ)
    (hf : ∀ n ∈ logProbWindow L U, ‖f (q * n + r)‖ ≤ B) :
    ‖logProbExpectation L U (fun n ↦ f (q * n + r)) -
        logProbAffineReweighted L U q r f‖ ≤
      ((r : ℝ) / (q * L + r : ℕ)) * B := by
  rw [logProbExpectation, logProbAffineReweighted, ← Finset.sum_sub_distrib]
  calc
    ‖∑ n : LogProbIndex L U,
        ((logProbWeightNN L U n : ℝ) • f (q * n.1 + r) -
          (logProbWeightNN L U n : ℝ) •
            ((((q * n.1 : ℕ) : ℝ) / (q * n.1 + r : ℕ)) •
              f (q * n.1 + r)))‖ ≤
        ∑ n : LogProbIndex L U,
          ‖(logProbWeightNN L U n : ℝ) • f (q * n.1 + r) -
            (logProbWeightNN L U n : ℝ) •
              ((((q * n.1 : ℕ) : ℝ) / (q * n.1 + r : ℕ)) •
                f (q * n.1 + r))‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ n : LogProbIndex L U,
        (logProbWeightNN L U n : ℝ) *
          (((r : ℝ) / (q * L + r : ℕ)) * B) := by
      apply Finset.sum_le_sum
      intro n _
      rw [← smul_sub]
      have hdiff :
          f (q * n.1 + r) -
              (((q * n.1 : ℕ) : ℝ) / (q * n.1 + r : ℕ)) • f (q * n.1 + r) =
            ((1 : ℝ) - ((q * n.1 : ℕ) : ℝ) / (q * n.1 + r : ℕ)) •
              f (q * n.1 + r) := by
        rw [sub_smul, one_smul]
      rw [hdiff, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (NNReal.coe_nonneg (logProbWeightNN L U n)),
        norm_smul, Real.norm_eq_abs]
      have hn : L ≤ n.1 := (mem_logProbWindow.mp n.2).1
      have hfac0 :
          0 ≤ (1 : ℝ) - (q * n.1 : ℕ) / (q * n.1 + r : ℕ) :=
        sub_nonneg.mpr (nat_mul_div_add_le_one q n.1 r)
      rw [abs_of_nonneg hfac0]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (one_sub_mul_div_mul_add_le hL hq hn) (hf n.1 n.2)
          (norm_nonneg _) (by positivity))
        (NNReal.coe_nonneg (logProbWeightNN L U n))
    _ = ((r : ℝ) / (q * L + r : ℕ)) * B := by
      rw [← Finset.sum_mul, ← NNReal.coe_sum, sum_logProbWeightNN hL hLU]
      simp

/-- Pure dilation has no Radon--Nikodym error: its affine reweighting factor is one. -/
theorem logProbAffineReweighted_zero (L U q : ℕ) (hL : 0 < L) (hq : 0 < q)
    {E : Type*} [AddCommMonoid E] [Module ℝ E] (f : ℕ → E) :
    logProbAffineReweighted L U q 0 f =
      logProbExpectation L U (fun n ↦ f (q * n)) := by
  unfold logProbAffineReweighted logProbExpectation
  apply Finset.sum_congr rfl
  intro n _
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hnR : (n.1 : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (hL.trans_le (mem_logProbWindow.mp n.2).1)
  simp only [Nat.add_zero]
  rw [Nat.cast_mul, div_self (mul_ne_zero hqR hnR), one_smul]

/-! ## The associated real finite probability vector -/

open FiniteEntropy

/-- The harmonic PMF written as the real finite probability vector used by the
finite entropy and CRT arguments. -/
def logProbFiniteLaw (L U : ℕ) (hL : 0 < L) (hLU : L ≤ U) :
    FinProb (LogProbIndex L U) :=
  ⟨fun n ↦ (logProbWeightNN L U n : ℝ), by
    constructor
    · intro n
      exact NNReal.coe_nonneg (logProbWeightNN L U n)
    · rw [← NNReal.coe_sum, sum_logProbWeightNN hL hLU]
      simp⟩

@[simp]
theorem logProbFiniteLaw_apply (L U : ℕ) (hL : 0 < L) (hLU : L ≤ U)
    (n : LogProbIndex L U) :
    logProbFiniteLaw L U hL hLU n = (logProbWeightNN L U n : ℝ) :=
  rfl

end

end Erdos67
