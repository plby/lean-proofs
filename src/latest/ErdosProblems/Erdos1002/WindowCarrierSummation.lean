import ErdosProblems.Erdos1002.WindowArithmeticEnergy
import Mathlib.Order.Filter.AtTopBot.Interval

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Summation over the Bernoulli carrier modes

This module closes the purely Hilbert-space carrier summation left after
`WindowArithmeticEnergy`.  The Bernoulli coefficients decay quadratically,
so both their total mass and their first logarithmic moment are summable.
Consequently the symmetric finite carrier sums are uniformly `o(log)` and
converge in `UnitCircleL2` as the carrier cutoff tends to infinity.

No identification with the literal shot error is asserted here.
-/

open Filter Finset
open scoped BigOperators Topology ComplexConjugate

namespace Erdos1002

noncomputable section

/-! ## Linear norm form of the one-carrier estimate -/

theorem uniform_norm_windowModeFourierPolynomial_small_above_scale
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ H : ℝ, 0 ≤ H ∧
      ∀ (N P K : ℕ) (ell : ℤ), 0 < P →
        H ≤ Real.log (windowArithmeticScale N P ell) →
          ‖windowModeFourierPolynomial N P K ell‖ ≤
            delta * Real.log (windowArithmeticScale N P ell) := by
  have hdeltaSq : 0 < delta ^ 2 := sq_pos_of_pos hdelta
  rcases uniform_norm_windowModeFourierPolynomial_sq_small_above_scale
    hdeltaSq with ⟨H, hH, hsq⟩
  refine ⟨H, hH, ?_⟩
  intro N P K ell hP hscale
  let L : ℝ := Real.log (windowArithmeticScale N P ell)
  have hL : 0 ≤ L := by
    dsimp [L]
    exact le_trans (by norm_num) (one_le_log_windowArithmeticScale N P ell)
  have h := hsq N P K ell hP hscale
  have hsquare :
      ‖windowModeFourierPolynomial N P K ell‖ ^ 2 ≤
        (delta * L) ^ 2 := by
    calc
      ‖windowModeFourierPolynomial N P K ell‖ ^ 2 ≤ delta ^ 2 * L ^ 2 := by
        simpa only [L] using! h
      _ = (delta * L) ^ 2 := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hdelta.le hL)).mp hsquare

/-! ## Summable carrier weights -/

/-- A simple scalar majorant for the exact Bernoulli coefficient. -/
def bernoulliCarrierMajorant (ell : ℤ) : ℝ :=
  if ell = 0 then 1 else 1 / (ell.natAbs : ℝ) ^ 2

theorem norm_bernoulliMarkFourierCoefficient_eq
    {ell : ℤ} (hell : ell ≠ 0) :
    ‖bernoulliMarkFourierCoefficient ell‖ =
      1 / (4 * Real.pi ^ 2 * (ell.natAbs : ℝ) ^ 2) := by
  rw [bernoulliMarkFourierCoefficient, if_neg hell, norm_neg, norm_div]
  simp only [norm_one, norm_mul, norm_pow, Complex.norm_intCast,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [show ‖(4 : ℂ)‖ = (4 : ℝ) by norm_num]
  have habs : |(ell : ℝ)| = (ell.natAbs : ℝ) := by
    rw [← Int.cast_abs, ← Nat.cast_natAbs]
  rw [habs]

theorem norm_bernoulliMarkFourierCoefficient_le_majorant (ell : ℤ) :
    ‖bernoulliMarkFourierCoefficient ell‖ ≤ bernoulliCarrierMajorant ell := by
  by_cases hell : ell = 0
  · subst ell
    norm_num [bernoulliMarkFourierCoefficient, bernoulliCarrierMajorant]
  · rw [norm_bernoulliMarkFourierCoefficient_eq hell]
    rw [bernoulliCarrierMajorant, if_neg hell]
    have hnPos : (0 : ℝ) < (ell.natAbs : ℝ) ^ 2 := by
      positivity
    apply one_div_le_one_div_of_le hnPos
    have hpi : (1 : ℝ) ≤ 4 * Real.pi ^ 2 := by
      nlinarith [Real.pi_gt_three]
    simpa only [one_mul] using!
      mul_le_mul_of_nonneg_right hpi (sq_nonneg (ell.natAbs : ℝ))

theorem bernoulliCarrierMajorant_nonneg (ell : ℤ) :
    0 ≤ bernoulliCarrierMajorant ell := by
  unfold bernoulliCarrierMajorant
  split_ifs <;> positivity

@[simp]
theorem bernoulliCarrierMajorant_neg (ell : ℤ) :
    bernoulliCarrierMajorant (-ell) = bernoulliCarrierMajorant ell := by
  simp only [bernoulliCarrierMajorant, neg_eq_zero, Int.natAbs_neg]

private theorem summable_bernoulliCarrierMajorant_nat :
    Summable fun n : ℕ ↦ bernoulliCarrierMajorant (n : ℤ) := by
  have htail : Summable fun n : ℕ ↦
      bernoulliCarrierMajorant ((n + 1 : ℕ) : ℤ) := by
    have hp :=
      ((summable_nat_add_iff (f := fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) 1).2
        (Real.summable_one_div_nat_pow.mpr (by norm_num)))
    apply hp.congr
    intro n
    have hne : ((n + 1 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
    rw [bernoulliCarrierMajorant, if_neg hne, Int.natAbs_natCast]
  exact (summable_nat_add_iff 1).mp htail

theorem summable_bernoulliCarrierMajorant :
    Summable bernoulliCarrierMajorant := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · exact summable_bernoulliCarrierMajorant_nat
  · simpa only [bernoulliCarrierMajorant_neg] using!
      summable_bernoulliCarrierMajorant_nat

/-- Elementary bound used to control the logarithmic carrier moment. -/
theorem log_nat_add_one_le_three_sqrt
    (n : ℕ) (hn : 0 < n) :
    Real.log ((n + 1 : ℕ) : ℝ) ≤ 3 * Real.sqrt (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hone : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hnadd : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    push_cast
    exact_mod_cast (by omega : n + 1 ≤ 2 * n)
  have hlogmono : Real.log ((n + 1 : ℕ) : ℝ) ≤
      Real.log (2 * (n : ℝ)) := by
    apply Real.log_le_log
    · positivity
    · exact hnadd
  have hlogTwo : Real.log 2 ≤ Real.sqrt (n : ℝ) := by
    have h : Real.log 2 ≤ 1 := by
      have h' := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    exact h.trans hone
  have hlogSqrt : Real.log (Real.sqrt (n : ℝ)) ≤
      Real.sqrt (n : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hsqrt
  have hlogn : Real.log (n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
    have hsquare : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
      Real.sq_sqrt hnR.le
    calc
      Real.log (n : ℝ) = 2 * Real.log (Real.sqrt (n : ℝ)) := by
        rw [← hsquare, Real.log_pow]
        norm_num
      _ ≤ 2 * (Real.sqrt (n : ℝ) - 1) :=
        mul_le_mul_of_nonneg_left hlogSqrt (by norm_num)
      _ ≤ 2 * Real.sqrt (n : ℝ) := by linarith
  calc
    Real.log ((n + 1 : ℕ) : ℝ) ≤ Real.log (2 * (n : ℝ)) := hlogmono
    _ = Real.log 2 + Real.log (n : ℝ) := by
      rw [Real.log_mul (by norm_num) hnR.ne']
    _ ≤ 3 * Real.sqrt (n : ℝ) := by linarith

private theorem summable_bernoulliCarrierLogMoment_nat :
    Summable fun n : ℕ ↦
      bernoulliCarrierMajorant (n : ℤ) * Real.log ((n + 1 : ℕ) : ℝ) := by
  have hmajor : Summable fun n : ℕ ↦
      3 * (1 / (((n + 1 : ℕ) : ℝ) *
        Real.sqrt ((n + 1 : ℕ) : ℝ))) := by
    exact (summable_nat_add_iff 1).2
      (summable_windowDThreeHalfTerm.mul_left 3)
  have htail : Summable fun n : ℕ ↦
      bernoulliCarrierMajorant ((n + 1 : ℕ) : ℤ) *
        Real.log (((n + 1) + 1 : ℕ) : ℝ) := by
    apply hmajor.of_nonneg_of_le
    · intro n
      exact mul_nonneg (bernoulliCarrierMajorant_nonneg _)
        (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ (n + 1) + 1)))
    · intro n
      have hnPos : 0 < n + 1 := by omega
      have hlog := log_nat_add_one_le_three_sqrt (n + 1) hnPos
      have hnR : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have hsqrt : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) :=
        Real.sqrt_pos.2 hnR
      have hne : ((n + 1 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
      rw [bernoulliCarrierMajorant, if_neg hne, Int.natAbs_natCast]
      calc
        (1 / (((n + 1 : ℕ) : ℝ) ^ 2)) *
            Real.log (((n + 1) + 1 : ℕ) : ℝ) ≤
          (1 / (((n + 1 : ℕ) : ℝ) ^ 2)) *
            (3 * Real.sqrt ((n + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
        _ = 3 * (1 / (((n + 1 : ℕ) : ℝ) *
            Real.sqrt ((n + 1 : ℕ) : ℝ))) := by
          field_simp
          rw [Real.sq_sqrt hnR.le]
  exact (summable_nat_add_iff 1).mp htail

theorem summable_bernoulliCarrierLogMoment :
    Summable fun ell : ℤ ↦
      bernoulliCarrierMajorant ell *
        Real.log ((ell.natAbs + 1 : ℕ) : ℝ) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · simpa only [Int.natAbs_natCast] using!
      summable_bernoulliCarrierLogMoment_nat
  · simpa only [bernoulliCarrierMajorant_neg, Int.natAbs_neg,
      Int.natAbs_natCast] using!
      summable_bernoulliCarrierLogMoment_nat

/-- Total carrier mass. -/
def windowCarrierMassConstant : ℝ :=
  ∑' ell : ℤ, bernoulliCarrierMajorant ell

/-- First logarithmic moment of the carrier mass. -/
def windowCarrierLogMomentConstant : ℝ :=
  ∑' ell : ℤ, bernoulliCarrierMajorant ell *
    Real.log ((ell.natAbs + 1 : ℕ) : ℝ)

theorem windowCarrierMassConstant_nonneg : 0 ≤ windowCarrierMassConstant := by
  exact tsum_nonneg bernoulliCarrierMajorant_nonneg

theorem windowCarrierLogMomentConstant_nonneg :
    0 ≤ windowCarrierLogMomentConstant := by
  exact tsum_nonneg fun ell ↦ mul_nonneg
    (bernoulliCarrierMajorant_nonneg ell)
    (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ ell.natAbs + 1)))

/-! ## Uniform summation of the finite carrier block -/

/-- Smallest carrier scale, attained at `ell = 0`. -/
def windowCarrierBaseScale (P : ℕ) : ℝ :=
  Real.exp 1 + P

/-- One common scale which dominates the `ell = 1` carrier and is used in
the final logarithmic bound. -/
def windowCarrierGlobalScale (N P : ℕ) : ℝ :=
  Real.exp 1 + (N + 1) * P

theorem one_le_log_windowCarrierBaseScale (P : ℕ) :
    1 ≤ Real.log (windowCarrierBaseScale P) := by
  have hbase : Real.exp 1 ≤ windowCarrierBaseScale P := by
    unfold windowCarrierBaseScale
    have hP : (0 : ℝ) ≤ (P : ℝ) := by positivity
    linarith
  calc
    1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
    _ ≤ Real.log (windowCarrierBaseScale P) :=
      Real.log_le_log (Real.exp_pos 1) hbase

theorem one_le_log_windowCarrierGlobalScale (N P : ℕ) :
    1 ≤ Real.log (windowCarrierGlobalScale N P) := by
  have hbase : Real.exp 1 ≤ windowCarrierGlobalScale N P := by
    unfold windowCarrierGlobalScale
    have hnonneg : (0 : ℝ) ≤ ((N : ℝ) + 1) * P := by positivity
    linarith
  calc
    1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
    _ ≤ Real.log (windowCarrierGlobalScale N P) :=
      Real.log_le_log (Real.exp_pos 1) hbase

theorem log_windowCarrierBaseScale_le_arithmeticScale
    (N P : ℕ) (ell : ℤ) :
    Real.log (windowCarrierBaseScale P) ≤
      Real.log (windowArithmeticScale N P ell) := by
  apply Real.log_le_log
  · unfold windowCarrierBaseScale
    positivity
  · unfold windowCarrierBaseScale windowArithmeticScale
    have hprod : (0 : ℝ) ≤ (ell.natAbs : ℝ) * N * P := by positivity
    nlinarith

theorem log_windowArithmeticScale_le_global_add_carrier
    (N P : ℕ) (ell : ℤ) :
    Real.log (windowArithmeticScale N P ell) ≤
      Real.log (windowCarrierGlobalScale N P) +
        Real.log ((ell.natAbs + 1 : ℕ) : ℝ) := by
  have hfactor : (0 : ℝ) < ((ell.natAbs + 1 : ℕ) : ℝ) := by positivity
  have hglobal : 0 < windowCarrierGlobalScale N P := by
    unfold windowCarrierGlobalScale
    positivity
  have hscale : windowArithmeticScale N P ell ≤
      ((ell.natAbs + 1 : ℕ) : ℝ) * windowCarrierGlobalScale N P := by
    unfold windowArithmeticScale windowCarrierGlobalScale
    push_cast
    have ha : (0 : ℝ) ≤ (ell.natAbs : ℝ) := by positivity
    have hN : (0 : ℝ) ≤ (N : ℝ) := by positivity
    have hP : (0 : ℝ) ≤ (P : ℝ) := by positivity
    have he : 0 < Real.exp 1 := Real.exp_pos 1
    nlinarith [mul_nonneg ha he.le,
      mul_nonneg (add_nonneg ha hN) hP]
  calc
    Real.log (windowArithmeticScale N P ell) ≤
        Real.log (((ell.natAbs + 1 : ℕ) : ℝ) *
          windowCarrierGlobalScale N P) := by
      apply Real.log_le_log
      · unfold windowArithmeticScale
        positivity
      · exact hscale
    _ = Real.log (windowCarrierGlobalScale N P) +
        Real.log ((ell.natAbs + 1 : ℕ) : ℝ) := by
      rw [Real.log_mul hfactor.ne' hglobal.ne']
      ring

theorem sum_bernoulliCarrierMajorant_le (s : Finset ℤ) :
    (∑ ell ∈ s, bernoulliCarrierMajorant ell) ≤
      windowCarrierMassConstant := by
  exact summable_bernoulliCarrierMajorant.sum_le_tsum s
    (fun ell hell ↦ bernoulliCarrierMajorant_nonneg ell)

theorem sum_bernoulliCarrierLogMoment_le (s : Finset ℤ) :
    (∑ ell ∈ s, bernoulliCarrierMajorant ell *
        Real.log ((ell.natAbs + 1 : ℕ) : ℝ)) ≤
      windowCarrierLogMomentConstant := by
  exact summable_bernoulliCarrierLogMoment.sum_le_tsum s
    (fun ell hell ↦ mul_nonneg (bernoulliCarrierMajorant_nonneg ell)
      (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ ell.natAbs + 1))))

/-- Total constant used in the carrier aggregation. -/
def windowCarrierAggregationConstant : ℝ :=
  windowCarrierMassConstant + windowCarrierLogMomentConstant

theorem one_le_windowCarrierMassConstant : 1 ≤ windowCarrierMassConstant := by
  have hterm := summable_bernoulliCarrierMajorant.le_tsum (0 : ℤ)
    (fun ell hell ↦ bernoulliCarrierMajorant_nonneg ell)
  simpa [bernoulliCarrierMajorant, windowCarrierMassConstant] using! hterm

theorem windowCarrierAggregationConstant_pos :
    0 < windowCarrierAggregationConstant := by
  unfold windowCarrierAggregationConstant
  have := one_le_windowCarrierMassConstant
  have hlog := windowCarrierLogMomentConstant_nonneg
  linarith

private theorem finite_carrier_weighted_log_sum_le
    (N P J : ℕ) :
    (∑ ell ∈ Icc (-(J : ℤ)) (J : ℤ),
        ‖bernoulliMarkFourierCoefficient ell‖ *
          Real.log (windowArithmeticScale N P ell)) ≤
      windowCarrierAggregationConstant *
        Real.log (windowCarrierGlobalScale N P) := by
  let s : Finset ℤ := Icc (-(J : ℤ)) (J : ℤ)
  have hpoint : ∀ ell ∈ s,
      ‖bernoulliMarkFourierCoefficient ell‖ *
          Real.log (windowArithmeticScale N P ell) ≤
        bernoulliCarrierMajorant ell *
          Real.log (windowCarrierGlobalScale N P) +
        bernoulliCarrierMajorant ell *
          Real.log ((ell.natAbs + 1 : ℕ) : ℝ) := by
    intro ell hell
    have hcoeff := norm_bernoulliMarkFourierCoefficient_le_majorant ell
    have hlog := log_windowArithmeticScale_le_global_add_carrier N P ell
    have hlogNonneg : 0 ≤ Real.log (windowArithmeticScale N P ell) :=
      le_trans (by norm_num) (one_le_log_windowArithmeticScale N P ell)
    have hmajorNonneg := bernoulliCarrierMajorant_nonneg ell
    calc
      ‖bernoulliMarkFourierCoefficient ell‖ *
          Real.log (windowArithmeticScale N P ell) ≤
        bernoulliCarrierMajorant ell *
          Real.log (windowArithmeticScale N P ell) :=
        mul_le_mul_of_nonneg_right hcoeff hlogNonneg
      _ ≤ bernoulliCarrierMajorant ell *
          (Real.log (windowCarrierGlobalScale N P) +
            Real.log ((ell.natAbs + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog hmajorNonneg
      _ = bernoulliCarrierMajorant ell *
          Real.log (windowCarrierGlobalScale N P) +
        bernoulliCarrierMajorant ell *
          Real.log ((ell.natAbs + 1 : ℕ) : ℝ) := by ring
  have hmass := sum_bernoulliCarrierMajorant_le s
  have hmoment := sum_bernoulliCarrierLogMoment_le s
  have hglobalLog : 0 ≤ Real.log (windowCarrierGlobalScale N P) :=
    le_trans (by norm_num) (one_le_log_windowCarrierGlobalScale N P)
  calc
    (∑ ell ∈ Icc (-(J : ℤ)) (J : ℤ),
        ‖bernoulliMarkFourierCoefficient ell‖ *
          Real.log (windowArithmeticScale N P ell)) =
      ∑ ell ∈ s,
        ‖bernoulliMarkFourierCoefficient ell‖ *
          Real.log (windowArithmeticScale N P ell) := by rfl
    _ ≤ ∑ ell ∈ s,
        (bernoulliCarrierMajorant ell *
          Real.log (windowCarrierGlobalScale N P) +
        bernoulliCarrierMajorant ell *
          Real.log ((ell.natAbs + 1 : ℕ) : ℝ)) :=
      Finset.sum_le_sum hpoint
    _ = (∑ ell ∈ s, bernoulliCarrierMajorant ell) *
          Real.log (windowCarrierGlobalScale N P) +
        ∑ ell ∈ s, bernoulliCarrierMajorant ell *
          Real.log ((ell.natAbs + 1 : ℕ) : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ windowCarrierMassConstant *
          Real.log (windowCarrierGlobalScale N P) +
        windowCarrierLogMomentConstant :=
      add_le_add (mul_le_mul_of_nonneg_right hmass hglobalLog) hmoment
    _ ≤ windowCarrierAggregationConstant *
          Real.log (windowCarrierGlobalScale N P) := by
      unfold windowCarrierAggregationConstant
      have hLone := one_le_log_windowCarrierGlobalScale N P
      have hmomentNonneg := windowCarrierLogMomentConstant_nonneg
      nlinarith [mul_le_mul_of_nonneg_left hLone hmomentNonneg]

/-- Uniform finite-carrier aggregation.  The estimate is simultaneous in
both the carrier cutoff `J` and the Fourier cutoff `K`. -/
theorem uniform_finiteWindowFourierPolynomial_sublogarithmic
    {eta : ℝ} (heta : 0 < eta) :
    ∃ H : ℝ, 0 ≤ H ∧
      ∀ (N P J K : ℕ), 0 < P →
        H ≤ Real.log (windowCarrierBaseScale P) →
          ‖finiteWindowFourierPolynomial N P J K‖ ≤
            eta * Real.log (windowCarrierGlobalScale N P) := by
  let delta : ℝ := eta / windowCarrierAggregationConstant
  have hdelta : 0 < delta := div_pos heta windowCarrierAggregationConstant_pos
  rcases uniform_norm_windowModeFourierPolynomial_small_above_scale hdelta with
    ⟨H, hH, hmode⟩
  refine ⟨H, hH, ?_⟩
  intro N P J K hP hscale
  have hmodeAll : ∀ ell : ℤ,
      ‖windowModeFourierPolynomial N P K ell‖ ≤
        delta * Real.log (windowArithmeticScale N P ell) := by
    intro ell
    apply hmode N P K ell hP
    exact hscale.trans
      (log_windowCarrierBaseScale_le_arithmeticScale N P ell)
  calc
    ‖finiteWindowFourierPolynomial N P J K‖ ≤
        ∑ ell ∈ Icc (-(J : ℤ)) (J : ℤ),
          ‖bernoulliMarkFourierCoefficient ell •
            windowModeFourierPolynomial N P K ell‖ := by
      unfold finiteWindowFourierPolynomial
      exact norm_sum_le _ _
    _ = ∑ ell ∈ Icc (-(J : ℤ)) (J : ℤ),
        ‖bernoulliMarkFourierCoefficient ell‖ *
          ‖windowModeFourierPolynomial N P K ell‖ := by
      apply Finset.sum_congr rfl
      intro ell hell
      rw [norm_smul]
    _ ≤ ∑ ell ∈ Icc (-(J : ℤ)) (J : ℤ),
        ‖bernoulliMarkFourierCoefficient ell‖ *
          (delta * Real.log (windowArithmeticScale N P ell)) := by
      apply Finset.sum_le_sum
      intro ell hell
      exact mul_le_mul_of_nonneg_left (hmodeAll ell) (norm_nonneg _)
    _ = delta * (∑ ell ∈ Icc (-(J : ℤ)) (J : ℤ),
        ‖bernoulliMarkFourierCoefficient ell‖ *
          Real.log (windowArithmeticScale N P ell)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ell hell
      ring
    _ ≤ delta * (windowCarrierAggregationConstant *
          Real.log (windowCarrierGlobalScale N P)) :=
      mul_le_mul_of_nonneg_left
        (finite_carrier_weighted_log_sum_le N P J) hdelta.le
    _ = eta * Real.log (windowCarrierGlobalScale N P) := by
      dsimp [delta]
      field_simp [windowCarrierAggregationConstant_pos.ne']

/-- Squared `L²` formulation of the preceding result.  This is the uniform
`o(log²)` estimate for the actual finite carrier Fourier polynomial, with no
assumption on either cutoff `J` or `K`. -/
theorem uniform_norm_finiteWindowFourierPolynomial_sq_small_above_scale
    {eta : ℝ} (heta : 0 < eta) :
    ∃ H : ℝ, 0 ≤ H ∧
      ∀ (N P J K : ℕ), 0 < P →
        H ≤ Real.log (windowCarrierBaseScale P) →
          ‖finiteWindowFourierPolynomial N P J K‖ ^ 2 ≤
            eta * (Real.log (windowCarrierGlobalScale N P)) ^ 2 := by
  have hsqrt : 0 < Real.sqrt eta := Real.sqrt_pos.2 heta
  rcases uniform_finiteWindowFourierPolynomial_sublogarithmic hsqrt with
    ⟨H, hH, hfinite⟩
  refine ⟨H, hH, ?_⟩
  intro N P J K hP hscale
  have hlinear := hfinite N P J K hP hscale
  calc
    ‖finiteWindowFourierPolynomial N P J K‖ ^ 2 ≤
        (Real.sqrt eta * Real.log (windowCarrierGlobalScale N P)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hlinear 2
    _ = eta * (Real.log (windowCarrierGlobalScale N P)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt heta.le]

/-- Natural-denominator specialization `P = N`.  This is the usual
asymptotic formulation: after one threshold in `N`, the squared `L²` norm is
at most `eta * (log N)²`, uniformly in both finite cutoffs. -/
theorem uniform_norm_finiteWindowFourierPolynomial_sq_small_natural_scale
    {eta : ℝ} (heta : 0 < eta) :
    ∃ N₀ : ℕ, ∀ (N J K : ℕ), N₀ ≤ N →
      ‖finiteWindowFourierPolynomial N N J K‖ ^ 2 ≤
        eta * (Real.log (N : ℝ)) ^ 2 := by
  have hetaNine : 0 < eta / 9 := by positivity
  rcases uniform_norm_finiteWindowFourierPolynomial_sq_small_above_scale
    hetaNine with ⟨H, hH, hfinite⟩
  have hlogNat :
      Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ N : ℕ in atTop, H ≤ Real.log (N : ℝ) :=
    (tendsto_atTop.1 hlogNat) H
  rcases (eventually_atTop.1 hevent) with ⟨N₁, hN₁⟩
  refine ⟨max 3 N₁, ?_⟩
  intro N J K hN
  have hNthree : 3 ≤ N := (le_max_left 3 N₁).trans hN
  have hNN₁ : N₁ ≤ N := (le_max_right 3 N₁).trans hN
  have hNpos : 0 < N := by omega
  have hNRpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hlogNnonneg : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hbase : H ≤ Real.log (windowCarrierBaseScale N) := by
    exact (hN₁ N hNN₁).trans (Real.log_le_log hNRpos (by
      unfold windowCarrierBaseScale
      have he : 0 < Real.exp 1 := Real.exp_pos 1
      linarith))
  have hraw := hfinite N N J K hNpos hbase
  have hglobalScale :
      windowCarrierGlobalScale N N ≤ (N : ℝ) ^ 3 := by
    unfold windowCarrierGlobalScale
    have he : Real.exp 1 < 3 := Real.exp_one_lt_three
    have hNRthree : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNthree
    nlinarith [mul_nonneg (sub_nonneg.mpr hNRthree)
      (sq_nonneg (N : ℝ)), sq_nonneg ((N : ℝ) - 1)]
  have hglobalLog :
      Real.log (windowCarrierGlobalScale N N) ≤
        3 * Real.log (N : ℝ) := by
    calc
      Real.log (windowCarrierGlobalScale N N) ≤
          Real.log ((N : ℝ) ^ 3) := by
        apply Real.log_le_log
        · unfold windowCarrierGlobalScale
          positivity
        · exact hglobalScale
      _ = 3 * Real.log (N : ℝ) := by
        rw [Real.log_pow]
        norm_num
  have hglobalNonneg :
      0 ≤ Real.log (windowCarrierGlobalScale N N) :=
    le_trans (by norm_num) (one_le_log_windowCarrierGlobalScale N N)
  have hglobalSq :
      (Real.log (windowCarrierGlobalScale N N)) ^ 2 ≤
        (3 * Real.log (N : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hglobalNonneg hglobalLog 2
  calc
    ‖finiteWindowFourierPolynomial N N J K‖ ^ 2 ≤
        (eta / 9) *
          (Real.log (windowCarrierGlobalScale N N)) ^ 2 := hraw
    _ ≤ (eta / 9) * (3 * Real.log (N : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hglobalSq hetaNine.le
    _ = eta * (Real.log (N : ℝ)) ^ 2 := by ring

/-! ## Infinite carrier series and its exact tail -/

/-- The `ell`-th carrier summand.  This is only the algebraic summand built
from `windowModeFourierPolynomial`; no identification with the literal shot
error is part of this definition. -/
def windowCarrierTerm (N P K : ℕ) (ell : ℤ) : UnitCircleL2 :=
  bernoulliMarkFourierCoefficient ell •
    windowModeFourierPolynomial N P K ell

/-- The full carrier series in circle `L²`.  Its summability in the
asymptotic range is proved below. -/
def infiniteWindowFourierSeries (N P K : ℕ) : UnitCircleL2 :=
  ∑' ell : ℤ, windowCarrierTerm N P K ell

private theorem summable_windowCarrierScalarMajorant (N P : ℕ) :
    Summable fun ell : ℤ ↦
      bernoulliCarrierMajorant ell *
        (Real.log (windowCarrierGlobalScale N P) +
          Real.log ((ell.natAbs + 1 : ℕ) : ℝ)) := by
  simpa only [mul_add] using!
    (summable_bernoulliCarrierMajorant.mul_right
      (Real.log (windowCarrierGlobalScale N P))).add
      summable_bernoulliCarrierLogMoment

/-- Absolute carrier summability follows from a unit-strength bound for
every individual carrier mode. -/
theorem summable_norm_windowCarrierTerm_of_mode_bound
    (N P K : ℕ)
    (hmode : ∀ ell : ℤ,
      ‖windowModeFourierPolynomial N P K ell‖ ≤
        Real.log (windowArithmeticScale N P ell)) :
    Summable fun ell : ℤ ↦ ‖windowCarrierTerm N P K ell‖ := by
  apply (summable_windowCarrierScalarMajorant N P).of_nonneg_of_le
  · intro ell
    exact norm_nonneg _
  · intro ell
    have hcoeff := norm_bernoulliMarkFourierCoefficient_le_majorant ell
    have hmodeNonneg :
        0 ≤ ‖windowModeFourierPolynomial N P K ell‖ := norm_nonneg _
    have hmajorNonneg := bernoulliCarrierMajorant_nonneg ell
    unfold windowCarrierTerm
    rw [norm_smul]
    calc
      ‖bernoulliMarkFourierCoefficient ell‖ *
          ‖windowModeFourierPolynomial N P K ell‖ ≤
        bernoulliCarrierMajorant ell *
          ‖windowModeFourierPolynomial N P K ell‖ :=
        mul_le_mul_of_nonneg_right hcoeff hmodeNonneg
      _ ≤ bernoulliCarrierMajorant ell *
          Real.log (windowArithmeticScale N P ell) :=
        mul_le_mul_of_nonneg_left (hmode ell) hmajorNonneg
      _ ≤ bernoulliCarrierMajorant ell *
          (Real.log (windowCarrierGlobalScale N P) +
            Real.log ((ell.natAbs + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (log_windowArithmeticScale_le_global_add_carrier N P ell)
          hmajorNonneg

/-- There is one threshold, independent of `N`, `K`, and the carrier
cutoff, above which the full carrier family is absolutely summable. -/
theorem uniform_summable_norm_windowCarrierTerm_above_scale :
    ∃ H : ℝ, 0 ≤ H ∧
      ∀ (N P K : ℕ), 0 < P →
        H ≤ Real.log (windowCarrierBaseScale P) →
          Summable fun ell : ℤ ↦ ‖windowCarrierTerm N P K ell‖ := by
  rcases uniform_norm_windowModeFourierPolynomial_small_above_scale
    (by norm_num : (0 : ℝ) < 1) with ⟨H, hH, hmode⟩
  refine ⟨H, hH, ?_⟩
  intro N P K hP hscale
  apply summable_norm_windowCarrierTerm_of_mode_bound
  intro ell
  simpa only [one_mul] using! hmode N P K ell hP
    (hscale.trans (log_windowCarrierBaseScale_le_arithmeticScale N P ell))

/-- Absolute summability implies summability in `UnitCircleL2`. -/
theorem summable_windowCarrierTerm_of_norm
    (N P K : ℕ)
    (h : Summable fun ell : ℤ ↦ ‖windowCarrierTerm N P K ell‖) :
    Summable (windowCarrierTerm N P K) :=
  h.of_norm

/-- Symmetric carrier blocks converge to the full algebraic carrier series
whenever the norm series is summable. -/
theorem tendsto_finiteWindowFourierPolynomial_carrier
    (N P K : ℕ)
    (h : Summable fun ell : ℤ ↦ ‖windowCarrierTerm N P K ell‖) :
    Tendsto (fun J : ℕ ↦ finiteWindowFourierPolynomial N P J K) atTop
      (nhds (infiniteWindowFourierSeries N P K)) := by
  have hseries := (summable_windowCarrierTerm_of_norm N P K h).hasSum
  have hlimit := hseries.comp (Finset.tendsto_Icc_neg (R := ℤ))
  simpa only [finiteWindowFourierPolynomial, windowCarrierTerm,
    infiniteWindowFourierSeries] using! hlimit

/-- Exact complement-tail bound for a symmetric carrier block. -/
theorem norm_infiniteWindowFourierSeries_sub_finite_le_tail
    (N P J K : ℕ)
    (h : Summable fun ell : ℤ ↦ ‖windowCarrierTerm N P K ell‖) :
    ‖infiniteWindowFourierSeries N P K -
        finiteWindowFourierPolynomial N P J K‖ ≤
      ∑' ell : {ell : ℤ //
          ell ∉ Icc (-(J : ℤ)) (J : ℤ)},
        ‖windowCarrierTerm N P K ell‖ := by
  let s : Finset ℤ := Icc (-(J : ℤ)) (J : ℤ)
  have hseries : Summable (windowCarrierTerm N P K) := h.of_norm
  have hdecomp := hseries.sum_add_tsum_subtype_compl s
  have hid :
      infiniteWindowFourierSeries N P K -
          finiteWindowFourierPolynomial N P J K =
        ∑' ell : {ell : ℤ // ell ∉ s},
          windowCarrierTerm N P K ell := by
    change (∑' ell : ℤ, windowCarrierTerm N P K ell) -
        (∑ ell ∈ s, windowCarrierTerm N P K ell) =
      ∑' ell : {ell : ℤ // ell ∉ s},
        windowCarrierTerm N P K ell
    rw [← hdecomp]
    exact add_sub_cancel_left _ _
  rw [hid]
  exact norm_tsum_le_tsum_norm (h.subtype {ell : ℤ | ell ∉ s})

/-- The explicit scalar complement tail in the preceding inequality tends
to zero along symmetric carrier blocks. -/
theorem tendsto_windowCarrierNormTail_zero
    (N P K : ℕ)
    (h : Summable fun ell : ℤ ↦ ‖windowCarrierTerm N P K ell‖) :
    Tendsto
      (fun J : ℕ ↦
        ∑' ell : {ell : ℤ //
            ell ∉ Icc (-(J : ℤ)) (J : ℤ)},
          ‖windowCarrierTerm N P K ell‖)
      atTop (nhds 0) := by
  let f : ℤ → ℝ := fun ell ↦ ‖windowCarrierTerm N P K ell‖
  have hpartial :
      Tendsto (fun J : ℕ ↦ ∑ ell ∈ Icc (-(J : ℤ)) (J : ℤ), f ell)
        atTop (nhds (∑' ell : ℤ, f ell)) :=
    h.hasSum.comp (Finset.tendsto_Icc_neg (R := ℤ))
  have htailEq (J : ℕ) :
      (∑' ell : {ell : ℤ //
          ell ∉ Icc (-(J : ℤ)) (J : ℤ)}, f ell) =
        (∑' ell : ℤ, f ell) -
          ∑ ell ∈ Icc (-(J : ℤ)) (J : ℤ), f ell := by
    have hdecomp := h.sum_add_tsum_subtype_compl
      (Icc (-(J : ℤ)) (J : ℤ))
    linarith
  have hconst :
      Tendsto (fun _J : ℕ ↦ ∑' ell : ℤ, f ell) atTop
        (nhds (∑' ell : ℤ, f ell)) := tendsto_const_nhds
  have hdiff := hconst.sub hpartial
  have hdiffZero :
      Tendsto
        (fun J : ℕ ↦ (∑' ell : ℤ, f ell) -
          ∑ ell ∈ Icc (-(J : ℤ)) (J : ℤ), f ell)
        atTop (nhds 0) := by
    simpa only [sub_self] using! hdiff
  apply hdiffZero.congr'
  exact Filter.Eventually.of_forall fun J ↦ (htailEq J).symm

/-- A single asymptotic threshold gives both absolute convergence of the
carrier series and convergence of all its symmetric partial sums. -/
theorem uniform_tendsto_finiteWindowFourierPolynomial_carrier_above_scale :
    ∃ H : ℝ, 0 ≤ H ∧
      ∀ (N P K : ℕ), 0 < P →
        H ≤ Real.log (windowCarrierBaseScale P) →
          Tendsto (fun J : ℕ ↦ finiteWindowFourierPolynomial N P J K) atTop
            (nhds (infiniteWindowFourierSeries N P K)) := by
  rcases uniform_summable_norm_windowCarrierTerm_above_scale with
    ⟨H, hH, hsummable⟩
  refine ⟨H, hH, ?_⟩
  intro N P K hP hscale
  exact tendsto_finiteWindowFourierPolynomial_carrier N P K
    (hsummable N P K hP hscale)

/-- The full algebraic carrier series inherits the same uniform
sublogarithmic bound by passage to the rigorously controlled carrier limit. -/
theorem uniform_infiniteWindowFourierSeries_sublogarithmic
    {eta : ℝ} (heta : 0 < eta) :
    ∃ H : ℝ, 0 ≤ H ∧
      ∀ (N P K : ℕ), 0 < P →
        H ≤ Real.log (windowCarrierBaseScale P) →
          ‖infiniteWindowFourierSeries N P K‖ ≤
            eta * Real.log (windowCarrierGlobalScale N P) := by
  rcases uniform_finiteWindowFourierPolynomial_sublogarithmic heta with
    ⟨Hfinite, hHfinite, hfinite⟩
  rcases uniform_summable_norm_windowCarrierTerm_above_scale with
    ⟨Hsum, hHsum, hsummable⟩
  refine ⟨max Hfinite Hsum, ?_, ?_⟩
  · exact hHfinite.trans (le_max_left _ _)
  · intro N P K hP hscale
    have hscaleFinite : Hfinite ≤ Real.log (windowCarrierBaseScale P) :=
      (le_max_left _ _).trans hscale
    have hscaleSum : Hsum ≤ Real.log (windowCarrierBaseScale P) :=
      (le_max_right _ _).trans hscale
    have hconv := tendsto_finiteWindowFourierPolynomial_carrier N P K
      (hsummable N P K hP hscaleSum)
    apply le_of_tendsto hconv.norm
    exact Filter.Eventually.of_forall fun J ↦
      hfinite N P J K hP hscaleFinite

/-- Squared `L²` form of the infinite-carrier estimate. -/
theorem uniform_norm_infiniteWindowFourierSeries_sq_small_above_scale
    {eta : ℝ} (heta : 0 < eta) :
    ∃ H : ℝ, 0 ≤ H ∧
      ∀ (N P K : ℕ), 0 < P →
        H ≤ Real.log (windowCarrierBaseScale P) →
          ‖infiniteWindowFourierSeries N P K‖ ^ 2 ≤
            eta * (Real.log (windowCarrierGlobalScale N P)) ^ 2 := by
  have hsqrt : 0 < Real.sqrt eta := Real.sqrt_pos.2 heta
  rcases uniform_infiniteWindowFourierSeries_sublogarithmic hsqrt with
    ⟨H, hH, hinfinite⟩
  refine ⟨H, hH, ?_⟩
  intro N P K hP hscale
  have hlinear := hinfinite N P K hP hscale
  calc
    ‖infiniteWindowFourierSeries N P K‖ ^ 2 ≤
        (Real.sqrt eta * Real.log (windowCarrierGlobalScale N P)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hlinear 2
    _ = eta * (Real.log (windowCarrierGlobalScale N P)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt heta.le]

end

end Erdos1002
