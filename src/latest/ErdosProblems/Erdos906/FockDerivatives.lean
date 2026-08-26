module

public import ErdosProblems.Erdos906.FockSeries
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Iterated derivatives of the beta = 1/2 Fock series

This file gives the exact coefficient formula for every iterated derivative of a bounded-coefficient
Fock series. It also records summability, entire analyticity, and measurability in the coefficient
sequence.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace CofiniteDerivatives

noncomputable section

/-- The coefficient of degree `m` in the `n`-th derivative of a Fock series. -/
def fockIteratedCoefficient (ξ : ℕ → ℂ) (n m : ℕ) : ℂ :=
  ξ (n + m) * Real.sqrt ((n + m).factorial : ℝ) / (m.factorial : ℂ)

/-- The formal power series of the `n`-th derivative of a Fock series. -/
def fockIteratedPowerSeries (ξ : ℕ → ℂ) (n : ℕ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fockIteratedCoefficient ξ n)

private theorem fockIteratedCoefficient_zero (ξ : ℕ → ℂ) (m : ℕ) :
    fockIteratedCoefficient ξ 0 m = fockCoefficient ξ m := by
  have hden : (Real.sqrt (m.factorial : ℝ) : ℂ) * Real.sqrt (m.factorial : ℝ) =
      (m.factorial : ℕ) := by
    norm_cast
    exact Real.mul_self_sqrt (by positivity)
  have hfac : (m.factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr m.factorial_ne_zero
  have hsqrt : (Real.sqrt (m.factorial : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
  rw [fockIteratedCoefficient, fockCoefficient, fockDenominator]
  simp only [zero_add]
  field_simp [hfac, hsqrt]
  rw [pow_two, hden]

private theorem fockIteratedCoefficient_succ (ξ : ℕ → ℂ) (n m : ℕ) :
    (m + 1) * fockIteratedCoefficient ξ n (m + 1) =
      fockIteratedCoefficient ξ (n + 1) m := by
  have hi : n + (m + 1) = n + 1 + m := by omega
  rw [fockIteratedCoefficient, fockIteratedCoefficient, hi, Nat.factorial_succ]
  push_cast
  field_simp

private theorem fockIteratedPowerSeries_zero (ξ : ℕ → ℂ) :
    fockIteratedPowerSeries ξ 0 = fockPowerSeries ξ := by
  ext m
  simp [fockIteratedPowerSeries, fockPowerSeries, fockIteratedCoefficient_zero]

private theorem fock_iterated_derivSeries_eq (ξ : ℕ → ℂ) (n : ℕ) :
    (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries
        (fockIteratedPowerSeries ξ n).derivSeries =
      fockIteratedPowerSeries ξ (n + 1) := by
  change (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries
      (FormalMultilinearSeries.ofScalars ℂ (fockIteratedCoefficient ξ n)).derivSeries =
    FormalMultilinearSeries.ofScalars ℂ (fockIteratedCoefficient ξ (n + 1))
  apply funext
  intro m
  rw [← FormalMultilinearSeries.mkPiRing_coeff_eq
      ((ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries
        (FormalMultilinearSeries.ofScalars ℂ
          (fockIteratedCoefficient ξ n)).derivSeries) m,
    ← FormalMultilinearSeries.mkPiRing_coeff_eq
      (FormalMultilinearSeries.ofScalars ℂ
        (fockIteratedCoefficient ξ (n + 1))) m]
  congr 1
  rw [FormalMultilinearSeries.coeff_ofScalars]
  change ((FormalMultilinearSeries.ofScalars ℂ
    (fockIteratedCoefficient ξ n)).derivSeries.coeff m) 1 =
    fockIteratedCoefficient ξ (n + 1) m
  rw [FormalMultilinearSeries.derivSeries_coeff_one]
  simpa [nsmul_eq_mul] using!
    fockIteratedCoefficient_succ ξ n m

/-- The exact formal power series of every iterated derivative, valid on all of `ℂ`. -/
theorem hasFPowerSeriesOnBall_iteratedDeriv_fockFunction
    (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1) (n : ℕ) :
    HasFPowerSeriesOnBall (iteratedDeriv n (fockFunction ξ))
      (fockIteratedPowerSeries ξ n) 0 ⊤ := by
  induction n with
  | zero =>
      rw [iteratedDeriv_zero, fockIteratedPowerSeries_zero]
      exact hasFPowerSeriesOnBall_fockFunction ξ hξ
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have h := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).comp_hasFPowerSeriesOnBall ih.fderiv
      rw [fock_iterated_derivSeries_eq ξ n] at h
      apply h.congr
      intro z _
      exact fderiv_apply_one_eq_deriv

/-- The exact all-orders derivative formula in the Fock factorial normalization. -/
theorem iteratedDeriv_fockFunction_eq_tsum
    (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1) (n : ℕ) (z : ℂ) :
    iteratedDeriv n (fockFunction ξ) z =
      ∑' m : ℕ, ξ (n + m) * Real.sqrt ((n + m).factorial : ℝ) /
        (m.factorial : ℂ) * z ^ m := by
  have h := hasFPowerSeriesOnBall_iteratedDeriv_fockFunction ξ hξ n
  calc
    iteratedDeriv n (fockFunction ξ) z = (fockIteratedPowerSeries ξ n).sum z := by
      simpa using! h.sum (by simp)
    _ = ∑' m : ℕ, ξ (n + m) * Real.sqrt ((n + m).factorial : ℝ) /
        (m.factorial : ℂ) * z ^ m := by
      rw [FormalMultilinearSeries.sum]
      apply tsum_congr
      intro m
      simp [fockIteratedPowerSeries, fockIteratedCoefficient, mul_comm]

/-- The series in the exact all-orders derivative formula is summable at every point. -/
theorem summable_fockIteratedSeries
    (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1) (n : ℕ) (z : ℂ) :
    Summable fun m : ℕ => ξ (n + m) * Real.sqrt ((n + m).factorial : ℝ) /
      (m.factorial : ℂ) * z ^ m := by
  have h := (hasFPowerSeriesOnBall_iteratedDeriv_fockFunction ξ hξ n).hasSum
    (show z ∈ Metric.eball (0 : ℂ) (⊤ : ℝ≥0∞) by simp)
  simpa [fockIteratedPowerSeries, fockIteratedCoefficient,
    FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using! h.summable

/-- Every iterated derivative of a bounded-coefficient Fock series is entire. -/
theorem analyticOnNhd_iteratedDeriv_fockFunction
    (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1) (n : ℕ) :
    AnalyticOnNhd ℂ (iteratedDeriv n (fockFunction ξ)) Set.univ := by
  intro z _
  exact (hasFPowerSeriesOnBall_iteratedDeriv_fockFunction ξ hξ n).analyticAt_of_mem (by simp)

/-- Coefficient sequences in the closed unit disk, with the measurable structure inherited from
the full product space `ℕ → ℂ`. -/
abbrev BoundedFockCoefficients := {ξ : ℕ → ℂ // ∀ k, ‖ξ k‖ ≤ 1}

/-- Evaluation of an iterated Fock derivative is measurable in a bounded coefficient sequence. -/
theorem measurable_iteratedDeriv_fockFunction (n : ℕ) (z : ℂ) :
    Measurable (fun ξ : BoundedFockCoefficients =>
      iteratedDeriv n (fockFunction ξ.1) z) := by
  let partialSum : ℕ → BoundedFockCoefficients → ℂ := fun N ξ =>
    ∑ m ∈ Finset.range N,
      ξ.1 (n + m) * Real.sqrt ((n + m).factorial : ℝ) /
        (m.factorial : ℂ) * z ^ m
  have hpartial : ∀ N, Measurable (partialSum N) := by
    intro N
    dsimp [partialSum]
    refine Finset.measurable_fun_sum (Finset.range N) fun m _ => ?_
    have hcoord : Measurable (fun ξ : BoundedFockCoefficients => ξ.1 (n + m)) :=
      (measurable_pi_apply (X := fun _ : ℕ => ℂ) (n + m)).comp measurable_subtype_coe
    simpa only [div_eq_mul_inv, mul_assoc] using!
      hcoord.mul_const ((Real.sqrt ((n + m).factorial : ℝ) : ℂ) /
        (m.factorial : ℂ) * z ^ m)
  apply measurable_of_tendsto_metrizable hpartial
  rw [tendsto_pi_nhds]
  intro ξ
  rw [iteratedDeriv_fockFunction_eq_tsum ξ.1 ξ.2 n z]
  exact (summable_fockIteratedSeries ξ.1 ξ.2 n z).hasSum.tendsto_sum_nat

/-- Evaluation of an iterated Fock derivative is almost everywhere measurable for every measure
on the bounded coefficient space. -/
theorem aemeasurable_iteratedDeriv_fockFunction_bounded
    (n : ℕ) (z : ℂ) (μ : Measure BoundedFockCoefficients) :
    AEMeasurable (fun ξ : BoundedFockCoefficients =>
      iteratedDeriv n (fockFunction ξ.1) z) μ :=
  (measurable_iteratedDeriv_fockFunction n z).aemeasurable

/-- Under any measure supported on bounded coefficient sequences, evaluation of the `n`-th Fock
derivative at `z` is almost everywhere measurable in the coefficient sequence. -/
theorem aemeasurable_iteratedDeriv_fockFunction
    (n : ℕ) (z : ℂ) (μ : Measure (ℕ → ℂ))
    (hμ : ∀ᵐ ξ ∂μ, ∀ k, ‖ξ k‖ ≤ 1) :
    AEMeasurable (fun ξ : ℕ → ℂ => iteratedDeriv n (fockFunction ξ) z) μ := by
  let partialSum : ℕ → (ℕ → ℂ) → ℂ := fun N ξ =>
    ∑ m ∈ Finset.range N,
      ξ (n + m) * Real.sqrt ((n + m).factorial : ℝ) /
        (m.factorial : ℂ) * z ^ m
  have hpartial : ∀ N, Measurable (partialSum N) := by
    intro N
    dsimp [partialSum]
    measurability
  apply aemeasurable_of_tendsto_metrizable_ae atTop
    (fun N => (hpartial N).aemeasurable)
  filter_upwards [hμ] with ξ hξ
  rw [iteratedDeriv_fockFunction_eq_tsum ξ hξ n z]
  exact (summable_fockIteratedSeries ξ hξ n z).hasSum.tendsto_sum_nat

end

end CofiniteDerivatives
