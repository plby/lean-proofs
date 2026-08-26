/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Boundary-average maximal moments for the endpoint estimates in Erdős 521.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.ComplexMaximal
import ErdosProblems.Erdos521.PolynomialDisk

namespace Erdos521

open MeasureTheory Filter
open scoped BigOperators

theorem maximumSquaredComplexPowerSum_joint_continuous (n : ℕ) :
    Continuous (fun p : ℂ × (ℕ → ℝ) ↦ maximumSquaredComplexPowerSum n p.1 p.2) := by
  apply Continuous.finset_sup'_apply
  intro k _
  unfold complexPowerSum
  fun_prop

theorem norm_circleMap_le (c : ℂ) (R θ : ℝ) :
    ‖circleMap c R θ‖ ≤ ‖c‖ + |R| := by
  calc
    ‖circleMap c R θ‖ = ‖c + circleMap 0 R θ‖ := by simp [circleMap]
    _ ≤ ‖c‖ + ‖circleMap 0 R θ‖ := norm_add_le _ _
    _ = _ := by rw [norm_circleMap_zero]

theorem geometricVariance_mono_base {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (N : ℕ) :
    geometricVariance x N ≤ geometricVariance y N := by
  exact Finset.sum_le_sum (fun i _ ↦ pow_le_pow_left₀ hx hxy (2 * i))

theorem circular_maximum_joint_continuous (n : ℕ) (c : ℂ) (R : ℝ) :
    Continuous (fun p : ℝ × (ℕ → ℝ) ↦
      maximumSquaredComplexPowerSum n (circleMap c R p.1) p.2) := by
  apply Continuous.finset_sup'_apply
  intro k _
  unfold complexPowerSum
  fun_prop

theorem circular_maximum_integral_bound (n : ℕ) (c : ℂ) (R θ : ℝ) :
    (∫ ε, maximumSquaredComplexPowerSum n (circleMap c R θ) ε ∂sequenceLaw) ≤
      geometricVariance (‖c‖ + |R|) (n + 1) * (1 + Real.log (n + 1)) := by
  apply (integral_maximumSquaredComplexPowerSum_le n _).trans
  apply mul_le_mul_of_nonneg_right
    (geometricVariance_mono_base (norm_nonneg _) (norm_circleMap_le c R θ) (n + 1))
  have hlog : 0 ≤ Real.log (n + 1) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  linarith

theorem integrable_product_of_uniform_norm_bound {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasure μ] [SFinite ν] {f : α × β → ℝ} (hf : StronglyMeasurable f)
    (hsection : ∀ x, Integrable (fun y ↦ f (x, y)) ν) (C : ℝ)
    (hbound : ∀ x, (∫ y, ‖f (x, y)‖ ∂ν) ≤ C) : Integrable f (μ.prod ν) := by
  rw [integrable_prod_iff hf.aestronglyMeasurable]
  refine ⟨Eventually.of_forall hsection, ?_⟩
  apply Integrable.mono' (integrable_const C)
    hf.norm.integral_prod_right'.aestronglyMeasurable
  exact Eventually.of_forall fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
    exact hbound x

theorem circular_maximum_product_integrable (n : ℕ) (c : ℂ) (R : ℝ) :
    Integrable (fun p : ℝ × (ℕ → ℝ) ↦
      maximumSquaredComplexPowerSum n (circleMap c R p.1) p.2)
      ((volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod sequenceLaw) := by
  have : IsFiniteMeasure (volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
    constructor
    simp [Set.uIoc_of_le Real.two_pi_pos.le]
    finiteness
  have hcont := circular_maximum_joint_continuous n c R
  apply integrable_product_of_uniform_norm_bound
    (volume.restrict (Set.uIoc 0 (2 * Real.pi))) sequenceLaw hcont.stronglyMeasurable
    (fun θ ↦ maximumSquaredComplexPowerSum_integrable n (circleMap c R θ))
    (geometricVariance (‖c‖ + |R|) (n + 1) * (1 + Real.log (n + 1)))
  intro θ
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (maximumSquaredComplexPowerSum_nonneg n _ _)]
  exact circular_maximum_integral_bound n c R θ

theorem integral_circleAverage_maximum_le (n : ℕ) (c : ℂ) (R : ℝ) :
    (∫ ε, Real.circleAverage (fun z ↦ maximumSquaredComplexPowerSum n z ε) c R ∂sequenceLaw) ≤
      geometricVariance (‖c‖ + |R|) (n + 1) * (1 + Real.log (n + 1)) := by
  simp only [Real.circleAverage, smul_eq_mul, integral_const_mul]
  rw [← intervalIntegral_integral_swap (circular_maximum_product_integrable n c R)]
  have hint : IntervalIntegrable (fun θ ↦
      ∫ ε, maximumSquaredComplexPowerSum n (circleMap c R θ) ε ∂sequenceLaw)
      volume 0 (2 * Real.pi) := by
    exact intervalIntegrable_iff.mpr (circular_maximum_product_integrable n c R).integral_prod_left
  have hbound := intervalIntegral.integral_mono_on Real.two_pi_pos.le hint intervalIntegrable_const
    (fun θ _ ↦ circular_maximum_integral_bound n c R θ)
  have hmul := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr Real.two_pi_pos.le)
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ Real.two_pi_pos.ne', one_mul] using hmul

/-- The largest squared polynomial value is averaged over one fixed circle. -/
noncomputable def circularMaximum (n : ℕ) (c : ℂ) (R : ℝ) (ε : ℕ → ℝ) : ℝ :=
  Real.circleAverage (fun z ↦ maximumSquaredComplexPowerSum n z ε) c R

theorem circularMaximum_integrable (n : ℕ) (c : ℂ) (R : ℝ) :
    Integrable (circularMaximum n c R) sequenceLaw := by
  change Integrable (fun ε ↦ (2 * Real.pi)⁻¹ *
    ∫ θ in 0..(2 * Real.pi), maximumSquaredComplexPowerSum n (circleMap c R θ) ε) sequenceLaw
  have h := (circular_maximum_product_integrable n c R).integral_prod_right.const_mul
    (2 * Real.pi)⁻¹
  simpa only [circularMaximum, Real.circleAverage, smul_eq_mul,
    intervalIntegral.integral_of_le Real.two_pi_pos.le, Set.uIoc_of_le Real.two_pi_pos.le] using h

theorem circularMaximum_nonneg (n : ℕ) (c : ℂ) (R : ℝ) (ε : ℕ → ℝ) :
    0 ≤ circularMaximum n c R ε := by
  exact Real.circleAverage_nonneg_of_nonneg
    (fun z _ ↦ maximumSquaredComplexPowerSum_nonneg n z ε)

theorem maximumSquaredComplexPowerSum_continuous (n : ℕ) (ε : ℕ → ℝ) :
    Continuous (fun z ↦ maximumSquaredComplexPowerSum n z ε) := by
  apply Continuous.finset_sup'_apply
  intro k _
  unfold complexPowerSum
  fun_prop

theorem circularMaximum_one_le (n : ℕ) (c : ℂ) (R : ℝ) (ε : ℕ → ℝ)
    (hε : |ε 0| = 1) : 1 ≤ circularMaximum n c R ε := by
  have h := Real.circleAverage_mono (circleIntegrable_const (1 : ℝ) c R)
    (maximumSquaredComplexPowerSum_continuous n ε).continuousOn.circleIntegrable'
    (fun z _ ↦ ?_)
  · simpa only [Real.circleAverage_const, circularMaximum] using h
  · have h₀ := Finset.le_sup' (fun k ↦ ‖complexPowerSum ε k z‖ ^ 2)
      (by simp : 0 ∈ Finset.range (n + 1))
    calc
      1 = ‖complexPowerSum ε 0 z‖ ^ 2 := by simp [complexPowerSum, hε]
      _ ≤ _ := h₀

theorem circleAverage_powerSum_sq_le (n m : ℕ) (hm : m ≤ n) (c : ℂ) (R : ℝ)
    (ε : ℕ → ℝ) :
    Real.circleAverage (fun z ↦ ‖complexPowerSum ε m z‖ ^ 2) c R ≤
      circularMaximum n c R ε := by
  have hc : Continuous (fun z ↦ ‖complexPowerSum ε m z‖ ^ 2) := by
    unfold complexPowerSum
    fun_prop
  apply Real.circleAverage_mono hc.continuousOn.circleIntegrable'
    (maximumSquaredComplexPowerSum_continuous n ε).continuousOn.circleIntegrable'
  intro z _
  exact Finset.le_sup' (fun k ↦ ‖complexPowerSum ε k z‖ ^ 2) (by simp; omega)

end Erdos521
