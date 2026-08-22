/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.ProfileSmallBall
import Mathlib.Probability.BrownianMotion.Basic

/-!
# Gaussian blocks in the HLOZ small-ball argument

Appendix Lemma A.8 of Hao--Li--Okada--Zheng uses the kernels

`b_l(x,y) = (sqrt (2*pi) * 2*l)^(-1) * exp (-(x-y)^2 / (8*l^2))`.

They are the transition densities of a Gaussian random walk whose `l`-th
increment has variance `4*l^2`; equivalently they are the transition
densities of Brownian motion across a time interval of length `4*l^2`.

This file establishes that bridge without asymptotic notation.  It also gives
an explicit lower bound for one increment to lie in a symmetric interval and
lifts that estimate to a finite independent Gaussian block.  The final
Brownian exit estimate used in A.8 (the survival probability in a two-sided
strip) is not asserted here: Mathlib currently provides Brownian
finite-dimensional laws but not that exit-time distribution.
-/

open scoped BigOperators ENNReal NNReal

namespace Erdos1165.BrownianSmallBall

noncomputable section

open MeasureTheory ProbabilityTheory Set

/-- Variance of the `l`-th Gaussian increment in HLOZ (A.11). -/
def hlozVariance (l : ℕ) : ℝ≥0 :=
  ⟨4 * (l : ℝ) ^ 2, by positivity⟩

@[simp] lemma coe_hlozVariance (l : ℕ) :
    (hlozVariance l : ℝ) = 4 * (l : ℝ) ^ 2 := rfl

lemma hlozVariance_ne_zero {l : ℕ} (hl : 0 < l) : hlozVariance l ≠ 0 := by
  intro hzero
  have hcoe : (hlozVariance l : ℝ) = 0 := by rw [hzero]; rfl
  rw [coe_hlozVariance] at hcoe
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  nlinarith

/-- The Gaussian kernel denoted by `b_l` in HLOZ (A.11), defined through
Mathlib's normalized Gaussian density. -/
def hlozKernel (l : ℕ) (x y : ℝ) : ℝ :=
  gaussianPDFReal x (hlozVariance l) y

lemma hlozKernel_nonneg (l : ℕ) (x y : ℝ) :
    0 ≤ hlozKernel l x y :=
  gaussianPDFReal_nonneg _ _ _

lemma hlozKernel_pos {l : ℕ} (hl : 0 < l) (x y : ℝ) :
    0 < hlozKernel l x y :=
  gaussianPDFReal_pos _ _ _ (hlozVariance_ne_zero hl)

/-- Exact identification of `b_l` with the formula printed in HLOZ (A.11). -/
theorem hlozKernel_eq {l : ℕ} (hl : 0 < l) (x y : ℝ) :
    hlozKernel l x y =
      (√(2 * Real.pi) * (2 * l : ℝ))⁻¹ *
        Real.exp (-((x - y) ^ 2) / (8 * (l : ℝ) ^ 2)) := by
  rw [hlozKernel, gaussianPDFReal]
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  have hsqrt : √(2 * Real.pi * (hlozVariance l : ℝ)) =
      √(2 * Real.pi) * (2 * l : ℝ) := by
    rw [coe_hlozVariance]
    calc
      √(2 * Real.pi * (4 * (l : ℝ) ^ 2)) =
          √(2 * Real.pi) * √(4 * (l : ℝ) ^ 2) := by
        rw [Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ) * Real.pi)]
      _ = √(2 * Real.pi) * (2 * l : ℝ) := by
        congr 1
        rw [show (4 : ℝ) * (l : ℝ) ^ 2 = (2 * l) ^ 2 by ring,
          Real.sqrt_sq_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 2 * l)]
  rw [hsqrt]
  congr 2
  rw [coe_hlozVariance]
  field_simp
  ring

/-- The kernel is symmetric in its two spatial arguments. -/
lemma hlozKernel_comm (l : ℕ) (x y : ℝ) :
    hlozKernel l x y = hlozKernel l y x := by
  unfold hlozKernel gaussianPDFReal
  congr 2
  ring

/-- Integrating one HLOZ transition kernel gives one. -/
lemma integral_hlozKernel_eq_one {l : ℕ} (hl : 0 < l) (x : ℝ) :
    ∫ y, hlozKernel l x y = 1 := by
  exact integral_gaussianPDFReal_eq_one x (hlozVariance_ne_zero hl)

/-! ## The HLOZ Brownian clock -/

/-- Brownian time accumulated from levels `start,...,stop-1`.  Coercing to
`ℝ`, this is exactly `4 * ∑ j in Ico start stop, j^2`. -/
def hlozClock (start stop : ℕ) : ℝ≥0 :=
  ∑ l ∈ Finset.Ico start stop, hlozVariance l

@[simp] lemma hlozClock_self (start : ℕ) : hlozClock start start = 0 := by
  simp [hlozClock]

lemma hlozClock_succ {start l : ℕ} (hstart : start ≤ l) :
    hlozClock start (l + 1) = hlozClock start l + hlozVariance l := by
  simp only [hlozClock, Finset.sum_Ico_succ_top hstart]

variable {Omega : Type*} {mOmega : MeasurableSpace Omega}
    {P : Measure Omega} {B : ℝ≥0 → Omega → ℝ}

/-- A Brownian increment across an interval of length `4*l^2` has precisely
the Gaussian law whose density is `hlozKernel l`. -/
theorem hasLaw_hlozIncrement
    (hB : IsPreBrownianReal B P) (t : ℝ≥0) (l : ℕ) :
    HasLaw (fun omega ↦ B (t + hlozVariance l) omega - B t omega)
      (gaussianReal 0 (hlozVariance l)) P := by
  change HasLaw (B (t + hlozVariance l) - B t)
    (gaussianReal 0 (hlozVariance l)) P
  convert hB.hasLaw_sub (t + hlozVariance l) t using 1
  congr 1
  apply NNReal.eq
  simp

/-- Consecutive observations of Brownian motion at the HLOZ clock therefore
have the transition law represented by `hlozKernel`. -/
theorem hasLaw_hlozClockIncrement
    (hB : IsPreBrownianReal B P) {start l : ℕ} (hstart : start ≤ l) :
    HasLaw
      (fun omega ↦ B (hlozClock start (l + 1)) omega -
        B (hlozClock start l) omega)
      (gaussianReal 0 (hlozVariance l)) P := by
  rw [hlozClock_succ hstart]
  exact hasLaw_hlozIncrement hB (hlozClock start l) l

/-- One-step pointwise lower bound.  This is the elementary estimate used
when a Gaussian block is confined by bounding each of its increments. -/
lemma hlozKernel_lower_of_abs_sub_le {l : ℕ} (hl : 0 < l)
    {x y r : ℝ} (hr : 0 ≤ r) (hxy : |x - y| ≤ r) :
    (√(2 * Real.pi) * (2 * l : ℝ))⁻¹ *
        Real.exp (-(r ^ 2) / (8 * (l : ℝ) ^ 2)) ≤
      hlozKernel l x y := by
  rw [hlozKernel_eq hl]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hsquare : (x - y) ^ 2 ≤ r ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg hr]
    exact hxy
  have hden : (0 : ℝ) < 8 * (l : ℝ) ^ 2 := by positivity
  exact (div_le_div_iff_of_pos_right hden).mpr (neg_le_neg hsquare)

/-- Explicit lower bound on the mass of one centered Gaussian increment in
`[-r,r]`. -/
theorem gaussianIncrement_Icc_lower {l : ℕ} (hl : 0 < l) {r : ℝ}
    (hr : 0 ≤ r) :
    ENNReal.ofReal
        ((2 * r) * ((√(2 * Real.pi) * (2 * l : ℝ))⁻¹ *
          Real.exp (-(r ^ 2) / (8 * (l : ℝ) ^ 2)))) ≤
      gaussianReal 0 (hlozVariance l) (Icc (-r) r) := by
  rw [gaussianReal_apply_eq_integral 0 (hlozVariance_ne_zero hl)]
  apply ENNReal.ofReal_le_ofReal
  have hconst : IntegrableOn
      (fun _ : ℝ ↦
        (√(2 * Real.pi) * (2 * l : ℝ))⁻¹ *
          Real.exp (-(r ^ 2) / (8 * (l : ℝ) ^ 2))) (Icc (-r) r) := by
    exact integrableOn_const (by simp : volume (Icc (-r) r) ≠ ∞)
  have hpdf : IntegrableOn (gaussianPDFReal 0 (hlozVariance l)) (Icc (-r) r) :=
    (integrable_gaussianPDFReal _ _).integrableOn
  calc
    (2 * r) * ((√(2 * Real.pi) * (2 * l : ℝ))⁻¹ *
          Real.exp (-(r ^ 2) / (8 * (l : ℝ) ^ 2))) =
        ∫ _y in Icc (-r) r,
          ((√(2 * Real.pi) * (2 * l : ℝ))⁻¹ *
            Real.exp (-(r ^ 2) / (8 * (l : ℝ) ^ 2))) := by
      rw [setIntegral_const]
      simp only [smul_eq_mul]
      congr 1
      rw [measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith : 0 ≤ r - -r)]
      ring
    _ ≤ ∫ y in Icc (-r) r, gaussianPDFReal 0 (hlozVariance l) y := by
      refine setIntegral_mono_on hconst hpdf measurableSet_Icc ?_
      intro y hy
      apply hlozKernel_lower_of_abs_sub_le hl hr
      simpa only [zero_sub, abs_neg] using (abs_le.mpr hy)

/-! ## A finite independent Gaussian block -/

/-- Product law of independent centered HLOZ Gaussian increments. -/
def gaussianBlockMeasure {N : ℕ} (level : Fin N → ℕ) :
    Measure (Fin N → ℝ) :=
  Measure.pi fun i ↦ gaussianReal 0 (hlozVariance (level i))

/-- The box in which every increment has absolute value at most its assigned
radius. -/
def incrementBox {N : ℕ} (radius : Fin N → ℝ) : Set (Fin N → ℝ) :=
  Set.pi Set.univ fun i ↦ Icc (-(radius i)) (radius i)

lemma measurableSet_incrementBox {N : ℕ} (radius : Fin N → ℝ) :
    MeasurableSet (incrementBox radius) := by
  exact MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc

/-- Exact factorization of the finite Gaussian increment box. -/
theorem gaussianBlockMeasure_incrementBox {N : ℕ} (level : Fin N → ℕ)
    (radius : Fin N → ℝ) :
    gaussianBlockMeasure level (incrementBox radius) =
      ∏ i, gaussianReal 0 (hlozVariance (level i))
        (Icc (-(radius i)) (radius i)) := by
  rw [gaussianBlockMeasure, incrementBox, Measure.pi_pi]

/-- A checked direct finite Gaussian-block lower bound.  Unlike the sharper
Brownian strip argument in HLOZ, this confines the increments separately;
it is nevertheless a fully explicit small-ball estimate for every finite
block. -/
theorem gaussianBlockMeasure_incrementBox_lower {N : ℕ}
    (level : Fin N → ℕ) (radius : Fin N → ℝ)
    (hlevel : ∀ i, 0 < level i) (hradius : ∀ i, 0 ≤ radius i) :
    ∏ i, ENNReal.ofReal
        ((2 * radius i) *
          ((√(2 * Real.pi) * (2 * level i : ℝ))⁻¹ *
            Real.exp (-((radius i) ^ 2) / (8 * (level i : ℝ) ^ 2)))) ≤
      gaussianBlockMeasure level (incrementBox radius) := by
  rw [gaussianBlockMeasure_incrementBox]
  exact Finset.prod_le_prod (fun _ _ ↦ bot_le) fun i _ ↦
    gaussianIncrement_Icc_lower (hlevel i) (hradius i)

/-- Deterministic triangle-inequality companion to the increment-box bound:
if every increment is in its interval, every partial sum is bounded by the
sum of the corresponding radii. -/
theorem abs_partialSum_le_of_mem_incrementBox {N : ℕ}
    {radius : Fin N → ℝ} {z : Fin N → ℝ}
    (hz : z ∈ incrementBox radius) (k : ℕ) :
    |∑ i ∈ Finset.univ.filter (fun i : Fin N ↦ (i : ℕ) < k), z i| ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin N ↦ (i : ℕ) < k), radius i := by
  calc
    |∑ i ∈ Finset.univ.filter (fun i : Fin N ↦ (i : ℕ) < k), z i| ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin N ↦ (i : ℕ) < k), |z i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin N ↦ (i : ℕ) < k), radius i := by
      apply Finset.sum_le_sum
      intro i hi
      have hiBox := hz i (Set.mem_univ i)
      rw [mem_Icc] at hiBox
      exact abs_le.mpr hiBox

end

end Erdos1165.BrownianSmallBall
