import Mathlib

/-!
# Gaussian tail estimates for Erdős Problem 228

This file packages the one-dimensional Chernoff estimate supplied by
Mathlib's sub-Gaussian MGF API and applies it to a finite product of centred
standard Gaussians.  The final estimates are stated both with the sharp
sub-Gaussian exponent `1 / 2` and with the weaker denominator `16` used in
the Lovett--Meka constraint budget.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal

namespace Erdos228.GaussianTail

/-! ## Abstract one-dimensional estimates -/

/-- The union-bound form of the two-sided sub-Gaussian Chernoff estimate. -/
theorem measureReal_abs_ge_le_of_hasSubgaussianMGF
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {X : Omega → ℝ} {variance : ℝ≥0}
    (hX : HasSubgaussianMGF X variance mu) {threshold : ℝ}
    (hthreshold : 0 ≤ threshold) :
    mu.real {omega | threshold ≤ |X omega|} ≤
      2 * exp (-threshold ^ 2 / (2 * variance)) := by
  have hset : {omega | threshold ≤ |X omega|} =
      {omega | threshold ≤ X omega} ∪ {omega | threshold ≤ -X omega} := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro h
      by_cases hnonneg : 0 ≤ X omega
      · exact Or.inl (by simpa [abs_of_nonneg hnonneg] using h)
      · exact Or.inr (by simpa [abs_of_nonpos (le_of_not_ge hnonneg)] using h)
    · rintro (h | h)
      · exact h.trans (le_abs_self (X omega))
      · exact h.trans (neg_le_abs (X omega))
  rw [hset]
  calc
    mu.real ({omega | threshold ≤ X omega} ∪
        {omega | threshold ≤ -X omega}) ≤
        mu.real {omega | threshold ≤ X omega} +
          mu.real {omega | threshold ≤ -X omega} :=
      measureReal_union_le _ _
    _ ≤ exp (-threshold ^ 2 / (2 * variance)) +
          exp (-threshold ^ 2 / (2 * variance)) :=
      add_le_add (hX.measure_ge_le hthreshold)
        (hX.neg.measure_ge_le hthreshold)
    _ = 2 * exp (-threshold ^ 2 / (2 * variance)) := by ring

/-- A normalized one-sided tail estimate for a positive variance proxy. -/
theorem measureReal_ge_mul_sqrt_le
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {X : Omega → ℝ} {variance : ℝ≥0}
    (hX : HasSubgaussianMGF X variance mu) (hvariance : 0 < variance)
    {c : ℝ} (hc : 0 ≤ c) :
    mu.real {omega | c * sqrt variance ≤ X omega} ≤ exp (-c ^ 2 / 2) := by
  have hvreal : (0 : ℝ) < variance := by exact_mod_cast hvariance
  have hsqrt : 0 ≤ c * sqrt variance :=
    mul_nonneg hc (sqrt_nonneg _)
  calc
    mu.real {omega | c * sqrt variance ≤ X omega} ≤
        exp (-(c * sqrt variance) ^ 2 / (2 * variance)) :=
      hX.measure_ge_le hsqrt
    _ = exp (-c ^ 2 / 2) := by
      congr 1
      rw [mul_pow, sq_sqrt (le_of_lt hvreal)]
      field_simp

/-- The normalized two-sided sub-Gaussian tail estimate. -/
theorem measureReal_abs_ge_mul_sqrt_le
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {X : Omega → ℝ} {variance : ℝ≥0}
    (hX : HasSubgaussianMGF X variance mu) (hvariance : 0 < variance)
    {c : ℝ} (hc : 0 ≤ c) :
    mu.real {omega | c * sqrt variance ≤ |X omega|} ≤
      2 * exp (-c ^ 2 / 2) := by
  have hvreal : (0 : ℝ) < variance := by exact_mod_cast hvariance
  have hsqrt : 0 ≤ c * sqrt variance :=
    mul_nonneg hc (sqrt_nonneg _)
  calc
    mu.real {omega | c * sqrt variance ≤ |X omega|} ≤
        2 * exp (-(c * sqrt variance) ^ 2 / (2 * variance)) :=
      measureReal_abs_ge_le_of_hasSubgaussianMGF hX hsqrt
    _ = 2 * exp (-c ^ 2 / 2) := by
      congr 2
      rw [mul_pow, sq_sqrt (le_of_lt hvreal)]
      field_simp

/-- Lovett--Meka uses the deliberately weaker denominator `16` in its
constraint budget.  The sharp normalized estimate immediately implies it. -/
theorem measureReal_ge_mul_sqrt_le_exp_sixteen
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {X : Omega → ℝ} {variance : ℝ≥0}
    (hX : HasSubgaussianMGF X variance mu) (hvariance : 0 < variance)
    {c : ℝ} (hc : 0 ≤ c) :
    mu.real {omega | c * sqrt variance ≤ X omega} ≤ exp (-c ^ 2 / 16) := by
  refine (measureReal_ge_mul_sqrt_le hX hvariance hc).trans ?_
  exact exp_le_exp.mpr (by nlinarith [sq_nonneg c])

/-- Two-sided version of the weakened Lovett--Meka exponent. -/
theorem measureReal_abs_ge_mul_sqrt_le_exp_sixteen
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {X : Omega → ℝ} {variance : ℝ≥0}
    (hX : HasSubgaussianMGF X variance mu) (hvariance : 0 < variance)
    {c : ℝ} (hc : 0 ≤ c) :
    mu.real {omega | c * sqrt variance ≤ |X omega|} ≤
      2 * exp (-c ^ 2 / 16) := by
  refine (measureReal_abs_ge_mul_sqrt_le hX hvariance hc).trans ?_
  apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num)
  nlinarith [sq_nonneg c]

/-! ## Centred Gaussians and finite Gaussian vectors -/

/-- The identity random variable under a centred real Gaussian distribution
has variance proxy equal to the distribution's variance. -/
theorem hasSubgaussianMGF_id_gaussianReal (variance : ℝ≥0) :
    HasSubgaussianMGF id variance (gaussianReal 0 variance) where
  integrable_exp_mul t := by
    simpa [id_eq] using
      (integrable_exp_mul_gaussianReal (μ := 0) (v := variance) t)
  mgf_le t := by
    rw [mgf_id_gaussianReal]
    simp

/-- The sharp normalized two-sided tail of a nondegenerate centred Gaussian. -/
theorem gaussianReal_measureReal_abs_ge_mul_sqrt_le
    (variance : ℝ≥0) (hvariance : 0 < variance) {c : ℝ} (hc : 0 ≤ c) :
    (gaussianReal 0 variance).real {x | c * sqrt variance ≤ |x|} ≤
      2 * exp (-c ^ 2 / 2) := by
  exact measureReal_abs_ge_mul_sqrt_le
    (hasSubgaussianMGF_id_gaussianReal variance) hvariance hc

/-- Standard Gaussian coordinates indexed by a finite type. -/
noncomputable def standardGaussianProduct (iota : Type*) [Fintype iota] :
    Measure (iota → ℝ) :=
  Measure.pi fun _ : iota ↦ gaussianReal 0 1

noncomputable instance instIsProbabilityMeasureStandardGaussianProduct
    (iota : Type*) [Fintype iota] :
    IsProbabilityMeasure (standardGaussianProduct iota) := by
  unfold standardGaussianProduct
  infer_instance

/-- Coordinate projections of the standard Gaussian product are independent. -/
theorem iIndepFun_standardGaussianProduct
    (iota : Type*) [Fintype iota] :
    iIndepFun (fun i : iota ↦ fun omega : iota → ℝ ↦ omega i)
      (standardGaussianProduct iota) := by
  unfold standardGaussianProduct
  exact iIndepFun_pi fun _ ↦ measurable_id.aemeasurable

/-- A coordinate of the standard Gaussian product is one-sub-Gaussian. -/
theorem hasSubgaussianMGF_standardGaussianCoord
    (iota : Type*) [Fintype iota] (i : iota) :
    HasSubgaussianMGF (fun omega : iota → ℝ ↦ omega i) 1
      (standardGaussianProduct iota) := by
  refine HasSubgaussianMGF.of_map (μ := standardGaussianProduct iota) (X := id)
    (Y := fun omega : iota → ℝ ↦ omega i)
    (measurable_pi_apply i).aemeasurable ?_
  have hmap : (standardGaussianProduct iota).map
      (fun omega : iota → ℝ ↦ omega i) = gaussianReal 0 1 := by
    unfold standardGaussianProduct
    exact (measurePreserving_eval
      (μ := fun _ : iota ↦ gaussianReal 0 1) i).map_eq
  rw [hmap]
  exact hasSubgaussianMGF_id_gaussianReal 1

/-- The variance proxy used for a weighted standard-Gaussian linear form.
The apparently redundant multiplication by one matches the output of
`HasSubgaussianMGF.const_mul` definitionally and avoids rewriting dependent
proof fields in `NNReal`. -/
noncomputable def gaussianVarianceProxy
    {iota : Type*} [Fintype iota] (a : iota → ℝ) : ℝ≥0 :=
  ∑ i, ⟨a i ^ 2, sq_nonneg (a i)⟩ * 1

theorem coe_gaussianVarianceProxy
    {iota : Type*} [Fintype iota] (a : iota → ℝ) :
    (gaussianVarianceProxy a : ℝ) = ∑ i, a i ^ 2 := by
  rw [gaussianVarianceProxy, NNReal.coe_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change a i ^ 2 * 1 = a i ^ 2
  ring

/-- A finite weighted standard-Gaussian sum is sub-Gaussian with variance
proxy `∑ i, a i ^ 2`. -/
theorem hasSubgaussianMGF_weightedStandardGaussianSum
    (iota : Type*) [Fintype iota] (a : iota → ℝ) :
    HasSubgaussianMGF
      (fun omega : iota → ℝ ↦ ∑ i, a i * omega i)
      (gaussianVarianceProxy a) (standardGaussianProduct iota) := by
  apply HasSubgaussianMGF.sum_of_iIndepFun
    ((iIndepFun_standardGaussianProduct iota).comp
      (fun i x ↦ a i * x) (fun i ↦ measurable_const.mul measurable_id))
    (s := Finset.univ)
  intro i hi
  exact (hasSubgaussianMGF_standardGaussianCoord iota i).const_mul (a i)

/-- Sharp normalized two-sided tail for a nonzero finite-dimensional Gaussian
linear form. -/
theorem weightedStandardGaussianSum_abs_tail
    (iota : Type*) [Fintype iota] (a : iota → ℝ)
    (hvariance : 0 < gaussianVarianceProxy a) {c : ℝ} (hc : 0 ≤ c) :
    (standardGaussianProduct iota).real
        {omega | c * sqrt (gaussianVarianceProxy a) ≤
          |∑ i, a i * omega i|} ≤
      2 * exp (-c ^ 2 / 2) := by
  exact measureReal_abs_ge_mul_sqrt_le
    (hasSubgaussianMGF_weightedStandardGaussianSum iota a) hvariance hc

/-- The finite-dimensional Gaussian tail in the exact weakened exponential
form used by the Lovett--Meka constraint budget. -/
theorem weightedStandardGaussianSum_abs_tail_exp_sixteen
    (iota : Type*) [Fintype iota] (a : iota → ℝ)
    (hvariance : 0 < gaussianVarianceProxy a) {c : ℝ} (hc : 0 ≤ c) :
    (standardGaussianProduct iota).real
        {omega | c * sqrt (gaussianVarianceProxy a) ≤
          |∑ i, a i * omega i|} ≤
      2 * exp (-c ^ 2 / 16) := by
  exact measureReal_abs_ge_mul_sqrt_le_exp_sixteen
    (hasSubgaussianMGF_weightedStandardGaussianSum iota a) hvariance hc

end Erdos228.GaussianTail
