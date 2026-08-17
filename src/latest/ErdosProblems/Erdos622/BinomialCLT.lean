import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Distributions.Binomial
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# A de Moivre--Laplace interface for Erdős Problem 622

This file derives the fixed-window central limit theorem for a fair binomial
law from Mathlib's characteristic-function central limit theorem.  It also
uses Mathlib's canonical binomial probability measure, so the finite counting
layer can connect to it through `binomial_real_singleton`.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory Topology unitInterval

namespace Erdos622.BinomialCLT

noncomputable section

/-- The parameter `1 / 2` as an element of the unit interval. -/
def fair : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

@[simp] lemma fair_coe : (fair : ℝ) = 1 / 2 := rfl

/-- A fair random sign, represented as a two-point probability measure on
the reals. -/
def fairRademacher : Measure ℝ := Ber((1 : ℝ), -1, fair)

instance : IsProbabilityMeasure fairRademacher := by
  unfold fairRademacher
  infer_instance

@[simp] lemma integral_id_fairRademacher :
    ∫ x : ℝ, x ∂fairRademacher = 0 := by
  rw [fairRademacher, integral_bernoulliMeasure]
  norm_num

@[simp] lemma integral_sq_fairRademacher :
    ∫ x : ℝ, x ^ 2 ∂fairRademacher = 1 := by
  rw [fairRademacher, integral_bernoulliMeasure]
  norm_num

lemma charFun_fairRademacher (t : ℝ) :
    charFun fairRademacher t =
      (Complex.exp (t * Complex.I) + Complex.exp (-t * Complex.I)) / 2 := by
  rw [fairRademacher, charFun_apply_real, integral_bernoulliMeasure]
  simp only [fair_coe]
  norm_num [Complex.real_smul]
  ring

/-- Characteristic functions transform predictably under a real affine map. -/
lemma charFun_map_affine (μ : Measure ℝ) (a b t : ℝ) :
    charFun (μ.map (fun x ↦ a * x + b)) t =
      charFun μ (a * t) * Complex.exp (b * t * Complex.I) := by
  rw [show (fun x : ℝ ↦ a * x + b) = (fun x ↦ x + b) ∘ (fun x ↦ a * x) by
    funext x
    rfl]
  rw [← AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
  rw [charFun_map_add_const, charFun_map_mul]
  congr 2
  simp only [Real.inner_apply]
  push_cast
  ring

/-- The characteristic function of a binomial law, in the form needed below. -/
lemma charFun_map_cast_binomial (n : ℕ) (p : unitInterval) (t : ℝ) :
    charFun Bin(ℝ, n, p) t =
      (((p : ℂ) * Complex.exp (t * Complex.I)) + (1 - (p : ℂ))) ^ n := by
  rw [charFun_apply_real, integral_map_cast_binomial, add_pow]
  rw [← Nat.range_succ_eq_Iic]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' : k ≤ n := by simpa using hk
  rw [show Complex.exp (t * (k : ℝ) * Complex.I) =
      Complex.exp (t * Complex.I) ^ k by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring]
  simp only [Complex.real_smul]
  push_cast
  ring

/-- The fair binomial law on the reals. -/
def fairBinomial (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨Bin(ℝ, n, fair), by infer_instance⟩

/-- The fair binomial law after centering and normalization to variance one. -/
def standardizedFairBinomial (n : ℕ) : ProbabilityMeasure ℝ :=
  (fairBinomial n).map (by fun_prop : AEMeasurable
    (fun x : ℝ ↦ (2 * x - n) / Real.sqrt n) (fairBinomial n))

/-- The standard Gaussian law as a bundled probability measure. -/
def standardGaussian : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 1, by infer_instance⟩

/-- Centering a fair binomial characteristic function turns it into a power
of the fair-Rademacher characteristic function. -/
lemma charFun_standardizedFairBinomial (n : ℕ) (t : ℝ) :
    charFun (standardizedFairBinomial n : Measure ℝ) t =
      charFun fairRademacher ((Real.sqrt n)⁻¹ * t) ^ n := by
  rw [standardizedFairBinomial, ProbabilityMeasure.toMeasure_map]
  rw [show (fun x : ℝ ↦ (2 * x - n) / Real.sqrt n) =
      fun x ↦ (2 / Real.sqrt n) * x + (-n / Real.sqrt n) by
    funext x
    ring]
  rw [charFun_map_affine]
  change charFun Bin(ℝ, n, fair) (2 / Real.sqrt n * t) * _ = _
  rw [charFun_map_cast_binomial, charFun_fairRademacher]
  let u : ℝ := (Real.sqrt n)⁻¹ * t
  have hau : 2 / Real.sqrt n * t = 2 * u := by
    simp only [u]
    ring
  have hbu : -↑n / Real.sqrt n * t = -↑n * u := by
    simp only [u]
    ring
  rw [hau]
  rw [show (Real.sqrt n)⁻¹ * t = u from rfl]
  have hbuC : ((-↑n / Real.sqrt n : ℝ) : ℂ) * (t : ℂ) =
      ((-↑n * u : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_mul] using congrArg Complex.ofReal hbu
  rw [hbuC]
  simp only [fair_coe]
  have hexp_n : Complex.exp (((-↑n * u : ℝ) : ℂ) * Complex.I) =
      Complex.exp (-u * Complex.I) ^ n := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hexp_n, ← mul_pow]
  congr 1
  have hexp_cancel :
      Complex.exp (((2 * u : ℝ) : ℂ) * Complex.I) * Complex.exp (-u * Complex.I) =
        Complex.exp (u * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [add_mul, mul_assoc, hexp_cancel]
  ring

/-- De Moivre--Laplace in weak-convergence form: the centered, variance-one
fair binomial laws converge to the standard Gaussian law. -/
theorem standardizedFairBinomial_tendsto :
    Tendsto standardizedFairBinomial atTop (𝓝 standardGaussian) := by
  rw [ProbabilityMeasure.tendsto_iff_tendsto_charFun]
  intro t
  simp_rw [charFun_standardizedFairBinomial]
  have h := tendsto_charFun_inv_sqrt_mul_pow
    (P := fairRademacher) (X := fun x : ℝ ↦ x) (by fun_prop)
    integral_id_fairRademacher integral_sq_fairRademacher t
  convert h using 1 <;> simp [standardGaussian, charFun_gaussianReal] <;> ring

/-- Probability that a standardized fair binomial lies in the fixed closed
interval `[a,b]`, as a real number. -/
def fairBinomialWindowMass (n : ℕ) (a b : ℝ) : ℝ :=
  (standardizedFairBinomial n (Icc a b) : ℝ)

/-- Standard Gaussian mass of the fixed closed interval `[a,b]`. -/
def gaussianWindowMass (a b : ℝ) : ℝ :=
  (standardGaussian (Icc a b) : ℝ)

/-- The normalized point corresponding to the binomial value `k`. -/
def standardizedBinomialPoint (n k : ℕ) : ℝ :=
  (2 * k - n) / Real.sqrt n

/-- The finite binomial-coefficient sum for a standardized closed window. -/
def explicitFairBinomialWindowMass (n : ℕ) (a b : ℝ) : ℝ :=
  ∑ k ∈ Finset.Iic n,
    if standardizedBinomialPoint n k ∈ Icc a b then
      (n.choose k : ℝ) * (1 / 2 : ℝ) ^ k * (1 / 2 : ℝ) ^ (n - k)
    else 0

/-- Number of subsets of an `n`-element set whose cardinality lies in the
specified standardized interval. -/
def fairBinomialWindowCount (n : ℕ) (a b : ℝ) : ℕ :=
  ∑ k ∈ Finset.Iic n,
    if standardizedBinomialPoint n k ∈ Icc a b then n.choose k else 0

lemma fairBinomialWeight_eq (n k : ℕ) (hk : k ≤ n) :
    (n.choose k : ℝ) * (1 / 2 : ℝ) ^ k * (1 / 2 : ℝ) ^ (n - k) =
      (n.choose k : ℝ) / (2 : ℝ) ^ n := by
  rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hk]
  simp [div_eq_mul_inv]

/-- The explicit mass is the favorable subset count divided by `2^n`. -/
theorem explicitFairBinomialWindowMass_eq_count (n : ℕ) (a b : ℝ) :
    explicitFairBinomialWindowMass n a b =
      (fairBinomialWindowCount n a b : ℝ) / (2 : ℝ) ^ n := by
  rw [explicitFairBinomialWindowMass, fairBinomialWindowCount]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hkn : k ≤ n := by simpa using hk
  by_cases hmem : standardizedBinomialPoint n k ∈ Icc a b
  · simp only [hmem, if_true]
    exact fairBinomialWeight_eq n k hkn
  · simp [hmem]

/-- The measure-valued binomial window is exactly its finite
binomial-coefficient sum. -/
theorem fairBinomialWindowMass_eq_explicit (n : ℕ) (a b : ℝ) :
    fairBinomialWindowMass n a b = explicitFairBinomialWindowMass n a b := by
  rw [fairBinomialWindowMass, ← ProbabilityMeasure.measureReal_eq_coe_coeFn]
  rw [← integral_indicator_one measurableSet_Icc]
  rw [standardizedFairBinomial, ProbabilityMeasure.toMeasure_map]
  change (∫ y : ℝ, (Icc a b).indicator (fun _ : ℝ ↦ (1 : ℝ)) y
    ∂Measure.map (fun x : ℝ ↦ (2 * x - n) / Real.sqrt n)
      (fairBinomial n : Measure ℝ)) = _
  rw [integral_map (by fun_prop)
    ((measurable_const.indicator measurableSet_Icc).aestronglyMeasurable)]
  change (∫ x : ℝ, (Icc a b).indicator (fun _ ↦ (1 : ℝ))
    ((2 * x - n) / Real.sqrt n) ∂Bin(ℝ, n, fair)) = _
  rw [integral_map_cast_binomial]
  rw [explicitFairBinomialWindowMass]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  by_cases hmem : standardizedBinomialPoint n k ∈ Icc a b
  · rw [if_pos hmem]
    simp only [standardizedBinomialPoint] at hmem
    rw [Set.indicator_of_mem hmem]
    simp only [fair_coe]
    ring
  · rw [if_neg hmem]
    simp only [standardizedBinomialPoint] at hmem
    rw [Set.indicator_of_notMem hmem]
    simp

/-- Fixed-window de Moivre--Laplace theorem.  The normalization is
`(2 B(n,1/2) - n) / sqrt n`, equivalently
`(B(n,1/2) - n/2) / (sqrt n / 2)`. -/
theorem fairBinomialWindowMass_tendsto {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun n ↦ fairBinomialWindowMass n a b) atTop
      (𝓝 (gaussianWindowMass a b)) := by
  have hfrontier : standardGaussian (frontier (Icc a b)) = 0 := by
    rw [frontier_Icc hab]
    letI : NullSingletonClass (gaussianReal 0 1) :=
      nullSingletonClass_gaussianReal (by norm_num)
    have hpair : gaussianReal 0 1 ({a, b} : Set ℝ) = 0 := by
      simpa only [insert_eq] using measure_union_null
        (measure_singleton a : gaussianReal 0 1 {a} = 0)
        (measure_singleton b : gaussianReal 0 1 {b} = 0)
    simp [standardGaussian, hpair]
  have hmass :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
      standardizedFairBinomial_tendsto hfrontier
  exact (NNReal.continuous_coe.tendsto _).comp hmass

/-- Counting form of the fixed-window de Moivre--Laplace theorem. -/
theorem fairBinomialWindowCount_ratio_tendsto {a b : ℝ} (hab : a ≤ b) :
    Tendsto
      (fun n ↦ (fairBinomialWindowCount n a b : ℝ) / (2 : ℝ) ^ n)
      atTop (𝓝 (gaussianWindowMass a b)) := by
  simpa only [fairBinomialWindowMass_eq_explicit,
    explicitFairBinomialWindowMass_eq_count] using
      fairBinomialWindowMass_tendsto hab

/-- Any strict lower bound for the limiting Gaussian window holds for all
sufficiently large fair-binomial laws. -/
theorem eventually_lt_fairBinomialWindowCount_ratio {a b c : ℝ}
    (hab : a ≤ b) (hc : c < gaussianWindowMass a b) :
    ∀ᶠ n : ℕ in atTop,
      c < (fairBinomialWindowCount n a b : ℝ) / (2 : ℝ) ^ n :=
  (fairBinomialWindowCount_ratio_tendsto hab).eventually_const_lt hc

end

end Erdos622.BinomialCLT
