/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 523.
https://www.erdosproblems.com/forum/thread/523

Informal authors:
- Gábor Halász

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos523.md
-/
/-
Copyright (c) 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license.
-/

import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Probability.BorelCantelli

/-!
# Erdős Problem 523

Let `ε₀, ε₁, ...` be independent random signs and put

`Pₙ(z) = ∑ k ∈ {0, ..., n}, εₖ z^k`.

Halász proved that, almost surely, the maximum of `|Pₙ|` on the complex unit circle is
asymptotic to `√(n log n)`.  In particular the constant asked for in Erdős Problem 523 is `1`.

The accompanying mathematical proof and the correspondence between its steps and the declarations
in this file are in `tex/523.tex`.
-/

open scoped BigOperators ENNReal NNReal Topology ComplexConjugate
open Filter MeasureTheory Metric Set
open ProbabilityTheory

namespace Erdos523

noncomputable section

/-! ## The canonical Rademacher product space -/

/-- A sample is an infinite real sequence.  The probability measure below is concentrated on
the sequences whose entries are signs. -/
abbrev Sample := ℕ → ℝ

/-- The fair probability distribution on the two real values `1` and `-1`. -/
def rademacherMeasure : Measure ℝ :=
  bernoulliMeasure (1 : ℝ) (-1 : ℝ) ⟨(1 / 2 : ℝ), by norm_num⟩

instance : IsProbabilityMeasure rademacherMeasure := by
  unfold rademacherMeasure
  infer_instance

/-- The countable product of the fair two-point distributions. -/
def signMeasure : Measure Sample :=
  Measure.infinitePi fun _ : ℕ ↦ rademacherMeasure

instance : IsProbabilityMeasure signMeasure := by
  unfold signMeasure
  infer_instance

/-- The coordinate random variables in the canonical model are jointly independent. -/
lemma iIndepFun_coordinate :
    iIndepFun (fun k (ω : Sample) ↦ ω k) signMeasure := by
  unfold signMeasure
  exact iIndepFun_infinitePi (X := fun (_ : ℕ) (x : ℝ) ↦ x) (by fun_prop)

/-- Every coordinate in the canonical model has the fair Rademacher law. -/
lemma hasLaw_coordinate (k : ℕ) :
    HasLaw (fun ω : Sample ↦ ω k) rademacherMeasure signMeasure := by
  unfold signMeasure
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ rademacherMeasure) k).hasLaw

lemma ae_coordinate_isSign (k : ℕ) :
    ∀ᵐ ω ∂signMeasure, ω k = 1 ∨ ω k = -1 := by
  rw [(hasLaw_coordinate k).ae_iff
    (p := fun x : ℝ ↦ x = 1 ∨ x = -1) (by fun_prop)]
  rw [ae_iff]
  simp [rademacherMeasure, bernoulliMeasure_def]

/-- Almost every sample of the canonical product measure is genuinely a sequence of signs. -/
lemma ae_all_coordinates_are_signs :
    ∀ᵐ ω ∂signMeasure, ∀ k : ℕ, ω k = 1 ∨ ω k = -1 :=
  ae_all_iff.2 ae_coordinate_isSign

lemma integral_coordinate (k : ℕ) :
    ∫ ω : Sample, ω k ∂signMeasure = 0 := by
  rw [(hasLaw_coordinate k).integral_eq]
  simp only [rademacherMeasure, integral_bernoulliMeasure, id_eq, one_smul, neg_smul,
    smul_eq_mul]
  change (1 / 2 : ℝ) * 1 + (1 - 1 / 2) * -1 = 0
  norm_num

lemma coordinate_mem_Icc (k : ℕ) :
    ∀ᵐ ω ∂signMeasure, ω k ∈ Icc (-1 : ℝ) 1 := by
  filter_upwards [ae_coordinate_isSign k] with ω hω
  rcases hω with hω | hω <;> simp [hω]

/-- Each coordinate has the sharp sub-Gaussian MGF parameter `1`. -/
lemma coordinate_hasSubgaussianMGF (k : ℕ) :
    HasSubgaussianMGF (fun ω : Sample ↦ ω k) 1 signMeasure := by
  convert hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (X := fun ω : Sample ↦ ω k) (a := (-1 : ℝ)) (b := 1)
    (measurable_pi_apply k).aemeasurable (coordinate_mem_Icc k) (integral_coordinate k)
      using 1 <;> norm_num

/-- Hoeffding's sharp projection bound for a finite real Rademacher linear form. -/
lemma measureReal_linearForm_ge_le (s : Finset ℕ) (a : ℕ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    signMeasure.real {ω | t ≤ ∑ k ∈ s, a k * ω k} ≤
      Real.exp (-t ^ 2 / (2 * ∑ k ∈ s, a k ^ 2)) := by
  have hIndep : iIndepFun (fun k (ω : Sample) ↦ a k * ω k) signMeasure :=
    by
      convert iIndepFun_coordinate.comp (fun (k : ℕ) (x : ℝ) ↦ a k * x)
        (fun _ ↦ measurable_const.mul measurable_id) using 1 <;>
        simp only [Function.comp_def]
  have hSubG : ∀ k ∈ s,
      HasSubgaussianMGF (fun ω : Sample ↦ a k * ω k)
        (NNReal.mk (a k ^ 2) (sq_nonneg _) * (1 : ℝ≥0)) signMeasure := by
    intro k _hk
    exact (coordinate_hasSubgaussianMGF k).const_mul (a k)
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hIndep hSubG ht
  have hsum :
      ((∑ k ∈ s, (NNReal.mk (a k ^ 2) (sq_nonneg _) * (1 : ℝ≥0)) : ℝ≥0) : ℝ) =
        ∑ k ∈ s, a k ^ 2 := by
    push_cast
    apply Finset.sum_congr rfl
    intro k _hk
    rw [mul_one]
  rw [hsum] at h
  exact h

/-! ## The random polynomial and its maximum -/

/-- The random Littlewood polynomial with coefficients indexed from `0` through `n`. -/
def randomPolynomial (ω : Sample) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), (ω k : ℂ) * z ^ k

lemma randomPolynomial_zero (ω : Sample) (z : ℂ) : randomPolynomial ω 0 z = ω 0 := by
  simp [randomPolynomial]

lemma randomPolynomial_succ (ω : Sample) (n : ℕ) (z : ℂ) :
    randomPolynomial ω (n + 1) z = randomPolynomial ω n z + (ω (n + 1) : ℂ) * z ^ (n + 1) := by
  simp [randomPolynomial, Finset.sum_range_succ]

lemma continuous_randomPolynomial (ω : Sample) (n : ℕ) :
    Continuous (randomPolynomial ω n) := by
  unfold randomPolynomial
  fun_prop

lemma continuous_randomPolynomial_joint (n : ℕ) :
    Continuous fun p : Sample × ℂ ↦ randomPolynomial p.1 n p.2 := by
  unfold randomPolynomial
  fun_prop

/-- The maximum modulus on the unit circle, defined as the supremum of its compact range. -/
def maximumModulus (ω : Sample) (n : ℕ) : ℝ :=
  sSup (range fun z : Circle ↦ ‖randomPolynomial ω n (z : ℂ)‖)

lemma continuous_norm_randomPolynomial_circle (ω : Sample) (n : ℕ) :
    Continuous fun z : Circle ↦ ‖randomPolynomial ω n (z : ℂ)‖ := by
  exact ((continuous_randomPolynomial ω n).comp continuous_subtype_val).norm

lemma exists_maximumModulus (ω : Sample) (n : ℕ) :
    ∃ z : Circle, ‖randomPolynomial ω n (z : ℂ)‖ = maximumModulus ω n := by
  let f : Circle → ℝ := fun z ↦ ‖randomPolynomial ω n (z : ℂ)‖
  obtain ⟨z, _hz, hzmax⟩ :=
    IsCompact.exists_isMaxOn isCompact_univ Set.univ_nonempty
      (continuous_norm_randomPolynomial_circle ω n).continuousOn
  have hBdd : BddAbove (range f) := ⟨f z, by rintro _ ⟨w, rfl⟩; exact hzmax trivial⟩
  have hNonempty : (range f).Nonempty := ⟨f z, z, rfl⟩
  refine ⟨z, le_antisymm ?_ ?_⟩
  · exact le_csSup hBdd ⟨z, rfl⟩
  · exact csSup_le hNonempty (by rintro _ ⟨w, rfl⟩; exact hzmax trivial)

lemma norm_randomPolynomial_le_maximumModulus (ω : Sample) (n : ℕ) (z : Circle) :
    ‖randomPolynomial ω n (z : ℂ)‖ ≤ maximumModulus ω n := by
  let f : Circle → ℝ := fun w ↦ ‖randomPolynomial ω n (w : ℂ)‖
  obtain ⟨w, _hw, hwmax⟩ :=
    IsCompact.exists_isMaxOn isCompact_univ Set.univ_nonempty
      (continuous_norm_randomPolynomial_circle ω n).continuousOn
  have hBdd : BddAbove (range f) := ⟨f w, by rintro _ ⟨u, rfl⟩; exact hwmax trivial⟩
  exact le_csSup hBdd ⟨z, rfl⟩

lemma maximumModulus_nonneg (ω : Sample) (n : ℕ) : 0 ≤ maximumModulus ω n := by
  obtain ⟨z, hz⟩ := exists_maximumModulus ω n
  rw [← hz]
  exact norm_nonneg _

/-- For fixed degree, the maximum modulus is a continuous (hence measurable) function of the
coefficient sequence.  Only the first `n + 1` coordinates are used. -/
lemma continuous_maximumModulus (n : ℕ) : Continuous fun ω : Sample ↦ maximumModulus ω n := by
  have hjoint :
      Continuous fun p : Sample × Circle ↦ ‖randomPolynomial p.1 n (p.2 : ℂ)‖ := by
    exact ((continuous_randomPolynomial_joint n).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).norm
  simpa only [maximumModulus, image_univ, range_comp, Function.comp_def] using
    (isCompact_univ.continuous_sSup hjoint)

lemma measurable_maximumModulus (n : ℕ) : Measurable fun ω : Sample ↦ maximumModulus ω n :=
  (continuous_maximumModulus n).measurable

lemma norm_randomPolynomial_sub_le (ω η : Sample) (n : ℕ) (z : Circle) :
    ‖randomPolynomial ω n (z : ℂ) - randomPolynomial η n (z : ℂ)‖ ≤
      ∑ k ∈ Finset.range (n + 1), |ω k - η k| := by
  rw [randomPolynomial, randomPolynomial, ← Finset.sum_sub_distrib]
  calc
    ‖∑ k ∈ Finset.range (n + 1),
        ((ω k : ℂ) * (z : ℂ) ^ k - (η k : ℂ) * (z : ℂ) ^ k)‖
        ≤ ∑ k ∈ Finset.range (n + 1),
            ‖(ω k : ℂ) * (z : ℂ) ^ k - (η k : ℂ) * (z : ℂ) ^ k‖ :=
      norm_sum_le _ _
    _ = ∑ k ∈ Finset.range (n + 1), |ω k - η k| := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [← sub_mul]
      rw [norm_mul, norm_pow, Circle.norm_coe, one_pow, mul_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs]

/-- The maximum modulus is `1`-Lipschitz in the `ℓ¹` distance between the finitely many
coefficients that occur. -/
lemma abs_maximumModulus_sub_le (ω η : Sample) (n : ℕ) :
    |maximumModulus ω n - maximumModulus η n| ≤
      ∑ k ∈ Finset.range (n + 1), |ω k - η k| := by
  obtain ⟨z, hz⟩ := exists_maximumModulus ω n
  obtain ⟨w, hw⟩ := exists_maximumModulus η n
  rw [abs_le]
  constructor
  · have h : maximumModulus η n - maximumModulus ω n ≤
        ∑ k ∈ Finset.range (n + 1), |ω k - η k| := by
      rw [← hw]
      calc
        ‖randomPolynomial η n (w : ℂ)‖ - maximumModulus ω n
            ≤ ‖randomPolynomial η n (w : ℂ)‖ -
                ‖randomPolynomial ω n (w : ℂ)‖ := by
              gcongr
              exact norm_randomPolynomial_le_maximumModulus ω n w
        _ ≤ ‖randomPolynomial η n (w : ℂ) - randomPolynomial ω n (w : ℂ)‖ :=
          norm_sub_norm_le _ _
        _ = ‖randomPolynomial ω n (w : ℂ) - randomPolynomial η n (w : ℂ)‖ :=
          norm_sub_rev _ _
        _ ≤ ∑ k ∈ Finset.range (n + 1), |ω k - η k| :=
          norm_randomPolynomial_sub_le ω η n w
    linarith
  · have h : maximumModulus ω n - maximumModulus η n ≤
        ∑ k ∈ Finset.range (n + 1), |ω k - η k| := by
      rw [← hz]
      calc
        ‖randomPolynomial ω n (z : ℂ)‖ - maximumModulus η n
            ≤ ‖randomPolynomial ω n (z : ℂ)‖ -
                ‖randomPolynomial η n (z : ℂ)‖ := by
              gcongr
              exact norm_randomPolynomial_le_maximumModulus η n z
        _ ≤ ‖randomPolynomial ω n (z : ℂ) - randomPolynomial η n (z : ℂ)‖ :=
          norm_sub_norm_le _ _
        _ ≤ ∑ k ∈ Finset.range (n + 1), |ω k - η k| :=
          norm_randomPolynomial_sub_le ω η n z
    exact h

/-! ## Fourier values and sharp one-dimensional projections -/

/-- The `N`-term random Fourier sum, parametrized by a real angle. -/
def fourierSum (ω : Sample) (N : ℕ) (θ : ℝ) : ℂ :=
  ∑ k ∈ Finset.range N, (ω k : ℂ) * (Circle.exp θ : ℂ) ^ k

lemma fourierSum_succ_eq_randomPolynomial (ω : Sample) (n : ℕ) (θ : ℝ) :
    fourierSum ω (n + 1) θ = randomPolynomial ω n (Circle.exp θ : ℂ) := by
  rfl

lemma norm_fourierSum_le_maximumModulus (ω : Sample) (n : ℕ) (θ : ℝ) :
    ‖fourierSum ω (n + 1) θ‖ ≤ maximumModulus ω n := by
  rw [fourierSum_succ_eq_randomPolynomial]
  exact norm_randomPolynomial_le_maximumModulus ω n (Circle.exp θ)

/-- The real projection of a Fourier value in direction `φ`. -/
def realProjection (ω : Sample) (N : ℕ) (θ φ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, Real.cos ((k : ℝ) * θ - φ) * ω k

lemma measurable_realProjection (N : ℕ) (θ φ : ℝ) :
    Measurable fun ω : Sample ↦ realProjection ω N θ φ := by
  unfold realProjection
  fun_prop

/-- The sharp Hoeffding bound for a directional projection of a random Fourier value. -/
lemma measureReal_realProjection_ge_le (N : ℕ) (θ φ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    signMeasure.real {ω | t ≤ realProjection ω N θ φ} ≤
      Real.exp
        (-t ^ 2 /
          (2 * ∑ k ∈ Finset.range N, Real.cos ((k : ℝ) * θ - φ) ^ 2)) := by
  simpa only [realProjection] using measureReal_linearForm_ge_le (Finset.range N)
    (fun k ↦ Real.cos ((k : ℝ) * θ - φ)) ht

lemma sum_projection_variances (N : ℕ) (θ φ : ℝ) :
    ∑ k ∈ Finset.range N, Real.cos ((k : ℝ) * θ - φ) ^ 2 =
      (N : ℝ) / 2 +
        (1 / 2 : ℝ) *
          ∑ k ∈ Finset.range N, Real.cos (2 * ((k : ℝ) * θ - φ)) := by
  calc
    ∑ k ∈ Finset.range N, Real.cos ((k : ℝ) * θ - φ) ^ 2 =
        ∑ k ∈ Finset.range N,
          ((1 / 2 : ℝ) + Real.cos (2 * ((k : ℝ) * θ - φ)) / 2) := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact Real.cos_sq _
    _ = (N : ℝ) / 2 +
        (1 / 2 : ℝ) *
          ∑ k ∈ Finset.range N, Real.cos (2 * ((k : ℝ) * θ - φ)) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← Finset.sum_div]
      ring

lemma norm_geom_sum_le_card (q : ℂ) (N : ℕ) (hq : ‖q‖ = 1) :
    ‖∑ k ∈ Finset.range N, q ^ k‖ ≤ N := by
  calc
    ‖∑ k ∈ Finset.range N, q ^ k‖ ≤ ∑ k ∈ Finset.range N, ‖q ^ k‖ := norm_sum_le _ _
    _ = N := by simp [norm_pow, hq]

lemma norm_geom_sum_le_two_div (q : ℂ) (N : ℕ) (hq : q ≠ 1) (hqnorm : ‖q‖ = 1) :
    ‖∑ k ∈ Finset.range N, q ^ k‖ ≤ 2 / ‖q - 1‖ := by
  have hmul := geom_sum_mul q N
  have hnorm :
      ‖∑ k ∈ Finset.range N, q ^ k‖ * ‖q - 1‖ = ‖q ^ N - 1‖ := by
    rw [← norm_mul, hmul]
  have hnum : ‖q ^ N - 1‖ ≤ 2 := by
    calc
      ‖q ^ N - 1‖ ≤ ‖q ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hqnorm]; norm_num
  apply (le_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hq))).2
  rw [hnorm]
  exact hnum

lemma norm_geom_sum_angular_le_inv_abs_sin (N : ℕ) (θ : ℝ) (hθ : Real.sin θ ≠ 0) :
    ‖∑ k ∈ Finset.range N,
        Complex.exp (Complex.I * ((2 * θ : ℝ) : ℂ)) ^ k‖ ≤
      1 / |Real.sin θ| := by
  let q : ℂ := Complex.exp (Complex.I * ((2 * θ : ℝ) : ℂ))
  have hqnorm : ‖q‖ = 1 := by
    dsimp [q]
    simpa only [mul_comm] using Complex.norm_exp_ofReal_mul_I (2 * θ)
  have hqsub : ‖q - 1‖ = 2 * |Real.sin θ| := by
    dsimp [q]
    calc
      ‖Complex.exp (Complex.I * ((2 * θ : ℝ) : ℂ)) - 1‖ =
          ‖(2 : ℝ) * Real.sin ((2 * θ) / 2)‖ :=
        Complex.norm_exp_I_mul_ofReal_sub_one (2 * θ)
      _ = 2 * |Real.sin θ| := by
        rw [show (2 * θ) / 2 = θ by ring, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (by norm_num)]
  have hq : q ≠ 1 := by
    intro h
    have : ‖q - 1‖ = 0 := by rw [h, sub_self, norm_zero]
    rw [hqsub, mul_eq_zero] at this
    exact hθ (abs_eq_zero.mp (this.resolve_left (by norm_num)))
  have h := norm_geom_sum_le_two_div q N hq hqnorm
  rw [hqsub] at h
  convert h using 1
  field_simp [abs_ne_zero.mpr hθ]

/-! ## Root-of-unity orthogonality -/

lemma geom_sum_eq_zero_of_pow_eq_one {q : ℂ} {N : ℕ} (hq : q ≠ 1) (hqN : q ^ N = 1) :
    ∑ k ∈ Finset.range N, q ^ k = 0 := by
  have h := geom_sum_mul q N
  rw [hqN, sub_self] at h
  exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hq)

/-- The standard primitive `N`-th root of unity.  The value at `N = 0` is harmless; all
orthogonality lemmas explicitly assume `N ≠ 0`. -/
def standardRoot (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

/-- The same root, bundled as a point of the unit circle. -/
def standardRootCircle (N : ℕ) : Circle := Circle.exp (2 * Real.pi / N)

lemma coe_standardRootCircle (N : ℕ) :
    (standardRootCircle N : ℂ) = standardRoot N := by
  simp only [standardRootCircle, Circle.coe_exp, standardRoot]
  congr 1
  push_cast
  ring

lemma standardRoot_isPrimitive {N : ℕ} (hN : N ≠ 0) :
    IsPrimitiveRoot (standardRoot N) N := by
  simpa only [standardRoot] using Complex.isPrimitiveRoot_exp N hN

/-- Finite Fourier orthogonality for the standard root of unity. -/
lemma sum_standardRoot_pow (N r : ℕ) (hN : N ≠ 0) :
    ∑ k ∈ Finset.range N, standardRoot N ^ (r * k) =
      if N ∣ r then (N : ℂ) else 0 := by
  by_cases hr : N ∣ r
  · rw [if_pos hr]
    have hroot : standardRoot N ^ r = 1 :=
      ((standardRoot_isPrimitive hN).pow_eq_one_iff_dvd r).2 hr
    calc
      ∑ k ∈ Finset.range N, standardRoot N ^ (r * k) =
          ∑ k ∈ Finset.range N, (standardRoot N ^ r) ^ k := by
            apply Finset.sum_congr rfl
            intro k _hk
            rw [pow_mul]
      _ = (N : ℂ) := by simp [hroot]
  · rw [if_neg hr]
    have hne : standardRoot N ^ r ≠ 1 := by
      intro h
      exact hr (((standardRoot_isPrimitive hN).pow_eq_one_iff_dvd r).1 h)
    have hpow : (standardRoot N ^ r) ^ N = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, (standardRoot_isPrimitive hN).pow_eq_one, one_pow]
    calc
      ∑ k ∈ Finset.range N, standardRoot N ^ (r * k) =
          ∑ k ∈ Finset.range N, (standardRoot N ^ r) ^ k := by
            apply Finset.sum_congr rfl
            intro k _hk
            rw [pow_mul]
      _ = 0 := geom_sum_eq_zero_of_pow_eq_one hne hpow

/-- The discrete Fourier transform of the first `N` signs at frequency `r`. -/
def dftValue (ω : Sample) (N r : ℕ) : ℂ :=
  ∑ k ∈ Finset.range N, (ω k : ℂ) * standardRoot N ^ (r * k)

lemma dftValue_succ_eq_randomPolynomial (ω : Sample) (n r : ℕ) :
    dftValue ω (n + 1) r =
      randomPolynomial ω n ((standardRootCircle (n + 1) : ℂ) ^ r) := by
  unfold dftValue randomPolynomial
  apply Finset.sum_congr rfl
  intro k _hk
  rw [coe_standardRootCircle, pow_mul]

lemma norm_dftValue_le_maximumModulus (ω : Sample) (n r : ℕ) :
    ‖dftValue ω (n + 1) r‖ ≤ maximumModulus ω n := by
  rw [dftValue_succ_eq_randomPolynomial]
  exact norm_randomPolynomial_le_maximumModulus ω n ((standardRootCircle (n + 1)) ^ r)

lemma measurable_dftValue (N r : ℕ) : Measurable fun ω : Sample ↦ dftValue ω N r := by
  unfold dftValue
  fun_prop

lemma norm_standardRoot_pow (N m : ℕ) : ‖standardRoot N ^ m‖ = 1 := by
  rw [← coe_standardRootCircle, ← Circle.coe_pow, Circle.norm_coe]

lemma sum_standardRoot_pow_re (N r : ℕ) (hN : N ≠ 0) (hr : ¬N ∣ r) :
    ∑ k ∈ Finset.range N, (standardRoot N ^ (r * k)).re = 0 := by
  have h := sum_standardRoot_pow N r hN
  rw [if_neg hr] at h
  have hre := congrArg Complex.re h
  rw [Complex.re_sum] at hre
  simpa only [Complex.zero_re] using hre

lemma sum_standardRoot_pow_im (N r : ℕ) (hN : N ≠ 0) (hr : ¬N ∣ r) :
    ∑ k ∈ Finset.range N, (standardRoot N ^ (r * k)).im = 0 := by
  have h := sum_standardRoot_pow N r hN
  rw [if_neg hr] at h
  have him := congrArg Complex.im h
  rw [Complex.im_sum] at him
  simpa only [Complex.zero_im] using him

lemma complex_re_sq_of_norm_one (z : ℂ) (hz : ‖z‖ = 1) :
    z.re ^ 2 = (1 + (z ^ 2).re) / 2 := by
  have hnorm : z.re ^ 2 + z.im ^ 2 = 1 := by
    calc
      z.re ^ 2 + z.im ^ 2 = Complex.normSq z := by
        rw [Complex.normSq_apply]
        ring
      _ = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
      _ = 1 := by rw [hz]; norm_num
  rw [pow_two z, Complex.mul_re]
  nlinarith

lemma complex_im_sq_of_norm_one (z : ℂ) (hz : ‖z‖ = 1) :
    z.im ^ 2 = (1 - (z ^ 2).re) / 2 := by
  have hnorm : z.re ^ 2 + z.im ^ 2 = 1 := by
    calc
      z.re ^ 2 + z.im ^ 2 = Complex.normSq z := by
        rw [Complex.normSq_apply]
        ring
      _ = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
      _ = 1 := by rw [hz]; norm_num
  rw [pow_two z, Complex.mul_re]
  nlinarith

lemma complex_re_mul_im (z : ℂ) : z.re * z.im = (z ^ 2).im / 2 := by
  rw [pow_two z, Complex.mul_im]
  ring

lemma complex_re_mul_re (z w : ℂ) :
    z.re * w.re = ((z * w).re + (z * conj w).re) / 2 := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

lemma complex_im_mul_im (z w : ℂ) :
    z.im * w.im = ((z * conj w).re - (z * w).re) / 2 := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

lemma complex_re_mul_im_two (z w : ℂ) :
    z.re * w.im = ((z * w).im - (z * conj w).im) / 2 := by
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

lemma sum_standardRoot_pow_re_sq (N r : ℕ) (hN : N ≠ 0) (hr : ¬N ∣ 2 * r) :
    ∑ k ∈ Finset.range N, (standardRoot N ^ (r * k)).re ^ 2 = (N : ℝ) / 2 := by
  have hpowterms :
      ∑ k ∈ Finset.range N, ((standardRoot N ^ (r * k)) ^ 2).re =
        ∑ k ∈ Finset.range N, (standardRoot N ^ ((2 * r) * k)).re := by
    apply Finset.sum_congr rfl
    intro k _hk
    rw [← pow_mul, show (r * k) * 2 = (2 * r) * k by ac_rfl]
  calc
    ∑ k ∈ Finset.range N, (standardRoot N ^ (r * k)).re ^ 2 =
        ∑ k ∈ Finset.range N,
          (1 + ((standardRoot N ^ (r * k)) ^ 2).re) / 2 := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact complex_re_sq_of_norm_one _ (norm_standardRoot_pow N (r * k))
    _ = (N : ℝ) / 2 +
        (∑ k ∈ Finset.range N, (standardRoot N ^ ((2 * r) * k)).re) / 2 := by
      simp_rw [add_div, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      push_cast
      rw [← Finset.sum_div, hpowterms, Finset.sum_div]
      ring
    _ = (N : ℝ) / 2 := by rw [sum_standardRoot_pow_re N (2 * r) hN hr, zero_div, add_zero]

lemma sum_standardRoot_pow_im_sq (N r : ℕ) (hN : N ≠ 0) (hr : ¬N ∣ 2 * r) :
    ∑ k ∈ Finset.range N, (standardRoot N ^ (r * k)).im ^ 2 = (N : ℝ) / 2 := by
  have hpowterms :
      ∑ k ∈ Finset.range N, ((standardRoot N ^ (r * k)) ^ 2).re =
        ∑ k ∈ Finset.range N, (standardRoot N ^ ((2 * r) * k)).re := by
    apply Finset.sum_congr rfl
    intro k _hk
    rw [← pow_mul, show (r * k) * 2 = (2 * r) * k by ac_rfl]
  calc
    ∑ k ∈ Finset.range N, (standardRoot N ^ (r * k)).im ^ 2 =
        ∑ k ∈ Finset.range N,
          (1 - ((standardRoot N ^ (r * k)) ^ 2).re) / 2 := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact complex_im_sq_of_norm_one _ (norm_standardRoot_pow N (r * k))
    _ = (N : ℝ) / 2 -
        (∑ k ∈ Finset.range N, (standardRoot N ^ ((2 * r) * k)).re) / 2 := by
      simp_rw [sub_div, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      rw [← Finset.sum_div, hpowterms, Finset.sum_div]
      ring
    _ = (N : ℝ) / 2 := by rw [sum_standardRoot_pow_re N (2 * r) hN hr, zero_div, sub_zero]

lemma sum_standardRoot_pow_re_mul_im (N r : ℕ) (hN : N ≠ 0) (hr : ¬N ∣ 2 * r) :
    ∑ k ∈ Finset.range N,
      (standardRoot N ^ (r * k)).re * (standardRoot N ^ (r * k)).im = 0 := by
  have hpowterms :
      ∑ k ∈ Finset.range N, ((standardRoot N ^ (r * k)) ^ 2).im =
        ∑ k ∈ Finset.range N, (standardRoot N ^ ((2 * r) * k)).im := by
    apply Finset.sum_congr rfl
    intro k _hk
    rw [← pow_mul, show (r * k) * 2 = (2 * r) * k by ac_rfl]
  calc
    ∑ k ∈ Finset.range N,
        (standardRoot N ^ (r * k)).re * (standardRoot N ^ (r * k)).im =
        ∑ k ∈ Finset.range N, ((standardRoot N ^ (r * k)) ^ 2).im / 2 := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact complex_re_mul_im _
    _ = (∑ k ∈ Finset.range N,
          (standardRoot N ^ ((2 * r) * k)).im) / 2 := by
      rw [← Finset.sum_div, hpowterms]
    _ = 0 := by rw [sum_standardRoot_pow_im N (2 * r) hN hr, zero_div]

lemma standardRoot_pow_mul_pow (N r s k : ℕ) :
    standardRoot N ^ (r * k) * standardRoot N ^ (s * k) =
      standardRoot N ^ ((r + s) * k) := by
  rw [← pow_add, Nat.add_mul]

lemma standardRoot_pow_mul_conj_pow (N r s k : ℕ) (hsr : s ≤ r) :
    standardRoot N ^ (r * k) * conj (standardRoot N ^ (s * k)) =
      standardRoot N ^ ((r - s) * k) := by
  have hne : standardRoot N ≠ 0 := by
    rw [← coe_standardRootCircle]
    exact Circle.coe_ne_zero _
  rw [← Complex.inv_eq_conj (norm_standardRoot_pow N (s * k)),
    ← pow_sub₀ _ hne (Nat.mul_le_mul_right k hsr), Nat.sub_mul]

lemma sum_standardRoot_pow_re_mul_re (N r s : ℕ) (hN : N ≠ 0) (hsr : s ≤ r)
    (hplus : ¬N ∣ r + s) (hminus : ¬N ∣ r - s) :
    ∑ k ∈ Finset.range N,
      (standardRoot N ^ (r * k)).re * (standardRoot N ^ (s * k)).re = 0 := by
  calc
    ∑ k ∈ Finset.range N,
        (standardRoot N ^ (r * k)).re * (standardRoot N ^ (s * k)).re =
        ∑ k ∈ Finset.range N,
          ((standardRoot N ^ ((r + s) * k)).re +
            (standardRoot N ^ ((r - s) * k)).re) / 2 := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [complex_re_mul_re, standardRoot_pow_mul_pow,
        standardRoot_pow_mul_conj_pow N r s k hsr]
    _ = ((∑ k ∈ Finset.range N, (standardRoot N ^ ((r + s) * k)).re) +
          ∑ k ∈ Finset.range N, (standardRoot N ^ ((r - s) * k)).re) / 2 := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, Finset.sum_add_distrib]
    _ = 0 := by
      rw [sum_standardRoot_pow_re N (r + s) hN hplus,
        sum_standardRoot_pow_re N (r - s) hN hminus]
      norm_num

lemma sum_standardRoot_pow_im_mul_im (N r s : ℕ) (hN : N ≠ 0) (hsr : s ≤ r)
    (hplus : ¬N ∣ r + s) (hminus : ¬N ∣ r - s) :
    ∑ k ∈ Finset.range N,
      (standardRoot N ^ (r * k)).im * (standardRoot N ^ (s * k)).im = 0 := by
  calc
    ∑ k ∈ Finset.range N,
        (standardRoot N ^ (r * k)).im * (standardRoot N ^ (s * k)).im =
        ∑ k ∈ Finset.range N,
          ((standardRoot N ^ ((r - s) * k)).re -
            (standardRoot N ^ ((r + s) * k)).re) / 2 := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [complex_im_mul_im, standardRoot_pow_mul_pow,
        standardRoot_pow_mul_conj_pow N r s k hsr]
    _ = ((∑ k ∈ Finset.range N, (standardRoot N ^ ((r - s) * k)).re) -
          ∑ k ∈ Finset.range N, (standardRoot N ^ ((r + s) * k)).re) / 2 := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, Finset.sum_sub_distrib]
    _ = 0 := by
      rw [sum_standardRoot_pow_re N (r - s) hN hminus,
        sum_standardRoot_pow_re N (r + s) hN hplus]
      norm_num

lemma sum_standardRoot_pow_re_mul_im_two (N r s : ℕ) (hN : N ≠ 0) (hsr : s ≤ r)
    (hplus : ¬N ∣ r + s) (hminus : ¬N ∣ r - s) :
    ∑ k ∈ Finset.range N,
      (standardRoot N ^ (r * k)).re * (standardRoot N ^ (s * k)).im = 0 := by
  calc
    ∑ k ∈ Finset.range N,
        (standardRoot N ^ (r * k)).re * (standardRoot N ^ (s * k)).im =
        ∑ k ∈ Finset.range N,
          ((standardRoot N ^ ((r + s) * k)).im -
            (standardRoot N ^ ((r - s) * k)).im) / 2 := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [complex_re_mul_im_two, standardRoot_pow_mul_pow,
        standardRoot_pow_mul_conj_pow N r s k hsr]
    _ = ((∑ k ∈ Finset.range N, (standardRoot N ^ ((r + s) * k)).im) -
          ∑ k ∈ Finset.range N, (standardRoot N ^ ((r - s) * k)).im) / 2 := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, Finset.sum_sub_distrib]
    _ = 0 := by
      rw [sum_standardRoot_pow_im N (r + s) hN hplus,
        sum_standardRoot_pow_im N (r - s) hN hminus]
      norm_num

/-! ## Exponential tilting for one Fourier coordinate -/

/-- The moment generating function of a scaled coordinate is a hyperbolic cosine. -/
lemma mgf_mul_coordinate (a t : ℝ) (k : ℕ) :
    mgf (fun ω : Sample ↦ a * ω k) signMeasure t = Real.cosh (t * a) := by
  rw [mgf]
  calc
    ∫ ω : Sample, Real.exp (t * (a * ω k)) ∂signMeasure =
        ∫ x : ℝ, Real.exp (t * (a * x)) ∂rademacherMeasure := by
      simpa only [Function.comp_apply] using
        (hasLaw_coordinate k).integral_comp
          (f := fun x : ℝ ↦ Real.exp (t * (a * x))) (by fun_prop)
    _ = Real.cosh (t * a) := by
      simp only [rademacherMeasure, integral_bernoulliMeasure, smul_eq_mul]
      rw [Real.cosh_eq]
      congr 1 <;> ring_nf

/-- A finite real linear form in the signs. -/
def linearForm (s : Finset ℕ) (a : ℕ → ℝ) (ω : Sample) : ℝ :=
  ∑ k ∈ s, a k * ω k

lemma measurable_linearForm (s : Finset ℕ) (a : ℕ → ℝ) :
    Measurable (linearForm s a) := by
  unfold linearForm
  fun_prop

lemma iIndepFun_mul_coordinate (a : ℕ → ℝ) :
    iIndepFun (fun k (ω : Sample) ↦ a k * ω k) signMeasure := by
  convert iIndepFun_coordinate.comp (fun k (x : ℝ) ↦ a k * x)
    (fun _ ↦ measurable_const.mul measurable_id) using 1
  simp only [Function.comp_def]

/-- Exact cumulant-generating function of a finite Rademacher linear form. -/
lemma cgf_linearForm (s : Finset ℕ) (a : ℕ → ℝ) (t : ℝ) :
    cgf (linearForm s a) signMeasure t =
      ∑ k ∈ s, Real.log (Real.cosh (t * a k)) := by
  have hInt : ∀ k ∈ s,
      Integrable (fun ω : Sample ↦ Real.exp (t * (a k * ω k))) signMeasure := by
    intro k _hk
    have hBound : ∀ᵐ ω ∂signMeasure,
        ‖Real.exp (t * (a k * ω k))‖ ≤ Real.exp |t * a k| := by
      filter_upwards [ae_coordinate_isSign k] with ω hω
      rcases hω with hω | hω <;> rw [hω] <;>
        simp only [mul_one, mul_neg, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      · exact Real.exp_le_exp.mpr (le_abs_self _)
      · exact Real.exp_le_exp.mpr (neg_le_abs _)
    exact Integrable.mono' (integrable_const (Real.exp |t * a k|))
      ((measurable_const.mul (measurable_const.mul (measurable_pi_apply k))).exp.aestronglyMeasurable)
      hBound
  have h := (iIndepFun_mul_coordinate a).cgf_sum
    (s := s) (t := t) (fun _ ↦ by fun_prop) hInt
  rw [show linearForm s a = ∑ k ∈ s, fun ω : Sample ↦ a k * ω k by
    funext ω
    simp only [linearForm, Finset.sum_apply]]
  rw [h]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [cgf, mgf_mul_coordinate]

lemma hasSubgaussianMGF_linearForm (s : Finset ℕ) (a : ℕ → ℝ) :
    HasSubgaussianMGF (linearForm s a)
      (∑ k ∈ s, NNReal.mk (a k ^ 2) (sq_nonneg _) * (1 : ℝ≥0)) signMeasure := by
  have h := HasSubgaussianMGF.sum_of_iIndepFun (iIndepFun_mul_coordinate a)
    (s := s) (c := fun k ↦ NNReal.mk (a k ^ 2) (sq_nonneg _) * (1 : ℝ≥0))
    (fun k _hk ↦ by
      exact (coordinate_hasSubgaussianMGF k).const_mul (a k))
  exact h.congr (Y := linearForm s a) (ae_of_all _ fun _ω ↦ rfl)

/-- First derivative of one summand in the exact cumulant-generating function. -/
lemma hasDerivAt_log_cosh_mul (a t : ℝ) :
    HasDerivAt (fun x : ℝ ↦ Real.log (Real.cosh (x * a)))
      (a * (Real.sinh (t * a) / Real.cosh (t * a))) t := by
  have hinner : HasDerivAt (fun x : ℝ ↦ x * a) a t := by
    exact hasDerivAt_mul_const (x := t) a
  have hcosh : HasDerivAt (fun x : ℝ ↦ Real.cosh (x * a))
      (Real.sinh (t * a) * a) t := (Real.hasDerivAt_cosh _).comp t hinner
  have h := (Real.hasDerivAt_log (x := Real.cosh (t * a)) (Real.cosh_pos _).ne').comp t hcosh
  apply h.congr_deriv
  field_simp [Real.cosh_pos _ |>.ne']

/-- Second derivative of one summand in the exact cumulant-generating function. -/
lemma hasDerivAt_tiltedMeanTerm (a t : ℝ) :
    HasDerivAt (fun x : ℝ ↦ a * (Real.sinh (x * a) / Real.cosh (x * a)))
      (a ^ 2 / Real.cosh (t * a) ^ 2) t := by
  have hinner : HasDerivAt (fun x : ℝ ↦ x * a) a t := by
    exact hasDerivAt_mul_const (x := t) a
  have hsinh : HasDerivAt (fun x : ℝ ↦ Real.sinh (x * a))
      (Real.cosh (t * a) * a) t := (Real.hasDerivAt_sinh _).comp t hinner
  have hcosh : HasDerivAt (fun x : ℝ ↦ Real.cosh (x * a))
      (Real.sinh (t * a) * a) t := (Real.hasDerivAt_cosh _).comp t hinner
  have h := (hsinh.div hcosh (Real.cosh_pos _).ne').const_mul a
  apply h.congr_deriv
  field_simp [Real.cosh_pos _ |>.ne']
  rw [show a * t = t * a by ring, Real.cosh_sq_sub_sinh_sq, mul_one]

lemma deriv_cgf_linearForm (s : Finset ℕ) (a : ℕ → ℝ) (t : ℝ) :
    deriv (cgf (linearForm s a) signMeasure) t =
      ∑ k ∈ s, a k * (Real.sinh (t * a k) / Real.cosh (t * a k)) := by
  have hfun : cgf (linearForm s a) signMeasure =
      fun x ↦ ∑ k ∈ s, Real.log (Real.cosh (x * a k)) := by
    funext x
    exact cgf_linearForm s a x
  rw [hfun]
  exact (HasDerivAt.fun_sum fun k _hk ↦ hasDerivAt_log_cosh_mul (a k) t).deriv

lemma iteratedDeriv_two_cgf_linearForm (s : Finset ℕ) (a : ℕ → ℝ) (t : ℝ) :
    iteratedDeriv 2 (cgf (linearForm s a) signMeasure) t =
      ∑ k ∈ s, a k ^ 2 / Real.cosh (t * a k) ^ 2 := by
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  have hfun : deriv (cgf (linearForm s a) signMeasure) =
      fun x ↦ ∑ k ∈ s, a k * (Real.sinh (x * a k) / Real.cosh (x * a k)) := by
    funext x
    exact deriv_cgf_linearForm s a x
  rw [hfun]
  exact (HasDerivAt.fun_sum fun k _hk ↦ hasDerivAt_tiltedMeanTerm (a k) t).deriv

lemma mem_interior_integrableExpSet_linearForm (s : Finset ℕ) (a : ℕ → ℝ) (t : ℝ) :
    t ∈ interior (integrableExpSet (linearForm s a) signMeasure) := by
  rw [(hasSubgaussianMGF_linearForm s a).integrableExpSet_eq_univ]
  simp

/-- Exact mean of a Rademacher linear form under its exponential tilt. -/
lemma integral_linearForm_tilted (s : Finset ℕ) (a : ℕ → ℝ) (t : ℝ) :
    ∫ ω, linearForm s a ω
        ∂(signMeasure.tilted (fun ω ↦ t * linearForm s a ω)) =
      ∑ k ∈ s, a k * (Real.sinh (t * a k) / Real.cosh (t * a k)) := by
  rw [integral_tilted_mul_self (mem_interior_integrableExpSet_linearForm s a t)]
  exact deriv_cgf_linearForm s a t

/-- Exact variance under the exponential tilt. -/
lemma variance_linearForm_tilted (s : Finset ℕ) (a : ℕ → ℝ) (t : ℝ) :
    Var[linearForm s a;
        signMeasure.tilted (fun ω ↦ t * linearForm s a ω)] =
      ∑ k ∈ s, a k ^ 2 / Real.cosh (t * a k) ^ 2 := by
  rw [variance_tilted_mul (mem_interior_integrableExpSet_linearForm s a t)]
  exact iteratedDeriv_two_cgf_linearForm s a t

lemma variance_linearForm_tilted_le (s : Finset ℕ) (a : ℕ → ℝ) (t : ℝ) :
    Var[linearForm s a;
        signMeasure.tilted (fun ω ↦ t * linearForm s a ω)] ≤
      ∑ k ∈ s, a k ^ 2 := by
  rw [variance_linearForm_tilted]
  apply Finset.sum_le_sum
  intro k _hk
  have hden : 1 ≤ Real.cosh (t * a k) ^ 2 := by
    nlinarith [Real.one_le_cosh (t * a k)]
  exact div_le_self (sq_nonneg _) hden

lemma hasDerivAt_tanh (x : ℝ) :
    HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have h := hasDerivAt_tiltedMeanTerm 1 x
  simp only [one_mul, mul_one, one_pow] at h
  convert h using 1
  funext y
  exact Real.tanh_eq_sinh_div_cosh y

lemma tanh_le_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.tanh x ≤ x := by
  let f : ℝ → ℝ := fun y ↦ y - Real.tanh y
  have hfderiv (y : ℝ) : HasDerivAt f (1 - 1 / Real.cosh y ^ 2) y := by
    dsimp [f]
    have hid : HasDerivAt (fun z : ℝ ↦ z) 1 y := hasDerivAt_id' y
    exact hid.sub (hasDerivAt_tanh y)
  have hf : Differentiable ℝ f := fun y ↦ (hfderiv y).differentiableAt
  have hmono : Monotone f := monotone_of_deriv_nonneg hf fun y ↦ by
    rw [(hfderiv y).deriv]
    have hcosh : 1 ≤ Real.cosh y ^ 2 := by nlinarith [Real.one_le_cosh y]
    have hcoshpos : 0 < Real.cosh y ^ 2 := lt_of_lt_of_le zero_lt_one hcosh
    have := (div_le_one hcoshpos).2 hcosh
    linarith
  have h := hmono hx
  dsimp [f] at h
  rw [Real.tanh_zero, sub_zero] at h
  linarith

lemma tanh_cubic_lower {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 ≤ Real.tanh x := by
  let g : ℝ → ℝ := (Real.tanh - fun y : ℝ ↦ y) + (fun y : ℝ ↦ y) ^ 3
  have hgderiv (y : ℝ) :
      HasDerivAt g (1 / Real.cosh y ^ 2 - 1 + 3 * y ^ 2) y := by
    dsimp [g]
    have hid : HasDerivAt (fun z : ℝ ↦ z) 1 y := hasDerivAt_id' y
    simpa only [Pi.sub_apply, Pi.add_apply, Pi.pow_apply, Nat.cast_ofNat,
      Nat.reduceSub, mul_one] using ((hasDerivAt_tanh y).sub hid).add (hid.pow 3)
  have hg : Differentiable ℝ g := fun y ↦ (hgderiv y).differentiableAt
  have hmono : MonotoneOn g (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hg.continuous.continuousOn
      hg.differentiableOn
    intro y hy
    rw [interior_Ici, mem_Ioi] at hy
    rw [(hgderiv y).deriv]
    have htanh0 : 0 ≤ Real.tanh y := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonneg (Real.sinh_nonneg_iff.mpr hy.le) (Real.cosh_pos _).le
    have htanhle : Real.tanh y ≤ y := tanh_le_self_of_nonneg hy.le
    have hsq : Real.tanh y ^ 2 ≤ y ^ 2 := by nlinarith
    have hid : 1 / Real.cosh y ^ 2 = 1 - Real.tanh y ^ 2 := by
      rw [Real.tanh_eq_sinh_div_cosh]
      field_simp [Real.cosh_pos y |>.ne']
      nlinarith [Real.cosh_sq_sub_sinh_sq y]
    rw [hid]
    nlinarith
  have h := hmono (mem_Ici.mpr (le_refl 0)) (mem_Ici.mpr hx) hx
  dsimp [g] at h
  rw [Real.tanh_zero] at h
  norm_num at h
  linarith

lemma mul_tanh_mul_lower (a t : ℝ) (ht : 0 ≤ t) :
    t * a ^ 2 - t ^ 3 * a ^ 4 ≤ a * Real.tanh (t * a) := by
  have hpos (b : ℝ) (hb : 0 ≤ b) :
      t * b ^ 2 - t ^ 3 * b ^ 4 ≤ b * Real.tanh (t * b) := by
    have h := tanh_cubic_lower (mul_nonneg ht hb)
    have := mul_le_mul_of_nonneg_left h hb
    nlinarith
  by_cases ha : 0 ≤ a
  · exact hpos a ha
  · have hna : 0 ≤ -a := neg_nonneg.mpr (le_of_lt (lt_of_not_ge ha))
    have h := hpos (-a) hna
    rw [mul_neg, Real.tanh_neg, mul_neg, neg_mul, neg_neg] at h
    convert h using 1 <;> ring

lemma mul_tanh_mul_upper (a t : ℝ) (ht : 0 ≤ t) :
    a * Real.tanh (t * a) ≤ t * a ^ 2 := by
  have hpos (b : ℝ) (hb : 0 ≤ b) : b * Real.tanh (t * b) ≤ t * b ^ 2 := by
    have h := tanh_le_self_of_nonneg (mul_nonneg ht hb)
    have := mul_le_mul_of_nonneg_left h hb
    nlinarith
  by_cases ha : 0 ≤ a
  · exact hpos a ha
  · have hna : 0 ≤ -a := neg_nonneg.mpr (le_of_lt (lt_of_not_ge ha))
    have h := hpos (-a) hna
    rw [mul_neg, Real.tanh_neg, mul_neg, neg_mul, neg_neg] at h
    convert h using 1 <;> ring

lemma integral_linearForm_tilted_lower (s : Finset ℕ) (a : ℕ → ℝ) (t : ℝ)
    (ht : 0 ≤ t) :
    t * (∑ k ∈ s, a k ^ 2) - t ^ 3 * (∑ k ∈ s, a k ^ 4) ≤
      ∫ ω, linearForm s a ω
        ∂(signMeasure.tilted (fun ω ↦ t * linearForm s a ω)) := by
  rw [integral_linearForm_tilted]
  calc
    t * (∑ k ∈ s, a k ^ 2) - t ^ 3 * (∑ k ∈ s, a k ^ 4) =
        ∑ k ∈ s, (t * a k ^ 2 - t ^ 3 * a k ^ 4) := by
      simp_rw [Finset.mul_sum, Finset.sum_sub_distrib]
    _ ≤ ∑ k ∈ s, a k * (Real.sinh (t * a k) / Real.cosh (t * a k)) := by
      apply Finset.sum_le_sum
      intro k _hk
      rw [← Real.tanh_eq_sinh_div_cosh]
      exact mul_tanh_mul_lower (a k) t ht

lemma integral_linearForm_tilted_upper (s : Finset ℕ) (a : ℕ → ℝ) (t : ℝ)
    (ht : 0 ≤ t) :
    (∫ ω, linearForm s a ω
        ∂(signMeasure.tilted (fun ω ↦ t * linearForm s a ω))) ≤
      t * (∑ k ∈ s, a k ^ 2) := by
  rw [integral_linearForm_tilted]
  calc
    ∑ k ∈ s, a k * (Real.sinh (t * a k) / Real.cosh (t * a k)) ≤
        ∑ k ∈ s, t * a k ^ 2 := by
      apply Finset.sum_le_sum
      intro k _hk
      rw [← Real.tanh_eq_sinh_div_cosh]
      exact mul_tanh_mul_upper (a k) t ht
    _ = t * (∑ k ∈ s, a k ^ 2) := by rw [Finset.mul_sum]

lemma hasDerivAt_log_cosh (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Real.log (Real.cosh y)) (Real.tanh x) x := by
  have h := hasDerivAt_log_cosh_mul 1 x
  simp only [mul_one, one_mul] at h
  rw [Real.tanh_eq_sinh_div_cosh]
  exact h

/-- The elementary fourth-order lower bound used in the change-of-measure estimate. -/
lemma log_cosh_lower (x : ℝ) :
    x ^ 2 / 2 - x ^ 4 / 4 ≤ Real.log (Real.cosh x) := by
  have hnonneg (y : ℝ) (hy : 0 ≤ y) :
      y ^ 2 / 2 - y ^ 4 / 4 ≤ Real.log (Real.cosh y) := by
    let f : ℝ → ℝ :=
      (fun z ↦ Real.log (Real.cosh z)) - (fun z : ℝ ↦ z ^ 2 / 2) +
        (fun z : ℝ ↦ z ^ 4 / 4)
    have hfderiv (z : ℝ) :
        HasDerivAt f (Real.tanh z - z + z ^ 3) z := by
      have hsq : HasDerivAt (fun w : ℝ ↦ w ^ 2 / 2) z z := by
        have h := (hasDerivAt_pow 2 z).div_const 2
        apply h.congr_deriv
        norm_num
      have hfour : HasDerivAt (fun w : ℝ ↦ w ^ 4 / 4) (z ^ 3) z := by
        have h := (hasDerivAt_pow 4 z).div_const 4
        apply h.congr_deriv
        norm_num
      exact ((hasDerivAt_log_cosh z).sub hsq).add hfour
    have hf : Differentiable ℝ f := fun z ↦ (hfderiv z).differentiableAt
    have hmono : MonotoneOn f (Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hf.continuous.continuousOn
        hf.differentiableOn
      intro z hz
      rw [interior_Ici, mem_Ioi] at hz
      rw [(hfderiv z).deriv]
      linarith [tanh_cubic_lower hz.le]
    have h := hmono (mem_Ici.mpr (le_refl 0)) (mem_Ici.mpr hy) hy
    dsimp [f] at h
    norm_num at h
    linarith
  have h := hnonneg |x| (abs_nonneg x)
  have h2 : |x| ^ 2 = x ^ 2 := sq_abs x
  have h4 : |x| ^ 4 = x ^ 4 := by
    calc
      |x| ^ 4 = (|x| ^ 2) ^ 2 := by ring
      _ = (x ^ 2) ^ 2 := by rw [h2]
      _ = x ^ 4 := by ring
  rw [Real.cosh_abs, h2, h4] at h
  exact h

lemma cgf_linearForm_lower (s : Finset ℕ) (a : ℕ → ℝ) (t : ℝ) :
    t ^ 2 / 2 * (∑ k ∈ s, a k ^ 2) -
        t ^ 4 / 4 * (∑ k ∈ s, a k ^ 4) ≤
      cgf (linearForm s a) signMeasure t := by
  rw [cgf_linearForm]
  calc
    t ^ 2 / 2 * (∑ k ∈ s, a k ^ 2) -
        t ^ 4 / 4 * (∑ k ∈ s, a k ^ 4) =
        ∑ k ∈ s, ((t * a k) ^ 2 / 2 - (t * a k) ^ 4 / 4) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_sub_distrib]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro k _hk <;> ring
    _ ≤ ∑ k ∈ s, Real.log (Real.cosh (t * a k)) := by
      apply Finset.sum_le_sum
      intro k _hk
      exact log_cosh_lower (t * a k)

lemma measureReal_tilted_linearForm_eq_setIntegral (s : Finset ℕ) (a : ℕ → ℝ)
    (t : ℝ) {A : Set Sample} (hA : MeasurableSet A) :
    (signMeasure.tilted (fun ω ↦ t * linearForm s a ω)).real A =
      ∫ ω in A, Real.exp (t * linearForm s a ω -
        cgf (linearForm s a) signMeasure t) ∂signMeasure := by
  have hInt := (hasSubgaussianMGF_linearForm s a).integrable_exp_mul t
  rw [measureReal_def,
    tilted_mul_apply_eq_ofReal_integral_cgf' (X := linearForm s a) hA hInt,
    ENNReal.toReal_ofReal]
  exact integral_nonneg fun _ ↦ Real.exp_nonneg _

/-- On a set where the linear form is at most `B`, its tilted probability is controlled by its
original probability and the likelihood-ratio bound. -/
lemma measureReal_tilted_linearForm_le (s : Finset ℕ) (a : ℕ → ℝ)
    {t B : ℝ} (ht : 0 ≤ t) {A : Set Sample} (hA : MeasurableSet A)
    (hB : ∀ ω ∈ A, linearForm s a ω ≤ B) :
    (signMeasure.tilted (fun ω ↦ t * linearForm s a ω)).real A ≤
      Real.exp (t * B - cgf (linearForm s a) signMeasure t) * signMeasure.real A := by
  rw [measureReal_tilted_linearForm_eq_setIntegral s a t hA]
  have hnonneg : 0 ≤ ∫ ω in A,
      Real.exp (t * linearForm s a ω - cgf (linearForm s a) signMeasure t) ∂signMeasure :=
    integral_nonneg fun _ ↦ Real.exp_nonneg _
  calc
    ∫ ω in A, Real.exp (t * linearForm s a ω -
        cgf (linearForm s a) signMeasure t) ∂signMeasure =
        ‖∫ ω in A, Real.exp (t * linearForm s a ω -
          cgf (linearForm s a) signMeasure t) ∂signMeasure‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    _ ≤ Real.exp (t * B - cgf (linearForm s a) signMeasure t) *
        signMeasure.real A := by
      apply norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _)
      intro ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      nlinarith [hB ω hω]

/-- Chebyshev under the tilted law gives positive mass to an interval around the tilted mean. -/
lemma measureReal_tilted_interval_lower (s : Finset ℕ) (a : ℕ → ℝ)
    {t u B r q : ℝ} (hr : 0 < r)
    (hmean_lower : u + r ≤
      ∫ ω, linearForm s a ω
        ∂(signMeasure.tilted (fun ω ↦ t * linearForm s a ω)))
    (hmean_upper :
      (∫ ω, linearForm s a ω
        ∂(signMeasure.tilted (fun ω ↦ t * linearForm s a ω))) + r ≤ B)
    (hvar : Var[linearForm s a;
        signMeasure.tilted (fun ω ↦ t * linearForm s a ω)] ≤ q * r ^ 2) :
    1 - q ≤
      (signMeasure.tilted (fun ω ↦ t * linearForm s a ω)).real
        {ω | u ≤ linearForm s a ω ∧ linearForm s a ω ≤ B} := by
  let μt : Measure Sample :=
    signMeasure.tilted (fun ω ↦ t * linearForm s a ω)
  let m : ℝ := ∫ ω, linearForm s a ω ∂μt
  let D : Set Sample := {ω | r ≤ |linearForm s a ω - m|}
  let A : Set Sample := {ω | u ≤ linearForm s a ω ∧ linearForm s a ω ≤ B}
  have hInt := (hasSubgaussianMGF_linearForm s a).integrable_exp_mul t
  letI : IsProbabilityMeasure μt := by
    dsimp [μt]
    exact isProbabilityMeasure_tilted hInt
  have hD : MeasurableSet D := by
    dsimp [D, m, μt]
    exact measurableSet_le measurable_const
      (((measurable_linearForm s a).sub measurable_const).abs)
  have hA : MeasurableSet A := by
    dsimp [A]
    exact (measurableSet_le measurable_const (measurable_linearForm s a)).inter
      (measurableSet_le (measurable_linearForm s a) measurable_const)
  have hLp : MemLp (linearForm s a) 2 μt := by
    dsimp [μt]
    exact memLp_tilted_mul (mem_interior_integrableExpSet_linearForm s a t) 2
  have hcheb := meas_ge_le_variance_div_sq hLp hr
  have hchebReal : μt.real D ≤
      Var[linearForm s a; μt] / r ^ 2 := by
    rw [measureReal_def]
    calc
      (μt D).toReal ≤
          (ENNReal.ofReal (Var[linearForm s a; μt] / r ^ 2)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb
      _ = Var[linearForm s a; μt] / r ^ 2 := by
        rw [ENNReal.toReal_ofReal]
        exact div_nonneg (variance_nonneg _ _) (sq_nonneg _)
  have hDq : μt.real D ≤ q := by
    have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
    have hv : Var[linearForm s a; μt] ≤ q * r ^ 2 := by
      simpa only [μt] using hvar
    calc
      μt.real D ≤ Var[linearForm s a; μt] / r ^ 2 := hchebReal
      _ ≤ q := (div_le_iff₀ hr2).2 (by simpa [mul_comm] using hv)
  have hsubset : Dᶜ ⊆ A := by
    intro ω hω
    have hn : ¬r ≤ |linearForm s a ω - m| := by
      simpa only [D, Set.mem_compl_iff, Set.mem_setOf_eq] using hω
    have habs : |linearForm s a ω - m| < r := lt_of_not_ge hn
    rw [abs_lt] at habs
    have hml : u + r ≤ m := by simpa only [m, μt] using hmean_lower
    have hmu : m + r ≤ B := by simpa only [m, μt] using hmean_upper
    dsimp [A]
    constructor <;> linarith
  have hmono : μt.real Dᶜ ≤ μt.real A := measureReal_mono hsubset
  rw [measureReal_compl hD, probReal_univ] at hmono
  simpa only [A, μt] using (show 1 - q ≤ μt.real A by linarith)

/-- A finite, fully explicit lower-tail estimate obtained by exponential tilting. -/
lemma measureReal_linearForm_ge_lower_tilt (s : Finset ℕ) (a : ℕ → ℝ)
    {t u B r : ℝ} (ht : 0 ≤ t) (hr : 0 < r)
    (hcenter_lower :
      u + r ≤ t * (∑ k ∈ s, a k ^ 2) - t ^ 3 * (∑ k ∈ s, a k ^ 4))
    (hcenter_upper : t * (∑ k ∈ s, a k ^ 2) + r ≤ B) :
    Real.exp (-t * B + cgf (linearForm s a) signMeasure t) *
        (1 - (∑ k ∈ s, a k ^ 2) / r ^ 2) ≤
      signMeasure.real {ω | u ≤ linearForm s a ω} := by
  let A : Set Sample := {ω | u ≤ linearForm s a ω ∧ linearForm s a ω ≤ B}
  let T : Set Sample := {ω | u ≤ linearForm s a ω}
  have hA : MeasurableSet A := by
    dsimp [A]
    exact (measurableSet_le measurable_const (measurable_linearForm s a)).inter
      (measurableSet_le (measurable_linearForm s a) measurable_const)
  have hmean_lower : u + r ≤
      ∫ ω, linearForm s a ω
        ∂(signMeasure.tilted (fun ω ↦ t * linearForm s a ω)) :=
    hcenter_lower.trans (integral_linearForm_tilted_lower s a t ht)
  have hmean_upper :
      (∫ ω, linearForm s a ω
        ∂(signMeasure.tilted (fun ω ↦ t * linearForm s a ω))) + r ≤ B :=
    by
      have hu := integral_linearForm_tilted_upper s a t ht
      linarith
  have hvar : Var[linearForm s a;
      signMeasure.tilted (fun ω ↦ t * linearForm s a ω)] ≤
      ((∑ k ∈ s, a k ^ 2) / r ^ 2) * r ^ 2 := by
    calc
      Var[linearForm s a;
          signMeasure.tilted (fun ω ↦ t * linearForm s a ω)] ≤
          ∑ k ∈ s, a k ^ 2 := variance_linearForm_tilted_le s a t
      _ = ((∑ k ∈ s, a k ^ 2) / r ^ 2) * r ^ 2 := by
        field_simp [hr.ne']
  have htilt : 1 - (∑ k ∈ s, a k ^ 2) / r ^ 2 ≤
      (signMeasure.tilted (fun ω ↦ t * linearForm s a ω)).real A := by
    simpa only [A] using measureReal_tilted_interval_lower s a hr hmean_lower hmean_upper hvar
  have hlike :
      (signMeasure.tilted (fun ω ↦ t * linearForm s a ω)).real A ≤
        Real.exp (t * B - cgf (linearForm s a) signMeasure t) *
          signMeasure.real A :=
    measureReal_tilted_linearForm_le s a ht hA fun _ω hω ↦ hω.2
  have hfactor :
      Real.exp (-t * B + cgf (linearForm s a) signMeasure t) *
          Real.exp (t * B - cgf (linearForm s a) signMeasure t) = 1 := by
    rw [← Real.exp_add]
    rw [show -t * B + cgf (linearForm s a) signMeasure t +
      (t * B - cgf (linearForm s a) signMeasure t) = 0 by ring, Real.exp_zero]
  calc
    Real.exp (-t * B + cgf (linearForm s a) signMeasure t) *
        (1 - (∑ k ∈ s, a k ^ 2) / r ^ 2) ≤
        Real.exp (-t * B + cgf (linearForm s a) signMeasure t) *
          (signMeasure.tilted (fun ω ↦ t * linearForm s a ω)).real A :=
      mul_le_mul_of_nonneg_left htilt (Real.exp_nonneg _)
    _ ≤ Real.exp (-t * B + cgf (linearForm s a) signMeasure t) *
        (Real.exp (t * B - cgf (linearForm s a) signMeasure t) *
          signMeasure.real A) := mul_le_mul_of_nonneg_left hlike (Real.exp_nonneg _)
    _ = signMeasure.real A := by rw [← mul_assoc, hfactor, one_mul]
    _ ≤ signMeasure.real T := measureReal_mono fun _ω hω ↦ hω.1
    _ = signMeasure.real {ω | u ≤ linearForm s a ω} := rfl

/-! ## Specialization of the tilted estimate to Fourier roots -/

def rootRealProjection (ω : Sample) (N r : ℕ) : ℝ :=
  linearForm (Finset.range N) (fun k ↦ (standardRoot N ^ (r * k)).re) ω

lemma rootRealProjection_eq_re (ω : Sample) (N r : ℕ) :
    rootRealProjection ω N r = (dftValue ω N r).re := by
  unfold rootRealProjection linearForm dftValue
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

lemma measurable_rootRealProjection (N r : ℕ) :
    Measurable fun ω : Sample ↦ rootRealProjection ω N r :=
  measurable_linearForm _ _

lemma sum_standardRoot_pow_re_fourth_le (N r : ℕ) :
    ∑ k ∈ Finset.range N, (standardRoot N ^ (r * k)).re ^ 4 ≤
      ∑ k ∈ Finset.range N, (standardRoot N ^ (r * k)).re ^ 2 := by
  apply Finset.sum_le_sum
  intro k _hk
  let z : ℂ := standardRoot N ^ (r * k)
  have habs : |z.re| ≤ 1 := by
    simpa only [z, norm_standardRoot_pow] using Complex.abs_re_le_norm z
  have hsquare : z.re ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one z.re).2 habs
  have hnonneg : 0 ≤ z.re ^ 2 := sq_nonneg _
  change z.re ^ 4 ≤ z.re ^ 2
  nlinarith [sq_nonneg (z.re ^ 2)]

lemma cgf_rootRealProjection_lower (N r : ℕ) (t : ℝ) (hN : N ≠ 0)
    (hr : ¬N ∣ 2 * r) :
    t ^ 2 * (N : ℝ) / 4 - t ^ 4 * (N : ℝ) / 8 ≤
      cgf (rootRealProjection · N r) signMeasure t := by
  have h := cgf_linearForm_lower (Finset.range N)
    (fun k ↦ (standardRoot N ^ (r * k)).re) t
  rw [sum_standardRoot_pow_re_sq N r hN hr] at h
  have hfour := sum_standardRoot_pow_re_fourth_le N r
  have hfourN :
      ∑ k ∈ Finset.range N, (standardRoot N ^ (r * k)).re ^ 4 ≤ (N : ℝ) / 2 :=
    hfour.trans_eq (sum_standardRoot_pow_re_sq N r hN hr)
  have ht4 : 0 ≤ t ^ 4 / 4 := by positivity
  calc
    t ^ 2 * (N : ℝ) / 4 - t ^ 4 * (N : ℝ) / 8 =
        t ^ 2 / 2 * ((N : ℝ) / 2) - t ^ 4 / 4 * ((N : ℝ) / 2) := by ring
    _ ≤ t ^ 2 / 2 * ((N : ℝ) / 2) -
        t ^ 4 / 4 *
          (∑ k ∈ Finset.range N, (standardRoot N ^ (r * k)).re ^ 4) := by
      gcongr
    _ ≤ cgf (rootRealProjection · N r) signMeasure t := by
      simpa only [rootRealProjection] using h

/-- A fixed positive-density set of nonzero, pairwise nonconjugate Fourier frequencies. -/
def frequencySet (N : ℕ) : Finset ℕ := Finset.Icc 1 (N / 4)

lemma frequencySet_pos {N r : ℕ} (hr : r ∈ frequencySet N) : 0 < r := by
  change r ∈ Finset.Icc 1 (N / 4) at hr
  exact (Finset.mem_Icc.mp hr).1

lemma frequencySet_le_quarter {N r : ℕ} (hr : r ∈ frequencySet N) : r ≤ N / 4 := by
  change r ∈ Finset.Icc 1 (N / 4) at hr
  exact (Finset.mem_Icc.mp hr).2

lemma not_dvd_of_pos_of_lt {N m : ℕ} (hm0 : 0 < m) (hmN : m < N) : ¬N ∣ m := by
  intro h
  exact (not_le_of_gt hmN) (Nat.le_of_dvd hm0 h)

lemma frequencySet_not_dvd_two_mul {N r : ℕ} (hN : 4 ≤ N)
    (hr : r ∈ frequencySet N) : ¬N ∣ 2 * r := by
  apply not_dvd_of_pos_of_lt
  · have hrpos := frequencySet_pos hr
    omega
  · have hrN := frequencySet_le_quarter hr
    have hr4 : r * 4 ≤ N := (Nat.le_div_iff_mul_le (by omega)).mp hrN
    omega

lemma frequencySet_not_dvd_add {N r s : ℕ} (hN : 4 ≤ N)
    (hr : r ∈ frequencySet N) (hs : s ∈ frequencySet N) : ¬N ∣ r + s := by
  apply not_dvd_of_pos_of_lt
  · have hrpos := frequencySet_pos hr
    have hspos := frequencySet_pos hs
    omega
  · have hrN := frequencySet_le_quarter hr
    have hsN := frequencySet_le_quarter hs
    have hr4 : r * 4 ≤ N := (Nat.le_div_iff_mul_le (by omega)).mp hrN
    have hs4 : s * 4 ≤ N := (Nat.le_div_iff_mul_le (by omega)).mp hsN
    omega

lemma frequencySet_not_dvd_sub {N r s : ℕ} (hN : 4 ≤ N)
    (hr : r ∈ frequencySet N) (hs : s ∈ frequencySet N) (hsr : s < r) :
    ¬N ∣ r - s := by
  apply not_dvd_of_pos_of_lt
  · omega
  · have hrN := frequencySet_le_quarter hr
    have hr4 : r * 4 ≤ N := (Nat.le_div_iff_mul_le (by omega)).mp hrN
    omega

lemma sum_add_sq {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b : ι → ℝ) :
    ∑ k ∈ s, (a k + b k) ^ 2 =
      (∑ k ∈ s, a k ^ 2) + (∑ k ∈ s, b k ^ 2) +
        2 * ∑ k ∈ s, a k * b k := by
  calc
    ∑ k ∈ s, (a k + b k) ^ 2 =
        ∑ k ∈ s, (a k ^ 2 + b k ^ 2 + 2 * (a k * b k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (∑ k ∈ s, a k ^ 2) + (∑ k ∈ s, b k ^ 2) +
          2 * ∑ k ∈ s, a k * b k := by
      simp_rw [Finset.sum_add_distrib, Finset.mul_sum]

lemma sum_two_rootRealProjection_coeff_sq (N r s : ℕ) (hN : 4 ≤ N)
    (hr : r ∈ frequencySet N) (hs : s ∈ frequencySet N) (hrs : r ≠ s) :
    ∑ k ∈ Finset.range N,
        ((standardRoot N ^ (r * k)).re + (standardRoot N ^ (s * k)).re) ^ 2 = N := by
  have hN0 : N ≠ 0 := by omega
  have hrr := frequencySet_not_dvd_two_mul hN hr
  have hss := frequencySet_not_dvd_two_mul hN hs
  have hplus := frequencySet_not_dvd_add hN hr hs
  by_cases hsr : s ≤ r
  · have hsr' : s < r := lt_of_le_of_ne hsr (Ne.symm hrs)
    have hminus := frequencySet_not_dvd_sub hN hr hs hsr'
    have hcross := sum_standardRoot_pow_re_mul_re N r s hN0 hsr hplus hminus
    calc
      ∑ k ∈ Finset.range N,
          ((standardRoot N ^ (r * k)).re + (standardRoot N ^ (s * k)).re) ^ 2 =
          (∑ k ∈ Finset.range N, (standardRoot N ^ (r * k)).re ^ 2) +
            (∑ k ∈ Finset.range N, (standardRoot N ^ (s * k)).re ^ 2) +
              2 * ∑ k ∈ Finset.range N,
                (standardRoot N ^ (r * k)).re * (standardRoot N ^ (s * k)).re := by
        exact sum_add_sq (Finset.range N) _ _
      _ = (N : ℝ) := by
        rw [sum_standardRoot_pow_re_sq N r hN0 hrr,
          sum_standardRoot_pow_re_sq N s hN0 hss, hcross]
        ring
  · have hrsle : r ≤ s := le_of_not_ge hsr
    have hrs' : r < s := lt_of_le_of_ne hrsle hrs
    have hminus := frequencySet_not_dvd_sub hN hs hr hrs'
    have hcross := sum_standardRoot_pow_re_mul_re N s r hN0 hrsle
      (by simpa [add_comm] using hplus) hminus
    calc
      ∑ k ∈ Finset.range N,
          ((standardRoot N ^ (r * k)).re + (standardRoot N ^ (s * k)).re) ^ 2 =
          (∑ k ∈ Finset.range N, (standardRoot N ^ (r * k)).re ^ 2) +
            (∑ k ∈ Finset.range N, (standardRoot N ^ (s * k)).re ^ 2) +
              2 * ∑ k ∈ Finset.range N,
                (standardRoot N ^ (r * k)).re * (standardRoot N ^ (s * k)).re := by
        exact sum_add_sq (Finset.range N) _ _
      _ = (N : ℝ) := by
        rw [sum_standardRoot_pow_re_sq N r hN0 hrr,
          sum_standardRoot_pow_re_sq N s hN0 hss]
        rw [show (∑ k ∈ Finset.range N,
            (standardRoot N ^ (r * k)).re * (standardRoot N ^ (s * k)).re) = 0 by
          simpa only [mul_comm] using hcross]
        ring

/-- For two distinct frequencies in `frequencySet`, simultaneous real-part exceedance has the
square-scale Hoeffding bound required in the lower-bound second-moment argument. -/
lemma measureReal_two_rootRealProjection_ge_le (N r s : ℕ) (hN : 4 ≤ N)
    (hr : r ∈ frequencySet N) (hs : s ∈ frequencySet N) (hrs : r ≠ s)
    {u : ℝ} (hu : 0 ≤ u) :
    signMeasure.real {ω | u ≤ rootRealProjection ω N r ∧
      u ≤ rootRealProjection ω N s} ≤
      Real.exp (-2 * u ^ 2 / (N : ℝ)) := by
  let a : ℕ → ℝ := fun k ↦
    (standardRoot N ^ (r * k)).re + (standardRoot N ^ (s * k)).re
  have hsum : ∑ k ∈ Finset.range N, a k ^ 2 = (N : ℝ) := by
    exact sum_two_rootRealProjection_coeff_sq N r s hN hr hs hrs
  have hsubset :
      {ω | u ≤ rootRealProjection ω N r ∧ u ≤ rootRealProjection ω N s} ⊆
        {ω | 2 * u ≤ linearForm (Finset.range N) a ω} := by
    intro ω hω
    change u ≤ rootRealProjection ω N r ∧ u ≤ rootRealProjection ω N s at hω
    change 2 * u ≤ linearForm (Finset.range N) a ω
    have hadd : rootRealProjection ω N r + rootRealProjection ω N s =
        linearForm (Finset.range N) a ω := by
      unfold rootRealProjection linearForm a
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _hk
      ring
    rw [← hadd]
    linarith [hω.1, hω.2]
  calc
    signMeasure.real {ω | u ≤ rootRealProjection ω N r ∧
        u ≤ rootRealProjection ω N s} ≤
        signMeasure.real {ω | 2 * u ≤ linearForm (Finset.range N) a ω} :=
      measureReal_mono hsubset
    _ ≤ Real.exp (-(2 * u) ^ 2 /
        (2 * ∑ k ∈ Finset.range N, a k ^ 2)) := by
      exact measureReal_linearForm_ge_le (Finset.range N) a (by positivity)
    _ = Real.exp (-2 * u ^ 2 / (N : ℝ)) := by
      rw [hsum]
      congr 1
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
      field_simp

lemma measureReal_rootRealProjection_ge_le (N r : ℕ) (hN : 4 ≤ N)
    (hr : r ∈ frequencySet N) {u : ℝ} (hu : 0 ≤ u) :
    signMeasure.real {ω | u ≤ rootRealProjection ω N r} ≤
      Real.exp (-u ^ 2 / (N : ℝ)) := by
  let a : ℕ → ℝ := fun k ↦ (standardRoot N ^ (r * k)).re
  have hN0 : N ≠ 0 := by omega
  have hsum : ∑ k ∈ Finset.range N, a k ^ 2 = (N : ℝ) / 2 := by
    exact sum_standardRoot_pow_re_sq N r hN0 (frequencySet_not_dvd_two_mul hN hr)
  calc
    signMeasure.real {ω | u ≤ rootRealProjection ω N r} ≤
        Real.exp (-u ^ 2 / (2 * ∑ k ∈ Finset.range N, a k ^ 2)) := by
      simpa only [rootRealProjection, linearForm, a] using
        (measureReal_linearForm_ge_le (Finset.range N) a hu)
    _ = Real.exp (-u ^ 2 / (N : ℝ)) := by rw [hsum]; ring_nf

/-- The explicit one-frequency lower tail obtained from the exponential tilt.  The hypotheses
expose exactly the two elementary centering inequalities later discharged by the asymptotic
choice of the tilt and window. -/
lemma measureReal_rootRealProjection_ge_lower_tilt (N r : ℕ) (hN : 4 ≤ N)
    (hrfreq : r ∈ frequencySet N) {t u B ρ : ℝ}
    (ht : 0 ≤ t) (hρ : 0 < ρ) (hq : (N : ℝ) / 2 ≤ ρ ^ 2)
    (hcenter_lower :
      u + ρ ≤ t * ((N : ℝ) / 2) - t ^ 3 * ((N : ℝ) / 2))
    (hcenter_upper : t * ((N : ℝ) / 2) + ρ ≤ B) :
    Real.exp (-t * B + (t ^ 2 * (N : ℝ) / 4 - t ^ 4 * (N : ℝ) / 8)) *
        (1 - ((N : ℝ) / 2) / ρ ^ 2) ≤
      signMeasure.real {ω | u ≤ rootRealProjection ω N r} := by
  let a : ℕ → ℝ := fun k ↦ (standardRoot N ^ (r * k)).re
  have hN0 : N ≠ 0 := by omega
  have hr : ¬N ∣ 2 * r := frequencySet_not_dvd_two_mul hN hrfreq
  have hsquare : ∑ k ∈ Finset.range N, a k ^ 2 = (N : ℝ) / 2 := by
    exact sum_standardRoot_pow_re_sq N r hN0 hr
  have hfourth : ∑ k ∈ Finset.range N, a k ^ 4 ≤ (N : ℝ) / 2 := by
    exact (sum_standardRoot_pow_re_fourth_le N r).trans_eq hsquare
  have ht3 : 0 ≤ t ^ 3 := by positivity
  have hcenter_lower' :
      u + ρ ≤ t * (∑ k ∈ Finset.range N, a k ^ 2) -
        t ^ 3 * (∑ k ∈ Finset.range N, a k ^ 4) := by
    rw [hsquare]
    calc
      u + ρ ≤ t * ((N : ℝ) / 2) - t ^ 3 * ((N : ℝ) / 2) := hcenter_lower
      _ ≤ t * ((N : ℝ) / 2) -
          t ^ 3 * (∑ k ∈ Finset.range N, a k ^ 4) := by gcongr
  have hcenter_upper' :
      t * (∑ k ∈ Finset.range N, a k ^ 2) + ρ ≤ B := by
    simpa only [hsquare] using hcenter_upper
  have htilt := measureReal_linearForm_ge_lower_tilt (Finset.range N) a ht hρ
    hcenter_lower' hcenter_upper'
  have hcgf := cgf_rootRealProjection_lower N r t hN0 hr
  have hfactor : 0 ≤ 1 - ((N : ℝ) / 2) / ρ ^ 2 := by
    have hρ2 : 0 < ρ ^ 2 := sq_pos_of_pos hρ
    rw [sub_nonneg, div_le_one hρ2]
    exact hq
  calc
    Real.exp (-t * B + (t ^ 2 * (N : ℝ) / 4 - t ^ 4 * (N : ℝ) / 8)) *
        (1 - ((N : ℝ) / 2) / ρ ^ 2) ≤
        Real.exp (-t * B + cgf (rootRealProjection · N r) signMeasure t) *
          (1 - ((N : ℝ) / 2) / ρ ^ 2) := by
      gcongr
    _ ≤ signMeasure.real {ω | u ≤ rootRealProjection ω N r} := by
      simpa only [a, rootRealProjection, hsquare] using htilt

/-! ## The finite second-moment argument -/

/-- A convenient real-valued second-moment inequality.  It is the `θ = 0` case of the
Paley--Zygmund principle, written in a form that follows directly from Chebyshev and is suited to
finite sums of indicators. -/
lemma measureReal_pos_ge_two_sub_secondMoment_div_mean_sq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) (hLp : MemLp X 2 μ)
    (hXnonneg : ∀ ω, 0 ≤ X ω) (hmean : 0 < ∫ ω, X ω ∂μ) :
    2 - (∫ ω, X ω ^ 2 ∂μ) / (∫ ω, X ω ∂μ) ^ 2 ≤
      μ.real {ω | 0 < X ω} := by
  let m : ℝ := ∫ ω, X ω ∂μ
  let Z : Set Ω := {ω | X ω = 0}
  let P : Set Ω := {ω | 0 < X ω}
  have hm : 0 < m := by simpa only [m] using hmean
  have hP : MeasurableSet P := measurableSet_lt measurable_const hX
  have hcomp : Z = Pᶜ := by
    ext ω
    simp only [Z, P, Set.mem_ofPred_eq, Set.mem_compl_iff]
    constructor
    · intro hz hp
      rw [hz] at hp
      exact (lt_irrefl 0 hp)
    · intro hp
      have hnonneg := hXnonneg ω
      simp only [not_lt] at hp
      linarith
  have hsubset : Z ⊆ {ω | m ≤ |X ω - m|} := by
    intro ω hω
    change X ω = 0 at hω
    change m ≤ |X ω - m|
    rw [hω, zero_sub, abs_neg, abs_of_pos hm]
  have hcheb := meas_ge_le_variance_div_sq hLp hm
  have hchebReal : μ.real {ω | m ≤ |X ω - m|} ≤ Var[X; μ] / m ^ 2 := by
    rw [measureReal_def]
    calc
      (μ {ω | m ≤ |X ω - m|}).toReal ≤
          (ENNReal.ofReal (Var[X; μ] / m ^ 2)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb
      _ = Var[X; μ] / m ^ 2 := by
        rw [ENNReal.toReal_ofReal]
        exact div_nonneg (variance_nonneg _ _) (sq_nonneg _)
  have hzero : μ.real Z ≤ Var[X; μ] / m ^ 2 :=
    (measureReal_mono hsubset).trans hchebReal
  have hvar : Var[X; μ] = (∫ ω, X ω ^ 2 ∂μ) - m ^ 2 := by
    change Var[X; μ] = (∫ ω, (X ^ 2) ω ∂μ) - m ^ 2
    simpa only [m] using (variance_eq_sub (μ := μ) (X := X) hLp)
  have hpos : μ.real P = 1 - μ.real Z := by
    have hz := measureReal_compl (μ := μ) hP
    rw [probReal_univ] at hz
    rw [← hcomp] at hz
    linarith
  rw [hvar] at hzero
  rw [show (∫ ω, X ω ∂μ) = m by rfl, show {ω | 0 < X ω} = P by rfl, hpos]
  have hm2 : 0 < m ^ 2 := sq_pos_of_pos hm
  have hzero' : μ.real Z ≤ (∫ ω, X ω ^ 2 ∂μ) / m ^ 2 - 1 := by
    calc
      μ.real Z ≤ ((∫ ω, X ω ^ 2 ∂μ) - m ^ 2) / m ^ 2 := hzero
      _ = (∫ ω, X ω ^ 2 ∂μ) / m ^ 2 - 1 := by field_simp
  linarith

def rootExceedanceEvent (N r : ℕ) (u : ℝ) : Set Sample :=
  {ω | u ≤ rootRealProjection ω N r}

def rootExceedanceCount (N : ℕ) (u : ℝ) (ω : Sample) : ℝ :=
  ∑ r ∈ frequencySet N,
    (rootExceedanceEvent N r u).indicator (fun _ ↦ (1 : ℝ)) ω

lemma measurableSet_rootExceedanceEvent (N r : ℕ) (u : ℝ) :
    MeasurableSet (rootExceedanceEvent N r u) := by
  exact measurableSet_le measurable_const (measurable_rootRealProjection N r)

lemma measurable_rootExceedanceCount (N : ℕ) (u : ℝ) :
    Measurable (rootExceedanceCount N u) := by
  unfold rootExceedanceCount
  apply Finset.measurable_sum
  intro r _hr
  exact measurable_const.indicator (measurableSet_rootExceedanceEvent N r u)

lemma rootExceedanceCount_nonneg (N : ℕ) (u : ℝ) (ω : Sample) :
    0 ≤ rootExceedanceCount N u ω := by
  unfold rootExceedanceCount
  apply Finset.sum_nonneg
  intro r _hr
  by_cases h : ω ∈ rootExceedanceEvent N r u <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]

lemma rootExceedanceCount_le_card (N : ℕ) (u : ℝ) (ω : Sample) :
    rootExceedanceCount N u ω ≤ (frequencySet N).card := by
  unfold rootExceedanceCount
  calc
    ∑ r ∈ frequencySet N,
        (rootExceedanceEvent N r u).indicator (fun _ ↦ (1 : ℝ)) ω ≤
        ∑ _r ∈ frequencySet N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro r _hr
      by_cases h : ω ∈ rootExceedanceEvent N r u <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
    _ = (frequencySet N).card := by simp

lemma rootExceedanceCount_memLp_two (N : ℕ) (u : ℝ) :
    MemLp (rootExceedanceCount N u) 2 signMeasure := by
  apply memLp_of_bounded
    (show ∀ᵐ ω ∂signMeasure,
      rootExceedanceCount N u ω ∈ Icc 0 ((frequencySet N).card : ℝ) from
      ae_of_all _ fun ω ↦ ⟨rootExceedanceCount_nonneg N u ω,
        rootExceedanceCount_le_card N u ω⟩)
  exact (measurable_rootExceedanceCount N u).aestronglyMeasurable

lemma integral_rootExceedanceCount (N : ℕ) (u : ℝ) :
    ∫ ω, rootExceedanceCount N u ω ∂signMeasure =
      ∑ r ∈ frequencySet N, signMeasure.real (rootExceedanceEvent N r u) := by
  unfold rootExceedanceCount
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro r _hr
    exact integral_indicator_one (measurableSet_rootExceedanceEvent N r u)
  · intro r _hr
    exact (integrable_const (μ := signMeasure) (1 : ℝ)).indicator
      (measurableSet_rootExceedanceEvent N r u)

lemma rootExceedanceCount_sq_eq_sum_intersections (N : ℕ) (u : ℝ) (ω : Sample) :
    rootExceedanceCount N u ω ^ 2 =
      ∑ r ∈ frequencySet N, ∑ s ∈ frequencySet N,
        ((rootExceedanceEvent N r u) ∩ (rootExceedanceEvent N s u)).indicator
          (fun _ ↦ (1 : ℝ)) ω := by
  unfold rootExceedanceCount
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _hs
  by_cases hrω : ω ∈ rootExceedanceEvent N r u <;>
    by_cases hsω : ω ∈ rootExceedanceEvent N s u <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hrω, hsω]

lemma integral_rootExceedanceCount_sq (N : ℕ) (u : ℝ) :
    ∫ ω, rootExceedanceCount N u ω ^ 2 ∂signMeasure =
      ∑ r ∈ frequencySet N, ∑ s ∈ frequencySet N,
        signMeasure.real ((rootExceedanceEvent N r u) ∩
          (rootExceedanceEvent N s u)) := by
  calc
    ∫ ω, rootExceedanceCount N u ω ^ 2 ∂signMeasure =
        ∫ ω, ∑ r ∈ frequencySet N, ∑ s ∈ frequencySet N,
          ((rootExceedanceEvent N r u) ∩ (rootExceedanceEvent N s u)).indicator
            (fun _ ↦ (1 : ℝ)) ω ∂signMeasure := by
      apply integral_congr_ae
      exact ae_of_all _ (rootExceedanceCount_sq_eq_sum_intersections N u)
    _ = ∑ r ∈ frequencySet N, ∑ s ∈ frequencySet N,
        signMeasure.real ((rootExceedanceEvent N r u) ∩
          (rootExceedanceEvent N s u)) := by
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro r _hr
        rw [integral_finset_sum]
        · apply Finset.sum_congr rfl
          intro s _hs
          exact integral_indicator_one
            ((measurableSet_rootExceedanceEvent N r u).inter
              (measurableSet_rootExceedanceEvent N s u))
        · intro s _hs
          exact (integrable_const (μ := signMeasure) (1 : ℝ)).indicator
            ((measurableSet_rootExceedanceEvent N r u).inter
              (measurableSet_rootExceedanceEvent N s u))
      · intro r _hr
        apply integrable_finset_sum
        intro s _hs
        exact (integrable_const (μ := signMeasure) (1 : ℝ)).indicator
          ((measurableSet_rootExceedanceEvent N r u).inter
            (measurableSet_rootExceedanceEvent N s u))

lemma integral_rootExceedanceCount_sq_le (N : ℕ) (hN : 4 ≤ N) {u : ℝ}
    (hu : 0 ≤ u) :
    ∫ ω, rootExceedanceCount N u ω ^ 2 ∂signMeasure ≤
      ((frequencySet N).card : ℝ) * Real.exp (-u ^ 2 / (N : ℝ)) +
        ((frequencySet N).card : ℝ) ^ 2 * Real.exp (-u ^ 2 / (N : ℝ)) ^ 2 := by
  let q : ℝ := Real.exp (-u ^ 2 / (N : ℝ))
  rw [integral_rootExceedanceCount_sq]
  calc
    ∑ r ∈ frequencySet N, ∑ s ∈ frequencySet N,
        signMeasure.real (rootExceedanceEvent N r u ∩ rootExceedanceEvent N s u) ≤
        ∑ _r ∈ frequencySet N,
          (q + ((frequencySet N).card : ℝ) * q ^ 2) := by
      apply Finset.sum_le_sum
      intro r hr
      calc
        ∑ s ∈ frequencySet N,
            signMeasure.real (rootExceedanceEvent N r u ∩ rootExceedanceEvent N s u) ≤
            ∑ s ∈ frequencySet N, (q ^ 2 + if s = r then q else 0) := by
          apply Finset.sum_le_sum
          intro s hs
          by_cases hrs : s = r
          · subst s
            rw [Set.inter_self, if_pos rfl]
            have hsingle : signMeasure.real (rootExceedanceEvent N r u) ≤ q := by
              simpa only [rootExceedanceEvent, q] using
                (measureReal_rootRealProjection_ge_le N r hN hr hu)
            nlinarith [sq_nonneg q]
          · simp only [if_neg hrs, add_zero]
            have hpair :
                signMeasure.real (rootExceedanceEvent N r u ∩
                  rootExceedanceEvent N s u) ≤ Real.exp (-2 * u ^ 2 / (N : ℝ)) := by
              simpa only [rootExceedanceEvent, Set.inter_def, Set.mem_ofPred_eq] using
                (measureReal_two_rootRealProjection_ge_le N r s hN hr hs (Ne.symm hrs) hu)
            calc
              signMeasure.real (rootExceedanceEvent N r u ∩
                  rootExceedanceEvent N s u) ≤ Real.exp (-2 * u ^ 2 / (N : ℝ)) := hpair
              _ = q ^ 2 := by
                dsimp [q]
                calc
                  Real.exp (-2 * u ^ 2 / (N : ℝ)) =
                      Real.exp (-u ^ 2 / (N : ℝ) + -u ^ 2 / (N : ℝ)) := by
                    congr 1
                    ring
                  _ = Real.exp (-u ^ 2 / (N : ℝ)) *
                      Real.exp (-u ^ 2 / (N : ℝ)) := Real.exp_add _ _
                  _ = Real.exp (-u ^ 2 / (N : ℝ)) ^ 2 := by ring
        _ = q + ((frequencySet N).card : ℝ) * q ^ 2 := by
          rw [Finset.sum_add_distrib]
          simp [hr]
          ring
    _ = ((frequencySet N).card : ℝ) * Real.exp (-u ^ 2 / (N : ℝ)) +
        ((frequencySet N).card : ℝ) ^ 2 * Real.exp (-u ^ 2 / (N : ℝ)) ^ 2 := by
      dsimp [q]
      simp
      ring

lemma frequencySet_nonempty {N : ℕ} (hN : 4 ≤ N) : (frequencySet N).Nonempty := by
  refine ⟨1, ?_⟩
  change 1 ∈ Finset.Icc 1 (N / 4)
  rw [Finset.mem_Icc]
  constructor
  · rfl
  · exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2 (by simpa using hN)

lemma integral_rootExceedanceCount_ge_card_mul (N : ℕ) (u p : ℝ)
    (hprob : ∀ r ∈ frequencySet N,
      p ≤ signMeasure.real (rootExceedanceEvent N r u)) :
    ((frequencySet N).card : ℝ) * p ≤
      ∫ ω, rootExceedanceCount N u ω ∂signMeasure := by
  rw [integral_rootExceedanceCount]
  calc
    ((frequencySet N).card : ℝ) * p = ∑ _r ∈ frequencySet N, p := by simp
    _ ≤ ∑ r ∈ frequencySet N,
        signMeasure.real (rootExceedanceEvent N r u) := by
      exact Finset.sum_le_sum fun r hr ↦ hprob r hr

/-- Quantitative finite lower bound for the probability that at least one selected root has real
part above `u`.  The lower input `p` will be supplied by the tilt estimate, while the displayed
upper expression comes from exact Fourier orthogonality and Hoeffding. -/
lemma measureReal_rootExceedanceCount_pos_ge (N : ℕ) (hN : 4 ≤ N) {u p : ℝ}
    (hu : 0 ≤ u) (hp : 0 < p)
    (hprob : ∀ r ∈ frequencySet N,
      p ≤ signMeasure.real (rootExceedanceEvent N r u)) :
    2 -
        (((frequencySet N).card : ℝ) * Real.exp (-u ^ 2 / (N : ℝ)) +
          ((frequencySet N).card : ℝ) ^ 2 * Real.exp (-u ^ 2 / (N : ℝ)) ^ 2) /
          (((frequencySet N).card : ℝ) * p) ^ 2 ≤
      signMeasure.real {ω | 0 < rootExceedanceCount N u ω} := by
  let L : ℝ := ((frequencySet N).card : ℝ) * p
  let M : ℝ := ∫ ω, rootExceedanceCount N u ω ∂signMeasure
  let A : ℝ :=
    ((frequencySet N).card : ℝ) * Real.exp (-u ^ 2 / (N : ℝ)) +
      ((frequencySet N).card : ℝ) ^ 2 * Real.exp (-u ^ 2 / (N : ℝ)) ^ 2
  have hcard : 0 < ((frequencySet N).card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr (frequencySet_nonempty hN))
  have hL : 0 < L := by dsimp [L]; positivity
  have hLM : L ≤ M := by
    simpa only [L, M] using integral_rootExceedanceCount_ge_card_mul N u p hprob
  have hM : 0 < M := hL.trans_le hLM
  have hsecond :
      ∫ ω, rootExceedanceCount N u ω ^ 2 ∂signMeasure ≤ A := by
    simpa only [A] using integral_rootExceedanceCount_sq_le N hN hu
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hratio :
      (∫ ω, rootExceedanceCount N u ω ^ 2 ∂signMeasure) / M ^ 2 ≤ A / L ^ 2 := by
    apply div_le_div₀ hA hsecond (sq_pos_of_pos hL)
    nlinarith
  have hpaley := measureReal_pos_ge_two_sub_secondMoment_div_mean_sq
    signMeasure (measurable_rootExceedanceCount N u) (rootExceedanceCount_memLp_two N u)
      (rootExceedanceCount_nonneg N u) (by simpa only [M] using hM)
  change 2 - A / L ^ 2 ≤ signMeasure.real {ω | 0 < rootExceedanceCount N u ω}
  calc
    2 - A / L ^ 2 ≤
        2 - (∫ ω, rootExceedanceCount N u ω ^ 2 ∂signMeasure) / M ^ 2 := by
      linarith
    _ ≤ signMeasure.real {ω | 0 < rootExceedanceCount N u ω} := by
      simpa only [M] using hpaley

/-! ## A quantitative Lindeberg comparison for maxima of projections -/

def affineMomentSum {ι : Type*} (s : Finset ι) (β : ℝ)
    (a b : ι → ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ s, Real.exp (β * (b i + a i * x)) * a i ^ m

def affineLogSumExp {ι : Type*} (s : Finset ι) (β : ℝ)
    (a b : ι → ℝ) (x : ℝ) : ℝ :=
  Real.log (affineMomentSum s β a b 0 x) / β

lemma affineMomentSum_zero_pos {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (β : ℝ) (a b : ι → ℝ) (x : ℝ) :
    0 < affineMomentSum s β a b 0 x := by
  unfold affineMomentSum
  apply Finset.sum_pos
  · intro i hi
    positivity
  · exact hs

lemma hasDerivAt_affineMomentSum {ι : Type*} (s : Finset ι) (β : ℝ)
    (a b : ι → ℝ) (m : ℕ) (x : ℝ) :
    HasDerivAt (affineMomentSum s β a b m)
      (β * affineMomentSum s β a b (m + 1) x) x := by
  unfold affineMomentSum
  have hsum : HasDerivAt
      (fun y : ℝ ↦ ∑ i ∈ s, Real.exp (β * (b i + a i * y)) * a i ^ m)
      (∑ i ∈ s, β * Real.exp (β * (b i + a i * x)) * a i ^ (m + 1)) x := by
    apply HasDerivAt.fun_sum
    intro i _hi
    have hlinear : HasDerivAt (fun y : ℝ ↦ b i + a i * y) (a i) x := by
      exact (hasDerivAt_const_mul (x := x) (a i)).const_add (b i)
    have hinner : HasDerivAt (fun y : ℝ ↦ β * (b i + a i * y)) (β * a i) x :=
      hlinear.const_mul β
    have hraw := hinner.exp.mul_const (a i ^ m)
    apply hraw.congr_deriv
    rw [pow_succ']
    ring
  apply hsum.congr_deriv
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

def affineLogSumExpDerivOne {ι : Type*} (s : Finset ι) (β : ℝ)
    (a b : ι → ℝ) (x : ℝ) : ℝ :=
  affineMomentSum s β a b 1 x / affineMomentSum s β a b 0 x

def affineLogSumExpDerivTwo {ι : Type*} (s : Finset ι) (β : ℝ)
    (a b : ι → ℝ) (x : ℝ) : ℝ :=
  β * (affineMomentSum s β a b 2 x / affineMomentSum s β a b 0 x -
    (affineMomentSum s β a b 1 x / affineMomentSum s β a b 0 x) ^ 2)

def affineLogSumExpDerivThree {ι : Type*} (s : Finset ι) (β : ℝ)
    (a b : ι → ℝ) (x : ℝ) : ℝ :=
  β ^ 2 * (affineMomentSum s β a b 3 x / affineMomentSum s β a b 0 x -
    3 * affineMomentSum s β a b 1 x * affineMomentSum s β a b 2 x /
      affineMomentSum s β a b 0 x ^ 2 +
    2 * affineMomentSum s β a b 1 x ^ 3 / affineMomentSum s β a b 0 x ^ 3)

lemma hasDerivAt_affineLogSumExp {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {β : ℝ} (hβ : β ≠ 0) (a b : ι → ℝ) (x : ℝ) :
    HasDerivAt (affineLogSumExp s β a b)
      (affineLogSumExpDerivOne s β a b x) x := by
  have hpos := affineMomentSum_zero_pos hs β a b x
  have hsum := hasDerivAt_affineMomentSum s β a b 0 x
  have hlog := hsum.log (ne_of_gt hpos)
  unfold affineLogSumExp affineLogSumExpDerivOne
  apply (hlog.div_const β).congr_deriv
  field_simp

lemma hasDerivAt_affineLogSumExpDerivOne {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) (β : ℝ) (a b : ι → ℝ) (x : ℝ) :
    HasDerivAt (affineLogSumExpDerivOne s β a b)
      (affineLogSumExpDerivTwo s β a b x) x := by
  have hzero : affineMomentSum s β a b 0 x ≠ 0 :=
    ne_of_gt (affineMomentSum_zero_pos hs β a b x)
  have hnum := hasDerivAt_affineMomentSum s β a b 1 x
  have hden := hasDerivAt_affineMomentSum s β a b 0 x
  unfold affineLogSumExpDerivOne affineLogSumExpDerivTwo
  apply (hnum.div hden hzero).congr_deriv
  field_simp

lemma hasDerivAt_affineLogSumExpDerivTwo {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) (β : ℝ) (a b : ι → ℝ) (x : ℝ) :
    HasDerivAt (affineLogSumExpDerivTwo s β a b)
      (affineLogSumExpDerivThree s β a b x) x := by
  have hzero : affineMomentSum s β a b 0 x ≠ 0 :=
    ne_of_gt (affineMomentSum_zero_pos hs β a b x)
  have h0 := hasDerivAt_affineMomentSum s β a b 0 x
  have h1 := hasDerivAt_affineMomentSum s β a b 1 x
  have h2 := hasDerivAt_affineMomentSum s β a b 2 x
  have hratioTwo := h2.div h0 hzero
  have hratioOne := h1.div h0 hzero
  unfold affineLogSumExpDerivTwo affineLogSumExpDerivThree
  have hraw := (hratioTwo.sub (hratioOne.pow 2)).const_mul β
  apply hraw.congr_deriv
  simp only [Pi.div_apply, div_eq_mul_inv]
  field_simp [hzero]
  norm_num
  field_simp [hzero]
  ring

lemma abs_affineMomentSum_le {ι : Type*} {s : Finset ι} {β c : ℝ}
    {a b : ι → ℝ} (hc : 0 ≤ c) (ha : ∀ i ∈ s, |a i| ≤ c) (m : ℕ) (x : ℝ) :
    |affineMomentSum s β a b m x| ≤ c ^ m * affineMomentSum s β a b 0 x := by
  unfold affineMomentSum
  calc
    |∑ i ∈ s, Real.exp (β * (b i + a i * x)) * a i ^ m| ≤
        ∑ i ∈ s, |Real.exp (β * (b i + a i * x)) * a i ^ m| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, Real.exp (β * (b i + a i * x)) * |a i| ^ m := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
    _ ≤ ∑ i ∈ s, Real.exp (β * (b i + a i * x)) * c ^ m := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg (a i)) (ha i hi) m) (Real.exp_nonneg _)
    _ = c ^ m * ∑ i ∈ s, Real.exp (β * (b i + a i * x)) * a i ^ 0 := by
      simp only [pow_zero, mul_one]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring

lemma abs_affineMomentRatio_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {β c : ℝ} {a b : ι → ℝ} (hc : 0 ≤ c) (ha : ∀ i ∈ s, |a i| ≤ c)
    (m : ℕ) (x : ℝ) :
    |affineMomentSum s β a b m x / affineMomentSum s β a b 0 x| ≤ c ^ m := by
  have hpos := affineMomentSum_zero_pos hs β a b x
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  exact abs_affineMomentSum_le hc ha m x

lemma abs_affineLogSumExpDerivThree_le {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {β c : ℝ} {a b : ι → ℝ} (hc : 0 ≤ c)
    (ha : ∀ i ∈ s, |a i| ≤ c) (x : ℝ) :
    |affineLogSumExpDerivThree s β a b x| ≤ 6 * β ^ 2 * c ^ 3 := by
  have hzero : affineMomentSum s β a b 0 x ≠ 0 :=
    ne_of_gt (affineMomentSum_zero_pos hs β a b x)
  have h1 := abs_affineMomentRatio_le hs (β := β) (c := c) (a := a) (b := b) hc ha 1 x
  have h2 := abs_affineMomentRatio_le hs (β := β) (c := c) (a := a) (b := b) hc ha 2 x
  have h3 := abs_affineMomentRatio_le hs (β := β) (c := c) (a := a) (b := b) hc ha 3 x
  have h1' :
      |affineMomentSum s β a b 1 x / affineMomentSum s β a b 0 x| ≤ c := by
    simpa only [pow_one] using h1
  have h12 :
      |3 * affineMomentSum s β a b 1 x * affineMomentSum s β a b 2 x /
          affineMomentSum s β a b 0 x ^ 2| ≤ 3 * c ^ 3 := by
    have heq :
        3 * affineMomentSum s β a b 1 x * affineMomentSum s β a b 2 x /
            affineMomentSum s β a b 0 x ^ 2 =
          3 * (affineMomentSum s β a b 1 x / affineMomentSum s β a b 0 x) *
            (affineMomentSum s β a b 2 x / affineMomentSum s β a b 0 x) := by
      field_simp [hzero]
    rw [heq, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    calc
      3 * |affineMomentSum s β a b 1 x / affineMomentSum s β a b 0 x| *
          |affineMomentSum s β a b 2 x / affineMomentSum s β a b 0 x| ≤
          3 * c ^ 1 * c ^ 2 := by gcongr
      _ = 3 * c ^ 3 := by ring
  have h111 :
      |2 * affineMomentSum s β a b 1 x ^ 3 /
          affineMomentSum s β a b 0 x ^ 3| ≤ 2 * c ^ 3 := by
    have heq :
        2 * affineMomentSum s β a b 1 x ^ 3 /
            affineMomentSum s β a b 0 x ^ 3 =
          2 * (affineMomentSum s β a b 1 x /
            affineMomentSum s β a b 0 x) ^ 3 := by
      field_simp [hzero]
    rw [heq, abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    gcongr
  unfold affineLogSumExpDerivThree
  rw [abs_mul, abs_pow, sq_abs]
  have hinside :
      |affineMomentSum s β a b 3 x / affineMomentSum s β a b 0 x -
          3 * affineMomentSum s β a b 1 x * affineMomentSum s β a b 2 x /
            affineMomentSum s β a b 0 x ^ 2 +
          2 * affineMomentSum s β a b 1 x ^ 3 /
            affineMomentSum s β a b 0 x ^ 3| ≤ 6 * c ^ 3 := by
    calc
      |affineMomentSum s β a b 3 x / affineMomentSum s β a b 0 x -
          3 * affineMomentSum s β a b 1 x * affineMomentSum s β a b 2 x /
            affineMomentSum s β a b 0 x ^ 2 +
          2 * affineMomentSum s β a b 1 x ^ 3 /
            affineMomentSum s β a b 0 x ^ 3| ≤
          |affineMomentSum s β a b 3 x / affineMomentSum s β a b 0 x| +
            |3 * affineMomentSum s β a b 1 x * affineMomentSum s β a b 2 x /
              affineMomentSum s β a b 0 x ^ 2| +
            |2 * affineMomentSum s β a b 1 x ^ 3 /
              affineMomentSum s β a b 0 x ^ 3| := by
        calc
          |affineMomentSum s β a b 3 x / affineMomentSum s β a b 0 x -
              3 * affineMomentSum s β a b 1 x * affineMomentSum s β a b 2 x /
                affineMomentSum s β a b 0 x ^ 2 +
              2 * affineMomentSum s β a b 1 x ^ 3 /
                affineMomentSum s β a b 0 x ^ 3| ≤
              |affineMomentSum s β a b 3 x / affineMomentSum s β a b 0 x -
                3 * affineMomentSum s β a b 1 x * affineMomentSum s β a b 2 x /
                  affineMomentSum s β a b 0 x ^ 2| +
                |2 * affineMomentSum s β a b 1 x ^ 3 /
                affineMomentSum s β a b 0 x ^ 3| := abs_add_le _ _
          _ ≤ _ := by gcongr; exact abs_sub _ _
      _ ≤ c ^ 3 + 3 * c ^ 3 + 2 * c ^ 3 := by gcongr
      _ = 6 * c ^ 3 := by ring
  calc
    β ^ 2 *
        |affineMomentSum s β a b 3 x / affineMomentSum s β a b 0 x -
            3 * affineMomentSum s β a b 1 x * affineMomentSum s β a b 2 x /
              affineMomentSum s β a b 0 x ^ 2 +
            2 * affineMomentSum s β a b 1 x ^ 3 /
              affineMomentSum s β a b 0 x ^ 3| ≤
        β ^ 2 * (6 * c ^ 3) := mul_le_mul_of_nonneg_left hinside (sq_nonneg β)
    _ = 6 * β ^ 2 * c ^ 3 := by ring

lemma abs_affineLogSumExpDerivOne_le {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {β c : ℝ} {a b : ι → ℝ} (hc : 0 ≤ c)
    (ha : ∀ i ∈ s, |a i| ≤ c) (x : ℝ) :
    |affineLogSumExpDerivOne s β a b x| ≤ c := by
  unfold affineLogSumExpDerivOne
  simpa only [pow_one] using
    (abs_affineMomentRatio_le hs (β := β) (c := c) (a := a) (b := b) hc ha 1 x)

lemma abs_affineLogSumExpDerivTwo_le {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {β c : ℝ} {a b : ι → ℝ} (hβ : 0 ≤ β) (hc : 0 ≤ c)
    (ha : ∀ i ∈ s, |a i| ≤ c) (x : ℝ) :
    |affineLogSumExpDerivTwo s β a b x| ≤ 2 * β * c ^ 2 := by
  have h1 := abs_affineLogSumExpDerivOne_le hs (β := β) (c := c)
    (a := a) (b := b) hc ha x
  have h2 := abs_affineMomentRatio_le hs (β := β) (c := c) (a := a) (b := b) hc ha 2 x
  unfold affineLogSumExpDerivTwo
  rw [abs_mul, abs_of_nonneg hβ]
  calc
    β * |affineMomentSum s β a b 2 x / affineMomentSum s β a b 0 x -
        (affineMomentSum s β a b 1 x / affineMomentSum s β a b 0 x) ^ 2| ≤
        β * (|affineMomentSum s β a b 2 x / affineMomentSum s β a b 0 x| +
          |(affineMomentSum s β a b 1 x / affineMomentSum s β a b 0 x) ^ 2|) := by
      gcongr
      exact abs_sub _ _
    _ ≤ β * (c ^ 2 + c ^ 2) := by
      gcongr
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = 2 * β * c ^ 2 := by ring

def affineExpNegLogSumExp {ι : Type*} (s : Finset ι) (β γ : ℝ)
    (a b : ι → ℝ) (x : ℝ) : ℝ :=
  Real.exp (-γ * affineLogSumExp s β a b x)

def affineExpNegLogSumExpDerivOne {ι : Type*} (s : Finset ι) (β γ : ℝ)
    (a b : ι → ℝ) (x : ℝ) : ℝ :=
  -γ * affineLogSumExpDerivOne s β a b x * affineExpNegLogSumExp s β γ a b x

def affineExpNegLogSumExpDerivTwo {ι : Type*} (s : Finset ι) (β γ : ℝ)
    (a b : ι → ℝ) (x : ℝ) : ℝ :=
  (γ ^ 2 * affineLogSumExpDerivOne s β a b x ^ 2 -
    γ * affineLogSumExpDerivTwo s β a b x) * affineExpNegLogSumExp s β γ a b x

def affineExpNegLogSumExpDerivThree {ι : Type*} (s : Finset ι) (β γ : ℝ)
    (a b : ι → ℝ) (x : ℝ) : ℝ :=
  (-γ * affineLogSumExpDerivThree s β a b x +
      3 * γ ^ 2 * affineLogSumExpDerivOne s β a b x *
        affineLogSumExpDerivTwo s β a b x -
      γ ^ 3 * affineLogSumExpDerivOne s β a b x ^ 3) *
    affineExpNegLogSumExp s β γ a b x

lemma hasDerivAt_affineExpNegLogSumExp {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {β : ℝ} (hβ : β ≠ 0) (γ : ℝ) (a b : ι → ℝ) (x : ℝ) :
    HasDerivAt (affineExpNegLogSumExp s β γ a b)
      (affineExpNegLogSumExpDerivOne s β γ a b x) x := by
  have hinner := (hasDerivAt_affineLogSumExp hs hβ a b x).const_mul (-γ)
  unfold affineExpNegLogSumExp affineExpNegLogSumExpDerivOne
  apply hinner.exp.congr_deriv
  simp only [affineExpNegLogSumExp]
  ring

lemma hasDerivAt_affineExpNegLogSumExpDerivOne {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {β : ℝ} (hβ : β ≠ 0) (γ : ℝ) (a b : ι → ℝ) (x : ℝ) :
    HasDerivAt (affineExpNegLogSumExpDerivOne s β γ a b)
      (affineExpNegLogSumExpDerivTwo s β γ a b x) x := by
  have h1 := hasDerivAt_affineLogSumExpDerivOne hs β a b x
  have he := hasDerivAt_affineExpNegLogSumExp hs hβ γ a b x
  unfold affineExpNegLogSumExpDerivOne affineExpNegLogSumExpDerivTwo
  have hraw := ((h1.const_mul (-γ)).mul he)
  apply hraw.congr_deriv
  simp only [affineExpNegLogSumExpDerivOne, affineExpNegLogSumExp]
  ring

lemma hasDerivAt_affineExpNegLogSumExpDerivTwo {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {β : ℝ} (hβ : β ≠ 0) (γ : ℝ) (a b : ι → ℝ) (x : ℝ) :
    HasDerivAt (affineExpNegLogSumExpDerivTwo s β γ a b)
      (affineExpNegLogSumExpDerivThree s β γ a b x) x := by
  have h1 := hasDerivAt_affineLogSumExpDerivOne hs β a b x
  have h2 := hasDerivAt_affineLogSumExpDerivTwo hs β a b x
  have he := hasDerivAt_affineExpNegLogSumExp hs hβ γ a b x
  have hcoef := ((h1.pow 2).const_mul (γ ^ 2)).sub (h2.const_mul γ)
  unfold affineExpNegLogSumExpDerivTwo affineExpNegLogSumExpDerivThree
  have hraw := hcoef.mul he
  apply hraw.congr_deriv
  simp only [Pi.sub_apply, Pi.pow_apply, affineExpNegLogSumExpDerivOne,
    affineExpNegLogSumExp]
  norm_num
  ring

lemma abs_affineExpNegLogSumExpDerivThree_le {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {β γ c : ℝ} {a b : ι → ℝ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hc : 0 ≤ c) (ha : ∀ i ∈ s, |a i| ≤ c) (x : ℝ)
    (hL : 0 ≤ affineLogSumExp s β a b x) :
    |affineExpNegLogSumExpDerivThree s β γ a b x| ≤
      (γ ^ 3 + 6 * γ ^ 2 * β + 6 * γ * β ^ 2) * c ^ 3 := by
  have h1 := abs_affineLogSumExpDerivOne_le hs (β := β) (c := c)
    (a := a) (b := b) hc ha x
  have h2 := abs_affineLogSumExpDerivTwo_le hs (β := β) (c := c)
    (a := a) (b := b) hβ hc ha x
  have h3 := abs_affineLogSumExpDerivThree_le hs (β := β) (c := c)
    (a := a) (b := b) hc ha x
  have hexp : affineExpNegLogSumExp s β γ a b x ≤ 1 := by
    unfold affineExpNegLogSumExp
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hexp0 : 0 ≤ affineExpNegLogSumExp s β γ a b x := by
    unfold affineExpNegLogSumExp
    positivity
  unfold affineExpNegLogSumExpDerivThree
  rw [abs_mul, abs_of_nonneg hexp0]
  calc
    |-γ * affineLogSumExpDerivThree s β a b x +
          3 * γ ^ 2 * affineLogSumExpDerivOne s β a b x *
            affineLogSumExpDerivTwo s β a b x -
          γ ^ 3 * affineLogSumExpDerivOne s β a b x ^ 3| *
        affineExpNegLogSumExp s β γ a b x ≤
      (γ * |affineLogSumExpDerivThree s β a b x| +
          3 * γ ^ 2 * |affineLogSumExpDerivOne s β a b x| *
            |affineLogSumExpDerivTwo s β a b x| +
          γ ^ 3 * |affineLogSumExpDerivOne s β a b x| ^ 3) *
        affineExpNegLogSumExp s β γ a b x := by
      gcongr
      calc
        |-γ * affineLogSumExpDerivThree s β a b x +
              3 * γ ^ 2 * affineLogSumExpDerivOne s β a b x *
                affineLogSumExpDerivTwo s β a b x -
              γ ^ 3 * affineLogSumExpDerivOne s β a b x ^ 3| ≤
            |-γ * affineLogSumExpDerivThree s β a b x +
              3 * γ ^ 2 * affineLogSumExpDerivOne s β a b x *
                affineLogSumExpDerivTwo s β a b x| +
              |γ ^ 3 * affineLogSumExpDerivOne s β a b x ^ 3| := abs_sub _ _
        _ ≤
            (|-γ * affineLogSumExpDerivThree s β a b x| +
              |3 * γ ^ 2 * affineLogSumExpDerivOne s β a b x *
                affineLogSumExpDerivTwo s β a b x|) +
              |γ ^ 3 * affineLogSumExpDerivOne s β a b x ^ 3| := by
          gcongr
          exact abs_add_le _ _
        _ = _ := by
          simp only [abs_mul, abs_pow, abs_neg, abs_of_nonneg hγ]
          norm_num
    _ ≤ (γ * (6 * β ^ 2 * c ^ 3) +
          3 * γ ^ 2 * c * (2 * β * c ^ 2) + γ ^ 3 * c ^ 3) * 1 := by
      gcongr
    _ = (γ ^ 3 + 6 * γ ^ 2 * β + 6 * γ * β ^ 2) * c ^ 3 := by ring

lemma contDiff_affineMomentSum {ι : Type*} (s : Finset ι) (β : ℝ)
    (a b : ι → ℝ) (m : ℕ) : ContDiff ℝ ⊤ (affineMomentSum s β a b m) := by
  unfold affineMomentSum
  fun_prop

lemma contDiff_affineLogSumExp {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {β : ℝ} (hβ : β ≠ 0) (a b : ι → ℝ) :
    ContDiff ℝ ⊤ (affineLogSumExp s β a b) := by
  unfold affineLogSumExp
  exact ((contDiff_affineMomentSum s β a b 0).log
    (fun x ↦ ne_of_gt (affineMomentSum_zero_pos hs β a b x))).div_const β

lemma contDiff_affineExpNegLogSumExp {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {β : ℝ} (hβ : β ≠ 0) (γ : ℝ) (a b : ι → ℝ) :
    ContDiff ℝ ⊤ (affineExpNegLogSumExp s β γ a b) := by
  unfold affineExpNegLogSumExp
  have hinner : ContDiff ℝ ⊤ (fun x ↦ -γ * affineLogSumExp s β a b x) :=
    contDiff_const.mul (contDiff_affineLogSumExp hs hβ a b)
  exact hinner.exp

lemma iteratedDeriv_three_affineExpNegLogSumExp {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {β : ℝ} (hβ : β ≠ 0) (γ : ℝ) (a b : ι → ℝ) (x : ℝ) :
    iteratedDeriv 3 (affineExpNegLogSumExp s β γ a b) x =
      affineExpNegLogSumExpDerivThree s β γ a b x := by
  have hd0 : deriv (affineExpNegLogSumExp s β γ a b) =
      affineExpNegLogSumExpDerivOne s β γ a b :=
    funext fun y ↦ (hasDerivAt_affineExpNegLogSumExp hs hβ γ a b y).deriv
  have hd1 : deriv (affineExpNegLogSumExpDerivOne s β γ a b) =
      affineExpNegLogSumExpDerivTwo s β γ a b :=
    funext fun y ↦ (hasDerivAt_affineExpNegLogSumExpDerivOne hs hβ γ a b y).deriv
  have hd2 : deriv (affineExpNegLogSumExpDerivTwo s β γ a b) =
      affineExpNegLogSumExpDerivThree s β γ a b :=
    funext fun y ↦ (hasDerivAt_affineExpNegLogSumExpDerivTwo hs hβ γ a b y).deriv
  rw [show (3 : ℕ) = 2 + 1 by norm_num, iteratedDeriv_succ,
    show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
    show (1 : ℕ) = 0 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_zero,
    hd0, hd1, hd2]

lemma iteratedDeriv_one_affineExpNegLogSumExp {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {β : ℝ} (hβ : β ≠ 0) (γ : ℝ) (a b : ι → ℝ) (x : ℝ) :
    iteratedDeriv 1 (affineExpNegLogSumExp s β γ a b) x =
      affineExpNegLogSumExpDerivOne s β γ a b x := by
  rw [show (1 : ℕ) = 0 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_zero,
    (hasDerivAt_affineExpNegLogSumExp hs hβ γ a b x).deriv]

lemma iteratedDeriv_two_affineExpNegLogSumExp {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {β : ℝ} (hβ : β ≠ 0) (γ : ℝ) (a b : ι → ℝ) (x : ℝ) :
    iteratedDeriv 2 (affineExpNegLogSumExp s β γ a b) x =
      affineExpNegLogSumExpDerivTwo s β γ a b x := by
  have hd0 : deriv (affineExpNegLogSumExp s β γ a b) =
      affineExpNegLogSumExpDerivOne s β γ a b :=
    funext fun y ↦ (hasDerivAt_affineExpNegLogSumExp hs hβ γ a b y).deriv
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
    show (1 : ℕ) = 0 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_zero,
    hd0, (hasDerivAt_affineExpNegLogSumExpDerivOne hs hβ γ a b x).deriv]

lemma abs_affineExpNegLogSumExp_taylor_le {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {β γ c : ℝ} (hβ : 0 < β) (hγ : 0 ≤ γ) {a b : ι → ℝ}
    (hc : 0 ≤ c) (ha : ∀ i ∈ s, |a i| ≤ c)
    (hL : ∀ y, 0 ≤ affineLogSumExp s β a b y) (x : ℝ) :
    |affineExpNegLogSumExp s β γ a b x -
        (affineExpNegLogSumExp s β γ a b 0 +
          affineExpNegLogSumExpDerivOne s β γ a b 0 * x +
          affineExpNegLogSumExpDerivTwo s β γ a b 0 * x ^ 2 / 2)| ≤
      (γ ^ 3 + 6 * γ ^ 2 * β + 6 * γ * β ^ 2) * c ^ 3 * |x| ^ 3 / 6 := by
  by_cases hx : x = 0
  · subst x
    simp
  have hx0 : (0 : ℝ) ≠ x := Ne.symm hx
  have hfull := contDiff_affineExpNegLogSumExp hs hβ.ne' γ a b
  have hf3 : ContDiffOn ℝ 3 (affineExpNegLogSumExp s β γ a b) (uIcc 0 x) :=
    (hfull.of_le (by simp)).contDiffOn
  obtain ⟨y, _hy, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) hx0 hf3
  have hu : UniqueDiffOn ℝ (uIcc (0 : ℝ) x) := uniqueDiffOn_uIcc hx0
  have hzero_mem : (0 : ℝ) ∈ uIcc 0 x := left_mem_uIcc
  have hi1 :
      iteratedDerivWithin 1 (affineExpNegLogSumExp s β γ a b) (uIcc 0 x) 0 =
        affineExpNegLogSumExpDerivOne s β γ a b 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu
      (hfull.contDiffAt.of_le (by simp)) hzero_mem]
    exact iteratedDeriv_one_affineExpNegLogSumExp hs hβ.ne' γ a b 0
  have hi2 :
      iteratedDerivWithin 2 (affineExpNegLogSumExp s β γ a b) (uIcc 0 x) 0 =
        affineExpNegLogSumExpDerivTwo s β γ a b 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu
      (hfull.contDiffAt.of_le (by simp)) hzero_mem]
    exact iteratedDeriv_two_affineExpNegLogSumExp hs hβ.ne' γ a b 0
  have htaylor :
      taylorWithinEval (affineExpNegLogSumExp s β γ a b) 2 (uIcc 0 x) 0 x =
        affineExpNegLogSumExp s β γ a b 0 +
          affineExpNegLogSumExpDerivOne s β γ a b 0 * x +
          affineExpNegLogSumExpDerivTwo s β γ a b 0 * x ^ 2 / 2 := by
    norm_num [taylorWithinEval_succ, smul_eq_mul, hi1, hi2]
    ring
  have hiter :
      iteratedDeriv 3 (affineExpNegLogSumExp s β γ a b) y =
        affineExpNegLogSumExpDerivThree s β γ a b y :=
    iteratedDeriv_three_affineExpNegLogSumExp hs hβ.ne' γ a b y
  rw [htaylor, hiter] at hrem
  rw [hrem, abs_div, abs_mul, abs_pow]
  norm_num [Nat.factorial]
  have hthird := abs_affineExpNegLogSumExpDerivThree_le hs hβ.le hγ hc ha y (hL y)
  calc
    |affineExpNegLogSumExpDerivThree s β γ a b y| * |x| ^ 3 / 6 ≤
        ((γ ^ 3 + 6 * γ ^ 2 * β + 6 * γ * β ^ 2) * c ^ 3) * |x| ^ 3 / 6 := by
      gcongr
    _ = (γ ^ 3 + 6 * γ ^ 2 * β + 6 * γ * β ^ 2) * c ^ 3 * |x| ^ 3 / 6 := by
      ring

lemma iteratedDeriv_three_affineLogSumExp {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {β : ℝ} (hβ : β ≠ 0) (a b : ι → ℝ) (x : ℝ) :
    iteratedDeriv 3 (affineLogSumExp s β a b) x =
      affineLogSumExpDerivThree s β a b x := by
  have hd0 : deriv (affineLogSumExp s β a b) = affineLogSumExpDerivOne s β a b :=
    funext fun y ↦ (hasDerivAt_affineLogSumExp hs hβ a b y).deriv
  have hd1 : deriv (affineLogSumExpDerivOne s β a b) =
      affineLogSumExpDerivTwo s β a b :=
    funext fun y ↦ (hasDerivAt_affineLogSumExpDerivOne hs β a b y).deriv
  have hd2 : deriv (affineLogSumExpDerivTwo s β a b) =
      affineLogSumExpDerivThree s β a b :=
    funext fun y ↦ (hasDerivAt_affineLogSumExpDerivTwo hs β a b y).deriv
  rw [show (3 : ℕ) = 2 + 1 by norm_num, iteratedDeriv_succ,
    show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
    show (1 : ℕ) = 0 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_zero,
    hd0, hd1, hd2]

lemma iteratedDeriv_one_affineLogSumExp {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {β : ℝ} (hβ : β ≠ 0) (a b : ι → ℝ) (x : ℝ) :
    iteratedDeriv 1 (affineLogSumExp s β a b) x =
      affineLogSumExpDerivOne s β a b x := by
  rw [show (1 : ℕ) = 0 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_zero,
    (hasDerivAt_affineLogSumExp hs hβ a b x).deriv]

lemma iteratedDeriv_two_affineLogSumExp {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {β : ℝ} (hβ : β ≠ 0) (a b : ι → ℝ) (x : ℝ) :
    iteratedDeriv 2 (affineLogSumExp s β a b) x =
      affineLogSumExpDerivTwo s β a b x := by
  have hd0 : deriv (affineLogSumExp s β a b) = affineLogSumExpDerivOne s β a b :=
    funext fun y ↦ (hasDerivAt_affineLogSumExp hs hβ a b y).deriv
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
    show (1 : ℕ) = 0 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_zero,
    hd0, (hasDerivAt_affineLogSumExpDerivOne hs β a b x).deriv]

lemma abs_affineLogSumExp_taylor_le {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {β c : ℝ} (hβ : β ≠ 0) {a b : ι → ℝ} (hc : 0 ≤ c)
    (ha : ∀ i ∈ s, |a i| ≤ c) (x : ℝ) :
    |affineLogSumExp s β a b x -
        (affineLogSumExp s β a b 0 +
          affineLogSumExpDerivOne s β a b 0 * x +
          affineLogSumExpDerivTwo s β a b 0 * x ^ 2 / 2)| ≤
      β ^ 2 * c ^ 3 * |x| ^ 3 := by
  by_cases hx : x = 0
  · subst x
    simp
  have hx0 : (0 : ℝ) ≠ x := Ne.symm hx
  have hfull := contDiff_affineLogSumExp hs hβ a b
  have hf3 : ContDiffOn ℝ 3 (affineLogSumExp s β a b) (uIcc 0 x) :=
    (hfull.of_le (by simp)).contDiffOn
  obtain ⟨y, _hy, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) hx0 hf3
  have hu : UniqueDiffOn ℝ (uIcc (0 : ℝ) x) := uniqueDiffOn_uIcc hx0
  have hzero_mem : (0 : ℝ) ∈ uIcc 0 x := left_mem_uIcc
  have hi1 :
      iteratedDerivWithin 1 (affineLogSumExp s β a b) (uIcc 0 x) 0 =
        affineLogSumExpDerivOne s β a b 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu
      (hfull.contDiffAt.of_le (by simp)) hzero_mem]
    exact iteratedDeriv_one_affineLogSumExp hs hβ a b 0
  have hi2 :
      iteratedDerivWithin 2 (affineLogSumExp s β a b) (uIcc 0 x) 0 =
        affineLogSumExpDerivTwo s β a b 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu
      (hfull.contDiffAt.of_le (by simp)) hzero_mem]
    exact iteratedDeriv_two_affineLogSumExp hs hβ a b 0
  have htaylor :
      taylorWithinEval (affineLogSumExp s β a b) 2 (uIcc 0 x) 0 x =
        affineLogSumExp s β a b 0 +
          affineLogSumExpDerivOne s β a b 0 * x +
          affineLogSumExpDerivTwo s β a b 0 * x ^ 2 / 2 := by
    norm_num [taylorWithinEval_succ, smul_eq_mul, hi1, hi2]
    ring
  have hiter :
      iteratedDeriv 3 (affineLogSumExp s β a b) y =
        affineLogSumExpDerivThree s β a b y :=
    iteratedDeriv_three_affineLogSumExp hs hβ a b y
  rw [htaylor, hiter] at hrem
  rw [hrem, abs_div, abs_mul, abs_pow]
  norm_num [Nat.factorial]
  have hthird := abs_affineLogSumExpDerivThree_le hs (β := β) (c := c)
    (a := a) (b := b) hc ha y
  calc
    |affineLogSumExpDerivThree s β a b y| * |x| ^ 3 / 6 ≤
        (6 * β ^ 2 * c ^ 3) * |x| ^ 3 / 6 := by
      gcongr
    _ = β ^ 2 * c ^ 3 * |x| ^ 3 := by ring

/-! ## A coupled sign/Gaussian product space -/

abbrev CoupledSample := ℕ → (ℝ × ℝ)

def standardGaussianMeasure : Measure ℝ := gaussianReal 0 1

instance : IsProbabilityMeasure standardGaussianMeasure := by
  unfold standardGaussianMeasure
  infer_instance

def coupledCoordinateMeasure : Measure (ℝ × ℝ) :=
  rademacherMeasure.prod standardGaussianMeasure

instance : IsProbabilityMeasure coupledCoordinateMeasure := by
  unfold coupledCoordinateMeasure
  infer_instance

def coupledMeasure : Measure CoupledSample :=
  Measure.infinitePi fun _ : ℕ ↦ coupledCoordinateMeasure

instance : IsProbabilityMeasure coupledMeasure := by
  unfold coupledMeasure
  infer_instance

def coupledSign (k : ℕ) (ω : CoupledSample) : ℝ := (ω k).1

def coupledGaussian (k : ℕ) (ω : CoupledSample) : ℝ := (ω k).2

lemma iIndepFun_coupledCoordinate :
    iIndepFun (fun k (ω : CoupledSample) ↦ ω k) coupledMeasure := by
  unfold coupledMeasure
  exact iIndepFun_infinitePi (X := fun (_ : ℕ) (x : ℝ × ℝ) ↦ x) (by fun_prop)

lemma hasLaw_coupledCoordinate (k : ℕ) :
    HasLaw (fun ω : CoupledSample ↦ ω k) coupledCoordinateMeasure coupledMeasure := by
  unfold coupledMeasure
  exact (measurePreserving_eval_infinitePi
    (fun _ : ℕ ↦ coupledCoordinateMeasure) k).hasLaw

lemma hasLaw_coupledSign (k : ℕ) :
    HasLaw (coupledSign k) rademacherMeasure coupledMeasure := by
  unfold coupledSign
  exact measurePreserving_fst.hasLaw.fun_comp (hasLaw_coupledCoordinate k)

lemma hasLaw_coupledGaussian (k : ℕ) :
    HasLaw (coupledGaussian k) standardGaussianMeasure coupledMeasure := by
  unfold coupledGaussian
  exact measurePreserving_snd.hasLaw.fun_comp (hasLaw_coupledCoordinate k)

lemma integral_coupledSign (k : ℕ) :
    ∫ ω, coupledSign k ω ∂coupledMeasure = 0 := by
  rw [(hasLaw_coupledSign k).integral_eq]
  simp only [rademacherMeasure, integral_bernoulliMeasure, one_smul, neg_smul,
    smul_eq_mul]
  norm_num

lemma integral_coupledGaussian (k : ℕ) :
    ∫ ω, coupledGaussian k ω ∂coupledMeasure = 0 := by
  rw [(hasLaw_coupledGaussian k).integral_eq]
  simp [standardGaussianMeasure]

lemma integral_sq_coupledSign (k : ℕ) :
    ∫ ω, coupledSign k ω ^ 2 ∂coupledMeasure = 1 := by
  calc
    ∫ ω, coupledSign k ω ^ 2 ∂coupledMeasure =
        ∫ x : ℝ, x ^ 2 ∂rademacherMeasure := by
      simpa only [Function.comp_apply] using
        (hasLaw_coupledSign k).integral_comp (f := fun x : ℝ ↦ x ^ 2) (by fun_prop)
    _ = 1 := by
      simp only [rademacherMeasure, integral_bernoulliMeasure, one_smul, neg_smul,
        smul_eq_mul]
      norm_num

lemma integral_sq_standardGaussian :
    ∫ x : ℝ, x ^ 2 ∂standardGaussianMeasure = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := (1 : ℝ≥0))
  rw [variance_eq_integral (X := fun x : ℝ ↦ x) measurable_id.aemeasurable] at h
  simpa [standardGaussianMeasure] using h

lemma integral_sq_coupledGaussian (k : ℕ) :
    ∫ ω, coupledGaussian k ω ^ 2 ∂coupledMeasure = 1 := by
  calc
    ∫ ω, coupledGaussian k ω ^ 2 ∂coupledMeasure =
        ∫ x : ℝ, x ^ 2 ∂standardGaussianMeasure := by
      simpa only [Function.comp_apply] using
        (hasLaw_coupledGaussian k).integral_comp (f := fun x : ℝ ↦ x ^ 2) (by fun_prop)
    _ = 1 := integral_sq_standardGaussian

lemma integrable_abs_cube_coupledSign (k : ℕ) :
    Integrable (fun ω ↦ |coupledSign k ω| ^ 3) coupledMeasure := by
  have hae : ∀ᵐ ω ∂coupledMeasure,
      coupledSign k ω = 1 ∨ coupledSign k ω = -1 := by
    rw [(hasLaw_coupledSign k).ae_iff
      (p := fun x : ℝ ↦ x = 1 ∨ x = -1) (by fun_prop)]
    rw [ae_iff]
    simp [rademacherMeasure, bernoulliMeasure_def]
  apply (integrable_const (c := (1 : ℝ))).congr
  filter_upwards [hae] with ω hω
  rcases hω with hω | hω <;> simp [hω]

lemma integrable_abs_cube_coupledGaussian (k : ℕ) :
    Integrable (fun ω ↦ |coupledGaussian k ω| ^ 3) coupledMeasure := by
  have hg : Integrable (fun x : ℝ ↦ |x| ^ 3) standardGaussianMeasure := by
    simpa [standardGaussianMeasure, Real.norm_eq_abs] using
      (memLp_id_gaussianReal (μ := 0) (v := 1) 3).integrable_norm_pow'
  have hcomp : Integrable
      ((fun x : ℝ ↦ |x| ^ 3) ∘ coupledGaussian k) coupledMeasure := by
    apply (integrable_map_measure (by fun_prop)
      (hasLaw_coupledGaussian k).aemeasurable).mp
    rw [(hasLaw_coupledGaussian k).map_eq]
    exact hg
  change Integrable ((fun x : ℝ ↦ |x| ^ 3) ∘ coupledGaussian k) coupledMeasure
  exact hcomp

lemma abs_le_one_add_abs_cube (x : ℝ) : |x| ≤ 1 + |x| ^ 3 := by
  by_cases hx : |x| ≤ 1
  · nlinarith [abs_nonneg x, pow_nonneg (abs_nonneg x) 3]
  · have hx1 : 1 ≤ |x| := le_of_lt (lt_of_not_ge hx)
    have hsq : 1 ≤ |x| ^ 2 := by nlinarith [abs_nonneg x]
    nlinarith [mul_le_mul_of_nonneg_left hsq (abs_nonneg x)]

lemma sq_le_one_add_abs_cube (x : ℝ) : x ^ 2 ≤ 1 + |x| ^ 3 := by
  by_cases hx : |x| ≤ 1
  · rw [← sq_abs]
    nlinarith [abs_nonneg x, pow_nonneg (abs_nonneg x) 3]
  · have hx1 : 1 ≤ |x| := le_of_lt (lt_of_not_ge hx)
    rw [← sq_abs]
    nlinarith [mul_le_mul_of_nonneg_left hx1 (sq_nonneg |x|)]

lemma integrable_of_integrable_abs_cube {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (hX₃ : Integrable (fun ω ↦ |X ω| ^ 3) μ) : Integrable X μ := by
  apply Integrable.mono' ((integrable_const (μ := μ) (1 : ℝ)).add hX₃)
    hX.aestronglyMeasurable
  filter_upwards with ω
  simpa only [Real.norm_eq_abs, Pi.add_apply] using abs_le_one_add_abs_cube (X ω)

lemma integrable_sq_of_integrable_abs_cube {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (hX₃ : Integrable (fun ω ↦ |X ω| ^ 3) μ) :
    Integrable (fun ω ↦ X ω ^ 2) μ := by
  apply Integrable.mono' ((integrable_const (μ := μ) (1 : ℝ)).add hX₃)
    (hX.pow_const 2).aestronglyMeasurable
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (X ω)), Pi.add_apply]
  exact sq_le_one_add_abs_cube (X ω)

lemma integrable_coupledSign (k : ℕ) : Integrable (coupledSign k) coupledMeasure :=
  integrable_of_integrable_abs_cube (by unfold coupledSign; fun_prop)
    (integrable_abs_cube_coupledSign k)

lemma integrable_coupledGaussian (k : ℕ) :
    Integrable (coupledGaussian k) coupledMeasure :=
  integrable_of_integrable_abs_cube (by unfold coupledGaussian; fun_prop)
    (integrable_abs_cube_coupledGaussian k)

lemma integrable_sq_coupledSign (k : ℕ) :
    Integrable (fun ω ↦ coupledSign k ω ^ 2) coupledMeasure :=
  integrable_sq_of_integrable_abs_cube (by unfold coupledSign; fun_prop)
    (integrable_abs_cube_coupledSign k)

lemma integrable_sq_coupledGaussian (k : ℕ) :
    Integrable (fun ω ↦ coupledGaussian k ω ^ 2) coupledMeasure :=
  integrable_sq_of_integrable_abs_cube (by unfold coupledGaussian; fun_prop)
    (integrable_abs_cube_coupledGaussian k)

def normalizedRootCoeff (N r k : ℕ) : ℝ :=
  Real.sqrt (2 / (N : ℝ)) * (standardRoot N ^ (r * k)).re

def hybridInput (m k : ℕ) (ω : CoupledSample) : ℝ :=
  if k < m then coupledGaussian k ω else coupledSign k ω

def hybridRootProjection (N m r : ℕ) (ω : CoupledSample) : ℝ :=
  ∑ k ∈ Finset.range N, normalizedRootCoeff N r k * hybridInput m k ω

def hybridRootLogSumExp (N m : ℕ) (β : ℝ) (ω : CoupledSample) : ℝ :=
  Real.log (∑ r ∈ frequencySet N, Real.exp (β * hybridRootProjection N m r ω)) / β

def zeroAugmentFinset {ι : Type*} [DecidableEq ι]
    (s : Finset ι) : Finset (Option ι) :=
  insert none (s.map Function.Embedding.some)

def zeroExtend {ι : Type*} (f : ι → ℝ) : Option ι → ℝ
  | none => 0
  | some i => f i

lemma zeroAugmentFinset_nonempty {ι : Type*} [DecidableEq ι] (s : Finset ι) :
    (zeroAugmentFinset s).Nonempty := by
  classical
  exact ⟨none, by simp [zeroAugmentFinset]⟩

lemma zeroExtend_abs_le {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {f : ι → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hf : ∀ i ∈ s, |f i| ≤ c) :
    ∀ i ∈ zeroAugmentFinset s, |zeroExtend f i| ≤ c := by
  classical
  intro i hi
  rcases i with _ | i
  · simpa [zeroExtend] using hc
  · exact hf i (by simpa [zeroAugmentFinset] using hi)

lemma affineMomentSum_zeroAugment_zero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (β : ℝ) (a b : ι → ℝ) (x : ℝ) :
    affineMomentSum (zeroAugmentFinset s) β (zeroExtend a) (zeroExtend b) 0 x =
      1 + ∑ i ∈ s, Real.exp (β * (b i + a i * x)) := by
  unfold affineMomentSum zeroAugmentFinset
  rw [Finset.sum_insert (by simp), Finset.sum_map]
  simp [zeroExtend]

lemma affineLogSumExp_zeroAugment_nonneg {ι : Type*} [DecidableEq ι]
    (s : Finset ι)
    {β : ℝ} (hβ : 0 < β) (a b : ι → ℝ) (x : ℝ) :
    0 ≤ affineLogSumExp (zeroAugmentFinset s) β (zeroExtend a) (zeroExtend b) x := by
  classical
  have hsum : 1 ≤ affineMomentSum (zeroAugmentFinset s) β
      (zeroExtend a) (zeroExtend b) 0 x := by
    rw [affineMomentSum_zeroAugment_zero]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ by positivity)
  unfold affineLogSumExp
  exact div_nonneg (Real.log_nonneg hsum) hβ.le

lemma affineExpNegLogSumExp_nonneg {ι : Type*} (s : Finset ι) (β γ : ℝ)
    (a b : ι → ℝ) (x : ℝ) :
    0 ≤ affineExpNegLogSumExp s β γ a b x := by
  unfold affineExpNegLogSumExp
  positivity

lemma abs_affineExpNegLogSumExp_le_one {ι : Type*} {s : Finset ι}
    {β γ : ℝ} {a b : ι → ℝ} {x : ℝ} (hγ : 0 ≤ γ)
    (hL : 0 ≤ affineLogSumExp s β a b x) :
    |affineExpNegLogSumExp s β γ a b x| ≤ 1 := by
  rw [abs_of_nonneg (affineExpNegLogSumExp_nonneg s β γ a b x), ← Real.exp_zero]
  unfold affineExpNegLogSumExp
  exact Real.exp_le_exp.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγ) hL)

lemma abs_affineExpNegLogSumExpDerivOne_le {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {β γ c : ℝ} {a b : ι → ℝ}
    (hγ : 0 ≤ γ) (hc : 0 ≤ c) (ha : ∀ i ∈ s, |a i| ≤ c) (x : ℝ)
    (hL : 0 ≤ affineLogSumExp s β a b x) :
    |affineExpNegLogSumExpDerivOne s β γ a b x| ≤ γ * c := by
  have h1 := abs_affineLogSumExpDerivOne_le hs (β := β) (c := c)
    (a := a) (b := b) hc ha x
  have he := abs_affineExpNegLogSumExp_le_one (s := s) hγ hL
  unfold affineExpNegLogSumExpDerivOne
  rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hγ]
  calc
    γ * |affineLogSumExpDerivOne s β a b x| *
        |affineExpNegLogSumExp s β γ a b x| ≤ γ * c * 1 := by gcongr
    _ = γ * c := by ring

lemma abs_affineExpNegLogSumExpDerivTwo_le {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {β γ c : ℝ} {a b : ι → ℝ}
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hc : 0 ≤ c)
    (ha : ∀ i ∈ s, |a i| ≤ c) (x : ℝ)
    (hL : 0 ≤ affineLogSumExp s β a b x) :
    |affineExpNegLogSumExpDerivTwo s β γ a b x| ≤
      (γ ^ 2 + 2 * γ * β) * c ^ 2 := by
  have h1 := abs_affineLogSumExpDerivOne_le hs (β := β) (c := c)
    (a := a) (b := b) hc ha x
  have h2 := abs_affineLogSumExpDerivTwo_le hs (β := β) (c := c)
    (a := a) (b := b) hβ hc ha x
  have he := abs_affineExpNegLogSumExp_le_one (s := s) hγ hL
  unfold affineExpNegLogSumExpDerivTwo
  rw [abs_mul]
  calc
    |γ ^ 2 * affineLogSumExpDerivOne s β a b x ^ 2 -
          γ * affineLogSumExpDerivTwo s β a b x| *
        |affineExpNegLogSumExp s β γ a b x| ≤
        (γ ^ 2 * |affineLogSumExpDerivOne s β a b x| ^ 2 +
          γ * |affineLogSumExpDerivTwo s β a b x|) * 1 := by
      gcongr
      calc
        |γ ^ 2 * affineLogSumExpDerivOne s β a b x ^ 2 -
            γ * affineLogSumExpDerivTwo s β a b x| ≤
            |γ ^ 2 * affineLogSumExpDerivOne s β a b x ^ 2| +
              |γ * affineLogSumExpDerivTwo s β a b x| := abs_sub _ _
        _ = γ ^ 2 * |affineLogSumExpDerivOne s β a b x| ^ 2 +
              γ * |affineLogSumExpDerivTwo s β a b x| := by
          simp only [abs_mul, abs_pow, abs_of_nonneg hγ, pow_nonneg]
    _ ≤ (γ ^ 2 * c ^ 2 + γ * (2 * β * c ^ 2)) * 1 := by gcongr
    _ = (γ ^ 2 + 2 * γ * β) * c ^ 2 := by ring

def hybridRootLogSumExpZero (N m : ℕ) (β : ℝ) (ω : CoupledSample) : ℝ :=
  Real.log (1 + ∑ r ∈ frequencySet N,
    Real.exp (β * hybridRootProjection N m r ω)) / β

def hybridRootExpNegLogSumExpZero (N m : ℕ) (β γ : ℝ)
    (ω : CoupledSample) : ℝ :=
  Real.exp (-γ * hybridRootLogSumExpZero N m β ω)

def hybridRootBaseline (N k r : ℕ) (ω : CoupledSample) : ℝ :=
  ∑ j ∈ (Finset.range N).erase k,
    normalizedRootCoeff N r j * hybridInput k j ω

lemma hybridInput_self (k : ℕ) (ω : CoupledSample) :
    hybridInput k k ω = coupledSign k ω := by
  simp [hybridInput]

lemma hybridInput_succ_self (k : ℕ) (ω : CoupledSample) :
    hybridInput (k + 1) k ω = coupledGaussian k ω := by
  simp [hybridInput]

lemma hybridInput_succ_eq_of_ne {k j : ℕ} (hjk : j ≠ k) (ω : CoupledSample) :
    hybridInput (k + 1) j ω = hybridInput k j ω := by
  unfold hybridInput
  by_cases hj : j < k
  · simp [hj, hj.trans_le (Nat.le_succ k)]
  · have hkj : k < j := lt_of_le_of_ne (Nat.le_of_not_gt hj) (Ne.symm hjk)
    simp [Nat.not_lt.mpr hkj.le, Nat.not_lt.mpr (Nat.succ_le_iff.mpr hkj)]

lemma hybridRootProjection_step_sign {N k r : ℕ} (hk : k < N)
    (ω : CoupledSample) :
    hybridRootProjection N k r ω =
      hybridRootBaseline N k r ω + normalizedRootCoeff N r k * coupledSign k ω := by
  unfold hybridRootProjection hybridRootBaseline
  rw [← Finset.sum_erase_add (Finset.range N)
    (fun j ↦ normalizedRootCoeff N r j * hybridInput k j ω)
    (Finset.mem_range.mpr hk)]
  simp only [hybridInput_self]

lemma hybridRootProjection_step_gaussian {N k r : ℕ} (hk : k < N)
    (ω : CoupledSample) :
    hybridRootProjection N (k + 1) r ω =
      hybridRootBaseline N k r ω + normalizedRootCoeff N r k * coupledGaussian k ω := by
  unfold hybridRootProjection hybridRootBaseline
  rw [← Finset.sum_erase_add (Finset.range N)
    (fun j ↦ normalizedRootCoeff N r j * hybridInput (k + 1) j ω)
    (Finset.mem_range.mpr hk)]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [hybridInput_succ_eq_of_ne (Finset.ne_of_mem_erase hj)]
  · rw [hybridInput_succ_self]

lemma hybridRootLogSumExp_step_sign {N k : ℕ} (hk : k < N) (β : ℝ)
    (ω : CoupledSample) :
    hybridRootLogSumExp N k β ω =
      affineLogSumExp (frequencySet N) β (normalizedRootCoeff N · k)
        (hybridRootBaseline N k · ω) (coupledSign k ω) := by
  unfold hybridRootLogSumExp affineLogSumExp affineMomentSum
  congr 2
  apply Finset.sum_congr rfl
  intro r hr
  rw [hybridRootProjection_step_sign hk]
  norm_num

lemma hybridRootLogSumExp_step_gaussian {N k : ℕ} (hk : k < N) (β : ℝ)
    (ω : CoupledSample) :
    hybridRootLogSumExp N (k + 1) β ω =
      affineLogSumExp (frequencySet N) β (normalizedRootCoeff N · k)
        (hybridRootBaseline N k · ω) (coupledGaussian k ω) := by
  unfold hybridRootLogSumExp affineLogSumExp affineMomentSum
  congr 2
  apply Finset.sum_congr rfl
  intro r hr
  rw [hybridRootProjection_step_gaussian hk]
  norm_num

lemma hybridRootLogSumExpZero_step_sign {N k : ℕ} (hk : k < N) (β : ℝ)
    (ω : CoupledSample) :
    hybridRootLogSumExpZero N k β ω =
      affineLogSumExp (zeroAugmentFinset (frequencySet N)) β
        (zeroExtend (normalizedRootCoeff N · k))
        (zeroExtend (hybridRootBaseline N k · ω)) (coupledSign k ω) := by
  classical
  unfold hybridRootLogSumExpZero affineLogSumExp
  rw [affineMomentSum_zeroAugment_zero]
  congr 3
  apply Finset.sum_congr rfl
  intro r _hr
  rw [hybridRootProjection_step_sign hk]

lemma hybridRootLogSumExpZero_step_gaussian {N k : ℕ} (hk : k < N) (β : ℝ)
    (ω : CoupledSample) :
    hybridRootLogSumExpZero N (k + 1) β ω =
      affineLogSumExp (zeroAugmentFinset (frequencySet N)) β
        (zeroExtend (normalizedRootCoeff N · k))
        (zeroExtend (hybridRootBaseline N k · ω)) (coupledGaussian k ω) := by
  classical
  unfold hybridRootLogSumExpZero affineLogSumExp
  rw [affineMomentSum_zeroAugment_zero]
  congr 3
  apply Finset.sum_congr rfl
  intro r _hr
  rw [hybridRootProjection_step_gaussian hk]

lemma hybridRootExpNegLogSumExpZero_step_sign {N k : ℕ} (hk : k < N)
    (β γ : ℝ) (ω : CoupledSample) :
    hybridRootExpNegLogSumExpZero N k β γ ω =
      affineExpNegLogSumExp (zeroAugmentFinset (frequencySet N)) β γ
        (zeroExtend (normalizedRootCoeff N · k))
        (zeroExtend (hybridRootBaseline N k · ω)) (coupledSign k ω) := by
  unfold hybridRootExpNegLogSumExpZero affineExpNegLogSumExp
  rw [hybridRootLogSumExpZero_step_sign hk]

lemma hybridRootExpNegLogSumExpZero_step_gaussian {N k : ℕ} (hk : k < N)
    (β γ : ℝ) (ω : CoupledSample) :
    hybridRootExpNegLogSumExpZero N (k + 1) β γ ω =
      affineExpNegLogSumExp (zeroAugmentFinset (frequencySet N)) β γ
        (zeroExtend (normalizedRootCoeff N · k))
        (zeroExtend (hybridRootBaseline N k · ω)) (coupledGaussian k ω) := by
  unfold hybridRootExpNegLogSumExpZero affineExpNegLogSumExp
  rw [hybridRootLogSumExpZero_step_gaussian hk]

lemma measurable_coupledSign (k : ℕ) : Measurable (coupledSign k) := by
  unfold coupledSign
  fun_prop

lemma measurable_coupledGaussian (k : ℕ) : Measurable (coupledGaussian k) := by
  unfold coupledGaussian
  fun_prop

lemma measurable_hybridInput (m k : ℕ) : Measurable (hybridInput m k) := by
  unfold hybridInput
  by_cases hk : k < m
  · simpa only [if_pos hk] using measurable_coupledGaussian k
  · simpa only [if_neg hk] using measurable_coupledSign k

lemma measurable_hybridRootBaseline (N k r : ℕ) :
    Measurable (hybridRootBaseline N k r) := by
  unfold hybridRootBaseline
  apply Finset.measurable_sum
  intro j _hj
  exact measurable_const.mul (measurable_hybridInput k j)

lemma abs_normalizedRootCoeff_le (N r k : ℕ) :
    |normalizedRootCoeff N r k| ≤ Real.sqrt (2 / (N : ℝ)) := by
  have hre : |(standardRoot N ^ (r * k)).re| ≤ 1 := by
    calc
      |(standardRoot N ^ (r * k)).re| ≤ ‖standardRoot N ^ (r * k)‖ :=
        Complex.abs_re_le_norm _
      _ = 1 := norm_standardRoot_pow N (r * k)
  unfold normalizedRootCoeff
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  nlinarith [Real.sqrt_nonneg (2 / (N : ℝ))]

lemma indepFun_coupledCoordinate_hybridRootBaseline {N k : ℕ} (hk : k < N) :
    IndepFun (fun ω : CoupledSample ↦ ω k)
      (fun ω r ↦ hybridRootBaseline N k r ω) coupledMeasure := by
  let T : Finset ℕ := (Finset.range N).erase k
  have hdisj : Disjoint ({k} : Finset ℕ) T := by
    simp [T]
  have hraw := iIndepFun_coupledCoordinate.indepFun_finset
    ({k} : Finset ℕ) T hdisj (fun _ ↦ measurable_pi_apply _)
  let φ : (↥({k} : Finset ℕ) → (ℝ × ℝ)) → (ℝ × ℝ) :=
    fun v ↦ v ⟨k, by simp⟩
  let ψ : (↥T → (ℝ × ℝ)) → (ℕ → ℝ) := fun v r ↦
    ∑ j : T, normalizedRootCoeff N r j.1 *
      (if j.1 < k then (v j).2 else (v j).1)
  have hφ : Measurable φ := by
    dsimp only [φ]
    fun_prop
  have hψ : Measurable ψ := by
    dsimp only [ψ]
    apply measurable_pi_lambda
    intro r
    apply Finset.measurable_sum
    intro j _hj
    by_cases hjk : j.1 < k <;> simp only [hjk, ↓reduceIte] <;> fun_prop
  have hcomp := hraw.comp (φ := φ) (ψ := ψ) hφ hψ
  have hleft : φ ∘ (fun a (i : ({k} : Finset ℕ)) ↦ a i) =
      fun ω : CoupledSample ↦ ω k := by
    funext ω
    rfl
  have hright : ψ ∘ (fun a (i : T) ↦ a i) =
      fun ω r ↦ hybridRootBaseline N k r ω := by
    funext ω r
    simp only [Function.comp_apply, ψ, hybridRootBaseline, hybridInput,
      coupledGaussian, coupledSign, T]
    exact (Finset.sum_subtype ((Finset.range N).erase k) (fun _ ↦ Iff.rfl)
      (fun j ↦ normalizedRootCoeff N r j *
        (if j < k then (ω j).2 else (ω j).1))).symm
  rw [hleft, hright] at hcomp
  exact hcomp

def rootTaylorCoeffZero (N k : ℕ) (β γ : ℝ) (b : ℕ → ℝ) : ℝ :=
  affineExpNegLogSumExp (zeroAugmentFinset (frequencySet N)) β γ
    (zeroExtend (normalizedRootCoeff N · k))
    (zeroExtend b) 0

def rootTaylorCoeffOne (N k : ℕ) (β γ : ℝ) (b : ℕ → ℝ) : ℝ :=
  affineExpNegLogSumExpDerivOne (zeroAugmentFinset (frequencySet N)) β γ
    (zeroExtend (normalizedRootCoeff N · k))
    (zeroExtend b) 0

def rootTaylorCoeffTwo (N k : ℕ) (β γ : ℝ) (b : ℕ → ℝ) : ℝ :=
  affineExpNegLogSumExpDerivTwo (zeroAugmentFinset (frequencySet N)) β γ
    (zeroExtend (normalizedRootCoeff N · k))
    (zeroExtend b) 0

def hybridTaylorCoeffZero (N k : ℕ) (β γ : ℝ) (ω : CoupledSample) : ℝ :=
  rootTaylorCoeffZero N k β γ (hybridRootBaseline N k · ω)

def hybridTaylorCoeffOne (N k : ℕ) (β γ : ℝ) (ω : CoupledSample) : ℝ :=
  rootTaylorCoeffOne N k β γ (hybridRootBaseline N k · ω)

def hybridTaylorCoeffTwo (N k : ℕ) (β γ : ℝ) (ω : CoupledSample) : ℝ :=
  rootTaylorCoeffTwo N k β γ (hybridRootBaseline N k · ω)

def hybridCubicError (N : ℕ) (β γ : ℝ) : ℝ :=
  (γ ^ 3 + 6 * γ ^ 2 * β + 6 * γ * β ^ 2) *
    Real.sqrt (2 / (N : ℝ)) ^ 3 / 6

lemma measurable_zeroExtend_hybridRootBaseline (N k : ℕ) (i : Option ℕ) :
    Measurable (fun ω ↦ zeroExtend (hybridRootBaseline N k · ω) i) := by
  rcases i with _ | i
  · simp [zeroExtend]
  · simpa only [zeroExtend] using measurable_hybridRootBaseline N k i

lemma measurable_affineMomentSum_random {Ω ι : Type*} [MeasurableSpace Ω]
    (s : Finset ι) (β : ℝ) (a : ι → ℝ) (b : ι → Ω → ℝ)
    (hb : ∀ i ∈ s, Measurable (b i)) (m : ℕ) (x : ℝ) :
    Measurable (fun ω ↦ affineMomentSum s β a (fun i ↦ b i ω) m x) := by
  unfold affineMomentSum
  apply Finset.measurable_sum
  intro i hi
  exact ((measurable_const.mul ((hb i hi).add measurable_const)).exp).mul measurable_const

lemma measurable_zeroExtend_apply (i : Option ℕ) :
    Measurable (fun b : ℕ → ℝ ↦ zeroExtend b i) := by
  rcases i with _ | i
  · simp [zeroExtend]
  · simpa only [zeroExtend] using measurable_pi_apply i

lemma measurable_rootTaylorCoeffOne (N k : ℕ) (β γ : ℝ) :
    Measurable (rootTaylorCoeffOne N k β γ) := by
  have hm (m : ℕ) : Measurable (fun b : ℕ → ℝ ↦
      affineMomentSum (zeroAugmentFinset (frequencySet N)) β
        (zeroExtend (normalizedRootCoeff N · k)) (zeroExtend b) m 0) := by
    apply measurable_affineMomentSum_random
    intro i _hi
    exact measurable_zeroExtend_apply i
  unfold rootTaylorCoeffOne affineExpNegLogSumExpDerivOne
    affineExpNegLogSumExp affineLogSumExpDerivOne affineLogSumExp
  exact (measurable_const.mul ((hm 1).div (hm 0))).mul
    (measurable_const.mul ((hm 0).log.div_const β)).exp

lemma measurable_rootTaylorCoeffTwo (N k : ℕ) (β γ : ℝ) :
    Measurable (rootTaylorCoeffTwo N k β γ) := by
  have hm (m : ℕ) : Measurable (fun b : ℕ → ℝ ↦
      affineMomentSum (zeroAugmentFinset (frequencySet N)) β
        (zeroExtend (normalizedRootCoeff N · k)) (zeroExtend b) m 0) := by
    apply measurable_affineMomentSum_random
    intro i _hi
    exact measurable_zeroExtend_apply i
  unfold rootTaylorCoeffTwo affineExpNegLogSumExpDerivTwo
    affineExpNegLogSumExp affineLogSumExpDerivOne affineLogSumExpDerivTwo
    affineLogSumExp
  have hr1 := (hm 1).div (hm 0)
  have hr2 := (hm 2).div (hm 0)
  exact ((measurable_const.mul (hr1.pow_const 2)).sub
    (measurable_const.mul (measurable_const.mul (hr2.sub (hr1.pow_const 2))))).mul
    (measurable_const.mul ((hm 0).log.div_const β)).exp

lemma measurable_hybridTaylorCoeffZero (N k : ℕ) (β γ : ℝ) :
    Measurable (hybridTaylorCoeffZero N k β γ) := by
  have hm (m : ℕ) : Measurable (fun ω ↦
      affineMomentSum (zeroAugmentFinset (frequencySet N)) β
        (zeroExtend (normalizedRootCoeff N · k))
        (zeroExtend (hybridRootBaseline N k · ω)) m 0) := by
    apply measurable_affineMomentSum_random
    intro i _hi
    exact measurable_zeroExtend_hybridRootBaseline N k i
  unfold hybridTaylorCoeffZero rootTaylorCoeffZero affineExpNegLogSumExp affineLogSumExp
  exact (measurable_const.mul ((hm 0).log.div_const β)).exp

lemma measurable_hybridTaylorCoeffOne (N k : ℕ) (β γ : ℝ) :
    Measurable (hybridTaylorCoeffOne N k β γ) := by
  have hm (m : ℕ) : Measurable (fun ω ↦
      affineMomentSum (zeroAugmentFinset (frequencySet N)) β
        (zeroExtend (normalizedRootCoeff N · k))
        (zeroExtend (hybridRootBaseline N k · ω)) m 0) := by
    apply measurable_affineMomentSum_random
    intro i _hi
    exact measurable_zeroExtend_hybridRootBaseline N k i
  unfold hybridTaylorCoeffOne rootTaylorCoeffOne affineExpNegLogSumExpDerivOne
    affineExpNegLogSumExp affineLogSumExpDerivOne affineLogSumExp
  exact (measurable_const.mul ((hm 1).div (hm 0))).mul
    (measurable_const.mul ((hm 0).log.div_const β)).exp

lemma measurable_hybridTaylorCoeffTwo (N k : ℕ) (β γ : ℝ) :
    Measurable (hybridTaylorCoeffTwo N k β γ) := by
  have hm (m : ℕ) : Measurable (fun ω ↦
      affineMomentSum (zeroAugmentFinset (frequencySet N)) β
        (zeroExtend (normalizedRootCoeff N · k))
        (zeroExtend (hybridRootBaseline N k · ω)) m 0) := by
    apply measurable_affineMomentSum_random
    intro i _hi
    exact measurable_zeroExtend_hybridRootBaseline N k i
  unfold hybridTaylorCoeffTwo rootTaylorCoeffTwo affineExpNegLogSumExpDerivTwo
    affineExpNegLogSumExp affineLogSumExpDerivOne affineLogSumExpDerivTwo
    affineLogSumExp
  have hr1 := (hm 1).div (hm 0)
  have hr2 := (hm 2).div (hm 0)
  exact ((measurable_const.mul (hr1.pow_const 2)).sub
    (measurable_const.mul (measurable_const.mul (hr2.sub (hr1.pow_const 2))))).mul
    (measurable_const.mul ((hm 0).log.div_const β)).exp

lemma measurable_hybridRootProjection (N m r : ℕ) :
    Measurable (hybridRootProjection N m r) := by
  unfold hybridRootProjection
  apply Finset.measurable_sum
  intro k _hk
  exact measurable_const.mul (measurable_hybridInput m k)

lemma measurable_hybridRootLogSumExpZero (N m : ℕ) (β : ℝ) :
    Measurable (hybridRootLogSumExpZero N m β) := by
  unfold hybridRootLogSumExpZero
  apply Measurable.div_const
  apply Measurable.log
  apply measurable_const.add
  apply Finset.measurable_sum
  intro r _hr
  exact (measurable_const.mul (measurable_hybridRootProjection N m r)).exp

lemma hybridRootLogSumExpZero_nonneg (N m : ℕ) {β : ℝ} (hβ : 0 < β)
    (ω : CoupledSample) : 0 ≤ hybridRootLogSumExpZero N m β ω := by
  have hsum : 1 ≤ 1 + ∑ r ∈ frequencySet N,
      Real.exp (β * hybridRootProjection N m r ω) :=
    le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ by positivity)
  unfold hybridRootLogSumExpZero
  exact div_nonneg (Real.log_nonneg hsum) hβ.le

lemma measurable_hybridRootExpNegLogSumExpZero (N m : ℕ) (β γ : ℝ) :
    Measurable (hybridRootExpNegLogSumExpZero N m β γ) := by
  unfold hybridRootExpNegLogSumExpZero
  exact (measurable_const.mul (measurable_hybridRootLogSumExpZero N m β)).exp

lemma integrable_hybridRootExpNegLogSumExpZero (N m : ℕ) {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 ≤ γ) :
    Integrable (hybridRootExpNegLogSumExpZero N m β γ) coupledMeasure := by
  apply Integrable.of_bound
    (measurable_hybridRootExpNegLogSumExpZero N m β γ).aestronglyMeasurable 1
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    unfold hybridRootExpNegLogSumExpZero
    positivity)]
  unfold hybridRootExpNegLogSumExpZero
  rw [← Real.exp_zero]
  exact Real.exp_le_exp.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγ)
      (hybridRootLogSumExpZero_nonneg N m hβ ω))

lemma hybridTaylorCoeffZero_abs_le_one (N k : ℕ) {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 ≤ γ) (ω : CoupledSample) :
    |hybridTaylorCoeffZero N k β γ ω| ≤ 1 := by
  apply abs_affineExpNegLogSumExp_le_one hγ
  exact affineLogSumExp_zeroAugment_nonneg (frequencySet N) hβ _ _ 0

lemma hybridTaylorCoeffOne_abs_le (N k : ℕ) {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 ≤ γ) (ω : CoupledSample) :
    |hybridTaylorCoeffOne N k β γ ω| ≤
      γ * Real.sqrt (2 / (N : ℝ)) := by
  apply abs_affineExpNegLogSumExpDerivOne_le
    (zeroAugmentFinset_nonempty (frequencySet N)) hγ (Real.sqrt_nonneg _)
  · exact zeroExtend_abs_le (Real.sqrt_nonneg _)
      (fun i _hi ↦ abs_normalizedRootCoeff_le N i k)
  · exact affineLogSumExp_zeroAugment_nonneg (frequencySet N) hβ _ _ 0

lemma hybridTaylorCoeffTwo_abs_le (N k : ℕ) {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 ≤ γ) (ω : CoupledSample) :
    |hybridTaylorCoeffTwo N k β γ ω| ≤
      (γ ^ 2 + 2 * γ * β) * Real.sqrt (2 / (N : ℝ)) ^ 2 := by
  apply abs_affineExpNegLogSumExpDerivTwo_le
    (zeroAugmentFinset_nonempty (frequencySet N)) hβ.le hγ (Real.sqrt_nonneg _)
  · exact zeroExtend_abs_le (Real.sqrt_nonneg _)
      (fun i _hi ↦ abs_normalizedRootCoeff_le N i k)
  · exact affineLogSumExp_zeroAugment_nonneg (frequencySet N) hβ _ _ 0

lemma integrable_hybridTaylorCoeffZero (N k : ℕ) {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 ≤ γ) :
    Integrable (hybridTaylorCoeffZero N k β γ) coupledMeasure := by
  apply Integrable.of_bound (measurable_hybridTaylorCoeffZero N k β γ).aestronglyMeasurable 1
  exact ae_of_all _ (hybridTaylorCoeffZero_abs_le_one N k hβ hγ)

lemma integrable_hybridTaylorCoeffOne (N k : ℕ) {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 ≤ γ) :
    Integrable (hybridTaylorCoeffOne N k β γ) coupledMeasure := by
  apply Integrable.of_bound (measurable_hybridTaylorCoeffOne N k β γ).aestronglyMeasurable
    (γ * Real.sqrt (2 / (N : ℝ)))
  exact ae_of_all _ (hybridTaylorCoeffOne_abs_le N k hβ hγ)

lemma integrable_hybridTaylorCoeffTwo (N k : ℕ) {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 ≤ γ) :
    Integrable (hybridTaylorCoeffTwo N k β γ) coupledMeasure := by
  apply Integrable.of_bound (measurable_hybridTaylorCoeffTwo N k β γ).aestronglyMeasurable
    ((γ ^ 2 + 2 * γ * β) * Real.sqrt (2 / (N : ℝ)) ^ 2)
  exact ae_of_all _ (hybridTaylorCoeffTwo_abs_le N k hβ hγ)

lemma indepFun_hybridTaylorCoeffOne_coupledSign {N k : ℕ} (hk : k < N)
    (β γ : ℝ) :
    IndepFun (hybridTaylorCoeffOne N k β γ) (coupledSign k) coupledMeasure := by
  have h := (indepFun_coupledCoordinate_hybridRootBaseline hk).symm.comp
    (measurable_rootTaylorCoeffOne N k β γ) measurable_fst
  convert h using 1 <;> funext ω <;> rfl

lemma indepFun_hybridTaylorCoeffOne_coupledGaussian {N k : ℕ} (hk : k < N)
    (β γ : ℝ) :
    IndepFun (hybridTaylorCoeffOne N k β γ) (coupledGaussian k) coupledMeasure := by
  have h := (indepFun_coupledCoordinate_hybridRootBaseline hk).symm.comp
    (measurable_rootTaylorCoeffOne N k β γ) measurable_snd
  convert h using 1 <;> funext ω <;> rfl

lemma indepFun_hybridTaylorCoeffTwo_coupledSign {N k : ℕ} (hk : k < N)
    (β γ : ℝ) :
    IndepFun (hybridTaylorCoeffTwo N k β γ) (coupledSign k) coupledMeasure := by
  have h := (indepFun_coupledCoordinate_hybridRootBaseline hk).symm.comp
    (measurable_rootTaylorCoeffTwo N k β γ) measurable_fst
  convert h using 1 <;> funext ω <;> rfl

lemma indepFun_hybridTaylorCoeffTwo_coupledGaussian {N k : ℕ} (hk : k < N)
    (β γ : ℝ) :
    IndepFun (hybridTaylorCoeffTwo N k β γ) (coupledGaussian k) coupledMeasure := by
  have h := (indepFun_coupledCoordinate_hybridRootBaseline hk).symm.comp
    (measurable_rootTaylorCoeffTwo N k β γ) measurable_snd
  convert h using 1 <;> funext ω <;> rfl

lemma hybridCubicError_nonneg (N : ℕ) {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ) :
    0 ≤ hybridCubicError N β γ := by
  unfold hybridCubicError
  positivity

lemma hybridRoot_taylor_sign {N k : ℕ} (hk : k < N) {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 ≤ γ) (ω : CoupledSample) :
    |hybridRootExpNegLogSumExpZero N k β γ ω -
        (hybridTaylorCoeffZero N k β γ ω +
          hybridTaylorCoeffOne N k β γ ω * coupledSign k ω +
          hybridTaylorCoeffTwo N k β γ ω * coupledSign k ω ^ 2 / 2)| ≤
      hybridCubicError N β γ * |coupledSign k ω| ^ 3 := by
  rw [hybridRootExpNegLogSumExpZero_step_sign hk]
  have h := abs_affineExpNegLogSumExp_taylor_le
    (s := zeroAugmentFinset (frequencySet N)) (β := β) (γ := γ)
    (c := Real.sqrt (2 / (N : ℝ)))
    (a := zeroExtend (normalizedRootCoeff N · k))
    (b := zeroExtend (hybridRootBaseline N k · ω))
    (zeroAugmentFinset_nonempty (frequencySet N)) hβ hγ (Real.sqrt_nonneg _)
    (zeroExtend_abs_le (Real.sqrt_nonneg _)
      (fun i _hi ↦ abs_normalizedRootCoeff_le N i k))
    (fun y ↦ affineLogSumExp_zeroAugment_nonneg (frequencySet N) hβ _ _ y)
    (coupledSign k ω)
  simp only [hybridTaylorCoeffZero, hybridTaylorCoeffOne, hybridTaylorCoeffTwo,
    rootTaylorCoeffZero, rootTaylorCoeffOne, rootTaylorCoeffTwo, hybridCubicError]
  exact h.trans_eq (by ring)

lemma hybridRoot_taylor_gaussian {N k : ℕ} (hk : k < N) {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 ≤ γ) (ω : CoupledSample) :
    |hybridRootExpNegLogSumExpZero N (k + 1) β γ ω -
        (hybridTaylorCoeffZero N k β γ ω +
          hybridTaylorCoeffOne N k β γ ω * coupledGaussian k ω +
          hybridTaylorCoeffTwo N k β γ ω * coupledGaussian k ω ^ 2 / 2)| ≤
      hybridCubicError N β γ * |coupledGaussian k ω| ^ 3 := by
  rw [hybridRootExpNegLogSumExpZero_step_gaussian hk]
  have h := abs_affineExpNegLogSumExp_taylor_le
    (s := zeroAugmentFinset (frequencySet N)) (β := β) (γ := γ)
    (c := Real.sqrt (2 / (N : ℝ)))
    (a := zeroExtend (normalizedRootCoeff N · k))
    (b := zeroExtend (hybridRootBaseline N k · ω))
    (zeroAugmentFinset_nonempty (frequencySet N)) hβ hγ (Real.sqrt_nonneg _)
    (zeroExtend_abs_le (Real.sqrt_nonneg _)
      (fun i _hi ↦ abs_normalizedRootCoeff_le N i k))
    (fun y ↦ affineLogSumExp_zeroAugment_nonneg (frequencySet N) hβ _ _ y)
    (coupledGaussian k ω)
  simp only [hybridTaylorCoeffZero, hybridTaylorCoeffOne, hybridTaylorCoeffTwo,
    rootTaylorCoeffZero, rootTaylorCoeffOne, rootTaylorCoeffTwo, hybridCubicError]
  exact h.trans_eq (by ring)

/-- A scalar Lindeberg replacement step.  The two inputs have the same first two
moments, while the (random) Taylor coefficients are independent of either input.
Only the cubic Taylor remainders survive after integration. -/
lemma integral_lindeberg_step
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X Y C₀ C₁ C₂ F_X F_Y : Ω → ℝ) {K : ℝ}
    (hK : 0 ≤ K)
    (hX : Integrable X μ) (hY : Integrable Y μ)
    (hX₂ : Integrable (fun ω ↦ X ω ^ 2) μ)
    (hY₂ : Integrable (fun ω ↦ Y ω ^ 2) μ)
    (hX₃ : Integrable (fun ω ↦ |X ω| ^ 3) μ)
    (hY₃ : Integrable (fun ω ↦ |Y ω| ^ 3) μ)
    (hC₀ : Integrable C₀ μ) (hC₁ : Integrable C₁ μ) (hC₂ : Integrable C₂ μ)
    (hFX : Integrable F_X μ) (hFY : Integrable F_Y μ)
    (hC₁X : IndepFun C₁ X μ) (hC₁Y : IndepFun C₁ Y μ)
    (hC₂X : IndepFun C₂ X μ) (hC₂Y : IndepFun C₂ Y μ)
    (hmean : (∫ ω, X ω ∂μ) = ∫ ω, Y ω ∂μ)
    (hsecond : (∫ ω, X ω ^ 2 ∂μ) = ∫ ω, Y ω ^ 2 ∂μ)
    (hremX : ∀ᵐ ω ∂μ,
      |F_X ω - (C₀ ω + C₁ ω * X ω + C₂ ω * X ω ^ 2 / 2)| ≤
        K * |X ω| ^ 3)
    (hremY : ∀ᵐ ω ∂μ,
      |F_Y ω - (C₀ ω + C₁ ω * Y ω + C₂ ω * Y ω ^ 2 / 2)| ≤
        K * |Y ω| ^ 3) :
    |(∫ ω, F_X ω ∂μ) - ∫ ω, F_Y ω ∂μ| ≤
      K * ((∫ ω, |X ω| ^ 3 ∂μ) + ∫ ω, |Y ω| ^ 3 ∂μ) := by
  let P_X : Ω → ℝ := fun ω ↦ C₀ ω + C₁ ω * X ω + C₂ ω * X ω ^ 2 / 2
  let P_Y : Ω → ℝ := fun ω ↦ C₀ ω + C₁ ω * Y ω + C₂ ω * Y ω ^ 2 / 2
  have hC₁X_int : Integrable (fun ω ↦ C₁ ω * X ω) μ := by
    change Integrable (C₁ * X) μ
    exact hC₁X.integrable_mul hC₁ hX
  have hC₁Y_int : Integrable (fun ω ↦ C₁ ω * Y ω) μ := by
    change Integrable (C₁ * Y) μ
    exact hC₁Y.integrable_mul hC₁ hY
  have hC₂X₂ : IndepFun C₂ (fun ω ↦ X ω ^ 2) μ := by
    convert hC₂X.comp measurable_id (measurable_id.pow_const 2) using 1 <;>
      funext ω <;> rfl
  have hC₂Y₂ : IndepFun C₂ (fun ω ↦ Y ω ^ 2) μ := by
    convert hC₂Y.comp measurable_id (measurable_id.pow_const 2) using 1 <;>
      funext ω <;> rfl
  have hC₂X_int : Integrable (fun ω ↦ C₂ ω * X ω ^ 2) μ := by
    change Integrable (C₂ * fun ω ↦ X ω ^ 2) μ
    exact hC₂X₂.integrable_mul hC₂ hX₂
  have hC₂Y_int : Integrable (fun ω ↦ C₂ ω * Y ω ^ 2) μ := by
    change Integrable (C₂ * fun ω ↦ Y ω ^ 2) μ
    exact hC₂Y₂.integrable_mul hC₂ hY₂
  have hC₂X_div : Integrable (fun ω ↦ C₂ ω * X ω ^ 2 / 2) μ := by
    simpa only [div_eq_mul_inv] using hC₂X_int.mul_const (2 : ℝ)⁻¹
  have hC₂Y_div : Integrable (fun ω ↦ C₂ ω * Y ω ^ 2 / 2) μ := by
    simpa only [div_eq_mul_inv] using hC₂Y_int.mul_const (2 : ℝ)⁻¹
  have hPX : Integrable P_X μ := by
    dsimp only [P_X]
    exact (hC₀.add hC₁X_int).add hC₂X_div
  have hPY : Integrable P_Y μ := by
    dsimp only [P_Y]
    exact (hC₀.add hC₁Y_int).add hC₂Y_div
  have hlin₁X :
      (∫ ω, C₁ ω * X ω ∂μ) = (∫ ω, C₁ ω ∂μ) * ∫ ω, X ω ∂μ :=
    hC₁X.integral_fun_mul_eq_mul_integral hC₁.1 hX.1
  have hlin₁Y :
      (∫ ω, C₁ ω * Y ω ∂μ) = (∫ ω, C₁ ω ∂μ) * ∫ ω, Y ω ∂μ :=
    hC₁Y.integral_fun_mul_eq_mul_integral hC₁.1 hY.1
  have hlin₂X :
      (∫ ω, C₂ ω * X ω ^ 2 ∂μ) =
        (∫ ω, C₂ ω ∂μ) * ∫ ω, X ω ^ 2 ∂μ :=
    hC₂X₂.integral_fun_mul_eq_mul_integral hC₂.1 hX₂.1
  have hlin₂Y :
      (∫ ω, C₂ ω * Y ω ^ 2 ∂μ) =
        (∫ ω, C₂ ω ∂μ) * ∫ ω, Y ω ^ 2 ∂μ :=
    hC₂Y₂.integral_fun_mul_eq_mul_integral hC₂.1 hY₂.1
  have hP_eq : (∫ ω, P_X ω ∂μ) = ∫ ω, P_Y ω ∂μ := by
    dsimp only [P_X, P_Y]
    calc
      (∫ ω, C₀ ω + C₁ ω * X ω + C₂ ω * X ω ^ 2 / 2 ∂μ) =
          (∫ ω, C₀ ω + C₁ ω * X ω ∂μ) +
            ∫ ω, C₂ ω * X ω ^ 2 / 2 ∂μ :=
        integral_add (hC₀.add hC₁X_int) hC₂X_div
      _ = ((∫ ω, C₀ ω ∂μ) + ∫ ω, C₁ ω * X ω ∂μ) +
            (∫ ω, C₂ ω * X ω ^ 2 ∂μ) / 2 := by
        rw [integral_add hC₀ hC₁X_int, integral_div]
      _ = ((∫ ω, C₀ ω ∂μ) + ∫ ω, C₁ ω * Y ω ∂μ) +
            (∫ ω, C₂ ω * Y ω ^ 2 ∂μ) / 2 := by
        rw [hlin₁X, hlin₁Y, hlin₂X, hlin₂Y, hmean, hsecond]
      _ = (∫ ω, C₀ ω + C₁ ω * Y ω ∂μ) +
            ∫ ω, C₂ ω * Y ω ^ 2 / 2 ∂μ := by
        rw [integral_add hC₀ hC₁Y_int, integral_div]
      _ = ∫ ω, C₀ ω + C₁ ω * Y ω + C₂ ω * Y ω ^ 2 / 2 ∂μ :=
        (integral_add (hC₀.add hC₁Y_int) hC₂Y_div).symm
  have hRX : Integrable (fun ω ↦ F_X ω - P_X ω) μ := hFX.sub hPX
  have hRY : Integrable (fun ω ↦ F_Y ω - P_Y ω) μ := hFY.sub hPY
  have hboundX :
      |∫ ω, F_X ω - P_X ω ∂μ| ≤ K * ∫ ω, |X ω| ^ 3 ∂μ := by
    calc
      |∫ ω, F_X ω - P_X ω ∂μ| ≤ ∫ ω, K * |X ω| ^ 3 ∂μ := by
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_of_norm_le (f := fun ω ↦ F_X ω - P_X ω)
            (hX₃.const_mul K) (by
              filter_upwards [hremX] with ω hω
              simpa only [P_X, Real.norm_eq_abs] using hω))
      _ = K * ∫ ω, |X ω| ^ 3 ∂μ := by rw [integral_const_mul]
  have hboundY :
      |∫ ω, F_Y ω - P_Y ω ∂μ| ≤ K * ∫ ω, |Y ω| ^ 3 ∂μ := by
    calc
      |∫ ω, F_Y ω - P_Y ω ∂μ| ≤ ∫ ω, K * |Y ω| ^ 3 ∂μ := by
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_of_norm_le (f := fun ω ↦ F_Y ω - P_Y ω)
            (hY₃.const_mul K) (by
              filter_upwards [hremY] with ω hω
              simpa only [P_Y, Real.norm_eq_abs] using hω))
      _ = K * ∫ ω, |Y ω| ^ 3 ∂μ := by rw [integral_const_mul]
  have hrewrite :
      (∫ ω, F_X ω ∂μ) - ∫ ω, F_Y ω ∂μ =
        (∫ ω, F_X ω - P_X ω ∂μ) - ∫ ω, F_Y ω - P_Y ω ∂μ := by
    rw [integral_sub hFX hPX, integral_sub hFY hPY, hP_eq]
    ring
  rw [hrewrite]
  calc
    |(∫ ω, F_X ω - P_X ω ∂μ) - ∫ ω, F_Y ω - P_Y ω ∂μ| ≤
        |∫ ω, F_X ω - P_X ω ∂μ| + |∫ ω, F_Y ω - P_Y ω ∂μ| := abs_sub _ _
    _ ≤ K * (∫ ω, |X ω| ^ 3 ∂μ) + K * (∫ ω, |Y ω| ^ 3 ∂μ) :=
      add_le_add hboundX hboundY
    _ = K * ((∫ ω, |X ω| ^ 3 ∂μ) + ∫ ω, |Y ω| ^ 3 ∂μ) := by ring

lemma integral_hybridRootExpNegLogSumExpZero_step {N k : ℕ} (hk : k < N)
    {β γ : ℝ} (hβ : 0 < β) (hγ : 0 ≤ γ) :
    |(∫ ω, hybridRootExpNegLogSumExpZero N k β γ ω ∂coupledMeasure) -
        ∫ ω, hybridRootExpNegLogSumExpZero N (k + 1) β γ ω ∂coupledMeasure| ≤
      hybridCubicError N β γ *
        ((∫ ω, |coupledSign k ω| ^ 3 ∂coupledMeasure) +
          ∫ ω, |coupledGaussian k ω| ^ 3 ∂coupledMeasure) := by
  apply integral_lindeberg_step
    (X := coupledSign k) (Y := coupledGaussian k)
    (C₀ := hybridTaylorCoeffZero N k β γ)
    (C₁ := hybridTaylorCoeffOne N k β γ)
    (C₂ := hybridTaylorCoeffTwo N k β γ)
    (F_X := hybridRootExpNegLogSumExpZero N k β γ)
    (F_Y := hybridRootExpNegLogSumExpZero N (k + 1) β γ)
    (K := hybridCubicError N β γ)
  · exact hybridCubicError_nonneg N hβ.le hγ
  · exact integrable_coupledSign k
  · exact integrable_coupledGaussian k
  · exact integrable_sq_coupledSign k
  · exact integrable_sq_coupledGaussian k
  · exact integrable_abs_cube_coupledSign k
  · exact integrable_abs_cube_coupledGaussian k
  · exact integrable_hybridTaylorCoeffZero N k hβ hγ
  · exact integrable_hybridTaylorCoeffOne N k hβ hγ
  · exact integrable_hybridTaylorCoeffTwo N k hβ hγ
  · exact integrable_hybridRootExpNegLogSumExpZero N k hβ hγ
  · exact integrable_hybridRootExpNegLogSumExpZero N (k + 1) hβ hγ
  · exact indepFun_hybridTaylorCoeffOne_coupledSign hk β γ
  · exact indepFun_hybridTaylorCoeffOne_coupledGaussian hk β γ
  · exact indepFun_hybridTaylorCoeffTwo_coupledSign hk β γ
  · exact indepFun_hybridTaylorCoeffTwo_coupledGaussian hk β γ
  · rw [integral_coupledSign, integral_coupledGaussian]
  · rw [integral_sq_coupledSign, integral_sq_coupledGaussian]
  · exact ae_of_all _ (hybridRoot_taylor_sign hk hβ hγ)
  · exact ae_of_all _ (hybridRoot_taylor_gaussian hk hβ hγ)

lemma abs_sub_le_sum_range_abs_sub (a : ℕ → ℝ) (N : ℕ) :
    |a 0 - a N| ≤ ∑ k ∈ Finset.range N, |a k - a (k + 1)| := by
  induction N with
  | zero => simp
  | succ N ih =>
      calc
        |a 0 - a (N + 1)| = |(a 0 - a N) + (a N - a (N + 1))| := by congr 1 <;> ring
        _ ≤ |a 0 - a N| + |a N - a (N + 1)| := abs_add_le _ _
        _ ≤ (∑ k ∈ Finset.range N, |a k - a (k + 1)|) +
            |a N - a (N + 1)| := by gcongr
        _ = ∑ k ∈ Finset.range (N + 1), |a k - a (k + 1)| := by
          rw [Finset.sum_range_succ]

lemma integral_abs_cube_coupledSign (k : ℕ) :
    (∫ ω, |coupledSign k ω| ^ 3 ∂coupledMeasure) = 1 := by
  calc
    (∫ ω, |coupledSign k ω| ^ 3 ∂coupledMeasure) =
        ∫ x : ℝ, |x| ^ 3 ∂rademacherMeasure := by
      simpa only [Function.comp_apply] using
        (hasLaw_coupledSign k).integral_comp (f := fun x : ℝ ↦ |x| ^ 3) (by fun_prop)
    _ = 1 := by
      simp only [rademacherMeasure, integral_bernoulliMeasure, one_smul, neg_smul,
        smul_eq_mul]
      norm_num

def standardGaussianAbsCube : ℝ :=
  ∫ x : ℝ, |x| ^ 3 ∂standardGaussianMeasure

lemma integral_abs_cube_coupledGaussian (k : ℕ) :
    (∫ ω, |coupledGaussian k ω| ^ 3 ∂coupledMeasure) = standardGaussianAbsCube := by
  unfold standardGaussianAbsCube
  simpa only [Function.comp_apply] using
    (hasLaw_coupledGaussian k).integral_comp (f := fun x : ℝ ↦ |x| ^ 3) (by fun_prop)

lemma integral_hybridRootExpNegLogSumExpZero_endpoints {N : ℕ} {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 ≤ γ) :
    |(∫ ω, hybridRootExpNegLogSumExpZero N 0 β γ ω ∂coupledMeasure) -
        ∫ ω, hybridRootExpNegLogSumExpZero N N β γ ω ∂coupledMeasure| ≤
      (N : ℝ) * hybridCubicError N β γ * (1 + standardGaussianAbsCube) := by
  let A : ℕ → ℝ := fun m ↦
    ∫ ω, hybridRootExpNegLogSumExpZero N m β γ ω ∂coupledMeasure
  calc
    |(∫ ω, hybridRootExpNegLogSumExpZero N 0 β γ ω ∂coupledMeasure) -
        ∫ ω, hybridRootExpNegLogSumExpZero N N β γ ω ∂coupledMeasure| =
        |A 0 - A N| := rfl
    _ ≤ ∑ k ∈ Finset.range N, |A k - A (k + 1)| :=
      abs_sub_le_sum_range_abs_sub A N
    _ ≤ ∑ k ∈ Finset.range N,
        hybridCubicError N β γ * (1 + standardGaussianAbsCube) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkN := Finset.mem_range.mp hk
      simpa only [A, integral_abs_cube_coupledSign,
        integral_abs_cube_coupledGaussian] using
        integral_hybridRootExpNegLogSumExpZero_step hkN hβ hγ
    _ = (N : ℝ) * hybridCubicError N β γ * (1 + standardGaussianAbsCube) := by
      simp
      ring

lemma iIndepFun_coupledGaussian :
    iIndepFun (fun k ↦ coupledGaussian k) coupledMeasure := by
  have h := iIndepFun_coupledCoordinate.comp (fun _ ↦ Prod.snd)
    (fun _ ↦ measurable_snd)
  convert h using 1 <;> funext ω <;> rfl

lemma iIndepFun_coupledSign :
    iIndepFun (fun k ↦ coupledSign k) coupledMeasure := by
  have h := iIndepFun_coupledCoordinate.comp (fun _ ↦ Prod.fst)
    (fun _ ↦ measurable_fst)
  convert h using 1 <;> funext ω <;> rfl

def coupledSigns (ω : CoupledSample) : Sample := fun k ↦ coupledSign k ω

lemma hasLaw_coupledSigns : HasLaw coupledSigns signMeasure coupledMeasure := by
  change HasLaw (fun ω k ↦ coupledSign k ω) signMeasure coupledMeasure
  unfold signMeasure
  exact iIndepFun_coupledSign.hasLaw_infinitePi hasLaw_coupledSign
    ((measurable_pi_iff.2 fun k ↦ measurable_coupledSign k).aemeasurable)

lemma hasGaussianLaw_coupledGaussian (k : ℕ) :
    HasGaussianLaw (coupledGaussian k) coupledMeasure := by
  letI : IsGaussian standardGaussianMeasure := by
    unfold standardGaussianMeasure
    infer_instance
  exact (hasLaw_coupledGaussian k).hasGaussianLaw

abbrev RootFrequency (N : ℕ) := ↥(frequencySet N)

def gaussianRootProjection (N : ℕ) (r : RootFrequency N) (ω : CoupledSample) : ℝ :=
  ∑ k : Fin N, normalizedRootCoeff N r.1 k.1 * coupledGaussian k.1 ω

noncomputable def gaussianRootTransform (N : ℕ) :
    (Fin N → ℝ) →L[ℝ] (RootFrequency N → ℝ) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun x r ↦ ∑ k : Fin N, normalizedRootCoeff N r.1 k.1 * x k
    map_add' := by
      intro x y
      funext r
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    map_smul' := by
      intro c x
      funext r
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      change normalizedRootCoeff N r.1 k.1 * (c * x k) =
        c * (normalizedRootCoeff N r.1 k.1 * x k)
      ring }

lemma hasGaussianLaw_gaussianCoordinates (N : ℕ) :
    HasGaussianLaw (fun ω (k : Fin N) ↦ coupledGaussian k.1 ω) coupledMeasure := by
  have hind : iIndepFun (fun k : Fin N ↦ coupledGaussian k.1) coupledMeasure :=
    iIndepFun_coupledGaussian.precomp Fin.val_injective
  exact hind.hasGaussianLaw (fun k ↦ hasGaussianLaw_coupledGaussian k.1)

lemma hasGaussianLaw_gaussianRootProjection (N : ℕ) :
    @HasGaussianLaw CoupledSample (RootFrequency N → ℝ) _
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace
      Pi.normedAddCommGroup.toAddCommMonoid Pi.normedSpace.toModule _
      (fun ω (r : RootFrequency N) ↦ gaussianRootProjection N r ω)
      coupledMeasure := by
  have h := (hasGaussianLaw_gaussianCoordinates N).map_fun (gaussianRootTransform N)
  convert h using 1
  funext ω r
  rfl

lemma sum_frequency_re_mul_re_eq_zero {N r s : ℕ} (hN : 4 ≤ N)
    (hr : r ∈ frequencySet N) (hs : s ∈ frequencySet N) (hrs : r ≠ s) :
    ∑ k ∈ Finset.range N,
      (standardRoot N ^ (r * k)).re * (standardRoot N ^ (s * k)).re = 0 := by
  have hN0 : N ≠ 0 := by omega
  have htwo := sum_two_rootRealProjection_coeff_sq N r s hN hr hs hrs
  have hrr := sum_standardRoot_pow_re_sq N r hN0
    (frequencySet_not_dvd_two_mul hN hr)
  have hss := sum_standardRoot_pow_re_sq N s hN0
    (frequencySet_not_dvd_two_mul hN hs)
  have hexpand := sum_add_sq (Finset.range N)
    (fun k ↦ (standardRoot N ^ (r * k)).re)
    (fun k ↦ (standardRoot N ^ (s * k)).re)
  rw [htwo, hrr, hss] at hexpand
  linarith

lemma sum_normalizedRootCoeff_sq {N r : ℕ} (hN : 4 ≤ N)
    (hr : r ∈ frequencySet N) :
    ∑ k : Fin N, normalizedRootCoeff N r k.1 ^ 2 = 1 := by
  have hN0 : N ≠ 0 := by omega
  have hsum := sum_standardRoot_pow_re_sq N r hN0
    (frequencySet_not_dvd_two_mul hN hr)
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ normalizedRootCoeff N r k ^ 2) N]
  unfold normalizedRootCoeff
  have hq : 0 ≤ 2 / (N : ℝ) := by positivity
  have hsqrt : Real.sqrt (2 / (N : ℝ)) ^ 2 = 2 / (N : ℝ) :=
    Real.sq_sqrt hq
  simp_rw [mul_pow, hsqrt]
  rw [← Finset.mul_sum, hsum]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN0
  field_simp

lemma sum_normalizedRootCoeff_mul_eq_zero {N r s : ℕ} (hN : 4 ≤ N)
    (hr : r ∈ frequencySet N) (hs : s ∈ frequencySet N) (hrs : r ≠ s) :
    ∑ k : Fin N,
      normalizedRootCoeff N r k.1 * normalizedRootCoeff N s k.1 = 0 := by
  have hcross := sum_frequency_re_mul_re_eq_zero hN hr hs hrs
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ ↦
    normalizedRootCoeff N r k * normalizedRootCoeff N s k) N]
  unfold normalizedRootCoeff
  have hq : 0 ≤ 2 / (N : ℝ) := by positivity
  have hsqrt : Real.sqrt (2 / (N : ℝ)) * Real.sqrt (2 / (N : ℝ)) =
      2 / (N : ℝ) := Real.mul_self_sqrt hq
  calc
    ∑ k ∈ Finset.range N,
        (Real.sqrt (2 / (N : ℝ)) * (standardRoot N ^ (r * k)).re) *
          (Real.sqrt (2 / (N : ℝ)) * (standardRoot N ^ (s * k)).re) =
        (2 / (N : ℝ)) * ∑ k ∈ Finset.range N,
          (standardRoot N ^ (r * k)).re * (standardRoot N ^ (s * k)).re := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      calc
        (Real.sqrt (2 / (N : ℝ)) * (standardRoot N ^ (r * k)).re) *
            (Real.sqrt (2 / (N : ℝ)) * (standardRoot N ^ (s * k)).re) =
            (Real.sqrt (2 / (N : ℝ)) * Real.sqrt (2 / (N : ℝ))) *
              ((standardRoot N ^ (r * k)).re *
                (standardRoot N ^ (s * k)).re) := by ring
        _ = (2 / (N : ℝ)) * ((standardRoot N ^ (r * k)).re *
              (standardRoot N ^ (s * k)).re) := by rw [hsqrt]
    _ = 0 := by rw [hcross, mul_zero]

lemma memLp_two_coupledGaussian (k : ℕ) :
    MemLp (coupledGaussian k) 2 coupledMeasure :=
  (hasGaussianLaw_coupledGaussian k).memLp_two

lemma covariance_coupledGaussian (k l : ℕ) :
    cov[coupledGaussian k, coupledGaussian l; coupledMeasure] = if k = l then 1 else 0 := by
  by_cases hkl : k = l
  · subst l
    rw [if_pos rfl, covariance_self (measurable_coupledGaussian k).aemeasurable,
      variance_eq_integral (measurable_coupledGaussian k).aemeasurable,
      integral_coupledGaussian]
    simp only [sub_zero]
    exact integral_sq_coupledGaussian k
  · rw [if_neg hkl]
    exact (iIndepFun_coupledGaussian.indepFun hkl).covariance_eq_zero
      (memLp_two_coupledGaussian k) (memLp_two_coupledGaussian l)

lemma covariance_gaussianRootProjection (N : ℕ) (r s : RootFrequency N) :
    cov[gaussianRootProjection N r, gaussianRootProjection N s; coupledMeasure] =
      ∑ k : Fin N, normalizedRootCoeff N r.1 k.1 * normalizedRootCoeff N s.1 k.1 := by
  unfold gaussianRootProjection
  rw [covariance_fun_sum_fun_sum
    (fun k : Fin N ↦ (memLp_two_coupledGaussian k.1).const_mul _)
    (fun k : Fin N ↦ (memLp_two_coupledGaussian k.1).const_mul _)]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right,
    covariance_coupledGaussian]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [Finset.sum_eq_single k]
  · simp
  · intro l _hl hlk
    have hval : k.1 ≠ l.1 := by
      intro h
      apply hlk
      exact Fin.ext h.symm
    simp [hval]
  · simp

lemma variance_gaussianRootProjection {N : ℕ} (hN : 4 ≤ N) (r : RootFrequency N) :
    Var[gaussianRootProjection N r; coupledMeasure] = 1 := by
  have hm : Measurable (gaussianRootProjection N r) := by
    unfold gaussianRootProjection
    apply Finset.measurable_sum
    intro k _hk
    exact measurable_const.mul (measurable_coupledGaussian k.1)
  rw [← covariance_self hm.aemeasurable, covariance_gaussianRootProjection]
  simpa only [pow_two] using sum_normalizedRootCoeff_sq hN r.2

lemma integral_gaussianRootProjection (N : ℕ) (r : RootFrequency N) :
    (∫ ω, gaussianRootProjection N r ω ∂coupledMeasure) = 0 := by
  unfold gaussianRootProjection
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro k _hk
    rw [integral_const_mul, integral_coupledGaussian, mul_zero]
  · intro k _hk
    exact (integrable_coupledGaussian k.1).const_mul _

lemma iIndepFun_gaussianRootProjection {N : ℕ} (hN : 4 ≤ N) :
    iIndepFun (gaussianRootProjection N) coupledMeasure := by
  apply (hasGaussianLaw_gaussianRootProjection N).iIndepFun_of_covariance_eq_zero
  intro r s hrs
  rw [covariance_gaussianRootProjection]
  apply sum_normalizedRootCoeff_mul_eq_zero hN r.2 s.2
  intro h
  apply hrs
  exact Subtype.ext h

lemma hasLaw_gaussianRootProjection {N : ℕ} (hN : 4 ≤ N) (r : RootFrequency N) :
    HasLaw (gaussianRootProjection N r) standardGaussianMeasure coupledMeasure := by
  have hg : HasGaussianLaw (gaussianRootProjection N r) coupledMeasure :=
    (hasGaussianLaw_gaussianRootProjection N).eval r
  refine ⟨hg.aemeasurable, ?_⟩
  rw [hg.map_eq_gaussianReal, integral_gaussianRootProjection,
    variance_gaussianRootProjection hN]
  simp [standardGaussianMeasure]

def normalizedRootRealProjection (ω : Sample) (N r : ℕ) : ℝ :=
  Real.sqrt (2 / (N : ℝ)) * rootRealProjection ω N r

lemma normalizedRootRealProjection_eq_sum (ω : Sample) (N r : ℕ) :
    normalizedRootRealProjection ω N r =
      ∑ k ∈ Finset.range N, normalizedRootCoeff N r k * ω k := by
  unfold normalizedRootRealProjection rootRealProjection linearForm normalizedRootCoeff
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  ring

lemma hybridRootProjection_zero (N r : ℕ) (ω : CoupledSample) :
    hybridRootProjection N 0 r ω = normalizedRootRealProjection (coupledSigns ω) N r := by
  rw [normalizedRootRealProjection_eq_sum]
  unfold hybridRootProjection coupledSigns hybridInput
  simp only [Nat.not_lt_zero, ↓reduceIte]

lemma hybridRootProjection_allGaussian (N : ℕ) (r : RootFrequency N)
    (ω : CoupledSample) :
    hybridRootProjection N N r.1 ω = gaussianRootProjection N r ω := by
  unfold hybridRootProjection gaussianRootProjection hybridInput
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ ↦ normalizedRootCoeff N r.1 k * coupledGaussian k ω) N]
  apply Finset.sum_congr rfl
  intro k hk
  rw [if_pos (Finset.mem_range.mp hk)]

lemma gaussianPDF_standard_antitone_nonneg {t x : ℝ} (ht : 0 ≤ t)
    (hx : x ∈ Icc t (t + 1)) :
    gaussianPDF 0 1 (t + 1) ≤ gaussianPDF 0 1 x := by
  unfold gaussianPDF gaussianPDFReal
  apply ENNReal.ofReal_le_ofReal
  have hx0 : 0 ≤ x := ht.trans hx.1
  have ht1 : 0 ≤ t + 1 := by linarith
  have hsq : x ^ 2 ≤ (t + 1) ^ 2 := (sq_le_sq₀ hx0 ht1).2 hx.2
  apply mul_le_mul_of_nonneg_left
  · apply Real.exp_le_exp.mpr
    norm_num
    linarith
  · positivity

lemma standardGaussianMeasure_Icc_lower {t : ℝ} (ht : 0 ≤ t) :
    gaussianPDF 0 1 (t + 1) ≤ standardGaussianMeasure (Icc t (t + 1)) := by
  unfold standardGaussianMeasure
  rw [gaussianReal_apply 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  calc
    gaussianPDF 0 1 (t + 1) =
        ∫⁻ _x : ℝ in Icc t (t + 1), gaussianPDF 0 1 (t + 1) := by
      rw [setLIntegral_const, Real.volume_Icc]
      simp
    _ ≤ ∫⁻ x : ℝ in Icc t (t + 1), gaussianPDF 0 1 x :=
      setLIntegral_mono (measurable_gaussianPDF 0 1)
        (fun x hx ↦ gaussianPDF_standard_antitone_nonneg ht hx)

def gaussianAllBelow (N : ℕ) (t : ℝ) : Set CoupledSample :=
  ⋂ r : RootFrequency N, {ω | gaussianRootProjection N r ω < t}

lemma measure_gaussianAllBelow {N : ℕ} (hN : 4 ≤ N) (t : ℝ) :
    coupledMeasure (gaussianAllBelow N t) =
      ∏ _r : RootFrequency N, standardGaussianMeasure (Iio t) := by
  have hprod := (iIndepFun_gaussianRootProjection hN).measure_inter_preimage_eq_mul
    (Finset.univ : Finset (RootFrequency N))
    (sets := fun _r ↦ Iio t) (fun _r _hr ↦ measurableSet_Iio)
  rw [show gaussianAllBelow N t =
      ⋂ r ∈ (Finset.univ : Finset (RootFrequency N)),
        gaussianRootProjection N r ⁻¹' Iio t by
    ext ω
    simp [gaussianAllBelow]]
  rw [hprod]
  apply Finset.prod_congr rfl
  intro r _hr
  exact (hasLaw_gaussianRootProjection hN r).measure_eq measurableSet_Iio

lemma measurableSet_gaussianAllBelow (N : ℕ) (t : ℝ) :
    MeasurableSet (gaussianAllBelow N t) := by
  unfold gaussianAllBelow
  apply MeasurableSet.iInter
  intro r
  have hm : Measurable (gaussianRootProjection N r) := by
    unfold gaussianRootProjection
    apply Finset.measurable_sum
    intro k _hk
    exact measurable_const.mul (measurable_coupledGaussian k.1)
  exact measurableSet_lt hm measurable_const

lemma hybridRootProjection_le_logSumExpZero {N m r : ℕ}
    (hr : r ∈ frequencySet N) {β : ℝ} (hβ : 0 < β) (ω : CoupledSample) :
    hybridRootProjection N m r ω ≤ hybridRootLogSumExpZero N m β ω := by
  have hterm : Real.exp (β * hybridRootProjection N m r ω) ≤
      ∑ s ∈ frequencySet N, Real.exp (β * hybridRootProjection N m s ω) := by
    exact Finset.single_le_sum
      (f := fun s ↦ Real.exp (β * hybridRootProjection N m s ω))
      (fun s _hs ↦ Real.exp_nonneg _) hr
  have hsum : Real.exp (β * hybridRootProjection N m r ω) ≤
      1 + ∑ s ∈ frequencySet N, Real.exp (β * hybridRootProjection N m s ω) :=
    hterm.trans (le_add_of_nonneg_left zero_le_one)
  have hlog := Real.log_le_log (Real.exp_pos _) hsum
  rw [Real.log_exp] at hlog
  unfold hybridRootLogSumExpZero
  rw [le_div_iff₀ hβ]
  nlinarith

lemma hybridRootExpNegLogSumExpZero_allGaussian_le {N : ℕ} (hN : 4 ≤ N)
    {β γ t : ℝ} (hβ : 0 < β) (hγ : 0 ≤ γ) (ω : CoupledSample) :
    hybridRootExpNegLogSumExpZero N N β γ ω ≤
      Real.exp (-γ * t) +
        (gaussianAllBelow N t).indicator (1 : CoupledSample → ℝ) ω := by
  by_cases hbelow : ω ∈ gaussianAllBelow N t
  · have hle : hybridRootExpNegLogSumExpZero N N β γ ω ≤ 1 := by
      unfold hybridRootExpNegLogSumExpZero
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγ)
        (hybridRootLogSumExpZero_nonneg N N hβ ω)
    simp only [Set.indicator_of_mem hbelow, Pi.one_apply]
    linarith [Real.exp_pos (-γ * t)]
  · have hexists : ∃ r : RootFrequency N,
        t ≤ gaussianRootProjection N r ω := by
      simp only [gaussianAllBelow, Set.mem_iInter, Set.mem_setOf_eq] at hbelow
      push_neg at hbelow
      exact hbelow
    obtain ⟨r, hr⟩ := hexists
    have hL : t ≤ hybridRootLogSumExpZero N N β ω := by
      calc
        t ≤ gaussianRootProjection N r ω := hr
        _ = hybridRootProjection N N r.1 ω := (hybridRootProjection_allGaussian N r ω).symm
        _ ≤ hybridRootLogSumExpZero N N β ω :=
          hybridRootProjection_le_logSumExpZero r.2 hβ ω
    simp only [Set.indicator_of_notMem hbelow, Pi.one_apply, add_zero]
    unfold hybridRootExpNegLogSumExpZero
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hL (neg_nonpos.mpr hγ)

lemma integral_hybridRootExpNegLogSumExpZero_allGaussian_le {N : ℕ} (hN : 4 ≤ N)
    {β γ t : ℝ} (hβ : 0 < β) (hγ : 0 ≤ γ) :
    (∫ ω, hybridRootExpNegLogSumExpZero N N β γ ω ∂coupledMeasure) ≤
      Real.exp (-γ * t) + coupledMeasure.real (gaussianAllBelow N t) := by
  let G : CoupledSample → ℝ := fun ω ↦
    Real.exp (-γ * t) + (gaussianAllBelow N t).indicator (1 : CoupledSample → ℝ) ω
  have hset := measurableSet_gaussianAllBelow N t
  have hG : Integrable G coupledMeasure := by
    exact (integrable_const (c := Real.exp (-γ * t))).add
      ((integrable_const (c := (1 : ℝ))).indicator hset)
  have hmono := integral_mono
    (integrable_hybridRootExpNegLogSumExpZero N N hβ hγ) hG
    (hybridRootExpNegLogSumExpZero_allGaussian_le hN hβ hγ)
  calc
    (∫ ω, hybridRootExpNegLogSumExpZero N N β γ ω ∂coupledMeasure) ≤
        ∫ ω, G ω ∂coupledMeasure := hmono
    _ = Real.exp (-γ * t) + coupledMeasure.real (gaussianAllBelow N t) := by
      unfold G
      calc
        (∫ ω, Real.exp (-γ * t) +
            (gaussianAllBelow N t).indicator (1 : CoupledSample → ℝ) ω
            ∂coupledMeasure) =
            (∫ _ω : CoupledSample, Real.exp (-γ * t) ∂coupledMeasure) +
              ∫ ω, (gaussianAllBelow N t).indicator (1 : CoupledSample → ℝ) ω
                ∂coupledMeasure := by
          apply integral_add
          · exact integrable_const _
          · exact (integrable_const (c := (1 : ℝ))).indicator hset
        _ = Real.exp (-γ * t) + coupledMeasure.real (gaussianAllBelow N t) := by
          rw [integral_const, integral_indicator_one hset]
          simp

def signAllAtMost (N : ℕ) (u : ℝ) : Set Sample :=
  ⋂ r : RootFrequency N, {ω | normalizedRootRealProjection ω N r.1 ≤ u}

lemma measurableSet_signAllAtMost (N : ℕ) (u : ℝ) :
    MeasurableSet (signAllAtMost N u) := by
  unfold signAllAtMost
  apply MeasurableSet.iInter
  intro r
  exact measurableSet_le
    (by
      unfold normalizedRootRealProjection
      exact measurable_const.mul (measurable_rootRealProjection N r.1))
    measurable_const

lemma hybridRootLogSumExpZero_le {N m : ℕ} {β u : ℝ}
    (hβ : 0 < β) (hu : 0 ≤ u) (ω : CoupledSample)
    (hproj : ∀ r ∈ frequencySet N, hybridRootProjection N m r ω ≤ u) :
    hybridRootLogSumExpZero N m β ω ≤
      u + Real.log ((frequencySet N).card + 1 : ℝ) / β := by
  have hexp : ∀ r ∈ frequencySet N,
      Real.exp (β * hybridRootProjection N m r ω) ≤ Real.exp (β * u) := by
    intro r hr
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hproj r hr) hβ.le)
  have hsum : 1 + ∑ r ∈ frequencySet N,
      Real.exp (β * hybridRootProjection N m r ω) ≤
      ((frequencySet N).card + 1 : ℝ) * Real.exp (β * u) := by
    calc
      1 + ∑ r ∈ frequencySet N,
          Real.exp (β * hybridRootProjection N m r ω) ≤
          1 + ∑ _r ∈ frequencySet N, Real.exp (β * u) := by
        gcongr
        exact hproj r ‹r ∈ frequencySet N›
      _ = 1 + ((frequencySet N).card : ℝ) * Real.exp (β * u) := by simp
      _ ≤ Real.exp (β * u) + ((frequencySet N).card : ℝ) * Real.exp (β * u) := by
        gcongr
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (mul_nonneg hβ.le hu)
      _ = ((frequencySet N).card + 1 : ℝ) * Real.exp (β * u) := by ring
  have hcard : 0 < ((frequencySet N).card + 1 : ℝ) := by positivity
  have hlog := Real.log_le_log (by positivity) hsum
  rw [Real.log_mul (ne_of_gt hcard) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at hlog
  unfold hybridRootLogSumExpZero
  rw [div_le_iff₀ hβ]
  calc
    Real.log (1 + ∑ r ∈ frequencySet N,
        Real.exp (β * hybridRootProjection N m r ω)) ≤
        Real.log ((frequencySet N).card + 1 : ℝ) + β * u := hlog
    _ = (u + Real.log ((frequencySet N).card + 1 : ℝ) / β) * β := by
      field_simp
      ring

lemma coupledSigns_mem_signAllAtMost_iff (N : ℕ) (u : ℝ) (ω : CoupledSample) :
    coupledSigns ω ∈ signAllAtMost N u ↔
      ∀ r ∈ frequencySet N, hybridRootProjection N 0 r ω ≤ u := by
  simp only [signAllAtMost, Set.mem_iInter, Set.mem_setOf_eq]
  constructor
  · intro h r hr
    simpa only [hybridRootProjection_zero] using h ⟨r, hr⟩
  · intro h r
    simpa only [hybridRootProjection_zero] using h r.1 r.2

lemma exp_neg_softmax_le_signFunctional {N : ℕ} {β γ u : ℝ}
    (hβ : 0 < β) (hγ : 0 ≤ γ) (hu : 0 ≤ u) (ω : CoupledSample)
    (hω : coupledSigns ω ∈ signAllAtMost N u) :
    Real.exp (-γ * (u + Real.log ((frequencySet N).card + 1 : ℝ) / β)) ≤
      hybridRootExpNegLogSumExpZero N 0 β γ ω := by
  have hL := hybridRootLogSumExpZero_le hβ hu ω
    ((coupledSigns_mem_signAllAtMost_iff N u ω).1 hω)
  unfold hybridRootExpNegLogSumExpZero
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left hL (neg_nonpos.mpr hγ)

lemma measureReal_signAllAtMost_le {N : ℕ} (hN : 4 ≤ N)
    {β γ u t : ℝ} (hβ : 0 < β) (hγ : 0 ≤ γ) (hu : 0 ≤ u) :
    signMeasure.real (signAllAtMost N u) ≤
      Real.exp (γ * (u + Real.log ((frequencySet N).card + 1 : ℝ) / β)) *
        (Real.exp (-γ * t) + coupledMeasure.real (gaussianAllBelow N t) +
          (N : ℝ) * hybridCubicError N β γ * (1 + standardGaussianAbsCube)) := by
  let B : ℝ := u + Real.log ((frequencySet N).card + 1 : ℝ) / β
  let c : ℝ := Real.exp (-γ * B)
  let F : CoupledSample → ℝ := hybridRootExpNegLogSumExpZero N 0 β γ
  let E : Set CoupledSample := coupledSigns ⁻¹' signAllAtMost N u
  have hc : 0 < c := Real.exp_pos _
  have hFnonneg : ∀ᵐ ω ∂coupledMeasure, 0 ≤ F ω := by
    filter_upwards with ω
    unfold F hybridRootExpNegLogSumExpZero
    positivity
  have hFint : Integrable F coupledMeasure :=
    integrable_hybridRootExpNegLogSumExpZero N 0 hβ hγ
  have hthreshold : E ⊆ {ω | c ≤ F ω} := by
    intro ω hω
    exact exp_neg_softmax_le_signFunctional hβ hγ hu ω hω
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hFnonneg hFint c
  have hpull : coupledMeasure.real E = signMeasure.real (signAllAtMost N u) := by
    unfold E
    exact hasLaw_coupledSigns.measureReal_eq (measurableSet_signAllAtMost N u)
  have hweighted : c * signMeasure.real (signAllAtMost N u) ≤
      ∫ ω, F ω ∂coupledMeasure := by
    calc
      c * signMeasure.real (signAllAtMost N u) = c * coupledMeasure.real E := by
        rw [hpull]
      _ ≤ c * coupledMeasure.real {ω | c ≤ F ω} := by
        apply mul_le_mul_of_nonneg_left
        · exact measureReal_mono (μ := coupledMeasure) hthreshold
        · exact hc.le
      _ ≤ ∫ ω, F ω ∂coupledMeasure := hmarkov
  have htelescope := integral_hybridRootExpNegLogSumExpZero_endpoints (N := N) hβ hγ
  have hI0IN : (∫ ω, F ω ∂coupledMeasure) ≤
      (∫ ω, hybridRootExpNegLogSumExpZero N N β γ ω ∂coupledMeasure) +
        (N : ℝ) * hybridCubicError N β γ * (1 + standardGaussianAbsCube) := by
    unfold F
    linarith [le_trans (le_abs_self
      ((∫ ω, hybridRootExpNegLogSumExpZero N 0 β γ ω ∂coupledMeasure) -
        ∫ ω, hybridRootExpNegLogSumExpZero N N β γ ω ∂coupledMeasure)) htelescope]
  have hgauss := integral_hybridRootExpNegLogSumExpZero_allGaussian_le hN hβ hγ
    (t := t)
  have hI : (∫ ω, F ω ∂coupledMeasure) ≤
      Real.exp (-γ * t) + coupledMeasure.real (gaussianAllBelow N t) +
        (N : ℝ) * hybridCubicError N β γ * (1 + standardGaussianAbsCube) := by
    linarith
  have hp : signMeasure.real (signAllAtMost N u) ≤
      Real.exp (γ * B) * ∫ ω, F ω ∂coupledMeasure := by
    calc
      signMeasure.real (signAllAtMost N u) ≤
          (∫ ω, F ω ∂coupledMeasure) / c := (le_div_iff₀ hc).2 (by
            simpa only [mul_comm] using hweighted)
      _ = Real.exp (γ * B) * ∫ ω, F ω ∂coupledMeasure := by
        simp [c, show -γ * B = -(γ * B) by ring, Real.exp_neg, mul_comm]
  simpa only [B] using hp.trans (mul_le_mul_of_nonneg_left hI (Real.exp_nonneg _))

lemma gaussianPDF_toReal_le_standardGaussian_tail {t : ℝ} (ht : 0 ≤ t) :
    (gaussianPDF 0 1 (t + 1)).toReal ≤ standardGaussianMeasure.real (Ici t) := by
  rw [measureReal_def]
  apply ENNReal.toReal_mono (by finiteness)
  exact (standardGaussianMeasure_Icc_lower ht).trans
    (measure_mono fun x hx ↦ hx.1)

lemma standardGaussianMeasure_real_Iio (t : ℝ) :
    standardGaussianMeasure.real (Iio t) =
      1 - standardGaussianMeasure.real (Ici t) := by
  have h := measureReal_compl (μ := standardGaussianMeasure) (s := Ici t) measurableSet_Ici
  rw [probReal_univ] at h
  simpa only [compl_Ici] using h

lemma measureReal_gaussianAllBelow_le_exp {N : ℕ} (hN : 4 ≤ N)
    {t : ℝ} (ht : 0 ≤ t) :
    coupledMeasure.real (gaussianAllBelow N t) ≤
      Real.exp (-((frequencySet N).card : ℝ) *
        (gaussianPDF 0 1 (t + 1)).toReal) := by
  let q : ℝ := (gaussianPDF 0 1 (t + 1)).toReal
  let p : ℝ := standardGaussianMeasure.real (Ici t)
  have hqp : q ≤ p := gaussianPDF_toReal_le_standardGaussian_tail ht
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hp1 : p ≤ 1 := by
    rw [← probReal_univ (μ := standardGaussianMeasure)]
    exact measureReal_mono (μ := standardGaussianMeasure) (subset_univ _)
  have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
  have hq1 : q ≤ 1 := hqp.trans hp1
  have hall : coupledMeasure.real (gaussianAllBelow N t) =
      (standardGaussianMeasure.real (Iio t)) ^ (frequencySet N).card := by
    rw [measureReal_def, measure_gaussianAllBelow hN,
      ENNReal.toReal_prod]
    simp only [measureReal_def, Finset.prod_const]
    rw [Finset.card_univ, Fintype.card_coe]
  calc
    coupledMeasure.real (gaussianAllBelow N t) =
        (1 - p) ^ (frequencySet N).card := by
      rw [hall, standardGaussianMeasure_real_Iio]
    _ ≤ (1 - q) ^ (frequencySet N).card := by
      apply pow_le_pow_left₀
      · linarith
      · linarith
    _ ≤ Real.exp (-q) ^ (frequencySet N).card := by
      exact pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg q) _
    _ = Real.exp (-((frequencySet N).card : ℝ) * q) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    _ = Real.exp (-((frequencySet N).card : ℝ) *
        (gaussianPDF 0 1 (t + 1)).toReal) := rfl

/-! ## Explicit parameter estimates for the lower bound -/

lemma card_frequencySet {N : ℕ} (hN : 4 ≤ N) :
    (frequencySet N).card = N / 4 := by
  simp [frequencySet, Nat.add_sub_cancel, Nat.le_div_iff_mul_le (by omega : 0 < 4)]

lemma quarter_le_card_frequencySet {N : ℕ} (hN : 4 ≤ N) :
    (N : ℝ) / 8 ≤ ((frequencySet N).card : ℝ) := by
  rw [card_frequencySet hN]
  have hq : 1 ≤ N / 4 := (Nat.le_div_iff_mul_le (by omega : 0 < 4)).2 hN
  have hr : N % 4 < 4 := Nat.mod_lt N (by omega)
  have hd : N % 4 + 4 * (N / 4) = N := Nat.mod_add_div N 4
  have h : N ≤ 8 * (N / 4) := by omega
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 8)]
  exact_mod_cast (by simpa [mul_comm] using h)

/-- The smoothing scale used in the quantitative Halász lower bound. -/
def lowerBeta (N : ℕ) : ℝ := Real.log N ^ 2

/-- The Laplace parameter used in the quantitative Halász lower bound. -/
def lowerGamma (N : ℕ) : ℝ := Real.sqrt (Real.log N) / 100

/-- The target level for the Rademacher projections. -/
def lowerSignLevel (δ : ℝ) (N : ℕ) : ℝ :=
  (1 - δ) * Real.sqrt (2 * Real.log N)

/-- The slightly larger comparison level for the independent Gaussian projections. -/
def lowerGaussianLevel (δ : ℝ) (N : ℕ) : ℝ :=
  (1 - δ / 2) * Real.sqrt (2 * Real.log N)

lemma lowerBeta_pos {N : ℕ} (hN : 2 ≤ N) : 0 < lowerBeta N := by
  unfold lowerBeta
  exact sq_pos_of_pos (Real.log_pos (by exact_mod_cast hN))

lemma lowerGamma_nonneg (N : ℕ) : 0 ≤ lowerGamma N := by
  unfold lowerGamma
  positivity

lemma lowerSignLevel_nonneg {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) : 0 ≤ lowerSignLevel δ N := by
  unfold lowerSignLevel
  positivity

lemma lowerGaussianLevel_nonneg {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) : 0 ≤ lowerGaussianLevel δ N := by
  unfold lowerGaussianLevel
  have : 0 ≤ 1 - δ / 2 := by linarith
  positivity

def standardGaussianDensityConstant : ℝ := (Real.sqrt (2 * Real.pi))⁻¹

lemma standardGaussianDensityConstant_pos : 0 < standardGaussianDensityConstant := by
  unfold standardGaussianDensityConstant
  positivity [Real.pi_pos]

lemma gaussianPDF_standard_toReal_eq (x : ℝ) :
    (gaussianPDF 0 1 x).toReal =
      standardGaussianDensityConstant * Real.exp (-x ^ 2 / 2) := by
  rw [toReal_gaussianPDF]
  simp [gaussianPDFReal, standardGaussianDensityConstant]

lemma tendsto_nat_log_atTop :
    Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma eventually_standardGaussianDensity_lower {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ᶠ N : ℕ in atTop,
      ((N : ℝ) ^ (-(1 - δ / 2) : ℝ)) ≤
        (gaussianPDF 0 1 (lowerGaussianLevel δ N + 1)).toReal := by
  let C : ℝ := standardGaussianDensityConstant
  let A : ℝ := |(1 / 2 : ℝ) - Real.log C|
  have hC : 0 < C := standardGaussianDensityConstant_pos
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ0
  have hlarge := tendsto_nat_log_atTop.eventually_ge_atTop
    (max 1 (max (128 / δ ^ 2) (8 * A / δ)))
  filter_upwards [hlarge, eventually_gt_atTop 0] with N hL hN
  let L : ℝ := Real.log (N : ℝ)
  let S : ℝ := Real.sqrt (2 * L)
  let a : ℝ := 1 - δ / 2
  let b : ℝ := 1 - δ / 2
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hL0 : 0 ≤ L := le_trans zero_le_one hL1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have ha0 : 0 ≤ a := by dsimp [a]; linarith
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hSsq : S ^ 2 = 2 * L := by
    dsimp [S]
    rw [Real.sq_sqrt]
    positivity
  have hLsqrt : 128 / δ ^ 2 ≤ L :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hL)
  have hscale : 128 ≤ δ ^ 2 * L := by
    calc
      128 = (128 / δ ^ 2) * δ ^ 2 := by field_simp
      _ ≤ L * δ ^ 2 := mul_le_mul_of_nonneg_right hLsqrt hδsq.le
      _ = δ ^ 2 * L := by ring
  have hS : S ≤ δ * L / 8 := by
    have hright : 0 ≤ δ * L / 8 := by positivity
    nlinarith [sq_nonneg (δ * L / 8 - S)]
  have hLA : 8 * A / δ ≤ L :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hL)
  have hA : A ≤ δ * L / 8 := by
    have := mul_le_mul_of_nonneg_right hLA hδ0.le
    field_simp at this ⊢
    nlinarith
  have hconstant : (1 / 2 : ℝ) - Real.log C ≤ δ * L / 8 :=
    le_trans (le_abs_self _) hA
  have haS : a * S ≤ δ * L / 8 := by
    calc
      a * S ≤ 1 * S := mul_le_mul_of_nonneg_right ha1 hS0
      _ ≤ δ * L / 8 := by simpa using hS
  have ha_sq : a ^ 2 ≤ 1 - 3 * δ / 4 := by
    dsimp [a]
    nlinarith [sq_nonneg δ]
  have hexponent :
      a ^ 2 * L + a * S + (1 / 2 - Real.log C) ≤ b * L := by
    dsimp [b]
    have := mul_le_mul_of_nonneg_right ha_sq hL0
    nlinarith
  rw [gaussianPDF_standard_toReal_eq]
  have hx : lowerGaussianLevel δ N + 1 = a * S + 1 := by
    rfl
  rw [hx, Real.rpow_def_of_pos hNpos]
  rw [show Real.log (N : ℝ) * (-(1 - δ / 2)) = -b * L by
    dsimp [b, L]
    ring]
  change Real.exp (-b * L) ≤ C * Real.exp (-(a * S + 1) ^ 2 / 2)
  rw [← Real.exp_log hC]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h_expand : (a * S + 1) ^ 2 / 2 = a ^ 2 * L + a * S + 1 / 2 := by
    nlinarith
  rw [show -(a * S + 1) ^ 2 / 2 = -(a ^ 2 * L + a * S + 1 / 2) by
    linarith]
  linarith

lemma eventually_lower_smoothing_gap {δ : ℝ} (hδ0 : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      Real.log ((frequencySet N).card + 1 : ℝ) / lowerBeta N ≤
        δ / 4 * Real.sqrt (2 * Real.log N) := by
  have hlarge := tendsto_nat_log_atTop.eventually_ge_atTop (max 1 (4 / δ))
  filter_upwards [hlarge, eventually_ge_atTop 4] with N hL hN
  let L : ℝ := Real.log (N : ℝ)
  let S : ℝ := Real.sqrt (2 * L)
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hLpos : 0 < L := zero_lt_one.trans_le hL1
  have hLδ : 4 / δ ≤ L := le_trans (le_max_right _ _) hL
  have hcard : (frequencySet N).card + 1 ≤ N := by
    rw [card_frequencySet hN]
    omega
  have hlog : Real.log ((frequencySet N).card + 1 : ℝ) ≤ L := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast hcard
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hSsq : S ^ 2 = 2 * L := by
    dsimp [S]
    rw [Real.sq_sqrt]
    positivity
  have hS1 : 1 ≤ S := by nlinarith
  have hinv : 1 / L ≤ δ / 4 := by
    rw [div_le_iff₀ hLpos]
    calc
      1 = (δ / 4) * (4 / δ) := by field_simp
      _ ≤ (δ / 4) * L :=
        mul_le_mul_of_nonneg_left hLδ (by positivity)
  calc
    Real.log ((frequencySet N).card + 1 : ℝ) / lowerBeta N ≤ L / L ^ 2 := by
      unfold lowerBeta
      exact div_le_div_of_nonneg_right hlog (sq_nonneg L)
    _ = 1 / L := by field_simp
    _ ≤ δ / 4 := hinv
    _ ≤ δ / 4 * S := by
      nth_rewrite 1 [← mul_one (δ / 4)]
      exact mul_le_mul_of_nonneg_left hS1 (by positivity)
    _ = δ / 4 * Real.sqrt (2 * Real.log N) := rfl

lemma lower_smoothed_level_gap {δ : ℝ} {N : ℕ}
    (hgap : Real.log ((frequencySet N).card + 1 : ℝ) / lowerBeta N ≤
      δ / 4 * Real.sqrt (2 * Real.log N)) :
    lowerSignLevel δ N +
        Real.log ((frequencySet N).card + 1 : ℝ) / lowerBeta N ≤
      lowerGaussianLevel δ N - δ / 4 * Real.sqrt (2 * Real.log N) := by
  unfold lowerSignLevel lowerGaussianLevel
  linarith

lemma lower_exponential_prefactor_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {N : ℕ}
    (hN : 1 ≤ N)
    (hB : lowerSignLevel δ N +
        Real.log ((frequencySet N).card + 1 : ℝ) / lowerBeta N ≤
      lowerGaussianLevel δ N) :
    Real.exp (lowerGamma N *
      (lowerSignLevel δ N +
        Real.log ((frequencySet N).card + 1 : ℝ) / lowerBeta N)) ≤
      (N : ℝ) ^ (1 / 50 : ℝ) := by
  let L : ℝ := Real.log (N : ℝ)
  let R : ℝ := Real.sqrt L
  let S : ℝ := Real.sqrt (2 * L)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hN)
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hRsq : R ^ 2 = L := Real.sq_sqrt hL0
  have hSsq : S ^ 2 = 2 * L := by
    dsimp [S]
    rw [Real.sq_sqrt]
    positivity
  have hRS : R * S ≤ 2 * L := by
    nlinarith [sq_nonneg (2 * L - R * S), sq_nonneg (R * S)]
  have ht : lowerGaussianLevel δ N ≤ S := by
    unfold lowerGaussianLevel
    have : 1 - δ / 2 ≤ 1 := by linarith
    simpa only [S, L, one_mul] using mul_le_mul_of_nonneg_right this hS0
  apply (Real.exp_le_exp.mpr ?_).trans_eq (Real.rpow_def_of_pos hNpos _).symm
  calc
    lowerGamma N *
        (lowerSignLevel δ N +
          Real.log ((frequencySet N).card + 1 : ℝ) / lowerBeta N) ≤
        lowerGamma N * lowerGaussianLevel δ N :=
      mul_le_mul_of_nonneg_left hB (lowerGamma_nonneg N)
    _ ≤ (R / 100) * S := by
      unfold lowerGamma
      exact mul_le_mul_of_nonneg_left ht (by positivity)
    _ ≤ L / 50 := by linarith
    _ = Real.log (N : ℝ) * (1 / 50 : ℝ) := by dsimp [L]; ring

lemma lower_cutoff_term_le {δ : ℝ} (hδ0 : 0 ≤ δ) {N : ℕ} (hN : 1 ≤ N)
    (hgap : Real.log ((frequencySet N).card + 1 : ℝ) / lowerBeta N ≤
      δ / 4 * Real.sqrt (2 * Real.log N)) :
    Real.exp (lowerGamma N *
        (lowerSignLevel δ N +
          Real.log ((frequencySet N).card + 1 : ℝ) / lowerBeta N)) *
      Real.exp (-lowerGamma N * lowerGaussianLevel δ N) ≤
        (N : ℝ) ^ (-(δ / 400) : ℝ) := by
  let L : ℝ := Real.log (N : ℝ)
  let R : ℝ := Real.sqrt L
  let S : ℝ := Real.sqrt (2 * L)
  let B : ℝ := lowerSignLevel δ N +
    Real.log ((frequencySet N).card + 1 : ℝ) / lowerBeta N
  let t : ℝ := lowerGaussianLevel δ N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hN)
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hRsq : R ^ 2 = L := Real.sq_sqrt hL0
  have hSsq : S ^ 2 = 2 * L := by
    dsimp [S]
    rw [Real.sq_sqrt]
    positivity
  have hRSsq : (R * S) ^ 2 = 2 * L ^ 2 := by
    rw [mul_pow, hRsq, hSsq]
    ring
  have hRleS : R ≤ S := by nlinarith [sq_nonneg (S - R)]
  have hRS : L ≤ R * S := by
    calc
      L = R * R := by nlinarith
      _ ≤ R * S := mul_le_mul_of_nonneg_left hRleS hR0
  have hBt : B ≤ t - δ / 4 * S := lower_smoothed_level_gap hgap
  rw [← Real.exp_add]
  apply (Real.exp_le_exp.mpr ?_).trans_eq (Real.rpow_def_of_pos hNpos _).symm
  calc
    lowerGamma N * B + -lowerGamma N * t = -lowerGamma N * (t - B) := by ring
    _ ≤ -lowerGamma N * (δ / 4 * S) := by
      apply mul_le_mul_of_nonpos_left
      · linarith
      · exact neg_nonpos.mpr (lowerGamma_nonneg N)
    _ = -(δ / 400) * (R * S) := by
      unfold lowerGamma
      dsimp [R, L]
      ring
    _ ≤ -(δ / 400) * L :=
      mul_le_mul_of_nonpos_left hRS
        (neg_nonpos.mpr (div_nonneg hδ0 (by norm_num)))
    _ = Real.log (N : ℝ) * (-(δ / 400) : ℝ) := by ring

lemma standardGaussianAbsCube_nonneg : 0 ≤ standardGaussianAbsCube := by
  unfold standardGaussianAbsCube
  exact integral_nonneg fun _ ↦ by positivity

lemma eventually_lower_lindeberg_term_le :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (1 / 50 : ℝ) *
          ((N : ℝ) * hybridCubicError N (lowerBeta N) (lowerGamma N) *
            (1 + standardGaussianAbsCube)) ≤
        (N : ℝ) ^ (-(1 / 4) : ℝ) := by
  let C : ℝ := 1 + standardGaussianAbsCube
  let D : ℝ := 52 * C
  have hC : 0 < C := by
    dsimp [C]
    linarith [standardGaussianAbsCube_nonneg]
  have hD : 0 < D := by dsimp [D]; positivity
  have hpolyReal :=
    (isLittleO_log_rpow_rpow_atTop (6 : ℝ) (by norm_num : (0 : ℝ) < 1 / 5)).bound
      (one_div_pos.mpr hD)
  have hpolyNat := tendsto_natCast_atTop_atTop.eventually hpolyReal
  have hlarge := tendsto_nat_log_atTop.eventually_ge_atTop 1
  filter_upwards [hpolyNat, hlarge, eventually_ge_atTop 1] with N hpoly hL hN
  let x : ℝ := (N : ℝ)
  let L : ℝ := Real.log x
  let R : ℝ := Real.sqrt L
  let T : ℝ := Real.sqrt x
  let q : ℝ := Real.sqrt (2 / x)
  let β : ℝ := lowerBeta N
  let γ : ℝ := lowerGamma N
  have hx : 1 ≤ x := by dsimp [x]; exact_mod_cast hN
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hL1 : 1 ≤ L := hL
  have hL0 : 0 ≤ L := zero_le_one.trans hL1
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hRsq : R ^ 2 = L := Real.sq_sqrt hL0
  have hT0 : 0 ≤ T := Real.sqrt_nonneg _
  have hTpos : 0 < T := Real.sqrt_pos.2 hx0
  have hTsq : T ^ 2 = x := Real.sq_sqrt hx0.le
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqSq : q ^ 2 = 2 / x := by
    dsimp [q]
    rw [Real.sq_sqrt]
    positivity
  have hRleL : R ≤ L := by nlinarith [sq_nonneg (L - R)]
  have hLleLsq : L ≤ L ^ 2 := by nlinarith
  have hγ0 : 0 ≤ γ := lowerGamma_nonneg N
  have hβ0 : 0 ≤ β := by dsimp [β, lowerBeta]; positivity
  have hγβ : γ ≤ β := by
    dsimp [γ, β, lowerGamma, lowerBeta]
    calc
      R / 100 ≤ R := by nlinarith
      _ ≤ L := hRleL
      _ ≤ L ^ 2 := hLleLsq
  have hγ3 : γ ^ 3 ≤ β ^ 3 := by gcongr
  have hγ2β : γ ^ 2 * β ≤ β ^ 3 := by
    have : γ ^ 2 ≤ β ^ 2 := by gcongr
    calc
      γ ^ 2 * β ≤ β ^ 2 * β := mul_le_mul_of_nonneg_right this hβ0
      _ = β ^ 3 := by ring
  have hγβ2 : γ * β ^ 2 ≤ β ^ 3 := by
    calc
      γ * β ^ 2 ≤ β * β ^ 2 := mul_le_mul_of_nonneg_right hγβ (sq_nonneg β)
      _ = β ^ 3 := by ring
  have hcubicCoeff : γ ^ 3 + 6 * γ ^ 2 * β + 6 * γ * β ^ 2 ≤ 13 * β ^ 3 := by
    linarith
  have hq_eq : q = Real.sqrt 2 / T := by
    dsimp [q, T]
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hqT : q ≤ 2 / T := by
    rw [hq_eq]
    exact div_le_div_of_nonneg_right hsqrt2 hT0
  have hNq : x * q ^ 3 ≤ 4 / T := by
    have heq : x * q ^ 3 = 2 * q := by
      calc
        x * q ^ 3 = (x * q ^ 2) * q := by ring
        _ = 2 * q := by rw [hqSq]; field_simp
    rw [heq]
    calc
      2 * q ≤ 2 * (2 / T) := mul_le_mul_of_nonneg_left hqT (by norm_num)
      _ = 4 / T := by ring
  have hpoly' : L ^ 6 ≤ (1 / D) * x ^ (1 / 5 : ℝ) := by
    have hp := hpoly
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx) _),
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _)] at hp
    have hpR : L ^ (6 : ℝ) ≤ (1 / D) * x ^ (1 / 5 : ℝ) := by
      simpa only [L, x] using hp
    exact (Real.rpow_natCast L 6).symm.trans_le hpR
  have hDpoly : D * L ^ 6 ≤ x ^ (1 / 5 : ℝ) := by
    calc
      D * L ^ 6 ≤ D * ((1 / D) * x ^ (1 / 5 : ℝ)) :=
        mul_le_mul_of_nonneg_left hpoly' hD.le
      _ = x ^ (1 / 5 : ℝ) := by field_simp
  have herror :
      x * hybridCubicError N (lowerBeta N) (lowerGamma N) * C ≤
        D * L ^ 6 / T := by
    have hq3 : Real.sqrt (2 / (N : ℝ)) ^ 3 = q ^ 3 := rfl
    unfold hybridCubicError
    change x * ((γ ^ 3 + 6 * γ ^ 2 * β + 6 * γ * β ^ 2) * q ^ 3 / 6) * C ≤
      D * L ^ 6 / T
    have hcoeff0 : 0 ≤ γ ^ 3 + 6 * γ ^ 2 * β + 6 * γ * β ^ 2 := by positivity
    calc
      x * ((γ ^ 3 + 6 * γ ^ 2 * β + 6 * γ * β ^ 2) * q ^ 3 / 6) * C ≤
          x * ((13 * β ^ 3) * q ^ 3) * C := by
        have hmul := mul_le_mul_of_nonneg_right hcubicCoeff (pow_nonneg hq0 3)
        have hleft0 : 0 ≤
            (γ ^ 3 + 6 * γ ^ 2 * β + 6 * γ * β ^ 2) * q ^ 3 :=
          mul_nonneg hcoeff0 (pow_nonneg hq0 3)
        have hinner :
            (γ ^ 3 + 6 * γ ^ 2 * β + 6 * γ * β ^ 2) * q ^ 3 / 6 ≤
              (13 * β ^ 3) * q ^ 3 := by
          nlinarith
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hinner hC.le) hx0.le
      _ = 13 * C * β ^ 3 * (x * q ^ 3) := by ring
      _ ≤ 13 * C * β ^ 3 * (4 / T) := by
        gcongr
      _ = D * L ^ 6 / T := by
        dsimp [D, β, lowerBeta]
        ring
  have hT_rpow : T = x ^ (1 / 2 : ℝ) := by
    dsimp [T]
    rw [Real.sqrt_eq_rpow]
  have hcombine :
      x ^ (1 / 50 : ℝ) * (x ^ (1 / 5 : ℝ) / T) =
        x ^ (-(7 / 25) : ℝ) := by
    rw [hT_rpow, ← Real.rpow_sub hx0, ← Real.rpow_add hx0]
    congr 1
    norm_num
  calc
    (N : ℝ) ^ (1 / 50 : ℝ) *
        ((N : ℝ) * hybridCubicError N (lowerBeta N) (lowerGamma N) *
          (1 + standardGaussianAbsCube)) =
        x ^ (1 / 50 : ℝ) *
          (x * hybridCubicError N (lowerBeta N) (lowerGamma N) * C) := rfl
    _ ≤ x ^ (1 / 50 : ℝ) * (D * L ^ 6 / T) :=
      mul_le_mul_of_nonneg_left herror (Real.rpow_nonneg hx0.le _)
    _ ≤ x ^ (1 / 50 : ℝ) * (x ^ (1 / 5 : ℝ) / T) := by
      apply mul_le_mul_of_nonneg_left
      · exact div_le_div_of_nonneg_right hDpoly hT0
      · exact Real.rpow_nonneg hx0.le _
    _ = x ^ (-(7 / 25) : ℝ) := hcombine
    _ ≤ x ^ (-(1 / 4) : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hx
      norm_num
    _ = (N : ℝ) ^ (-(1 / 4) : ℝ) := rfl

lemma eventually_lower_gaussian_term_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (1 / 50 : ℝ) *
          coupledMeasure.real (gaussianAllBelow N (lowerGaussianLevel δ N)) ≤
        (N : ℝ) ^ (-(δ / 400) : ℝ) := by
  let K : ℝ := 1 / 50 + δ / 400
  have hK : 0 < K := by dsimp [K]; positivity
  have hlittleReal :=
    (isLittleO_log_rpow_atTop (by positivity : (0 : ℝ) < δ / 2)).bound
      (by positivity : (0 : ℝ) < 1 / (8 * K))
  have hlittleNat := tendsto_natCast_atTop_atTop.eventually hlittleReal
  filter_upwards [eventually_standardGaussianDensity_lower hδ0 hδ1,
    hlittleNat, eventually_ge_atTop 4] with N hdensity hlog hN
  let x : ℝ := (N : ℝ)
  let L : ℝ := Real.log x
  let q : ℝ := (gaussianPDF 0 1 (lowerGaussianLevel δ N + 1)).toReal
  let b : ℝ := 1 - δ / 2
  have hx : 1 ≤ x := by dsimp [x]; exact_mod_cast (le_trans (by omega : 1 ≤ 4) hN)
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hL0 : 0 ≤ L := Real.log_nonneg hx
  have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
  have hq : x ^ (-b) ≤ q := by simpa only [x, b] using hdensity
  have hcard : x / 8 ≤ ((frequencySet N).card : ℝ) := by
    simpa only [x] using quarter_le_card_frequencySet hN
  have hprod : x ^ (δ / 2) / 8 ≤ ((frequencySet N).card : ℝ) * q := by
    have hp : x * x ^ (-b) = x ^ (δ / 2) := by
      calc
        x * x ^ (-b) = x ^ (1 : ℝ) * x ^ (-b) := by rw [Real.rpow_one]
        _ = x ^ ((1 : ℝ) + (-b)) := (Real.rpow_add hx0 _ _).symm
        _ = x ^ (δ / 2) := by
          congr 1
          dsimp [b]
          ring
    calc
      x ^ (δ / 2) / 8 = (x / 8) * x ^ (-b) := by rw [← hp]; ring
      _ ≤ ((frequencySet N).card : ℝ) * q :=
        mul_le_mul hcard hq (Real.rpow_nonneg hx0.le _) (by positivity)
  have hlog' : L ≤ (1 / (8 * K)) * x ^ (δ / 2) := by
    have hl := hlog
    rw [Real.norm_eq_abs, abs_of_nonneg hL0, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hx0.le _)] at hl
    simpa only [L, x] using hl
  have hKL : K * L ≤ x ^ (δ / 2) / 8 := by
    calc
      K * L ≤ K * ((1 / (8 * K)) * x ^ (δ / 2)) :=
        mul_le_mul_of_nonneg_left hlog' hK.le
      _ = x ^ (δ / 2) / 8 := by field_simp
  have hall := measureReal_gaussianAllBelow_le_exp hN
    (lowerGaussianLevel_nonneg hδ0.le hδ1 (by omega : 1 ≤ N))
  have hall' : coupledMeasure.real (gaussianAllBelow N (lowerGaussianLevel δ N)) ≤
      Real.exp (-((frequencySet N).card : ℝ) * q) := by
    simpa only [q] using hall
  calc
    x ^ (1 / 50 : ℝ) *
        coupledMeasure.real (gaussianAllBelow N (lowerGaussianLevel δ N)) ≤
        x ^ (1 / 50 : ℝ) *
          Real.exp (-((frequencySet N).card : ℝ) * q) :=
      mul_le_mul_of_nonneg_left hall' (Real.rpow_nonneg hx0.le _)
    _ = Real.exp ((1 / 50 : ℝ) * L - ((frequencySet N).card : ℝ) * q) := by
      rw [Real.rpow_def_of_pos hx0, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(δ / 400) * L) := by
      apply Real.exp_le_exp.mpr
      have := hKL.trans hprod
      dsimp [K] at this
      linarith
    _ = x ^ (-(δ / 400) : ℝ) := by
      rw [Real.rpow_def_of_pos hx0]
      congr 1
      ring
    _ = (N : ℝ) ^ (-(δ / 400) : ℝ) := rfl

theorem eventually_measureReal_signAllAtMost_lowerSignLevel_le {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ᶠ N : ℕ in atTop,
      signMeasure.real (signAllAtMost N (lowerSignLevel δ N)) ≤
        3 * (N : ℝ) ^ (-(δ / 400) : ℝ) := by
  filter_upwards [eventually_lower_smoothing_gap hδ0,
    eventually_lower_gaussian_term_le hδ0 hδ1,
    eventually_lower_lindeberg_term_le, eventually_ge_atTop 4] with
      N hgap hgaussian hreplacement hN
  let x : ℝ := (N : ℝ)
  let B : ℝ := lowerSignLevel δ N +
    Real.log ((frequencySet N).card + 1 : ℝ) / lowerBeta N
  let A : ℝ := Real.exp (lowerGamma N * B)
  let e : ℝ := Real.exp (-lowerGamma N * lowerGaussianLevel δ N)
  let g : ℝ := coupledMeasure.real (gaussianAllBelow N (lowerGaussianLevel δ N))
  let r : ℝ := (N : ℝ) * hybridCubicError N (lowerBeta N) (lowerGamma N) *
    (1 + standardGaussianAbsCube)
  let p : ℝ := x ^ (-(δ / 400) : ℝ)
  have hx : 1 ≤ x := by dsimp [x]; exact_mod_cast (le_trans (by omega : 1 ≤ 4) hN)
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hB : B ≤ lowerGaussianLevel δ N := by
    exact (lower_smoothed_level_gap hgap).trans (sub_le_self _ (by positivity))
  have hpref : A ≤ x ^ (1 / 50 : ℝ) := by
    simpa only [A, B, x] using lower_exponential_prefactor_le hδ0.le hδ1
      (le_trans (by omega : 1 ≤ 4) hN) hB
  have hcut : A * e ≤ p := by
    simpa only [A, B, e, p, x] using
      lower_cutoff_term_le hδ0.le (le_trans (by omega : 1 ≤ 4) hN) hgap
  have hg0 : 0 ≤ g := by dsimp [g]; exact measureReal_nonneg
  have hr0 : 0 ≤ r := by
    dsimp [r]
    have hβ := lowerBeta_pos (le_trans (by omega : 2 ≤ 4) hN)
    have hγ := lowerGamma_nonneg N
    have herr : 0 ≤ hybridCubicError N (lowerBeta N) (lowerGamma N) := by
      unfold hybridCubicError
      positivity
    exact mul_nonneg
      (mul_nonneg (by positivity : (0 : ℝ) ≤ N) herr)
      (by linarith [standardGaussianAbsCube_nonneg])
  have hgaussian' : A * g ≤ p := by
    calc
      A * g ≤ x ^ (1 / 50 : ℝ) * g := mul_le_mul_of_nonneg_right hpref hg0
      _ ≤ p := by simpa only [g, p, x] using hgaussian
  have hreplacement' : A * r ≤ p := by
    calc
      A * r ≤ x ^ (1 / 50 : ℝ) * r := mul_le_mul_of_nonneg_right hpref hr0
      _ ≤ x ^ (-(1 / 4) : ℝ) := by simpa only [r, x] using hreplacement
      _ ≤ p := by
        dsimp [p]
        apply Real.rpow_le_rpow_of_exponent_le hx
        have : δ / 400 ≤ 1 / 4 := by nlinarith
        linarith
  have hraw := measureReal_signAllAtMost_le hN
    (lowerBeta_pos (le_trans (by omega : 2 ≤ 4) hN))
    (lowerGamma_nonneg N)
    (lowerSignLevel_nonneg hδ0.le hδ1 (le_trans (by omega : 1 ≤ 4) hN))
    (t := lowerGaussianLevel δ N)
  change signMeasure.real (signAllAtMost N (lowerSignLevel δ N)) ≤
      A * (e + g + r) at hraw
  calc
    signMeasure.real (signAllAtMost N (lowerSignLevel δ N)) ≤ A * (e + g + r) := hraw
    _ = A * e + A * g + A * r := by ring
    _ ≤ 3 * p := by linarith
    _ = 3 * (N : ℝ) ^ (-(δ / 400) : ℝ) := rfl

def lowerMaximumLevel (δ : ℝ) (N : ℕ) : ℝ :=
  (1 - δ) * Real.sqrt ((N : ℝ) * Real.log N)

lemma normalizedRootRealProjection_le_maximumModulus {N : ℕ} (hN : 1 ≤ N)
    (ω : Sample) (r : ℕ) :
    normalizedRootRealProjection ω N r ≤
      Real.sqrt (2 / (N : ℝ)) * maximumModulus ω (N - 1) := by
  have hs : N - 1 + 1 = N := Nat.sub_add_cancel hN
  have hdft : ‖dftValue ω N r‖ ≤ maximumModulus ω (N - 1) := by
    simpa only [hs] using norm_dftValue_le_maximumModulus ω (N - 1) r
  unfold normalizedRootRealProjection
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  rw [rootRealProjection_eq_re]
  exact (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans hdft)

lemma sqrt_normalization_mul_lowerMaximumLevel {δ : ℝ} {N : ℕ} (hN : 1 ≤ N) :
    Real.sqrt (2 / (N : ℝ)) * lowerMaximumLevel δ N = lowerSignLevel δ N := by
  let x : ℝ := (N : ℝ)
  let L : ℝ := Real.log x
  let q : ℝ := Real.sqrt (2 / x)
  let v : ℝ := Real.sqrt (x * L)
  let S : ℝ := Real.sqrt (2 * L)
  have hx : 1 ≤ x := by dsimp [x]; exact_mod_cast hN
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hL0 : 0 ≤ L := Real.log_nonneg hx
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hqSq : q ^ 2 = 2 / x := by
    dsimp [q]
    rw [Real.sq_sqrt]
    positivity
  have hvSq : v ^ 2 = x * L := by
    dsimp [v]
    rw [Real.sq_sqrt]
    positivity
  have hSSq : S ^ 2 = 2 * L := by
    dsimp [S]
    rw [Real.sq_sqrt]
    positivity
  have hqv : q * v = S := by
    have hsq : (q * v) ^ 2 = S ^ 2 := by
      rw [mul_pow, hqSq, hvSq]
      field_simp
      exact hSSq.symm
    have hqv0 : 0 ≤ q * v := mul_nonneg hq0 hv0
    nlinarith [sq_nonneg (q * v - S)]
  unfold lowerMaximumLevel lowerSignLevel
  change q * ((1 - δ) * v) = (1 - δ) * S
  rw [← hqv]
  ring

def lowerMaximumFailure (δ : ℝ) (N : ℕ) : Set Sample :=
  {ω | maximumModulus ω (N - 1) ≤ lowerMaximumLevel δ N}

lemma measurableSet_lowerMaximumFailure (δ : ℝ) (N : ℕ) :
    MeasurableSet (lowerMaximumFailure δ N) := by
  exact measurableSet_le (measurable_maximumModulus (N - 1)) measurable_const

lemma lowerMaximumFailure_subset_signAllAtMost {δ : ℝ} {N : ℕ}
    (hδ : δ ≤ 1) (hN : 1 ≤ N) :
    lowerMaximumFailure δ N ⊆ signAllAtMost N (lowerSignLevel δ N) := by
  intro ω hω
  simp only [signAllAtMost, Set.mem_iInter, Set.mem_setOf_eq]
  intro r
  calc
    normalizedRootRealProjection ω N r.1 ≤
        Real.sqrt (2 / (N : ℝ)) * maximumModulus ω (N - 1) :=
      normalizedRootRealProjection_le_maximumModulus hN ω r.1
    _ ≤ Real.sqrt (2 / (N : ℝ)) * lowerMaximumLevel δ N :=
      mul_le_mul_of_nonneg_left hω (Real.sqrt_nonneg _)
    _ = lowerSignLevel δ N := sqrt_normalization_mul_lowerMaximumLevel hN

theorem eventually_measureReal_lowerMaximumFailure_le {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ᶠ N : ℕ in atTop,
      signMeasure.real (lowerMaximumFailure δ N) ≤
        3 * (N : ℝ) ^ (-(δ / 400) : ℝ) := by
  filter_upwards [eventually_measureReal_signAllAtMost_lowerSignLevel_le hδ0 hδ1,
    eventually_ge_atTop 1] with N hbound hN
  exact (measureReal_mono (μ := signMeasure)
    (lowerMaximumFailure_subset_signAllAtMost hδ1 hN)).trans hbound

/-! ## Deterministic circle discretization -/

lemma differentiable_randomPolynomial (ω : Sample) (n : ℕ) :
    Differentiable ℂ (randomPolynomial ω n) := by
  unfold randomPolynomial
  fun_prop

lemma norm_randomPolynomial_le_maximumModulus_of_norm_le_one
    (ω : Sample) (n : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖randomPolynomial ω n z‖ ≤ maximumModulus ω n := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (Metric.isBounded_ball : Bornology.IsBounded (ball (0 : ℂ) 1))
    ((differentiable_randomPolynomial ω n).diffContOnCl)
  · intro w hw
    rw [frontier_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] at hw
    have hwnorm : ‖w‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hw
    let wc : Circle := ⟨w, by simpa [Submonoid.unitSphere] using hwnorm⟩
    simpa only [wc] using norm_randomPolynomial_le_maximumModulus ω n wc
  · rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0),
      Metric.mem_closedBall, dist_zero_right]
    exact hz

def reverseRandomPolynomial (ω : Sample) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), (ω k : ℂ) * z ^ (n - k)

lemma differentiable_reverseRandomPolynomial (ω : Sample) (n : ℕ) :
    Differentiable ℂ (reverseRandomPolynomial ω n) := by
  unfold reverseRandomPolynomial
  fun_prop

lemma reverseRandomPolynomial_eq (ω : Sample) (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    reverseRandomPolynomial ω n z = z ^ n * randomPolynomial ω n z⁻¹ := by
  unfold reverseRandomPolynomial randomPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hk
  calc
    (ω k : ℂ) * z ^ (n - k) = (ω k : ℂ) * (z ^ n * (z⁻¹) ^ k) := by
      congr 1
      rw [pow_sub₀ z hz hkn, inv_pow]
    _ = z ^ n * ((ω k : ℂ) * (z⁻¹) ^ k) := by ring

lemma norm_reverseRandomPolynomial_le_maximumModulus_of_norm_le_one
    (ω : Sample) (n : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖reverseRandomPolynomial ω n z‖ ≤ maximumModulus ω n := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (Metric.isBounded_ball : Bornology.IsBounded (ball (0 : ℂ) 1))
    ((differentiable_reverseRandomPolynomial ω n).diffContOnCl)
  · intro w hw
    rw [frontier_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] at hw
    have hwnorm : ‖w‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hw
    have hw0 : w ≠ 0 := by
      intro h
      rw [h, norm_zero] at hwnorm
      norm_num at hwnorm
    rw [reverseRandomPolynomial_eq ω n hw0, norm_mul, norm_pow, hwnorm, one_pow, one_mul]
    have hinvnorm : ‖w⁻¹‖ = 1 := by rw [norm_inv, hwnorm, inv_one]
    let wc : Circle := ⟨w⁻¹, by simpa [Submonoid.unitSphere] using hinvnorm⟩
    simpa only [wc] using norm_randomPolynomial_le_maximumModulus ω n wc
  · rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0),
      Metric.mem_closedBall, dist_zero_right]
    exact hz

lemma norm_randomPolynomial_le_norm_pow_mul_maximumModulus
    (ω : Sample) (n : ℕ) {z : ℂ} (hz : 1 ≤ ‖z‖) :
    ‖randomPolynomial ω n z‖ ≤ ‖z‖ ^ n * maximumModulus ω n := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    norm_num at hz
  have hinvnorm : ‖z⁻¹‖ ≤ 1 := by
    rw [norm_inv, inv_le_one₀ (by positivity)]
    exact hz
  have hrev := norm_reverseRandomPolynomial_le_maximumModulus_of_norm_le_one
    ω n (z := z⁻¹) hinvnorm
  rw [reverseRandomPolynomial_eq ω n (inv_ne_zero hz0), inv_inv, norm_mul, norm_pow,
    norm_inv, inv_pow] at hrev
  have hzpow : 0 < ‖z‖ ^ n := pow_pos (norm_pos_iff.mpr hz0) _
  calc
    ‖randomPolynomial ω n z‖ = ‖z‖ ^ n *
        ((‖z‖ ^ n)⁻¹ * ‖randomPolynomial ω n z‖) := by field_simp
    _ ≤ ‖z‖ ^ n * maximumModulus ω n :=
      mul_le_mul_of_nonneg_left hrev hzpow.le

lemma norm_randomPolynomial_le_radius_pow_mul_maximumModulus
    (ω : Sample) (n : ℕ) {ρ : ℝ} (hρ : 1 ≤ ρ) {z : ℂ} (hz : ‖z‖ ≤ ρ) :
    ‖randomPolynomial ω n z‖ ≤ ρ ^ n * maximumModulus ω n := by
  by_cases hzin : ‖z‖ ≤ 1
  · calc
      ‖randomPolynomial ω n z‖ ≤ maximumModulus ω n :=
        norm_randomPolynomial_le_maximumModulus_of_norm_le_one ω n hzin
      _ ≤ ρ ^ n * maximumModulus ω n := by
        nth_rewrite 1 [← one_mul (maximumModulus ω n)]
        exact mul_le_mul_of_nonneg_right (one_le_pow₀ hρ) (maximumModulus_nonneg ω n)
  · have hzout : 1 ≤ ‖z‖ := le_of_not_ge hzin
    calc
      ‖randomPolynomial ω n z‖ ≤ ‖z‖ ^ n * maximumModulus ω n :=
        norm_randomPolynomial_le_norm_pow_mul_maximumModulus ω n hzout
      _ ≤ ρ ^ n * maximumModulus ω n :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hz n)
          (maximumModulus_nonneg ω n)

lemma one_add_inv_nat_pow_le_three (N : ℕ) :
    (1 + ((N : ℝ)⁻¹)) ^ N ≤ 3 := by
  exact Real.one_add_inv_pow_le_exp.trans Real.exp_one_lt_three.le

lemma norm_deriv_randomPolynomial_circle_le (ω : Sample) (n : ℕ) (z : Circle) :
    ‖deriv (randomPolynomial ω n) (z : ℂ)‖ ≤
      3 * (n + 1 : ℝ) * maximumModulus ω n := by
  let N : ℕ := n + 1
  let R : ℝ := 1 / (N : ℝ)
  let ρ : ℝ := 1 + R
  have hN : 0 < N := by dsimp [N]; omega
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hR : 0 < R := by dsimp [R]; positivity
  have hρ : 1 ≤ ρ := by dsimp [ρ]; linarith
  have hpow : ρ ^ n ≤ 3 := by
    have hnN : n ≤ N := by dsimp [N]; omega
    calc
      ρ ^ n ≤ ρ ^ N := pow_le_pow_right₀ hρ hnN
      _ = (1 + ((N : ℝ)⁻¹)) ^ N := by
        congr 1
        dsimp [ρ, R]
        rw [one_div]
      _ ≤ 3 := one_add_inv_nat_pow_le_three N
  have hsphere : ∀ w ∈ sphere (z : ℂ) R,
      ‖randomPolynomial ω n w‖ ≤ 3 * maximumModulus ω n := by
    intro w hw
    have hdist : ‖w - (z : ℂ)‖ = R := by
      simpa only [mem_sphere, Complex.dist_eq] using hw
    have hwnorm : ‖w‖ ≤ ρ := by
      calc
        ‖w‖ = ‖(z : ℂ) + (w - (z : ℂ))‖ := by ring_nf
        _ ≤ ‖(z : ℂ)‖ + ‖w - (z : ℂ)‖ := norm_add_le _ _
        _ = ρ := by rw [Circle.norm_coe, hdist]
    calc
      ‖randomPolynomial ω n w‖ ≤ ρ ^ n * maximumModulus ω n :=
        norm_randomPolynomial_le_radius_pow_mul_maximumModulus ω n hρ hwnorm
      _ ≤ 3 * maximumModulus ω n :=
        mul_le_mul_of_nonneg_right hpow (maximumModulus_nonneg ω n)
  have hCauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (f := randomPolynomial ω n) hR
    ((differentiable_randomPolynomial ω n).diffContOnCl)
    (C := 3 * maximumModulus ω n) hsphere
  calc
    ‖deriv (randomPolynomial ω n) (z : ℂ)‖ ≤
        (3 * maximumModulus ω n) / R := hCauchy
    _ = 3 * (n + 1 : ℝ) * maximumModulus ω n := by
      dsimp [R, N]
      field_simp
      push_cast
      ring

def angularPolynomial (ω : Sample) (n : ℕ) (θ : ℝ) : ℂ :=
  randomPolynomial ω n (circleMap 0 1 θ)

def randomPolynomialDerivative (ω : Sample) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    (ω k : ℂ) * ((k : ℂ) * z ^ (k - 1))

lemma hasDerivAt_randomPolynomial (ω : Sample) (n : ℕ) (z : ℂ) :
    HasDerivAt (randomPolynomial ω n) (randomPolynomialDerivative ω n z) z := by
  unfold randomPolynomial randomPolynomialDerivative
  apply HasDerivAt.fun_sum
  intro k _hk
  have hk := ((hasDerivAt_id z).pow k).const_smul (ω k : ℂ)
  have hk' : HasDerivAt ((ω k : ℂ) • (id : ℂ → ℂ) ^ k)
      ((ω k : ℂ) * ((k : ℂ) * z ^ (k - 1))) z :=
    hk.congr_deriv (by simp [smul_eq_mul])
  apply hk'.congr_of_eventuallyEq
  filter_upwards with y
  simp [Pi.smul_apply, smul_eq_mul, id_eq]

lemma deriv_randomPolynomial (ω : Sample) (n : ℕ) (z : ℂ) :
    deriv (randomPolynomial ω n) z = randomPolynomialDerivative ω n z :=
  (hasDerivAt_randomPolynomial ω n z).deriv

lemma hasDerivAt_angularPolynomial (ω : Sample) (n : ℕ) (θ : ℝ) :
    HasDerivAt (angularPolynomial ω n)
      (randomPolynomialDerivative ω n (circleMap 0 1 θ) *
        (circleMap 0 1 θ * Complex.I)) θ := by
  unfold angularPolynomial randomPolynomial randomPolynomialDerivative
  rw [Finset.sum_mul]
  apply HasDerivAt.fun_sum
  intro k _hk
  have hk := (hasDerivAt_circleMap (0 : ℂ) 1 θ).pow k
  have hs := hk.const_smul (ω k : ℂ)
  have hs' : HasDerivAt ((ω k : ℂ) • (circleMap 0 1) ^ k)
      ((ω k : ℂ) * ((k : ℂ) * circleMap 0 1 θ ^ (k - 1)) *
        (circleMap 0 1 θ * Complex.I)) θ :=
    hs.congr_deriv (by simp [smul_eq_mul]; ring)
  apply hs'.congr_of_eventuallyEq
  filter_upwards with y
  simp [Pi.smul_apply, smul_eq_mul]

lemma norm_deriv_angularPolynomial_le (ω : Sample) (n : ℕ) (θ : ℝ) :
    ‖deriv (angularPolynomial ω n) θ‖ ≤
      3 * (n + 1 : ℝ) * maximumModulus ω n := by
  let z : Circle := Circle.exp θ
  have hz : (z : ℂ) = circleMap 0 1 θ := by
    dsimp [z]
    simp [circleMap]
  have h := norm_deriv_randomPolynomial_circle_le ω n z
  rw [(hasDerivAt_angularPolynomial ω n θ).deriv, ← deriv_randomPolynomial,
    norm_mul, norm_mul, Complex.norm_I, mul_one,
    show ‖circleMap 0 1 θ‖ = 1 by simp, mul_one]
  simpa only [hz] using h

lemma norm_angularPolynomial_sub_le (ω : Sample) (n : ℕ) (θ φ : ℝ) :
    ‖angularPolynomial ω n θ - angularPolynomial ω n φ‖ ≤
      (3 * (n + 1 : ℝ) * maximumModulus ω n) * |θ - φ| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.univ) (f := angularPolynomial ω n)
    (x := φ) (y := θ)
    (fun x _hx ↦ (hasDerivAt_angularPolynomial ω n x).differentiableAt)
    (fun x _hx ↦ norm_deriv_angularPolynomial_le ω n x)
    convex_univ (Set.mem_univ _) (Set.mem_univ _)
  simpa only [Real.norm_eq_abs] using h

/-! ## A sharp finite upper-tail mesh bound -/

/-- The geometric sum which measures the anisotropy of a Fourier value at the `j`-th
`M`-th root of unity. -/
def rootGeometricSum (M N j : ℕ) : ℂ :=
  ∑ k ∈ Finset.range N, standardRoot M ^ (2 * j * k)

lemma sum_root_pair (M N k l : ℕ) (hM : M ≠ 0) (hsize : 2 * N ≤ M)
    (hk : k < N) (hl : l < N) :
    ∑ j ∈ Finset.range M,
        conj (standardRoot M ^ (2 * j * k)) * standardRoot M ^ (2 * j * l) =
      if k = l then (M : ℂ) else 0 := by
  let ζ : ℂ := standardRoot M
  have hζ : IsPrimitiveRoot ζ M := standardRoot_isPrimitive hM
  by_cases hkl : k = l
  · subst l
    rw [if_pos rfl]
    simp only [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
      norm_standardRoot_pow, one_pow, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
    norm_num
  · rw [if_neg hkl]
    let q : ℂ := conj (ζ ^ (2 * k)) * ζ ^ (2 * l)
    have hζnorm : ‖ζ‖ = 1 := by
      dsimp [ζ]
      simpa using norm_standardRoot_pow M 1
    have hkexp : 2 * k < M := by omega
    have hlexp : 2 * l < M := by omega
    have hqne : q ≠ 1 := by
      intro hq
      have hconj : conj (ζ ^ (2 * k)) = (ζ ^ (2 * k))⁻¹ := by
        rw [← Complex.inv_eq_conj]
        simp [hζnorm]
      dsimp [q] at hq
      rw [hconj] at hq
      have hpows : ζ ^ (2 * k) = ζ ^ (2 * l) :=
        (inv_mul_eq_one₀ (pow_ne_zero _ (norm_pos_iff.mp (by simpa [hζnorm])))).mp hq
      have : 2 * k = 2 * l := hζ.pow_inj hkexp hlexp hpows
      omega
    have hqpow : q ^ M = 1 := by
      dsimp [q]
      have hζM : ζ ^ M = 1 := hζ.pow_eq_one
      have hpow_comm (a : ℕ) : (ζ ^ a) ^ M = (ζ ^ M) ^ a := by
        rw [← pow_mul, ← pow_mul]
        congr 1
        ac_rfl
      calc
        (conj (ζ ^ (2 * k)) * ζ ^ (2 * l)) ^ M =
            conj ((ζ ^ M) ^ (2 * k)) * (ζ ^ M) ^ (2 * l) := by
              rw [mul_pow, ← map_pow, hpow_comm, hpow_comm]
        _ = 1 := by rw [hζM]; simp
    calc
      ∑ j ∈ Finset.range M,
          conj (standardRoot M ^ (2 * j * k)) * standardRoot M ^ (2 * j * l) =
          ∑ j ∈ Finset.range M, q ^ j := by
            apply Finset.sum_congr rfl
            intro j _hj
            dsimp [q, ζ]
            have hpow_comm (a : ℕ) :
                standardRoot M ^ (2 * j * a) = (standardRoot M ^ (2 * a)) ^ j := by
              rw [← pow_mul]
              congr 1
              ac_rfl
            rw [hpow_comm k, hpow_comm l, map_pow, mul_pow]
      _ = 0 := geom_sum_eq_zero_of_pow_eq_one hqne hqpow

/-- Discrete Parseval for the anisotropy sums.  The hypothesis `2N ≤ M` prevents aliasing
between the doubled frequencies. -/
lemma sum_norm_rootGeometricSum_sq (M N : ℕ) (hM : M ≠ 0) (hsize : 2 * N ≤ M) :
    ∑ j ∈ Finset.range M, ‖rootGeometricSum M N j‖ ^ 2 = (M : ℝ) * N := by
  simp_rw [← Complex.normSq_eq_norm_sq]
  rw [← Complex.ofReal_inj]
  rw [Complex.ofReal_sum]
  simp only [Complex.normSq_eq_conj_mul_self, rootGeometricSum, map_sum]
  push_cast
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.range M)]
  calc
    _ = ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
          if k = l then (M : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      exact sum_root_pair M N k l hM hsize
        (Finset.mem_range.mp hk) (Finset.mem_range.mp hl)
    _ = (M : ℂ) * N := by
      calc
        ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
              (if k = l then (M : ℂ) else 0) =
            ∑ k ∈ Finset.range N, (M : ℂ) := by
          apply Finset.sum_congr rfl
          intro k hk
          simp [Finset.mem_range.mp hk]
        _ = (M : ℂ) * N := by simp [mul_comm]

/-- Every angle is within `π/M` of an angle representing an `M`-th root of unity.  The
integer representative is retained because it makes the rounding estimate independent of a
choice of fundamental interval. -/
lemma exists_near_standardRoot (M : ℕ) (hM : 0 < M) (θ : ℝ) :
    ∃ j < M, ∃ q : ℤ,
      |θ - 2 * Real.pi * (q : ℝ) / M| ≤ Real.pi / M ∧
      Circle.exp (2 * Real.pi * (q : ℝ) / M) = standardRootCircle M ^ j := by
  let x : ℝ := θ * M / (2 * Real.pi)
  let q : ℤ := round x
  let r : ℤ := q.emod M
  let j : ℕ := r.toNat
  have hMint : (0 : ℤ) < M := by exact_mod_cast hM
  have hr0 : 0 ≤ r := Int.emod_nonneg q (ne_of_gt hMint)
  have hrM : r < M := Int.emod_lt_of_pos q hMint
  have hjcast : (j : ℤ) = r := by
    dsimp [j]
    rw [Int.toNat_of_nonneg hr0]
  have hj : j < M := by
    rw [← Int.ofNat_lt, hjcast]
    exact hrM
  refine ⟨j, hj, q, ?_, ?_⟩
  · have hround : |x - (q : ℝ)| ≤ 1 / 2 := by
      simpa only [q] using abs_sub_round x
    have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
    have hfactor : 0 < 2 * Real.pi / (M : ℝ) := by positivity
    have hid : θ - 2 * Real.pi * (q : ℝ) / M =
        (2 * Real.pi / M) * (x - (q : ℝ)) := by
      dsimp [x]
      field_simp [Real.pi_ne_zero, ne_of_gt hMreal]
    rw [hid, abs_mul, abs_of_pos hfactor]
    calc
      (2 * Real.pi / M) * |x - (q : ℝ)| ≤
          (2 * Real.pi / M) * (1 / 2) :=
        mul_le_mul_of_nonneg_left hround hfactor.le
      _ = Real.pi / M := by ring
  · rw [show standardRootCircle M ^ j =
        Circle.exp ((j : ℝ) * (2 * Real.pi / M)) by
      unfold standardRootCircle
      exact (Circle.exp_natCast_mul (2 * Real.pi / M) j).symm]
    apply Circle.exp_eq_exp.2
    refine ⟨q.ediv M, ?_⟩
    have hdecomp := Int.emod_add_mul_ediv q (M : ℤ)
    have hjcastReal : (j : ℝ) = (r : ℝ) := by exact_mod_cast hjcast
    have hqcast : (q : ℝ) = (j : ℝ) + (M : ℝ) * (q.ediv M : ℤ) := by
      rw [hjcastReal]
      exact_mod_cast hdecomp.symm
    rw [hqcast]
    field_simp [ne_of_gt (by exact_mod_cast hM : (0 : ℝ) < M)]

lemma exists_root_controlling_maximum (ω : Sample) (n M : ℕ) (hM : 0 < M) :
    ∃ j < M,
      (1 - 3 * Real.pi * (n + 1 : ℝ) / M) * maximumModulus ω n ≤
        ‖randomPolynomial ω n ((standardRootCircle M : Circle) ^ j : ℂ)‖ := by
  obtain ⟨z, hz⟩ := exists_maximumModulus ω n
  obtain ⟨j, hj, q, hnear, hroot⟩ :=
    exists_near_standardRoot M hM (z : ℂ).arg
  refine ⟨j, hj, ?_⟩
  let θ : ℝ := (z : ℂ).arg
  let φ : ℝ := 2 * Real.pi * (q : ℝ) / M
  have hθ : Circle.exp θ = z := by
    dsimp [θ]
    exact Circle.exp_arg z
  have hφ : Circle.exp φ = standardRootCircle M ^ j := by
    simpa only [φ] using hroot
  have hangularθ : angularPolynomial ω n θ = randomPolynomial ω n (z : ℂ) := by
    unfold angularPolynomial
    rw [show circleMap 0 1 θ = (Circle.exp θ : ℂ) by simp [circleMap]]
    rw [hθ]
  have hangularφ : angularPolynomial ω n φ =
      randomPolynomial ω n ((standardRootCircle M ^ j : Circle) : ℂ) := by
    unfold angularPolynomial
    rw [show circleMap 0 1 φ = (Circle.exp φ : ℂ) by simp [circleMap]]
    rw [hφ]
  have hdiff := norm_angularPolynomial_sub_le ω n θ φ
  have hdiff' : ‖angularPolynomial ω n θ - angularPolynomial ω n φ‖ ≤
      (3 * (n + 1 : ℝ) * maximumModulus ω n) * (Real.pi / M) :=
    hdiff.trans (mul_le_mul_of_nonneg_left hnear
      (mul_nonneg (by positivity) (maximumModulus_nonneg ω n)))
  rw [hangularθ, hangularφ] at hdiff'
  calc
    (1 - 3 * Real.pi * (n + 1 : ℝ) / M) * maximumModulus ω n =
        maximumModulus ω n -
          (3 * (n + 1 : ℝ) * maximumModulus ω n) * (Real.pi / M) := by ring
    _ ≤ ‖randomPolynomial ω n (z : ℂ)‖ -
          ‖randomPolynomial ω n (↑(standardRootCircle M ^ j) : ℂ) -
            randomPolynomial ω n (z : ℂ)‖ := by
      rw [hz]
      gcongr
      simpa only [norm_sub_rev] using hdiff'
    _ ≤ ‖randomPolynomial ω n (↑(standardRootCircle M ^ j) : ℂ)‖ := by
      have htri := norm_sub_norm_le
        (randomPolynomial ω n (z : ℂ))
        (randomPolynomial ω n (↑(standardRootCircle M ^ j) : ℂ))
      rw [norm_sub_rev] at htri
      linarith

lemma rotated_re_eq_norm_mul_cos (w : ℂ) (φ : ℝ) :
    (Complex.exp ((-φ : ℂ) * Complex.I) * w).re =
      ‖w‖ * Real.cos (w.arg - φ) := by
  nth_rw 1 [← Complex.norm_mul_exp_arg_mul_I w]
  rw [show Complex.exp ((-φ : ℂ) * Complex.I) *
        ((‖w‖ : ℂ) * Complex.exp ((w.arg : ℂ) * Complex.I)) =
      (‖w‖ : ℂ) * (Complex.exp ((-φ : ℂ) * Complex.I) *
        Complex.exp ((w.arg : ℂ) * Complex.I)) by ring]
  rw [← Complex.exp_add]
  have hexp : (-φ : ℂ) * Complex.I + (w.arg : ℂ) * Complex.I =
      ((w.arg - φ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hexp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re]

lemma realProjection_eq_rotated_fourier_re (ω : Sample) (N : ℕ) (θ φ : ℝ) :
    realProjection ω N θ φ =
      (Complex.exp ((-φ : ℂ) * Complex.I) * fourierSum ω N θ).re := by
  unfold realProjection fourierSum
  rw [Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  simp only [Circle.coe_exp]
  rw [← Complex.exp_nat_mul]
  have hexp : (-φ : ℂ) * Complex.I + ((k : ℝ) * θ : ℂ) * Complex.I =
      (((k : ℝ) * θ - φ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [show Complex.exp ((-φ : ℂ) * Complex.I) *
        ((ω k : ℂ) * Complex.exp ((k : ℂ) * ((θ : ℂ) * Complex.I))) =
      (ω k : ℂ) * Complex.exp
        ((-φ : ℂ) * Complex.I + ((k : ℝ) * θ : ℂ) * Complex.I) by
      rw [Complex.exp_add]
      push_cast
      ring]
  rw [hexp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re]
  ring

def badRootIndices (M N : ℕ) (η : ℝ) : Finset ℕ :=
  (Finset.range M).filter fun j ↦ η * N < ‖rootGeometricSum M N j‖

lemma badRootIndices_weighted_card_le (M N : ℕ) {η : ℝ} (hη : 0 ≤ η)
    (hM : M ≠ 0) (hsize : 2 * N ≤ M) :
    (badRootIndices M N η).card * (η * N) ^ 2 ≤ (M : ℝ) * N := by
  have hterm : ∀ j ∈ badRootIndices M N η,
      (η * N) ^ 2 ≤ ‖rootGeometricSum M N j‖ ^ 2 := by
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    exact (sq_le_sq₀ (mul_nonneg hη (Nat.cast_nonneg _)) (norm_nonneg _)).2 hj'.le
  calc
    (badRootIndices M N η).card * (η * N) ^ 2 =
        ∑ _j ∈ badRootIndices M N η, (η * N) ^ 2 := by
      simp [mul_comm]
    _ ≤ ∑ j ∈ badRootIndices M N η, ‖rootGeometricSum M N j‖ ^ 2 :=
      Finset.sum_le_sum hterm
    _ ≤ ∑ j ∈ Finset.range M, ‖rootGeometricSum M N j‖ ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        exact (Finset.mem_filter.mp hj).1
      · intro j _hj _hnot
        positivity
    _ = (M : ℝ) * N := sum_norm_rootGeometricSum_sq M N hM hsize

lemma badRootIndices_card_mul_le (M N : ℕ) {η : ℝ} (hη : 0 < η)
    (hN : 0 < N) (hM : M ≠ 0) (hsize : 2 * N ≤ M) :
    ((badRootIndices M N η).card : ℝ) * η ^ 2 * N ≤ M := by
  have hraw := badRootIndices_weighted_card_le M N hη.le hM hsize
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  apply le_of_mul_le_mul_right ?_ hNreal
  calc
    ((badRootIndices M N η).card : ℝ) * η ^ 2 * N * N =
        ((badRootIndices M N η).card : ℝ) * (η * N) ^ 2 := by ring
    _ ≤ (M : ℝ) * N := hraw

def rootAngle (M j : ℕ) : ℝ := 2 * Real.pi * j / M

lemma fourierSum_one_two_rootAngle (M N j : ℕ) :
    fourierSum (fun _ ↦ 1) N (2 * rootAngle M j) = rootGeometricSum M N j := by
  unfold fourierSum rootGeometricSum rootAngle standardRoot
  apply Finset.sum_congr rfl
  intro k _hk
  simp only [Nat.cast_ofNat, one_mul, Circle.coe_exp]
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma sum_projection_variances_root_le (M N j : ℕ) (φ : ℝ) :
    ∑ k ∈ Finset.range N, Real.cos ((k : ℝ) * rootAngle M j - φ) ^ 2 ≤
      (N : ℝ) / 2 + ‖rootGeometricSum M N j‖ / 2 := by
  rw [sum_projection_variances]
  have hreal : ∑ k ∈ Finset.range N,
      Real.cos (2 * ((k : ℝ) * rootAngle M j - φ)) =
      (Complex.exp ((-(2 * φ) : ℂ) * Complex.I) *
        rootGeometricSum M N j).re := by
    calc
      ∑ k ∈ Finset.range N, Real.cos (2 * ((k : ℝ) * rootAngle M j - φ)) =
          realProjection (fun _ ↦ 1) N (2 * rootAngle M j) (2 * φ) := by
        unfold realProjection
        apply Finset.sum_congr rfl
        intro k _hk
        simp only [mul_one]
        congr 1
        ring
      _ = (Complex.exp ((-(2 * φ) : ℂ) * Complex.I) *
          fourierSum (fun _ ↦ 1) N (2 * rootAngle M j)).re :=
        by simpa only [Complex.ofReal_neg, Complex.ofReal_mul,
          Complex.ofReal_ofNat] using
            (realProjection_eq_rotated_fourier_re (fun _ ↦ 1) N
              (2 * rootAngle M j) (2 * φ))
      _ = _ := by rw [fourierSum_one_two_rootAngle]
  rw [hreal]
  have hre := Complex.re_le_norm
    (Complex.exp ((-(2 * φ) : ℂ) * Complex.I) * rootGeometricSum M N j)
  rw [norm_mul, Complex.norm_exp, show ((-(2 * φ) : ℂ) * Complex.I).re = 0 by simp,
    Real.exp_zero, one_mul] at hre
  linarith

def phaseFactor (Q : ℕ) : ℝ := 1 - (Real.pi / Q) ^ 2 / 2

lemma exists_phase_projection_ge (Q : ℕ) (hQ : 0 < Q) (w : ℂ) :
    ∃ l < Q, phaseFactor Q * ‖w‖ ≤
      (Complex.exp ((-rootAngle Q l : ℂ) * Complex.I) * w).re := by
  obtain ⟨l, hl, q, hnear, hroot⟩ := exists_near_standardRoot Q hQ w.arg
  refine ⟨l, hl, ?_⟩
  let φ : ℝ := 2 * Real.pi * (q : ℝ) / Q
  have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hsquare : (w.arg - φ) ^ 2 ≤ (Real.pi / Q) ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg (w.arg - φ)) hnear
    simpa only [← pow_two, sq_abs] using h
  have hcos : phaseFactor Q ≤ Real.cos (w.arg - φ) := by
    unfold phaseFactor
    linarith [Real.one_sub_sq_div_two_le_cos (x := w.arg - φ)]
  have hprojφ : phaseFactor Q * ‖w‖ ≤
      (Complex.exp ((-φ : ℂ) * Complex.I) * w).re := by
    rw [rotated_re_eq_norm_mul_cos]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_right hcos (norm_nonneg w)
  have hrootangle : Circle.exp (rootAngle Q l) = standardRootCircle Q ^ l := by
    unfold rootAngle standardRootCircle
    convert Circle.exp_natCast_mul (2 * Real.pi / Q) l using 1 <;> ring
  have hpositive : Complex.exp ((φ : ℂ) * Complex.I) =
      Complex.exp ((rootAngle Q l : ℂ) * Complex.I) := by
    have hc : Circle.exp φ = Circle.exp (rootAngle Q l) := by
      rw [hrootangle]
      simpa only [φ] using hroot
    exact congrArg Subtype.val hc
  have hnegative : Complex.exp ((-φ : ℂ) * Complex.I) =
      Complex.exp ((-rootAngle Q l : ℂ) * Complex.I) := by
    have hi := congrArg Inv.inv hpositive
    rw [← Complex.exp_neg, ← Complex.exp_neg] at hi
    convert hi using 1 <;> congr 1 <;> ring
  rwa [← hnegative]

lemma measureReal_linearForm_ge_le_of_sum_sq_le (s : Finset ℕ) (a : ℕ → ℝ)
    {t v : ℝ} (ht : 0 < t) (hv : 0 < v) (hsum : ∑ k ∈ s, a k ^ 2 ≤ v) :
    signMeasure.real {ω | t ≤ linearForm s a ω} ≤ Real.exp (-t ^ 2 / (2 * v)) := by
  let S : ℝ := ∑ k ∈ s, a k ^ 2
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  by_cases hSz : S = 0
  · have ha : ∀ k ∈ s, a k = 0 := by
      intro k hk
      have hkzero : a k ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ sq_nonneg (a i))).mp hSz k hk
      exact sq_eq_zero_iff.mp hkzero
    have hempty : {ω | t ≤ linearForm s a ω} = ∅ := by
      ext ω
      have hlinear : linearForm s a ω = 0 := by
        unfold linearForm
        apply Finset.sum_eq_zero
        intro k hk
        rw [ha k hk, zero_mul]
      simp [hlinear, not_le.mpr ht]
    rw [hempty, measureReal_empty]
    positivity
  · have hSpos : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hSz)
    have hbase := measureReal_linearForm_ge_le s a ht.le
    change signMeasure.real {ω | t ≤ linearForm s a ω} ≤
      Real.exp (-t ^ 2 / (2 * S)) at hbase
    change signMeasure.real {ω | t ≤ linearForm s a ω} ≤ _
    change S ≤ v at hsum
    refine hbase.trans (Real.exp_le_exp.mpr ?_)
    have hdiv := div_le_div_of_nonneg_left (sq_nonneg t)
      (by positivity : 0 < 2 * S)
      (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2))
    rw [neg_div, neg_div]
    exact neg_le_neg hdiv

lemma measureReal_fourier_norm_ge_le_of_projection_variance
    (N Q : ℕ) (θ : ℝ) {T v : ℝ} (hQ : 0 < Q)
    (hfactor : 0 < phaseFactor Q) (hT : 0 < T) (hv : 0 < v)
    (hvar : ∀ l < Q,
      ∑ k ∈ Finset.range N, Real.cos ((k : ℝ) * θ - rootAngle Q l) ^ 2 ≤ v) :
    signMeasure.real {ω | T ≤ ‖fourierSum ω N θ‖} ≤
      Q * Real.exp (-(phaseFactor Q * T) ^ 2 / (2 * v)) := by
  let A : Set Sample := {ω | T ≤ ‖fourierSum ω N θ‖}
  let B : ℕ → Set Sample := fun l ↦
    {ω | phaseFactor Q * T ≤ realProjection ω N θ (rootAngle Q l)}
  have hsubset : A ⊆ ⋃ l ∈ Finset.range Q, B l := by
    intro ω hω
    obtain ⟨l, hl, hproj⟩ := exists_phase_projection_ge Q hQ (fourierSum ω N θ)
    have hthreshold : phaseFactor Q * T ≤
        phaseFactor Q * ‖fourierSum ω N θ‖ :=
      mul_le_mul_of_nonneg_left hω hfactor.le
    have hrotated :
        (Complex.exp ((-rootAngle Q l : ℂ) * Complex.I) *
          fourierSum ω N θ).re = realProjection ω N θ (rootAngle Q l) :=
      (realProjection_eq_rotated_fourier_re ω N θ (rootAngle Q l)).symm
    simp only [mem_iUnion, mem_setOf_eq, B]
    exact ⟨l, ⟨Finset.mem_range.mpr hl, by rw [← hrotated]; exact hthreshold.trans hproj⟩⟩
  calc
    signMeasure.real A ≤ signMeasure.real (⋃ l ∈ Finset.range Q, B l) :=
      measureReal_mono hsubset (measure_lt_top signMeasure _).ne
    _ ≤ ∑ l ∈ Finset.range Q, signMeasure.real (B l) :=
      measureReal_biUnion_finset_le (Finset.range Q) B
    _ ≤ ∑ _l ∈ Finset.range Q,
        Real.exp (-(phaseFactor Q * T) ^ 2 / (2 * v)) := by
      apply Finset.sum_le_sum
      intro l hl
      have hlQ := Finset.mem_range.mp hl
      simpa only [B, realProjection, linearForm] using
        measureReal_linearForm_ge_le_of_sum_sq_le (Finset.range N)
          (fun k ↦ Real.cos ((k : ℝ) * θ - rootAngle Q l))
          (mul_pos hfactor hT) hv (hvar l hlQ)
    _ = Q * Real.exp (-(phaseFactor Q * T) ^ 2 / (2 * v)) := by
      simp [mul_comm]

lemma fourierSum_rootAngle_eq_randomPolynomial (ω : Sample) (n M j : ℕ) :
    fourierSum ω (n + 1) (rootAngle M j) =
      randomPolynomial ω n (↑(standardRootCircle M ^ j) : ℂ) := by
  rw [fourierSum_succ_eq_randomPolynomial]
  congr 1
  have h := Circle.exp_natCast_mul (2 * Real.pi / M) j
  unfold rootAngle standardRootCircle
  convert congrArg Subtype.val h using 1 <;> ring

lemma measureReal_fourier_root_norm_ge_le_good
    (M N j Q : ℕ) {η T : ℝ} (hj : j < M) (hN : 0 < N) (hη : 0 < η)
    (hQ : 0 < Q) (hfactor : 0 < phaseFactor Q) (hT : 0 < T)
    (hgood : j ∉ badRootIndices M N η) :
    signMeasure.real {ω | T ≤ ‖fourierSum ω N (rootAngle M j)‖} ≤
      Q * Real.exp (-(phaseFactor Q * T) ^ 2 / ((1 + η) * N)) := by
  have hgeom : ‖rootGeometricSum M N j‖ ≤ η * N := by
    rw [badRootIndices, Finset.mem_filter, not_and_or] at hgood
    exact le_of_not_gt (hgood.resolve_left (not_not_intro (Finset.mem_range.mpr hj)))
  have hv : 0 < (1 + η) * N / 2 := by positivity
  have hvar (l : ℕ) (_hl : l < Q) :
      ∑ k ∈ Finset.range N,
          Real.cos ((k : ℝ) * rootAngle M j - rootAngle Q l) ^ 2 ≤
        (1 + η) * N / 2 := by
    calc
      _ ≤ (N : ℝ) / 2 + ‖rootGeometricSum M N j‖ / 2 :=
        sum_projection_variances_root_le M N j (rootAngle Q l)
      _ ≤ (1 + η) * N / 2 := by nlinarith
  convert measureReal_fourier_norm_ge_le_of_projection_variance
    N Q (rootAngle M j) hQ hfactor hT hv hvar using 1 <;> ring

lemma measureReal_fourier_root_norm_ge_le_crude
    (M N j Q : ℕ) {T : ℝ} (hN : 0 < N)
    (hQ : 0 < Q) (hfactor : 0 < phaseFactor Q) (hT : 0 < T) :
    signMeasure.real {ω | T ≤ ‖fourierSum ω N (rootAngle M j)‖} ≤
      Q * Real.exp (-(phaseFactor Q * T) ^ 2 / (2 * N)) := by
  have hv : (0 : ℝ) < N := by exact_mod_cast hN
  have hvar (l : ℕ) (_hl : l < Q) :
      ∑ k ∈ Finset.range N,
          Real.cos ((k : ℝ) * rootAngle M j - rootAngle Q l) ^ 2 ≤ (N : ℝ) := by
    calc
      _ ≤ ∑ _k ∈ Finset.range N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k _hk
        nlinarith [Real.neg_one_le_cos ((k : ℝ) * rootAngle M j - rootAngle Q l),
          Real.cos_le_one ((k : ℝ) * rootAngle M j - rootAngle Q l)]
      _ = N := by simp
  exact measureReal_fourier_norm_ge_le_of_projection_variance
    N Q (rootAngle M j) hQ hfactor hT hv hvar

def meshFactor (K : ℕ) : ℝ := 1 - 3 * Real.pi / K

def upperK (m : ℕ) : ℕ := 10000 * m

def upperQ (m : ℕ) : ℕ := 100 * m

def upperEta (m : ℕ) : ℝ := 1 / (100 * m)

lemma upper_phase_lower {m : ℕ} (hm : 1 ≤ m) :
    1 - 1 / (100 * (m : ℝ)) ≤ phaseFactor (upperQ m) := by
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpi0 := Real.pi_pos.le
  have hpi4 := (Real.pi_lt_four).le
  have hpisq : Real.pi ^ 2 ≤ 16 := by nlinarith [sq_nonneg (4 - Real.pi)]
  unfold phaseFactor upperQ
  push_cast
  have hden : (0 : ℝ) < 100 * m := by positivity
  have hm100 : (100 : ℝ) ≤ 100 * m := by nlinarith
  have hsmall : (Real.pi / (100 * m)) ^ 2 / 2 ≤ 1 / (100 * m) := by
    rw [div_pow]
    field_simp
    nlinarith
  exact sub_le_sub_left hsmall 1

lemma upper_mesh_lower {m : ℕ} (hm : 1 ≤ m) :
    1 - 1 / (100 * (m : ℝ)) ≤ meshFactor (upperK m) := by
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  unfold meshFactor upperK
  push_cast
  have hden : (0 : ℝ) < 10000 * m := by positivity
  have hpi := (Real.pi_lt_four).le
  apply sub_le_sub_left
  apply (div_le_iff₀ hden).2
  field_simp
  nlinarith

lemma upper_effective_lower {m : ℕ} (hm : 1 ≤ m) :
    1 + 9 / (10 * (m : ℝ)) ≤
      phaseFactor (upperQ m) * meshFactor (upperK m) * (1 + 1 / (m : ℝ)) := by
  let x : ℝ := (m : ℝ)
  let d : ℝ := 1 / (100 * x)
  have hx : 1 ≤ x := by dsimp [x]; exact_mod_cast hm
  have hphase : 1 - d ≤ phaseFactor (upperQ m) := by
    simpa only [d, x] using upper_phase_lower hm
  have hmesh : 1 - d ≤ meshFactor (upperK m) := by
    simpa only [d, x] using upper_mesh_lower hm
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hdle : d ≤ 1 / 100 := by
    dsimp [d]
    exact one_div_le_one_div_of_le (by norm_num)
      (by nlinarith : (100 : ℝ) ≤ 100 * x)
  have hbase0 : 0 ≤ 1 - d := by linarith
  have hphase0 : 0 ≤ phaseFactor (upperQ m) := hbase0.trans hphase
  have hprod : (1 - d) ^ 2 ≤ phaseFactor (upperQ m) * meshFactor (upperK m) := by
    calc
      (1 - d) ^ 2 = (1 - d) * (1 - d) := by ring
      _ ≤ phaseFactor (upperQ m) * meshFactor (upperK m) :=
        mul_le_mul hphase hmesh hbase0 hphase0
  have hscale : 0 ≤ 1 + 1 / x := by positivity
  calc
    1 + 9 / (10 * (m : ℝ)) ≤ (1 - d) ^ 2 * (1 + 1 / x) := by
      dsimp [d, x]
      field_simp
      nlinarith
    _ ≤ phaseFactor (upperQ m) * meshFactor (upperK m) * (1 + 1 / x) :=
      mul_le_mul_of_nonneg_right hprod hscale
    _ = _ := by rfl

lemma upper_effective_good_sq {m : ℕ} (hm : 1 ≤ m) :
    (1 + 1 / (m : ℝ)) * (1 + upperEta m) ≤
      (phaseFactor (upperQ m) * meshFactor (upperK m) *
        (1 + 1 / (m : ℝ))) ^ 2 := by
  let x : ℝ := (m : ℝ)
  let e : ℝ := phaseFactor (upperQ m) * meshFactor (upperK m) * (1 + 1 / x)
  have hx : 1 ≤ x := by dsimp [x]; exact_mod_cast hm
  have he : 1 + 9 / (10 * x) ≤ e := by
    simpa only [e, x] using upper_effective_lower hm
  have he0 : 0 ≤ e := (by positivity : (0 : ℝ) ≤ 1 + 9 / (10 * x)).trans he
  have htarget : (1 + 1 / x) * (1 + 1 / (100 * x)) ≤
      (1 + 9 / (10 * x)) ^ 2 := by
    field_simp
    nlinarith
  calc
    (1 + 1 / (m : ℝ)) * (1 + upperEta m) =
        (1 + 1 / x) * (1 + 1 / (100 * x)) := by rfl
    _ ≤ (1 + 9 / (10 * x)) ^ 2 := htarget
    _ ≤ e ^ 2 := by
      exact (sq_le_sq₀ (by positivity) he0).2 he
    _ = _ := by rfl

lemma measureReal_maximum_ge_le_mesh
    (n K Q : ℕ) {η U : ℝ} (hK : 2 ≤ K) (hη : 0 < η)
    (hQ : 0 < Q) (hphase : 0 < phaseFactor Q)
    (hmesh : 0 < meshFactor K) (hU : 0 < U) :
    let N := n + 1
    let M := K * N
    let T := meshFactor K * U
    signMeasure.real {ω | U ≤ maximumModulus ω n} ≤
      M * (Q * Real.exp (-(phaseFactor Q * T) ^ 2 / ((1 + η) * N))) +
      (badRootIndices M N η).card *
        (Q * Real.exp (-(phaseFactor Q * T) ^ 2 / (2 * N))) := by
  dsimp only
  let N : ℕ := n + 1
  let M : ℕ := K * N
  let T : ℝ := meshFactor K * U
  let A : Set Sample := {ω | U ≤ maximumModulus ω n}
  let B : ℕ → Set Sample := fun j ↦
    {ω | T ≤ ‖fourierSum ω N (rootAngle M j)‖}
  have hN : 0 < N := by dsimp [N]; omega
  have hM : 0 < M := mul_pos (lt_of_lt_of_le (by omega) hK) hN
  have hT : 0 < T := mul_pos hmesh hU
  have hsize : 2 * N ≤ M := by dsimp [M]; nlinarith
  have hfactor_identity : 1 - 3 * Real.pi * (n + 1 : ℝ) / M = meshFactor K := by
    unfold meshFactor
    dsimp [M, N]
    have hKreal : (0 : ℝ) < K := by exact_mod_cast (lt_of_lt_of_le (by omega) hK)
    have hNreal : (0 : ℝ) < n + 1 := by positivity
    push_cast
    field_simp
  have hsubset : A ⊆ ⋃ j ∈ Finset.range M, B j := by
    intro ω hω
    obtain ⟨j, hj, hjmax⟩ := exists_root_controlling_maximum ω n M hM
    rw [hfactor_identity] at hjmax
    have hthreshold : T ≤ meshFactor K * maximumModulus ω n := by
      exact mul_le_mul_of_nonneg_left hω hmesh.le
    have hroot : fourierSum ω N (rootAngle M j) =
        randomPolynomial ω n (↑(standardRootCircle M ^ j) : ℂ) := by
      simpa only [N] using fourierSum_rootAngle_eq_randomPolynomial ω n M j
    simp only [mem_iUnion, mem_setOf_eq, B]
    exact ⟨j, ⟨Finset.mem_range.mpr hj, by rw [hroot]; exact hthreshold.trans hjmax⟩⟩
  let pGood : ℝ :=
    Q * Real.exp (-(phaseFactor Q * T) ^ 2 / ((1 + η) * N))
  let pBad : ℝ :=
    Q * Real.exp (-(phaseFactor Q * T) ^ 2 / (2 * N))
  have hroot_bound (j : ℕ) (hj : j ∈ Finset.range M) :
      signMeasure.real (B j) ≤ pGood + if j ∈ badRootIndices M N η then pBad else 0 := by
    have hjM := Finset.mem_range.mp hj
    by_cases hbad : j ∈ badRootIndices M N η
    · have hcrude := measureReal_fourier_root_norm_ge_le_crude
        M N j Q hN hQ hphase hT
      dsimp [B, pBad] at hcrude ⊢
      rw [if_pos hbad]
      exact hcrude.trans (le_add_of_nonneg_left (by positivity))
    · have hgood := measureReal_fourier_root_norm_ge_le_good
        M N j Q hjM hN hη hQ hphase hT hbad
      dsimp [B, pGood] at hgood ⊢
      rw [if_neg hbad, add_zero]
      exact hgood
  calc
    signMeasure.real A ≤ signMeasure.real (⋃ j ∈ Finset.range M, B j) :=
      measureReal_mono hsubset (measure_lt_top signMeasure _).ne
    _ ≤ ∑ j ∈ Finset.range M, signMeasure.real (B j) :=
      measureReal_biUnion_finset_le (Finset.range M) B
    _ ≤ ∑ j ∈ Finset.range M,
        (pGood + if j ∈ badRootIndices M N η then pBad else 0) :=
      Finset.sum_le_sum hroot_bound
    _ = M * pGood + (badRootIndices M N η).card * pBad := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hsub : badRootIndices M N η ⊆ Finset.range M := by
        intro j hj
        exact (Finset.mem_filter.mp hj).1
      have hfilter : (Finset.range M).filter (fun j ↦ j ∈ badRootIndices M N η) =
          badRootIndices M N η := by
        ext j
        simp [badRootIndices]
      rw [← Finset.sum_filter]
      rw [hfilter]
      simp [mul_comm]
    _ = _ := by rfl

def upperMaximumLevel (m N : ℕ) : ℝ :=
  (1 + 1 / (m : ℝ)) * Real.sqrt ((N : ℝ) * Real.log N)

def upperMaximumFailure (m N : ℕ) : Set Sample :=
  {ω | upperMaximumLevel m N ≤ maximumModulus ω (N - 1)}

def upperTailConstant (m : ℕ) : ℝ :=
  upperK m * upperQ m + (upperK m / upperEta m ^ 2) * upperQ m

theorem measureReal_upperMaximumFailure_le_two_terms {m N : ℕ} (hm : 1 ≤ m) (hN : 2 ≤ N) :
    signMeasure.real (upperMaximumFailure m N) ≤
      (upperK m : ℝ) * upperQ m * (N : ℝ) ^ (-(1 / (m : ℝ)) : ℝ) +
        (upperK m / upperEta m ^ 2) * upperQ m * (N : ℝ) ^ (-(1 / 2) : ℝ) := by
  let x : ℝ := (N : ℝ)
  let L : ℝ := Real.log x
  let η : ℝ := upperEta m
  let K : ℕ := upperK m
  let Q : ℕ := upperQ m
  let e : ℝ := phaseFactor Q * meshFactor K * (1 + 1 / (m : ℝ))
  let U : ℝ := upperMaximumLevel m N
  let T : ℝ := meshFactor K * U
  have hx : 1 ≤ x := by dsimp [x]; exact_mod_cast (le_trans (by omega : 1 ≤ 2) hN)
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hL0 : 0 ≤ L := Real.log_nonneg hx
  have hLpos : 0 < L := Real.log_pos (by dsimp [x]; exact_mod_cast hN)
  have hη : 0 < η := by dsimp [η, upperEta]; positivity
  have hK : 2 ≤ K := by dsimp [K, upperK]; nlinarith
  have hQ : 0 < Q := by dsimp [Q, upperQ]; omega
  have hbasepos : 0 < 1 - 1 / (100 * (m : ℝ)) := by
    have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have : 1 / (100 * (m : ℝ)) ≤ 1 / 100 :=
      one_div_le_one_div_of_le (by norm_num) (by nlinarith)
    linarith
  have hphase : 0 < phaseFactor Q := by
    dsimp [Q]
    exact hbasepos.trans_le (upper_phase_lower hm)
  have hmesh : 0 < meshFactor K := by
    dsimp [K]
    exact hbasepos.trans_le (upper_mesh_lower hm)
  have hU : 0 < U := by
    dsimp [U, upperMaximumLevel]
    positivity
  have hT : 0 < T := mul_pos hmesh hU
  have hsqrtSq : Real.sqrt (x * L) ^ 2 = x * L := by
    rw [Real.sq_sqrt]
    positivity
  have heq : phaseFactor Q * T = e * Real.sqrt (x * L) := by
    dsimp [T, U, e, upperMaximumLevel, x, L]
    ring
  have heff : 1 + 9 / (10 * (m : ℝ)) ≤ e := by
    dsimp [e, Q, K]
    exact upper_effective_lower hm
  have he0 : 0 ≤ e := (by positivity : (0 : ℝ) ≤ 1 + 9 / (10 * (m : ℝ))).trans heff
  have heone : 1 ≤ e := by
    have : 0 ≤ 9 / (10 * (m : ℝ)) := by positivity
    linarith
  have hegood : (1 + 1 / (m : ℝ)) * (1 + η) ≤ e ^ 2 := by
    dsimp [e, Q, K, η]
    exact upper_effective_good_sq hm
  have hgoodExponent :
      (1 + 1 / (m : ℝ)) * L ≤ (phaseFactor Q * T) ^ 2 / ((1 + η) * x) := by
    have hden : 0 < (1 + η) * x := by positivity
    rw [heq, mul_pow, hsqrtSq]
    apply (le_div_iff₀ hden).2
    have hmul := mul_le_mul_of_nonneg_right hegood (mul_nonneg hx0.le hL0)
    nlinarith
  have hbadExponent : L / 2 ≤ (phaseFactor Q * T) ^ 2 / (2 * x) := by
    rw [heq, mul_pow, hsqrtSq]
    have heSq : 1 ≤ e ^ 2 := by nlinarith [sq_nonneg (e - 1)]
    have hden : (0 : ℝ) < 2 * x := by positivity
    apply (le_div_iff₀ hden).2
    nlinarith [mul_le_mul_of_nonneg_right heSq (mul_nonneg hx0.le hL0)]
  have hgoodExp : Real.exp (-(phaseFactor Q * T) ^ 2 / ((1 + η) * x)) ≤
      x ^ (-(1 + 1 / (m : ℝ)) : ℝ) := by
    rw [Real.rpow_def_of_pos hx0]
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    nlinarith
  have hbadExp : Real.exp (-(phaseFactor Q * T) ^ 2 / (2 * x)) ≤
      x ^ (-(1 / 2) : ℝ) := by
    rw [Real.rpow_def_of_pos hx0]
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    nlinarith
  have hn : N - 1 + 1 = N := Nat.sub_add_cancel (le_trans (by omega : 1 ≤ 2) hN)
  have hraw := measureReal_maximum_ge_le_mesh (N - 1) K Q hK hη hQ hphase hmesh hU
  dsimp only at hraw
  rw [hn] at hraw
  change signMeasure.real {ω | U ≤ maximumModulus ω (N - 1)} ≤
      (K * N : ℕ) *
          (Q * Real.exp (-(phaseFactor Q * T) ^ 2 / ((1 + η) * N))) +
        (badRootIndices (K * N) N η).card *
          (Q * Real.exp (-(phaseFactor Q * T) ^ 2 / (2 * N))) at hraw
  have hgoodTerm :
      ((K * N : ℕ) : ℝ) *
          (Q * Real.exp (-(phaseFactor Q * T) ^ 2 / ((1 + η) * N))) ≤
        (K : ℝ) * Q * x ^ (-(1 / (m : ℝ)) : ℝ) := by
    calc
      _ ≤ ((K * N : ℕ) : ℝ) * (Q * x ^ (-(1 + 1 / (m : ℝ)) : ℝ)) := by
        gcongr
      _ = (K : ℝ) * Q * x ^ (-(1 / (m : ℝ)) : ℝ) := by
        push_cast
        calc
          (K : ℝ) * x * (Q * x ^ (-(1 + 1 / (m : ℝ)) : ℝ)) =
              (K : ℝ) * Q *
                (x ^ (1 : ℝ) * x ^ (-(1 + 1 / (m : ℝ)) : ℝ)) := by
            rw [Real.rpow_one]
            ring
          _ = (K : ℝ) * Q *
              x ^ ((1 : ℝ) + (-(1 + 1 / (m : ℝ)))) := by
            rw [Real.rpow_add hx0]
          _ = _ := by congr 2; ring
  have hbadCardRaw := badRootIndices_card_mul_le (K * N) N hη
    (lt_of_lt_of_le (by omega) hN) (by positivity) (by nlinarith [hK])
  have hbadCard : ((badRootIndices (K * N) N η).card : ℝ) ≤ K / η ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hη)).2
    apply le_of_mul_le_mul_right ?_ hx0
    calc
      ((badRootIndices (K * N) N η).card : ℝ) * η ^ 2 * x =
          ((badRootIndices (K * N) N η).card : ℝ) * η ^ 2 * (N : ℝ) := rfl
      _ ≤ ((K * N : ℕ) : ℝ) := hbadCardRaw
      _ = (K : ℝ) * x := by push_cast; rfl
  have hbadTerm :
      ((badRootIndices (K * N) N η).card : ℝ) *
          (Q * Real.exp (-(phaseFactor Q * T) ^ 2 / (2 * N))) ≤
        (K / η ^ 2) * Q * x ^ (-(1 / 2) : ℝ) := by
    calc
      _ ≤ (K / η ^ 2) * (Q * x ^ (-(1 / 2) : ℝ)) := by
        gcongr
      _ = _ := by ring
  exact hraw.trans (add_le_add hgoodTerm hbadTerm)

theorem measureReal_upperMaximumFailure_le {m N : ℕ} (hm : 1 ≤ m) (hN : 2 ≤ N) :
    signMeasure.real (upperMaximumFailure m N) ≤
      upperTailConstant m * (N : ℝ) ^ (-(1 / (2 * (m : ℝ))) : ℝ) := by
  let x : ℝ := (N : ℝ)
  have hx : 1 ≤ x := by dsimp [x]; exact_mod_cast (le_trans (by omega : 1 ≤ 2) hN)
  have hpowerGood : x ^ (-(1 / (m : ℝ)) : ℝ) ≤
      x ^ (-(1 / (2 * (m : ℝ))) : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le hx
    have hmreal : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by omega) hm)
    rw [neg_le_neg_iff]
    field_simp
    norm_num
  have hpowerBad : x ^ (-(1 / 2) : ℝ) ≤
      x ^ (-(1 / (2 * (m : ℝ))) : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le hx
    have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
    rw [neg_le_neg_iff]
    field_simp
    exact hmreal
  have hraw := measureReal_upperMaximumFailure_le_two_terms hm hN
  let a : ℝ := (upperK m : ℝ) * upperQ m
  let b : ℝ := (upperK m / upperEta m ^ 2) * upperQ m
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by
    dsimp [b, upperEta]
    positivity
  change signMeasure.real (upperMaximumFailure m N) ≤
      (a + b) * x ^ (-(1 / (2 * (m : ℝ))) : ℝ)
  change signMeasure.real (upperMaximumFailure m N) ≤
      a * x ^ (-(1 / (m : ℝ)) : ℝ) + b * x ^ (-(1 / 2) : ℝ) at hraw
  calc
    signMeasure.real (upperMaximumFailure m N) ≤
        a * x ^ (-(1 / (m : ℝ)) : ℝ) + b * x ^ (-(1 / 2) : ℝ) := hraw
    _ ≤ a * x ^ (-(1 / (2 * (m : ℝ))) : ℝ) +
          b * x ^ (-(1 / (2 * (m : ℝ))) : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hpowerGood ha)
        (mul_le_mul_of_nonneg_left hpowerBad hb)
    _ = (a + b) * x ^ (-(1 / (2 * (m : ℝ))) : ℝ) := by ring

/-! ## Geometric subsequences and Borel--Cantelli -/

def geometricIndex (L : ℕ) : ℕ → ℕ
  | 0 => 1
  | j + 1 => geometricIndex L j + geometricIndex L j / L + 1

@[simp] lemma geometricIndex_zero (L : ℕ) : geometricIndex L 0 = 1 := rfl

@[simp] lemma geometricIndex_succ (L j : ℕ) :
    geometricIndex L (j + 1) =
      geometricIndex L j + geometricIndex L j / L + 1 := rfl

lemma geometricIndex_pos (L j : ℕ) : 0 < geometricIndex L j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [geometricIndex_succ]
      exact lt_of_lt_of_le ih
        (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))

lemma geometricIndex_strictMono (L : ℕ) : StrictMono (geometricIndex L) := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [geometricIndex_succ]
  have h : 0 ≤ geometricIndex L j / L := Nat.zero_le _
  omega

lemma geometricIndex_growth {L : ℕ} (hL : 0 < L) (j : ℕ) :
    (1 + 1 / (L : ℝ)) * geometricIndex L j ≤ geometricIndex L (j + 1) := by
  let N := geometricIndex L j
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hnat : N < (N / L + 1) * L := by
    exact (Nat.div_lt_iff_lt_mul hL).mp (Nat.lt_succ_self (N / L))
  have hdiv : (N : ℝ) / L < (N / L : ℕ) + 1 := by
    apply (div_lt_iff₀ hLreal).2
    exact_mod_cast hnat
  rw [geometricIndex_succ]
  change (1 + 1 / (L : ℝ)) * (N : ℝ) ≤ (N + N / L + 1 : ℕ)
  push_cast
  calc
    (1 + 1 / (L : ℝ)) * (N : ℝ) = (N : ℝ) + (N : ℝ) / L := by ring
    _ ≤ (N : ℝ) + (N / L : ℕ) + 1 := by linarith

lemma geometric_pow_le_index {L : ℕ} (hL : 0 < L) (j : ℕ) :
    (1 + 1 / (L : ℝ)) ^ j ≤ geometricIndex L j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ]
      calc
        (1 + 1 / (L : ℝ)) ^ j * (1 + 1 / (L : ℝ)) ≤
            (geometricIndex L j : ℝ) * (1 + 1 / (L : ℝ)) := by
          gcongr
        _ = (1 + 1 / (L : ℝ)) * geometricIndex L j := by ring
        _ ≤ geometricIndex L (j + 1) := geometricIndex_growth hL j

lemma tendsto_geometricIndex_atTop {L : ℕ} (hL : 0 < L) :
    Tendsto (geometricIndex L) atTop atTop := by
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hone : (1 : ℝ) < 1 + 1 / (L : ℝ) := by
    linarith [one_div_pos.mpr hLreal]
  have hpow := tendsto_pow_atTop_atTop_of_one_lt hone
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  exact tendsto_atTop_mono' atTop
    (Eventually.of_forall fun j ↦ geometric_pow_le_index hL j) hpow

lemma summable_geometricIndex_rpow {L : ℕ} (hL : 0 < L) {p : ℝ} (hp : 0 < p) :
    Summable fun j : ℕ ↦ (geometricIndex L j : ℝ) ^ (-p) := by
  let r : ℝ := 1 + 1 / (L : ℝ)
  let q : ℝ := r ^ (-p)
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hr : 1 < r := by dsimp [r]; linarith [one_div_pos.mpr hLreal]
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hq0 : 0 ≤ q := Real.rpow_nonneg hr0.le _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg hr (neg_neg_of_pos hp)
  have hgeom : Summable fun j : ℕ ↦ q ^ j := summable_geometric_of_lt_one hq0 hq1
  apply Summable.of_nonneg_of_le (fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun j ↦ ?_) hgeom
  have hbase := geometric_pow_le_index hL j
  have hpow := Real.rpow_le_rpow_of_nonpos (pow_pos hr0 j) hbase (neg_nonpos.mpr hp.le)
  calc
    (geometricIndex L j : ℝ) ^ (-p) ≤ (r ^ j) ^ (-p) := by
      simpa only [r] using hpow
    _ = q ^ j := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr0.le,
        show (j : ℝ) * -p = -p * j by ring, Real.rpow_mul hr0.le,
        Real.rpow_natCast]

/-! Shifts of the canonical product space have exactly the same law.  This lets us apply the
finite-polynomial estimates above to every consecutive block of coefficients. -/

def shiftSample (a : ℕ) (ω : Sample) : Sample := fun k ↦ ω (a + k)

lemma measurable_shiftSample (a : ℕ) : Measurable (shiftSample a) := by
  exact measurable_pi_lambda _ fun k ↦ measurable_pi_apply (a + k)

lemma hasLaw_shiftSample (a : ℕ) : HasLaw (shiftSample a) signMeasure signMeasure := by
  have hind : iIndepFun (fun k (ω : Sample) ↦ ω (a + k)) signMeasure := by
    apply iIndepFun_coordinate.precomp
    intro k l hkl
    omega
  have hlaw : ∀ k : ℕ,
      HasLaw (fun ω : Sample ↦ ω (a + k)) rademacherMeasure signMeasure :=
    fun k ↦ hasLaw_coordinate (a + k)
  unfold signMeasure
  exact hind.hasLaw_infinitePi hlaw (measurable_shiftSample a).aemeasurable

lemma measurableSet_upperMaximumFailure (m N : ℕ) :
    MeasurableSet (upperMaximumFailure m N) := by
  exact measurableSet_le measurable_const (measurable_maximumModulus (N - 1))

lemma measureReal_shift_upperMaximumFailure (a m N : ℕ) :
    signMeasure.real {ω | shiftSample a ω ∈ upperMaximumFailure m N} =
      signMeasure.real (upperMaximumFailure m N) := by
  exact (hasLaw_shiftSample a).measureReal_eq (measurableSet_upperMaximumFailure m N)

/-! A deliberately coarse but threshold-sensitive version of the finite upper estimate.  Its
exponent is what is needed to control all partial polynomials in a short coefficient block. -/

lemma measureReal_maximum_ge_le_crude
    (n K Q : ℕ) {U : ℝ} (hK : 2 ≤ K) (hQ : 0 < Q)
    (hphase : 0 < phaseFactor Q) (hmesh : 0 < meshFactor K) (hU : 0 < U) :
    signMeasure.real {ω | U ≤ maximumModulus ω n} ≤
      2 * (K * (n + 1) : ℕ) * Q *
        Real.exp (-(phaseFactor Q * meshFactor K * U) ^ 2 / (2 * (n + 1))) := by
  have hraw := measureReal_maximum_ge_le_mesh n K Q (η := (1 : ℝ)) (U := U)
    hK (by norm_num) hQ hphase hmesh hU
  dsimp only at hraw
  norm_num [Nat.cast_add, Nat.cast_mul, mul_assoc] at hraw
  have hcardNat : (badRootIndices (K * (n + 1)) (n + 1) 1).card ≤ K * (n + 1) := by
    simpa only [badRootIndices, Finset.card_range] using
      (Finset.card_filter_le (Finset.range (K * (n + 1)))
        (fun j : ℕ ↦ (1 : ℝ) * ((n + 1 : ℕ) : ℝ) <
          ‖rootGeometricSum (K * (n + 1)) (n + 1) j‖))
  have hcard : ((badRootIndices (K * (n + 1)) (n + 1) 1).card : ℝ) ≤
      K * (n + 1) := by exact_mod_cast hcardNat
  have hQ0 : (0 : ℝ) ≤ Q := by positivity
  have hX0 : 0 ≤ Real.exp (-(phaseFactor Q * meshFactor K * U) ^ 2 /
      (2 * (n + 1))) := Real.exp_pos _ |>.le
  have hraw' : signMeasure.real {ω | U ≤ maximumModulus ω n} ≤
      (K * (n + 1)) *
          (Q * Real.exp (-(phaseFactor Q * meshFactor K * U) ^ 2 / (2 * (n + 1)))) +
        (badRootIndices (K * (n + 1)) (n + 1) 1).card *
          (Q * Real.exp (-(phaseFactor Q * meshFactor K * U) ^ 2 /
            (2 * (n + 1)))) := by
    simpa only [mul_assoc] using hraw
  calc
    signMeasure.real {ω | U ≤ maximumModulus ω n} ≤
        (K * (n + 1)) *
            (Q * Real.exp (-(phaseFactor Q * meshFactor K * U) ^ 2 / (2 * (n + 1)))) +
          (badRootIndices (K * (n + 1)) (n + 1) 1).card *
            (Q * Real.exp (-(phaseFactor Q * meshFactor K * U) ^ 2 /
              (2 * (n + 1)))) := hraw'
    _ ≤ (K * (n + 1)) *
            (Q * Real.exp (-(phaseFactor Q * meshFactor K * U) ^ 2 / (2 * (n + 1)))) +
          (K * (n + 1)) *
            (Q * Real.exp (-(phaseFactor Q * meshFactor K * U) ^ 2 /
              (2 * (n + 1)))) := by
      gcongr
    _ = 2 * (K * (n + 1) : ℕ) * Q *
        Real.exp (-(phaseFactor Q * meshFactor K * U) ^ 2 / (2 * (n + 1))) := by
      push_cast
      ring

lemma phaseFactor_ten_ge_half : (1 / 2 : ℝ) ≤ phaseFactor 10 := by
  unfold phaseFactor
  push_cast
  have hpi0 := Real.pi_pos.le
  have hpi4 := (Real.pi_lt_four).le
  have hpisq : Real.pi ^ 2 ≤ 16 := by nlinarith [sq_nonneg (4 - Real.pi)]
  nlinarith

lemma meshFactor_hundred_ge_half : (1 / 2 : ℝ) ≤ meshFactor 100 := by
  unfold meshFactor
  push_cast
  have hpi := (Real.pi_lt_four).le
  nlinarith

lemma measureReal_maximum_ge_le_simple (n : ℕ) {U : ℝ} (hU : 0 < U) :
    signMeasure.real {ω | U ≤ maximumModulus ω n} ≤
      2000 * (n + 1) * Real.exp (-U ^ 2 / (32 * (n + 1))) := by
  have hphase0 : 0 < phaseFactor 10 := (by norm_num : (0 : ℝ) < 1 / 2).trans_le
    phaseFactor_ten_ge_half
  have hmesh0 : 0 < meshFactor 100 := (by norm_num : (0 : ℝ) < 1 / 2).trans_le
    meshFactor_hundred_ge_half
  have hraw := measureReal_maximum_ge_le_crude n 100 10 (by omega) (by omega)
    hphase0 hmesh0 hU
  have hprod : (1 / 4 : ℝ) ≤ phaseFactor 10 * meshFactor 100 := by
    nlinarith [mul_le_mul phaseFactor_ten_ge_half meshFactor_hundred_ge_half
      (by norm_num : (0 : ℝ) ≤ 1 / 2) hphase0.le]
  have hN : (0 : ℝ) < n + 1 := by positivity
  have hsquare : U ^ 2 / 16 ≤ (phaseFactor 10 * meshFactor 100 * U) ^ 2 := by
    have hU0 := hU.le
    nlinarith [mul_le_mul_of_nonneg_right hprod hU0,
      sq_nonneg (phaseFactor 10 * meshFactor 100 * U - U / 4)]
  have hexp :
      Real.exp (-(phaseFactor 10 * meshFactor 100 * U) ^ 2 / (2 * (n + 1))) ≤
        Real.exp (-U ^ 2 / (32 * (n + 1))) := by
    apply Real.exp_le_exp.mpr
    calc
      -(phaseFactor 10 * meshFactor 100 * U) ^ 2 / (2 * (n + 1)) ≤
          -(U ^ 2 / 16) / (2 * (n + 1)) := by
        exact div_le_div_of_nonneg_right (neg_le_neg hsquare) (by positivity)
      _ = -U ^ 2 / (32 * (n + 1)) := by
        field_simp
        <;> ring
  calc
    signMeasure.real {ω | U ≤ maximumModulus ω n} ≤
        2 * (100 * (n + 1) : ℕ) * 10 *
          Real.exp (-(phaseFactor 10 * meshFactor 100 * U) ^ 2 /
            (2 * (n + 1))) := hraw
    _ ≤ 2 * (100 * (n + 1) : ℕ) * 10 *
          Real.exp (-U ^ 2 / (32 * (n + 1))) := by
      exact mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = 2000 * (n + 1) * Real.exp (-U ^ 2 / (32 * (n + 1))) := by
      push_cast
      ring

lemma ae_eventually_notMem_of_summable_measureReal (s : ℕ → Set Sample)
    (hs : Summable fun j ↦ signMeasure.real (s j)) :
    ∀ᵐ ω ∂signMeasure, ∀ᶠ j : ℕ in atTop, ω ∉ s j := by
  apply ae_eventually_notMem
  have heq : (∑' j, signMeasure (s j)) =
      ∑' j, ENNReal.ofReal (signMeasure.real (s j)) := by
    apply tsum_congr
    intro j
    exact (ENNReal.ofReal_toReal (measure_ne_top signMeasure (s j))).symm
  rw [heq]
  exact hs.tsum_ofReal_ne_top

lemma summable_upperMaximumFailure_geometric {m L : ℕ} (hm : 1 ≤ m) (hL : 0 < L) :
    Summable fun j ↦ signMeasure.real (upperMaximumFailure m (geometricIndex L j)) := by
  let p : ℝ := 1 / (2 * (m : ℝ))
  have hp : 0 < p := by dsimp [p]; positivity
  have hmajor : Summable fun j ↦
      upperTailConstant m * (geometricIndex L j : ℝ) ^ (-p) :=
    (summable_geometricIndex_rpow hL hp).mul_left (upperTailConstant m)
  apply hmajor.of_norm_bounded_eventually_nat
  have hN : ∀ᶠ j : ℕ in atTop, 2 ≤ geometricIndex L j :=
    (tendsto_geometricIndex_atTop hL).eventually (eventually_ge_atTop 2)
  filter_upwards [hN] with j hj
  have hbound := measureReal_upperMaximumFailure_le hm hj
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  simpa only [p] using hbound

lemma summable_lowerMaximumFailure_geometric {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {L : ℕ} (hL : 0 < L) :
    Summable fun j ↦ signMeasure.real (lowerMaximumFailure δ (geometricIndex L j)) := by
  let p : ℝ := δ / 400
  have hp : 0 < p := by dsimp [p]; positivity
  have hmajor : Summable fun j ↦ 3 * (geometricIndex L j : ℝ) ^ (-p) :=
    (summable_geometricIndex_rpow hL hp).mul_left 3
  apply hmajor.of_norm_bounded_eventually_nat
  have hbound := (tendsto_geometricIndex_atTop hL).eventually
    (eventually_measureReal_lowerMaximumFailure_le hδ0 hδ1)
  filter_upwards [hbound] with j hj
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  simpa only [p] using hj

def blockMaximumFailure (a h : ℕ) (U : ℝ) : Set Sample :=
  ⋃ d ∈ Finset.range h, {ω | U ≤ maximumModulus (shiftSample a ω) d}

lemma mem_blockMaximumFailure_iff {a h : ℕ} {U : ℝ} {ω : Sample} :
    ω ∈ blockMaximumFailure a h U ↔
      ∃ d < h, U ≤ maximumModulus (shiftSample a ω) d := by
  simp [blockMaximumFailure]

lemma measureReal_shift_maximum_ge_eq (a n : ℕ) (U : ℝ) :
    signMeasure.real {ω | U ≤ maximumModulus (shiftSample a ω) n} =
      signMeasure.real {ω | U ≤ maximumModulus ω n} := by
  exact (hasLaw_shiftSample a).measureReal_eq
    (measurableSet_le measurable_const (measurable_maximumModulus n))

lemma measureReal_blockMaximumFailure_le {a h : ℕ} {U : ℝ}
    (hh : 0 < h) (hU : 0 < U) :
    signMeasure.real (blockMaximumFailure a h U) ≤
      2000 * h ^ 2 * Real.exp (-U ^ 2 / (32 * h)) := by
  let B : ℕ → Set Sample := fun d ↦
    {ω | U ≤ maximumModulus (shiftSample a ω) d}
  have hterm (d : ℕ) (hd : d ∈ Finset.range h) :
      signMeasure.real (B d) ≤
        2000 * h * Real.exp (-U ^ 2 / (32 * h)) := by
    have hdmem : d < h := Finset.mem_range.mp hd
    have hdlt : d + 1 ≤ h := by omega
    have hraw := measureReal_maximum_ge_le_simple d hU
    rw [← measureReal_shift_maximum_ge_eq a d U] at hraw
    have hden0 : (0 : ℝ) < 32 * (d + 1) := by positivity
    have hden : (32 : ℝ) * (d + 1) ≤ 32 * h := by exact_mod_cast (Nat.mul_le_mul_left 32 hdlt)
    have hinv : (32 * (h : ℝ))⁻¹ ≤ (32 * (d + 1 : ℝ))⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hden0 hden
    have hexparg : -U ^ 2 / (32 * (d + 1)) ≤ -U ^ 2 / (32 * h) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonpos_left hinv (neg_nonpos.mpr (sq_nonneg U))
    have hexp : Real.exp (-U ^ 2 / (32 * (d + 1))) ≤
        Real.exp (-U ^ 2 / (32 * h)) := Real.exp_le_exp.mpr hexparg
    calc
      signMeasure.real (B d) ≤
          2000 * (d + 1) * Real.exp (-U ^ 2 / (32 * (d + 1))) := by
        simpa only [B] using hraw
      _ ≤ 2000 * h * Real.exp (-U ^ 2 / (32 * h)) := by
        have hdh : (d : ℝ) + 1 ≤ h := by exact_mod_cast hdlt
        have hcoef : (2000 : ℝ) * (d + 1) ≤ 2000 * h := by nlinarith
        calc
          2000 * (d + 1) * Real.exp (-U ^ 2 / (32 * (d + 1))) ≤
              2000 * h * Real.exp (-U ^ 2 / (32 * (d + 1))) :=
            mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le
          _ ≤ 2000 * h * Real.exp (-U ^ 2 / (32 * h)) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
  calc
    signMeasure.real (blockMaximumFailure a h U) =
        signMeasure.real (⋃ d ∈ Finset.range h, B d) := by rfl
    _ ≤ ∑ d ∈ Finset.range h, signMeasure.real (B d) :=
      measureReal_biUnion_finset_le (Finset.range h) B
    _ ≤ ∑ _d ∈ Finset.range h,
        2000 * h * Real.exp (-U ^ 2 / (32 * h)) := Finset.sum_le_sum hterm
    _ = 2000 * h ^ 2 * Real.exp (-U ^ 2 / (32 * h)) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring

def blockLevel (N h : ℕ) : ℝ :=
  Real.sqrt (128 * (h : ℝ) * Real.log N)

lemma blockLevel_pos {N h : ℕ} (hN : 2 ≤ N) (hh : 0 < h) :
    0 < blockLevel N h := by
  unfold blockLevel
  apply Real.sqrt_pos.2
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  positivity

lemma measureReal_blockMaximumFailure_blockLevel_le {a N h : ℕ}
    (hN : 2 ≤ N) (hh : 0 < h) :
    signMeasure.real (blockMaximumFailure a h (blockLevel N h)) ≤
      2000 * h ^ 2 * (N : ℝ) ^ (-4 : ℝ) := by
  have hraw := measureReal_blockMaximumFailure_le (a := a) hh (blockLevel_pos hN hh)
  have hNreal : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hN)
  have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hsq : blockLevel N h ^ 2 = 128 * (h : ℝ) * Real.log N := by
    unfold blockLevel
    rw [Real.sq_sqrt]
    positivity
  have harg : -blockLevel N h ^ 2 / (32 * h) = -4 * Real.log N := by
    rw [hsq]
    have hhreal : (0 : ℝ) < h := by exact_mod_cast hh
    field_simp
    ring
  have hexp : Real.exp (-4 * Real.log (N : ℝ)) = (N : ℝ) ^ (-4 : ℝ) := by
    rw [Real.rpow_def_of_pos hNreal]
    congr 1
    ring
  rw [harg, hexp] at hraw
  exact hraw

def interpolationScale (m : ℕ) : ℕ := 256 * m ^ 2

def geometricBlockLength (L j : ℕ) : ℕ := geometricIndex L j / L + 1

lemma geometricIndex_succ_eq_add_blockLength (L j : ℕ) :
    geometricIndex L (j + 1) = geometricIndex L j + geometricBlockLength L j := by
  simp [geometricBlockLength, geometricIndex_succ, Nat.add_assoc]

lemma geometricBlockLength_pos (L j : ℕ) : 0 < geometricBlockLength L j := by
  unfold geometricBlockLength
  exact Nat.zero_lt_succ _

lemma geometricBlockLength_le_index {L j : ℕ} (hL : 2 ≤ L)
    (hN : 2 ≤ geometricIndex L j) :
    geometricBlockLength L j ≤ geometricIndex L j := by
  let N := geometricIndex L j
  have hdiv : N / L < N := Nat.div_lt_self (by omega) (by omega)
  unfold geometricBlockLength
  change N / L + 1 ≤ N
  omega

lemma interpolationScale_ge_two {m : ℕ} (hm : 1 ≤ m) : 2 ≤ interpolationScale m := by
  unfold interpolationScale
  nlinarith [sq_nonneg (m : ℤ)]

lemma natCast_sq_mul_rpow_neg_four {N : ℕ} (hN : 0 < N) :
    (N : ℝ) ^ 2 * (N : ℝ) ^ (-4 : ℝ) = (N : ℝ) ^ (-2 : ℝ) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_add hNreal]
  norm_num

lemma summable_blockMaximumFailure_geometric {m : ℕ} (hm : 1 ≤ m) :
    let L := interpolationScale m
    Summable fun j ↦
      signMeasure.real
        (blockMaximumFailure (geometricIndex L j) (geometricBlockLength L j)
          (blockLevel (geometricIndex L j) (geometricBlockLength L j))) := by
  dsimp only
  let L := interpolationScale m
  have hL : 0 < L := lt_of_lt_of_le (by omega) (interpolationScale_ge_two hm)
  have hL2 : 2 ≤ L := interpolationScale_ge_two hm
  have hmajor : Summable fun j ↦ 2000 * (geometricIndex L j : ℝ) ^ (-2 : ℝ) :=
    (summable_geometricIndex_rpow hL (by norm_num : (0 : ℝ) < 2)).mul_left 2000
  apply hmajor.of_norm_bounded_eventually_nat
  have hNevent : ∀ᶠ j : ℕ in atTop, 2 ≤ geometricIndex L j :=
    (tendsto_geometricIndex_atTop hL).eventually (eventually_ge_atTop 2)
  filter_upwards [hNevent] with j hN
  let N := geometricIndex L j
  let h := geometricBlockLength L j
  have hh : 0 < h := geometricBlockLength_pos L j
  have hhN : h ≤ N := geometricBlockLength_le_index hL2 hN
  have hbound := measureReal_blockMaximumFailure_blockLevel_le
    (a := N) hN hh
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  calc
    signMeasure.real (blockMaximumFailure N h (blockLevel N h)) ≤
        2000 * h ^ 2 * (N : ℝ) ^ (-4 : ℝ) := hbound
    _ ≤ 2000 * N ^ 2 * (N : ℝ) ^ (-4 : ℝ) := by
      have hhNreal : (h : ℝ) ≤ N := by exact_mod_cast hhN
      have hsq : (h : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by nlinarith
      gcongr
    _ = 2000 * (N : ℝ) ^ (-2 : ℝ) := by
      rw [mul_assoc, natCast_sq_mul_rpow_neg_four (by omega)]

/-! Deterministic interpolation between two neighboring subsequence indices. -/

lemma randomPolynomial_add_shifted_block (ω : Sample) {N : ℕ} (hN : 0 < N)
    (d : ℕ) (z : ℂ) :
    randomPolynomial ω (N + d) z =
      randomPolynomial ω (N - 1) z + z ^ N * randomPolynomial (shiftSample N ω) d z := by
  unfold randomPolynomial shiftSample
  rw [show N + d + 1 = N + (d + 1) by omega, Finset.sum_range_add]
  have hNm : N - 1 + 1 = N := by omega
  rw [hNm]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [pow_add]
  push_cast
  ring

lemma norm_randomPolynomial_add_shifted_block_sub (ω : Sample) {N : ℕ} (hN : 0 < N)
    (d : ℕ) (z : Circle) :
    ‖randomPolynomial ω (N + d) (z : ℂ) - randomPolynomial ω (N - 1) (z : ℂ)‖ =
      ‖randomPolynomial (shiftSample N ω) d (z : ℂ)‖ := by
  rw [randomPolynomial_add_shifted_block ω hN]
  rw [add_sub_cancel_left, norm_mul, norm_pow, Circle.norm_coe, one_pow, one_mul]

lemma abs_maximumModulus_add_shifted_block_sub_le (ω : Sample) {N : ℕ} (hN : 0 < N)
    (d : ℕ) :
    |maximumModulus ω (N + d) - maximumModulus ω (N - 1)| ≤
      maximumModulus (shiftSample N ω) d := by
  obtain ⟨z, hz⟩ := exists_maximumModulus ω (N + d)
  obtain ⟨w, hw⟩ := exists_maximumModulus ω (N - 1)
  rw [abs_le]
  constructor
  · have hdiff : maximumModulus ω (N - 1) - maximumModulus ω (N + d) ≤
        maximumModulus (shiftSample N ω) d := by
      rw [← hw]
      calc
        ‖randomPolynomial ω (N - 1) (w : ℂ)‖ - maximumModulus ω (N + d) ≤
            ‖randomPolynomial ω (N - 1) (w : ℂ)‖ -
              ‖randomPolynomial ω (N + d) (w : ℂ)‖ := by
          gcongr
          exact norm_randomPolynomial_le_maximumModulus ω (N + d) w
        _ ≤ ‖randomPolynomial ω (N - 1) (w : ℂ) -
              randomPolynomial ω (N + d) (w : ℂ)‖ := norm_sub_norm_le _ _
        _ = ‖randomPolynomial ω (N + d) (w : ℂ) -
              randomPolynomial ω (N - 1) (w : ℂ)‖ := norm_sub_rev _ _
        _ = ‖randomPolynomial (shiftSample N ω) d (w : ℂ)‖ :=
          norm_randomPolynomial_add_shifted_block_sub ω hN d w
        _ ≤ maximumModulus (shiftSample N ω) d :=
          norm_randomPolynomial_le_maximumModulus _ _ _
    linarith
  · rw [← hz]
    calc
      ‖randomPolynomial ω (N + d) (z : ℂ)‖ - maximumModulus ω (N - 1) ≤
          ‖randomPolynomial ω (N + d) (z : ℂ)‖ -
            ‖randomPolynomial ω (N - 1) (z : ℂ)‖ := by
        gcongr
        exact norm_randomPolynomial_le_maximumModulus ω (N - 1) z
      _ ≤ ‖randomPolynomial ω (N + d) (z : ℂ) -
            randomPolynomial ω (N - 1) (z : ℂ)‖ := norm_sub_norm_le _ _
      _ = ‖randomPolynomial (shiftSample N ω) d (z : ℂ)‖ :=
        norm_randomPolynomial_add_shifted_block_sub ω hN d z
      _ ≤ maximumModulus (shiftSample N ω) d :=
        norm_randomPolynomial_le_maximumModulus _ _ _

lemma abs_maximumModulus_sub_endpoint_le_of_not_blockFailure
    (ω : Sample) {N h : ℕ} {U : ℝ} (hN : 1 ≤ N) (hh : 0 < h)
    {n : ℕ} (hnlo : N ≤ n + 1) (hnhi : n + 1 ≤ N + h)
    (hgood : ω ∉ blockMaximumFailure N h U) :
    |maximumModulus ω n - maximumModulus ω (N - 1)| ≤ U := by
  by_cases heq : n + 1 = N
  · have hn : n = N - 1 := by omega
    rw [hn, sub_self, abs_zero]
    by_contra hU
    have hUneg : U < 0 := lt_of_not_ge hU
    apply hgood
    rw [mem_blockMaximumFailure_iff]
    exact ⟨0, hh, hUneg.le.trans (maximumModulus_nonneg _ _)⟩
  · have hNn : N ≤ n := by omega
    let d := n - N
    have hn : N + d = n := Nat.add_sub_of_le hNn
    have hd : d < h := by
      dsimp [d]
      omega
    have hnot : ¬ U ≤ maximumModulus (shiftSample N ω) d := by
      intro hbad
      apply hgood
      rw [mem_blockMaximumFailure_iff]
      exact ⟨d, hd, hbad⟩
    calc
      |maximumModulus ω n - maximumModulus ω (N - 1)| =
          |maximumModulus ω (N + d) - maximumModulus ω (N - 1)| := by rw [hn]
      _ ≤ maximumModulus (shiftSample N ω) d :=
        abs_maximumModulus_add_shifted_block_sub_le ω (by omega) d
      _ ≤ U := le_of_not_ge hnot

lemma exists_geometricIndex_bracket (L : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    ∃ j : ℕ, geometricIndex L j ≤ N ∧ N < geometricIndex L (j + 1) := by
  let P : ℕ → Prop := fun j ↦ geometricIndex L j ≤ N
  let j := Nat.findGreatest P N
  have hP0 : P 0 := by simpa [P] using hN
  have hjP : P j := Nat.findGreatest_spec (P := P) (Nat.zero_le N) hP0
  refine ⟨j, hjP, ?_⟩
  by_contra hnot
  have hnext : P (j + 1) := by
    dsimp [P]
    exact le_of_not_gt hnot
  have hjnextN : j + 1 ≤ N := by
    exact (StrictMono.id_le (geometricIndex_strictMono L) (j + 1)).trans hnext
  exact (Nat.findGreatest_is_greatest (P := P) (Nat.lt_succ_self j) hjnextN) hnext

lemma bracket_index_ge {L J j N : ℕ}
    (hbracket : geometricIndex L j ≤ N ∧ N < geometricIndex L (j + 1))
    (hJN : geometricIndex L J ≤ N) : J ≤ j := by
  by_contra hnot
  have hjJ : j + 1 ≤ J := by omega
  have hmono : geometricIndex L (j + 1) ≤ geometricIndex L J :=
    (geometricIndex_strictMono L).monotone hjJ
  omega

def asymptoticScale (N : ℕ) : ℝ :=
  Real.sqrt ((N : ℝ) * Real.log N)

lemma asymptoticScale_pos {N : ℕ} (hN : 2 ≤ N) : 0 < asymptoticScale N := by
  unfold asymptoticScale
  apply Real.sqrt_pos.2
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  positivity

lemma asymptoticScale_mono {N X : ℕ} (hN : 1 ≤ N) (hNX : N ≤ X) :
    asymptoticScale N ≤ asymptoticScale X := by
  unfold asymptoticScale
  apply Real.sqrt_le_sqrt
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hlog : Real.log (N : ℝ) ≤ Real.log (X : ℝ) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast hNX
  have hcast : (N : ℝ) ≤ X := by exact_mod_cast hNX
  exact mul_le_mul hcast hlog hlogN (by positivity)

lemma geometricBlockLength_mul_scale_le_two_index {L j : ℕ} (hL : 0 < L)
    (hNL : L ≤ geometricIndex L j) :
    geometricBlockLength L j * L ≤ 2 * geometricIndex L j := by
  let N := geometricIndex L j
  have hone : 1 ≤ N / L := by
    exact (Nat.le_div_iff_mul_le hL).2 (by simpa using hNL)
  have hlength : geometricBlockLength L j ≤ 2 * (N / L) := by
    unfold geometricBlockLength
    change N / L + 1 ≤ 2 * (N / L)
    omega
  calc
    geometricBlockLength L j * L ≤ (2 * (N / L)) * L :=
      Nat.mul_le_mul_right L hlength
    _ = 2 * ((N / L) * L) := by ring
    _ ≤ 2 * N := Nat.mul_le_mul_left 2 (Nat.div_mul_le_self N L)

lemma blockLevel_le_one_div_mul_asymptoticScale {m N h : ℕ} (hm : 1 ≤ m)
    (hN : 2 ≤ N) (hscale : h * interpolationScale m ≤ 2 * N) :
    blockLevel N h ≤ (1 / (m : ℝ)) * asymptoticScale N := by
  have hmreal : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hm)
  have hlog0 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hscaleReal : (h : ℝ) * (256 * (m : ℝ) ^ 2) ≤ 2 * N := by
    exact_mod_cast hscale
  have hcoef : 128 * (h : ℝ) * (m : ℝ) ^ 2 ≤ N := by nlinarith
  have hblock0 : 0 ≤ blockLevel N h := Real.sqrt_nonneg _
  have hA0 : 0 ≤ asymptoticScale N := Real.sqrt_nonneg _
  have hsquare : ((m : ℝ) * blockLevel N h) ^ 2 ≤ asymptoticScale N ^ 2 := by
    have hblockSq : blockLevel N h ^ 2 = 128 * (h : ℝ) * Real.log N := by
      unfold blockLevel
      rw [Real.sq_sqrt]
      positivity
    have hASq : asymptoticScale N ^ 2 = (N : ℝ) * Real.log N := by
      unfold asymptoticScale
      rw [Real.sq_sqrt]
      positivity
    rw [mul_pow, hblockSq, hASq]
    nlinarith [mul_le_mul_of_nonneg_right hcoef hlog0]
  have hmul : (m : ℝ) * blockLevel N h ≤ asymptoticScale N :=
    (sq_le_sq₀ (mul_nonneg hmreal.le hblock0) hA0).mp hsquare
  calc
    blockLevel N h ≤ asymptoticScale N / (m : ℝ) :=
      (le_div_iff₀ hmreal).2 (by simpa [mul_comm] using hmul)
    _ = (1 / (m : ℝ)) * asymptoticScale N := by ring

lemma asymptoticScale_le_one_add_inv_mul_of_close {m N h X : ℕ} (hm : 1 ≤ m)
    (hN : 3 ≤ N) (hNX : N ≤ X) (hX : X ≤ N + h)
    (hscale : h * interpolationScale m ≤ 2 * N) :
    asymptoticScale X ≤ (1 + 1 / (m : ℝ)) * asymptoticScale N := by
  let c : ℝ := 1 + 1 / (m : ℝ)
  have hmreal : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hm)
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hNreal : (0 : ℝ) < N := by positivity
  have hXreal : (0 : ℝ) < X := hNreal.trans_le (by exact_mod_cast hNX)
  have hscaleReal : (h : ℝ) * (256 * (m : ℝ) ^ 2) ≤ 2 * N := by
    exact_mod_cast hscale
  have hhm : (h : ℝ) * m ≤ N := by
    have haux : 0 ≤ (h : ℝ) * m * (m - 1) := by positivity
    nlinarith
  have hhdiv : (h : ℝ) ≤ (N : ℝ) / m := (le_div_iff₀ hmreal).2 hhm
  have hXcast : (X : ℝ) ≤ N + h := by exact_mod_cast hX
  have hXbound : (X : ℝ) ≤ c * N := by
    dsimp [c]
    calc
      (X : ℝ) ≤ N + h := hXcast
      _ ≤ N + N / (m : ℝ) := by linarith
      _ = (1 + 1 / (m : ℝ)) * N := by ring
  have hratioPos : 0 < (X : ℝ) / N := div_pos hXreal hNreal
  have hratio : (X : ℝ) / N - 1 ≤ 1 / (m : ℝ) := by
    apply (sub_le_iff_le_add).2
    apply (div_le_iff₀ hNreal).2
    simpa only [c, add_comm] using hXbound
  have hlogN1 : (1 : ℝ) ≤ Real.log N := by
    apply (Real.le_log_iff_exp_le hNreal).2
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hN)
  have hlogX : Real.log (X : ℝ) ≤ c * Real.log N := by
    have hinc : Real.log ((X : ℝ) / N) ≤ 1 / (m : ℝ) :=
      (Real.log_le_sub_one_of_pos hratioPos).trans hratio
    have hid : Real.log (X : ℝ) = Real.log N + Real.log ((X : ℝ) / N) := by
      rw [Real.log_div hXreal.ne' hNreal.ne']
      ring
    rw [hid]
    dsimp [c]
    have hinv0 : 0 ≤ 1 / (m : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hlogN1 hinv0]
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := by linarith
  have hlogX0 : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hprod : (X : ℝ) * Real.log X ≤ c ^ 2 * ((N : ℝ) * Real.log N) := by
    calc
      (X : ℝ) * Real.log X ≤ (c * N) * (c * Real.log N) :=
        mul_le_mul hXbound hlogX hlogX0 (mul_nonneg hc0 (Nat.cast_nonneg _))
      _ = c ^ 2 * ((N : ℝ) * Real.log N) := by ring
  have hsquare : asymptoticScale X ^ 2 ≤ (c * asymptoticScale N) ^ 2 := by
    have hXSq : asymptoticScale X ^ 2 = (X : ℝ) * Real.log X := by
      unfold asymptoticScale
      rw [Real.sq_sqrt]
      exact mul_nonneg (Nat.cast_nonneg _) hlogX0
    have hNSq : asymptoticScale N ^ 2 = (N : ℝ) * Real.log N := by
      unfold asymptoticScale
      rw [Real.sq_sqrt]
      exact mul_nonneg (Nat.cast_nonneg _) hlogN0
    rw [mul_pow, hXSq, hNSq]
    exact hprod
  exact (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hc0 (Real.sqrt_nonneg _))).mp hsquare

lemma ae_eventually_maximum_between_parameter_bounds (m : ℕ) (hm : 4 ≤ m) :
    ∀ᵐ ω ∂signMeasure, ∀ᶠ X : ℕ in atTop,
      (1 - 4 / (m : ℝ)) * asymptoticScale X ≤ maximumModulus ω (X - 1) ∧
        maximumModulus ω (X - 1) ≤ (1 + 2 / (m : ℝ)) * asymptoticScale X := by
  let L := interpolationScale m
  have hm1 : 1 ≤ m := by omega
  have hL : 0 < L := lt_of_lt_of_le (by omega) (interpolationScale_ge_two hm1)
  have hδ0 : (0 : ℝ) < 1 / (m : ℝ) := by positivity
  have hδ1 : (1 / (m : ℝ)) ≤ 1 := by
    exact (div_le_one (by positivity)).2 (by exact_mod_cast hm1)
  have hUpperAE := ae_eventually_notMem_of_summable_measureReal
    (fun j ↦ upperMaximumFailure m (geometricIndex L j))
    (summable_upperMaximumFailure_geometric hm1 hL)
  have hLowerAE := ae_eventually_notMem_of_summable_measureReal
    (fun j ↦ lowerMaximumFailure (1 / (m : ℝ)) (geometricIndex L j))
    (summable_lowerMaximumFailure_geometric hδ0 hδ1 hL)
  have hBlockAE := ae_eventually_notMem_of_summable_measureReal
    (fun j ↦ blockMaximumFailure (geometricIndex L j) (geometricBlockLength L j)
      (blockLevel (geometricIndex L j) (geometricBlockLength L j)))
    (by simpa only [L] using summable_blockMaximumFailure_geometric hm1)
  filter_upwards [hUpperAE, hLowerAE, hBlockAE] with ω hUpper hLower hBlock
  have hLarge : ∀ᶠ j : ℕ in atTop, L ≤ geometricIndex L j ∧ 3 ≤ geometricIndex L j := by
    filter_upwards [
      (tendsto_geometricIndex_atTop hL).eventually (eventually_ge_atTop L),
      (tendsto_geometricIndex_atTop hL).eventually (eventually_ge_atTop 3)] with j hjL hj3
    exact ⟨hjL, hj3⟩
  have hGood : ∀ᶠ j : ℕ in atTop,
      ω ∉ upperMaximumFailure m (geometricIndex L j) ∧
      ω ∉ lowerMaximumFailure (1 / (m : ℝ)) (geometricIndex L j) ∧
      ω ∉ blockMaximumFailure (geometricIndex L j) (geometricBlockLength L j)
        (blockLevel (geometricIndex L j) (geometricBlockLength L j)) ∧
      L ≤ geometricIndex L j ∧ 3 ≤ geometricIndex L j := by
    filter_upwards [hUpper, hLower, hBlock, hLarge] with j hu hl hb hlarge
    exact ⟨hu, hl, hb, hlarge⟩
  rw [eventually_atTop] at hGood ⊢
  obtain ⟨J, hJ⟩ := hGood
  refine ⟨geometricIndex L J, fun X hX ↦ ?_⟩
  have hX1 : 1 ≤ X := (geometricIndex_pos L J).trans_le hX
  obtain ⟨j, hNjX, hXnext⟩ := exists_geometricIndex_bracket L hX1
  have hJj : J ≤ j := bracket_index_ge ⟨hNjX, hXnext⟩ hX
  obtain ⟨hUpperGood, hLowerGood, hBlockGood, hLN, hN3⟩ := hJ j hJj
  let N := geometricIndex L j
  let h := geometricBlockLength L j
  have hh : 0 < h := geometricBlockLength_pos L j
  have hN1 : 1 ≤ N := by omega
  have hNX : N ≤ X := hNjX
  have hXNh : X ≤ N + h := by
    rw [← geometricIndex_succ_eq_add_blockLength L j]
    omega
  have hscale : h * interpolationScale m ≤ 2 * N := by
    simpa only [L, N, h] using geometricBlockLength_mul_scale_le_two_index hL hLN
  have hclose :
      |maximumModulus ω (X - 1) - maximumModulus ω (N - 1)| ≤ blockLevel N h := by
    apply abs_maximumModulus_sub_endpoint_le_of_not_blockFailure ω hN1 hh
    · simpa [Nat.sub_add_cancel hX1] using hNX
    · simpa [Nat.sub_add_cancel hX1] using hXNh
    · simpa only [N, h] using hBlockGood
  have hblock : blockLevel N h ≤ (1 / (m : ℝ)) * asymptoticScale N :=
    blockLevel_le_one_div_mul_asymptoticScale hm1 (by omega) hscale
  have hANX : asymptoticScale N ≤ asymptoticScale X :=
    asymptoticScale_mono hN1 hNX
  have hAXN : asymptoticScale X ≤
      (1 + 1 / (m : ℝ)) * asymptoticScale N :=
    asymptoticScale_le_one_add_inv_mul_of_close hm1 hN3 hNX hXNh hscale
  have hUpperEndpoint : maximumModulus ω (N - 1) ≤
      (1 + 1 / (m : ℝ)) * asymptoticScale N := by
    have hnot : ¬ upperMaximumLevel m N ≤ maximumModulus ω (N - 1) := hUpperGood
    have hlt := lt_of_not_ge hnot
    simpa only [upperMaximumLevel, asymptoticScale] using hlt.le
  have hLowerEndpoint :
      (1 - 1 / (m : ℝ)) * asymptoticScale N ≤ maximumModulus ω (N - 1) := by
    have hnot : ¬ maximumModulus ω (N - 1) ≤
        lowerMaximumLevel (1 / (m : ℝ)) N := hLowerGood
    have hlt := lt_of_not_ge hnot
    simpa only [lowerMaximumLevel, asymptoticScale] using hlt.le
  have hdiff := (abs_le.mp hclose)
  have hUpperX : maximumModulus ω (X - 1) ≤
      (1 + 2 / (m : ℝ)) * asymptoticScale N := by
    calc
      maximumModulus ω (X - 1) ≤ maximumModulus ω (N - 1) + blockLevel N h := by
        linarith [hdiff.2]
      _ ≤ (1 + 1 / (m : ℝ)) * asymptoticScale N +
          (1 / (m : ℝ)) * asymptoticScale N := add_le_add hUpperEndpoint hblock
      _ = (1 + 2 / (m : ℝ)) * asymptoticScale N := by ring
  have hLowerX : (1 - 2 / (m : ℝ)) * asymptoticScale N ≤
      maximumModulus ω (X - 1) := by
    calc
      (1 - 2 / (m : ℝ)) * asymptoticScale N =
          (1 - 1 / (m : ℝ)) * asymptoticScale N -
            (1 / (m : ℝ)) * asymptoticScale N := by ring
      _ ≤ maximumModulus ω (N - 1) - blockLevel N h :=
        sub_le_sub hLowerEndpoint hblock
      _ ≤ maximumModulus ω (X - 1) := by linarith [hdiff.1]
  have hmreal : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hLowerCoeff : (0 : ℝ) ≤ 1 - 4 / (m : ℝ) := by
    apply sub_nonneg.mpr
    exact (div_le_one (by positivity)).2 hmreal
  have hCoeff :
      (1 - 4 / (m : ℝ)) * (1 + 1 / (m : ℝ)) ≤ 1 - 2 / (m : ℝ) := by
    have hmpos : (0 : ℝ) < m := by positivity
    field_simp
    nlinarith
  constructor
  · calc
      (1 - 4 / (m : ℝ)) * asymptoticScale X ≤
          (1 - 4 / (m : ℝ)) *
            ((1 + 1 / (m : ℝ)) * asymptoticScale N) :=
        mul_le_mul_of_nonneg_left hAXN hLowerCoeff
      _ = ((1 - 4 / (m : ℝ)) * (1 + 1 / (m : ℝ))) * asymptoticScale N := by ring
      _ ≤ (1 - 2 / (m : ℝ)) * asymptoticScale N :=
        mul_le_mul_of_nonneg_right hCoeff (Real.sqrt_nonneg _)
      _ ≤ maximumModulus ω (X - 1) := hLowerX
  · exact hUpperX.trans (mul_le_mul_of_nonneg_left hANX (by positivity))

lemma ae_tendsto_sampleSize_normalized_maximum :
    ∀ᵐ ω ∂signMeasure,
      Tendsto
        (fun X : ℕ ↦ maximumModulus ω (X - 1) / asymptoticScale X)
        atTop (𝓝 1) := by
  have hAll : ∀ᵐ ω ∂signMeasure, ∀ n : ℕ, ∀ᶠ X : ℕ in atTop,
      (1 - 4 / ((n + 4 : ℕ) : ℝ)) * asymptoticScale X ≤
          maximumModulus ω (X - 1) ∧
        maximumModulus ω (X - 1) ≤
          (1 + 2 / ((n + 4 : ℕ) : ℝ)) * asymptoticScale X := by
    rw [ae_all_iff]
    intro n
    exact ae_eventually_maximum_between_parameter_bounds (n + 4) (by omega)
  filter_upwards [hAll] with ω hω
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨n : ℕ, hn⟩ := exists_nat_one_div_lt (by positivity : 0 < ε / 4)
  let m : ℕ := n + 4
  have hm : 4 ≤ m := by dsimp [m]; omega
  have hden : (n : ℝ) + 1 ≤ m := by exact_mod_cast (by dsimp [m]; omega)
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hinv : 1 / (m : ℝ) ≤ 1 / ((n : ℝ) + 1) :=
    one_div_le_one_div_of_le hnpos hden
  have hfour : 4 / (m : ℝ) < ε := by
    have hmul := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 4)
    have hn4 : 4 * (1 / ((n : ℝ) + 1)) < ε := by nlinarith
    simpa [div_eq_mul_inv] using hmul.trans_lt hn4
  have hbound := hω n
  apply eventually_atTop.1
  filter_upwards [hbound, eventually_ge_atTop 2] with X hX hX2
  have hApos : 0 < asymptoticScale X := asymptoticScale_pos hX2
  have hlower : 1 - 4 / (m : ℝ) ≤
      maximumModulus ω (X - 1) / asymptoticScale X := by
    apply (le_div_iff₀ hApos).2
    simpa only [m] using hX.1
  have hupper : maximumModulus ω (X - 1) / asymptoticScale X ≤
      1 + 2 / (m : ℝ) := by
    apply (div_le_iff₀ hApos).2
    simpa only [m] using hX.2
  rw [Real.dist_eq, abs_lt]
  have hinv0 : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
  constructor
  · calc
      -ε < -(4 / (m : ℝ)) := neg_lt_neg hfour
      _ ≤ maximumModulus ω (X - 1) / asymptoticScale X - 1 := by linarith
  · calc
      maximumModulus ω (X - 1) / asymptoticScale X - 1 ≤ 2 / (m : ℝ) := by
        linarith
      _ ≤ 4 / (m : ℝ) := by
        exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
      _ < ε := hfour

lemma tendsto_nat_succ_div_nat :
    Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) / n) atTop (𝓝 1) := by
  have hconst : Tendsto (fun _n : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h' : Tendsto (fun n : ℕ ↦ (1 : ℝ) + 1 / n) atTop (𝓝 1) := by
    simpa only [add_zero] using hconst.add
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply h'.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  field_simp
  norm_num [Nat.cast_add, Nat.cast_one, add_comm]

lemma tendsto_log_nat_succ_div_log_nat :
    Tendsto (fun n : ℕ ↦ Real.log ((n : ℝ) + 1) / Real.log (n : ℝ))
      atTop (𝓝 1) := by
  have hlogTop : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogInv : Tendsto (fun n : ℕ ↦ (Real.log (n : ℝ))⁻¹) atTop (𝓝 0) :=
    hlogTop.inv_tendsto_atTop
  have hzero := Real.tendsto_log_nat_add_one_sub_log.mul hlogInv
  have hconst : Tendsto (fun _n : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hone : Tendsto
      (fun n : ℕ ↦ (1 : ℝ) +
        (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) *
          (Real.log (n : ℝ))⁻¹) atTop (𝓝 1) := by
    simpa only [zero_mul, add_zero] using hconst.add hzero
  apply hone.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlog : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  field_simp
  ring

lemma tendsto_asymptoticScale_succ_div :
    Tendsto (fun n : ℕ ↦ asymptoticScale (n + 1) / asymptoticScale n)
      atTop (𝓝 1) := by
  have hprod := tendsto_nat_succ_div_nat.mul tendsto_log_nat_succ_div_log_nat
  have hsqrt : Tendsto
      (fun n : ℕ ↦ Real.sqrt
        ((((n + 1 : ℕ) : ℝ) / n) *
          (Real.log ((n : ℝ) + 1) / Real.log (n : ℝ))))
      atTop (𝓝 1) := by
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hprod
    change Tendsto
      (fun n : ℕ ↦ Real.sqrt
        ((((n + 1 : ℕ) : ℝ) / n) *
          (Real.log ((n : ℝ) + 1) / Real.log (n : ℝ))))
      atTop (𝓝 (Real.sqrt (1 * 1))) at hs
    simpa only [one_mul, Real.sqrt_one] using hs
  apply hsqrt.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hlogsucc : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n + 1))
  unfold asymptoticScale
  rw [← Real.sqrt_div (mul_nonneg (Nat.cast_nonneg _) hlogsucc)]
  congr 1
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp

/-- The exact almost-sure asymptotic assertion in Erdős Problem 523, on the canonical product
space of independent uniformly distributed signs. -/
def Erdos523Statement : Prop :=
  ∀ᵐ ω ∂signMeasure,
    Tendsto
      (fun n : ℕ ↦ maximumModulus ω n / Real.sqrt ((n : ℝ) * Real.log n))
      atTop (𝓝 1)

theorem erdos_523 :
    ∀ᵐ ω ∂signMeasure,
      Tendsto
        (fun n : ℕ ↦ maximumModulus ω n / Real.sqrt ((n : ℝ) * Real.log n))
        atTop (𝓝 1) := by
  change Erdos523Statement
  unfold Erdos523Statement
  filter_upwards [ae_tendsto_sampleSize_normalized_maximum] with ω hω
  have hshift := hω.comp (tendsto_add_atTop_nat 1)
  have hproduct := hshift.mul tendsto_asymptoticScale_succ_div
  have hproduct' : Tendsto
      (fun n : ℕ ↦
        ((fun X : ℕ ↦ maximumModulus ω (X - 1) / asymptoticScale X) (n + 1)) *
          (asymptoticScale (n + 1) / asymptoticScale n))
      atTop (𝓝 1) := by
    simpa only [Function.comp_apply, one_mul] using hproduct
  have hfinal : Tendsto
      (fun n : ℕ ↦ maximumModulus ω n / asymptoticScale n) atTop (𝓝 1) := by
    apply hproduct'.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hAn : asymptoticScale n ≠ 0 := (asymptoticScale_pos hn).ne'
    have hAsucc : asymptoticScale (n + 1) ≠ 0 :=
      (asymptoticScale_pos (by omega)).ne'
    simp only [Nat.add_sub_cancel]
    field_simp
  simpa only [asymptoticScale] using hfinal

#print axioms erdos_523

end

end Erdos523

alias _root_.Erdos523.erdos523 := _root_.Erdos523.erdos_523
