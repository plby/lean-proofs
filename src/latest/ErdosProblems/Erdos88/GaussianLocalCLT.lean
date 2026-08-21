import ErdosProblems.Erdos88.GaussianMoments
import ErdosProblems.Erdos88.LinearLCDCancellation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open scoped BigOperators FourierTransform RealInnerProductSpace
open scoped ComplexConjugate
open MeasureTheory ProbabilityTheory Real

namespace Erdos88
namespace GaussianQuadratic

lemma coordinateFirstMoment_eq_zero (a lam : ℝ) :
    ∫ x : ℝ, centeredCoordinatePolynomial a lam x ∂standardGaussian = 0 := by
  let f2 : ℝ → ℝ := fun x ↦ lam * x ^ 2
  let f1 : ℝ → ℝ := fun x ↦ a * x
  let f0 : ℝ → ℝ := fun _ ↦ -lam
  have h2 : Integrable f2 standardGaussian :=
    (Invariance.integrable_pow_standardGaussian 2).const_mul lam
  have h1 : Integrable f1 standardGaussian :=
    by simpa only [f1, pow_one] using
      (Invariance.integrable_pow_standardGaussian 1).const_mul a
  have h0 : Integrable f0 standardGaussian := integrable_const _
  have hexpand : centeredCoordinatePolynomial a lam = fun x ↦ f2 x + (f1 x + f0 x) := by
    funext x
    simp only [centeredCoordinatePolynomial, f2, f1, f0]
    ring
  rw [hexpand]
  have hadd1 :
      (∫ x : ℝ, f2 x + (f1 x + f0 x) ∂standardGaussian) =
        (∫ x : ℝ, f2 x ∂standardGaussian) +
          ∫ x : ℝ, f1 x + f0 x ∂standardGaussian :=
    integral_add h2 (h1.add h0)
  have hadd2 :
      (∫ x : ℝ, f1 x + f0 x ∂standardGaussian) =
        (∫ x : ℝ, f1 x ∂standardGaussian) +
          ∫ x : ℝ, f0 x ∂standardGaussian := integral_add h1 h0
  have hmean1 : ∫ x : ℝ, f1 x ∂standardGaussian = 0 := by
    change ∫ x : ℝ, a * x ∂standardGaussian = 0
    rw [show (fun x : ℝ ↦ a * x) = fun x ↦ a * x ^ 1 by
      funext x
      rw [pow_one]]
    rw [integral_const_mul, Invariance.standardGaussian_moment_one, mul_zero]
  rw [hadd1, hadd2]
  simp only [f2, f1, f0, integral_const_mul, integral_const,
    Invariance.standardGaussian_moment_two, hmean1]
  simp

lemma centeredCoordinatePolynomial_integrable (a lam : ℝ) :
    Integrable (centeredCoordinatePolynomial a lam) standardGaussian := by
  let X : ℝ → ℝ := centeredCoordinatePolynomial a lam
  have hXm : AEStronglyMeasurable X standardGaussian :=
    (continuous_centeredCoordinatePolynomial a lam).aestronglyMeasurable
  have hX4 : Integrable (fun x ↦ X x ^ 4) standardGaussian :=
    centeredCoordinatePolynomial_fourth_integrable a lam
  have hX1 := Erdos1028.integrable_pow_of_integrable_pow_four hXm hX4 1 (by norm_num)
  simpa only [pow_one, X] using hX1

lemma centeredCoordinatePolynomial_sq_integrable (a lam : ℝ) :
    Integrable (fun x ↦ centeredCoordinatePolynomial a lam x ^ 2)
      standardGaussian := by
  let X : ℝ → ℝ := centeredCoordinatePolynomial a lam
  have hXm : AEStronglyMeasurable X standardGaussian :=
    (continuous_centeredCoordinatePolynomial a lam).aestronglyMeasurable
  have hX4 : Integrable (fun x ↦ X x ^ 4) standardGaussian :=
    centeredCoordinatePolynomial_fourth_integrable a lam
  simpa only [X] using
    Erdos1028.integrable_pow_of_integrable_pow_four hXm hX4 2 (by norm_num)

lemma centeredCoordinatePolynomial_abs_cube_integrable (a lam : ℝ) :
    Integrable (fun x ↦ |centeredCoordinatePolynomial a lam x| ^ 3)
      standardGaussian := by
  let X : ℝ → ℝ := centeredCoordinatePolynomial a lam
  have hXm : AEStronglyMeasurable X standardGaussian :=
    (continuous_centeredCoordinatePolynomial a lam).aestronglyMeasurable
  have hX4 : Integrable (fun x ↦ X x ^ 4) standardGaussian :=
    centeredCoordinatePolynomial_fourth_integrable a lam
  have hX3 : Integrable (fun x ↦ X x ^ 3) standardGaussian :=
    Erdos1028.integrable_pow_of_integrable_pow_four hXm hX4 3 (by norm_num)
  simpa only [X, Real.norm_eq_abs, abs_pow] using hX3.norm

lemma centeredCoordinate_cexp_integrable (a lam t : ℝ) :
    Integrable (fun x : ℝ ↦
      Complex.exp ((((t * centeredCoordinatePolynomial a lam x : ℝ) : ℂ) *
        Complex.I))) standardGaussian := by
  apply (integrable_const (1 : ℝ)).mono'
  · have hreal : Continuous (fun x : ℝ ↦
        t * centeredCoordinatePolynomial a lam x) :=
      continuous_const.mul (continuous_centeredCoordinatePolynomial a lam)
    have hcomplex : Continuous (fun x : ℝ ↦
        ((t * centeredCoordinatePolynomial a lam x : ℝ) : ℂ)) :=
      Complex.ofRealCLM.continuous.comp hreal
    exact (hcomplex.mul continuous_const).cexp.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x ↦ by
      rw [Complex.norm_exp]
      simp

lemma norm_centeredCoordinate_cexp_sub_taylor_le (a lam t x : ℝ) :
    ‖Complex.exp ((((t * centeredCoordinatePolynomial a lam x : ℝ) : ℂ) * Complex.I)) -
        (1 + (((t * centeredCoordinatePolynomial a lam x : ℝ) : ℂ) * Complex.I) +
          ((((t * centeredCoordinatePolynomial a lam x : ℝ) : ℂ) * Complex.I) ^ 2) / 2)‖ ≤
      |t| ^ 3 * |centeredCoordinatePolynomial a lam x| ^ 3 / 2 := by
  have h := LinearLCDCancellation.norm_cexp_sub_taylor_le 2
    ((((t * centeredCoordinatePolynomial a lam x : ℝ) : ℂ) * Complex.I))
  norm_num only [Nat.reduceAdd, Nat.factorial_two, Nat.cast_ofNat] at h
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero, max_self,
    Real.exp_zero, one_mul, Complex.norm_mul, Complex.norm_real,
    Complex.norm_I, mul_one, abs_mul, mul_pow] at h
  convert h using 1
  · congr 2
    norm_num [Finset.sum_range_succ]
    rw [mul_pow, Complex.I_sq]
    ring
  · rw [Real.norm_eq_abs, abs_mul, mul_pow]

/-- The integrated one-coordinate Taylor estimate underlying the standard
Lyapunov characteristic-function argument in KSSS Lemma 5.5(a). -/
theorem norm_centeredCoordinateCharFactor_sub_quadratic_le (a lam t : ℝ) :
    ‖centeredCoordinateCharFactor a lam t -
        ((1 : ℂ) - ((t ^ 2 * coordinateVariance a lam / 2 : ℝ) : ℂ))‖ ≤
      |t| ^ 3 * coordinateThirdAbsMoment a lam / 2 := by
  let X : ℝ → ℝ := centeredCoordinatePolynomial a lam
  let z : ℝ → ℂ := fun x ↦ (((t * X x : ℝ) : ℂ) * Complex.I)
  let p : ℝ → ℂ := fun x ↦ 1 + z x + z x ^ 2 / 2
  have hX : Integrable X standardGaussian := centeredCoordinatePolynomial_integrable a lam
  have hX2 : Integrable (fun x ↦ X x ^ 2) standardGaussian :=
    centeredCoordinatePolynomial_sq_integrable a lam
  have hX3 : Integrable (fun x ↦ |X x| ^ 3) standardGaussian :=
    centeredCoordinatePolynomial_abs_cube_integrable a lam
  have hz : Integrable z standardGaussian := by
    have h := ((hX.const_mul t).ofReal :
      Integrable (fun x ↦ ((t * X x : ℝ) : ℂ)) standardGaussian)
    exact h.mul_const Complex.I
  have hz2 : Integrable (fun x ↦ z x ^ 2) standardGaussian := by
    have h := ((hX2.const_mul (t ^ 2)).ofReal :
      Integrable (fun x ↦ ((t ^ 2 * X x ^ 2 : ℝ) : ℂ)) standardGaussian)
    have h' := h.mul_const (Complex.I ^ 2)
    exact h'.congr (Filter.Eventually.of_forall fun x ↦ by
      simp only [z]
      push_cast
      simp only [mul_pow]
      ac_rfl)
  have hp : Integrable p standardGaussian := by
    exact ((integrable_const (1 : ℂ)).add hz).add (hz2.div_const 2)
  have hexp : Integrable (fun x ↦ Complex.exp (z x)) standardGaussian := by
    simpa only [z, X] using centeredCoordinate_cexp_integrable a lam t
  have hzInt : ∫ x, z x ∂standardGaussian = 0 := by
    have hzeq : z = fun x ↦ ((t : ℂ) * Complex.I) * (X x : ℂ) := by
      funext x
      simp only [z]
      push_cast
      ring
    rw [hzeq, integral_const_mul]
    have hcast : (∫ x, (X x : ℂ) ∂standardGaussian) =
        ((∫ x : ℝ, X x ∂standardGaussian : ℝ) : ℂ) :=
      integral_ofReal
    rw [hcast, show ∫ x, X x ∂standardGaussian = 0 by
      simpa only [X] using coordinateFirstMoment_eq_zero a lam]
    simp
  have hz2Int : ∫ x, z x ^ 2 ∂standardGaussian =
      -((t ^ 2 * coordinateVariance a lam : ℝ) : ℂ) := by
    have hz2eq : (fun x ↦ z x ^ 2) =
        fun x ↦ (-((t ^ 2 : ℝ) : ℂ)) * ((X x ^ 2 : ℝ) : ℂ) := by
      funext x
      simp only [z]
      push_cast
      rw [mul_pow, Complex.I_sq]
      ring
    rw [hz2eq, integral_const_mul]
    have hcast : (∫ x, ((X x ^ 2 : ℝ) : ℂ) ∂standardGaussian) =
        ((∫ x : ℝ, X x ^ 2 ∂standardGaussian : ℝ) : ℂ) :=
      integral_ofReal
    rw [hcast, show ∫ x, X x ^ 2 ∂standardGaussian = coordinateVariance a lam by
      simpa only [X] using coordinateSecondMoment_eq a lam]
    push_cast
    ring
  have hpInt : ∫ x, p x ∂standardGaussian =
      (1 : ℂ) - ((t ^ 2 * coordinateVariance a lam / 2 : ℝ) : ℂ) := by
    have h1z : Integrable (fun x ↦ (1 : ℂ) + z x) standardGaussian :=
      (integrable_const (1 : ℂ)).add hz
    change (∫ x, (1 : ℂ) + z x + z x ^ 2 / 2 ∂standardGaussian) = _
    rw [integral_add h1z (hz2.div_const 2),
      integral_add (integrable_const (1 : ℂ)) hz, integral_const,
      hzInt, integral_div, hz2Int]
    simp
    push_cast
    ring
  have hdiff : centeredCoordinateCharFactor a lam t -
        ((1 : ℂ) - ((t ^ 2 * coordinateVariance a lam / 2 : ℝ) : ℂ)) =
      ∫ x, Complex.exp (z x) - p x ∂standardGaussian := by
    unfold centeredCoordinateCharFactor
    change (∫ x, Complex.exp (z x) ∂standardGaussian) - _ = _
    rw [integral_sub hexp hp, hpInt]
  rw [hdiff]
  have hdiffInt : Integrable (fun x ↦ Complex.exp (z x) - p x)
      standardGaussian := hexp.sub hp
  have hmajor : Integrable (fun x ↦ |t| ^ 3 * |X x| ^ 3 / 2)
      standardGaussian := by
    exact (hX3.const_mul (|t| ^ 3)).div_const 2
  calc
    ‖∫ x, Complex.exp (z x) - p x ∂standardGaussian‖ ≤
        ∫ x, ‖Complex.exp (z x) - p x‖ ∂standardGaussian :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, |t| ^ 3 * |X x| ^ 3 / 2 ∂standardGaussian := by
      exact integral_mono_ae hdiffInt.norm hmajor
        (Filter.Eventually.of_forall fun x ↦ by
          simpa only [z, p, X] using
            norm_centeredCoordinate_cexp_sub_taylor_le a lam t x)
    _ = |t| ^ 3 * coordinateThirdAbsMoment a lam / 2 := by
      rw [show (fun x ↦ |t| ^ 3 * |X x| ^ 3 / 2) =
          fun x ↦ (|t| ^ 3 / 2) * |X x| ^ 3 by
        funext x
        ring]
      rw [integral_const_mul]
      unfold coordinateThirdAbsMoment
      simp only [X]
      ring

lemma abs_cos_sub_quadratic_le (u : ℝ) :
    |Real.cos u - (1 - u ^ 2 / 2)| ≤ |u| ^ 3 / 6 := by
  by_cases hu : u = 0
  · subst u
    simp
  have hu0 : (0 : ℝ) ≠ u := Ne.symm hu
  obtain ⟨y, _hy, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := Real.cos) (x := u) (x₀ := 0) (n := 2) hu0
      (by simpa using Real.contDiff_cos.contDiffOn)
  have huniq : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) u) := uniqueDiffOn_uIcc hu0
  have hzero : (0 : ℝ) ∈ Set.uIcc 0 u := Set.left_mem_uIcc
  have hi1 : iteratedDerivWithin 1 Real.cos (Set.uIcc 0 u) 0 = 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv huniq Real.contDiff_cos.contDiffAt hzero]
    simp
  have hi2 : iteratedDerivWithin 2 Real.cos (Set.uIcc 0 u) 0 = -1 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv huniq Real.contDiff_cos.contDiffAt hzero]
    simp
  have htaylor :
      taylorWithinEval Real.cos 2 (Set.uIcc 0 u) 0 u = 1 - u ^ 2 / 2 := by
    norm_num [taylorWithinEval_succ, smul_eq_mul, hi1, hi2]
    ring
  rw [htaylor] at hrem
  rw [hrem, abs_div, abs_mul, abs_pow]
  norm_num [Nat.factorial]
  calc
    |Real.sin y| * |u| ^ 3 / 6 ≤
        1 * |u| ^ 3 / 6 := by
      gcongr
      exact Real.abs_sin_le_one y
    _ = |u| ^ 3 / 6 := by ring

lemma cos_le_quadratic_add_cubic (u : ℝ) :
    Real.cos u ≤ 1 - u ^ 2 / 2 + |u| ^ 3 / 6 := by
  have h := (abs_le.mp (abs_cos_sub_quadratic_le u)).2
  linarith

lemma abs_sub_cube_le_four (x y : ℝ) :
    |x - y| ^ 3 ≤ 4 * (|x| ^ 3 + |y| ^ 3) := by
  have hxy : |x - y| ≤ |x| + |y| := abs_sub x y
  have hpow : |x - y| ^ 3 ≤ (|x| + |y|) ^ 3 := by
    exact pow_le_pow_left₀ (abs_nonneg _) hxy 3
  have hnonneg : 0 ≤ |x| + |y| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hsquare : 0 ≤ (|x| + |y|) * (|x| - |y|) ^ 2 :=
    mul_nonneg hnonneg (sq_nonneg _)
  calc
    |x - y| ^ 3 ≤ (|x| + |y|) ^ 3 := hpow
    _ ≤ 4 * (|x| ^ 3 + |y| ^ 3) := by nlinarith

lemma norm_centeredCoordinateCharFactor_sq_eq_integral_cos_sub
    (a lam t : ℝ) :
    ‖centeredCoordinateCharFactor a lam t‖ ^ 2 =
      ∫ z : ℝ × ℝ,
        Real.cos (t * (centeredCoordinatePolynomial a lam z.1 -
          centeredCoordinatePolynomial a lam z.2))
        ∂standardGaussian.prod standardGaussian := by
  let X : ℝ → ℝ := centeredCoordinatePolynomial a lam
  let f : ℝ → ℂ := fun x ↦ Complex.exp ((((t * X x : ℝ) : ℂ) * Complex.I))
  let g : ℝ → ℂ := fun y ↦ Complex.exp (((((-t) * X y : ℝ) : ℂ) * Complex.I))
  have hf : Integrable f standardGaussian := by
    simpa only [f, X] using centeredCoordinate_cexp_integrable a lam t
  have hg : Integrable g standardGaussian := by
    simpa only [g, X] using centeredCoordinate_cexp_integrable a lam (-t)
  have hprod : Integrable (fun z : ℝ × ℝ ↦ f z.1 * g z.2)
      (standardGaussian.prod standardGaussian) := hf.mul_prod hg
  have hconj : conj (∫ x, f x ∂standardGaussian) =
      ∫ y, g y ∂standardGaussian := by
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards [] with y
    simp only [f, g, ← Complex.exp_conj]
    congr 1
    simp
  have hmul :
      centeredCoordinateCharFactor a lam t *
          conj (centeredCoordinateCharFactor a lam t) =
        ∫ z : ℝ × ℝ, f z.1 * g z.2
          ∂standardGaussian.prod standardGaussian := by
    unfold centeredCoordinateCharFactor
    change (∫ x, f x ∂standardGaussian) *
        conj (∫ x, f x ∂standardGaussian) = _
    rw [hconj, integral_prod_mul]
  calc
    ‖centeredCoordinateCharFactor a lam t‖ ^ 2 =
        Complex.normSq (centeredCoordinateCharFactor a lam t) :=
      Complex.sq_norm _
    _ = (centeredCoordinateCharFactor a lam t *
          conj (centeredCoordinateCharFactor a lam t)).re := by
      rw [Complex.mul_conj]
      rfl
    _ = (∫ z : ℝ × ℝ, f z.1 * g z.2
          ∂standardGaussian.prod standardGaussian).re := by rw [hmul]
    _ = ∫ z : ℝ × ℝ, (f z.1 * g z.2).re
          ∂standardGaussian.prod standardGaussian :=
      (integral_re hprod).symm
    _ = ∫ z : ℝ × ℝ,
          Real.cos (t * (X z.1 - X z.2))
          ∂standardGaussian.prod standardGaussian := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [f, g, ← Complex.exp_add]
      have he :
          ((t * X z.1 : ℝ) : ℂ) * Complex.I +
              (((-t) * X z.2 : ℝ) : ℂ) * Complex.I =
            ((t * (X z.1 - X z.2) : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [he, Complex.exp_ofReal_mul_I_re]
    _ = ∫ z : ℝ × ℝ,
          Real.cos (t * (centeredCoordinatePolynomial a lam z.1 -
            centeredCoordinatePolynomial a lam z.2))
          ∂standardGaussian.prod standardGaussian := by rfl

lemma integral_centeredCoordinatePolynomial_sub_sq (a lam : ℝ) :
    (∫ z : ℝ × ℝ,
        (centeredCoordinatePolynomial a lam z.1 -
          centeredCoordinatePolynomial a lam z.2) ^ 2
        ∂standardGaussian.prod standardGaussian) =
      2 * coordinateVariance a lam := by
  let X : ℝ → ℝ := centeredCoordinatePolynomial a lam
  have hX : Integrable X standardGaussian := by
    simpa only [X] using centeredCoordinatePolynomial_integrable a lam
  have hX2 : Integrable (fun x ↦ X x ^ 2) standardGaussian := by
    simpa only [X] using centeredCoordinatePolynomial_sq_integrable a lam
  have hX2fst : Integrable (fun z : ℝ × ℝ ↦ X z.1 ^ 2)
      (standardGaussian.prod standardGaussian) :=
    hX2.comp_fst standardGaussian
  have hX2snd : Integrable (fun z : ℝ × ℝ ↦ X z.2 ^ 2)
      (standardGaussian.prod standardGaussian) :=
    hX2.comp_snd standardGaussian
  have hcross : Integrable (fun z : ℝ × ℝ ↦ X z.1 * X z.2)
      (standardGaussian.prod standardGaussian) := hX.mul_prod hX
  rw [show (fun z : ℝ × ℝ ↦ (X z.1 - X z.2) ^ 2) =
      fun z ↦ X z.1 ^ 2 + X z.2 ^ 2 - 2 * (X z.1 * X z.2) by
    funext z
    ring]
  have hsplit :
      (∫ z : ℝ × ℝ, X z.1 ^ 2 + X z.2 ^ 2 -
          2 * (X z.1 * X z.2) ∂standardGaussian.prod standardGaussian) =
        (∫ z : ℝ × ℝ, X z.1 ^ 2 + X z.2 ^ 2
          ∂standardGaussian.prod standardGaussian) -
        ∫ z : ℝ × ℝ, 2 * (X z.1 * X z.2)
          ∂standardGaussian.prod standardGaussian := by
    exact integral_sub (hX2fst.add hX2snd) (hcross.const_mul 2)
  have hfst :
      (∫ z : ℝ × ℝ, X z.1 ^ 2 ∂standardGaussian.prod standardGaussian) =
        ∫ x : ℝ, X x ^ 2 ∂standardGaussian := by
    simpa only [probReal_univ, one_smul] using
      (integral_fun_fst (μ := standardGaussian) (ν := standardGaussian)
        (fun x : ℝ ↦ X x ^ 2))
  have hsnd :
      (∫ z : ℝ × ℝ, X z.2 ^ 2 ∂standardGaussian.prod standardGaussian) =
        ∫ x : ℝ, X x ^ 2 ∂standardGaussian := by
    simpa only [probReal_univ, one_smul] using
      (integral_fun_snd (μ := standardGaussian) (ν := standardGaussian)
        (fun x : ℝ ↦ X x ^ 2))
  rw [hsplit, integral_add hX2fst hX2snd, integral_const_mul,
    integral_prod_mul, hfst, hsnd]
  rw [show ∫ x, X x ^ 2 ∂standardGaussian = coordinateVariance a lam by
      simpa only [X] using coordinateSecondMoment_eq a lam,
    show ∫ x, X x ∂standardGaussian = 0 by
      simpa only [X] using coordinateFirstMoment_eq_zero a lam]
  ring

lemma integral_abs_centeredCoordinatePolynomial_sub_cube_le (a lam : ℝ) :
    (∫ z : ℝ × ℝ,
        |centeredCoordinatePolynomial a lam z.1 -
          centeredCoordinatePolynomial a lam z.2| ^ 3
        ∂standardGaussian.prod standardGaussian) ≤
      8 * coordinateThirdAbsMoment a lam := by
  let X : ℝ → ℝ := centeredCoordinatePolynomial a lam
  have hX3 : Integrable (fun x ↦ |X x| ^ 3) standardGaussian := by
    simpa only [X] using centeredCoordinatePolynomial_abs_cube_integrable a lam
  have hX3fst : Integrable (fun z : ℝ × ℝ ↦ |X z.1| ^ 3)
      (standardGaussian.prod standardGaussian) :=
    hX3.comp_fst standardGaussian
  have hX3snd : Integrable (fun z : ℝ × ℝ ↦ |X z.2| ^ 3)
      (standardGaussian.prod standardGaussian) :=
    hX3.comp_snd standardGaussian
  have hmajor : Integrable
      (fun z : ℝ × ℝ ↦ 4 * (|X z.1| ^ 3 + |X z.2| ^ 3))
      (standardGaussian.prod standardGaussian) :=
    (hX3fst.add hX3snd).const_mul 4
  have hdiff : Integrable
      (fun z : ℝ × ℝ ↦ |X z.1 - X z.2| ^ 3)
      (standardGaussian.prod standardGaussian) := by
    apply hmajor.mono'
    · have hc : Continuous (fun z : ℝ × ℝ ↦
          |centeredCoordinatePolynomial a lam z.1 -
            centeredCoordinatePolynomial a lam z.2| ^ 3) := by
        exact (((continuous_centeredCoordinatePolynomial a lam).comp continuous_fst).sub
          ((continuous_centeredCoordinatePolynomial a lam).comp continuous_snd)).abs.pow 3
      simpa only [X] using hc.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun z ↦ by
        simpa only [Real.norm_eq_abs,
          abs_of_nonneg (by positivity : 0 ≤ |X z.1 - X z.2| ^ 3)] using
            abs_sub_cube_le_four (X z.1) (X z.2)
  have hfst :
      (∫ z : ℝ × ℝ, |X z.1| ^ 3 ∂standardGaussian.prod standardGaussian) =
        ∫ x : ℝ, |X x| ^ 3 ∂standardGaussian := by
    simpa only [probReal_univ, one_smul] using
      (integral_fun_fst (μ := standardGaussian) (ν := standardGaussian)
        (fun x : ℝ ↦ |X x| ^ 3))
  have hsnd :
      (∫ z : ℝ × ℝ, |X z.2| ^ 3 ∂standardGaussian.prod standardGaussian) =
        ∫ x : ℝ, |X x| ^ 3 ∂standardGaussian := by
    simpa only [probReal_univ, one_smul] using
      (integral_fun_snd (μ := standardGaussian) (ν := standardGaussian)
        (fun x : ℝ ↦ |X x| ^ 3))
  calc
    (∫ z : ℝ × ℝ, |X z.1 - X z.2| ^ 3
        ∂standardGaussian.prod standardGaussian) ≤
        ∫ z : ℝ × ℝ, 4 * (|X z.1| ^ 3 + |X z.2| ^ 3)
          ∂standardGaussian.prod standardGaussian := by
      exact integral_mono_ae hdiff hmajor
        (Filter.Eventually.of_forall fun z ↦ abs_sub_cube_le_four (X z.1) (X z.2))
    _ = 8 * coordinateThirdAbsMoment a lam := by
      rw [integral_const_mul, integral_add hX3fst hX3snd, hfst, hsnd]
      unfold coordinateThirdAbsMoment
      simp only [X]
      ring

/-- Symmetrization gives the one-coordinate damping estimate needed in the
Lyapunov characteristic-function argument. -/
theorem norm_centeredCoordinateCharFactor_sq_le (a lam t : ℝ) :
    ‖centeredCoordinateCharFactor a lam t‖ ^ 2 ≤
      1 - coordinateVariance a lam * t ^ 2 +
        (4 / 3 : ℝ) * coordinateThirdAbsMoment a lam * |t| ^ 3 := by
  rw [norm_centeredCoordinateCharFactor_sq_eq_integral_cos_sub]
  let X : ℝ → ℝ := centeredCoordinatePolynomial a lam
  let D : ℝ × ℝ → ℝ := fun z ↦ X z.1 - X z.2
  let M : ℝ × ℝ → ℝ := fun z ↦
    1 - t ^ 2 * D z ^ 2 / 2 + |t| ^ 3 * |D z| ^ 3 / 6
  have hX : Integrable X standardGaussian := by
    simpa only [X] using centeredCoordinatePolynomial_integrable a lam
  have hX2 : Integrable (fun x ↦ X x ^ 2) standardGaussian := by
    simpa only [X] using centeredCoordinatePolynomial_sq_integrable a lam
  have hX3 : Integrable (fun x ↦ |X x| ^ 3) standardGaussian := by
    simpa only [X] using centeredCoordinatePolynomial_abs_cube_integrable a lam
  have hX2fst : Integrable (fun z : ℝ × ℝ ↦ X z.1 ^ 2)
      (standardGaussian.prod standardGaussian) := hX2.comp_fst standardGaussian
  have hX2snd : Integrable (fun z : ℝ × ℝ ↦ X z.2 ^ 2)
      (standardGaussian.prod standardGaussian) := hX2.comp_snd standardGaussian
  have hcross : Integrable (fun z : ℝ × ℝ ↦ X z.1 * X z.2)
      (standardGaussian.prod standardGaussian) := hX.mul_prod hX
  have hD2 : Integrable (fun z ↦ D z ^ 2)
      (standardGaussian.prod standardGaussian) := by
    have h := (hX2fst.add hX2snd).sub (hcross.const_mul 2)
    exact h.congr (Filter.Eventually.of_forall fun z ↦ by
      change X z.1 ^ 2 + X z.2 ^ 2 - 2 * (X z.1 * X z.2) =
        D z ^ 2
      dsimp only [D]
      ring)
  have hX3fst : Integrable (fun z : ℝ × ℝ ↦ |X z.1| ^ 3)
      (standardGaussian.prod standardGaussian) := hX3.comp_fst standardGaussian
  have hX3snd : Integrable (fun z : ℝ × ℝ ↦ |X z.2| ^ 3)
      (standardGaussian.prod standardGaussian) := hX3.comp_snd standardGaussian
  have hD3major : Integrable
      (fun z : ℝ × ℝ ↦ 4 * (|X z.1| ^ 3 + |X z.2| ^ 3))
      (standardGaussian.prod standardGaussian) :=
    (hX3fst.add hX3snd).const_mul 4
  have hD3 : Integrable (fun z ↦ |D z| ^ 3)
      (standardGaussian.prod standardGaussian) := by
    apply hD3major.mono'
    · have hc : Continuous (fun z : ℝ × ℝ ↦
          |centeredCoordinatePolynomial a lam z.1 -
            centeredCoordinatePolynomial a lam z.2| ^ 3) := by
        exact (((continuous_centeredCoordinatePolynomial a lam).comp continuous_fst).sub
          ((continuous_centeredCoordinatePolynomial a lam).comp continuous_snd)).abs.pow 3
      simpa only [D, X] using hc.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun z ↦ by
        simpa only [Real.norm_eq_abs,
          abs_of_nonneg (by positivity : 0 ≤ |D z| ^ 3), D] using
            abs_sub_cube_le_four (X z.1) (X z.2)
  have hcos : Integrable (fun z : ℝ × ℝ ↦ Real.cos (t * D z))
      (standardGaussian.prod standardGaussian) := by
    apply (integrable_const (1 : ℝ)).mono'
    · have hc : Continuous (fun z : ℝ × ℝ ↦
          Real.cos (t * (centeredCoordinatePolynomial a lam z.1 -
            centeredCoordinatePolynomial a lam z.2))) := by
        apply Real.continuous_cos.comp
        exact continuous_const.mul
          (((continuous_centeredCoordinatePolynomial a lam).comp continuous_fst).sub
            ((continuous_centeredCoordinatePolynomial a lam).comp continuous_snd))
      simpa only [D, X] using hc.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun z ↦ by
        simpa only [Real.norm_eq_abs, norm_one] using Real.abs_cos_le_one (t * D z)
  have hA : Integrable (fun z : ℝ × ℝ ↦ 1 - t ^ 2 * D z ^ 2 / 2)
      (standardGaussian.prod standardGaussian) :=
    (integrable_const (1 : ℝ)).sub ((hD2.const_mul (t ^ 2)).div_const 2)
  have hB : Integrable (fun z : ℝ × ℝ ↦ |t| ^ 3 * |D z| ^ 3 / 6)
      (standardGaussian.prod standardGaussian) :=
    (hD3.const_mul (|t| ^ 3)).div_const 6
  have hM : Integrable M (standardGaussian.prod standardGaussian) := by
    dsimp only [M]
    exact (hA.add hB).congr (Filter.Eventually.of_forall fun _ ↦ rfl)
  have hpoint : ∀ z, Real.cos (t * D z) ≤ M z := by
    intro z
    dsimp only [M]
    have h := cos_le_quadratic_add_cubic (t * D z)
    rw [mul_pow, abs_mul, mul_pow] at h
    nlinarith
  have hsqInt :
      (∫ z : ℝ × ℝ, D z ^ 2 ∂standardGaussian.prod standardGaussian) =
        2 * coordinateVariance a lam := by
    simpa only [D, X] using integral_centeredCoordinatePolynomial_sub_sq a lam
  have hcubeInt :
      (∫ z : ℝ × ℝ, |D z| ^ 3 ∂standardGaussian.prod standardGaussian) ≤
        8 * coordinateThirdAbsMoment a lam := by
    simpa only [D, X] using
      integral_abs_centeredCoordinatePolynomial_sub_cube_le a lam
  calc
    (∫ z : ℝ × ℝ, Real.cos (t * D z)
        ∂standardGaussian.prod standardGaussian) ≤
        ∫ z : ℝ × ℝ, M z ∂standardGaussian.prod standardGaussian := by
      exact integral_mono_ae hcos hM (Filter.Eventually.of_forall hpoint)
    _ = 1 - t ^ 2 * coordinateVariance a lam +
          |t| ^ 3 / 6 *
            (∫ z : ℝ × ℝ, |D z| ^ 3
              ∂standardGaussian.prod standardGaussian) := by
      dsimp only [M]
      have hsplitM :
          (∫ z : ℝ × ℝ,
              (1 - t ^ 2 * D z ^ 2 / 2) +
                |t| ^ 3 * |D z| ^ 3 / 6
              ∂standardGaussian.prod standardGaussian) =
            (∫ z : ℝ × ℝ, 1 - t ^ 2 * D z ^ 2 / 2
              ∂standardGaussian.prod standardGaussian) +
            ∫ z : ℝ × ℝ, |t| ^ 3 * |D z| ^ 3 / 6
              ∂standardGaussian.prod standardGaussian := integral_add hA hB
      have hsplitA :
          (∫ z : ℝ × ℝ, 1 - t ^ 2 * D z ^ 2 / 2
              ∂standardGaussian.prod standardGaussian) =
            (∫ _z : ℝ × ℝ, (1 : ℝ)
              ∂standardGaussian.prod standardGaussian) -
            ∫ z : ℝ × ℝ, t ^ 2 * D z ^ 2 / 2
              ∂standardGaussian.prod standardGaussian :=
        integral_sub (integrable_const (1 : ℝ))
          ((hD2.const_mul (t ^ 2)).div_const 2)
      rw [hsplitM, hsplitA,
        integral_const, integral_div, integral_const_mul, integral_div,
        integral_const_mul, hsqInt]
      simp only [probReal_univ, one_smul]
      ring
    _ ≤ 1 - t ^ 2 * coordinateVariance a lam +
          |t| ^ 3 / 6 * (8 * coordinateThirdAbsMoment a lam) := by
      gcongr
    _ = 1 - coordinateVariance a lam * t ^ 2 +
          (4 / 3 : ℝ) * coordinateThirdAbsMoment a lam * |t| ^ 3 := by ring

theorem norm_centeredCoordinateCharFactor_le_exp (a lam t : ℝ) :
    ‖centeredCoordinateCharFactor a lam t‖ ≤
      Real.exp (-coordinateVariance a lam * t ^ 2 / 2 +
        (2 / 3 : ℝ) * coordinateThirdAbsMoment a lam * |t| ^ 3) := by
  let u : ℝ := -coordinateVariance a lam * t ^ 2 +
    (4 / 3 : ℝ) * coordinateThirdAbsMoment a lam * |t| ^ 3
  have hsquare : ‖centeredCoordinateCharFactor a lam t‖ ^ 2 ≤ Real.exp u := by
    calc
      ‖centeredCoordinateCharFactor a lam t‖ ^ 2 ≤
          1 - coordinateVariance a lam * t ^ 2 +
            (4 / 3 : ℝ) * coordinateThirdAbsMoment a lam * |t| ^ 3 :=
        norm_centeredCoordinateCharFactor_sq_le a lam t
      _ = u + 1 := by dsimp only [u]; ring
      _ ≤ Real.exp u := Real.add_one_le_exp u
  apply le_of_sq_le_sq _ (by positivity)
  calc
    ‖centeredCoordinateCharFactor a lam t‖ ^ 2 ≤ Real.exp u := hsquare
    _ = (Real.exp (-coordinateVariance a lam * t ^ 2 / 2 +
          (2 / 3 : ℝ) * coordinateThirdAbsMoment a lam * |t| ^ 3)) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      dsimp only [u]
      ring

lemma norm_finsetProd_sub_finsetProd_le
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f g : ι → ℂ) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤
      ∑ i ∈ s, ‖f i - g i‖ *
        ∏ j ∈ s.erase i, max ‖f j‖ ‖g j‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      have hrewrite :
          f i * (∏ j ∈ s, f j) - g i * ∏ j ∈ s, g j =
            (f i - g i) * (∏ j ∈ s, f j) +
              g i * ((∏ j ∈ s, f j) - ∏ j ∈ s, g j) := by ring
      rw [hrewrite]
      calc
        ‖(f i - g i) * (∏ j ∈ s, f j) +
            g i * ((∏ j ∈ s, f j) - ∏ j ∈ s, g j)‖ ≤
            ‖(f i - g i) * (∏ j ∈ s, f j)‖ +
              ‖g i * ((∏ j ∈ s, f j) - ∏ j ∈ s, g j)‖ :=
          norm_add_le _ _
        _ = ‖f i - g i‖ * (∏ j ∈ s, ‖f j‖) +
              ‖g i‖ * ‖(∏ j ∈ s, f j) - ∏ j ∈ s, g j‖ := by
          simp only [norm_mul, norm_prod]
        _ ≤ ‖f i - g i‖ * (∏ j ∈ s, max ‖f j‖ ‖g j‖) +
              max ‖f i‖ ‖g i‖ *
                (∑ j ∈ s, ‖f j - g j‖ *
                  ∏ k ∈ s.erase j, max ‖f k‖ ‖g k‖) := by
          apply add_le_add
          · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            apply Finset.prod_le_prod
            · intro j hj
              positivity
            · intro j hj
              exact le_max_left _ _
          · exact mul_le_mul (le_max_right _ _) ih (norm_nonneg _) (by positivity)
        _ = ∑ j ∈ insert i s, ‖f j - g j‖ *
              ∏ k ∈ (insert i s).erase j, max ‖f k‖ ‖g k‖ := by
          rw [Finset.sum_insert hi, Finset.erase_insert hi]
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          have hij : i ≠ j := fun h ↦ hi (h ▸ hj)
          rw [Finset.erase_insert_of_ne hij]
          rw [Finset.prod_insert]
          · ring
          · exact fun hmem ↦ hi (Finset.erase_subset j s hmem)

theorem norm_diagonalCenteredCharProduct_le_exp
    {ι : Type*} [Fintype ι] (a lam : ι → ℝ) (t : ℝ) :
    ‖diagonalCenteredCharProduct a lam t‖ ≤
      Real.exp (-totalVariance a lam * t ^ 2 / 2 +
        (2 / 3 : ℝ) * totalThirdAbsMoment a lam * |t| ^ 3) := by
  classical
  rw [diagonalCenteredCharProduct, norm_prod]
  calc
    (∏ i, ‖centeredCoordinateCharFactor (a i) (lam i) t‖) ≤
        ∏ i, Real.exp (-coordinateVariance (a i) (lam i) * t ^ 2 / 2 +
          (2 / 3 : ℝ) * coordinateThirdAbsMoment (a i) (lam i) * |t| ^ 3) := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        exact norm_centeredCoordinateCharFactor_le_exp (a i) (lam i) t
    _ = Real.exp (∑ i,
          (-coordinateVariance (a i) (lam i) * t ^ 2 / 2 +
            (2 / 3 : ℝ) * coordinateThirdAbsMoment (a i) (lam i) * |t| ^ 3)) := by
      rw [Real.exp_sum]
    _ = Real.exp (-totalVariance a lam * t ^ 2 / 2 +
          (2 / 3 : ℝ) * totalThirdAbsMoment a lam * |t| ^ 3) := by
      congr 1
      simp only [totalVariance, totalThirdAbsMoment, Finset.sum_add_distrib]
      congr 1
      · calc
          (∑ i, -coordinateVariance (a i) (lam i) * t ^ 2 / 2) =
              -(∑ i, coordinateVariance (a i) (lam i)) * t ^ 2 / 2 := by
            rw [← Finset.sum_div, ← Finset.sum_mul,
              ← Finset.sum_neg_distrib]
          _ = -(∑ i, coordinateVariance (a i) (lam i)) * t ^ 2 / 2 := rfl
      · calc
          (∑ i, (2 / 3 : ℝ) * coordinateThirdAbsMoment (a i) (lam i) *
              |t| ^ 3) =
              (2 / 3 : ℝ) *
                (∑ i, coordinateThirdAbsMoment (a i) (lam i)) * |t| ^ 3 := by
            rw [← Finset.sum_mul, ← Finset.mul_sum]
          _ = (2 / 3 : ℝ) *
                (∑ i, coordinateThirdAbsMoment (a i) (lam i)) * |t| ^ 3 := rfl

theorem norm_diagonalCenteredCharProduct_le_exp_neg_sq
    {ι : Type*} [Fintype ι] (a lam : ι → ℝ)
    (hsum : totalVariance a lam = 1) (t : ℝ)
    (ht : totalThirdAbsMoment a lam * |t| ≤ 1 / 4) :
    ‖diagonalCenteredCharProduct a lam t‖ ≤ Real.exp (-t ^ 2 / 3) := by
  have habs : |t| ^ 3 = |t| * t ^ 2 := by
    rw [pow_succ, sq_abs]
    ring
  have hmul := mul_le_mul_of_nonneg_right ht (sq_nonneg t)
  calc
    ‖diagonalCenteredCharProduct a lam t‖ ≤
        Real.exp (-totalVariance a lam * t ^ 2 / 2 +
          (2 / 3 : ℝ) * totalThirdAbsMoment a lam * |t| ^ 3) :=
      norm_diagonalCenteredCharProduct_le_exp a lam t
    _ ≤ Real.exp (-t ^ 2 / 3) := by
      apply Real.exp_le_exp.mpr
      rw [hsum, habs]
      nlinarith [sq_nonneg t]

lemma centeredCoordinateCharFactor_eq_charFun_map (a lam t : ℝ) :
    centeredCoordinateCharFactor a lam t =
      charFun (standardGaussian.map (centeredCoordinatePolynomial a lam)) t := by
  rw [charFun_apply_real, integral_map]
  · unfold centeredCoordinateCharFactor
    apply integral_congr_ae
    filter_upwards [] with x
    congr 2
    push_cast
    ring
  · exact (continuous_centeredCoordinatePolynomial a lam).aemeasurable
  · fun_prop

/-- Sharp third-order one-coordinate characteristic-function remainder. -/
theorem norm_centeredCoordinateCharFactor_sub_quadratic_le_sharp
    (a lam t : ℝ) :
    ‖centeredCoordinateCharFactor a lam t -
        ((1 : ℂ) - ((t ^ 2 * coordinateVariance a lam / 2 : ℝ) : ℂ))‖ ≤
      |t| ^ 3 * coordinateThirdAbsMoment a lam / 6 := by
  let X : ℝ → ℝ := centeredCoordinatePolynomial a lam
  let μ : Measure ℝ := standardGaussian.map X
  have hXm : AEStronglyMeasurable X standardGaussian :=
    (continuous_centeredCoordinatePolynomial a lam).aestronglyMeasurable
  have hX3 : Integrable (fun x ↦ |X x| ^ 3) standardGaussian := by
    simpa only [X] using centeredCoordinatePolynomial_abs_cube_integrable a lam
  have hmemX : MemLp X (3 : ENNReal) standardGaussian := by
    apply (integrable_norm_rpow_iff hXm (by norm_num) (by norm_num)).mp
    have hX3r : Integrable (fun x ↦ ‖X x‖ ^ (3 : ℝ)) standardGaussian :=
      hX3.congr (Filter.Eventually.of_forall fun x ↦ by
        change |X x| ^ (3 : ℕ) = |X x| ^ (3 : ℝ)
        exact (Real.rpow_natCast |X x| 3).symm)
    simpa only [ENNReal.toReal_ofNat] using hX3r
  have hmemId : MemLp id (3 : ENNReal) μ := by
    rw [memLp_map_measure_iff (by fun_prop) hXm.aemeasurable]
    change MemLp X (3 : ENNReal) standardGaussian
    exact hmemX
  letI : IsProbabilityMeasure μ := by
    dsimp only [μ]
    exact Measure.isProbabilityMeasure_map hXm.aemeasurable
  rw [centeredCoordinateCharFactor_eq_charFun_map]
  change ‖charFun μ t -
      ((1 : ℂ) - ((t ^ 2 * coordinateVariance a lam / 2 : ℝ) : ℂ))‖ ≤ _
  by_cases ht : t = 0
  · subst t
    simp [μ]
  have ht0 : (0 : ℝ) ≠ t := Ne.symm ht
  have hcont : ContDiff ℝ 3 (charFun μ) :=
    MeasureTheory.contDiff_charFun hmemId
  have hu : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) t) := uniqueDiffOn_uIcc ht0
  have hzero_mem : (0 : ℝ) ∈ Set.uIcc 0 t := Set.left_mem_uIcc
  have hmem1 : MemLp id (1 : ENNReal) μ := hmemId.mono_exponent (by norm_num)
  have hmem2 : MemLp id (2 : ENNReal) μ := hmemId.mono_exponent (by norm_num)
  have hmeanMap : ∫ x : ℝ, x ∂μ = 0 := by
    dsimp only [μ]
    rw [integral_map hXm.aemeasurable (by fun_prop)]
    simpa only [X] using coordinateFirstMoment_eq_zero a lam
  have hsecondMap : ∫ x : ℝ, x ^ 2 ∂μ = coordinateVariance a lam := by
    dsimp only [μ]
    rw [integral_map hXm.aemeasurable (by fun_prop)]
    simpa only [X] using coordinateSecondMoment_eq a lam
  have hi1 :
      iteratedDerivWithin 1 (charFun μ) (Set.uIcc 0 t) 0 = 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu
      (hcont.contDiffAt.of_le (by norm_num)) hzero_mem]
    rw [MeasureTheory.iteratedDeriv_charFun_zero (by simpa using hmem1)]
    simp only [pow_one, hmeanMap]
    simp
  have hi2 :
      iteratedDerivWithin 2 (charFun μ) (Set.uIcc 0 t) 0 =
        -((coordinateVariance a lam : ℝ) : ℂ) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu
      (hcont.contDiffAt.of_le (by norm_num)) hzero_mem]
    rw [MeasureTheory.iteratedDeriv_charFun_zero (by simpa using hmem2), hsecondMap]
    norm_num [Complex.I_sq]
  have htaylor :
      taylorWithinEval (charFun μ) 2 (Set.uIcc 0 t) 0 t =
        (1 : ℂ) - ((t ^ 2 * coordinateVariance a lam / 2 : ℝ) : ℂ) := by
    norm_num [taylorWithinEval_succ, RCLike.real_smul_eq_coe_mul, hi1, hi2]
    push_cast
    ring
  have hthird (y : ℝ) :
      ‖∫ x : ℝ, x ^ 3 * Complex.exp (y * x * Complex.I) ∂μ‖ ≤
        coordinateThirdAbsMoment a lam := by
    calc
      ‖∫ x : ℝ, x ^ 3 * Complex.exp (y * x * Complex.I) ∂μ‖ ≤
          ∫ x : ℝ, ‖(x ^ 3 : ℂ) * Complex.exp (y * x * Complex.I)‖ ∂μ :=
        norm_integral_le_integral_norm _
      _ = ∫ x : ℝ, |x| ^ 3 ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [norm_mul, Complex.norm_exp]
        norm_num [Real.norm_eq_abs, abs_pow]
      _ = coordinateThirdAbsMoment a lam := by
        dsimp only [μ]
        rw [integral_map hXm.aemeasurable (by fun_prop)]
        rfl
  have hderiv (y : ℝ) (hy : y ∈ Set.uIcc (0 : ℝ) t) :
      ‖iteratedDerivWithin 3 (charFun μ) (Set.uIcc 0 t) y‖ ≤
        coordinateThirdAbsMoment a lam := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu
      (hcont.contDiffAt.of_le (by norm_num)) hy]
    rw [MeasureTheory.iteratedDeriv_charFun (by simpa using hmemId), norm_mul]
    simp only [norm_pow, Complex.norm_I, one_pow, one_mul]
    exact hthird y
  have hrem := taylor_integral_remainder
    (f := charFun μ) (x := t) (x₀ := 0) (n := 2)
    (by simpa using hcont.contDiffOn)
  rw [htaylor] at hrem
  rw [hrem]
  let β : ℝ := coordinateThirdAbsMoment a lam
  let g : ℝ → ℝ := fun y ↦ β * (t - y) ^ 2 / 2
  have hβ : 0 ≤ β := by
    dsimp only [β, coordinateThirdAbsMoment]
    exact integral_nonneg fun _ ↦ by positivity
  have hgint : IntervalIntegrable g volume 0 t := by
    apply Continuous.intervalIntegrable
    fun_prop
  calc
    ‖∫ y in (0 : ℝ)..t,
        ((t - y) ^ 2 / (Nat.factorial 2 : ℝ)) •
          iteratedDerivWithin 3 (charFun μ) (Set.uIcc 0 t) y‖ ≤
        |∫ y in (0 : ℝ)..t, g y| := by
      apply intervalIntegral.norm_integral_le_abs_of_norm_le
      · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability :
            MeasurableSet (Set.uIoc (0 : ℝ) t))] with y hy
        have hy' : y ∈ Set.uIcc (0 : ℝ) t := Set.uIoc_subset_uIcc hy
        rw [norm_smul, Real.norm_eq_abs]
        norm_num [Nat.factorial, abs_of_nonneg (sq_nonneg (t - y))]
        dsimp only [g]
        rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (by norm_num))]
        calc
          (t - y) ^ 2 / 2 *
              ‖iteratedDerivWithin 3 (charFun μ) (Set.uIcc 0 t) y‖ ≤
              (t - y) ^ 2 / 2 * β :=
            mul_le_mul_of_nonneg_left (hderiv y hy')
              (div_nonneg (sq_nonneg _) (by norm_num))
          _ = β * (t - y) ^ 2 / 2 := by ring
      · exact hgint
    _ = β * |t| ^ 3 / 6 := by
      have hpow : (∫ y in (0 : ℝ)..t, (t - y) ^ 2) = t ^ 3 / 3 := by
        have hanti : ∀ y ∈ Set.uIcc (0 : ℝ) t,
            HasDerivAt (fun z : ℝ ↦ -(t - z) ^ 3 / 3) ((t - y) ^ 2) y := by
          intro y _
          have hd0 : HasDerivAt (fun z : ℝ ↦ t - z) (-1) y := by
            simpa only [id_eq] using (hasDerivAt_id y).const_sub t
          have hd3 := hd0.pow 3
          have hs := HasDerivAt.const_mul (-1 / 3 : ℝ) hd3
          have hfun : (fun z : ℝ ↦ -(t - z) ^ 3 / 3) =
              fun z : ℝ ↦ (-1 / 3) * (t - z) ^ 3 := by
            funext z
            ring
          rw [hfun]
          apply hs.congr_deriv
          norm_num
          ring
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hanti
          ((by fun_prop : Continuous (fun x : ℝ ↦ (t - x) ^ 2)).intervalIntegrable 0 t)]
        ring
      have hgform : g = fun y ↦ (β / 2) * (t - y) ^ 2 := by
        funext y
        dsimp only [g]
        ring
      rw [hgform, intervalIntegral.integral_const_mul, hpow]
      simp only [abs_mul, abs_div, abs_pow, abs_of_nonneg hβ]
      norm_num
      ring
    _ = |t| ^ 3 * coordinateThirdAbsMoment a lam / 6 := by
      dsimp only [β]
      ring

lemma coordinateVariance_mul_sq_lt_one_fourth
    (a lam t : ℝ)
    (hsmall : coordinateThirdAbsMoment a lam * |t| ^ 3 < 1 / 8) :
    coordinateVariance a lam * t ^ 2 < 1 / 4 := by
  let σ : ℝ := coordinateSigma a lam
  let β : ℝ := coordinateThirdAbsMoment a lam
  let y : ℝ := σ * |t|
  have hσ0 : 0 ≤ σ := by dsimp only [σ]; exact coordinateSigma_nonneg a lam
  have hy0 : 0 ≤ y := mul_nonneg hσ0 (abs_nonneg t)
  have hycube : y ^ 3 ≤ β * |t| ^ 3 := by
    have hmoment := coordinateThirdAbsMoment_lower a lam
    have hmul := mul_le_mul_of_nonneg_right hmoment (pow_nonneg (abs_nonneg t) 3)
    simpa only [σ, β, y, mul_pow] using hmul
  have hycube_lt : y ^ 3 < (1 / 2 : ℝ) ^ 3 := by
    calc
      y ^ 3 ≤ β * |t| ^ 3 := hycube
      _ < 1 / 8 := by simpa only [β] using hsmall
      _ = (1 / 2 : ℝ) ^ 3 := by norm_num
  have hy : y < 1 / 2 :=
    lt_of_pow_lt_pow_left₀ 3 (by norm_num) hycube_lt
  have hvty : coordinateVariance a lam * t ^ 2 = y ^ 2 := by
    dsimp only [y, σ]
    rw [mul_pow, sq_abs, coordinateSigma_sq]
  rw [hvty]
  nlinarith [sq_nonneg y]

theorem norm_centeredCoordinateCharFactor_sub_gaussian_le
    (a lam t : ℝ)
    (hsmall : coordinateThirdAbsMoment a lam * |t| ^ 3 < 1 / 8) :
    ‖centeredCoordinateCharFactor a lam t -
        ((Real.exp (-coordinateVariance a lam * t ^ 2 / 2) : ℝ) : ℂ)‖ ≤
      coordinateThirdAbsMoment a lam * |t| ^ 3 / 2 := by
  let σ : ℝ := coordinateSigma a lam
  let v : ℝ := coordinateVariance a lam
  let β : ℝ := coordinateThirdAbsMoment a lam
  let y : ℝ := σ * |t|
  let x : ℝ := v * t ^ 2 / 2
  have hσ0 : 0 ≤ σ := by dsimp only [σ]; exact coordinateSigma_nonneg a lam
  have hβ0 : 0 ≤ β := by
    dsimp only [β, coordinateThirdAbsMoment]
    exact integral_nonneg fun _ ↦ by positivity
  have hy0 : 0 ≤ y := mul_nonneg hσ0 (abs_nonneg t)
  have hycube : y ^ 3 ≤ β * |t| ^ 3 := by
    have hmoment := coordinateThirdAbsMoment_lower a lam
    have hmul := mul_le_mul_of_nonneg_right hmoment (pow_nonneg (abs_nonneg t) 3)
    simpa only [σ, β, y, mul_pow] using hmul
  have hycube_lt : y ^ 3 < (1 / 2 : ℝ) ^ 3 := by
    calc
      y ^ 3 ≤ β * |t| ^ 3 := hycube
      _ < 1 / 8 := by simpa only [β] using hsmall
      _ = (1 / 2 : ℝ) ^ 3 := by norm_num
  have hy : y < 1 / 2 :=
    lt_of_pow_lt_pow_left₀ 3 (by norm_num) hycube_lt
  have hvty : v * t ^ 2 = y ^ 2 := by
    dsimp only [v, y, σ]
    rw [mul_pow, sq_abs, coordinateSigma_sq]
  have hvtsmall : v * t ^ 2 < 1 / 4 := by rw [hvty]; nlinarith [sq_nonneg y]
  have hx0 : 0 ≤ x := by
    dsimp only [x, v]
    exact div_nonneg (mul_nonneg (coordinateVariance_nonneg a lam) (sq_nonneg t))
      (by norm_num)
  have hxle : x ≤ 1 := by
    dsimp only [x]
    linarith
  have hexpReal :
      |Real.exp (-x) - 1 - (-x)| ≤ x ^ 2 := by
    have h := Real.norm_exp_sub_one_sub_id_le (x := -x) (by
      rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg hx0]
      exact hxle)
    simpa only [Real.norm_eq_abs, abs_neg, sq_abs] using h
  have hexpComplex :
      ‖(((1 - x : ℝ) : ℂ) - ((Real.exp (-x) : ℝ) : ℂ))‖ ≤ x ^ 2 := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    convert hexpReal using 1 <;> ring
  have hxSq : x ^ 2 ≤ β * |t| ^ 3 / 8 := by
    calc
      x ^ 2 = y ^ 3 * y / 4 := by
        rw [show x = y ^ 2 / 2 by dsimp only [x]; rw [hvty]]
        ring
      _ ≤ (β * |t| ^ 3) * (1 / 2) / 4 := by
        gcongr
      _ = β * |t| ^ 3 / 8 := by ring
  have hfactor := norm_centeredCoordinateCharFactor_sub_quadratic_le_sharp
    a lam t
  have hdecomp :
      centeredCoordinateCharFactor a lam t -
          ((Real.exp (-v * t ^ 2 / 2) : ℝ) : ℂ) =
        (centeredCoordinateCharFactor a lam t -
          ((1 : ℂ) - ((v * t ^ 2 / 2 : ℝ) : ℂ))) +
        (((1 - x : ℝ) : ℂ) - ((Real.exp (-x) : ℝ) : ℂ)) := by
    dsimp only [x]
    push_cast
    ring
  rw [hdecomp]
  calc
    ‖(centeredCoordinateCharFactor a lam t -
          ((1 : ℂ) - ((v * t ^ 2 / 2 : ℝ) : ℂ))) +
        (((1 - x : ℝ) : ℂ) - ((Real.exp (-x) : ℝ) : ℂ))‖ ≤
        ‖centeredCoordinateCharFactor a lam t -
          ((1 : ℂ) - ((v * t ^ 2 / 2 : ℝ) : ℂ))‖ +
        ‖(((1 - x : ℝ) : ℂ) - ((Real.exp (-x) : ℝ) : ℂ))‖ :=
      norm_add_le _ _
    _ ≤ |t| ^ 3 * β / 6 + x ^ 2 := by
      apply add_le_add
      · calc
          ‖centeredCoordinateCharFactor a lam t -
              ((1 : ℂ) - ((v * t ^ 2 / 2 : ℝ) : ℂ))‖ =
              ‖centeredCoordinateCharFactor a lam t -
                ((1 : ℂ) -
                  ((t ^ 2 * coordinateVariance a lam / 2 : ℝ) : ℂ))‖ := by
            congr 3
            dsimp only [v]
            push_cast
            ring
          _ ≤ |t| ^ 3 * coordinateThirdAbsMoment a lam / 6 := hfactor
          _ = |t| ^ 3 * β / 6 := by rfl
      · exact hexpComplex
    _ ≤ β * |t| ^ 3 / 6 + β * |t| ^ 3 / 8 := by
      calc
        |t| ^ 3 * β / 6 + x ^ 2 = β * |t| ^ 3 / 6 + x ^ 2 := by ring
        _ ≤ β * |t| ^ 3 / 6 + β * |t| ^ 3 / 8 :=
          add_le_add le_rfl hxSq
    _ ≤ β * |t| ^ 3 / 2 := by
      nlinarith [mul_nonneg hβ0 (by positivity : 0 ≤ |t| ^ 3)]
    _ = coordinateThirdAbsMoment a lam * |t| ^ 3 / 2 := by rfl

/-- Petrov's finite-product characteristic-function estimate in the exact
normalized form used by KSSS Lemma 5.5(a). -/
theorem norm_diagonalCenteredCharProduct_sub_standardNormalChar_le
    {ι : Type*} [Fintype ι] (a lam : ι → ℝ)
    (hsum : totalVariance a lam = 1)
    (hL : 0 < totalThirdAbsMoment a lam) (t : ℝ)
    (ht : |t| ≤ 1 / (4 * totalThirdAbsMoment a lam)) :
    ‖diagonalCenteredCharProduct a lam t - standardNormalChar t‖ ≤
      16 * totalThirdAbsMoment a lam * localCLTEnvelope t := by
  classical
  let L : ℝ := totalThirdAbsMoment a lam
  have hL0 : 0 ≤ L := hL.le
  have hLt : L * |t| ≤ 1 / 4 := by
    have hden : 0 < 4 * L := mul_pos (by norm_num) hL
    have h := (le_div_iff₀ hden).mp (by simpa only [L] using ht)
    nlinarith
  have hglobal : ‖diagonalCenteredCharProduct a lam t‖ ≤ Real.exp (-t ^ 2 / 3) :=
    norm_diagonalCenteredCharProduct_le_exp_neg_sq a lam hsum t hLt
  have hnormal : ‖standardNormalChar t‖ = Real.exp (-t ^ 2 / 2) := by
    rw [standardNormalChar, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  by_cases hlarge : 1 / 8 ≤ L * |t| ^ 3
  · calc
      ‖diagonalCenteredCharProduct a lam t - standardNormalChar t‖ ≤
          ‖diagonalCenteredCharProduct a lam t‖ + ‖standardNormalChar t‖ :=
        norm_sub_le _ _
      _ ≤ Real.exp (-t ^ 2 / 3) + Real.exp (-t ^ 2 / 2) :=
        add_le_add hglobal hnormal.le
      _ ≤ 2 * Real.exp (-t ^ 2 / 3) := by
        have hexp : Real.exp (-t ^ 2 / 2) ≤ Real.exp (-t ^ 2 / 3) := by
          apply Real.exp_le_exp.mpr
          nlinarith [sq_nonneg t]
        linarith
      _ ≤ 16 * L * (|t| ^ 3 * Real.exp (-t ^ 2 / 3)) := by
        have hmul := mul_le_mul_of_nonneg_right hlarge
          (show 0 ≤ Real.exp (-t ^ 2 / 3) by positivity)
        nlinarith
      _ = 16 * totalThirdAbsMoment a lam * localCLTEnvelope t := by
        dsimp only [L]
        rw [localCLTEnvelope]
  · have hq : L * |t| ^ 3 < 1 / 8 := lt_of_not_ge hlarge
    let f : ι → ℂ := fun i ↦ centeredCoordinateCharFactor (a i) (lam i) t
    let g : ι → ℂ := fun i ↦
      ((Real.exp (-coordinateVariance (a i) (lam i) * t ^ 2 / 2) : ℝ) : ℂ)
    let u : ι → ℝ := fun i ↦
      -coordinateVariance (a i) (lam i) * t ^ 2 / 2 +
        (2 / 3 : ℝ) * coordinateThirdAbsMoment (a i) (lam i) * |t| ^ 3
    have hβ0 (i : ι) : 0 ≤ coordinateThirdAbsMoment (a i) (lam i) := by
      unfold coordinateThirdAbsMoment
      exact integral_nonneg fun _ ↦ by positivity
    have hβle (i : ι) : coordinateThirdAbsMoment (a i) (lam i) ≤ L := by
      dsimp only [L, totalThirdAbsMoment]
      exact Finset.single_le_sum (fun j _ ↦ hβ0 j) (Finset.mem_univ i)
    have hβt (i : ι) :
        coordinateThirdAbsMoment (a i) (lam i) * |t| ^ 3 < 1 / 8 :=
      (mul_le_mul_of_nonneg_right (hβle i) (by positivity)).trans_lt hq
    have hvtsmall (i : ι) :
        coordinateVariance (a i) (lam i) * t ^ 2 < 1 / 4 :=
      coordinateVariance_mul_sq_lt_one_fourth (a i) (lam i) t (hβt i)
    have hfBound (i : ι) : ‖f i‖ ≤ Real.exp (u i) := by
      dsimp only [f, u]
      exact norm_centeredCoordinateCharFactor_le_exp (a i) (lam i) t
    have hgNorm (i : ι) :
        ‖g i‖ = Real.exp (-coordinateVariance (a i) (lam i) * t ^ 2 / 2) := by
      dsimp only [g]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hgBound (i : ι) : ‖g i‖ ≤ Real.exp (u i) := by
      rw [hgNorm]
      apply Real.exp_le_exp.mpr
      dsimp only [u]
      have hnonneg : 0 ≤ coordinateThirdAbsMoment (a i) (lam i) * |t| ^ 3 :=
        mul_nonneg (hβ0 i) (by positivity)
      nlinarith
    have hmaxBound (i : ι) : max ‖f i‖ ‖g i‖ ≤ Real.exp (u i) :=
      max_le (hfBound i) (hgBound i)
    have hprodBound (i : ι) :
        (∏ j ∈ (Finset.univ : Finset ι).erase i, max ‖f j‖ ‖g j‖) ≤
          3 * Real.exp (-t ^ 2 / 3) := by
      have hprod :
          (∏ j ∈ (Finset.univ : Finset ι).erase i, max ‖f j‖ ‖g j‖) ≤
            ∏ j ∈ (Finset.univ : Finset ι).erase i, Real.exp (u j) := by
        apply Finset.prod_le_prod
        · intro j hj
          positivity
        · intro j hj
          exact hmaxBound j
      have hvErase :
          (∑ j ∈ (Finset.univ : Finset ι).erase i,
              coordinateVariance (a j) (lam j)) =
            1 - coordinateVariance (a i) (lam i) := by
        have h := Finset.sum_erase_add (Finset.univ : Finset ι)
          (fun j ↦ coordinateVariance (a j) (lam j)) (Finset.mem_univ i)
        simp only [totalVariance] at hsum
        rw [hsum] at h
        linarith
      have hβErase :
          (∑ j ∈ (Finset.univ : Finset ι).erase i,
              coordinateThirdAbsMoment (a j) (lam j)) ≤ L := by
        simpa only [L, totalThirdAbsMoment] using
          (Finset.sum_le_univ_sum_of_nonneg (s :=
            (Finset.univ : Finset ι).erase i) hβ0)
      have hβEraseMul := mul_le_mul_of_nonneg_right hβErase (by positivity : 0 ≤ |t| ^ 3)
      have hsumU :
          (∑ j ∈ (Finset.univ : Finset ι).erase i, u j) =
            -(∑ j ∈ (Finset.univ : Finset ι).erase i,
                coordinateVariance (a j) (lam j)) * t ^ 2 / 2 +
              (2 / 3 : ℝ) *
                (∑ j ∈ (Finset.univ : Finset ι).erase i,
                  coordinateThirdAbsMoment (a j) (lam j)) * |t| ^ 3 := by
        dsimp only [u]
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [← Finset.sum_div, ← Finset.sum_mul, ← Finset.sum_neg_distrib]
        · rw [← Finset.sum_mul, ← Finset.mul_sum]
      have hexponent :
          (∑ j ∈ (Finset.univ : Finset ι).erase i, u j) ≤
            -t ^ 2 / 3 + 1 := by
        rw [hsumU, hvErase]
        nlinarith [sq_nonneg t, hvtsmall i]
      calc
        (∏ j ∈ (Finset.univ : Finset ι).erase i, max ‖f j‖ ‖g j‖) ≤
            ∏ j ∈ (Finset.univ : Finset ι).erase i, Real.exp (u j) := hprod
        _ = Real.exp (∑ j ∈ (Finset.univ : Finset ι).erase i, u j) := by
          rw [Real.exp_sum]
        _ ≤ Real.exp (-t ^ 2 / 3 + 1) := Real.exp_le_exp.mpr hexponent
        _ = Real.exp 1 * Real.exp (-t ^ 2 / 3) := by
          rw [add_comm, Real.exp_add]
        _ ≤ 3 * Real.exp (-t ^ 2 / 3) := by
          exact mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le (Real.exp_pos _).le
    have hlocal (i : ι) : ‖f i - g i‖ ≤
        coordinateThirdAbsMoment (a i) (lam i) * |t| ^ 3 / 2 := by
      dsimp only [f, g]
      exact norm_centeredCoordinateCharFactor_sub_gaussian_le
        (a i) (lam i) t (hβt i)
    have hprodg : (∏ i, g i) = standardNormalChar t := by
      dsimp only [g, standardNormalChar]
      have hreal :
          (∏ i, Real.exp (-coordinateVariance (a i) (lam i) * t ^ 2 / 2)) =
            Real.exp (-t ^ 2 / 2) := by
        rw [← Real.exp_sum]
        congr 1
        simp only [totalVariance] at hsum
        rw [← Finset.sum_div, ← Finset.sum_mul, Finset.sum_neg_distrib, hsum]
        ring
      exact_mod_cast hreal
    have hperturb := norm_finsetProd_sub_finsetProd_le
      (Finset.univ : Finset ι) f g
    have hmain :
        ‖diagonalCenteredCharProduct a lam t - standardNormalChar t‖ ≤
          ∑ i, (coordinateThirdAbsMoment (a i) (lam i) * |t| ^ 3 / 2) *
            (3 * Real.exp (-t ^ 2 / 3)) := by
      rw [diagonalCenteredCharProduct, ← hprodg]
      calc
        ‖(∏ i, f i) - ∏ i, g i‖ ≤
            ∑ i, ‖f i - g i‖ *
              ∏ j ∈ (Finset.univ : Finset ι).erase i, max ‖f j‖ ‖g j‖ := by
          exact hperturb
        _ ≤ ∑ i, (coordinateThirdAbsMoment (a i) (lam i) * |t| ^ 3 / 2) *
              (3 * Real.exp (-t ^ 2 / 3)) := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul (hlocal i) (hprodBound i) (by positivity)
            (div_nonneg (mul_nonneg (hβ0 i) (by positivity)) (by norm_num))
    calc
      ‖diagonalCenteredCharProduct a lam t - standardNormalChar t‖ ≤
          ∑ i, (coordinateThirdAbsMoment (a i) (lam i) * |t| ^ 3 / 2) *
            (3 * Real.exp (-t ^ 2 / 3)) := hmain
      _ = (3 / 2 : ℝ) * L * (|t| ^ 3 * Real.exp (-t ^ 2 / 3)) := by
        dsimp only [L, totalThirdAbsMoment]
        rw [show (fun i ↦
            (coordinateThirdAbsMoment (a i) (lam i) * |t| ^ 3 / 2) *
              (3 * Real.exp (-t ^ 2 / 3))) =
            fun i ↦ coordinateThirdAbsMoment (a i) (lam i) *
              ((3 / 2 : ℝ) * |t| ^ 3 * Real.exp (-t ^ 2 / 3)) by
          funext i
          ring]
        rw [← Finset.sum_mul]
        ring
      _ ≤ 16 * L * (|t| ^ 3 * Real.exp (-t ^ 2 / 3)) := by
        gcongr
        norm_num
      _ = 16 * totalThirdAbsMoment a lam * localCLTEnvelope t := by
        dsimp only [L]
        rw [localCLTEnvelope]

noncomputable instance centeredCoordinateLaw_isProbabilityMeasure (a lam : ℝ) :
    IsProbabilityMeasure (centeredCoordinateLaw a lam) := by
  unfold centeredCoordinateLaw
  exact Measure.isProbabilityMeasure_map
    (continuous_centeredCoordinatePolynomial a lam).aemeasurable

/-- The law of the sum of independent centered quadratic Gaussian
coordinates. -/
noncomputable def diagonalCenteredLaw {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) : Measure ℝ :=
  (Measure.pi fun i ↦ centeredCoordinateLaw (a i) (lam i)).map
    (fun x ↦ ∑ i, x i)

/-- The characteristic function of the diagonal quadratic Gaussian law is
the finite product used in the local-CLT and spectral-tail estimates. -/
theorem charFun_diagonalCenteredLaw {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) :
    charFun (diagonalCenteredLaw a lam) = diagonalCenteredCharProduct a lam := by
  rw [diagonalCenteredLaw, charFun_map_sum_pi_eq_prod]
  funext t
  unfold diagonalCenteredCharProduct
  rw [show (∏ i, charFun (centeredCoordinateLaw (a i) (lam i))) t =
      ∏ i, charFun (centeredCoordinateLaw (a i) (lam i)) t by
    simpa using Finset.prod_apply t (Finset.univ : Finset ι)
      (fun i ↦ charFun (centeredCoordinateLaw (a i) (lam i)))]
  apply Finset.prod_congr rfl
  intro i hi
  exact (centeredCoordinateCharFactor_eq_charFun (a i) (lam i) t).symm

theorem diagonalCenteredLaw_isProbabilityMeasure
    {ι : Type*} [Fintype ι] (a lam : ι → ℝ) :
    IsProbabilityMeasure (diagonalCenteredLaw a lam) := by
  unfold diagonalCenteredLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The real part of the inverse Fourier transform in the probability
normalization used throughout the Gaussian comparison.  For a Hermitian
function this is already the full (real-valued) inverse transform. -/
noncomputable def inverseFourierDensityCandidate (phi : ℝ → ℂ) (u : ℝ) : ℝ :=
  ((((2 * π : ℝ) : ℂ))⁻¹ *
    ∫ t : ℝ, phi t * Complex.exp
      (-(((t * u : ℝ) : ℂ) * Complex.I))).re

/-- A Hermitian Fourier integrand has a real inverse transform, so its real
part satisfies the exact complex inverse-Fourier identity. -/
theorem inverseFourierDensityCandidate_hasInverse
    {phi : ℝ → ℂ}
    (hherm : ∀ t, phi (-t) = starRingEnd ℂ (phi t)) :
    HasInverseFourierDensity (inverseFourierDensityCandidate phi) phi := by
  intro u
  let F : ℝ → ℂ := fun t ↦ phi t * Complex.exp
    (-(((t * u : ℝ) : ℂ) * Complex.I))
  let z : ℂ := (((2 * π : ℝ) : ℂ))⁻¹ * ∫ t : ℝ, F t
  have hconjF (t : ℝ) : starRingEnd ℂ (F t) = F (-t) := by
    dsimp only [F]
    rw [map_mul, ← Complex.exp_conj, ← hherm t]
    congr 1
    simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hint : starRingEnd ℂ (∫ t : ℝ, F t) = ∫ t : ℝ, F t := by
    rw [← integral_conj]
    calc
      (∫ t : ℝ, starRingEnd ℂ (F t)) = ∫ t : ℝ, F (-t) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hconjF
      _ = ∫ t : ℝ, F t := integral_neg_eq_self F volume
  have hz : starRingEnd ℂ z = z := by
    dsimp only [z]
    calc
      starRingEnd ℂ (((2 * π : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, F t) =
          (((2 * π : ℝ) : ℂ))⁻¹ * starRingEnd ℂ (∫ t : ℝ, F t) := by
        simp only [map_mul, map_inv₀, Complex.conj_ofReal]
      _ = (((2 * π : ℝ) : ℂ))⁻¹ * ∫ t : ℝ, F t := by rw [hint]
  have hre : ((z.re : ℝ) : ℂ) = z := Complex.conj_eq_iff_re.mp hz
  simpa only [inverseFourierDensityCandidate, F, z] using hre

lemma inverseFourierDensityCandidate_eq_fourier
    (phi : ℝ → ℂ) (u : ℝ) :
    inverseFourierDensityCandidate phi u =
      ((((2 * π : ℝ) : ℂ))⁻¹ * 𝓕 phi (u / (2 * π))).re := by
  unfold inverseFourierDensityCandidate
  rw [Real.fourier_real_eq_integral_exp_smul]
  congr 2
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t ↦ by
    change phi t * Complex.exp (-(((t * u : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (((-2 * π * t * (u / (2 * π)) : ℝ) : ℂ) * Complex.I) • phi t
    rw [smul_eq_mul, mul_comm]
    congr 1
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]

/-- The inverse-transform candidate is continuous whenever the Fourier-side
function is integrable. -/
theorem continuous_inverseFourierDensityCandidate
    {phi : ℝ → ℂ} (hphi : Integrable phi) :
    Continuous (inverseFourierDensityCandidate phi) := by
  have hFourier : Continuous (𝓕 phi) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hphi
  have harg : Continuous (fun u : ℝ ↦ u / (2 * π)) := by fun_prop
  have hcomplex : Continuous (fun u : ℝ ↦
      (((2 * π : ℝ) : ℂ))⁻¹ * 𝓕 phi (u / (2 * π))) :=
    continuous_const.mul (hFourier.comp harg)
  have hreal : Continuous (fun u : ℝ ↦
      ((((2 * π : ℝ) : ℂ))⁻¹ * 𝓕 phi (u / (2 * π))).re) :=
    Complex.continuous_re.comp hcomplex
  convert hreal using 1
  funext u
  exact inverseFourierDensityCandidate_eq_fourier phi u

lemma centeredCoordinateCharFactor_neg (a lam t : ℝ) :
    centeredCoordinateCharFactor a lam (-t) =
      starRingEnd ℂ (centeredCoordinateCharFactor a lam t) := by
  rw [centeredCoordinateCharFactor_eq_charFun_map,
    centeredCoordinateCharFactor_eq_charFun_map, charFun_neg]

lemma diagonalCenteredCharProduct_neg {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) (t : ℝ) :
    diagonalCenteredCharProduct a lam (-t) =
      starRingEnd ℂ (diagonalCenteredCharProduct a lam t) := by
  classical
  unfold diagonalCenteredCharProduct
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact centeredCoordinateCharFactor_neg (a i) (lam i) t

theorem inverseFourierDensityCandidate_diagonal_hasInverse
    {ι : Type*} [Fintype ι] (a lam : ι → ℝ) :
    HasInverseFourierDensity
      (inverseFourierDensityCandidate (diagonalCenteredCharProduct a lam))
      (diagonalCenteredCharProduct a lam) :=
  inverseFourierDensityCandidate_hasInverse
    (diagonalCenteredCharProduct_neg a lam)

/-- Claim 12.1's Gaussian density comparison with Petrov's local-CLT input
discharged.  The sole remaining analytic input is the inverse-Fourier density
identity for the centered quadratic Gaussian law. -/
theorem diagonalDensityComparison_of_four_le_spectralBlocks_of_inverseFourier
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a lam : ι → ℝ) (B : κ → Finset ι)
    (hcard : 4 ≤ Fintype.card κ)
    (hdisj : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset κ) : Set κ) B)
    {p : ℝ → ℝ} {s : ℝ}
    (hsum : totalVariance a lam = 1)
    (hs : 0 < s)
    (hblock : ∀ j, s ≤ ∑ i ∈ B j, (lam i) ^ 2)
    (hpInv : HasInverseFourierDensity p (diagonalCenteredCharProduct a lam))
    (u : ℝ) :
    |p u - standardNormalDensity u| ≤
      (2 * π)⁻¹ *
        (1280 / lyapunovGamma a lam +
          16 / (s * lyapunovGamma a lam)) := by
  apply diagonalDensityComparison_of_four_le_spectralBlocks
    a lam B hcard hdisj hsum hs hblock hpInv
  intro t ht
  have hLya : 0 < lyapunovL a lam :=
    lyapunovL_pos_of_coordinate_moments a lam hsum
      (fun i ↦ coordinateThirdAbsMoment_lower (a i) (lam i))
      (fun i ↦ coordinateThirdAbsMoment_upper (a i) (lam i))
  have hthird : 0 < totalThirdAbsMoment a lam := by
    rw [← lyapunovL_eq_totalThirdAbsMoment_of_normalized hsum]
    exact hLya
  rw [lyapunovL_eq_totalThirdAbsMoment_of_normalized hsum] at ht ⊢
  exact norm_diagonalCenteredCharProduct_sub_standardNormalChar_le
    a lam hsum hthird t ht

/-- The unconditional Fourier-analytic part of Claim 12.1: the inverse
transform candidate is uniformly close to the standard normal density under
four positive-mass spectral blocks.  Identifying this candidate with the
pushforward law is a separate measure-theoretic density step. -/
theorem inverseFourierDensityCandidate_comparison_of_four_le_spectralBlocks
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a lam : ι → ℝ) (B : κ → Finset ι)
    (hcard : 4 ≤ Fintype.card κ)
    (hdisj : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset κ) : Set κ) B)
    {s : ℝ}
    (hsum : totalVariance a lam = 1)
    (hs : 0 < s)
    (hblock : ∀ j, s ≤ ∑ i ∈ B j, (lam i) ^ 2)
    (u : ℝ) :
    |inverseFourierDensityCandidate (diagonalCenteredCharProduct a lam) u -
        standardNormalDensity u| ≤
      (2 * π)⁻¹ *
        (1280 / lyapunovGamma a lam +
          16 / (s * lyapunovGamma a lam)) := by
  exact diagonalDensityComparison_of_four_le_spectralBlocks_of_inverseFourier
    a lam B hcard hdisj hsum hs hblock
      (inverseFourierDensityCandidate_diagonal_hasInverse a lam) u

open Complex

/-- The inverse transform of a Gaussian frequency damping is the positive
Gaussian spatial kernel. -/
lemma gaussianDampedPhase_integral (c y : ℝ) (hc : 0 < c) :
    (((2 * π : ℝ) : ℂ))⁻¹ *
        (∫ t : ℝ, cexp ((((t * y : ℝ) : ℂ) * I)) *
          cexp (((-(t ^ 2 / (2 * c ^ 2)) : ℝ) : ℂ))) =
      ((c / √(2 * π) * rexp (-(c ^ 2 * y ^ 2) / 2) : ℝ) : ℂ) := by
  let g : ℝ → ℂ := fun s ↦ standardNormalChar s *
    cexp (-(((s * (-c * y) : ℝ) : ℂ) * I))
  have hcomp : (fun t : ℝ ↦ cexp ((((t * y : ℝ) : ℂ) * I)) *
        cexp (((-(t ^ 2 / (2 * c ^ 2)) : ℝ) : ℂ))) =
      fun t ↦ g (t / c) := by
    funext t
    dsimp only [g]
    rw [standardNormalChar, Complex.ofReal_exp]
    rw [mul_comm]
    congr 1
    · apply congrArg cexp
      push_cast
      field_simp [hc.ne']
    · apply congrArg cexp
      push_cast
      field_simp [hc.ne']
  rw [hcomp, Measure.integral_comp_div g c, abs_of_pos hc]
  change (((2 * π : ℝ) : ℂ))⁻¹ * ((c : ℂ) * ∫ s : ℝ, g s) = _
  have hInv := standardNormal_hasInverseFourierDensity (-c * y)
  have hInv' : ((standardNormalDensity (-c * y) : ℝ) : ℂ) =
      (((2 * π : ℝ) : ℂ))⁻¹ * ∫ s : ℝ, g s := by
    simpa only [g] using hInv
  calc
    (((2 * π : ℝ) : ℂ))⁻¹ * ((c : ℂ) * ∫ s : ℝ, g s) =
        (c : ℂ) * ((((2 * π : ℝ) : ℂ))⁻¹ * ∫ s : ℝ, g s) := by ring
    _ = (c : ℂ) * ((standardNormalDensity (-c * y) : ℝ) : ℂ) := by rw [← hInv']
    _ = _ := by
      unfold standardNormalDensity
      push_cast
      field_simp [Real.pi_ne_zero, (Real.sqrt_pos.2 (by positivity : 0 < 2 * π)).ne']

/-- Fubini form of Gaussian smoothing: a Gaussian-damped inverse transform
of a characteristic function is an integral of positive Gaussian kernels. -/
lemma gaussianDampedCharFun_inverse_eq_kernelIntegral
    (mu : Measure ℝ) [IsFiniteMeasure mu] (c u : ℝ) (hc : 0 < c) :
    (((2 * π : ℝ) : ℂ))⁻¹ *
        (∫ t : ℝ, charFun mu t *
          cexp (-(((t * u : ℝ) : ℂ) * I)) *
          cexp (((-(t ^ 2 / (2 * c ^ 2)) : ℝ) : ℂ))) =
      ∫ x : ℝ,
        ((c / √(2 * π) * rexp (-(c ^ 2 * (x - u) ^ 2) / 2) : ℝ) : ℂ) ∂mu := by
  let damp : ℝ → ℝ := fun t ↦ rexp (-(t ^ 2 / (2 * c ^ 2)))
  let F : ℝ → ℝ → ℂ := fun t x ↦
    cexp ((((t * x : ℝ) : ℂ) * I)) *
      cexp (-(((t * u : ℝ) : ℂ) * I)) * (damp t : ℂ)
  have hdamp : Integrable damp := by
    have hbase := integrable_exp_neg_mul_sq
      (show 0 < 1 / (2 * c ^ 2) by positivity)
    convert hbase using 1
    funext t
    dsimp only [damp]
    congr 1
    field_simp [hc.ne']
  have hFmeas : AEStronglyMeasurable (Function.uncurry F) (volume.prod mu) := by
    apply Continuous.aestronglyMeasurable
    dsimp only [F, damp, Function.uncurry_apply_pair]
    fun_prop
  have hF : Integrable (Function.uncurry F) (volume.prod mu) := by
    apply (hdamp.comp_fst mu).mono' hFmeas
    exact Filter.Eventually.of_forall fun z ↦ by
      change ‖F z.1 z.2‖ ≤ damp z.1
      dsimp only [F, damp, Function.uncurry_apply_pair]
      rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp,
        Complex.norm_real, Real.norm_eq_abs]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero,
        neg_re, Real.exp_zero, one_mul, abs_exp]
      simp
  have hexpand (t : ℝ) :
      charFun mu t * cexp (-(((t * u : ℝ) : ℂ) * I)) *
          cexp (((-(t ^ 2 / (2 * c ^ 2)) : ℝ) : ℂ)) =
        ∫ x : ℝ, F t x ∂mu := by
    rw [charFun_apply_real]
    dsimp only [F, damp]
    rw [Complex.ofReal_exp]
    calc
      (∫ x : ℝ, cexp ((t : ℂ) * (x : ℂ) * I) ∂mu) *
            cexp (-(((t * u : ℝ) : ℂ) * I)) *
            cexp (((-(t ^ 2 / (2 * c ^ 2)) : ℝ) : ℂ)) =
          (∫ x : ℝ, cexp ((t : ℂ) * (x : ℂ) * I) ∂mu) *
            (cexp (-(((t * u : ℝ) : ℂ) * I)) *
              cexp (((-(t ^ 2 / (2 * c ^ 2)) : ℝ) : ℂ))) := by ring
      _ = ∫ x : ℝ, cexp ((t : ℂ) * (x : ℂ) * I) *
            (cexp (-(((t * u : ℝ) : ℂ) * I)) *
              cexp (((-(t ^ 2 / (2 * c ^ 2)) : ℝ) : ℂ))) ∂mu := by
            rw [integral_mul_const]
      _ = ∫ x : ℝ, cexp ((((t * x : ℝ) : ℂ) * I)) *
            cexp (-(((t * u : ℝ) : ℂ) * I)) *
            cexp (((-(t ^ 2 / (2 * c ^ 2)) : ℝ) : ℂ)) ∂mu := by
            congr 1
            funext x
            push_cast
            ring
  calc
    (((2 * π : ℝ) : ℂ))⁻¹ *
        (∫ t : ℝ, charFun mu t *
          cexp (-(((t * u : ℝ) : ℂ) * I)) *
          cexp (((-(t ^ 2 / (2 * c ^ 2)) : ℝ) : ℂ))) =
        (((2 * π : ℝ) : ℂ))⁻¹ * ∫ t : ℝ, ∫ x : ℝ, F t x ∂mu := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hexpand
    _ = (((2 * π : ℝ) : ℂ))⁻¹ * ∫ x : ℝ, ∫ t : ℝ, F t x ∂volume ∂mu := by
      rw [integral_integral_swap hF]
    _ = ∫ x : ℝ, (((2 * π : ℝ) : ℂ))⁻¹ *
          (∫ t : ℝ, F t x) ∂mu := by
      rw [integral_const_mul]
    _ = ∫ x : ℝ,
        ((c / √(2 * π) * rexp (-(c ^ 2 * (x - u) ^ 2) / 2) : ℝ) : ℂ) ∂mu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        change (((2 * π : ℝ) : ℂ))⁻¹ * (∫ t : ℝ, F t x) =
          ((c / √(2 * π) * rexp (-(c ^ 2 * (x - u) ^ 2) / 2) : ℝ) : ℂ)
        rw [← gaussianDampedPhase_integral c (x - u) hc]
        congr 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun t ↦ by
          dsimp only [F, damp]
          rw [Complex.ofReal_exp, ← Complex.exp_add]
          congr 1
          push_cast
          ring

lemma tendsto_gaussianDamping (t : ℝ) :
    Filter.Tendsto
      (fun n : ℕ ↦ Real.exp (-(t ^ 2 / (2 * ((n : ℝ) + 1) ^ 2))))
      Filter.atTop (nhds 1) := by
  have hc : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) + 1)
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hsq : Filter.Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) ^ 2)
      Filter.atTop Filter.atTop := by
    simpa only [pow_two] using hc.atTop_mul_atTop₀ hc
  have hden : Filter.Tendsto (fun n : ℕ ↦ 2 * ((n : ℝ) + 1) ^ 2)
      Filter.atTop Filter.atTop :=
    hsq.const_mul_atTop (by norm_num)
  have hquot : Filter.Tendsto
      (fun n : ℕ ↦ t ^ 2 / (2 * ((n : ℝ) + 1) ^ 2))
      Filter.atTop (nhds 0) := hden.const_div_atTop (t ^ 2)
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hquot.neg
  change Filter.Tendsto
    (fun n : ℕ ↦ Real.exp (-(t ^ 2 / (2 * ((n : ℝ) + 1) ^ 2))))
    Filter.atTop (nhds (Real.exp (-0))) at hexp
  simpa only [neg_zero, Real.exp_zero] using hexp

/-- If a finite measure has integrable characteristic function, its inverse
Fourier density candidate is pointwise nonnegative.  This is the positivity
part of the density inversion theorem, proved by Gaussian smoothing. -/
theorem inverseFourierDensityCandidate_charFun_nonneg
    (mu : Measure ℝ) [IsFiniteMeasure mu]
    (hchar : Integrable (charFun mu)) (u : ℝ) :
    0 ≤ inverseFourierDensityCandidate (charFun mu) u := by
  let F : ℕ → ℝ → ℂ := fun n t ↦
    charFun mu t * cexp (-(((t * u : ℝ) : ℂ) * I)) *
      cexp (((-(t ^ 2 / (2 * ((n : ℝ) + 1) ^ 2)) : ℝ) : ℂ))
  let f : ℝ → ℂ := fun t ↦
    charFun mu t * cexp (-(((t * u : ℝ) : ℂ) * I))
  have hFmeas (n : ℕ) : AEStronglyMeasurable (F n) := by
    apply AEStronglyMeasurable.mul
    · exact hchar.aestronglyMeasurable.mul (by fun_prop)
    · apply Continuous.aestronglyMeasurable
      fun_prop
  have hbound (n : ℕ) : ∀ᵐ t : ℝ, ‖F n t‖ ≤ ‖charFun mu t‖ :=
    Filter.Eventually.of_forall fun t ↦ by
      dsimp only [F]
      rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, mul_zero, sub_zero,
        neg_re, neg_zero, Real.exp_zero, mul_one]
      have hnpos : -(t ^ 2 / (2 * ((n : ℝ) + 1) ^ 2)) ≤ 0 := by
        exact neg_nonpos.mpr (div_nonneg (sq_nonneg t) (by positivity))
      calc
        ‖charFun mu t‖ * Real.exp (-(t ^ 2 / (2 * ((n : ℝ) + 1) ^ 2))) ≤
            ‖charFun mu t‖ * 1 := by
          gcongr
          exact Real.exp_le_one_iff.mpr hnpos
        _ = ‖charFun mu t‖ := mul_one _
  have hlim : ∀ᵐ t : ℝ,
      Filter.Tendsto (fun n ↦ F n t) Filter.atTop (nhds (f t)) :=
    Filter.Eventually.of_forall fun t ↦ by
      have hdampR := tendsto_gaussianDamping t
      have hdampC := Complex.continuous_ofReal.continuousAt.tendsto.comp hdampR
      have hdamp : Filter.Tendsto
          (fun n : ℕ ↦
            cexp (((-(t ^ 2 / (2 * ((n : ℝ) + 1) ^ 2)) : ℝ) : ℂ)))
          Filter.atTop (nhds 1) := by
        change Filter.Tendsto
          (fun n : ℕ ↦
            ((Real.exp (-(t ^ 2 / (2 * ((n : ℝ) + 1) ^ 2))) : ℝ) : ℂ))
          Filter.atTop (nhds ((1 : ℝ) : ℂ)) at hdampC
        simpa only [Complex.ofReal_exp, Complex.ofReal_one] using hdampC
      have hconst : Filter.Tendsto
          (fun _ : ℕ ↦ charFun mu t * cexp (-(((t * u : ℝ) : ℂ) * I)))
          Filter.atTop
          (nhds (charFun mu t * cexp (-(((t * u : ℝ) : ℂ) * I)))) :=
        tendsto_const_nhds
      simpa only [F, f, mul_one] using hconst.mul hdamp
  have hint : Filter.Tendsto (fun n ↦ ∫ t : ℝ, F n t)
      Filter.atTop (nhds (∫ t : ℝ, f t)) :=
    tendsto_integral_of_dominated_convergence
      (fun t ↦ ‖charFun mu t‖) hFmeas hchar.norm hbound hlim
  have hz : Filter.Tendsto
      (fun n ↦ (((2 * π : ℝ) : ℂ))⁻¹ * ∫ t : ℝ, F n t)
      Filter.atTop
      (nhds ((((2 * π : ℝ) : ℂ))⁻¹ * ∫ t : ℝ, f t)) :=
    tendsto_const_nhds.mul hint
  have hre : Filter.Tendsto
      (fun n ↦ ((((2 * π : ℝ) : ℂ))⁻¹ * ∫ t : ℝ, F n t).re)
      Filter.atTop
      (nhds (inverseFourierDensityCandidate (charFun mu) u)) := by
    have h := Complex.continuous_re.continuousAt.tendsto.comp hz
    change Filter.Tendsto
      (fun n ↦ ((((2 * π : ℝ) : ℂ))⁻¹ * ∫ t : ℝ, F n t).re)
      Filter.atTop
      (nhds (((((2 * π : ℝ) : ℂ))⁻¹ * ∫ t : ℝ, f t).re)) at h
    simpa only [inverseFourierDensityCandidate, f] using h
  apply ge_of_tendsto' hre
  intro n
  have hnpos : 0 < (n : ℝ) + 1 := by positivity
  have heq := gaussianDampedCharFun_inverse_eq_kernelIntegral
    mu ((n : ℝ) + 1) u hnpos
  have hkernel : 0 ≤ ∫ x : ℝ,
      ((n : ℝ) + 1) / √(2 * π) *
        Real.exp (-(((n : ℝ) + 1) ^ 2 * (x - u) ^ 2) / 2) ∂mu := by
    apply integral_nonneg
    intro x
    positivity
  have hreEq := congrArg Complex.re heq
  dsimp only [F]
  rw [hreEq]
  rw [integral_complex_ofReal]
  exact hkernel

end GaussianQuadratic
end Erdos88
