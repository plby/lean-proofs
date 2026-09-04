import ErdosProblems.Erdos88.GaussianSpectralTail
import ErdosProblems.Erdos88.Invariance

open scoped BigOperators
open MeasureTheory ProbabilityTheory Real

namespace Erdos88
namespace GaussianQuadratic

lemma deriv_standardGaussian_mgf_four :
    deriv (fun t : ℝ ↦ (3 + 6 * t ^ 2 + t ^ 4) * Real.exp (t ^ 2 / 2)) =
      fun t ↦ (15 * t + 10 * t ^ 3 + t ^ 5) * Real.exp (t ^ 2 / 2) := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by fun_prop), _root_.deriv_exp (by fun_prop)]
  rw [deriv_fun_add (by fun_prop) (by fun_prop),
    deriv_fun_add (by fun_prop) (by fun_prop), deriv_const,
    deriv_fun_mul (by fun_prop) (by fun_prop), deriv_const,
    deriv_fun_pow (by fun_prop) 2, deriv_id'',
    deriv_fun_pow (by fun_prop) 4, deriv_id'', deriv_div_const,
    deriv_fun_pow (by fun_prop) 2, deriv_id'']
  ring

lemma deriv_standardGaussian_mgf_five :
    deriv (fun t : ℝ ↦ (15 * t + 10 * t ^ 3 + t ^ 5) * Real.exp (t ^ 2 / 2)) =
      fun t ↦ (15 + 45 * t ^ 2 + 15 * t ^ 4 + t ^ 6) *
        Real.exp (t ^ 2 / 2) := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by fun_prop), _root_.deriv_exp (by fun_prop)]
  rw [deriv_fun_add (by fun_prop) (by fun_prop),
    deriv_fun_add (by fun_prop) (by fun_prop),
    deriv_fun_mul (by fun_prop) (by fun_prop), deriv_const, deriv_id'',
    deriv_fun_mul (by fun_prop) (by fun_prop), deriv_const,
    deriv_fun_pow (by fun_prop) 3, deriv_id'',
    deriv_fun_pow (by fun_prop) 5, deriv_id'', deriv_div_const,
    deriv_fun_pow (by fun_prop) 2, deriv_id'']
  ring

lemma deriv_standardGaussian_mgf_six :
    deriv (fun t : ℝ ↦ (15 + 45 * t ^ 2 + 15 * t ^ 4 + t ^ 6) *
      Real.exp (t ^ 2 / 2)) =
      fun t ↦ (105 * t + 105 * t ^ 3 + 21 * t ^ 5 + t ^ 7) *
        Real.exp (t ^ 2 / 2) := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by fun_prop), _root_.deriv_exp (by fun_prop)]
  rw [deriv_fun_add (by fun_prop) (by fun_prop),
    deriv_fun_add (by fun_prop) (by fun_prop),
    deriv_fun_add (by fun_prop) (by fun_prop), deriv_const,
    deriv_fun_mul (by fun_prop) (by fun_prop), deriv_const,
    deriv_fun_pow (by fun_prop) 2, deriv_id'',
    deriv_fun_mul (by fun_prop) (by fun_prop), deriv_const,
    deriv_fun_pow (by fun_prop) 4, deriv_id'',
    deriv_fun_pow (by fun_prop) 6, deriv_id'', deriv_div_const,
    deriv_fun_pow (by fun_prop) 2, deriv_id'']
  ring

lemma deriv_standardGaussian_mgf_seven :
    deriv (fun t : ℝ ↦ (105 * t + 105 * t ^ 3 + 21 * t ^ 5 + t ^ 7) *
      Real.exp (t ^ 2 / 2)) =
      fun t ↦ (105 + 420 * t ^ 2 + 210 * t ^ 4 + 28 * t ^ 6 + t ^ 8) *
        Real.exp (t ^ 2 / 2) := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by fun_prop), _root_.deriv_exp (by fun_prop)]
  rw [deriv_fun_add (by fun_prop) (by fun_prop),
    deriv_fun_add (by fun_prop) (by fun_prop),
    deriv_fun_add (by fun_prop) (by fun_prop),
    deriv_fun_mul (by fun_prop) (by fun_prop), deriv_const, deriv_id'',
    deriv_fun_mul (by fun_prop) (by fun_prop), deriv_const,
    deriv_fun_pow (by fun_prop) 3, deriv_id'',
    deriv_fun_mul (by fun_prop) (by fun_prop), deriv_const,
    deriv_fun_pow (by fun_prop) 5, deriv_id'',
    deriv_fun_pow (by fun_prop) 7, deriv_id'', deriv_div_const,
    deriv_fun_pow (by fun_prop) 2, deriv_id'']
  ring

@[simp] lemma standardGaussian_moment_five :
    ∫ x : ℝ, x ^ 5 ∂standardGaussian = 0 := by
  rw [Invariance.standardGaussian_moment_eq_iteratedDeriv]
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
    iteratedDeriv_succ, iteratedDeriv_one,
    Invariance.deriv_standardGaussian_mgf,
    Invariance.deriv_standardGaussian_mgf_one,
    Invariance.deriv_standardGaussian_mgf_two,
    Invariance.deriv_standardGaussian_mgf_three,
    deriv_standardGaussian_mgf_four]
  norm_num

@[simp] lemma standardGaussian_moment_six :
    ∫ x : ℝ, x ^ 6 ∂standardGaussian = 15 := by
  rw [Invariance.standardGaussian_moment_eq_iteratedDeriv]
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
    iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one,
    Invariance.deriv_standardGaussian_mgf,
    Invariance.deriv_standardGaussian_mgf_one,
    Invariance.deriv_standardGaussian_mgf_two,
    Invariance.deriv_standardGaussian_mgf_three,
    deriv_standardGaussian_mgf_four, deriv_standardGaussian_mgf_five]
  norm_num

@[simp] lemma standardGaussian_moment_seven :
    ∫ x : ℝ, x ^ 7 ∂standardGaussian = 0 := by
  rw [Invariance.standardGaussian_moment_eq_iteratedDeriv]
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
    iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one,
    Invariance.deriv_standardGaussian_mgf,
    Invariance.deriv_standardGaussian_mgf_one,
    Invariance.deriv_standardGaussian_mgf_two,
    Invariance.deriv_standardGaussian_mgf_three,
    deriv_standardGaussian_mgf_four, deriv_standardGaussian_mgf_five,
    deriv_standardGaussian_mgf_six]
  norm_num

@[simp] lemma standardGaussian_moment_eight :
    ∫ x : ℝ, x ^ 8 ∂standardGaussian = 105 := by
  rw [Invariance.standardGaussian_moment_eq_iteratedDeriv]
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
    iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
    iteratedDeriv_succ, iteratedDeriv_one,
    Invariance.deriv_standardGaussian_mgf,
    Invariance.deriv_standardGaussian_mgf_one,
    Invariance.deriv_standardGaussian_mgf_two,
    Invariance.deriv_standardGaussian_mgf_three,
    deriv_standardGaussian_mgf_four, deriv_standardGaussian_mgf_five,
    deriv_standardGaussian_mgf_six, deriv_standardGaussian_mgf_seven]
  norm_num

lemma continuous_centeredCoordinatePolynomial (a lam : ℝ) :
    Continuous (centeredCoordinatePolynomial a lam) := by
  unfold centeredCoordinatePolynomial
  fun_prop

lemma centeredCoordinatePolynomial_fourth_integrable (a lam : ℝ) :
    Integrable (fun x : ℝ ↦ centeredCoordinatePolynomial a lam x ^ 4)
      standardGaussian := by
  let X : ℝ → ℝ := fun x ↦ a * x
  let U : ℝ → ℝ := fun x ↦ x ^ 2
  let V : ℝ → ℝ := fun _ ↦ -1
  let Y : ℝ → ℝ := fun x ↦ lam * (x ^ 2 - 1)
  have hXmeas : AEStronglyMeasurable X standardGaussian := by
    exact (continuous_const.mul continuous_id).aestronglyMeasurable
  have hUmeas : AEStronglyMeasurable U standardGaussian := by
    exact (continuous_id.pow 2).aestronglyMeasurable
  have hVmeas : AEStronglyMeasurable V standardGaussian :=
    aestronglyMeasurable_const
  have hYmeas : AEStronglyMeasurable Y standardGaussian := by
    exact (continuous_const.mul ((continuous_id.pow 2).sub continuous_const)).aestronglyMeasurable
  have hX4 : Integrable (fun x ↦ X x ^ 4) standardGaussian := by
    convert (Invariance.integrable_pow_standardGaussian 4).const_mul (a ^ 4) using 1 <;>
      funext x <;> simp only [X] <;> ring
  have hU4 : Integrable (fun x ↦ U x ^ 4) standardGaussian := by
    convert Invariance.integrable_pow_standardGaussian 8 using 1 <;>
      funext x <;> simp only [U] <;> ring
  have hV4 : Integrable (fun x ↦ V x ^ 4) standardGaussian := by
    convert (integrable_const (1 : ℝ) :
      Integrable (fun _ : ℝ ↦ (1 : ℝ)) standardGaussian) using 1 <;>
      funext x <;> norm_num [V]
  have hUV4 : Integrable (fun x ↦ (U x + V x) ^ 4) standardGaussian :=
    Invariance.integrable_add_pow_four hUmeas hVmeas hU4 hV4
  have hY4 : Integrable (fun x ↦ Y x ^ 4) standardGaussian := by
    convert hUV4.const_mul (lam ^ 4) using 1 <;>
      funext x <;> simp only [Y, U, V] <;> ring
  have hsum := Invariance.integrable_add_pow_four hXmeas hYmeas hX4 hY4
  exact hsum.congr (Filter.Eventually.of_forall fun x ↦ by
    simp only [X, Y, centeredCoordinatePolynomial])

theorem coordinateSecondMoment_eq (a lam : ℝ) :
    ∫ x : ℝ, centeredCoordinatePolynomial a lam x ^ 2 ∂standardGaussian =
      coordinateVariance a lam := by
  let f4 : ℝ → ℝ := fun x ↦ lam ^ 2 * x ^ 4
  let f3 : ℝ → ℝ := fun x ↦ (2 * a * lam) * x ^ 3
  let f2 : ℝ → ℝ := fun x ↦ (a ^ 2 - 2 * lam ^ 2) * x ^ 2
  let f1 : ℝ → ℝ := fun x ↦ (-2 * a * lam) * x ^ 1
  let f0 : ℝ → ℝ := fun _ ↦ lam ^ 2
  have h4 : Integrable f4 standardGaussian :=
    (Invariance.integrable_pow_standardGaussian 4).const_mul _
  have h3 : Integrable f3 standardGaussian :=
    (Invariance.integrable_pow_standardGaussian 3).const_mul _
  have h2 : Integrable f2 standardGaussian :=
    (Invariance.integrable_pow_standardGaussian 2).const_mul _
  have h1 : Integrable f1 standardGaussian :=
    (Invariance.integrable_pow_standardGaussian 1).const_mul _
  have h0 : Integrable f0 standardGaussian := integrable_const _
  have integral_add_fun (f g : ℝ → ℝ)
      (hf : Integrable f standardGaussian)
      (hg : Integrable g standardGaussian) :
      integral standardGaussian (f + g) =
        integral standardGaussian f + integral standardGaussian g := by
    change (∫ x : ℝ, f x + g x ∂standardGaussian) = _
    exact integral_add hf hg
  have hexpand : (fun x : ℝ ↦ centeredCoordinatePolynomial a lam x ^ 2) =
      fun x ↦ f4 x + (f3 x + (f2 x + (f1 x + f0 x))) := by
    funext x
    simp only [centeredCoordinatePolynomial, f4, f3, f2, f1, f0]
    ring
  rw [hexpand]
  rw [show (fun x ↦ f4 x + (f3 x + (f2 x + (f1 x + f0 x)))) =
      f4 + (f3 + (f2 + (f1 + f0))) by rfl]
  rw [integral_add_fun f4 _ h4 (h3.add (h2.add (h1.add h0)))]
  rw [integral_add_fun f3 _ h3 (h2.add (h1.add h0))]
  rw [integral_add_fun f2 _ h2 (h1.add h0)]
  rw [integral_add_fun f1 f0 h1 h0]
  simp only [f4, f3, f2, f1, f0, integral_const_mul, integral_const,
    Invariance.standardGaussian_moment_one,
    Invariance.standardGaussian_moment_two,
    Invariance.standardGaussian_moment_three,
    Invariance.standardGaussian_moment_four]
  simp only [mul_zero, mul_one, neg_mul, probReal_univ, smul_eq_mul, one_mul, zero_add]
  unfold coordinateVariance
  ring

/-- Exact fourth moment of one centered quadratic Gaussian coordinate. -/
theorem coordinateFourthMoment_eq (a lam : ℝ) :
    ∫ x : ℝ, centeredCoordinatePolynomial a lam x ^ 4 ∂standardGaussian =
      3 * a ^ 4 + 60 * a ^ 2 * lam ^ 2 + 60 * lam ^ 4 := by
  let f8 : ℝ → ℝ := fun x ↦ lam ^ 4 * x ^ 8
  let f7 : ℝ → ℝ := fun x ↦ (4 * a * lam ^ 3) * x ^ 7
  let f6 : ℝ → ℝ := fun x ↦ (6 * a ^ 2 * lam ^ 2 - 4 * lam ^ 4) * x ^ 6
  let f5 : ℝ → ℝ := fun x ↦ (4 * a ^ 3 * lam - 12 * a * lam ^ 3) * x ^ 5
  let f4 : ℝ → ℝ := fun x ↦ (a ^ 4 - 12 * a ^ 2 * lam ^ 2 + 6 * lam ^ 4) * x ^ 4
  let f3 : ℝ → ℝ := fun x ↦ (-4 * a ^ 3 * lam + 12 * a * lam ^ 3) * x ^ 3
  let f2 : ℝ → ℝ := fun x ↦ (6 * a ^ 2 * lam ^ 2 - 4 * lam ^ 4) * x ^ 2
  let f1 : ℝ → ℝ := fun x ↦ (-4 * a * lam ^ 3) * x ^ 1
  let f0 : ℝ → ℝ := fun _ ↦ lam ^ 4
  have h8 : Integrable f8 standardGaussian :=
    (Invariance.integrable_pow_standardGaussian 8).const_mul _
  have h7 : Integrable f7 standardGaussian :=
    (Invariance.integrable_pow_standardGaussian 7).const_mul _
  have h6 : Integrable f6 standardGaussian :=
    (Invariance.integrable_pow_standardGaussian 6).const_mul _
  have h5 : Integrable f5 standardGaussian :=
    (Invariance.integrable_pow_standardGaussian 5).const_mul _
  have h4 : Integrable f4 standardGaussian :=
    (Invariance.integrable_pow_standardGaussian 4).const_mul _
  have h3 : Integrable f3 standardGaussian :=
    (Invariance.integrable_pow_standardGaussian 3).const_mul _
  have h2 : Integrable f2 standardGaussian :=
    (Invariance.integrable_pow_standardGaussian 2).const_mul _
  have h1 : Integrable f1 standardGaussian :=
    (Invariance.integrable_pow_standardGaussian 1).const_mul _
  have h0 : Integrable f0 standardGaussian := integrable_const _
  have integral_add_fun (f g : ℝ → ℝ)
      (hf : Integrable f standardGaussian)
      (hg : Integrable g standardGaussian) :
      integral standardGaussian (f + g) =
        integral standardGaussian f + integral standardGaussian g := by
    change (∫ x : ℝ, f x + g x ∂standardGaussian) = _
    exact integral_add hf hg
  have hexpand : (fun x : ℝ ↦ centeredCoordinatePolynomial a lam x ^ 4) =
      fun x ↦ f8 x + (f7 x + (f6 x + (f5 x + (f4 x +
        (f3 x + (f2 x + (f1 x + f0 x))))))) := by
    funext x
    simp only [centeredCoordinatePolynomial, f8, f7, f6, f5, f4, f3, f2, f1, f0]
    ring
  rw [hexpand]
  rw [show (fun x ↦ f8 x + (f7 x + (f6 x + (f5 x + (f4 x +
    (f3 x + (f2 x + (f1 x + f0 x)))))))) =
      f8 + (f7 + (f6 + (f5 + (f4 + (f3 + (f2 + (f1 + f0))))))) by rfl]
  rw [integral_add_fun f8 _ h8 (h7.add (h6.add (h5.add (h4.add
    (h3.add (h2.add (h1.add h0)))))))]
  rw [integral_add_fun f7 _ h7
    (h6.add (h5.add (h4.add (h3.add (h2.add (h1.add h0))))))]
  rw [integral_add_fun f6 _ h6
    (h5.add (h4.add (h3.add (h2.add (h1.add h0)))))]
  rw [integral_add_fun f5 _ h5 (h4.add (h3.add (h2.add (h1.add h0))))]
  rw [integral_add_fun f4 _ h4 (h3.add (h2.add (h1.add h0)))]
  rw [integral_add_fun f3 _ h3 (h2.add (h1.add h0))]
  rw [integral_add_fun f2 _ h2 (h1.add h0)]
  rw [integral_add_fun f1 f0 h1 h0]
  simp only [f8, f7, f6, f5, f4, f3, f2, f1, f0,
    integral_const_mul, integral_const,
    Invariance.standardGaussian_moment_one,
    Invariance.standardGaussian_moment_two,
    Invariance.standardGaussian_moment_three,
    Invariance.standardGaussian_moment_four,
    standardGaussian_moment_five, standardGaussian_moment_six,
    standardGaussian_moment_seven, standardGaussian_moment_eight]
  simp
  ring

theorem coordinateFourthMoment_le (a lam : ℝ) :
    ∫ x : ℝ, centeredCoordinatePolynomial a lam x ^ 4 ∂standardGaussian ≤
      15 * coordinateVariance a lam ^ 2 := by
  rw [coordinateFourthMoment_eq]
  unfold coordinateVariance
  nlinarith [sq_nonneg (a ^ 2)]

theorem coordinateThirdAbsMoment_upper (a lam : ℝ) :
    coordinateThirdAbsMoment a lam ≤
      8 * coordinateSigma a lam ^ 3 := by
  let X : ℝ → ℝ := centeredCoordinatePolynomial a lam
  have hXm : AEStronglyMeasurable X standardGaussian :=
    (continuous_centeredCoordinatePolynomial a lam).aestronglyMeasurable
  have hX4 : Integrable (fun x ↦ X x ^ 4) standardGaussian :=
    centeredCoordinatePolynomial_fourth_integrable a lam
  have hX2 : Integrable (fun x ↦ X x ^ 2) standardGaussian :=
    Erdos1028.integrable_pow_of_integrable_pow_four hXm hX4 2 (by norm_num)
  have habsMeas : AEStronglyMeasurable (fun x ↦ |X x|) standardGaussian :=
    by simpa only [Real.norm_eq_abs] using hXm.norm
  have hsqMeas : AEStronglyMeasurable (fun x ↦ X x ^ 2) standardGaussian :=
    hXm.pow 2
  have habs2 : Integrable (fun x ↦ |X x| ^ 2) standardGaussian :=
    hX2.congr (Filter.Eventually.of_forall fun x ↦ (sq_abs (X x)).symm)
  have hsq2 : Integrable (fun x ↦ (X x ^ 2) ^ 2) standardGaussian :=
    hX4.congr (Filter.Eventually.of_forall fun x ↦ by ring)
  have hfmem : MemLp (fun x ↦ |X x|) 2 standardGaussian :=
    (memLp_two_iff_integrable_sq habsMeas).2 habs2
  have hgmem : MemLp (fun x ↦ X x ^ 2) 2 standardGaussian :=
    (memLp_two_iff_integrable_sq hsqMeas).2 hsq2
  have hfmem' : MemLp (fun x ↦ |X x|) (ENNReal.ofReal (2 : ℝ))
      standardGaussian := by simpa using hfmem
  have hgmem' : MemLp (fun x ↦ X x ^ 2) (ENNReal.ofReal (2 : ℝ))
      standardGaussian := by simpa using hgmem
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun x ↦ abs_nonneg (X x))
    (Filter.Eventually.of_forall fun x ↦ sq_nonneg (X x)) hfmem' hgmem'
  have hholderNat :
      (∫ x, |X x| * X x ^ 2 ∂standardGaussian) ≤
        (∫ x, |X x| ^ (2 : ℕ) ∂standardGaussian) ^ (1 / (2 : ℝ)) *
          (∫ x, (X x ^ 2) ^ (2 : ℕ) ∂standardGaussian) ^ (1 / (2 : ℝ)) := by
    simpa only [Real.rpow_two] using hholder
  have hleft : (∫ x, |X x| * X x ^ 2 ∂standardGaussian) =
      ∫ x, |X x| ^ 3 ∂standardGaussian := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ by
      change |X x| * X x ^ 2 = |X x| ^ 3
      rw [← sq_abs]
      ring
  have hright1 : (∫ x, |X x| ^ 2 ∂standardGaussian) =
      ∫ x, X x ^ 2 ∂standardGaussian := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ sq_abs (X x)
  have hright2 : (∫ x, (X x ^ 2) ^ 2 ∂standardGaussian) =
      ∫ x, X x ^ 4 ∂standardGaussian := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ by ring
  have hholder' :
      ∫ x, |X x| ^ 3 ∂standardGaussian ≤
        √(∫ x, X x ^ 2 ∂standardGaussian) *
          √(∫ x, X x ^ 4 ∂standardGaussian) := by
    calc
      (∫ x, |X x| ^ 3 ∂standardGaussian) =
          ∫ x, |X x| * X x ^ 2 ∂standardGaussian := hleft.symm
      _ ≤ (∫ x, |X x| ^ 2 ∂standardGaussian) ^ (1 / (2 : ℝ)) *
          (∫ x, (X x ^ 2) ^ 2 ∂standardGaussian) ^ (1 / (2 : ℝ)) := hholderNat
      _ = _ := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
        exact congrArg₂ (fun u v : ℝ ↦ u * v)
          (congrArg (fun z : ℝ ↦ z ^ (1 / (2 : ℝ))) hright1)
          (congrArg (fun z : ℝ ↦ z ^ (1 / (2 : ℝ))) hright2)
  have hsecond : ∫ x, X x ^ 2 ∂standardGaussian =
      coordinateVariance a lam := coordinateSecondMoment_eq a lam
  have hfourth : ∫ x, X x ^ 4 ∂standardGaussian ≤
      15 * coordinateVariance a lam ^ 2 := coordinateFourthMoment_le a lam
  have hsqrt4 : √(∫ x, X x ^ 4 ∂standardGaussian) ≤
      4 * coordinateVariance a lam := by
    rw [Real.sqrt_le_iff]
    constructor
    · exact mul_nonneg (by norm_num) (coordinateVariance_nonneg a lam)
    · have hv := coordinateVariance_nonneg a lam
      nlinarith
  unfold coordinateThirdAbsMoment
  change (∫ x, |X x| ^ 3 ∂standardGaussian) ≤ _
  calc
    (∫ x, |X x| ^ 3 ∂standardGaussian) ≤
        √(∫ x, X x ^ 2 ∂standardGaussian) *
          √(∫ x, X x ^ 4 ∂standardGaussian) := hholder'
    _ ≤ √(coordinateVariance a lam) *
          (4 * coordinateVariance a lam) := by
      rw [hsecond]
      exact mul_le_mul_of_nonneg_left hsqrt4 (Real.sqrt_nonneg _)
    _ = 4 * coordinateSigma a lam ^ 3 := by
      rw [show √(coordinateVariance a lam) = coordinateSigma a lam by rfl,
        ← coordinateSigma_sq]
      ring
    _ ≤ 8 * coordinateSigma a lam ^ 3 := by
      nlinarith [pow_nonneg (coordinateSigma_nonneg a lam) 3]

theorem coordinateThirdAbsMoment_lower (a lam : ℝ) :
    coordinateSigma a lam ^ 3 ≤ coordinateThirdAbsMoment a lam := by
  let X : ℝ → ℝ := centeredCoordinatePolynomial a lam
  have hXm : AEStronglyMeasurable X standardGaussian :=
    (continuous_centeredCoordinatePolynomial a lam).aestronglyMeasurable
  have hX4 : Integrable (fun x ↦ X x ^ 4) standardGaussian :=
    centeredCoordinatePolynomial_fourth_integrable a lam
  have hX4norm : Integrable (fun x ↦ ‖X x‖ ^ 4) standardGaussian :=
    hX4.congr (Filter.Eventually.of_forall fun x ↦ by
      change X x ^ 4 = |X x| ^ 4
      rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ X x ^ 4)])
  have hX3norm : Integrable (fun x ↦ ‖X x‖ ^ 3) standardGaussian :=
    integrable_norm_pow_of_le hXm (by norm_num) hX4norm
  have hmem3 : MemLp X 3 standardGaussian := by
    apply (integrable_norm_rpow_iff hXm (by norm_num) (by norm_num)).mp
    simpa using hX3norm
  have hmem2 : MemLp X 2 standardGaussian :=
    hmem3.mono_exponent (by norm_num)
  have hlp := eLpNorm_le_eLpNorm_of_exponent_le
    (f := X) (μ := standardGaussian) (by norm_num : (2 : ENNReal) ≤ 3) hXm
  rw [hmem2.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    hmem3.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)] at hlp
  have hm3 : 0 ≤ ∫ x, ‖X x‖ ^ 3 ∂standardGaussian :=
    integral_nonneg fun x ↦ pow_nonneg (norm_nonneg _) 3
  have hroot :
      (∫ x, ‖X x‖ ^ 2 ∂standardGaussian) ^ (1 / (2 : ℝ)) ≤
        (∫ x, ‖X x‖ ^ 3 ∂standardGaussian) ^ (1 / (3 : ℝ)) := by
    apply (ENNReal.ofReal_le_ofReal_iff
      (Real.rpow_nonneg hm3 (1 / (3 : ℝ)))).mp
    simpa using hlp
  have hnorm2 : (∫ x, ‖X x‖ ^ 2 ∂standardGaussian) =
      coordinateVariance a lam := by
    calc
      (∫ x, ‖X x‖ ^ 2 ∂standardGaussian) =
          ∫ x, X x ^ 2 ∂standardGaussian := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x ↦ by
          change |X x| ^ 2 = X x ^ 2
          exact sq_abs (X x)
      _ = coordinateVariance a lam := coordinateSecondMoment_eq a lam
  have hnorm3 : (∫ x, ‖X x‖ ^ 3 ∂standardGaussian) =
      coordinateThirdAbsMoment a lam := by
    unfold coordinateThirdAbsMoment
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ by
      change |X x| ^ 3 = |centeredCoordinatePolynomial a lam x| ^ 3
      rfl
  rw [hnorm2, hnorm3] at hroot
  have hroot' : coordinateSigma a lam ≤
      coordinateThirdAbsMoment a lam ^ (1 / (3 : ℝ)) := by
    simpa only [coordinateSigma, Real.sqrt_eq_rpow] using hroot
  have hcube := pow_le_pow_left₀ (coordinateSigma_nonneg a lam) hroot' 3
  have hm3' : 0 ≤ coordinateThirdAbsMoment a lam := by
    rw [← hnorm3]
    exact hm3
  have hrootCube :
      (coordinateThirdAbsMoment a lam ^ (1 / (3 : ℝ))) ^ 3 =
        coordinateThirdAbsMoment a lam := by
    convert Real.rpow_inv_natCast_pow hm3' (by norm_num : (3 : ℕ) ≠ 0) using 1 <;>
      norm_num
  rw [hrootCube] at hcube
  exact hcube

theorem coordinateThirdAbsMoment_bounds (a lam : ℝ) :
    coordinateSigma a lam ^ 3 ≤ coordinateThirdAbsMoment a lam ∧
      coordinateThirdAbsMoment a lam ≤ 8 * coordinateSigma a lam ^ 3 :=
  ⟨coordinateThirdAbsMoment_lower a lam, coordinateThirdAbsMoment_upper a lam⟩

theorem lyapunov_parameter_bounds_of_gaussian_coordinates
    {ι : Type*} [Fintype ι] (a lam : ι → ℝ)
    (hsum : totalVariance a lam = 1) :
    1 / lyapunovGamma a lam ≤ lyapunovL a lam ∧
      lyapunovL a lam ≤ 8 / lyapunovGamma a lam := by
  exact lyapunov_parameter_bounds_of_coordinate_moments a lam hsum
    (fun i ↦ coordinateThirdAbsMoment_lower (a i) (lam i))
    (fun i ↦ coordinateThirdAbsMoment_upper (a i) (lam i))

/-- Claim 12.1's Gaussian density comparison after discharging all coordinate
moment hypotheses.  What remains explicit is precisely the pointwise local
CLT estimate and the inverse-Fourier identity for the quadratic law. -/
theorem diagonalDensityComparison_of_four_le_spectralBlocks
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
    (hstandard : ∀ t : ℝ, |t| ≤ 1 / (4 * lyapunovL a lam) →
      ‖diagonalCenteredCharProduct a lam t - standardNormalChar t‖ ≤
        16 * lyapunovL a lam * localCLTEnvelope t)
    (u : ℝ) :
    |p u - standardNormalDensity u| ≤
      (2 * π)⁻¹ *
        (1280 / lyapunovGamma a lam +
          16 / (s * lyapunovGamma a lam)) := by
  exact diagonalDensityComparison_of_coordinateMoments_of_four_le_spectralBlocks
    a lam B hcard hdisj hsum
      (fun i ↦ coordinateThirdAbsMoment_lower (a i) (lam i))
      (fun i ↦ coordinateThirdAbsMoment_upper (a i) (lam i))
      hs hblock hpInv hstandard u

end GaussianQuadratic
end Erdos88
