import ErdosProblems.Erdos88.GraphQuadraticScale
import ErdosProblems.Erdos88.SliceGaussianComparison

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace Erdos88
namespace BooleanSlices

open Classical Finset Invariance

lemma hybridEval_memLp_two {n t : ℕ} (i : Fin n) :
    MemLp (fun x : Fin n → ℝ ↦ x i) 2 (hybridMeasure n t) := by
  let hi := hybridEval_hasReplacementMoments (t := t) i
  apply (memLp_two_iff_integrable_sq hi.measurable.aestronglyMeasurable).2
  exact Erdos1028.integrable_pow_of_integrable_pow_four
    hi.measurable.aestronglyMeasurable hi.integrable_fourth 2 (by norm_num)

lemma hybridEval_mul_memLp_two {n t : ℕ} (i j : Fin n) :
    MemLp (fun x : Fin n → ℝ ↦ x i * x j) 2 (hybridMeasure n t) := by
  let hi := hybridEval_hasReplacementMoments (t := t) i
  let hj := hybridEval_hasReplacementMoments (t := t) j
  apply (memLp_two_iff_integrable_sq (by fun_prop)).2
  apply (hi.integrable_fourth.add hj.integrable_fourth).mono'
  · fun_prop
  · exact Filter.Eventually.of_forall fun x ↦ by
      change ‖(x i * x j) ^ 2‖ ≤ x i ^ 4 + x j ^ 4
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hsq : 0 ≤ (x i ^ 2 - x j ^ 2) ^ 2 := sq_nonneg _
      nlinarith [sq_nonneg (x i ^ 2), sq_nonneg (x j ^ 2)]

lemma quadraticCoeffs_eval_memLp_two {n t : ℕ} (q : QuadraticCoeffs n) :
    MemLp q.eval 2 (hybridMeasure n t) := by
  have hconst : MemLp (fun _x : Fin n → ℝ ↦ q.constant) 2
      (hybridMeasure n t) := memLp_const _
  have hlinear : MemLp (fun x : Fin n → ℝ ↦
      ∑ i, q.linear i * x i) 2 (hybridMeasure n t) := by
    have h := memLp_finsetSum' Finset.univ (fun i _ ↦
      (hybridEval_memLp_two (t := t) i).const_mul (q.linear i))
    convert h using 1
    funext x
    simp only [Finset.sum_apply]
  have hpair : ∀ i j : Fin n,
      MemLp (fun x : Fin n → ℝ ↦ q.symPair i j * x i * x j) 2
        (hybridMeasure n t) := by
    intro i j
    simpa only [mul_assoc] using
      (hybridEval_mul_memLp_two (t := t) i j).const_mul (q.symPair i j)
  have hquad : MemLp (fun x : Fin n → ℝ ↦
      ∑ i, ∑ j, q.symPair i j * x i * x j) 2 (hybridMeasure n t) := by
    have hi : ∀ i : Fin n, MemLp (fun x : Fin n → ℝ ↦
        ∑ j, q.symPair i j * x i * x j) 2 (hybridMeasure n t) := by
      intro i
      have h := memLp_finsetSum' Finset.univ (fun j _ ↦ hpair i j)
      convert h using 1
      funext x
      simp only [Finset.sum_apply]
    have h := memLp_finsetSum' Finset.univ (fun i _ ↦ hi i)
    convert h using 1
    funext x
    simp only [Finset.sum_apply]
  have htotal := (hconst.add hlinear).add (hquad.const_mul (1 / 2 : ℝ))
  convert htotal using 1
  funext x
  rfl

/-- Squared evaluations of a multilinear quadratic are integrable throughout
the Rademacher-to-Gaussian replacement chain. -/
lemma quadraticCoeffs_eval_sq_integrable {n t : ℕ} (q : QuadraticCoeffs n) :
    Integrable (fun x ↦ q.eval x ^ 2) (hybridMeasure n t) := by
  exact (memLp_two_iff_integrable_sq q.measurable_eval.aestronglyMeasurable).1
    (quadraticCoeffs_eval_memLp_two (t := t) q)

lemma integral_affine_sq_rademacher (a s : ℝ) :
    (∫ x, (a + s * x) ^ 2 ∂rademacherMeasure) = a ^ 2 + s ^ 2 := by
  have h0 : Integrable (fun _x : ℝ ↦ a ^ 2) rademacherMeasure :=
    integrable_const _
  have h1 : Integrable (fun x : ℝ ↦ 2 * a * s * x) rademacherMeasure :=
    by simpa using (integrable_pow_rademacher 1).const_mul (2 * a * s)
  have h2 : Integrable (fun x : ℝ ↦ s ^ 2 * x ^ 2) rademacherMeasure :=
    (integrable_pow_rademacher 2).const_mul (s ^ 2)
  have hi1 : (∫ x : ℝ, a ^ 2 + 2 * a * s * x ∂rademacherMeasure) =
      (∫ _x : ℝ, a ^ 2 ∂rademacherMeasure) +
        ∫ x : ℝ, 2 * a * s * x ∂rademacherMeasure := by
    simpa only [Pi.add_apply] using integral_add h0 h1
  have hi2 :
      (∫ x : ℝ, (a ^ 2 + 2 * a * s * x) + s ^ 2 * x ^ 2
        ∂rademacherMeasure) =
      (∫ x : ℝ, a ^ 2 + 2 * a * s * x ∂rademacherMeasure) +
        ∫ x : ℝ, s ^ 2 * x ^ 2 ∂rademacherMeasure := by
    simpa only [Pi.add_apply] using integral_add (h0.add h1) h2
  calc
    (∫ x, (a + s * x) ^ 2 ∂rademacherMeasure) =
        ∫ x, (a ^ 2 + 2 * a * s * x) + s ^ 2 * x ^ 2
          ∂rademacherMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by ring
    _ = a ^ 2 + s ^ 2 := by
      rw [hi2, hi1,
        integral_const, measureReal_def, integral_const_mul,
        integral_const_mul, integral_id_rademacher, integral_sq_rademacher]
      simp

lemma integral_affine_sq_standardGaussian (a s : ℝ) :
    (∫ x, (a + s * x) ^ 2 ∂standardGaussian) = a ^ 2 + s ^ 2 := by
  have h0 : Integrable (fun _x : ℝ ↦ a ^ 2) standardGaussian :=
    integrable_const _
  have h1 : Integrable (fun x : ℝ ↦ 2 * a * s * x) standardGaussian :=
    by simpa using (integrable_pow_standardGaussian 1).const_mul (2 * a * s)
  have h2 : Integrable (fun x : ℝ ↦ s ^ 2 * x ^ 2) standardGaussian :=
    (integrable_pow_standardGaussian 2).const_mul (s ^ 2)
  have hi1 : (∫ x : ℝ, a ^ 2 + 2 * a * s * x ∂standardGaussian) =
      (∫ _x : ℝ, a ^ 2 ∂standardGaussian) +
        ∫ x : ℝ, 2 * a * s * x ∂standardGaussian := by
    simpa only [Pi.add_apply] using integral_add h0 h1
  have hi2 :
      (∫ x : ℝ, (a ^ 2 + 2 * a * s * x) + s ^ 2 * x ^ 2
        ∂standardGaussian) =
      (∫ x : ℝ, a ^ 2 + 2 * a * s * x ∂standardGaussian) +
        ∫ x : ℝ, s ^ 2 * x ^ 2 ∂standardGaussian := by
    simpa only [Pi.add_apply] using integral_add (h0.add h1) h2
  have hm1 : (∫ x : ℝ, x ∂standardGaussian) = 0 := by
    simpa only [pow_one] using standardGaussian_moment_one
  calc
    (∫ x, (a + s * x) ^ 2 ∂standardGaussian) =
        ∫ x, (a ^ 2 + 2 * a * s * x) + s ^ 2 * x ^ 2
          ∂standardGaussian := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by ring
    _ = a ^ 2 + s ^ 2 := by
      rw [hi2, hi1,
        integral_const, measureReal_def, integral_const_mul,
        integral_const_mul, hm1, standardGaussian_moment_two]
      simp

/-- Replacing one Rademacher coordinate by a standard Gaussian preserves the
second moment of every multilinear quadratic exactly. -/
theorem hybrid_step_quadratic_sq_eq {n : ℕ} (q : QuadraticCoeffs (n + 1))
    (t : Fin (n + 1)) :
    (∫ x, q.eval x ^ 2 ∂hybridMeasure (n + 1) t.val) =
      ∫ x, q.eval x ^ 2 ∂hybridMeasure (n + 1) (t.val + 1) := by
  let split := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) t
  let g : ℝ × (Fin n → ℝ) → ℝ := fun p ↦
    (q.coordinateBase t p.2 + q.coordinateSlope t p.2 * p.1) ^ 2
  let Fr : (Fin n → ℝ) → ℝ := fun y ↦
    ∫ z, (q.coordinateBase t y + q.coordinateSlope t y * z) ^ 2
      ∂rademacherMeasure
  let Fg : (Fin n → ℝ) → ℝ := fun y ↦
    ∫ z, (q.coordinateBase t y + q.coordinateSlope t y * z) ^ 2
      ∂standardGaussian
  have hcomp : (fun x ↦ q.eval x ^ 2) = g ∘ split := by
    funext x
    dsimp only [g, Function.comp_apply]
    congr 1
    calc
      q.eval x = q.eval (split.symm (split x)) := by rw [split.symm_apply_apply]
      _ = q.coordinateBase t (split x).2 +
          q.coordinateSlope t (split x).2 * (split x).1 := by
        exact q.eval_piFinSuccAbove t (split x).1 (split x).2
  have hfullRad := quadraticCoeffs_eval_sq_integrable (t := t.val) q
  have hfullGauss := quadraticCoeffs_eval_sq_integrable (t := t.val + 1) q
  have hpairRad : Integrable g
      (rademacherMeasure.prod (hybridMeasure n t.val)) := by
    apply ((hybridMeasure_split_rademacher t).integrable_comp_emb
      split.measurableEmbedding).mp
    rw [← hcomp]
    exact hfullRad
  have hpairGauss : Integrable g
      (standardGaussian.prod (hybridMeasure n t.val)) := by
    apply ((hybridMeasure_split_gaussian t).integrable_comp_emb
      split.measurableEmbedding).mp
    rw [← hcomp]
    exact hfullGauss
  have hrad : (∫ x, q.eval x ^ 2 ∂hybridMeasure (n + 1) t.val) =
      ∫ y, Fr y ∂hybridMeasure n t.val := by
    calc
      (∫ x, q.eval x ^ 2 ∂hybridMeasure (n + 1) t.val) =
          ∫ x, g (split x) ∂hybridMeasure (n + 1) t.val := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x ↦ congrFun hcomp x
      _ = ∫ p, g p ∂rademacherMeasure.prod (hybridMeasure n t.val) :=
        (hybridMeasure_split_rademacher t).integral_comp' g
      _ = ∫ y, Fr y ∂hybridMeasure n t.val := by
        simpa [g, Fr] using integral_prod_symm g hpairRad
  have hgauss : (∫ x, q.eval x ^ 2
      ∂hybridMeasure (n + 1) (t.val + 1)) =
      ∫ y, Fg y ∂hybridMeasure n t.val := by
    calc
      (∫ x, q.eval x ^ 2 ∂hybridMeasure (n + 1) (t.val + 1)) =
          ∫ x, g (split x) ∂hybridMeasure (n + 1) (t.val + 1) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x ↦ congrFun hcomp x
      _ = ∫ p, g p ∂standardGaussian.prod (hybridMeasure n t.val) :=
        (hybridMeasure_split_gaussian t).integral_comp' g
      _ = ∫ y, Fg y ∂hybridMeasure n t.val := by
        simpa [g, Fg] using integral_prod_symm g hpairGauss
  rw [hrad, hgauss]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y ↦ by
    rw [show Fr y = q.coordinateBase t y ^ 2 + q.coordinateSlope t y ^ 2 by
      exact integral_affine_sq_rademacher _ _]
    rw [show Fg y = q.coordinateBase t y ^ 2 + q.coordinateSlope t y ^ 2 by
      exact integral_affine_sq_standardGaussian _ _]

/-- The Rademacher and Gaussian product laws give exactly the same second
moment to a multilinear quadratic polynomial. -/
theorem quadratic_secondMoment_rademacher_eq_gaussian {n : ℕ}
    (q : QuadraticCoeffs n) :
    (∫ x, q.eval x ^ 2 ∂rademacherProductMeasure n) =
      ∫ x, q.eval x ^ 2 ∂gaussianProductMeasure n := by
  rw [← hybridMeasure_zero n,
    ← hybridMeasure_eq_gaussian n n le_rfl]
  let A : ℕ → ℝ := fun t ↦ ∫ x, q.eval x ^ 2 ∂hybridMeasure n t
  have htel := telescoping_abs A n
  have hzero : (∑ i : Fin n, |A i.val - A (i.val + 1)|) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [show A i.val = A (i.val + 1) by
      cases n with
      | zero => exact Fin.elim0 i
      | succ m => exact hybrid_step_quadratic_sq_eq q i]
    simp
  rw [hzero] at htel
  have hz : |A 0 - A n| = 0 := le_antisymm htel (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp hz)

lemma quadraticCoeffs_eval_memLp_two_gaussian {n : ℕ}
    (q : QuadraticCoeffs n) :
    MemLp q.eval 2 (gaussianProductMeasure n) := by
  rw [← hybridMeasure_eq_gaussian n n le_rfl]
  exact quadraticCoeffs_eval_memLp_two (t := n) q

/-- Exact Gaussian second moment of the centered multilinearization of a
symmetric quadratic form. -/
lemma integral_sq_multilinearCenteredQuadratic {n : ℕ}
    (F : Fin n → Fin n → ℝ) (hF : ∀ i j, F i j = F j i) :
    (∫ x, (toQuadraticCoeffs (-trace F) (fun _ ↦ 0) F).eval x ^ 2
      ∂gaussianProductMeasure n) =
      2 * frobeniusSq F - 2 * ∑ i, F i i ^ 2 := by
  let q := toQuadraticCoeffs (-trace F) (fun _ ↦ 0) F
  have hrad : (∫ x, q.eval x ^ 2 ∂rademacherProductMeasure n) =
      uniformExpectation (fun S : Finset (Fin n) ↦
        sliceQuadratic (-trace F) (fun _ ↦ 0) F S ^ 2) := by
    change rademacherIntegralExpectation (fun x ↦ q.eval x ^ 2) = _
    rw [rademacherIntegralExpectation_eq _ (by
      exact q.measurable_eval.pow_const 2)]
    rw [rademacherExpectation_eq_uniformFinset]
    apply uniformExpectation_congr
    intro S
    simp only [q, toQuadraticCoeffs_eval_signOfSet]
  have hvar := rademacher_sliceQuadratic_variance_symmetric
    (-trace F) (fun _ ↦ 0) F hF
  have hfinite : uniformExpectation (fun S : Finset (Fin n) ↦
      sliceQuadratic (-trace F) (fun _ ↦ 0) F S ^ 2) =
      2 * frobeniusSq F - 2 * ∑ i, F i i ^ 2 := by
    rw [uniformVariance, rademacher_sliceQuadratic_mean] at hvar
    simpa [vectorSqNorm] using hvar
  change (∫ x, q.eval x ^ 2 ∂gaussianProductMeasure n) = _
  rw [← quadratic_secondMoment_rademacher_eq_gaussian q, hrad, hfinite]

lemma integral_sq_multilinearCenteredQuadratic_of_diagonal_zero {n : ℕ}
    (F : Fin n → Fin n → ℝ) (hF : ∀ i j, F i j = F j i)
    (hdiag : ∀ i, F i i = 0) :
    (∫ x, (toQuadraticCoeffs (-trace F) (fun _ ↦ 0) F).eval x ^ 2
      ∂gaussianProductMeasure n) = 2 * frobeniusSq F := by
  rw [integral_sq_multilinearCenteredQuadratic F hF]
  simp [hdiag]

/-- The centered multilinear Gaussian quadratic has `L¹` norm at most its
exact `L²` norm. -/
lemma integral_abs_multilinearCenteredQuadratic_le {n : ℕ}
    (F : Fin n → Fin n → ℝ) (hF : ∀ i j, F i j = F j i)
    (hdiag : ∀ i, F i i = 0) :
    (∫ x, |(toQuadraticCoeffs (-trace F) (fun _ ↦ 0) F).eval x|
      ∂gaussianProductMeasure n) ≤ √(2 * frobeniusSq F) := by
  let q := toQuadraticCoeffs (-trace F) (fun _ ↦ 0) F
  have hq : MemLp q.eval (ENNReal.ofReal (2 : ℝ))
      (gaussianProductMeasure n) := by
    norm_num
    exact quadraticCoeffs_eval_memLp_two_gaussian q
  have hOne : MemLp (fun _x : Fin n → ℝ ↦ (1 : ℝ))
      (ENNReal.ofReal (2 : ℝ)) (gaussianProductMeasure n) := by
    norm_num
    exact memLp_const 1
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    Real.HolderConjugate.two_two hq hOne
  have hsecond := integral_sq_multilinearCenteredQuadratic_of_diagonal_zero
    F hF hdiag
  change (∫ x, |q.eval x| ∂gaussianProductMeasure n) ≤ _
  calc
    (∫ x, |q.eval x| ∂gaussianProductMeasure n) =
        ∫ x, ‖q.eval x‖ * ‖(1 : ℝ)‖ ∂gaussianProductMeasure n := by
      simp [Real.norm_eq_abs]
    _ ≤ (∫ x, ‖q.eval x‖ ^ (2 : ℝ) ∂gaussianProductMeasure n) ^
          (1 / (2 : ℝ)) *
        (∫ _x : Fin n → ℝ, ‖(1 : ℝ)‖ ^ (2 : ℝ)
          ∂gaussianProductMeasure n) ^ (1 / (2 : ℝ)) := hholder
    _ = √(2 * frobeniusSq F) := by
      rw [show (∫ x, ‖q.eval x‖ ^ (2 : ℝ) ∂gaussianProductMeasure n) =
          2 * frobeniusSq F by
        simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs, q] using hsecond]
      simp [integral_const, measureReal_def, Real.sqrt_eq_rpow]

/-- Characteristic function of an affine linear form in independent standard
Gaussians. -/
noncomputable def gaussianLinearCharacteristic {n : ℕ}
    (f₀ : ℝ) (f : Fin n → ℝ) (t : ℝ) : ℂ :=
  ∫ x, Complex.exp ((((t * (f₀ + linearPart f x) : ℝ) : ℂ) * Complex.I))
    ∂gaussianProductMeasure n

lemma gaussianLinearCharacteristic_eq {n : ℕ}
    (f₀ : ℝ) (f : Fin n → ℝ) (t : ℝ) :
    gaussianLinearCharacteristic f₀ f t =
      Complex.exp ((((t * f₀ : ℝ) : ℂ) * Complex.I) -
        ((t ^ 2 * vectorSqNorm f / 2 : ℝ) : ℂ)) := by
  unfold gaussianLinearCharacteristic gaussianProductMeasure
  have hpoint : (fun x : Fin n → ℝ ↦
      Complex.exp ((((t * (f₀ + linearPart f x) : ℝ) : ℂ) * Complex.I))) =
      fun x ↦ Complex.exp ((((t * f₀ : ℝ) : ℂ) * Complex.I)) *
        ∏ i, Complex.exp (((((t * f i) * x i : ℝ) : ℂ) * Complex.I)) := by
    funext x
    rw [show t * (f₀ + linearPart f x) = t * f₀ + ∑ i, (t * f i) * x i by
      simp only [linearPart, mul_add, Finset.mul_sum, mul_assoc]]
    push_cast
    rw [add_mul, Complex.exp_add]
    simp_rw [Finset.sum_mul, Complex.exp_sum]
  rw [hpoint, integral_const_mul,
    integral_fintype_prod_eq_prod
      (fun i x ↦ Complex.exp (((((t * f i) * x : ℝ) : ℂ) * Complex.I)))]
  have hcoord (i : Fin n) :
      (∫ x : ℝ, Complex.exp (((((t * f i) * x : ℝ) : ℂ) * Complex.I))
          ∂standardGaussian) =
        Complex.exp (-(((t * f i) ^ 2 / 2 : ℝ) : ℂ)) := by
    calc
      (∫ x : ℝ, Complex.exp (((((t * f i) * x : ℝ) : ℂ) * Complex.I))
          ∂standardGaussian) = charFun standardGaussian (t * f i) := by
        rw [charFun_apply_real]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x ↦ by
          push_cast
          ring
      _ = Complex.exp (-(((t * f i) ^ 2 / 2 : ℝ) : ℂ)) := by
        rw [charFun_gaussianReal]
        congr 1
        push_cast
        ring
  simp_rw [hcoord]
  rw [← Complex.exp_sum, ← Complex.exp_add]
  congr 1
  rw [sub_eq_add_neg]
  congr 1
  have hsum : (∑ i, -((t * f i) ^ 2 / 2)) =
      -(t ^ 2 * vectorSqNorm f / 2) := by
    simp only [vectorSqNorm]
    rw [Finset.sum_neg_distrib]
    congr 1
    rw [Finset.mul_sum]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  calc
    (∑ i, -((((t * f i) ^ 2 / 2 : ℝ) : ℂ))) =
        (((∑ i, -((t * f i) ^ 2 / 2)) : ℝ) : ℂ) := by
          push_cast
          rfl
    _ = ((-(t ^ 2 * vectorSqNorm f / 2) : ℝ) : ℂ) := by rw [hsum]
    _ = -(((t ^ 2 * vectorSqNorm f / 2 : ℝ) : ℂ)) := by
      push_cast
      rfl

/-- The real/imaginary definition of the Gaussian quadratic characteristic
function is the ordinary complex exponential integral. -/
lemma gaussianQuadraticCharacteristic_eq_integral {n : ℕ}
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ) (t : ℝ) :
    gaussianQuadraticCharacteristic f₀ f F t =
      ∫ x, Complex.exp ((((t * quadraticPolynomial f₀ f F x : ℝ) : ℂ) *
        Complex.I)) ∂gaussianProductMeasure n := by
  have hpoly : Measurable (fun x : Fin n → ℝ ↦
      quadraticPolynomial f₀ f F x) := by
    simp only [quadraticPolynomial, linearPart, quadraticPart]
    fun_prop
  have hcos : Integrable (fun x : Fin n → ℝ ↦
      Real.cos (t * quadraticPolynomial f₀ f F x))
      (gaussianProductMeasure n) := by
    apply (integrable_const (1 : ℝ)).mono'
    · exact (hpoly.const_mul t).cos.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x ↦ by
        simpa only [Real.norm_eq_abs] using
          Real.abs_cos_le_one (t * quadraticPolynomial f₀ f F x)
  have hsin : Integrable (fun x : Fin n → ℝ ↦
      Real.sin (t * quadraticPolynomial f₀ f F x))
      (gaussianProductMeasure n) := by
    apply (integrable_const (1 : ℝ)).mono'
    · exact (hpoly.const_mul t).sin.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x ↦ by
        simpa only [Real.norm_eq_abs] using
          Real.abs_sin_le_one (t * quadraticPolynomial f₀ f F x)
  unfold gaussianQuadraticCharacteristic gaussianExpectation
  calc
    ((∫ x : Fin n → ℝ, Real.cos (t * quadraticPolynomial f₀ f F x)
        ∂gaussianProductMeasure n : ℝ) : ℂ) +
        ((∫ x : Fin n → ℝ, Real.sin (t * quadraticPolynomial f₀ f F x)
          ∂gaussianProductMeasure n : ℝ) : ℂ) * Complex.I =
        (∫ x : Fin n → ℝ,
          (Real.cos (t * quadraticPolynomial f₀ f F x) : ℂ)
          ∂gaussianProductMeasure n) +
        (∫ x : Fin n → ℝ,
          (Real.sin (t * quadraticPolynomial f₀ f F x) : ℂ)
          ∂gaussianProductMeasure n) * Complex.I := by
      congr 1
      · exact (integral_ofReal (𝕜 := ℂ)
          (f := fun x : Fin n → ℝ ↦
            Real.cos (t * quadraticPolynomial f₀ f F x))).symm
      · congr 1
        exact (integral_ofReal (𝕜 := ℂ)
          (f := fun x : Fin n → ℝ ↦
            Real.sin (t * quadraticPolynomial f₀ f F x))).symm
    _ = ∫ x : Fin n → ℝ,
          (Real.cos (t * quadraticPolynomial f₀ f F x) : ℂ) +
          (Real.sin (t * quadraticPolynomial f₀ f F x) : ℂ) * Complex.I
          ∂gaussianProductMeasure n := by
      rw [← integral_mul_const]
      exact (integral_add hcos.ofReal
        (hsin.ofReal.mul_const Complex.I)).symm
    _ = ∫ x : Fin n → ℝ,
          Complex.exp ((((t * quadraticPolynomial f₀ f F x : ℝ) : ℂ) *
            Complex.I)) ∂gaussianProductMeasure n := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        change (Real.cos (t * quadraticPolynomial f₀ f F x) : ℂ) +
            (Real.sin (t * quadraticPolynomial f₀ f F x) : ℂ) * Complex.I =
          Complex.exp (((t * quadraticPolynomial f₀ f F x : ℝ) : ℂ) *
            Complex.I)
        exact (Complex.exp_ofReal_mul_I _).symm

/-- For a symmetric zero-diagonal quadratic form, deleting the quadratic
part changes its Gaussian characteristic function by at most the sharp `L²`
size of that part. -/
lemma norm_gaussianQuadraticCharacteristic_sub_linear_le {n : ℕ}
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (hF : ∀ i j, F i j = F j i) (hdiag : ∀ i, F i i = 0) (t : ℝ) :
    ‖gaussianQuadraticCharacteristic f₀ f F t -
        gaussianLinearCharacteristic f₀ f t‖ ≤
      |t| * √(2 * frobeniusSq F) := by
  let q := toQuadraticCoeffs (-trace F) (fun _ ↦ 0) F
  have htrace : trace F = 0 := by simp [trace, hdiag]
  have hqpoint (x : Fin n → ℝ) :
      quadraticPolynomial f₀ f F x - (f₀ + linearPart f x) = q.eval x := by
    have hdiagCorrection : gaussianDiagonalCorrection F x = 0 := by
      simp [gaussianDiagonalCorrection, hdiag]
    rw [quadraticPolynomial_eq_multilinear_add_diagonal, hdiagCorrection,
      add_zero]
    simp only [q, toQuadraticCoeffs_eval, htrace, neg_zero, zero_add]
    simp [linearPart]
  have hpoly : Measurable (fun x : Fin n → ℝ ↦
      quadraticPolynomial f₀ f F x) := by
    simp only [quadraticPolynomial, linearPart, quadraticPart]
    fun_prop
  have hlinpoly : Measurable (fun x : Fin n → ℝ ↦
      f₀ + linearPart f x) := by
    simp only [linearPart]
    fun_prop
  have hexpIntegrable (p : (Fin n → ℝ) → ℝ) (hp : Measurable p) :
      Integrable (fun x ↦ Complex.exp ((((t * p x : ℝ) : ℂ) * Complex.I)))
        (gaussianProductMeasure n) := by
    refine Integrable.of_bound (Complex.continuous_exp.measurable.comp
      ((Complex.measurable_ofReal.comp (hp.const_mul t)).mul_const Complex.I)
        |>.aestronglyMeasurable) 1 ?_
    exact Filter.Eventually.of_forall fun x ↦ by
      rw [Complex.norm_exp]
      simp
  have hfull := hexpIntegrable _ hpoly
  have hlin := hexpIntegrable _ hlinpoly
  have hqint := (quadraticCoeffs_eval_memLp_two_gaussian q).integrable (by norm_num)
  have hmajor : Integrable (fun x ↦ |t| * |q.eval x|)
      (gaussianProductMeasure n) := by
    simpa only [Real.norm_eq_abs] using hqint.norm.const_mul |t|
  rw [gaussianQuadraticCharacteristic_eq_integral]
  unfold gaussianLinearCharacteristic
  rw [← integral_sub hfull hlin]
  calc
    ‖∫ x, Complex.exp ((((t * quadraticPolynomial f₀ f F x : ℝ) : ℂ) *
          Complex.I)) -
        Complex.exp ((((t * (f₀ + linearPart f x) : ℝ) : ℂ) * Complex.I))
        ∂gaussianProductMeasure n‖ ≤
        ∫ x, ‖Complex.exp ((((t * quadraticPolynomial f₀ f F x : ℝ) : ℂ) *
            Complex.I)) -
          Complex.exp ((((t * (f₀ + linearPart f x) : ℝ) : ℂ) * Complex.I))‖
          ∂gaussianProductMeasure n := norm_integral_le_integral_norm _
    _ ≤ ∫ x, |t| * |q.eval x| ∂gaussianProductMeasure n := by
      apply integral_mono (hfull.sub hlin).norm hmajor
      intro x
      calc
        ‖Complex.exp ((((t * quadraticPolynomial f₀ f F x : ℝ) : ℂ) *
              Complex.I)) -
            Complex.exp ((((t * (f₀ + linearPart f x) : ℝ) : ℂ) *
              Complex.I))‖ =
            ‖Complex.exp (Complex.I *
                ((t * quadraticPolynomial f₀ f F x : ℝ) : ℂ)) -
              Complex.exp (Complex.I *
                ((t * (f₀ + linearPart f x) : ℝ) : ℂ))‖ := by
              congr 3 <;> ring
        _ ≤ |t * quadraticPolynomial f₀ f F x -
              t * (f₀ + linearPart f x)| :=
          norm_exp_I_mul_sub_exp_I_mul_le _ _
        _ = |t| * |q.eval x| := by
          rw [← mul_sub, hqpoint, abs_mul]
    _ = |t| * ∫ x, |q.eval x| ∂gaussianProductMeasure n := by
      rw [integral_const_mul]
    _ ≤ |t| * √(2 * frobeniusSq F) := by
      gcongr
      exact integral_abs_multilinearCenteredQuadratic_le F hF hdiag

end BooleanSlices
end Erdos88

namespace Erdos88
namespace BooleanSlices

open Classical Finset Invariance

/-- Centering cancels the phase of an affine Gaussian characteristic
function exactly. -/
lemma centered_gaussianLinearCharacteristic_eq {n : ℕ}
    (f₀ : ℝ) (f : Fin n → ℝ) (t : ℝ) :
    Complex.exp (-((((t * f₀ : ℝ) : ℂ) * Complex.I))) *
        gaussianLinearCharacteristic f₀ f t =
      Complex.exp (-(((t ^ 2 * vectorSqNorm f / 2 : ℝ) : ℂ))) := by
  rw [gaussianLinearCharacteristic_eq, ← Complex.exp_add]
  congr 1
  ring

/-- After centering, a symmetric zero-diagonal Gaussian quadratic is close
to the exact Gaussian characteristic function of its linear part. -/
lemma norm_centeredGaussianQuadratic_sub_linearGaussian_le {n : ℕ}
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (hF : ∀ i j, F i j = F j i) (hdiag : ∀ i, F i i = 0) (t : ℝ) :
    ‖Complex.exp (-((((t * f₀ : ℝ) : ℂ) * Complex.I))) *
          gaussianQuadraticCharacteristic f₀ f F t -
        Complex.exp (-(((t ^ 2 * vectorSqNorm f / 2 : ℝ) : ℂ)))‖ ≤
      |t| * √(2 * frobeniusSq F) := by
  rw [← centered_gaussianLinearCharacteristic_eq]
  rw [← mul_sub]
  rw [norm_mul, Complex.norm_exp]
  have hre : (-((((t * f₀ : ℝ) : ℂ) * Complex.I))).re = 0 := by simp
  rw [hre, Real.exp_zero, one_mul]
  exact norm_gaussianQuadraticCharacteristic_sub_linear_le
    f₀ f F hF hdiag t

end BooleanSlices

namespace GraphQuadratic

open Classical

/-- Graph-coefficient specialization of the sharp Gaussian quadratic-to-linear
characteristic estimate. -/
theorem norm_graphGaussianQuadratic_sub_linear_le {n : ℕ}
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ) (t : ℝ) :
    ‖BooleanSlices.gaussianQuadraticCharacteristic
          (graphSliceConstant G e₀ c) (graphSliceLinear G c)
          (graphSliceMatrix G) t -
        BooleanSlices.gaussianLinearCharacteristic
          (graphSliceConstant G e₀ c) (graphSliceLinear G c) t‖ ≤
      |t| * √((G.edgeFinset.card : ℝ) / 16) := by
  simpa only [frobeniusSq_graphSliceMatrix, show
      2 * ((G.edgeFinset.card : ℝ) / 32) =
        (G.edgeFinset.card : ℝ) / 16 by ring] using
    BooleanSlices.norm_gaussianQuadraticCharacteristic_sub_linear_le
      (graphSliceConstant G e₀ c) (graphSliceLinear G c)
      (graphSliceMatrix G) (graphSliceMatrix_symmetric G)
      (graphSliceMatrix_diagonal G) t

/-- Centered graph Gaussian characteristic estimate in the exact edge-count
normalization. -/
theorem norm_centeredGraphGaussianQuadratic_sub_linearGaussian_le {n : ℕ}
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ) (t : ℝ) :
    ‖Complex.exp (-((((t * graphSliceConstant G e₀ c : ℝ) : ℂ) *
          Complex.I))) *
          BooleanSlices.gaussianQuadraticCharacteristic
            (graphSliceConstant G e₀ c) (graphSliceLinear G c)
            (graphSliceMatrix G) t -
        Complex.exp (-(((t ^ 2 *
          BooleanSlices.vectorSqNorm (graphSliceLinear G c) / 2 : ℝ) : ℂ)))‖ ≤
      |t| * √((G.edgeFinset.card : ℝ) / 16) := by
  simpa only [frobeniusSq_graphSliceMatrix, show
      2 * ((G.edgeFinset.card : ℝ) / 32) =
        (G.edgeFinset.card : ℝ) / 16 by ring] using
    BooleanSlices.norm_centeredGaussianQuadratic_sub_linearGaussian_le
      (graphSliceConstant G e₀ c) (graphSliceLinear G c)
      (graphSliceMatrix G) (graphSliceMatrix_symmetric G)
      (graphSliceMatrix_diagonal G) t

end GraphQuadratic
end Erdos88
