/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos88.GaussianWindow
import ErdosProblems.Erdos88.GaussianLocalCLT
import ErdosProblems.Erdos88.StructuredAveraging

/-!
# A local lower bound for a Rademacher linear form

This file supplies the Berry--Esseen input used in the outer averaging step
of KSSS Claim 12.1.  The proof is Fourier analytic: the exact product of
cosines is compared with the centered Gaussian characteristic function,
while the remaining coordinates provide Gaussian damping in the finite
product telescoping estimate.
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory Set

namespace Erdos88
namespace RademacherLinearLower

open GaussianQuadratic BoundedWindowAnalytic

attribute [local instance] Classical.propDecidable

/-- A cosine factor differs from its variance-matched Gaussian factor by a
cubic remainder on the unit interval. -/
lemma abs_cos_sub_exp_neg_half_sq_le (u : ℝ) (hu : |u| ≤ 1) :
    |Real.cos u - Real.exp (-u ^ 2 / 2)| ≤ |u| ^ 3 / 2 := by
  have hcos := GaussianQuadratic.abs_cos_sub_quadratic_le u
  let x : ℝ := u ^ 2 / 2
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hx1 : x ≤ 1 := by
    have huSq : u ^ 2 ≤ 1 := by
      have h := (sq_le_sq₀ (abs_nonneg u) (by norm_num : (0 : ℝ) ≤ 1)).2 hu
      simpa only [sq_abs, one_pow] using h
    dsimp only [x]
    linarith
  have hexp0 := Real.norm_exp_sub_one_sub_id_le (x := -x) (by
    rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg hx0]
    exact hx1)
  have hexp : |(1 - x) - Real.exp (-x)| ≤ x ^ 2 := by
    calc
      |(1 - x) - Real.exp (-x)| =
          |Real.exp (-x) - 1 - (-x)| := by
            rw [abs_sub_comm]
            congr 1
            ring
      _ ≤ x ^ 2 := by
        simpa only [Real.norm_eq_abs, abs_neg, sq_abs] using hexp0
  have hdecomp :
      Real.cos u - Real.exp (-u ^ 2 / 2) =
        (Real.cos u - (1 - u ^ 2 / 2)) +
          ((1 - x) - Real.exp (-x)) := by
    dsimp only [x]
    ring
  rw [hdecomp]
  calc
    |(Real.cos u - (1 - u ^ 2 / 2)) +
        ((1 - x) - Real.exp (-x))| ≤
        |Real.cos u - (1 - u ^ 2 / 2)| +
          |(1 - x) - Real.exp (-x)| := abs_add_le _ _
    _ ≤ |u| ^ 3 / 6 + x ^ 2 := add_le_add hcos hexp
    _ ≤ |u| ^ 3 / 6 + |u| ^ 3 / 4 := by
      gcongr
      dsimp only [x]
      rw [div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num]
      have hu0 : 0 ≤ |u| := abs_nonneg u
      have hu4 : |u| ^ 4 ≤ |u| ^ 3 := by
        calc
          |u| ^ 4 = |u| ^ 3 * |u| := by ring
          _ ≤ |u| ^ 3 * 1 :=
            mul_le_mul_of_nonneg_left hu (pow_nonneg hu0 3)
          _ = |u| ^ 3 := by ring
      have heq : (u ^ 2) ^ 2 = |u| ^ 4 := by
        rw [show u ^ 2 = |u| ^ 2 by exact (sq_abs u).symm]
        ring
      rw [heq]
      exact div_le_div_of_nonneg_right hu4 (by norm_num)
    _ ≤ |u| ^ 3 / 2 := by
      have hnonneg : 0 ≤ |u| ^ 3 := pow_nonneg (abs_nonneg u) 3
      nlinarith

/-- Both the Rademacher cosine factor and its Gaussian comparison factor
obey the same quadratic envelope on the unit interval. -/
lemma max_norm_cos_exp_le (u : ℝ) (hu : |u| ≤ 1) :
    max ‖(Real.cos u : ℂ)‖
        ‖((Real.exp (-u ^ 2 / 2) : ℝ) : ℂ)‖ ≤
      Real.exp (-(u / Real.pi) ^ 2) := by
  apply max_le
  · rw [Complex.norm_real, Real.norm_eq_abs]
    apply Fourier.abs_cos_le_exp_neg_sq_div_pi_sq
    have hpi : (1 : ℝ) ≤ Real.pi / 2 := by
      nlinarith [Real.pi_gt_three]
    exact hu.trans hpi
  · rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hpiSq : (2 : ℝ) ≤ Real.pi ^ 2 := by
      nlinarith [Real.pi_gt_three]
    have hnonneg : 0 ≤ u ^ 2 := sq_nonneg u
    have hdiv : u ^ 2 / Real.pi ^ 2 ≤ u ^ 2 / 2 := by
      exact div_le_div_of_nonneg_left hnonneg (by norm_num) hpiSq
    rw [div_pow]
    linarith

/-- The law of an independent Rademacher linear form. -/
noncomputable def rademacherLinearLaw {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℝ) : Measure ℝ :=
  Esseen.finiteUniformLaw (I → Bool)
    (fun xi ↦ ∑ i, a i * Fourier.rademacherSign (xi i))

noncomputable instance rademacherLinearLaw_isProbabilityMeasure
    {I : Type*} [Fintype I] [DecidableEq I] (a : I → ℝ) :
    IsProbabilityMeasure (rademacherLinearLaw a) := by
  unfold rademacherLinearLaw
  infer_instance

lemma charFun_rademacherLinearLaw_eq {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℝ) (t : ℝ) :
    charFun (rademacherLinearLaw a) t =
      ∏ i, ((Real.cos (t * a i) : ℝ) : ℂ) := by
  rw [rademacherLinearLaw, Esseen.charFun_finiteUniformLaw,
    Fourier.finCharFun_rademacher_linear]

lemma smallBall_rademacherLinearLaw_eq_finProbability
    {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℝ) (eps x : ℝ) :
    Esseen.smallBall (rademacherLinearLaw a) eps x =
      Fourier.finProbability (I → Bool) (fun xi ↦
        |∑ i, a i * Fourier.rademacherSign (xi i) - x| ≤ eps) := by
  rw [rademacherLinearLaw, Esseen.smallBall_finiteUniformLaw]

/-- The cubic coefficient mass in the Rademacher Berry--Esseen bound. -/
noncomputable def thirdAbsMass {I : Type*} [Fintype I]
    (a : I → ℝ) : ℝ :=
  ∑ i, |a i| ^ 3

lemma thirdAbsMass_nonneg {I : Type*} [Fintype I] (a : I → ℝ) :
    0 ≤ thirdAbsMass a := by
  unfold thirdAbsMass
  positivity

lemma thirdAbsMass_le_max_mul_sqMass
    {I : Type*} [Fintype I] (a : I → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hmax : ∀ i, |a i| ≤ B) :
    thirdAbsMass a ≤ B * ∑ i, a i ^ 2 := by
  unfold thirdAbsMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  calc
    |a i| ^ 3 = |a i| * a i ^ 2 := by rw [← sq_abs]; ring
    _ ≤ B * a i ^ 2 :=
      mul_le_mul_of_nonneg_right (hmax i) (sq_nonneg _)

lemma normalizedThirdError_le_max_div_sqrtVariance
    {I : Type*} [Fintype I] (a : I → ℝ) {B V : ℝ}
    (hB : 0 ≤ B) (hV : 0 < V)
    (hVeq : (∑ i, a i ^ 2) = V) (hmax : ∀ i, |a i| ≤ B) :
    (3 / 2 : ℝ) * thirdAbsMass a * (Real.pi ^ 4 / V ^ 2) *
        Real.sqrt V ≤
      (3 / 2 : ℝ) * B * Real.pi ^ 4 / Real.sqrt V := by
  have hthird := thirdAbsMass_le_max_mul_sqMass a hB hmax
  rw [hVeq] at hthird
  have hsqrt : 0 < Real.sqrt V := Real.sqrt_pos.2 hV
  calc
    (3 / 2 : ℝ) * thirdAbsMass a * (Real.pi ^ 4 / V ^ 2) *
        Real.sqrt V ≤
      (3 / 2 : ℝ) * (B * V) * (Real.pi ^ 4 / V ^ 2) *
        Real.sqrt V := by
          gcongr
    _ = (3 / 2 : ℝ) * B * Real.pi ^ 4 / Real.sqrt V := by
      rw [div_eq_mul_inv]
      field_simp [hV.ne', hsqrt.ne']
      rw [Real.sq_sqrt hV.le]

/-- The damped finite-product Berry--Esseen estimate.  The unit-frequency
hypothesis is exactly what is needed to rule out lattice resonances on the
Fourier window used by the reverse Esseen inequality. -/
theorem norm_charFun_rademacherLinearLaw_sub_gaussian_le
    {I : Type*} [Fintype I] [DecidableEq I] (a : I → ℝ) (t : ℝ)
    (hunit : ∀ i, |t * a i| ≤ 1) :
    ‖charFun (rademacherLinearLaw a) t -
        charFun (centeredGaussianLaw
          (Real.sqrt (∑ i, a i ^ 2))) t‖ ≤
      (3 / 2 : ℝ) * thirdAbsMass a * |t| ^ 3 *
        Real.exp (-((∑ i, a i ^ 2) / Real.pi ^ 2) * t ^ 2) := by
  classical
  let V : ℝ := ∑ i, a i ^ 2
  let f : I → ℂ := fun i ↦ (Real.cos (t * a i) : ℝ)
  let g : I → ℂ := fun i ↦ (Real.exp (-(t * a i) ^ 2 / 2) : ℝ)
  have hmax (i : I) : max ‖f i‖ ‖g i‖ ≤
      Real.exp (-((t * a i) / Real.pi) ^ 2) := by
    dsimp only [f, g]
    exact max_norm_cos_exp_le (t * a i) (hunit i)
  have hlocal (i : I) : ‖f i - g i‖ ≤ |t * a i| ^ 3 / 2 := by
    dsimp only [f, g]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact abs_cos_sub_exp_neg_half_sq_le (t * a i) (hunit i)
  have hprodBound (i : I) :
      (∏ j ∈ (Finset.univ : Finset I).erase i, max ‖f j‖ ‖g j‖) ≤
        3 * Real.exp (-(V / Real.pi ^ 2) * t ^ 2) := by
    have hprod :
        (∏ j ∈ (Finset.univ : Finset I).erase i, max ‖f j‖ ‖g j‖) ≤
          ∏ j ∈ (Finset.univ : Finset I).erase i,
            Real.exp (-((t * a j) / Real.pi) ^ 2) := by
      apply Finset.prod_le_prod
      · intro j hj
        positivity
      · intro j hj
        exact hmax j
    have hsumErase :
        (∑ j ∈ (Finset.univ : Finset I).erase i, a j ^ 2) =
          V - a i ^ 2 := by
      have h := Finset.sum_erase_add (Finset.univ : Finset I)
        (fun j ↦ a j ^ 2) (Finset.mem_univ i)
      dsimp only [V]
      linarith
    have hsumExp :
        (∏ j ∈ (Finset.univ : Finset I).erase i,
            Real.exp (-((t * a j) / Real.pi) ^ 2)) =
          Real.exp (-((V - a i ^ 2) / Real.pi ^ 2) * t ^ 2) := by
      rw [← Real.exp_sum]
      congr 1
      rw [show (fun j ↦ -((t * a j) / Real.pi) ^ 2) =
          fun j ↦ -(t ^ 2 / Real.pi ^ 2) * a j ^ 2 by
        funext j
        field_simp [Real.pi_ne_zero]]
      rw [← Finset.mul_sum, hsumErase]
      ring
    have hterm : a i ^ 2 * t ^ 2 / Real.pi ^ 2 ≤ 1 := by
      have hsq : (t * a i) ^ 2 ≤ 1 := by
        have h := (sq_le_sq₀ (abs_nonneg (t * a i))
          (by norm_num : (0 : ℝ) ≤ 1)).2 (hunit i)
        simpa only [sq_abs, one_pow] using h
      have hpiSq : (1 : ℝ) ≤ Real.pi ^ 2 := by
        nlinarith [Real.pi_gt_three]
      calc
        a i ^ 2 * t ^ 2 / Real.pi ^ 2 =
            (t * a i) ^ 2 / Real.pi ^ 2 := by ring
        _ ≤ 1 / Real.pi ^ 2 :=
          div_le_div_of_nonneg_right hsq (sq_nonneg Real.pi)
        _ ≤ 1 := by
          exact (div_le_one₀ (sq_pos_of_pos Real.pi_pos)).2 hpiSq
    have hexponent :
        -((V - a i ^ 2) / Real.pi ^ 2) * t ^ 2 ≤
          -(V / Real.pi ^ 2) * t ^ 2 + 1 := by
      have hpi0 : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
      calc
        -((V - a i ^ 2) / Real.pi ^ 2) * t ^ 2 =
            -(V / Real.pi ^ 2) * t ^ 2 +
              a i ^ 2 * t ^ 2 / Real.pi ^ 2 := by
            field_simp [hpi0.ne']
            ring
        _ ≤ -(V / Real.pi ^ 2) * t ^ 2 + 1 :=
          by simpa only [add_comm] using
            (add_le_add_left hterm (-(V / Real.pi ^ 2) * t ^ 2))
    calc
      (∏ j ∈ (Finset.univ : Finset I).erase i, max ‖f j‖ ‖g j‖) ≤
          ∏ j ∈ (Finset.univ : Finset I).erase i,
            Real.exp (-((t * a j) / Real.pi) ^ 2) := hprod
      _ = Real.exp (-((V - a i ^ 2) / Real.pi ^ 2) * t ^ 2) := hsumExp
      _ ≤ Real.exp (-(V / Real.pi ^ 2) * t ^ 2 + 1) :=
        Real.exp_le_exp.mpr hexponent
      _ = Real.exp 1 * Real.exp (-(V / Real.pi ^ 2) * t ^ 2) := by
        rw [add_comm, Real.exp_add]
      _ ≤ 3 * Real.exp (-(V / Real.pi ^ 2) * t ^ 2) := by
        exact mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le
          (Real.exp_pos _).le
  have hprodg : (∏ i, g i) =
      charFun (centeredGaussianLaw (Real.sqrt V)) t := by
    rw [charFun_centeredGaussianLaw_eq]
    unfold GaussianQuadratic.standardNormalChar
    have hreal :
        (∏ i, Real.exp (-(t * a i) ^ 2 / 2)) =
          Real.exp (-(Real.sqrt V * t) ^ 2 / 2) := by
      rw [← Real.exp_sum]
      congr 1
      have hV0 : 0 ≤ V := by
        dsimp only [V]
        positivity
      have hsum : ∑ i, -(t * a i) ^ 2 / 2 = -(V * t ^ 2) / 2 := by
        dsimp only [V]
        rw [← Finset.sum_div, Finset.sum_neg_distrib]
        rw [show (fun i ↦ (t * a i) ^ 2) =
            fun i ↦ t ^ 2 * a i ^ 2 by
          funext i
          ring]
        rw [← Finset.mul_sum]
        ring
      rw [hsum, mul_pow, Real.sq_sqrt hV0]
    dsimp only [g]
    exact_mod_cast hreal
  have hperturb := GaussianQuadratic.norm_finsetProd_sub_finsetProd_le
    (Finset.univ : Finset I) f g
  rw [charFun_rademacherLinearLaw_eq]
  change ‖(∏ i, f i) - charFun (centeredGaussianLaw (Real.sqrt V)) t‖ ≤ _
  rw [← hprodg]
  calc
    ‖(∏ i, f i) - ∏ i, g i‖ ≤
        ∑ i, ‖f i - g i‖ *
          ∏ j ∈ (Finset.univ : Finset I).erase i, max ‖f j‖ ‖g j‖ :=
      hperturb
    _ ≤ ∑ i, (|t * a i| ^ 3 / 2) *
        (3 * Real.exp (-(V / Real.pi ^ 2) * t ^ 2)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul (hlocal i) (hprodBound i) (by positivity) (by positivity)
    _ = (3 / 2 : ℝ) * thirdAbsMass a * |t| ^ 3 *
        Real.exp (-(V / Real.pi ^ 2) * t ^ 2) := by
      unfold thirdAbsMass
      rw [show (fun i ↦ (|t * a i| ^ 3 / 2) *
          (3 * Real.exp (-(V / Real.pi ^ 2) * t ^ 2))) =
        fun i ↦ |a i| ^ 3 *
          ((3 / 2 : ℝ) * |t| ^ 3 *
            Real.exp (-(V / Real.pi ^ 2) * t ^ 2)) by
          funext i
          rw [abs_mul, mul_pow]
          ring]
      rw [← Finset.sum_mul]
      ring
    _ = (3 / 2 : ℝ) * thirdAbsMass a * |t| ^ 3 *
        Real.exp (-((∑ i, a i ^ 2) / Real.pi ^ 2) * t ^ 2) := by
      rfl

/-- The physical-scale cubic Gaussian envelope occurring in the preceding
characteristic-function estimate. -/
noncomputable def rademacherCLTEnvelope (V t : ℝ) : ℝ :=
  |t| ^ 3 * Real.exp (-(V / Real.pi ^ 2) * t ^ 2)

lemma rademacherCLTEnvelope_nonneg (V t : ℝ) :
    0 ≤ rademacherCLTEnvelope V t := by
  unfold rademacherCLTEnvelope
  positivity

lemma rademacherCLTEnvelope_integrable {V : ℝ} (hV : 0 < V) :
    Integrable (rademacherCLTEnvelope V) := by
  have hb : 0 < V / Real.pi ^ 2 :=
    div_pos hV (sq_pos_of_pos Real.pi_pos)
  change Integrable
    (fun t : ℝ ↦ |t| ^ 3 * Real.exp (-(V / Real.pi ^ 2) * t ^ 2))
  exact LinearLCDCancellation.integrable_abs_pow_mul_exp_neg_mul_sq 3 hb

/-- Exact integral of the physical-scale cubic envelope. -/
lemma integral_rademacherCLTEnvelope {V : ℝ} (hV : 0 < V) :
    ∫ t : ℝ, rademacherCLTEnvelope V t = Real.pi ^ 4 / V ^ 2 := by
  have hb : 0 < V / Real.pi ^ 2 :=
    div_pos hV (sq_pos_of_pos Real.pi_pos)
  have h := LinearLCDCancellation.integral_abs_pow_mul_exp_neg_mul_sq
    3 hb
  rw [show (∫ t : ℝ, rademacherCLTEnvelope V t) =
      ∫ t : ℝ, |t| ^ 3 * Real.exp (-(V / Real.pi ^ 2) * t ^ 2) by rfl]
  rw [h]
  norm_num [Real.Gamma_nat_eq_factorial, Real.rpow_neg_natCast]
  field_simp [hV.ne', Real.pi_ne_zero]

/-- Integrated characteristic-function comparison on the reverse-Esseen
window. -/
theorem fourierError_rademacherLinearLaw_centeredGaussianLaw_le
    {I : Type*} [Fintype I] [DecidableEq I] (a : I → ℝ) {eps : ℝ}
    (heps : 0 < eps) (hV : 0 < ∑ i, a i ^ 2)
    (hscale : ∀ i, 2 * |a i| ≤ eps) :
    Esseen.fourierError (rademacherLinearLaw a)
        (centeredGaussianLaw (Real.sqrt (∑ i, a i ^ 2))) eps ≤
      (3 / 2 : ℝ) * thirdAbsMass a *
        (Real.pi ^ 4 / (∑ i, a i ^ 2) ^ 2) := by
  let V : ℝ := ∑ i, a i ^ 2
  let C : ℝ := (3 / 2 : ℝ) * thirdAbsMass a
  letI : IsProbabilityMeasure (centeredGaussianLaw (Real.sqrt V)) := by
    unfold centeredGaussianLaw
    infer_instance
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (by norm_num) (thirdAbsMass_nonneg a)
  have hends : -(2 / eps) ≤ 2 / eps := by
    have htwo : 0 < 2 / eps := div_pos (by norm_num) heps
    linarith
  have hpoint : ∀ t ∈ Set.Icc (-(2 / eps)) (2 / eps),
      ‖charFun (rademacherLinearLaw a) t -
          charFun (centeredGaussianLaw (Real.sqrt V)) t‖ ≤
        C * rademacherCLTEnvelope V t := by
    intro t ht
    have htAbs : |t| ≤ 2 / eps := by
      rw [abs_le]
      exact ht
    have hunit : ∀ i, |t * a i| ≤ 1 := by
      intro i
      rw [abs_mul]
      calc
        |t| * |a i| ≤ (2 / eps) * |a i| :=
          mul_le_mul_of_nonneg_right htAbs (abs_nonneg _)
        _ ≤ 1 := by
          rw [show (2 / eps) * |a i| = (2 * |a i|) / eps by ring]
          exact (div_le_one₀ heps).2 (hscale i)
    have hraw := norm_charFun_rademacherLinearLaw_sub_gaussian_le a t hunit
    simpa only [V, C, rademacherCLTEnvelope, mul_assoc] using hraw
  have hdiffInt : IntervalIntegrable (fun t ↦
      ‖charFun (rademacherLinearLaw a) t -
        charFun (centeredGaussianLaw (Real.sqrt V)) t‖)
      volume (-(2 / eps)) (2 / eps) := by
    exact (continuous_norm.comp
      (MeasureTheory.continuous_charFun.sub
        MeasureTheory.continuous_charFun)).intervalIntegrable _ _
  have hmajorInt : Integrable (fun t ↦ C * rademacherCLTEnvelope V t) :=
    (rademacherCLTEnvelope_integrable (by simpa only [V] using hV)).const_mul C
  have hinterval :
      (∫ t in -(2 / eps)..(2 / eps),
          ‖charFun (rademacherLinearLaw a) t -
            charFun (centeredGaussianLaw (Real.sqrt V)) t‖) ≤
        ∫ t in -(2 / eps)..(2 / eps), C * rademacherCLTEnvelope V t := by
    exact intervalIntegral.integral_mono_on hends hdiffInt
      hmajorInt.intervalIntegrable hpoint
  have hwhole :
      (∫ t in -(2 / eps)..(2 / eps), C * rademacherCLTEnvelope V t) ≤
        ∫ t : ℝ, C * rademacherCLTEnvelope V t := by
    rw [intervalIntegral.integral_of_le hends]
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun t ↦
        mul_nonneg hC (rademacherCLTEnvelope_nonneg V t)) hmajorInt
  rw [Esseen.fourierError]
  calc
    (∫ t in -(2 / eps)..(2 / eps),
        ‖charFun (rademacherLinearLaw a) t -
          charFun (centeredGaussianLaw (Real.sqrt (∑ i, a i ^ 2))) t‖) ≤
        ∫ t in -(2 / eps)..(2 / eps), C * rademacherCLTEnvelope V t :=
      hinterval
    _ ≤ ∫ t : ℝ, C * rademacherCLTEnvelope V t := hwhole
    _ = C * (Real.pi ^ 4 / V ^ 2) := by
      rw [integral_const_mul,
        integral_rademacherCLTEnvelope (by simpa only [V] using hV)]
    _ = (3 / 2 : ℝ) * thirdAbsMass a *
        (Real.pi ^ 4 / (∑ i, a i ^ 2) ^ 2) := by
      rfl

/-- A quantitative local lower bound for a Rademacher linear form.  The
Gaussian density-ratio hypothesis is elementary and is discharged by the
count-vector scale estimates in the structured application. -/
theorem smallBall_rademacherLinearLaw_lower
    {I : Type*} [Fintype I] [DecidableEq I] (a : I → ℝ)
    {eps M R x : ℝ}
    (heps : 0 < eps) (hV : 0 < ∑ i, a i ^ 2)
    (hepssigma : eps ≤ Real.sqrt (∑ i, a i ^ 2))
    (hM : 0 ≤ M)
    (hx : |x| ≤ M * Real.sqrt (∑ i, a i ^ 2))
    (hscale : ∀ i, 2 * |a i| ≤ eps)
    (hR : 4 ≤ R)
    (hratio : Esseen.DensityRatioOn
      (centeredGaussianDensity (Real.sqrt (∑ i, a i ^ 2))) x eps R 3) :
    (eps / Real.sqrt (∑ i, a i ^ 2)) *
        (Real.exp (-((M + 1) ^ 2) / 2) / 12 -
          Esseen.relativeEsseenConstant *
            (2 / R +
              (3 / 2 : ℝ) * thirdAbsMass a *
                (Real.pi ^ 4 / (∑ i, a i ^ 2) ^ 2) *
                  Real.sqrt (∑ i, a i ^ 2))) ≤
      Esseen.smallBall (rademacherLinearLaw a) (30000 * eps) x := by
  let V : ℝ := ∑ i, a i ^ 2
  let sigma : ℝ := Real.sqrt V
  let eta : ℝ := (3 / 2 : ℝ) * thirdAbsMass a *
    (Real.pi ^ 4 / V ^ 2) * sigma
  have hsigma : 0 < sigma := by
    dsimp only [sigma]
    exact Real.sqrt_pos.2 (by simpa only [V] using hV)
  letI : IsProbabilityMeasure (centeredGaussianLaw sigma) := by
    unfold centeredGaussianLaw
    infer_instance
  have herr : Esseen.fourierError (rademacherLinearLaw a)
      (centeredGaussianLaw sigma) eps ≤ eta / sigma := by
    have hbase := fourierError_rademacherLinearLaw_centeredGaussianLaw_le
      a heps hV hscale
    dsimp only [eta, sigma, V]
    calc
      Esseen.fourierError (rademacherLinearLaw a)
          (centeredGaussianLaw (Real.sqrt (∑ i, a i ^ 2))) eps ≤
          (3 / 2 : ℝ) * thirdAbsMass a *
            (Real.pi ^ 4 / (∑ i, a i ^ 2) ^ 2) := hbase
      _ = ((3 / 2 : ℝ) * thirdAbsMass a *
            (Real.pi ^ 4 / (∑ i, a i ^ 2) ^ 2) *
              Real.sqrt (∑ i, a i ^ 2)) /
            Real.sqrt (∑ i, a i ^ 2) := by
          field_simp [hsigma.ne']
  have hZ := smallBall_centeredGaussianLaw_lower hsigma heps
    (by simpa only [sigma, V] using hepssigma) hM
    (by simpa only [sigma, V] using hx)
  have hconc := concentration_centeredGaussianLaw_le hsigma heps
  have hnoise :
      Esseen.concentration (centeredGaussianLaw sigma) eps / R +
          eps * Esseen.fourierError (rademacherLinearLaw a)
            (centeredGaussianLaw sigma) eps ≤
        (2 * eps / sigma) / R + eps * (eta / sigma) := by
    exact add_le_add
      ((div_le_div_iff_of_pos_right
        (lt_of_lt_of_le (by norm_num) hR)).2 hconc)
      (mul_le_mul_of_nonneg_left herr heps.le)
  have hrel := Esseen.relative_esseen_6_3
    (rademacherLinearLaw a) (centeredGaussianLaw sigma)
    (hasContinuousDensity_centeredGaussianLaw hsigma)
    heps (show (1 : ℝ) ≤ 3 by norm_num) hR
    (by simpa only [sigma, V] using hratio)
  have hpositive :
      (1 / 8 : ℝ) *
          ((2 * eps) * Real.exp (-((M + 1) ^ 2) / 2) / (3 * sigma)) ≤
        (1 / 8 : ℝ) *
          Esseen.smallBall (centeredGaussianLaw sigma) eps x :=
    mul_le_mul_of_nonneg_left hZ (by norm_num)
  have hnoiseMul := mul_le_mul_of_nonneg_left hnoise
    Esseen.relativeEsseenConstant_nonneg
  change (eps / sigma) *
      (Real.exp (-((M + 1) ^ 2) / 2) / 12 -
        Esseen.relativeEsseenConstant * (2 / R + eta)) ≤ _
  calc
    (eps / sigma) *
        (Real.exp (-((M + 1) ^ 2) / 2) / 12 -
          Esseen.relativeEsseenConstant * (2 / R + eta)) =
        (1 / 8 : ℝ) *
            ((2 * eps) * Real.exp (-((M + 1) ^ 2) / 2) / (3 * sigma)) -
          Esseen.relativeEsseenConstant *
            ((2 * eps / sigma) / R + eps * (eta / sigma)) := by
      field_simp [hsigma.ne']
      ring
    _ ≤ (1 / 8 : ℝ) *
          Esseen.smallBall (centeredGaussianLaw sigma) eps x -
        Esseen.relativeEsseenConstant *
          (Esseen.concentration (centeredGaussianLaw sigma) eps / R +
            eps * Esseen.fourierError (rademacherLinearLaw a)
              (centeredGaussianLaw sigma) eps) := by
      linarith
    _ ≤ Esseen.smallBall (rademacherLinearLaw a)
        ((10000 * 3) * eps) x := hrel
    _ = Esseen.smallBall (rademacherLinearLaw a) (30000 * eps) x := by
      norm_num

end RademacherLinearLower
end Erdos88
