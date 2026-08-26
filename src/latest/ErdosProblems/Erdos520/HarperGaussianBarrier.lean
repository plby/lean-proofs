import Mathlib.Probability.Distributions.Gaussian.Real
import ErdosProblems.Erdos520.HarperBlockGaussian

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Erdos
namespace Problem520

/-!
# Elementary Gaussian barrier infrastructure

Harper's published proof invokes a sharp Gaussian ballot estimate after the
blockwise characteristic-function comparison.  For the upper bound needed by
#520, it is useful to isolate two considerably softer ingredients as well:

* a Gaussian endpoint interval has mass at most its length times the peak of
  the Gaussian density;
* a barrier event can be split according to whether its terminal distance
  from the barrier is small or large.

The latter split, combined with a positive superharmonic function for the
killed Gaussian walk, gives a polynomial survival saving without requiring
the sharp ballot constant.  This file starts that alternative route with the
fully explicit density and abstract splitting estimates.
-/

/-- The standard Gaussian kernel without its normalizing constant. -/
noncomputable def standardGaussianKernel (x : ℝ) : ℝ :=
  Real.exp (-(1 / 2 : ℝ) * x ^ 2)

theorem standardGaussianKernel_pos (x : ℝ) :
    0 < standardGaussianKernel x := by
  exact Real.exp_pos _

theorem continuous_standardGaussianKernel :
    Continuous standardGaussianKernel := by
  unfold standardGaussianKernel
  fun_prop

theorem hasDerivAt_standardGaussianKernel (x : ℝ) :
    HasDerivAt standardGaussianKernel
      (-x * standardGaussianKernel x) x := by
  unfold standardGaussianKernel
  have hinner : HasDerivAt (fun z : ℝ ↦ -(1 / 2 : ℝ) * z ^ 2) (-x) x := by
    convert! (((hasDerivAt_id x).pow 2).const_mul (-(1 / 2 : ℝ))) using 1 <;>
      simp only [id_eq] <;> ring
  convert! (Real.hasDerivAt_exp _).comp x hinner using 1 <;> ring

theorem integrable_standardGaussianKernel :
    Integrable standardGaussianKernel := by
  simpa only [standardGaussianKernel] using!
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2))

theorem integrable_id_mul_standardGaussianKernel :
    Integrable (fun x : ℝ ↦ x * standardGaussianKernel x) := by
  simpa only [standardGaussianKernel] using!
    (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2))

theorem tendsto_standardGaussianKernel_atBot :
    Filter.Tendsto standardGaussianKernel Filter.atBot (nhds 0) := by
  apply tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0)
      (f' := fun x : ℝ ↦ -x * standardGaussianKernel x)
  · intro x hx
    exact hasDerivAt_standardGaussianKernel x
  · simpa only [Pi.neg_apply, neg_mul] using!
      integrable_id_mul_standardGaussianKernel.neg.integrableOn
  · exact integrable_standardGaussianKernel.integrableOn

/-- Exact truncated first moment of the unnormalized standard Gaussian
kernel. -/
theorem integral_Iic_id_mul_standardGaussianKernel (x : ℝ) :
    (∫ z in Iic x, z * standardGaussianKernel z) =
      -standardGaussianKernel x := by
  have h := integral_Iic_of_hasDerivAt_of_tendsto'
    (a := x) (m := (0 : ℝ))
    (f := standardGaussianKernel)
    (f' := fun z : ℝ ↦ -z * standardGaussianKernel z)
    (fun z hz ↦ hasDerivAt_standardGaussianKernel z)
    (by simpa only [Pi.neg_apply, neg_mul] using!
      integrable_id_mul_standardGaussianKernel.neg.integrableOn)
    tendsto_standardGaussianKernel_atBot
  simp only [neg_mul, integral_neg, sub_zero] at h
  linarith

/-- An elementary finite-interval exponential integral used in the Gaussian
tail lower bound below. -/
theorem intervalIntegral_exp_neg_mul (a : ℝ) (ha : 0 < a) :
    (∫ u : ℝ in (0 : ℝ)..1, Real.exp (-a * u)) =
      (1 - Real.exp (-a)) / a := by
  let F : ℝ → ℝ := fun u ↦ -Real.exp (-a * u) / a
  have hF (u : ℝ) : HasDerivAt F (Real.exp (-a * u)) u := by
    have hinner : HasDerivAt (fun z : ℝ ↦ -a * z) (-a) u := by
      simpa [id] using! (hasDerivAt_id u).const_mul (-a)
    have hexp := (Real.hasDerivAt_exp _).comp u hinner
    unfold F
    convert! hexp.neg.div_const a using 1 <;>
      field_simp [ha.ne'] <;> ring
  calc
    (∫ u : ℝ in (0 : ℝ)..1, Real.exp (-a * u)) = F 1 - F 0 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num)
      · exact ((Real.continuous_exp.comp
          (continuous_const.neg.mul continuous_id)).neg.div_const a).continuousOn
      · intro u hu
        exact hF u
      · exact (Real.continuous_exp.comp
          (continuous_const.neg.mul continuous_id)).intervalIntegrable _ _
    _ = (1 - Real.exp (-a)) / a := by
      unfold F
      simp only [mul_one, mul_zero, Real.exp_zero]
      field_simp [ha.ne']
      ring

/-- The elementary exponential integral over `[0,1]` has the reciprocal
lower bound needed for a coarse Mills-ratio estimate. -/
theorem one_div_add_two_le_intervalIntegral_exp
    {x : ℝ} (hx : 0 ≤ x) :
    1 / (x + 2) ≤
      ∫ u : ℝ in (0 : ℝ)..1,
        Real.exp (-(x + 1 / 2) * u) := by
  let a : ℝ := x + 1 / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have ha1 : 0 < a + 1 := by linarith
  have ha32 : a + 1 ≤ a + 3 / 2 := by norm_num
  have hexpLower : a + 1 ≤ Real.exp a := by
    simpa only [add_comm] using! Real.add_one_le_exp a
  have hexpNeg : Real.exp (-a) ≤ 1 / (a + 1) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ ha1 hexpLower
  have hnum : a / (a + 1) ≤ 1 - Real.exp (-a) := by
    calc
      a / (a + 1) = 1 - 1 / (a + 1) := by
        field_simp [ha1.ne']
        ring
      _ ≤ 1 - Real.exp (-a) := sub_le_sub_left hexpNeg 1
  have hratio : 1 / (a + 1) ≤ (1 - Real.exp (-a)) / a := by
    rw [le_div_iff₀ ha]
    calc
      1 / (a + 1) * a = a / (a + 1) := by ring
      _ ≤ 1 - Real.exp (-a) := hnum
  rw [intervalIntegral_exp_neg_mul a ha]
  calc
    1 / (x + 2) = 1 / (a + 3 / 2) := by
      dsimp [a]
      ring
    _ ≤ 1 / (a + 1) := by
      simpa only [one_div] using! inv_anti₀ ha1 ha32
    _ ≤ (1 - Real.exp (-a)) / a := hratio

theorem standardGaussianKernel_mul_exp_le_add
    {x u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    standardGaussianKernel x * Real.exp (-(x + 1 / 2) * u) ≤
      standardGaussianKernel (x + u) := by
  unfold standardGaussianKernel
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have huu : u ^ 2 ≤ u := by nlinarith
  nlinarith

/-- Coarse Mills-ratio lower bound for the unnormalized standard Gaussian
kernel.  The constant `2` is deliberately generous and makes the proof use
only a one-unit interval. -/
theorem standardGaussianKernel_le_add_two_mul_tail
    {x : ℝ} (hx : 0 ≤ x) :
    standardGaussianKernel x ≤
      (x + 2) * ∫ z in Ioi x, standardGaussianKernel z := by
  have hx2 : 0 < x + 2 := by linarith
  have hpoint : ∀ u ∈ Icc (0 : ℝ) 1,
      standardGaussianKernel x * Real.exp (-(x + 1 / 2) * u) ≤
        standardGaussianKernel (x + u) := by
    intro u hu
    exact standardGaussianKernel_mul_exp_le_add hu.1 hu.2
  have hinterval :
      standardGaussianKernel x /
          (x + 2) ≤
        ∫ u : ℝ in (0 : ℝ)..1, standardGaussianKernel (x + u) := by
    calc
      standardGaussianKernel x / (x + 2) =
          standardGaussianKernel x * (1 / (x + 2)) := by ring
      _ ≤ standardGaussianKernel x *
          (∫ u : ℝ in (0 : ℝ)..1,
            Real.exp (-(x + 1 / 2) * u)) := by
        exact mul_le_mul_of_nonneg_left
          (one_div_add_two_le_intervalIntegral_exp hx)
          (standardGaussianKernel_pos x).le
      _ = ∫ u : ℝ in (0 : ℝ)..1,
          standardGaussianKernel x *
            Real.exp (-(x + 1 / 2) * u) := by
        rw [intervalIntegral.integral_const_mul]
      _ ≤ ∫ u : ℝ in (0 : ℝ)..1,
          standardGaussianKernel (x + u) := by
        apply intervalIntegral.integral_mono_on (by norm_num)
        · exact (continuous_const.mul <|
            Real.continuous_exp.comp
              (continuous_const.neg.mul continuous_id)).intervalIntegrable _ _
        · exact (continuous_standardGaussianKernel.comp
            (continuous_const.add continuous_id)).intervalIntegrable _ _
        · exact hpoint
  have htranslate :
      (∫ u : ℝ in (0 : ℝ)..1, standardGaussianKernel (x + u)) =
        ∫ z : ℝ in x..x + 1, standardGaussianKernel z := by
    simpa only [zero_add, add_zero, add_comm] using!
      (intervalIntegral.integral_comp_add_right
        (a := (0 : ℝ)) (b := 1) standardGaussianKernel x)
  have hset :
      (∫ z : ℝ in x..x + 1, standardGaussianKernel z) ≤
        ∫ z in Ioi x, standardGaussianKernel z := by
    rw [intervalIntegral.integral_of_le (by linarith : x ≤ x + 1)]
    apply setIntegral_mono_set integrable_standardGaussianKernel.integrableOn
    · change ∀ᵐ z ∂volume.restrict (Ioi x),
        (0 : ℝ) ≤ standardGaussianKernel z
      exact Filter.Eventually.of_forall fun z ↦
        (standardGaussianKernel_pos z).le
    · filter_upwards with z
      exact fun hz ↦ hz.1
  rw [htranslate] at hinterval
  have hdiv : standardGaussianKernel x / (x + 2) ≤
      ∫ z in Ioi x, standardGaussianKernel z := hinterval.trans hset
  simpa only [mul_comm] using! (div_le_iff₀ hx2).mp hdiv

/-- The affine distance-to-barrier function is superharmonic for the
standard Gaussian kernel killed on crossing the barrier. -/
theorem integral_Iic_gaussianBarrierPotential_le
    {x : ℝ} (hx : 0 ≤ x) :
    (∫ z in Iic x,
        (x - z + 2) * standardGaussianKernel z) ≤
      (x + 2) * ∫ z : ℝ, standardGaussianKernel z := by
  have hx2 : 0 ≤ x + 2 := by linarith
  have hconstInt : IntegrableOn
      (fun z : ℝ ↦ (x + 2) * standardGaussianKernel z) (Iic x) :=
    integrable_standardGaussianKernel.const_mul (x + 2) |>.integrableOn
  have hidInt : IntegrableOn
      (fun z : ℝ ↦ z * standardGaussianKernel z) (Iic x) :=
    integrable_id_mul_standardGaussianKernel.integrableOn
  calc
    (∫ z in Iic x,
        (x - z + 2) * standardGaussianKernel z) =
        (∫ z in Iic x,
          ((x + 2) * standardGaussianKernel z -
            z * standardGaussianKernel z)) := by
      apply setIntegral_congr_fun measurableSet_Iic
      intro z hz
      ring
    _ = (x + 2) * (∫ z in Iic x, standardGaussianKernel z) -
        ∫ z in Iic x, z * standardGaussianKernel z := by
      rw [integral_sub hconstInt hidInt, integral_const_mul]
    _ = (x + 2) * (∫ z in Iic x, standardGaussianKernel z) +
        standardGaussianKernel x := by
      rw [integral_Iic_id_mul_standardGaussianKernel]
      ring
    _ ≤ (x + 2) * (∫ z in Iic x, standardGaussianKernel z) +
        (x + 2) * ∫ z in Ioi x, standardGaussianKernel z := by
      simpa only [add_comm] using! add_le_add_left
        (standardGaussianKernel_le_add_two_mul_tail hx)
        ((x + 2) * ∫ z in Iic x, standardGaussianKernel z)
    _ = (x + 2) * ∫ z : ℝ, standardGaussianKernel z := by
      rw [← mul_add]
      congr 1
      rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
          integrable_standardGaussianKernel.integrableOn
          integrable_standardGaussianKernel.integrableOn,
        Set.Iic_union_Ioi, setIntegral_univ]

/-- Set-integral form of Mathlib's Gaussian density representation. -/
theorem setIntegral_gaussianReal_eq_integral_mul
    {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (s : Set ℝ) (hs : MeasurableSet s) (f : ℝ → ℝ) :
    (∫ x in s, f x ∂gaussianReal m v) =
      ∫ x in s, gaussianPDFReal m v x * f x := by
  rw [← integral_indicator hs,
    integral_gaussianReal_eq_integral_smul (f := s.indicator f) hv,
    ← integral_indicator hs]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    by_cases hx : x ∈ s <;> simp [hx, smul_eq_mul]

theorem gaussianPDFReal_zero_one_eq (x : ℝ) :
    gaussianPDFReal 0 1 x =
      (Real.sqrt (2 * Real.pi))⁻¹ * standardGaussianKernel x := by
  unfold gaussianPDFReal standardGaussianKernel
  simp only [NNReal.coe_one, mul_one, sub_zero]
  change (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) =
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2) * x ^ 2)
  congr 2
  ring

/-- The affine potential is genuinely superharmonic for one step of a
standard Gaussian random walk killed on leaving the nonnegative half-line. -/
theorem integral_Iic_gaussianReal_barrierPotential_le
    {x : ℝ} (hx : 0 ≤ x) :
    (∫ z in Iic x, (x - z + 2) ∂gaussianReal 0 1) ≤ x + 2 := by
  let c : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
  have hc : 0 ≤ c := by dsimp [c]; positivity
  rw [setIntegral_gaussianReal_eq_integral_mul (by norm_num) (Iic x)
    measurableSet_Iic]
  calc
    (∫ z in Iic x,
        gaussianPDFReal 0 1 z * (x - z + 2)) =
        c * ∫ z in Iic x,
          (x - z + 2) * standardGaussianKernel z := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Iic
      intro z hz
      change gaussianPDFReal 0 1 z * (x - z + 2) =
        c * ((x - z + 2) * standardGaussianKernel z)
      rw [gaussianPDFReal_zero_one_eq]
      dsimp [c]
      ring
    _ ≤ c * ((x + 2) * ∫ z : ℝ, standardGaussianKernel z) := by
      exact mul_le_mul_of_nonneg_left
        (integral_Iic_gaussianBarrierPotential_le hx) hc
    _ = (x + 2) * (c * ∫ z : ℝ, standardGaussianKernel z) := by ring
    _ = (x + 2) * ∫ z : ℝ, gaussianPDFReal 0 1 z := by
      congr 1
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z ↦ by
        rw [gaussianPDFReal_zero_one_eq]
    _ = x + 2 := by
      rw [integral_gaussianPDFReal_eq_one 0 (by norm_num)]
      ring

/-- A nondegenerate real Gaussian density is bounded by its value at its
mean. -/
theorem gaussianPDFReal_le_peak
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    gaussianPDFReal m v x ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
  unfold gaussianPDFReal
  have hden : 0 < (2 : ℝ) * (v : ℝ) := by
    positivity
  have hexponent : -(x - m) ^ 2 / (2 * (v : ℝ)) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) hden.le
  have hexp : Real.exp (-(x - m) ^ 2 / (2 * (v : ℝ))) ≤ 1 := by
    simpa only [Real.exp_zero] using! Real.exp_le_exp.mpr hexponent
  exact mul_le_of_le_one_right (by positivity) hexp

/-- The real mass of a Gaussian interval is bounded by its length times the
peak density.  No normal-CDF API is needed. -/
theorem gaussianReal_real_Icc_le
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {a b : ℝ} (hab : a ≤ b) :
    (gaussianReal m v).real (Icc a b) ≤
      (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * (b - a) := by
  rw [Measure.real, gaussianReal_apply_eq_integral m hv]
  rw [ENNReal.toReal_ofReal]
  · calc
      (∫ x in Icc a b, gaussianPDFReal m v x) ≤
          ∫ _x in Icc a b,
            (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
        apply setIntegral_mono_on
        · exact (integrable_gaussianPDFReal m v).integrableOn
        · exact integrableOn_const (by simp)
        · exact measurableSet_Icc
        · intro x hx
          exact gaussianPDFReal_le_peak m hv x
      _ = (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * (b - a) := by
        rw [setIntegral_const, Measure.real_def, Real.volume_Icc,
          ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
        simp only [smul_eq_mul]
        ring
  · exact integral_nonneg fun x ↦ gaussianPDFReal_nonneg m v x

/-- A version with a coarser but cleaner peak `1 / sqrt v`. -/
theorem gaussianReal_real_Icc_le_inv_sqrt
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {a b : ℝ} (hab : a ≤ b) :
    (gaussianReal m v).real (Icc a b) ≤
      (b - a) / Real.sqrt (v : ℝ) := by
  have hpi : 1 ≤ 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hv0 : 0 ≤ (v : ℝ) := v.2
  have hsqrtv : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hsqrt : Real.sqrt (v : ℝ) ≤
      Real.sqrt (2 * Real.pi * (v : ℝ)) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  calc
    (gaussianReal m v).real (Icc a b) ≤
        (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * (b - a) :=
      gaussianReal_real_Icc_le m hv hab
    _ ≤ (Real.sqrt (v : ℝ))⁻¹ * (b - a) := by
      exact mul_le_mul_of_nonneg_right (inv_anti₀ hsqrtv hsqrt)
        (sub_nonneg.mpr hab)
    _ = (b - a) / Real.sqrt (v : ℝ) := by ring

/-- Abstract near/far terminal-distance split for a barrier event.  The
weighted estimate is the output supplied by a positive supermartingale; the
small-distance estimate is supplied by an endpoint density bound. -/
theorem measureReal_barrier_le_of_terminal_split
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] {A near : Set Ω} (hA : MeasurableSet A)
    (hnear : MeasurableSet near) {D : Ω → ℝ} {r V M : ℝ}
    (hr : 0 < r)
    (hDnonneg : ∀ omega ∈ A, 0 ≤ D omega)
    (hDintegrable : IntegrableOn D A P)
    (hD : ∀ omega ∈ A \ near, r ≤ D omega)
    (hweighted : ∫ omega in A, D omega ∂P ≤ V)
    (hnearMass : P.real (A ∩ near) ≤ r * M) :
    P.real A ≤ V / r + r * M := by
  have hfarMeas : MeasurableSet (A \ near) := hA.diff hnear
  have hsplit : A = (A ∩ near) ∪ (A \ near) := by
    ext omega
    by_cases h : omega ∈ near <;> simp
  have hfarWeighted :
      r * P.real (A \ near) ≤ ∫ omega in A \ near, D omega ∂P := by
    calc
      r * P.real (A \ near) = ∫ _omega in A \ near, r ∂P := by
        rw [setIntegral_const]
        simp only [smul_eq_mul]
        ring
      _ ≤ ∫ omega in A \ near, D omega ∂P := by
        apply setIntegral_mono_on
        · exact integrableOn_const
        · exact hDintegrable.mono_set diff_subset
        · exact hfarMeas
        · intro omega homega
          exact hD omega homega
  have hfarIntegral_le :
      (∫ omega in A \ near, D omega ∂P) ≤ ∫ omega in A, D omega ∂P := by
    apply setIntegral_mono_set hDintegrable
    · change ∀ᵐ omega ∂P.restrict A, (0 : ℝ) ≤ D omega
      rw [ae_restrict_iff' hA]
      exact Filter.Eventually.of_forall fun omega homega ↦
        hDnonneg omega homega
    · filter_upwards with omega
      exact fun homega ↦ diff_subset homega
  have hfarMass : P.real (A \ near) ≤ V / r := by
    rw [le_div_iff₀ hr]
    rw [mul_comm]
    exact (hfarWeighted.trans hfarIntegral_le).trans hweighted
  rw [hsplit]
  calc
    P.real ((A ∩ near) ∪ (A \ near)) ≤
        P.real (A ∩ near) + P.real (A \ near) :=
      measureReal_union_le _ _
    _ ≤ r * M + V / r := add_le_add hnearMass hfarMass
    _ = V / r + r * M := add_comm _ _

end Problem520
end Erdos
