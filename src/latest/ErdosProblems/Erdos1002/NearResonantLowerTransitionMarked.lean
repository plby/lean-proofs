import ErdosProblems.Erdos1002.NearResonantLiteralMerge
import ErdosProblems.Erdos1002.MarkedShotFunctional
import ErdosProblems.Erdos1002.AnnularGridPartition
import ErdosProblems.Erdos1002.AnnularShotConvergence
import ErdosProblems.Erdos1002.AnnularCompoundPoissonGrid
import ErdosProblems.Erdos1002.ContinuousCompoundPoissonMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The lower smoothing transition as a literal marked shot

For the convention `a=A/(2 log N)`, the smooth near profile contains one
extra inner transition below the sharp cutoff `|xi|=A`.  This file writes
that residual exactly as a compactly supported function of the marked
resonance coordinate.  It is the precise interface required by a marked
point-process convergence theorem; no informal continuous-mapping step is
hidden in the definition.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators ComplexConjugate ENNReal Real

namespace Erdos1002

noncomputable section

open MultivariateFactorialMomentMethod

local instance probabilityMeasureWeakTopologyLowerTransition :
    TopologicalSpace (ProbabilityMeasure ℝ) :=
  ProbabilityMeasure.instTopologicalSpace

local instance lowerTransitionMarkedPropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- Radial weight of the lower transition in the scaled coordinate
`xi=(log N) p delta_p`.  It is zero on `|xi|<=A/2`, rises smoothly to one,
and is sharply deleted outside `|xi|<=A`. -/
def lowerTransitionRadialWeight (A xi : ℝ) : ℝ :=
  if |xi| ≤ A then
    1 - gevreyOuterCutoff 2 (2 * xi / A)
  else 0

theorem measurable_lowerTransitionRadialWeight (A : ℝ) :
    Measurable (lowerTransitionRadialWeight A) := by
  unfold lowerTransitionRadialWeight
  apply Measurable.ite
  · exact measurableSet_le measurable_abs measurable_const
  · exact measurable_const.sub
      ((gevreyOuterCutoff_contDiff (m := (⊤ : ℕ∞)) 2).continuous.measurable.comp
        ((measurable_const.mul measurable_id).div_const A))
  · exact measurable_const

theorem lowerTransitionRadialWeight_mem_Icc
    (A xi : ℝ) :
    lowerTransitionRadialWeight A xi ∈ Set.Icc (0 : ℝ) 1 := by
  unfold lowerTransitionRadialWeight
  by_cases hxi : |xi| ≤ A
  · rw [if_pos hxi]
    have hcut := gevreyOuterCutoff_mem_Icc (by norm_num : (0 : ℝ) < 2)
      (2 * xi / A)
    constructor <;> linarith [hcut.1, hcut.2]
  · rw [if_neg hxi]
    exact ⟨le_rfl, zero_le_one⟩

theorem lowerTransitionRadialWeight_neg (A xi : ℝ) :
    lowerTransitionRadialWeight A (-xi) =
      lowerTransitionRadialWeight A xi := by
  unfold lowerTransitionRadialWeight
  rw [abs_neg]
  by_cases hxi : |xi| ≤ A
  · rw [if_pos hxi, if_pos hxi]
    have harg : 2 * -xi / A = -(2 * xi / A) := by ring
    rw [harg, gevreyOuterCutoff_even]
  · rw [if_neg hxi, if_neg hxi]

theorem lowerTransitionRadialWeight_eq_zero_of_A_lt_abs
    {A xi : ℝ} (hxi : A < |xi|) :
    lowerTransitionRadialWeight A xi = 0 := by
  unfold lowerTransitionRadialWeight
  rw [if_neg (not_le.mpr hxi)]

theorem lowerTransitionRadialWeight_eq_zero_of_abs_le_half
    {A xi : ℝ} (hA : 0 < A) (hxi : |xi| ≤ A / 2) :
    lowerTransitionRadialWeight A xi = 0 := by
  have hxiA : |xi| ≤ A := hxi.trans (by linarith)
  have harg : |2 * xi / A| ≤ (2 : ℝ) / 2 := by
    rw [abs_div, abs_mul, abs_of_pos hA, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply (div_le_iff₀ hA).2
    linarith
  unfold lowerTransitionRadialWeight
  rw [if_pos hxiA,
    gevreyOuterCutoff_eq_one_of_abs_le_half
      (by norm_num : (0 : ℝ) < 2) harg, sub_self]

/-- Exact rescaling identity behind the lower transition.  The right-hand
side is the smooth radial multiplier minus the sharp hard cutoff, restricted
to the near window. -/
theorem lowerTransitionRadialWeight_scaled_eq
    (A ε L v : ℝ) (hA : 0 < A) (hL : 0 < L) (hε : 0 < ε)
    (hAε : A / L ≤ ε / 4) :
    (lowerTransitionRadialWeight A (L * v) : ℂ) =
      if |v| ≤ ε / 4 then
        nearRho (A / (2 * L)) ε v -
          if A < L * |v| then 1 else 0
      else 0 := by
  have ha : 0 < A / (2 * L) := by positivity
  have habs (x : ℝ) : |L * x| = L * |x| := by
    rw [abs_mul, abs_of_pos hL]
  by_cases hquarter : |v| ≤ ε / 4
  · rw [if_pos hquarter]
    by_cases hminor : A < L * |v|
    · have hnotWeight : ¬ |L * v| ≤ A := by
        rw [habs]
        exact not_le.mpr hminor
      have hdiv : A / L < |v| :=
        (div_lt_iff₀ hL).2 (by simpa [mul_comm] using! hminor)
      have htwo : 2 * (A / (2 * L)) ≤ |v| := by
        have hscale : 2 * (A / (2 * L)) = A / L := by
          field_simp [hL.ne']
        rw [hscale]
        exact hdiv.le
      have hrho : nearRho (A / (2 * L)) ε v = 1 :=
        nearRho_eq_one_of_two_mul_le_abs_of_abs_le_quarter
          (A / (2 * L)) ε v ha hε htwo hquarter
      unfold lowerTransitionRadialWeight
      rw [if_neg hnotWeight, if_pos hminor, hrho, sub_self]
      norm_num
    · have hweight : |L * v| ≤ A := by
        rw [habs]
        exact le_of_not_gt hminor
      have houter : scaledNearProfile (ε / 2) v = 1 := by
        exact scaledNearProfile_eq_one (ε / 2) v (by positivity)
          (hquarter.trans (by linarith))
      have harg : v / (A / (2 * L)) = 2 * (L * v) / A := by
        field_simp [hA.ne', hL.ne']
      unfold lowerTransitionRadialWeight
      rw [if_pos hweight, if_neg hminor]
      unfold nearRho
      rw [houter]
      unfold scaledNearProfile nearBaseProfile
      rw [harg]
      push_cast
      ring
  · rw [if_neg hquarter]
    have hquarter' : ε / 4 < |v| := lt_of_not_ge hquarter
    have hA_le : A ≤ L * (ε / 4) := by
      simpa [mul_comm] using! (div_le_iff₀ hL).1 hAε
    have hweight : A < |L * v| := by
      rw [habs]
      exact hA_le.trans_lt (mul_lt_mul_of_pos_left hquarter' hL)
    exact_mod_cast lowerTransitionRadialWeight_eq_zero_of_A_lt_abs hweight

/-- Complex form of the marked lower-transition jump.  Its value is in fact
real, but the complex codomain matches the Fourier-side near sum exactly. -/
def lowerTransitionMarkedKernel (A : ℝ)
    (z : ℝ × ℝ × ℝ) : ℂ :=
  (lowerTransitionRadialWeight A z.2.1 : ℂ) *
    (markedShotKernel z : ℂ)

/-- Real form of the same jump, used to define its probability law. -/
def lowerTransitionMarkedKernelReal (A : ℝ)
    (z : ℝ × ℝ × ℝ) : ℝ :=
  lowerTransitionRadialWeight A z.2.1 * markedShotKernel z

@[simp]
theorem lowerTransitionMarkedKernel_eq_real
    (A : ℝ) (z : ℝ × ℝ × ℝ) :
    lowerTransitionMarkedKernel A z =
      (lowerTransitionMarkedKernelReal A z : ℂ) := by
  unfold lowerTransitionMarkedKernel lowerTransitionMarkedKernelReal
  push_cast
  rfl

theorem markedShotKernel_signed_neg (t x u : ℝ) :
    markedShotKernel (t, -x, u) = -markedShotKernel (t, x, u) := by
  unfold markedShotKernel
  rw [div_neg]

theorem lowerTransitionMarkedKernelReal_signed_neg
    (A t x u : ℝ) :
    lowerTransitionMarkedKernelReal A (t, -x, u) =
      -lowerTransitionMarkedKernelReal A (t, x, u) := by
  unfold lowerTransitionMarkedKernelReal
  rw [lowerTransitionRadialWeight_neg,
    markedShotKernel_signed_neg]
  ring

theorem measurable_lowerTransitionMarkedKernel (A : ℝ) :
    Measurable (lowerTransitionMarkedKernel A) := by
  exact ((measurable_lowerTransitionRadialWeight A).comp
      (measurable_fst.comp measurable_snd)).complex_ofReal.mul
    (measurable_markedShotKernel.complex_ofReal)

theorem measurable_lowerTransitionMarkedKernelReal (A : ℝ) :
    Measurable (lowerTransitionMarkedKernelReal A) := by
  exact ((measurable_lowerTransitionRadialWeight A).comp
      (measurable_fst.comp measurable_snd)).mul
    measurable_markedShotKernel

theorem norm_lowerTransitionMarkedKernel_le_of_half_lt_abs
    {A : ℝ} (hA : 0 < A) (z : ℝ × ℝ × ℝ)
    (hz : A / 2 < |z.2.1|) :
    ‖lowerTransitionMarkedKernel A z‖ ≤ 1 / (4 * A) := by
  unfold lowerTransitionMarkedKernel
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (lowerTransitionRadialWeight_mem_Icc A z.2.1).1,
    Complex.norm_real, Real.norm_eq_abs]
  calc
    lowerTransitionRadialWeight A z.2.1 * |markedShotKernel z| ≤
        1 * ((1 / 8 : ℝ) / |z.2.1|) := by
      exact mul_le_mul
        (lowerTransitionRadialWeight_mem_Icc A z.2.1).2
        (abs_markedShotKernel_le z) (abs_nonneg _)
        (by norm_num)
    _ ≤ 1 * ((1 / 8 : ℝ) / (A / 2)) := by
      gcongr
    _ = 1 / (4 * A) := by field_simp [hA.ne']; ring

theorem norm_lowerTransitionMarkedKernel_le
    {A : ℝ} (hA : 0 < A) (z : ℝ × ℝ × ℝ) :
    ‖lowerTransitionMarkedKernel A z‖ ≤ 1 / (4 * A) := by
  by_cases hz : A / 2 < |z.2.1|
  · exact norm_lowerTransitionMarkedKernel_le_of_half_lt_abs hA z hz
  · have hzero := lowerTransitionRadialWeight_eq_zero_of_abs_le_half
      hA (le_of_not_gt hz)
    unfold lowerTransitionMarkedKernel
    rw [hzero, Complex.ofReal_zero, zero_mul, norm_zero]
    positivity

/-- Literal finite marked functional for the lower transition, with the
same denominator range `2<p≤N` as the carrier argument. -/
def lowerTransitionMarkedFunctional
    (N : ℕ) (A : ℝ) (alpha : ℝ) : ℂ :=
  ∑ p ∈ Finset.Ioc 2 N,
    if IsPrimitiveResonance p alpha then
      lowerTransitionMarkedKernel A (markedResonancePoint N p alpha)
    else 0

def lowerTransitionMarkedFunctionalReal
    (N : ℕ) (A : ℝ) (alpha : ℝ) : ℝ :=
  ∑ p ∈ Finset.Ioc 2 N,
    if IsPrimitiveResonance p alpha then
      lowerTransitionMarkedKernelReal A (markedResonancePoint N p alpha)
    else 0

theorem measurable_lowerTransitionMarkedFunctional
    (N : ℕ) (A : ℝ) :
    Measurable (lowerTransitionMarkedFunctional N A) := by
  unfold lowerTransitionMarkedFunctional
  apply Finset.measurable_fun_sum
  intro p _hp
  apply Measurable.ite (measurableSet_isPrimitiveResonance p)
  · exact (measurable_lowerTransitionMarkedKernel A).comp
      (measurable_markedResonancePoint N p)
  · exact measurable_const

theorem measurable_lowerTransitionMarkedFunctionalReal
    (N : ℕ) (A : ℝ) :
    Measurable (lowerTransitionMarkedFunctionalReal N A) := by
  unfold lowerTransitionMarkedFunctionalReal
  apply Finset.measurable_fun_sum
  intro p _hp
  apply Measurable.ite (measurableSet_isPrimitiveResonance p)
  · exact (measurable_lowerTransitionMarkedKernelReal A).comp
      (measurable_markedResonancePoint N p)
  · exact measurable_const

theorem lowerTransitionMarkedFunctional_eq_real
    (N : ℕ) (A alpha : ℝ) :
    lowerTransitionMarkedFunctional N A alpha =
      (lowerTransitionMarkedFunctionalReal N A alpha : ℂ) := by
  unfold lowerTransitionMarkedFunctional lowerTransitionMarkedFunctionalReal
  push_cast
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hprim : IsPrimitiveResonance p alpha <;> simp [hprim]

/-- Law of the normalized lower transition.  The exact bridge below shows
that this is also the law of the literal residual once `N` is in the
admissible scale range. -/
def lowerTransitionMarkedLaw (N : ℕ) (A : ℝ) : ProbabilityMeasure ℝ :=
  uniform01.map
    (measurable_lowerTransitionMarkedFunctionalReal N A).aemeasurable

/-! ## The explicit continuum compound-Poisson law -/

/-- The lower-transition jump after suppressing the logarithmic-time
coordinate, which the jump does not use. -/
def lowerTransitionSignedJumpKernel (A : ℝ) (xu : ℝ × ℝ) : ℝ :=
  lowerTransitionRadialWeight A xu.1 * signedAnnularJumpKernel xu

theorem measurable_lowerTransitionSignedJumpKernel (A : ℝ) :
    Measurable (lowerTransitionSignedJumpKernel A) := by
  exact ((measurable_lowerTransitionRadialWeight A).comp measurable_fst).mul
    measurable_signedAnnularJumpKernel

theorem lowerTransitionMarkedKernelReal_eq_signed
    (A : ℝ) (z : ℝ × ℝ × ℝ) :
    lowerTransitionMarkedKernelReal A z =
      lowerTransitionSignedJumpKernel A (z.2.1, z.2.2) := by
  rfl

/-- The normalized law of one lower-transition jump.  Its underlying signed
coordinate is uniform on `(-A,-A/2) ∪ (A/2,A)` and its torus mark is uniform
on `[0,1]`. -/
def lowerTransitionJumpProbability (A : ℝ) : ProbabilityMeasure ℝ :=
  (signedAnnularMarkProbability (A / 2) A).map
    (measurable_lowerTransitionSignedJumpKernel A).aemeasurable

/-- The continuum law of the lower transition.  The Poisson rate is the
actual annular intensity `A / ζ(2)`, not an abstract parameter. -/
def lowerTransitionCompoundPoissonProbability (A : ℝ) : ProbabilityMeasure ℝ :=
  continuousCompoundPoissonProbability (annularPoissonRate (A / 2) A)
    (lowerTransitionJumpProbability A)

/-- Complex exponent integrand of a single unnormalised lower-transition
state. -/
def lowerTransitionSignedExponentIntegrand
    (A t : ℝ) (xu : ℝ × ℝ) : ℂ :=
  Complex.exp ((t : ℂ) * lowerTransitionSignedJumpKernel A xu * Complex.I) - 1

theorem measurable_lowerTransitionSignedExponentIntegrand (A t : ℝ) :
    Measurable (lowerTransitionSignedExponentIntegrand A t) := by
  unfold lowerTransitionSignedExponentIntegrand
  exact (((measurable_const.mul
    (measurable_lowerTransitionSignedJumpKernel A).complex_ofReal).mul
      measurable_const).cexp).sub measurable_const

theorem integrable_lowerTransitionSignedExponentIntegrand_raw
    (A t : ℝ) :
    Integrable (lowerTransitionSignedExponentIntegrand A t)
      ((signedAnnulusFiniteMeasure (A / 2) A : Measure ℝ).prod
        uniform01Measure) := by
  have hExp : Integrable
      (fun xu : ℝ × ℝ ↦
        Complex.exp ((t : ℂ) *
          lowerTransitionSignedJumpKernel A xu * Complex.I))
      ((signedAnnulusFiniteMeasure (A / 2) A : Measure ℝ).prod
        uniform01Measure) := by
    refine (integrable_const (1 : ℝ)).mono
      (((measurable_const.mul
        (measurable_lowerTransitionSignedJumpKernel A).complex_ofReal).mul
          measurable_const).cexp.aestronglyMeasurable) ?_
    filter_upwards with xu
    rw [Complex.norm_exp]
    simp
  exact hExp.sub (integrable_const (1 : ℂ))

theorem charFun_lowerTransitionJumpProbability_sub_one
    {A : ℝ} (hA : 0 < A) (t : ℝ) :
    charFun (lowerTransitionJumpProbability A : Measure ℝ) t - 1 =
      (((signedAnnulusFiniteMeasure (A / 2) A).mass⁻¹ : NNReal) : ℝ) •
        (∫ xu : ℝ × ℝ, lowerTransitionSignedExponentIntegrand A t xu
          ∂((signedAnnulusFiniteMeasure (A / 2) A : Measure ℝ).prod
            uniform01Measure)) := by
  rw [charFun_apply_real, lowerTransitionJumpProbability,
    ProbabilityMeasure.toMeasure_map]
  rw [integral_map
    (measurable_lowerTransitionSignedJumpKernel A).aemeasurable (by fun_prop)]
  have hExp : Integrable
      (fun xu : ℝ × ℝ ↦
        Complex.exp ((t : ℂ) *
          lowerTransitionSignedJumpKernel A xu * Complex.I))
      (signedAnnularMarkProbability (A / 2) A : Measure (ℝ × ℝ)) := by
    refine (integrable_const (1 : ℝ)).mono
      (((measurable_const.mul
        (measurable_lowerTransitionSignedJumpKernel A).complex_ofReal).mul
          measurable_const).cexp.aestronglyMeasurable) ?_
    filter_upwards with xu
    rw [Complex.norm_exp]
    simp
  have hOne : Integrable (fun _ : ℝ × ℝ ↦ (1 : ℂ))
      (signedAnnularMarkProbability (A / 2) A : Measure (ℝ × ℝ)) :=
    integrable_const (1 : ℂ)
  calc
    (∫ xu : ℝ × ℝ,
        Complex.exp ((t : ℂ) *
          lowerTransitionSignedJumpKernel A xu * Complex.I)
        ∂(signedAnnularMarkProbability (A / 2) A : Measure (ℝ × ℝ))) - 1 =
        (∫ xu : ℝ × ℝ,
          Complex.exp ((t : ℂ) *
            lowerTransitionSignedJumpKernel A xu * Complex.I)
          ∂(signedAnnularMarkProbability (A / 2) A : Measure (ℝ × ℝ))) -
          ∫ _xu : ℝ × ℝ, (1 : ℂ)
            ∂(signedAnnularMarkProbability (A / 2) A : Measure (ℝ × ℝ)) := by
      simp
    _ = ∫ xu : ℝ × ℝ, lowerTransitionSignedExponentIntegrand A t xu
          ∂(signedAnnularMarkProbability (A / 2) A : Measure (ℝ × ℝ)) := by
      unfold lowerTransitionSignedExponentIntegrand
      exact (integral_sub hExp hOne).symm
    _ = _ := by
      rw [signedAnnularMarkProbability_toMeasure
        (by positivity : 0 ≤ A / 2) (by linarith : A / 2 < A),
        integral_smul_nnreal_measure]
      simp only [NNReal.smul_def]

/-- The unnormalised continuum exponent of the lower transition. -/
def lowerTransitionPoissonExponent (A t : ℝ) : ℂ :=
  (1 / (Real.pi ^ 2 / 6) : ℝ) •
    (∫ xu : ℝ × ℝ, lowerTransitionSignedExponentIntegrand A t xu
      ∂((signedAnnulusFiniteMeasure (A / 2) A : Measure ℝ).prod
        uniform01Measure))

/-- Exact characteristic function of the explicit continuum law. -/
theorem charFun_lowerTransitionCompoundPoissonProbability
    {A : ℝ} (hA : 0 < A) (t : ℝ) :
    charFun (lowerTransitionCompoundPoissonProbability A : Measure ℝ) t =
      Complex.exp (lowerTransitionPoissonExponent A t) := by
  rw [lowerTransitionCompoundPoissonProbability,
    charFun_continuousCompoundPoissonProbability,
    charFun_lowerTransitionJumpProbability_sub_one hA]
  congr 1
  unfold lowerTransitionPoissonExponent
  rw [coe_annularPoissonRate (by linarith : A / 2 < A),
    signedAnnulusFiniteMeasure_mass
      (by positivity : 0 ≤ A / 2) (by linarith : A / 2 < A)]
  simp only [Complex.real_smul, NNReal.coe_inv]
  have hm : 0 ≤ 2 * (A - A / 2) := by nlinarith
  rw [Real.coe_toNNReal (2 * (A - A / 2)) hm]
  push_cast
  have hAreal : A ≠ 0 := hA.ne'
  have hAcomplex : (A : ℂ) ≠ 0 := by exact_mod_cast hAreal
  field_simp [hAreal, hAcomplex, Real.pi_ne_zero]

/-! ## Compact annular state-space realization -/

def lowerTransitionMarkedRegion (A : ℝ) : Set (ℝ × ℝ × ℝ) :=
  compactAnnularMarkedRegion (A / 2) A

theorem isCompact_lowerTransitionMarkedRegion (A : ℝ) :
    IsCompact (lowerTransitionMarkedRegion A) :=
  isCompact_compactAnnularMarkedRegion (A / 2) A

theorem measurableSet_lowerTransitionMarkedRegion (A : ℝ) :
    MeasurableSet (lowerTransitionMarkedRegion A) :=
  (isCompact_lowerTransitionMarkedRegion A).isClosed.measurableSet

/-- The unscaled limiting state intensity of the annulus
`A/2 < |xi| < A` has total mass exactly `A`. -/
theorem annularRawStateMeasure_lowerTransition_univ
    {A : ℝ} (hA : 0 < A) :
    (annularRawStateMeasure (A / 2) A).real Set.univ = A := by
  unfold annularRawStateMeasure
  rw [measureReal_def, ← univ_prod_univ, Measure.prod_prod,
    show uniform01Measure Set.univ = 1 by simp, one_mul,
    ← univ_prod_univ, Measure.prod_prod,
    show uniform01Measure Set.univ = 1 by simp, mul_one]
  rw [← FiniteMeasure.ennreal_mass,
    signedAnnulusFiniteMeasure_mass (by positivity : 0 ≤ A / 2)
      (by linarith : A / 2 < A)]
  rw [ENNReal.coe_toReal]
  rw [show 2 * (A - A / 2) = A by ring]
  exact Real.coe_toNNReal A hA.le

theorem abs_lowerTransitionMarkedKernelReal_le
    {A : ℝ} (hA : 0 < A) (z : ℝ × ℝ × ℝ) :
    |lowerTransitionMarkedKernelReal A z| ≤ 1 / (4 * A) := by
  have h := norm_lowerTransitionMarkedKernel_le hA z
  rw [lowerTransitionMarkedKernel_eq_real,
    Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- The raw second-moment integral of the limiting lower-transition jump is
`O(1/A)`.  This bound is deliberately elementary: total annular mass is
`A`, and every jump has magnitude at most `1/(4A)`. -/
theorem integral_lowerTransitionMarkedKernelReal_sq_le
    {A : ℝ} (hA : 0 < A) :
    (∫ z : ℝ × ℝ × ℝ,
        lowerTransitionMarkedKernelReal A z ^ 2
          ∂annularRawStateMeasure (A / 2) A) ≤
      1 / (16 * A) := by
  let C : ℝ := (1 / (4 * A)) ^ 2
  have hC : 0 ≤ C := sq_nonneg _
  have hmeas : AEStronglyMeasurable
      (fun z : ℝ × ℝ × ℝ ↦
        lowerTransitionMarkedKernelReal A z ^ 2)
      (annularRawStateMeasure (A / 2) A) :=
    ((measurable_lowerTransitionMarkedKernelReal A).pow_const 2).aestronglyMeasurable
  have hfun : Integrable
      (fun z : ℝ × ℝ × ℝ ↦
        lowerTransitionMarkedKernelReal A z ^ 2)
      (annularRawStateMeasure (A / 2) A) := by
    apply (integrable_const C).mono hmeas
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg hC]
    simpa only [C, sq_abs] using!
      (pow_le_pow_left₀ (abs_nonneg _)
        (abs_lowerTransitionMarkedKernelReal_le hA z) 2)
  calc
    (∫ z : ℝ × ℝ × ℝ,
        lowerTransitionMarkedKernelReal A z ^ 2
          ∂annularRawStateMeasure (A / 2) A) ≤
        ∫ _z : ℝ × ℝ × ℝ, C
          ∂annularRawStateMeasure (A / 2) A := by
      apply integral_mono hfun (integrable_const C)
      intro z
      simpa only [C, sq_abs] using!
        (pow_le_pow_left₀ (abs_nonneg _)
          (abs_lowerTransitionMarkedKernelReal_le hA z) 2)
    _ = A * C := by
      rw [integral_const, smul_eq_mul,
        annularRawStateMeasure_lowerTransition_univ hA]
    _ = 1 / (16 * A) := by
      dsimp [C]
      field_simp [hA.ne']
      ring

/-- Signed-coordinate symmetry centers the limiting lower-transition jump
exactly, before any tail inequality is applied. -/
theorem integral_lowerTransitionMarkedKernelReal_section_eq_zero
    {A : ℝ} (hA : 0 < A) (t u : ℝ) :
    (∫ x : ℝ, lowerTransitionMarkedKernelReal A (t, x, u)
      ∂(signedAnnulusFiniteMeasure (A / 2) A : Measure ℝ)) = 0 := by
  let f : ℝ → ℝ := fun x ↦
    lowerTransitionMarkedKernelReal A (t, x, u)
  have hfinite : volume (signedAnnulusSet (A / 2) A) ≠ ∞ := by
    unfold signedAnnulusSet
    have hnegTop : volume (Ioo (-A) (-(A / 2))) < ∞ := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_lt_top
    have hposTop : volume (Ioo (A / 2) A) < ∞ := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_lt_top
    exact (measure_union_lt_top hnegTop hposTop).ne
  have hfull : IntegrableOn f (signedAnnulusSet (A / 2) A) volume := by
    refine Integrable.mono
      (integrableOn_const (C := 1 / (4 * A)) (hs := hfinite)) ?_ ?_
    · exact ((measurable_lowerTransitionMarkedKernelReal A).comp
          (measurable_const.prodMk (measurable_id.prodMk measurable_const)))
        |>.aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ 1 / (4 * A))]
      exact abs_lowerTransitionMarkedKernelReal_le hA (t, x, u)
  have hneg : IntegrableOn f (Ioo (-A) (-(A / 2))) volume := by
    apply hfull.mono_set
    intro x hx
    exact Or.inl hx
  have hpos : IntegrableOn f (Ioo (A / 2) A) volume := by
    apply hfull.mono_set
    intro x hx
    exact Or.inr hx
  have hnegInt : IntervalIntegrable f volume (-A) (-(A / 2)) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).mpr hneg
  have hposInt : IntervalIntegrable f volume (A / 2) A :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).mpr hpos
  have hnegCompInt : IntervalIntegrable (fun x ↦ f (-x)) volume
      (A / 2) A := by
    have h := (IntervalIntegrable.iff_comp_neg
      (f := f) (a := -A) (b := -(A / 2))).mp hnegInt
    simpa only [neg_neg] using! h.symm
  rw [signedAnnulusFiniteMeasure_toMeasure]
  change (∫ x : ℝ in signedAnnulusSet (A / 2) A, f x) = 0
  rw [signedAnnulusSet,
    integral_union_ae
      (disjoint_signedAnnulus_halves (by positivity : 0 ≤ A / 2)).aedisjoint
      measurableSet_Ioo.nullMeasurableSet hneg hpos]
  have hnegSet :
      (∫ x : ℝ in Ioo (-A) (-(A / 2)), f x) =
        ∫ x : ℝ in -A..-(A / 2), f x := by
    rw [intervalIntegral.integral_of_le (by linarith),
      integral_Ioc_eq_integral_Ioo]
  have hposSet :
      (∫ x : ℝ in Ioo (A / 2) A, f x) =
        ∫ x : ℝ in A / 2..A, f x := by
    rw [intervalIntegral.integral_of_le (by linarith),
      integral_Ioc_eq_integral_Ioo]
  rw [hnegSet, hposSet]
  have hreflect :
      (∫ x : ℝ in -A..-(A / 2), f x) =
        ∫ x : ℝ in A / 2..A, f (-x) := by
    simpa only [neg_neg] using!
      (intervalIntegral.integral_comp_neg
        (a := A / 2) (b := A) f).symm
  rw [hreflect, ← intervalIntegral.integral_add hnegCompInt hposInt]
  have hzero : (fun x : ℝ ↦ f (-x) + f x) = fun _x ↦ 0 := by
    funext x
    dsimp [f]
    rw [lowerTransitionMarkedKernelReal_signed_neg]
    ring
  rw [hzero, intervalIntegral.integral_zero]

theorem integrable_lowerTransitionMarkedKernelReal_raw
    {A : ℝ} (hA : 0 < A) :
    Integrable (lowerTransitionMarkedKernelReal A)
      (annularRawStateMeasure (A / 2) A) := by
  apply (integrable_const (1 / (4 * A))).mono
  · exact (measurable_lowerTransitionMarkedKernelReal A).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ 1 / (4 * A))]
    exact abs_lowerTransitionMarkedKernelReal_le hA z

/-- The raw first moment is exactly zero.  Consequently the Poisson second
moment has no squared-mean term; its variance is the intensity-scaled jump
second moment. -/
theorem integral_lowerTransitionMarkedKernelReal_eq_zero
    {A : ℝ} (hA : 0 < A) :
    (∫ z : ℝ × ℝ × ℝ,
        lowerTransitionMarkedKernelReal A z
          ∂annularRawStateMeasure (A / 2) A) = 0 := by
  have hInt := integrable_lowerTransitionMarkedKernelReal_raw hA
  unfold annularRawStateMeasure at hInt ⊢
  rw [integral_prod _ hInt]
  have hinner (t : ℝ) :
      (∫ xu : ℝ × ℝ,
          lowerTransitionMarkedKernelReal A (t, xu.1, xu.2)
            ∂(signedAnnulusFiniteMeasure (A / 2) A : Measure ℝ).prod
              uniform01Measure) = 0 := by
    have hIntInner : Integrable
        (fun xu : ℝ × ℝ ↦
          lowerTransitionMarkedKernelReal A (t, xu.1, xu.2))
        ((signedAnnulusFiniteMeasure (A / 2) A : Measure ℝ).prod
          uniform01Measure) := by
      apply (integrable_const (1 / (4 * A))).mono
      · exact ((measurable_lowerTransitionMarkedKernelReal A).comp
          (measurable_const.prodMk (measurable_fst.prodMk measurable_snd)))
          |>.aestronglyMeasurable
      · filter_upwards with xu
        rw [Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by positivity : 0 ≤ 1 / (4 * A))]
        exact abs_lowerTransitionMarkedKernelReal_le hA (t, xu.1, xu.2)
    rw [integral_prod_symm _ hIntInner]
    apply integral_eq_zero_of_ae
    exact Eventually.of_forall fun u ↦
      integral_lowerTransitionMarkedKernelReal_section_eq_zero hA t u
  apply integral_eq_zero_of_ae
  exact Eventually.of_forall hinner

/-- Intensity-scaled version of the second-moment bound. -/
theorem lowerTransitionPoissonVarianceIntegral_le
    {A : ℝ} (hA : 0 < A) :
    (1 / (Real.pi ^ 2 / 6)) *
        (∫ z : ℝ × ℝ × ℝ,
          lowerTransitionMarkedKernelReal A z ^ 2
            ∂annularRawStateMeasure (A / 2) A) ≤
      (1 / (Real.pi ^ 2 / 6)) * (1 / (16 * A)) := by
  gcongr
  exact integral_lowerTransitionMarkedKernelReal_sq_le hA

/-! ## Second moment and deletion tail of the continuum transition law -/

theorem integral_lowerTransitionSignedJumpKernel_raw_eq_zero
    {A : ℝ} (hA : 0 < A) :
    (∫ xu : ℝ × ℝ, lowerTransitionSignedJumpKernel A xu
      ∂((signedAnnulusFiniteMeasure (A / 2) A : Measure ℝ).prod
        uniform01Measure)) = 0 := by
  have hInt := integrable_lowerTransitionMarkedKernelReal_raw hA
  have hfull := integral_lowerTransitionMarkedKernelReal_eq_zero hA
  unfold annularRawStateMeasure at hInt hfull
  rw [integral_prod _ hInt] at hfull
  simp only [lowerTransitionMarkedKernelReal_eq_signed] at hfull
  rw [integral_const] at hfull
  simpa using! hfull

theorem integral_lowerTransitionSignedJumpKernel_sq_raw_le
    {A : ℝ} (hA : 0 < A) :
    (∫ xu : ℝ × ℝ, lowerTransitionSignedJumpKernel A xu ^ 2
      ∂((signedAnnulusFiniteMeasure (A / 2) A : Measure ℝ).prod
        uniform01Measure)) ≤ 1 / (16 * A) := by
  have hfull := integral_lowerTransitionMarkedKernelReal_sq_le hA
  have hIntFull : Integrable
      (fun z : ℝ × ℝ × ℝ ↦ lowerTransitionMarkedKernelReal A z ^ 2)
      (annularRawStateMeasure (A / 2) A) := by
    apply (integrable_const ((1 / (4 * A)) ^ 2)).mono
    · exact ((measurable_lowerTransitionMarkedKernelReal A).pow_const 2)
        |>.aestronglyMeasurable
    · filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
        Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs] using!
        pow_le_pow_left₀ (abs_nonneg _)
          (abs_lowerTransitionMarkedKernelReal_le hA z) 2
  unfold annularRawStateMeasure at hIntFull hfull
  rw [integral_prod _ hIntFull] at hfull
  simp only [lowerTransitionMarkedKernelReal_eq_signed] at hfull
  rw [integral_const] at hfull
  simpa using! hfull

theorem integrable_id_lowerTransitionJumpProbability
    {A : ℝ} (hA : 0 < A) :
    Integrable (fun x : ℝ ↦ x)
      (lowerTransitionJumpProbability A : Measure ℝ) := by
  rw [lowerTransitionJumpProbability, ProbabilityMeasure.toMeasure_map,
    integrable_map_measure (by fun_prop)
      (measurable_lowerTransitionSignedJumpKernel A).aemeasurable]
  apply (integrable_const (1 / (4 * A))).mono
  · exact (measurable_lowerTransitionSignedJumpKernel A).aestronglyMeasurable
  · filter_upwards with xu
    simp only [Function.comp_apply, Real.norm_eq_abs]
    simpa [lowerTransitionMarkedKernelReal_eq_signed, abs_of_pos hA] using!
      abs_lowerTransitionMarkedKernelReal_le hA (0, xu.1, xu.2)

theorem integral_id_lowerTransitionJumpProbability_eq_zero
    {A : ℝ} (hA : 0 < A) :
    (∫ x : ℝ, x ∂(lowerTransitionJumpProbability A : Measure ℝ)) = 0 := by
  rw [lowerTransitionJumpProbability, ProbabilityMeasure.toMeasure_map,
    integral_map
      (measurable_lowerTransitionSignedJumpKernel A).aemeasurable (by fun_prop)]
  rw [signedAnnularMarkProbability_toMeasure
    (by positivity : 0 ≤ A / 2) (by linarith : A / 2 < A),
    integral_smul_nnreal_measure,
    integral_lowerTransitionSignedJumpKernel_raw_eq_zero hA]
  simp

theorem integrable_sq_lowerTransitionJumpProbability
    {A : ℝ} (hA : 0 < A) :
    Integrable (fun x : ℝ ↦ x ^ 2)
      (lowerTransitionJumpProbability A : Measure ℝ) := by
  rw [lowerTransitionJumpProbability, ProbabilityMeasure.toMeasure_map,
    integrable_map_measure (by fun_prop)
      (measurable_lowerTransitionSignedJumpKernel A).aemeasurable]
  apply (integrable_const ((1 / (4 * A)) ^ 2)).mono
  · exact ((measurable_lowerTransitionSignedJumpKernel A).pow_const 2)
      |>.aestronglyMeasurable
  · filter_upwards with xu
    simp only [Function.comp_apply, Real.norm_eq_abs]
    rw [abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (sq_nonneg (1 / (4 * A)))]
    have hb : |lowerTransitionSignedJumpKernel A xu| ≤ 1 / (4 * A) := by
      simpa [lowerTransitionMarkedKernelReal_eq_signed] using!
        abs_lowerTransitionMarkedKernelReal_le hA (0, xu.1, xu.2)
    have hp := pow_le_pow_left₀
      (abs_nonneg (lowerTransitionSignedJumpKernel A xu)) hb 2
    simpa only [sq_abs] using! hp

/-- The normalized one-jump second moment is `O(A⁻²)`. -/
theorem integral_sq_lowerTransitionJumpProbability_le
    {A : ℝ} (hA : 0 < A) :
    (∫ x : ℝ, x ^ 2
      ∂(lowerTransitionJumpProbability A : Measure ℝ)) ≤ 1 / (16 * A ^ 2) := by
  rw [lowerTransitionJumpProbability, ProbabilityMeasure.toMeasure_map,
    integral_map
      (measurable_lowerTransitionSignedJumpKernel A).aemeasurable (by fun_prop)]
  rw [signedAnnularMarkProbability_toMeasure
    (by positivity : 0 ≤ A / 2) (by linarith : A / 2 < A),
    integral_smul_nnreal_measure]
  simp only [NNReal.smul_def]
  have hraw := integral_lowerTransitionSignedJumpKernel_sq_raw_le hA
  have hmass := signedAnnulusFiniteMeasure_mass
    (by positivity : 0 ≤ A / 2) (by linarith : A / 2 < A)
  rw [hmass]
  simp only [NNReal.coe_inv]
  have hmassPos : 0 <
      (((Real.toNNReal (2 * (A - A / 2)))⁻¹ : NNReal) : ℝ) := by
    have hbase : 0 < Real.toNNReal (2 * (A - A / 2)) := by
      rw [Real.toNNReal_pos]
      nlinarith
    exact_mod_cast inv_pos.mpr hbase
  calc
    (((Real.toNNReal (2 * (A - A / 2)))⁻¹ : NNReal) : ℝ) *
        (∫ xu : ℝ × ℝ, lowerTransitionSignedJumpKernel A xu ^ 2
          ∂((signedAnnulusFiniteMeasure (A / 2) A : Measure ℝ).prod
            uniform01Measure)) ≤
      (((Real.toNNReal (2 * (A - A / 2)))⁻¹ : NNReal) : ℝ) *
        (1 / (16 * A)) := mul_le_mul_of_nonneg_left hraw hmassPos.le
    _ = 1 / (16 * A ^ 2) := by
      rw [show 2 * (A - A / 2) = A by ring, NNReal.coe_inv,
        Real.coe_toNNReal A hA.le]
      field_simp [hA.ne']

theorem integrable_sq_lowerTransitionCompoundPoissonProbability
    {A : ℝ} (hA : 0 < A) :
    Integrable (fun x : ℝ ↦ x ^ 2)
      (lowerTransitionCompoundPoissonProbability A : Measure ℝ) := by
  unfold lowerTransitionCompoundPoissonProbability
  exact integrable_sq_continuousCompoundPoissonProbability_of_centered
    (annularPoissonRate (A / 2) A) (lowerTransitionJumpProbability A)
    (integrable_id_lowerTransitionJumpProbability hA)
    (integral_id_lowerTransitionJumpProbability_eq_zero hA)
    (integrable_sq_lowerTransitionJumpProbability hA)

/-- The continuum lower-transition second moment is `O(A⁻¹)`.  The
centering is essential: without the exact zero first moment above there
would be an additional squared-mean contribution. -/
theorem integral_sq_lowerTransitionCompoundPoissonProbability_le
    {A : ℝ} (hA : 0 < A) :
    (∫ x : ℝ, x ^ 2
      ∂(lowerTransitionCompoundPoissonProbability A : Measure ℝ)) ≤
      (1 / (Real.pi ^ 2 / 6)) * (1 / (16 * A)) := by
  rw [lowerTransitionCompoundPoissonProbability,
    integral_sq_continuousCompoundPoissonProbability_of_centered
      (annularPoissonRate (A / 2) A) (lowerTransitionJumpProbability A)
      (integrable_id_lowerTransitionJumpProbability hA)
      (integral_id_lowerTransitionJumpProbability_eq_zero hA)
      (integrable_sq_lowerTransitionJumpProbability hA)]
  have hjump := integral_sq_lowerTransitionJumpProbability_le hA
  have hrate : (annularPoissonRate (A / 2) A : ℝ) =
      A / (Real.pi ^ 2 / 6) := by
    rw [coe_annularPoissonRate (by linarith : A / 2 < A)]
    ring
  rw [hrate]
  calc
    A / (Real.pi ^ 2 / 6) *
        (∫ x : ℝ, x ^ 2
          ∂(lowerTransitionJumpProbability A : Measure ℝ)) ≤
      A / (Real.pi ^ 2 / 6) * (1 / (16 * A ^ 2)) := by
        gcongr
    _ = (1 / (Real.pi ^ 2 / 6)) * (1 / (16 * A)) := by
      field_simp [hA.ne', Real.pi_ne_zero]

/-- Chebyshev deletion estimate for the lower transition.  For every fixed
positive threshold `R`, its limiting probability is `O(1/A)`. -/
theorem lowerTransitionCompoundPoisson_tail_le
    {A R : ℝ} (hA : 0 < A) (hR : 0 < R) :
    (lowerTransitionCompoundPoissonProbability A : Measure ℝ).real
        {x : ℝ | R ≤ |x|} ≤
      ((1 / (Real.pi ^ 2 / 6)) * (1 / (16 * A))) / R ^ 2 := by
  let μ : Measure ℝ :=
    (lowerTransitionCompoundPoissonProbability A : Measure ℝ)
  have hInt : Integrable (fun x : ℝ ↦ x ^ 2) μ := by
    simpa only [μ] using!
      integrable_sq_lowerTransitionCompoundPoissonProbability hA
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (Eventually.of_forall fun x : ℝ ↦ sq_nonneg x)
      hInt (R ^ 2)
  have hset : {x : ℝ | R ≤ |x|} = {x : ℝ | R ^ 2 ≤ x ^ 2} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hx
      simpa only [sq_abs] using!
        (sq_le_sq₀ hR.le (abs_nonneg x)).2 hx
    · intro hx
      exact (sq_le_sq₀ hR.le (abs_nonneg x)).1
        (by simpa only [sq_abs] using! hx)
  rw [hset]
  have hsecond := integral_sq_lowerTransitionCompoundPoissonProbability_le hA
  have hmul : R ^ 2 * μ.real {x : ℝ | R ^ 2 ≤ x ^ 2} ≤
      (1 / (Real.pi ^ 2 / 6)) * (1 / (16 * A)) :=
    hmarkov.trans hsecond
  rw [div_eq_mul_inv]
  exact (le_mul_inv_iff₀ (sq_pos_of_pos hR)).2 (by
    simpa only [mul_comm] using! hmul)

/-- The displayed deletion majorant really tends to zero in the required
outer-cutoff order. -/
theorem tendsto_lowerTransitionCompoundPoisson_tail_majorant
    {R : ℝ} (hR : 0 < R) :
    Tendsto
      (fun m : ℕ ↦
        ((1 / (Real.pi ^ 2 / 6)) *
          (1 / (16 * ((m + 1 : ℕ) : ℝ)))) / R ^ 2)
      atTop (nhds 0) := by
  let C : ℝ := ((1 / (Real.pi ^ 2 / 6)) * (1 / 16)) / R ^ 2
  have h := (tendsto_const_div_atTop_nhds_zero_nat C).comp
    (tendsto_add_atTop_nat 1)
  apply h.congr'
  filter_upwards with m
  dsimp [C]
  have hm : (((m + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hm, hR.ne', Real.pi_ne_zero]

theorem lowerTransitionMarkedKernelReal_eq_smooth_on_region
    {A : ℝ} (hA : 0 ≤ A) (z : ℝ × ℝ × ℝ)
    (hz : z ∈ lowerTransitionMarkedRegion A) :
    lowerTransitionMarkedKernelReal A z =
      (1 - gevreyOuterCutoff 2 (2 * z.2.1 / A)) *
        markedShotKernel z := by
  unfold lowerTransitionMarkedKernelReal lowerTransitionRadialWeight
  rw [if_pos]
  unfold lowerTransitionMarkedRegion compactAnnularMarkedRegion at hz
  have hx := (mem_signedAnnulus_iff_abs (by positivity : 0 ≤ A / 2)).mp hz.2.1
  exact hx.2

theorem continuousOn_lowerTransitionMarkedKernelReal
    {A : ℝ} (hA : 0 < A) :
    ContinuousOn (lowerTransitionMarkedKernelReal A)
      (lowerTransitionMarkedRegion A) := by
  let k : ℝ × ℝ × ℝ → ℝ := fun z ↦
    (1 - gevreyOuterCutoff 2 (2 * z.2.1 / A)) * markedShotKernel z
  have hradial : Continuous (fun z : ℝ × ℝ × ℝ ↦
      1 - gevreyOuterCutoff 2 (2 * z.2.1 / A)) := by
    exact continuous_const.sub
      ((gevreyOuterCutoff_contDiff (m := (⊤ : ℕ∞)) 2).continuous.comp
        (by fun_prop))
  have hshot : ContinuousOn markedShotKernel
      (lowerTransitionMarkedRegion A) := by
    apply continuousOn_markedShotKernel_away_zero.mono
    intro z hz
    unfold lowerTransitionMarkedRegion compactAnnularMarkedRegion at hz
    have hx := (mem_signedAnnulus_iff_abs (by positivity : 0 ≤ A / 2)).mp hz.2.1
    intro hzero
    rw [hzero, abs_zero] at hx
    linarith
  have hk : ContinuousOn k (lowerTransitionMarkedRegion A) :=
    hradial.continuousOn.mul hshot
  apply hk.congr
  intro z hz
  exact lowerTransitionMarkedKernelReal_eq_smooth_on_region hA.le z hz

theorem uniformContinuousOn_lowerTransitionMarkedKernelReal
    {A : ℝ} (hA : 0 < A) :
    UniformContinuousOn (lowerTransitionMarkedKernelReal A)
      (lowerTransitionMarkedRegion A) :=
  (isCompact_lowerTransitionMarkedRegion A).uniformContinuousOn_of_continuous
    (continuousOn_lowerTransitionMarkedKernelReal hA)

/-! ## Tagged-grid convergence to the explicit continuum law -/

/-- Characteristic-exponent integrand on the full three-coordinate state. -/
def lowerTransitionStateExponentIntegrand
    (A t : ℝ) (z : ℝ × ℝ × ℝ) : ℂ :=
  Complex.exp ((t : ℂ) *
    lowerTransitionMarkedKernelReal A z * Complex.I) - 1

theorem measurable_lowerTransitionStateExponentIntegrand (A t : ℝ) :
    Measurable (lowerTransitionStateExponentIntegrand A t) := by
  unfold lowerTransitionStateExponentIntegrand
  exact (((measurable_const.mul
    (measurable_lowerTransitionMarkedKernelReal A).complex_ofReal).mul
      measurable_const).cexp).sub measurable_const

theorem lowerTransitionStateExponentIntegrand_eq_signed
    (A t : ℝ) (z : ℝ × ℝ × ℝ) :
    lowerTransitionStateExponentIntegrand A t z =
      lowerTransitionSignedExponentIntegrand A t (z.2.1, z.2.2) := by
  rfl

theorem integrable_lowerTransitionStateExponentIntegrand
    (A t : ℝ) :
    Integrable (lowerTransitionStateExponentIntegrand A t)
      (annularRawStateMeasure (A / 2) A) := by
  have hraw := integrable_lowerTransitionSignedExponentIntegrand_raw A t
  simpa only [annularRawStateMeasure,
    lowerTransitionStateExponentIntegrand,
    lowerTransitionSignedExponentIntegrand,
    lowerTransitionMarkedKernelReal_eq_signed, Prod.snd] using!
      hraw.comp_snd uniform01Measure

theorem integral_lowerTransitionStateExponentIntegrand
    (A t : ℝ) :
    (∫ z, lowerTransitionStateExponentIntegrand A t z
        ∂annularRawStateMeasure (A / 2) A) =
      ∫ xu, lowerTransitionSignedExponentIntegrand A t xu
        ∂((signedAnnulusFiniteMeasure (A / 2) A : Measure ℝ).prod
          uniform01Measure) := by
  have hInt := integrable_lowerTransitionStateExponentIntegrand A t
  rw [annularRawStateMeasure, integral_prod _ hInt]
  simp only [lowerTransitionStateExponentIntegrand_eq_signed]
  rw [integral_const]
  simp

theorem continuousOn_lowerTransitionStateExponentIntegrand
    {A : ℝ} (hA : 0 < A) (t : ℝ) :
    ContinuousOn (lowerTransitionStateExponentIntegrand A t)
      (lowerTransitionMarkedRegion A) := by
  have hkReal := continuousOn_lowerTransitionMarkedKernelReal hA
  have hkComplex : ContinuousOn
      (fun z ↦ (lowerTransitionMarkedKernelReal A z : ℂ))
      (lowerTransitionMarkedRegion A) := by
    simpa only [Function.comp_apply] using!
      Complex.continuous_ofReal.comp_continuousOn hkReal
  unfold lowerTransitionStateExponentIntegrand
  exact (((continuousOn_const.mul hkComplex).mul
    continuousOn_const).cexp).sub continuousOn_const

theorem uniformContinuousOn_lowerTransitionStateExponentIntegrand
    {A : ℝ} (hA : 0 < A) (t : ℝ) :
    UniformContinuousOn (lowerTransitionStateExponentIntegrand A t)
      (lowerTransitionMarkedRegion A) :=
  (isCompact_lowerTransitionMarkedRegion A).uniformContinuousOn_of_continuous
    (continuousOn_lowerTransitionStateExponentIntegrand hA t)

/-- Unscaled tagged exponent on the explicit annular grid. -/
def lowerTransitionGridTaggedExponent
    (A : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  ∑ i : AnnularGridIndex n,
    (annularRawStateMeasure (A / 2) A).real
        (annularGridCell (A / 2) A n i) •
      lowerTransitionStateExponentIntegrand A t
        (annularGridCenter (A / 2) A n i)

theorem integral_lowerTransitionStateExponentIntegrand_eq_sum_cells
    {A : ℝ} (hA : 0 < A) {n : ℕ} (hn : 0 < n) (t : ℝ) :
    (∫ z, lowerTransitionStateExponentIntegrand A t z
        ∂annularRawStateMeasure (A / 2) A) =
      ∑ i : AnnularGridIndex n,
        ∫ z in annularGridCell (A / 2) A n i,
          lowerTransitionStateExponentIntegrand A t z
            ∂annularRawStateMeasure (A / 2) A := by
  have hInt := integrable_lowerTransitionStateExponentIntegrand A t
  calc
    (∫ z, lowerTransitionStateExponentIntegrand A t z
        ∂annularRawStateMeasure (A / 2) A) =
        ∫ z in lowerTransitionMarkedRegion A,
          lowerTransitionStateExponentIntegrand A t z
            ∂annularRawStateMeasure (A / 2) A := by
      unfold lowerTransitionMarkedRegion
      rw [restrict_compactAnnularMarkedRegion_annularRawStateMeasure]
    _ = ∫ z in ⋃ i : AnnularGridIndex n,
          annularGridCell (A / 2) A n i,
          lowerTransitionStateExponentIntegrand A t z
            ∂annularRawStateMeasure (A / 2) A := by
      rw [iUnion_annularGridCell_eq_compactAnnularMarkedRegion
        (by positivity : 0 < A / 2) (by linarith : A / 2 < A) hn]
      rfl
    _ = _ := integral_iUnion_fintype
      (fun i ↦ measurableSet_annularGridCell (A / 2) A n i)
      (pairwise_disjoint_annularGridCell
        (by positivity : 0 < A / 2) (by linarith : A / 2 < A) hn)
      (fun _i ↦ hInt.integrableOn)

/-- Quantitative tagged-integral error for the lower-transition exponent. -/
theorem norm_lowerTransitionGridTaggedExponent_sub_integral_le
    {A η : ℝ} (hA : 0 < A) {n : ℕ} (hn : 0 < n) (t : ℝ)
    (hclose : ∀ (i : AnnularGridIndex n) z,
      z ∈ annularGridCell (A / 2) A n i →
        ‖lowerTransitionStateExponentIntegrand A t
            (annularGridCenter (A / 2) A n i) -
          lowerTransitionStateExponentIntegrand A t z‖ ≤ η) :
    ‖lowerTransitionGridTaggedExponent A n t -
        ∫ z, lowerTransitionStateExponentIntegrand A t z
          ∂annularRawStateMeasure (A / 2) A‖ ≤
      η * (annularRawStateMeasure (A / 2) A).real
        (lowerTransitionMarkedRegion A) := by
  classical
  rw [integral_lowerTransitionStateExponentIntegrand_eq_sum_cells hA hn]
  unfold lowerTransitionGridTaggedExponent
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ i : AnnularGridIndex n,
        ((annularRawStateMeasure (A / 2) A).real
              (annularGridCell (A / 2) A n i) •
            lowerTransitionStateExponentIntegrand A t
              (annularGridCenter (A / 2) A n i) -
          ∫ z in annularGridCell (A / 2) A n i,
            lowerTransitionStateExponentIntegrand A t z
              ∂annularRawStateMeasure (A / 2) A)‖ ≤
        ∑ i : AnnularGridIndex n,
          ‖(annularRawStateMeasure (A / 2) A).real
                (annularGridCell (A / 2) A n i) •
              lowerTransitionStateExponentIntegrand A t
                (annularGridCenter (A / 2) A n i) -
            ∫ z in annularGridCell (A / 2) A n i,
              lowerTransitionStateExponentIntegrand A t z
                ∂annularRawStateMeasure (A / 2) A‖ := norm_sum_le _ _
    _ ≤ ∑ i : AnnularGridIndex n,
          η * (annularRawStateMeasure (A / 2) A).real
            (annularGridCell (A / 2) A n i) := by
      apply Finset.sum_le_sum
      intro i _hi
      have hcellInt : IntegrableOn
          (lowerTransitionStateExponentIntegrand A t)
          (annularGridCell (A / 2) A n i)
          (annularRawStateMeasure (A / 2) A) :=
        (integrable_lowerTransitionStateExponentIntegrand A t).integrableOn
      have heq :
          (annularRawStateMeasure (A / 2) A).real
                (annularGridCell (A / 2) A n i) •
              lowerTransitionStateExponentIntegrand A t
                (annularGridCenter (A / 2) A n i) -
            ∫ z in annularGridCell (A / 2) A n i,
              lowerTransitionStateExponentIntegrand A t z
                ∂annularRawStateMeasure (A / 2) A =
          ∫ z in annularGridCell (A / 2) A n i,
            (lowerTransitionStateExponentIntegrand A t
                (annularGridCenter (A / 2) A n i) -
              lowerTransitionStateExponentIntegrand A t z)
              ∂annularRawStateMeasure (A / 2) A := by
        rw [integral_sub
          (μ := (annularRawStateMeasure (A / 2) A).restrict
            (annularGridCell (A / 2) A n i))
          (integrableOn_const
            (s := annularGridCell (A / 2) A n i)
            (μ := annularRawStateMeasure (A / 2) A)
            (C := lowerTransitionStateExponentIntegrand A t
              (annularGridCenter (A / 2) A n i)))
          hcellInt, setIntegral_const]
      rw [heq]
      exact norm_setIntegral_le_of_norm_le_const
        (measure_lt_top _ _) (hclose i)
    _ = η * (annularRawStateMeasure (A / 2) A).real
          (lowerTransitionMarkedRegion A) := by
      unfold lowerTransitionMarkedRegion
      rw [← Finset.mul_sum,
        sum_measureReal_annularGridCell
          (by positivity : 0 < A / 2) (by linarith : A / 2 < A) hn]

theorem tendsto_lowerTransitionGridTaggedExponent
    {A : ℝ} (hA : 0 < A) (t : ℝ) :
    Tendsto
      (fun m : ℕ ↦ lowerTransitionGridTaggedExponent A (m + 1) t)
      atTop
      (nhds (∫ z, lowerTransitionStateExponentIntegrand A t z
        ∂annularRawStateMeasure (A / 2) A)) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  let M : ℝ := (annularRawStateMeasure (A / 2) A).real
    (lowerTransitionMarkedRegion A)
  have hM : 0 ≤ M := measureReal_nonneg
  let q : ℝ := η / (M + 1)
  have hq : 0 < q := by
    dsimp [q]
    positivity
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (uniformContinuousOn_lowerTransitionStateExponentIntegrand hA t) q hq
  have htime : ∀ᶠ m : ℕ in atTop,
      (1 : ℝ) / ((m + 1 : ℕ) : ℝ) < δ := by
    simpa only [Nat.cast_add, Nat.cast_one] using!
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually_lt_const hδ
  have hsigned : ∀ᶠ m : ℕ in atTop,
      (A - A / 2) / ((m + 1 : ℕ) : ℝ) < δ := by
    have ht : Tendsto
        (fun m : ℕ ↦ (A - A / 2) / ((m + 1 : ℕ) : ℝ))
        atTop (nhds 0) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using!
        (tendsto_const_div_atTop_nhds_zero_nat (A - A / 2)).comp
          (tendsto_add_atTop_nat 1)
    exact ht.eventually_lt_const hδ
  apply eventually_atTop.1
  filter_upwards [htime, hsigned] with m htm hsm
  have herr := norm_lowerTransitionGridTaggedExponent_sub_integral_le
    hA (show 0 < m + 1 by omega) t (η := q) (by
      intro i z hz
      have hcenter := annularGridCenter_mem_compactAnnularMarkedRegion
        (by linarith : A / 2 < A) (show 0 < m + 1 by omega) i
      have hzK := annularGridCell_subset_compactAnnularMarkedRegion
        (by linarith : A / 2 < A) (show 0 < m + 1 by omega) i hz
      have hdist :
          dist (annularGridCenter (A / 2) A (m + 1) i) z < δ := by
        simpa only [dist_comm] using!
          dist_annularGridCenter_lt (by linarith : A / 2 < A)
            (show 0 < m + 1 by omega) htm hsm i hz
      simpa only [dist_eq_norm] using! (hclose _ hcenter _ hzK hdist).le)
  have hqM : q * M < η := by
    calc
      q * M < q * (M + 1) := by
        exact mul_lt_mul_of_pos_left (by linarith) hq
      _ = η := by
        dsimp [q]
        field_simp
  rw [dist_eq_norm]
  exact herr.trans_lt (by simpa only [M] using! hqM)

/-- Characteristic exponent of the finite independent-Poisson grid with the
actual lower-transition weights. -/
def lowerTransitionGridIndependentPoissonExponent
    (A : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  ∑ i : AnnularGridIndex n,
    (annularGridCellPoissonRate (A / 2) A n i : ℂ) *
      (Complex.exp
        (t * lowerTransitionMarkedKernelReal A
          (annularGridCenter (A / 2) A n i) * Complex.I) - 1)

theorem lowerTransitionGridIndependentPoissonExponent_eq_tagged
    (A : ℝ) (n : ℕ) (t : ℝ) :
    lowerTransitionGridIndependentPoissonExponent A n t =
      (1 / (Real.pi ^ 2 / 6) : ℝ) •
        lowerTransitionGridTaggedExponent A n t := by
  classical
  unfold lowerTransitionGridIndependentPoissonExponent
    lowerTransitionGridTaggedExponent
    lowerTransitionStateExponentIntegrand
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [smul_smul]
  simp only [coe_annularGridCellPoissonRate, Complex.real_smul]
  push_cast
  ring

theorem lowerTransitionPoissonExponent_eq_stateIntegral
    (A t : ℝ) :
    lowerTransitionPoissonExponent A t =
      (1 / (Real.pi ^ 2 / 6) : ℝ) •
        (∫ z, lowerTransitionStateExponentIntegrand A t z
          ∂annularRawStateMeasure (A / 2) A) := by
  unfold lowerTransitionPoissonExponent
  rw [integral_lowerTransitionStateExponentIntegrand]

theorem tendsto_lowerTransitionGridIndependentPoissonExponent
    {A : ℝ} (hA : 0 < A) (t : ℝ) :
    Tendsto
      (fun m : ℕ ↦
        lowerTransitionGridIndependentPoissonExponent A (m + 1) t)
      atTop (nhds (lowerTransitionPoissonExponent A t)) := by
  rw [lowerTransitionPoissonExponent_eq_stateIntegral]
  have h := (tendsto_lowerTransitionGridTaggedExponent hA t).const_smul
    (1 / (Real.pi ^ 2 / 6) : ℝ)
  simpa only [lowerTransitionGridIndependentPoissonExponent_eq_tagged] using! h

/-- The actual independent-Poisson cell laws converge to the explicitly
constructed continuum lower-transition law. -/
theorem tendsto_weightedIndependentPoissonLaw_lowerTransitionGrid
    {A : ℝ} (hA : 0 < A) :
    Tendsto
      (fun m : ℕ ↦ weightedIndependentPoissonLaw
        (annularGridCellPoissonRate (A / 2) A (m + 1))
        (fun i ↦ lowerTransitionMarkedKernelReal A
          (annularGridCenter (A / 2) A (m + 1) i)))
      atTop (nhds (lowerTransitionCompoundPoissonProbability A)) := by
  apply levy_continuity_real
  intro t
  rw [charFun_lowerTransitionCompoundPoissonProbability hA]
  have hExp : Tendsto
      (fun m : ℕ ↦ Complex.exp
        (lowerTransitionGridIndependentPoissonExponent A (m + 1) t))
      atTop
      (nhds (Complex.exp (lowerTransitionPoissonExponent A t))) :=
    Complex.continuous_exp.continuousAt.tendsto.comp
      (tendsto_lowerTransitionGridIndependentPoissonExponent hA t)
  apply hExp.congr'
  filter_upwards with m
  rw [charFun_weightedIndependentPoissonLaw]
  congr 1

theorem exists_uniform_cell_radius_lowerTransitionMarkedKernelReal
    {A η : ℝ} (hA : 0 < A) (hη : 0 < η) :
    ∃ δ > 0, ∀ z ∈ lowerTransitionMarkedRegion A,
      ∀ z' ∈ lowerTransitionMarkedRegion A,
        dist z z' < δ →
          |lowerTransitionMarkedKernelReal A z -
            lowerTransitionMarkedKernelReal A z'| < η := by
  exact Metric.uniformContinuousOn_iff.mp
    (uniformContinuousOn_lowerTransitionMarkedKernelReal hA) η hη

/-- The full denominator range is used by the existing factorial-count
infrastructure.  The difference from the carrier range `p>2` is a separate
finite-endpoint deletion. -/
def lowerTransitionMarkedFunctionalAll
    (N : ℕ) (A : ℝ) (alpha : ℝ) : ℝ :=
  ∑ p ∈ Finset.Icc 1 N,
    if IsPrimitiveResonance p alpha then
      lowerTransitionMarkedKernelReal A (markedResonancePoint N p alpha)
    else 0

theorem measurable_lowerTransitionMarkedFunctionalAll
    (N : ℕ) (A : ℝ) :
    Measurable (lowerTransitionMarkedFunctionalAll N A) := by
  unfold lowerTransitionMarkedFunctionalAll
  apply Finset.measurable_fun_sum
  intro p _hp
  apply Measurable.ite (measurableSet_isPrimitiveResonance p)
  · exact (measurable_lowerTransitionMarkedKernelReal A).comp
      (measurable_markedResonancePoint N p)
  · exact measurable_const

/-- The two fixed denominator terms introduced only to use the existing
all-denominator count-vector infrastructure. -/
def lowerTransitionMarkedEndpointFunctional
    (N : ℕ) (A : ℝ) (alpha : ℝ) : ℝ :=
  ∑ p ∈ Finset.Icc 1 2,
    if IsPrimitiveResonance p alpha then
      lowerTransitionMarkedKernelReal A (markedResonancePoint N p alpha)
    else 0

theorem measurable_lowerTransitionMarkedEndpointFunctional
    (N : ℕ) (A : ℝ) :
    Measurable (lowerTransitionMarkedEndpointFunctional N A) := by
  unfold lowerTransitionMarkedEndpointFunctional
  apply Finset.measurable_fun_sum
  intro p _hp
  apply Measurable.ite (measurableSet_isPrimitiveResonance p)
  · exact (measurable_lowerTransitionMarkedKernelReal A).comp
      (measurable_markedResonancePoint N p)
  · exact measurable_const

/-- Exact denominator split, with no endpoint silently absorbed in either
sum. -/
theorem lowerTransitionMarkedFunctionalAll_eq_endpoint_add
    {N : ℕ} (hN : 2 ≤ N) (A alpha : ℝ) :
    lowerTransitionMarkedFunctionalAll N A alpha =
      lowerTransitionMarkedEndpointFunctional N A alpha +
        lowerTransitionMarkedFunctionalReal N A alpha := by
  classical
  have hsplit : Finset.Icc 1 N =
      Finset.Icc 1 2 ∪ Finset.Ioc 2 N := by
    ext p
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 2) (Finset.Ioc 2 N) := by
    rw [Finset.disjoint_left]
    intro p hpLeft hpRight
    simp only [Finset.mem_Icc] at hpLeft
    simp only [Finset.mem_Ioc] at hpRight
    omega
  unfold lowerTransitionMarkedFunctionalAll
    lowerTransitionMarkedEndpointFunctional
    lowerTransitionMarkedFunctionalReal
  rw [hsplit, Finset.sum_union hdisj]

/-- On `(0,1)`, a nonzero fixed endpoint contribution forces one of the two
scaled primitive coordinates into the retained outer window. -/
theorem lowerTransitionMarkedEndpointFunctional_ne_zero_subset_bands
    (N : ℕ) (A : ℝ) :
    Ioo (0 : ℝ) 1 ∩
        {alpha | lowerTransitionMarkedEndpointFunctional N A alpha ≠ 0} ⊆
      scaledPrimitiveResonanceBand N 1 A ∪
        scaledPrimitiveResonanceBand N 2 A := by
  intro alpha halpha
  rcases halpha with ⟨hunit, hne⟩
  by_cases hbandOne : alpha ∈ scaledPrimitiveResonanceBand N 1 A
  · exact Or.inl hbandOne
  by_cases hbandTwo : alpha ∈ scaledPrimitiveResonanceBand N 2 A
  · exact Or.inr hbandTwo
  exfalso
  apply hne
  unfold lowerTransitionMarkedEndpointFunctional
  apply Finset.sum_eq_zero
  intro p hp
  have hpCases : p = 1 ∨ p = 2 := by
    simp only [Finset.mem_Icc] at hp
    omega
  have hnotBand : alpha ∉ scaledPrimitiveResonanceBand N p A := by
    rcases hpCases with rfl | rfl
    · exact hbandOne
    · exact hbandTwo
  by_cases hprim : IsPrimitiveResonance p alpha
  · rw [if_pos hprim]
    have hnotScale : ¬ |scaledResonanceCoordinate N p alpha| ≤ A := by
      intro hscale
      exact hnotBand ⟨hunit, hprim, hscale⟩
    have hweight := lowerTransitionRadialWeight_eq_zero_of_A_lt_abs
      (lt_of_not_ge hnotScale)
    unfold lowerTransitionMarkedKernelReal
    rw [markedResonancePoint]
    change lowerTransitionRadialWeight A
        (scaledResonanceCoordinate N p alpha) *
          markedShotKernel (markedResonancePoint N p alpha) = 0
    rw [hweight, zero_mul]
  · rw [if_neg hprim]

/-- The fixed denominators `p=1,2` disappear in probability at fixed `A`.
The explicit `6A/log N` bound keeps the exceptional modulus-one cell
separate from the ordinary `p=2` resonance-cell estimate. -/
theorem uniform01Measure_real_lowerTransitionEndpoint_ne_zero_le
    {N : ℕ} (hN : 2 ≤ N) {A : ℝ} (hA : 0 ≤ A) :
    uniform01Measure.real
        {alpha | lowerTransitionMarkedEndpointFunctional N A alpha ≠ 0} ≤
      6 * A / Real.log (N : ℝ) := by
  let E : Set ℝ :=
    {alpha | lowerTransitionMarkedEndpointFunctional N A alpha ≠ 0}
  let B₁ : Set ℝ := scaledPrimitiveResonanceBand N 1 A
  let B₂ : Set ℝ := scaledPrimitiveResonanceBand N 2 A
  have hE : MeasurableSet E := by
    have heq := measurableSet_eq_fun
      (measurable_lowerTransitionMarkedEndpointFunctional N A)
      (measurable_const : Measurable (fun _ : ℝ ↦ (0 : ℝ)))
    simpa only [E, ne_eq] using! heq.compl
  have hsub : Ioo (0 : ℝ) 1 ∩ E ⊆ B₁ ∪ B₂ := by
    exact lowerTransitionMarkedEndpointFunctional_ne_zero_subset_bands N A
  have hBsub : B₁ ∪ B₂ ⊆ Icc (0 : ℝ) 1 := by
    intro alpha halpha
    rcases halpha with halpha | halpha
    · exact ⟨halpha.1.1.le, halpha.1.2.le⟩
    · exact ⟨halpha.1.1.le, halpha.1.2.le⟩
  have hBne : volume (B₁ ∪ B₂) ≠ ⊤ := by
    apply measure_ne_top_of_subset hBsub
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hOne : volume.real B₁ ≤ 4 * A / Real.log (N : ℝ) := by
    exact volumeReal_scaledPrimitiveResonanceBand_one_le hN hA
  have hTwoRaw : volume.real B₂ ≤
      (2 * A / Real.log (N : ℝ)) *
        ((Nat.totient 2 : ℝ) / (2 : ℝ) ^ 2) := by
    exact volumeReal_scaledPrimitiveResonanceBand_le hN (by omega) hA
  have hfactor : (Nat.totient 2 : ℝ) / (2 : ℝ) ^ 2 ≤ 1 := by
    apply (div_le_one (by norm_num : (0 : ℝ) < (2 : ℝ) ^ 2)).2
    have hφ : (Nat.totient 2 : ℝ) ≤ (2 : ℝ) := by
      exact_mod_cast totient_le_self 2
    nlinarith
  have hTwo : volume.real B₂ ≤ 2 * A / Real.log (N : ℝ) := by
    calc
      volume.real B₂ ≤
          (2 * A / Real.log (N : ℝ)) *
            ((Nat.totient 2 : ℝ) / (2 : ℝ) ^ 2) := hTwoRaw
      _ ≤ (2 * A / Real.log (N : ℝ)) * 1 := by
        gcongr
      _ = 2 * A / Real.log (N : ℝ) := mul_one _
  rw [uniform01Measure, measureReal_restrict_apply hE]
  calc
    volume.real (E ∩ Ioo (0 : ℝ) 1) =
        volume.real (Ioo (0 : ℝ) 1 ∩ E) := by rw [Set.inter_comm]
    _ ≤ volume.real (B₁ ∪ B₂) := measureReal_mono hsub hBne
    _ ≤ volume.real B₁ + volume.real B₂ :=
      measureReal_union_le B₁ B₂
    _ ≤ 4 * A / Real.log (N : ℝ) +
        2 * A / Real.log (N : ℝ) := add_le_add hOne hTwo
    _ = 6 * A / Real.log (N : ℝ) := by ring

theorem tendsto_uniform01Measure_real_lowerTransitionEndpoint_ne_zero
    (A : ℝ) (hA : 0 ≤ A) :
    Tendsto
      (fun N : ℕ ↦ uniform01Measure.real
        {alpha | lowerTransitionMarkedEndpointFunctional N A alpha ≠ 0})
      atTop (nhds 0) := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun N : ℕ ↦ 6 * A / Real.log (N : ℝ))
      atTop (nhds 0) := hlog.const_div_atTop (6 * A)
  apply squeeze_zero'
  · exact Eventually.of_forall fun _N ↦ measureReal_nonneg
  · filter_upwards [eventually_ge_atTop 2] with N hN
    exact uniform01Measure_real_lowerTransitionEndpoint_ne_zero_le hN hA
  · exact hupper

/-- The all-denominator auxiliary functional and the literal carrier-range
functional differ by a term tending to zero in probability. -/
theorem tendstoInMeasure_lowerTransitionMarkedFunctionalReal_sub_all
    (A : ℝ) (hA : 0 ≤ A) :
    TendstoInMeasure uniform01Measure
      (fun N alpha ↦ lowerTransitionMarkedFunctionalReal N A alpha -
        lowerTransitionMarkedFunctionalAll N A alpha)
      atTop 0 := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro r hr
  let D : ℕ → Set ℝ := fun N ↦
    {alpha | lowerTransitionMarkedEndpointFunctional N A alpha ≠ 0}
  have hD : Tendsto (fun N ↦ uniform01Measure.real (D N))
      atTop (nhds 0) := by
    simpa only [D] using!
      tendsto_uniform01Measure_real_lowerTransitionEndpoint_ne_zero A hA
  apply squeeze_zero'
  · exact Eventually.of_forall fun _N ↦ measureReal_nonneg
  · filter_upwards [eventually_ge_atTop 2] with N hN
    apply measureReal_mono
    · intro alpha hbad
      change lowerTransitionMarkedEndpointFunctional N A alpha ≠ 0
      intro hzero
      have hall : lowerTransitionMarkedFunctionalAll N A alpha =
          lowerTransitionMarkedFunctionalReal N A alpha := by
        rw [lowerTransitionMarkedFunctionalAll_eq_endpoint_add hN,
          hzero, zero_add]
      simp only [Set.mem_setOf_eq, Pi.zero_apply, sub_zero] at hbad
      rw [hall, sub_self, norm_zero] at hbad
      linarith
    · exact measure_ne_top _ _
  · exact hD

def lowerTransitionMarkedLawAll
    (N : ℕ) (A : ℝ) : ProbabilityMeasure ℝ :=
  uniform01.map
    (measurable_lowerTransitionMarkedFunctionalAll N A).aemeasurable

/-- A weak limit for the all-denominator auxiliary law is exactly the weak
limit for the literal carrier range `p>2`, because the two fixed endpoints
vanish in probability. -/
theorem tendsto_lowerTransitionMarkedLaw_of_all
    (A : ℝ) (hA : 0 ≤ A) (ν : ProbabilityMeasure ℝ)
    (hAll : Tendsto (fun N ↦ lowerTransitionMarkedLawAll N A)
      atTop
      (@nhds (ProbabilityMeasure ℝ)
        probabilityMeasureWeakTopologyLowerTransition ν)) :
    Tendsto (fun N ↦ lowerTransitionMarkedLaw N A)
      atTop
      (@nhds (ProbabilityMeasure ℝ)
        probabilityMeasureWeakTopologyLowerTransition ν) := by
  refine tendsto_map_of_tendsto_map_of_tendstoInMeasure_sub
    (μ := uniform01Measure)
    (fun N ↦ lowerTransitionMarkedFunctionalAll N A)
    (fun N ↦ lowerTransitionMarkedFunctionalReal N A) ν ?_ ?_ ?_ ?_
  · intro N
    exact (measurable_lowerTransitionMarkedFunctionalAll N A).aemeasurable
  · intro N
    exact (measurable_lowerTransitionMarkedFunctionalReal N A).aemeasurable
  · simpa [lowerTransitionMarkedLawAll, uniform01] using! hAll
  · simpa only [Pi.sub_apply] using!
      tendstoInMeasure_lowerTransitionMarkedFunctionalReal_sub_all A hA

/-- Custom-kernel sum over the compact transition annulus. -/
def lowerTransitionMarkedKernelSum
    (N P : ℕ) (A : ℝ) (alpha : ℝ) : ℝ :=
  ∑ p ∈ Finset.Icc 1 P,
    if IsPrimitiveResonance p alpha ∧
        markedResonancePoint N p alpha ∈ lowerTransitionMarkedRegion A then
      lowerTransitionMarkedKernelReal A (markedResonancePoint N p alpha)
    else 0

theorem lowerTransitionMarkedFunctionalAll_eq_kernelSum
    {N : ℕ} (hN : 2 ≤ N) {A : ℝ} (hA : 0 < A) (alpha : ℝ) :
    lowerTransitionMarkedFunctionalAll N A alpha =
      lowerTransitionMarkedKernelSum N N A alpha := by
  unfold lowerTransitionMarkedFunctionalAll lowerTransitionMarkedKernelSum
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hprim : IsPrimitiveResonance p alpha
  · rw [if_pos hprim]
    by_cases hregion :
        markedResonancePoint N p alpha ∈ lowerTransitionMarkedRegion A
    · rw [if_pos ⟨hprim, hregion⟩]
    · rw [if_neg (fun h ↦ hregion h.2)]
      have hradial : ¬ (A / 2 ≤
          |scaledResonanceCoordinate N p alpha| ∧
        |scaledResonanceCoordinate N p alpha| ≤ A) := by
        intro h
        apply hregion
        unfold lowerTransitionMarkedRegion
        exact (markedResonancePoint_mem_compactAnnularMarkedRegion_iff
          hN hp (by positivity : 0 ≤ A / 2) alpha).2 h
      rcases not_and_or.mp hradial with hinner | houter
      · have hz := lowerTransitionRadialWeight_eq_zero_of_abs_le_half
          hA (le_of_not_ge hinner)
        unfold lowerTransitionMarkedKernelReal
        rw [markedResonancePoint]
        change lowerTransitionRadialWeight A
            (scaledResonanceCoordinate N p alpha) *
              markedShotKernel (markedResonancePoint N p alpha) = 0
        rw [hz, zero_mul]
      · have hz := lowerTransitionRadialWeight_eq_zero_of_A_lt_abs
          (lt_of_not_ge houter)
        unfold lowerTransitionMarkedKernelReal
        rw [markedResonancePoint]
        change lowerTransitionRadialWeight A
            (scaledResonanceCoordinate N p alpha) *
              markedShotKernel (markedResonancePoint N p alpha) = 0
        rw [hz, zero_mul]
  · rw [if_neg hprim, if_neg (fun h ↦ hprim h.1)]

variable {LTIndex : Type*} [Fintype LTIndex]

/-- Deterministic finite-cell approximation for the custom lower-transition
kernel.  This is the exact analogue of the standard annular marked-shot
estimate, with no assumption specific to a rectangular grid. -/
theorem abs_lowerTransitionMarkedKernelSum_sub_finiteCellApproximation_le_count
    (N P : ℕ) (A : ℝ)
    (B : LTIndex → Set (ℝ × ℝ × ℝ)) (w : LTIndex → ℝ)
    {η : ℝ}
    (hsub : ∀ i, B i ⊆ lowerTransitionMarkedRegion A)
    (hpart : ∀ z ∈ lowerTransitionMarkedRegion A, ∃! i, z ∈ B i)
    (happrox : ∀ i z, z ∈ B i →
      |lowerTransitionMarkedKernelReal A z - w i| ≤ η)
    (alpha : ℝ) :
    |lowerTransitionMarkedKernelSum N P A alpha -
        finiteCellMarkedShotApproximation N P B w alpha| ≤
      η * (markedResonanceCount N P
        (lowerTransitionMarkedRegion A) alpha : ℝ) := by
  classical
  unfold lowerTransitionMarkedKernelSum finiteCellMarkedShotApproximation
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ p ∈ Finset.Icc 1 P,
        ((if IsPrimitiveResonance p alpha ∧
              markedResonancePoint N p alpha ∈ lowerTransitionMarkedRegion A then
            lowerTransitionMarkedKernelReal A
              (markedResonancePoint N p alpha) else 0) -
          if IsPrimitiveResonance p alpha then
            ∑ i, if markedResonancePoint N p alpha ∈ B i then w i else 0
          else 0)| ≤
        ∑ p ∈ Finset.Icc 1 P,
          |((if IsPrimitiveResonance p alpha ∧
                markedResonancePoint N p alpha ∈
                  lowerTransitionMarkedRegion A then
              lowerTransitionMarkedKernelReal A
                (markedResonancePoint N p alpha) else 0) -
            if IsPrimitiveResonance p alpha then
              ∑ i, if markedResonancePoint N p alpha ∈ B i then w i else 0
            else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Finset.Icc 1 P,
          if IsPrimitiveResonance p alpha ∧
              markedResonancePoint N p alpha ∈ lowerTransitionMarkedRegion A
          then η else 0 := by
      apply Finset.sum_le_sum
      intro p _hp
      let z := markedResonancePoint N p alpha
      by_cases hprim : IsPrimitiveResonance p alpha
      · by_cases hzK : z ∈ lowerTransitionMarkedRegion A
        · obtain ⟨i, hiB, hiUnique⟩ := hpart z hzK
          have hsum : (∑ j, if z ∈ B j then w j else 0) = w i := by
            rw [Fintype.sum_eq_single i]
            · simp [hiB]
            · intro j hji
              rw [if_neg]
              intro hjB
              exact hji (hiUnique j hjB)
          simp only [hprim, hzK, and_self, if_true, z]
          rw [hsum]
          exact happrox i z hiB
        · have hnone : ∀ i, z ∉ B i := by
            intro i hiB
            exact hzK (hsub i hiB)
          simp [hprim, hzK, hnone, z]
      · simp [hprim]
    _ = η * (markedResonanceCount N P
          (lowerTransitionMarkedRegion A) alpha : ℝ) := by
      unfold markedResonanceCount
      simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      by_cases h : IsPrimitiveResonance p alpha ∧
          markedResonancePoint N p alpha ∈ lowerTransitionMarkedRegion A
      · simp [h]
      · simp [h]

/-! ## Explicit grids and a convergence criterion -/

def lowerTransitionGridApproximation
    (m N : ℕ) (A : ℝ) (alpha : ℝ) : ℝ :=
  finiteCellMarkedShotApproximation N N
    (annularGridCell (A / 2) A (m + 1))
    (fun i ↦ lowerTransitionMarkedKernelReal A
      (annularGridCenter (A / 2) A (m + 1) i)) alpha

theorem measurable_lowerTransitionGridApproximation
    (m N : ℕ) (A : ℝ) :
    Measurable (lowerTransitionGridApproximation m N A) := by
  unfold lowerTransitionGridApproximation
  exact measurable_finiteCellMarkedShotApproximation N N
    (fun i ↦ measurableSet_annularGridCell (A / 2) A (m + 1) i) _

def lowerTransitionGridLaw
    (m N : ℕ) (A : ℝ) : ProbabilityMeasure ℝ :=
  uniform01.map
    (measurable_lowerTransitionGridApproximation m N A).aemeasurable

theorem lowerTransitionGridLaw_eq_finiteCellMarkedShotLaw
    (m N : ℕ) (A : ℝ) :
    lowerTransitionGridLaw m N A =
      finiteCellMarkedShotLaw N N
        (annularGridCell (A / 2) A (m + 1))
        (fun i ↦ measurableSet_annularGridCell (A / 2) A (m + 1) i)
        (fun i ↦ lowerTransitionMarkedKernelReal A
          (annularGridCenter (A / 2) A (m + 1) i)) := by
  rfl

/-- Every sufficiently fine explicit grid has pointwise error at most
`eta` times the retained annular count, uniformly in `N >= 2`. -/
theorem eventually_lowerTransitionGridApproximation_error_le_count
    {A η : ℝ} (hA : 0 < A) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∀ N : ℕ, 2 ≤ N → ∀ alpha : ℝ,
      |lowerTransitionMarkedFunctionalAll N A alpha -
          lowerTransitionGridApproximation m N A alpha| ≤
        η * (markedResonanceCount N N
          (lowerTransitionMarkedRegion A) alpha : ℝ) := by
  obtain ⟨δ, hδ, hkernel⟩ :=
    exists_uniform_cell_radius_lowerTransitionMarkedKernelReal hA hη
  have htime : ∀ᶠ m : ℕ in atTop,
      (1 : ℝ) / ((m + 1 : ℕ) : ℝ) < δ := by
    simpa only [Nat.cast_add, Nat.cast_one] using!
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually_lt_const hδ
  have hsigned : ∀ᶠ m : ℕ in atTop,
      (A - A / 2) / ((m + 1 : ℕ) : ℝ) < δ := by
    have ht : Tendsto
        (fun m : ℕ ↦ (A - A / 2) / ((m + 1 : ℕ) : ℝ))
        atTop (nhds 0) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using!
        (tendsto_const_div_atTop_nhds_zero_nat (A - A / 2)).comp
          (tendsto_add_atTop_nat 1)
    exact ht.eventually_lt_const hδ
  filter_upwards [htime, hsigned] with m htm hsm
  intro N hN alpha
  rw [lowerTransitionMarkedFunctionalAll_eq_kernelSum hN hA alpha]
  unfold lowerTransitionGridApproximation
  apply abs_lowerTransitionMarkedKernelSum_sub_finiteCellApproximation_le_count
    N N A (annularGridCell (A / 2) A (m + 1))
      (fun i ↦ lowerTransitionMarkedKernelReal A
        (annularGridCenter (A / 2) A (m + 1) i))
    (annularGridCell_subset_compactAnnularMarkedRegion
      (by linarith : A / 2 < A) (by omega))
    (fun z hz ↦ existsUnique_mem_annularGridCell
      (by positivity : 0 < A / 2) (by linarith : A / 2 < A)
      (by omega) hz)
  intro i z hz
  exact (hkernel z
    (annularGridCell_subset_compactAnnularMarkedRegion
      (by linarith : A / 2 < A) (by omega) i hz)
    (annularGridCenter (A / 2) A (m + 1) i)
    (annularGridCenter_mem_compactAnnularMarkedRegion
      (by linarith : A / 2 < A) (by omega) i)
    (dist_annularGridCenter_lt (by linarith : A / 2 < A)
      (by omega) htm hsm i hz)).le

/-- Tightness of the retained annular count turns the deterministic mesh
bound into the nested probability estimate used by converging together. -/
theorem twoParameter_close_lowerTransitionGridApproximation
    (Ns : ℕ → ℕ) {A : ℝ} (hA : 0 < A)
    (hNs : ∀ᶠ n : ℕ in atTop, 2 ≤ Ns n)
    (hCountTight : ∀ δ > 0, ∃ K : ℕ, ∀ᶠ n : ℕ in atTop,
      uniform01Measure.real
        {alpha | K < markedResonanceCount (Ns n) (Ns n)
          (lowerTransitionMarkedRegion A) alpha} < δ) :
    ∀ r > 0, ∀ δ > 0,
      ∀ᶠ m : ℕ in atTop, ∀ᶠ n : ℕ in atTop,
        uniform01Measure.real
          {alpha | r ≤ ‖lowerTransitionMarkedFunctionalAll (Ns n) A alpha -
            lowerTransitionGridApproximation m (Ns n) A alpha‖} < δ := by
  intro r hr δ hδ
  obtain ⟨K, hK⟩ := hCountTight δ hδ
  let η : ℝ := r / ((K : ℝ) + 1)
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hm := eventually_lowerTransitionGridApproximation_error_le_count hA hη
  filter_upwards [hm] with m hm
  filter_upwards [hNs, hK] with n hN hcount
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans_lt hcount
  intro alpha hbad
  by_contra hnotLarge
  have hCle : markedResonanceCount (Ns n) (Ns n)
      (lowerTransitionMarkedRegion A) alpha ≤ K := Nat.le_of_not_gt hnotLarge
  have herr := hm (Ns n) hN alpha
  have hηC : η * (markedResonanceCount (Ns n) (Ns n)
        (lowerTransitionMarkedRegion A) alpha : ℝ) ≤ η * (K : ℝ) := by
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hCle) hη.le
  have hηK : η * (K : ℝ) < r := by
    dsimp [η]
    have hden : (0 : ℝ) < (K : ℝ) + 1 := by positivity
    calc
      r / ((K : ℝ) + 1) * (K : ℝ) <
          r / ((K : ℝ) + 1) * ((K : ℝ) + 1) := by
        apply mul_lt_mul_of_pos_left (by linarith) (div_pos hr hden)
      _ = r := by field_simp
  have herrlt :
      |lowerTransitionMarkedFunctionalAll (Ns n) A alpha -
          lowerTransitionGridApproximation m (Ns n) A alpha| < r :=
    herr.trans_lt (hηC.trans_lt hηK)
  simp only [Real.norm_eq_abs] at hbad
  exact (not_lt_of_ge hbad) herrlt

/-- Fully explicit convergence criterion for the weighted lower transition.
The only inputs left are the actual mixed factorial limits for every fixed
grid and convergence of the corresponding independent-Poisson grid laws. -/
theorem tendsto_lowerTransitionMarkedLawAll_of_gridFactorialMoments
    (Ns : ℕ → ℕ) {A : ℝ} (hA : 0 < A)
    (hNs : ∀ᶠ n : ℕ in atTop, 2 ≤ Ns n)
    (r : ∀ m : ℕ, AnnularGridIndex (m + 1) → NNReal)
    (hFac : ∀ m (k : AnnularGridIndex (m + 1) → ℕ),
      Tendsto
        (fun n ↦ mixedFactorialMoment
          (markedResonanceCountVectorLaw (Ns n) (Ns n)
            (annularGridCell (A / 2) A (m + 1))
            (fun i ↦ measurableSet_annularGridCell
              (A / 2) A (m + 1) i)) k)
        atTop (nhds (∏ i, (r m i : ℝ) ^ (k i))))
    (ν : ProbabilityMeasure ℝ)
    (hGridLimit : Tendsto
      (fun m ↦ weightedIndependentPoissonLaw (r m)
        (fun i ↦ lowerTransitionMarkedKernelReal A
          (annularGridCenter (A / 2) A (m + 1) i)))
      atTop (nhds ν)) :
    Tendsto (fun n ↦ lowerTransitionMarkedLawAll (Ns n) A)
      atTop (nhds ν) := by
  let XA : ℕ → ℕ → ℝ → ℝ :=
    fun m n ↦ lowerTransitionGridApproximation m (Ns n) A
  let X : ℕ → ℝ → ℝ :=
    fun n ↦ lowerTransitionMarkedFunctionalAll (Ns n) A
  let νm : ℕ → ProbabilityMeasure ℝ := fun m ↦
    weightedIndependentPoissonLaw (r m)
      (fun i ↦ lowerTransitionMarkedKernelReal A
        (annularGridCenter (A / 2) A (m + 1) i))
  have hfixed : ∀ m,
      Tendsto
        (fun n ↦ (⟨uniform01Measure.map (XA m n),
          Measure.isProbabilityMeasure_map
            (measurable_lowerTransitionGridApproximation
              m (Ns n) A).aemeasurable⟩ : ProbabilityMeasure ℝ))
        atTop
          (@nhds (ProbabilityMeasure ℝ)
            probabilityMeasureWeakTopologyLowerTransition (νm m)) := by
    intro m
    simpa only [XA, νm, lowerTransitionGridLaw] using!
      (tendsto_finiteCellMarkedShotLaw_of_mixedFactorialMoments
        Ns Ns (annularGridCell (A / 2) A (m + 1))
        (fun i ↦ measurableSet_annularGridCell (A / 2) A (m + 1) i)
        (r m)
        (fun i ↦ lowerTransitionMarkedKernelReal A
          (annularGridCenter (A / 2) A (m + 1) i)) (hFac m))
  have hCountTight : ∀ δ > 0, ∃ K : ℕ, ∀ᶠ n : ℕ in atTop,
      uniform01Measure.real
        {alpha | K < markedResonanceCount (Ns n) (Ns n)
          (lowerTransitionMarkedRegion A) alpha} < δ := by
    unfold lowerTransitionMarkedRegion
    apply annularMarkedCount_tight_of_gridFactorialMoments
      Ns (by positivity : 0 < A / 2) (by linarith : A / 2 < A) (r 0)
    simpa using! hFac 0
  have hclose : ∀ rr > 0, ∀ δ > 0,
      ∀ᶠ m : ℕ in atTop, ∀ᶠ n : ℕ in atTop,
        uniform01Measure.real
          {alpha | rr ≤ ‖X n alpha - XA m n alpha‖} < δ := by
    simpa only [X, XA] using!
      twoParameter_close_lowerTransitionGridApproximation
        Ns hA hNs hCountTight
  have hmain := tendsto_map_of_convergingTogether
    (μ := uniform01Measure) X XA νm ν
    (fun n ↦ (measurable_lowerTransitionMarkedFunctionalAll
      (Ns n) A).aemeasurable)
    (fun m n ↦ (measurable_lowerTransitionGridApproximation
      m (Ns n) A).aemeasurable)
    hfixed (by simpa only [νm] using! hGridLimit) hclose
  simpa only [lowerTransitionMarkedLawAll, X] using! hmain

/-- Source-faithful form of the lower-transition limit criterion.  Once the
mixed factorial moments of the *actual* explicit cells converge to their
geometric intensities, no abstract mesh law remains: the finite normalized
lower transition converges to the explicit continuum compound-Poisson law. -/
theorem tendsto_lowerTransitionMarkedLawAll_of_actualGridFactorialMoments
    (Ns : ℕ → ℕ) {A : ℝ} (hA : 0 < A)
    (hNs : ∀ᶠ n : ℕ in atTop, 2 ≤ Ns n)
    (hFac : ∀ m (k : AnnularGridIndex (m + 1) → ℕ),
      Tendsto
        (fun n ↦ mixedFactorialMoment
          (markedResonanceCountVectorLaw (Ns n) (Ns n)
            (annularGridCell (A / 2) A (m + 1))
            (fun i ↦ measurableSet_annularGridCell
              (A / 2) A (m + 1) i)) k)
        atTop
        (nhds (∏ i,
          (annularGridCellPoissonRate (A / 2) A (m + 1) i : ℝ) ^
            (k i)))) :
    Tendsto (fun n ↦ lowerTransitionMarkedLawAll (Ns n) A)
      atTop (nhds (lowerTransitionCompoundPoissonProbability A)) := by
  exact tendsto_lowerTransitionMarkedLawAll_of_gridFactorialMoments
    Ns hA hNs
    (fun m i ↦ annularGridCellPoissonRate (A / 2) A (m + 1) i)
    hFac (lowerTransitionCompoundPoissonProbability A)
    (tendsto_weightedIndependentPoissonLaw_lowerTransitionGrid hA)

/-- Final fixed-`A` lower-transition convergence criterion in the literal
denominator convention `2<p≤N`.  The hypotheses mention only the actual
mixed factorial moments of the explicit geometric grid cells. -/
theorem tendsto_lowerTransitionMarkedLaw_of_actualGridFactorialMoments
    {A : ℝ} (hA : 0 < A)
    (hFac : ∀ m (k : AnnularGridIndex (m + 1) → ℕ),
      Tendsto
        (fun N ↦ mixedFactorialMoment
          (markedResonanceCountVectorLaw N N
            (annularGridCell (A / 2) A (m + 1))
            (fun i ↦ measurableSet_annularGridCell
              (A / 2) A (m + 1) i)) k)
        atTop
        (nhds (∏ i,
          (annularGridCellPoissonRate (A / 2) A (m + 1) i : ℝ) ^
            (k i)))) :
    Tendsto (fun N ↦ lowerTransitionMarkedLaw N A)
      atTop (nhds (lowerTransitionCompoundPoissonProbability A)) := by
  apply tendsto_lowerTransitionMarkedLaw_of_all A hA.le
  apply tendsto_lowerTransitionMarkedLawAll_of_actualGridFactorialMoments
    (fun N ↦ N) hA (eventually_ge_atTop 2)
  simpa using! hFac

/-- Portmanteau plus the explicit compound-Poisson variance bound gives the
finite-`N` upper tail needed for the iterated deletion `N→∞`, then
`A→∞`. -/
theorem limsup_lowerTransitionMarkedLaw_tail_le_of_actualGridFactorialMoments
    {A R : ℝ} (hA : 0 < A) (hR : 0 < R)
    (hFac : ∀ m (k : AnnularGridIndex (m + 1) → ℕ),
      Tendsto
        (fun N ↦ mixedFactorialMoment
          (markedResonanceCountVectorLaw N N
            (annularGridCell (A / 2) A (m + 1))
            (fun i ↦ measurableSet_annularGridCell
              (A / 2) A (m + 1) i)) k)
        atTop
        (nhds (∏ i,
          (annularGridCellPoissonRate (A / 2) A (m + 1) i : ℝ) ^
            (k i)))) :
    atTop.limsup (fun N ↦
        (lowerTransitionMarkedLaw N A : Measure ℝ) {x : ℝ | R ≤ |x|}) ≤
      ENNReal.ofReal
        (((1 / (Real.pi ^ 2 / 6)) * (1 / (16 * A))) / R ^ 2) := by
  let F : Set ℝ := {x : ℝ | R ≤ |x|}
  let C : ℝ := ((1 / (Real.pi ^ 2 / 6)) * (1 / (16 * A))) / R ^ 2
  have hconv :=
    tendsto_lowerTransitionMarkedLaw_of_actualGridFactorialMoments hA hFac
  have hclosed : IsClosed F := by
    exact isClosed_Ici.preimage continuous_abs
  have hport : atTop.limsup (fun N ↦
      (lowerTransitionMarkedLaw N A : Measure ℝ) F) ≤
      (lowerTransitionCompoundPoissonProbability A : Measure ℝ) F :=
    ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hconv hclosed
  have htailReal :
      (lowerTransitionCompoundPoissonProbability A : Measure ℝ).real F ≤ C := by
    simpa only [F, C] using! lowerTransitionCompoundPoisson_tail_le hA hR
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have htailENN :
      (lowerTransitionCompoundPoissonProbability A : Measure ℝ) F ≤
        ENNReal.ofReal C := by
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _)
      ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hC0]
    simpa only [measureReal_def] using! htailReal
  exact hport.trans (by simpa only [C, F] using! htailENN)

/-- Exact one-denominator identification of the normalized lower residual
with the marked radial kernel. -/
theorem nearMinorLowerTransitionTerm_div_log_eq_marked
    (N p : ℕ) (A ε alpha : ℝ)
    (hA : 0 < A) (hL : 0 < Real.log (N : ℝ)) (hε : 0 < ε)
    (hAε : A / Real.log (N : ℝ) ≤ ε / 4) :
    nearMinorLowerTransitionTerm N A ε p alpha /
        (Real.log (N : ℝ) : ℂ) =
      if IsPrimitiveResonance p alpha then
        lowerTransitionMarkedKernel A (markedResonancePoint N p alpha)
      else 0 := by
  let L : ℝ := Real.log (N : ℝ)
  let v : ℝ := (p : ℝ) * resonanceDelta p alpha
  have hscaled : scaledResonanceCoordinate N p alpha = L * v := by
    unfold scaledResonanceCoordinate
    dsimp [L, v]
    ring
  have hradial := lowerTransitionRadialWeight_scaled_eq
    A ε L v hA (by simpa only [L] using! hL) hε
      (by simpa only [L] using! hAε)
  by_cases hprim : IsPrimitiveResonance p alpha
  · rw [if_pos hprim]
    have hshotR := primitiveShot_div_log_eq_markedShotKernel N p alpha
    rw [if_pos hprim] at hshotR
    have hshotC :
        (primitiveShot N p alpha : ℂ) / (L : ℂ) =
          (markedShotKernel (markedResonancePoint N p alpha) : ℂ) := by
      exact_mod_cast hshotR
    have hsmooth := smoothNearLiteralShotTerm_eq_rho_mul_primitiveShot
      N p (A / (2 * L)) ε alpha
    by_cases hquarter : |v| ≤ ε / 4
    · by_cases hminor : A < L * |v|
      · have hwindow : A < Real.log (N : ℝ) *
              |(p : ℝ) * resonanceDelta p alpha| ∧
            |(p : ℝ) * resonanceDelta p alpha| ≤ ε / 4 := by
          simpa only [L, v] using! And.intro hminor hquarter
        rw [nearMinorLowerTransitionTerm_eq_zero_of_window
          N p A ε alpha hA hL hε hwindow, zero_div]
        unfold lowerTransitionMarkedKernel
        have hweight : A <
            |(markedResonancePoint N p alpha).2.1| := by
          rw [markedResonancePoint]
          change A < |scaledResonanceCoordinate N p alpha|
          rw [hscaled, abs_mul, abs_of_pos (by simpa only [L] using! hL)]
          exact hminor
        rw [lowerTransitionRadialWeight_eq_zero_of_A_lt_abs hweight,
          Complex.ofReal_zero, zero_mul]
      · unfold nearMinorLowerTransitionTerm
        rw [if_pos (by simpa only [v] using! hquarter)]
        unfold nearMinorLargeDenominatorTerm
        rw [if_neg (fun h ↦ hminor (by simpa only [L, v] using! h.1))]
        rw [hsmooth]
        unfold lowerTransitionMarkedKernel
        rw [markedResonancePoint]
        change
          (nearRho (A / (2 * L)) ε v *
              (primitiveShot N p alpha : ℂ) - 0) / (L : ℂ) =
            (lowerTransitionRadialWeight A
                (scaledResonanceCoordinate N p alpha) : ℂ) *
              (markedShotKernel (markedResonancePoint N p alpha) : ℂ)
        rw [hscaled, hradial, if_pos hquarter, if_neg hminor, sub_zero,
          ← hshotC]
        ring
    · unfold nearMinorLowerTransitionTerm
      rw [if_neg (by simpa only [v] using! hquarter), zero_div]
      unfold lowerTransitionMarkedKernel
      rw [markedResonancePoint]
      change (0 : ℂ) =
        (lowerTransitionRadialWeight A
            (scaledResonanceCoordinate N p alpha) : ℂ) *
          (markedShotKernel (markedResonancePoint N p alpha) : ℂ)
      rw [hscaled, hradial, if_neg hquarter, zero_mul]
  · rw [if_neg hprim]
    simp [nearMinorLowerTransitionTerm, smoothNearLiteralShotTerm,
      nearPrimitivePole, nearMinorLargeDenominatorTerm,
      primitiveShot_of_not_primitive N p alpha hprim, hprim]

/-- Finite-sum form of the preceding exact marked-process bridge. -/
theorem nearMinorLowerTransitionSum_div_log_eq_markedFunctional
    (N : ℕ) (A ε alpha : ℝ)
    (hA : 0 < A) (hL : 0 < Real.log (N : ℝ)) (hε : 0 < ε)
    (hAε : A / Real.log (N : ℝ) ≤ ε / 4) :
    nearMinorLowerTransitionSum N A ε alpha /
        (Real.log (N : ℝ) : ℂ) =
      lowerTransitionMarkedFunctional N A alpha := by
  unfold nearMinorLowerTransitionSum lowerTransitionMarkedFunctional
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p _hp
  exact nearMinorLowerTransitionTerm_div_log_eq_marked
    N p A ε alpha hA hL hε hAε

/-- Real-valued form of the exact bridge.  This is the form used by the
probability-law and tail statements above. -/
theorem nearMinorLowerTransitionSum_div_log_eq_realMarkedFunctional
    (N : ℕ) (A ε alpha : ℝ)
    (hA : 0 < A) (hL : 0 < Real.log (N : ℝ)) (hε : 0 < ε)
    (hAε : A / Real.log (N : ℝ) ≤ ε / 4) :
    nearMinorLowerTransitionSum N A ε alpha /
        (Real.log (N : ℝ) : ℂ) =
      (lowerTransitionMarkedFunctionalReal N A alpha : ℂ) := by
  rw [nearMinorLowerTransitionSum_div_log_eq_markedFunctional
    N A ε alpha hA hL hε hAε,
    lowerTransitionMarkedFunctional_eq_real]

theorem norm_nearMinorLowerTransitionSum_div_log_eq_abs_markedFunctional
    (N : ℕ) (A ε alpha : ℝ)
    (hA : 0 < A) (hL : 0 < Real.log (N : ℝ)) (hε : 0 < ε)
    (hAε : A / Real.log (N : ℝ) ≤ ε / 4) :
    ‖nearMinorLowerTransitionSum N A ε alpha /
        (Real.log (N : ℝ) : ℂ)‖ =
      |lowerTransitionMarkedFunctionalReal N A alpha| := by
  rw [nearMinorLowerTransitionSum_div_log_eq_realMarkedFunctional
    N A ε alpha hA hL hε hAε,
    Complex.norm_real, Real.norm_eq_abs]

/-- For fixed positive `A` and near-window width `ε`, the scale assumptions
of the exact bridge hold automatically for every sufficiently large `N`. -/
theorem eventually_lowerTransition_scale_admissible
    (A ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      0 < Real.log (N : ℝ) ∧
        A / Real.log (N : ℝ) ≤ ε / 4 := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun N : ℕ ↦ A / Real.log (N : ℝ))
      atTop (nhds 0) := hlog.const_div_atTop A
  have hsmall : ∀ᶠ N : ℕ in atTop,
      A / Real.log (N : ℝ) < ε / 4 :=
    hratio.eventually_lt_const (by positivity)
  filter_upwards [eventually_ge_atTop 2, hsmall] with N hN hsmallN
  exact ⟨Real.log_pos (by exact_mod_cast hN), hsmallN.le⟩

end

end Erdos1002
