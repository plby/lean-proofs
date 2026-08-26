import ErdosProblems.Erdos1002.ContinuousCompoundPoisson
import ErdosProblems.Erdos1002.FixedCutoffSmallCoordinateAssembly
import ErdosProblems.Erdos1002.LevyContinuity
import ErdosProblems.Erdos1002.MarkedShotFunctional
import ErdosProblems.Erdos1002.PoissonCauchyExponent
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The continuum compound-Poisson laws of the marked shot

This file constructs the probability laws that occur after passing from the
finite marked-resonance process to its continuum Poisson limit.  The one-jump
law is not postulated: it is the normalized product of Lebesgue measure on the
two signed resonance-coordinate intervals and uniform measure on the torus
mark, pushed forward by the marked-shot kernel.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace Erdos1002

noncomputable section

open ProbabilityTheory

/-- The two open signed intervals retained by an annular cutoff. -/
def signedAnnulusSet (ε A : ℝ) : Set ℝ :=
  Ioo (-A) (-ε) ∪ Ioo ε A

theorem measurableSet_signedAnnulusSet (ε A : ℝ) :
    MeasurableSet (signedAnnulusSet ε A) := by
  exact measurableSet_Ioo.union measurableSet_Ioo

/-- Lebesgue measure on the two signed intervals, packaged as a finite
measure.  This definition is meaningful for all real parameters; the
nondegenerate mass formula is proved below under `0 ≤ ε < A`. -/
def signedAnnulusFiniteMeasure (ε A : ℝ) : FiniteMeasure ℝ :=
  ⟨volume.restrict (signedAnnulusSet ε A), by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    refine (measure_union_le (μ := volume)
      (Ioo (-A) (-ε)) (Ioo ε A)).trans_lt ?_
    rw [Real.volume_Ioo, Real.volume_Ioo]
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩⟩

@[simp]
theorem signedAnnulusFiniteMeasure_toMeasure (ε A : ℝ) :
    (signedAnnulusFiniteMeasure ε A : Measure ℝ) =
      volume.restrict (signedAnnulusSet ε A) :=
  rfl

theorem disjoint_signedAnnulus_halves {ε A : ℝ} (hε : 0 ≤ ε) :
    Disjoint (Ioo (-A) (-ε)) (Ioo ε A) := by
  rw [Set.disjoint_left]
  intro x hxneg hxpos
  linarith [hxneg.2, hxpos.1]

theorem signedAnnulusFiniteMeasure_mass
    {ε A : ℝ} (hε : 0 ≤ ε) (hεA : ε < A) :
    (signedAnnulusFiniteMeasure ε A).mass =
      Real.toNNReal (2 * (A - ε)) := by
  apply ENNReal.coe_injective
  rw [FiniteMeasure.ennreal_mass]
  change (volume.restrict (signedAnnulusSet ε A)) univ = _
  rw [Measure.restrict_apply_univ, signedAnnulusSet,
    measure_union (disjoint_signedAnnulus_halves hε) measurableSet_Ioo,
    Real.volume_Ioo, Real.volume_Ioo]
  rw [← ENNReal.ofReal_add (by linarith : 0 ≤ -ε - -A)
    (by linarith : 0 ≤ A - ε)]
  rw [show -ε - -A + (A - ε) = 2 * (A - ε) by ring]
  rfl

theorem signedAnnulusFiniteMeasure_ne_zero
    {ε A : ℝ} (hε : 0 ≤ ε) (hεA : ε < A) :
    signedAnnulusFiniteMeasure ε A ≠ 0 := by
  rw [← FiniteMeasure.mass_nonzero_iff,
    signedAnnulusFiniteMeasure_mass hε hεA]
  exact ne_of_gt (by
    rw [Real.toNNReal_pos]
    linarith)

/-- The normalized joint law of the signed resonance coordinate and the
uniform torus mark. -/
def signedAnnularMarkProbability (ε A : ℝ) : ProbabilityMeasure (ℝ × ℝ) :=
  (signedAnnulusFiniteMeasure ε A).normalize.prod uniform01

/-- The marked-shot kernel after suppressing the irrelevant logarithmic-time
coordinate. -/
def signedAnnularJumpKernel (xu : ℝ × ℝ) : ℝ :=
  markedShotKernel (0, xu.1, xu.2)

theorem measurable_signedAnnularJumpKernel :
    Measurable signedAnnularJumpKernel := by
  exact measurable_markedShotKernel.comp
    (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))

/-- The one-jump distribution obtained by applying `V(u) / x`. -/
def signedAnnularJumpProbability (ε A : ℝ) : ProbabilityMeasure ℝ :=
  (signedAnnularMarkProbability ε A).map
    measurable_signedAnnularJumpKernel.aemeasurable

/-- The total Poisson intensity of the signed annulus. -/
def annularPoissonRate (ε A : ℝ) : NNReal :=
  Real.toNNReal (2 * (A - ε) / (Real.pi ^ 2 / 6))

/-- The continuum compound-Poisson law for the annular marked shot. -/
def annularCompoundPoissonProbability (ε A : ℝ) : ProbabilityMeasure ℝ :=
  continuousCompoundPoissonProbability (annularPoissonRate ε A)
    (signedAnnularJumpProbability ε A)

/-- The fixed outer-cutoff law, with the null coordinate removed only as a
Lebesgue-null set. -/
def cutoffCompoundPoissonProbability (A : ℝ) : ProbabilityMeasure ℝ :=
  annularCompoundPoissonProbability 0 A

/-! ## Exact characteristic function of the finite annular law -/

/-- The complex integrand in the Lévy exponent of one marked point. -/
def signedAnnularExponentIntegrand (t : ℝ) (xu : ℝ × ℝ) : ℂ :=
  Complex.exp ((t : ℂ) * signedAnnularJumpKernel xu * Complex.I) - 1

theorem measurable_signedAnnularExponentIntegrand (t : ℝ) :
    Measurable (signedAnnularExponentIntegrand t) := by
  unfold signedAnnularExponentIntegrand
  exact (((measurable_const.mul
    measurable_signedAnnularJumpKernel.complex_ofReal).mul
      measurable_const).cexp).sub measurable_const

private theorem integrable_signedAnnularProbChar_raw
    (ε A t : ℝ) :
    Integrable
      (fun xu : ℝ × ℝ ↦
        Complex.exp ((t : ℂ) * signedAnnularJumpKernel xu * Complex.I))
      ((signedAnnulusFiniteMeasure ε A : Measure ℝ).prod uniform01Measure) := by
  refine (integrable_const (1 : ℝ)).mono
    (((measurable_const.mul
      measurable_signedAnnularJumpKernel.complex_ofReal).mul
        measurable_const).cexp.aestronglyMeasurable) ?_
  filter_upwards with xu
  rw [Complex.norm_exp]
  simp

theorem integrable_signedAnnularExponentIntegrand_raw
    (ε A t : ℝ) :
    Integrable (signedAnnularExponentIntegrand t)
      ((signedAnnulusFiniteMeasure ε A : Measure ℝ).prod uniform01Measure) := by
  exact (integrable_signedAnnularProbChar_raw ε A t).sub
    (integrable_const (1 : ℂ))

theorem signedAnnularMarkProbability_toMeasure
    {ε A : ℝ} (hε : 0 ≤ ε) (hεA : ε < A) :
    (signedAnnularMarkProbability ε A : Measure (ℝ × ℝ)) =
      ((signedAnnulusFiniteMeasure ε A).mass⁻¹ : NNReal) •
        ((signedAnnulusFiniteMeasure ε A : Measure ℝ).prod uniform01Measure) := by
  rw [signedAnnularMarkProbability, ProbabilityMeasure.toMeasure_prod,
    FiniteMeasure.toMeasure_normalize_eq_of_nonzero _
      (signedAnnulusFiniteMeasure_ne_zero hε hεA),
    ]
  change (((((signedAnnulusFiniteMeasure ε A).mass⁻¹ : NNReal) : ENNReal) •
      (signedAnnulusFiniteMeasure ε A : Measure ℝ)).prod uniform01Measure) =
    ((((signedAnnulusFiniteMeasure ε A).mass⁻¹ : NNReal) : ENNReal) •
      ((signedAnnulusFiniteMeasure ε A : Measure ℝ).prod uniform01Measure))
  exact Measure.prod_smul_left _

theorem coe_annularPoissonRate
    {ε A : ℝ} (hεA : ε < A) :
    (annularPoissonRate ε A : ℝ) =
      2 * (A - ε) / (Real.pi ^ 2 / 6) := by
  rw [annularPoissonRate, Real.coe_toNNReal]
  exact div_nonneg (by linarith) (by positivity)

theorem charFun_signedAnnularJumpProbability_sub_one
    {ε A : ℝ} (hε : 0 ≤ ε) (hεA : ε < A) (t : ℝ) :
    charFun (signedAnnularJumpProbability ε A : Measure ℝ) t - 1 =
      (((signedAnnulusFiniteMeasure ε A).mass⁻¹ : NNReal) : ℝ) •
        (∫ xu : ℝ × ℝ, signedAnnularExponentIntegrand t xu
          ∂((signedAnnulusFiniteMeasure ε A : Measure ℝ).prod
            uniform01Measure)) := by
  rw [charFun_apply_real, signedAnnularJumpProbability,
    ProbabilityMeasure.toMeasure_map]
  rw [integral_map measurable_signedAnnularJumpKernel.aemeasurable (by fun_prop)]
  have hExp : Integrable
      (fun xu : ℝ × ℝ ↦
        Complex.exp ((t : ℂ) * signedAnnularJumpKernel xu * Complex.I))
      (signedAnnularMarkProbability ε A : Measure (ℝ × ℝ)) := by
    refine (integrable_const (1 : ℝ)).mono
      (((measurable_const.mul
        measurable_signedAnnularJumpKernel.complex_ofReal).mul
          measurable_const).cexp.aestronglyMeasurable) ?_
    filter_upwards with xu
    rw [Complex.norm_exp]
    simp
  have hOne : Integrable (fun _ : ℝ × ℝ ↦ (1 : ℂ))
      (signedAnnularMarkProbability ε A : Measure (ℝ × ℝ)) :=
    integrable_const (1 : ℂ)
  calc
    (∫ xu : ℝ × ℝ,
        Complex.exp ((t : ℂ) * signedAnnularJumpKernel xu * Complex.I)
        ∂(signedAnnularMarkProbability ε A : Measure (ℝ × ℝ))) - 1 =
        (∫ xu : ℝ × ℝ,
          Complex.exp ((t : ℂ) * signedAnnularJumpKernel xu * Complex.I)
          ∂(signedAnnularMarkProbability ε A : Measure (ℝ × ℝ))) -
          ∫ _xu : ℝ × ℝ, (1 : ℂ)
            ∂(signedAnnularMarkProbability ε A : Measure (ℝ × ℝ)) := by simp
    _ = ∫ xu : ℝ × ℝ, signedAnnularExponentIntegrand t xu
          ∂(signedAnnularMarkProbability ε A : Measure (ℝ × ℝ)) := by
      unfold signedAnnularExponentIntegrand
      exact (integral_sub hExp hOne).symm
    _ = _ := by
      rw [signedAnnularMarkProbability_toMeasure hε hεA,
        integral_smul_nnreal_measure]
      simp only [NNReal.smul_def]

/-- The unnormalised finite-annulus exponent.  The intensity density is
exactly `1 / (π²/6)` with respect to `dx du`; logarithmic time has total
mass one and has already been integrated out. -/
def signedAnnularPoissonExponent (ε A t : ℝ) : ℂ :=
  (1 / (Real.pi ^ 2 / 6) : ℝ) •
    (∫ xu : ℝ × ℝ, signedAnnularExponentIntegrand t xu
      ∂((signedAnnulusFiniteMeasure ε A : Measure ℝ).prod uniform01Measure))

/-- Exact characteristic function of the continuum annular compound-Poisson
law. -/
theorem charFun_annularCompoundPoissonProbability
    {ε A : ℝ} (hε : 0 ≤ ε) (hεA : ε < A) (t : ℝ) :
    charFun (annularCompoundPoissonProbability ε A : Measure ℝ) t =
      Complex.exp (signedAnnularPoissonExponent ε A t) := by
  rw [annularCompoundPoissonProbability,
    charFun_continuousCompoundPoissonProbability,
    charFun_signedAnnularJumpProbability_sub_one hε hεA]
  congr 1
  unfold signedAnnularPoissonExponent
  rw [coe_annularPoissonRate hεA,
    signedAnnulusFiniteMeasure_mass hε hεA]
  simp only [Complex.real_smul]
  simp only [NNReal.coe_inv]
  have hm : 0 ≤ 2 * (A - ε) :=
    mul_nonneg (by norm_num) (sub_nonneg.mpr hεA.le)
  rw [Real.coe_toNNReal (2 * (A - ε)) hm]
  push_cast
  have hdiffR : A - ε ≠ 0 := ne_of_gt (sub_pos.mpr hεA)
  have hdiffC : ((A - ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hdiffR
  have hsubC : (↑A - ↑ε : ℂ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hεA.ne')
  field_simp [hdiffR, hdiffC, hsubC, Real.pi_ne_zero]

/-! ## Removing the inner annular cutoff -/

theorem antitone_smallCoordinateCutoff :
    Antitone smallCoordinateCutoff := by
  intro m n hmn
  unfold smallCoordinateCutoff
  have hmpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hden : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right hmn 1
  exact one_div_le_one_div_of_le hmpos hden

theorem monotone_signedAnnulusSet_smallCoordinateCutoff (A : ℝ) :
    Monotone (fun m : ℕ ↦ signedAnnulusSet (smallCoordinateCutoff m) A) := by
  intro m n hmn x hx
  have hcut := antitone_smallCoordinateCutoff hmn
  rcases hx with hx | hx
  · exact Or.inl ⟨hx.1, by linarith [hx.2, hcut]⟩
  · exact Or.inr ⟨by linarith [hx.1, hcut], hx.2⟩

theorem iUnion_signedAnnulusSet_smallCoordinateCutoff
    {A : ℝ} (_hA : 0 < A) :
    (⋃ m : ℕ, signedAnnulusSet (smallCoordinateCutoff m) A) =
      signedAnnulusSet 0 A := by
  apply Set.Subset.antisymm
  · rw [iUnion_subset_iff]
    intro m x hx
    have hcut := smallCoordinateCutoff_nonneg m
    rcases hx with hx | hx
    · exact Or.inl ⟨hx.1, by linarith [hx.2, hcut]⟩
    · exact Or.inr ⟨by linarith [hx.1, hcut], hx.2⟩
  · intro x hx
    rcases hx with hx | hx
    · have hxpos : 0 < -x := by linarith [hx.2]
      have he : ∀ᶠ m : ℕ in atTop, smallCoordinateCutoff m < -x :=
        tendsto_smallCoordinateCutoff.eventually_lt_const hxpos
      rcases (eventually_atTop.1 he) with ⟨m, hm⟩
      rw [mem_iUnion]
      exact ⟨m, Or.inl ⟨hx.1, by linarith [hm m le_rfl]⟩⟩
    · have hxpos : 0 < x := by linarith [hx.1]
      have he : ∀ᶠ m : ℕ in atTop, smallCoordinateCutoff m < x :=
        tendsto_smallCoordinateCutoff.eventually_lt_const hxpos
      rcases (eventually_atTop.1 he) with ⟨m, hm⟩
      rw [mem_iUnion]
      exact ⟨m, Or.inr ⟨hm m le_rfl, hx.2⟩⟩

/-- The raw annular exponent integrals converge when the deleted coordinate
strip shrinks to zero. -/
theorem tendsto_integral_signedAnnularExponentIntegrand_smallCoordinateCutoff
    {A : ℝ} (hA : 0 < A) (t : ℝ) :
    Tendsto
      (fun m : ℕ ↦
        ∫ xu : ℝ × ℝ, signedAnnularExponentIntegrand t xu
          ∂((signedAnnulusFiniteMeasure (smallCoordinateCutoff m) A : Measure ℝ).prod
            uniform01Measure))
      atTop
      (nhds (∫ xu : ℝ × ℝ, signedAnnularExponentIntegrand t xu
        ∂((signedAnnulusFiniteMeasure 0 A : Measure ℝ).prod uniform01Measure))) := by
  let s : ℕ → Set (ℝ × ℝ) := fun m ↦
    signedAnnulusSet (smallCoordinateCutoff m) A ×ˢ (univ : Set ℝ)
  have hsmeas : ∀ m, MeasurableSet (s m) := fun m ↦
    (measurableSet_signedAnnulusSet _ _).prod MeasurableSet.univ
  have hsmono : Monotone s := by
    intro m n hmn
    exact Set.prod_mono (monotone_signedAnnulusSet_smallCoordinateCutoff A hmn)
      (Subset.rfl)
  have hsUnion : (⋃ m, s m) = signedAnnulusSet 0 A ×ˢ (univ : Set ℝ) := by
    ext xu
    simp only [s, mem_iUnion, mem_prod, mem_univ, and_true]
    rw [← mem_iUnion]
    exact Set.ext_iff.mp (iUnion_signedAnnulusSet_smallCoordinateCutoff hA) xu.1
  have hInt : IntegrableOn (signedAnnularExponentIntegrand t)
      (⋃ m, s m) (volume.prod uniform01Measure) := by
    rw [hsUnion]
    have hraw := integrable_signedAnnularExponentIntegrand_raw 0 A t
    rw [signedAnnulusFiniteMeasure_toMeasure,
      show uniform01Measure = uniform01Measure.restrict univ by simp,
      Measure.prod_restrict] at hraw
    exact hraw
  have hlim := tendsto_setIntegral_of_monotone hsmeas hsmono hInt
  rw [hsUnion] at hlim
  have hprod (ε : ℝ) :
      (signedAnnulusFiniteMeasure ε A : Measure ℝ).prod uniform01Measure =
        (volume.prod uniform01Measure).restrict
          (signedAnnulusSet ε A ×ˢ (univ : Set ℝ)) := by
    rw [signedAnnulusFiniteMeasure_toMeasure]
    calc
      (volume.restrict (signedAnnulusSet ε A)).prod uniform01Measure =
          (volume.restrict (signedAnnulusSet ε A)).prod
            (uniform01Measure.restrict univ) := by rw [Measure.restrict_univ]
      _ = (volume.prod uniform01Measure).restrict
          (signedAnnulusSet ε A ×ˢ (univ : Set ℝ)) :=
        Measure.prod_restrict _ _
  have hsource :
      (fun m : ℕ ↦
        ∫ xu : ℝ × ℝ, signedAnnularExponentIntegrand t xu
          ∂((signedAnnulusFiniteMeasure (smallCoordinateCutoff m) A : Measure ℝ).prod
            uniform01Measure)) =
      (fun m : ℕ ↦ ∫ xu : ℝ × ℝ in s m,
        signedAnnularExponentIntegrand t xu ∂(volume.prod uniform01Measure)) := by
    funext m
    rw [hprod]
  have htarget :
      (∫ xu : ℝ × ℝ, signedAnnularExponentIntegrand t xu
        ∂((signedAnnulusFiniteMeasure 0 A : Measure ℝ).prod uniform01Measure)) =
      ∫ xu : ℝ × ℝ in signedAnnulusSet 0 A ×ˢ (univ : Set ℝ),
        signedAnnularExponentIntegrand t xu ∂(volume.prod uniform01Measure) := by
    rw [hprod]
  rw [hsource, htarget]
  exact hlim

theorem tendsto_signedAnnularPoissonExponent_smallCoordinateCutoff
    {A : ℝ} (hA : 0 < A) (t : ℝ) :
    Tendsto
      (fun m : ℕ ↦ signedAnnularPoissonExponent
        (smallCoordinateCutoff m) A t)
      atTop (nhds (signedAnnularPoissonExponent 0 A t)) := by
  unfold signedAnnularPoissonExponent
  exact (tendsto_integral_signedAnnularExponentIntegrand_smallCoordinateCutoff hA t).const_smul
    (1 / (Real.pi ^ 2 / 6) : ℝ)

/-- The continuum annular compound-Poisson laws converge weakly to the
fixed-outer-cutoff law when the deleted strip shrinks to zero. -/
theorem tendsto_annularCompoundPoissonProbability_smallCoordinateCutoff
    {A : ℝ} (hA : 0 < A) :
    Tendsto
      (fun m : ℕ ↦ annularCompoundPoissonProbability
        (smallCoordinateCutoff m) A)
      atTop (nhds (cutoffCompoundPoissonProbability A)) := by
  apply levy_continuity_real
  intro t
  have hcut : ∀ᶠ m : ℕ in atTop, smallCoordinateCutoff m < A :=
    tendsto_smallCoordinateCutoff.eventually_lt_const hA
  have hexp : Tendsto
      (fun m : ℕ ↦ Complex.exp
        (signedAnnularPoissonExponent (smallCoordinateCutoff m) A t))
      atTop (nhds (Complex.exp (signedAnnularPoissonExponent 0 A t))) :=
    Complex.continuous_exp.continuousAt.tendsto.comp
      (tendsto_signedAnnularPoissonExponent_smallCoordinateCutoff hA t)
  rw [cutoffCompoundPoissonProbability,
    charFun_annularCompoundPoissonProbability (le_refl 0) hA]
  apply hexp.congr'
  filter_upwards [hcut] with m hm
  rw [charFun_annularCompoundPoissonProbability
    (smallCoordinateCutoff_nonneg m) hm]

/-! ## Symmetry and the outer-cutoff limit -/

theorem signedAnnularExponentIntegrand_neg_add
    (t x u : ℝ) :
    signedAnnularExponentIntegrand t (-x, u) +
        signedAnnularExponentIntegrand t (x, u) =
      ((2 * (Real.cos (t * bernoulliMark u / x) - 1) : ℝ) : ℂ) := by
  unfold signedAnnularExponentIntegrand signedAnnularJumpKernel markedShotKernel
  have hdiv : bernoulliMark u / -x = -(bernoulliMark u / x) := by ring
  rw [hdiv]
  push_cast
  rw [show (↑t : ℂ) * (-(↑(bernoulliMark u) / ↑x)) * Complex.I =
      -((↑t : ℂ) * (↑(bernoulliMark u) / ↑x)) * Complex.I by ring]
  have hy : (↑t : ℂ) * (↑(bernoulliMark u) / ↑x) =
      ((t * bernoulliMark u / x : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hy]
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  simp only [Complex.cos_neg, Complex.sin_neg]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast
  ring

theorem integrableOn_signedAnnularExponentIntegrand_section
    (ε A t u : ℝ) :
    IntegrableOn (fun x : ℝ ↦ signedAnnularExponentIntegrand t (x, u))
      (signedAnnulusSet ε A) volume := by
  have hfinite : volume (signedAnnulusSet ε A) ≠ ∞ := by
    have h := measure_ne_top (signedAnnulusFiniteMeasure ε A : Measure ℝ) univ
    simpa only [signedAnnulusFiniteMeasure_toMeasure,
      Measure.restrict_apply_univ] using! h
  apply Measure.integrableOn_of_bounded hfinite
    ((measurable_signedAnnularExponentIntegrand t).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  filter_upwards with x
  unfold signedAnnularExponentIntegrand
  calc
    ‖Complex.exp ((t : ℂ) * signedAnnularJumpKernel (x, u) * Complex.I) - 1‖ ≤
        ‖Complex.exp ((t : ℂ) * signedAnnularJumpKernel (x, u) * Complex.I)‖ +
          ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by
      rw [Complex.norm_exp]
      norm_num

/-- For one torus mark, the two signed coordinate intervals pair to twice
the real cosine integral; their imaginary parts cancel exactly. -/
theorem integral_signedAnnularExponentIntegrand_section_zero
    {A : ℝ} (hA : 0 < A) (t u : ℝ) :
    (∫ x : ℝ, signedAnnularExponentIntegrand t (x, u)
      ∂(signedAnnulusFiniteMeasure 0 A : Measure ℝ)) =
      ∫ x : ℝ in 0..A,
        ((2 * (Real.cos (t * bernoulliMark u / x) - 1) : ℝ) : ℂ) := by
  let f : ℝ → ℂ := fun x ↦ signedAnnularExponentIntegrand t (x, u)
  have hfull : IntegrableOn f (signedAnnulusSet 0 A) volume :=
    integrableOn_signedAnnularExponentIntegrand_section 0 A t u
  have hneg : IntegrableOn f (Ioo (-A) 0) volume := by
    apply hfull.mono_set
    intro x hx
    exact Or.inl (by simpa only [neg_zero] using! hx)
  have hpos : IntegrableOn f (Ioo 0 A) volume := by
    apply hfull.mono_set
    intro x hx
    exact Or.inr hx
  have hnegInt : IntervalIntegrable f volume (-A) 0 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).mpr hneg
  have hposInt : IntervalIntegrable f volume 0 A :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hA.le).mpr hpos
  have hnegCompInt : IntervalIntegrable (fun x ↦ f (-x)) volume 0 A := by
    have h := (IntervalIntegrable.iff_comp_neg (f := f) (a := -A) (b := 0)).mp hnegInt
    simpa only [neg_neg, neg_zero] using! h.symm
  rw [signedAnnulusFiniteMeasure_toMeasure]
  change (∫ x : ℝ in signedAnnulusSet 0 A, f x) = _
  rw [signedAnnulusSet,
    integral_union_ae (disjoint_signedAnnulus_halves (le_refl 0)).aedisjoint
      measurableSet_Ioo.nullMeasurableSet
      (by simpa only [neg_zero] using! hneg) hpos]
  simp only [neg_zero]
  have hnegSet : (∫ x : ℝ in Ioo (-A) 0, f x) = ∫ x : ℝ in -A..0, f x := by
    rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
  have hposSet : (∫ x : ℝ in Ioo 0 A, f x) = ∫ x : ℝ in 0..A, f x := by
    rw [intervalIntegral.integral_of_le hA.le, integral_Ioc_eq_integral_Ioo]
  rw [hnegSet, hposSet]
  have hreflect : (∫ x : ℝ in -A..0, f x) = ∫ x : ℝ in 0..A, f (-x) := by
    simpa only [neg_zero] using!
      (intervalIntegral.integral_comp_neg (a := 0) (b := A) f).symm
  rw [hreflect]
  rw [← intervalIntegral.integral_add hnegCompInt hposInt]
  apply intervalIntegral.integral_congr
  intro x _hx
  exact signedAnnularExponentIntegrand_neg_add t x u

/-- Fubini plus signed-coordinate symmetry expresses the raw complex
integral as twice the real cosine integral appearing in the manuscript. -/
theorem integral_signedAnnularExponentIntegrand_zero_eq_cosine
    {A : ℝ} (hA : 0 < A) (t : ℝ) :
    (∫ xu : ℝ × ℝ, signedAnnularExponentIntegrand t xu
      ∂((signedAnnulusFiniteMeasure 0 A : Measure ℝ).prod uniform01Measure)) =
      ((2 * (∫ u : ℝ in 0..1,
        ∫ x : ℝ in 0..A,
          (Real.cos (t * bernoulliMark u / x) - 1)) : ℝ) : ℂ) := by
  have hraw := integrable_signedAnnularExponentIntegrand_raw 0 A t
  calc
    (∫ xu : ℝ × ℝ, signedAnnularExponentIntegrand t xu
        ∂((signedAnnulusFiniteMeasure 0 A : Measure ℝ).prod uniform01Measure)) =
        ∫ u : ℝ, ∫ x : ℝ, signedAnnularExponentIntegrand t (x, u)
          ∂(signedAnnulusFiniteMeasure 0 A : Measure ℝ) ∂uniform01Measure :=
      integral_prod_symm _ hraw
    _ = ∫ u : ℝ,
        (∫ x : ℝ in 0..A,
          ((2 * (Real.cos (t * bernoulliMark u / x) - 1) : ℝ) : ℂ))
        ∂uniform01Measure := by
      apply integral_congr_ae
      filter_upwards with u
      exact integral_signedAnnularExponentIntegrand_section_zero hA t u
    _ = ∫ u : ℝ in 0..1,
        (∫ x : ℝ in 0..A,
          ((2 * (Real.cos (t * bernoulliMark u / x) - 1) : ℝ) : ℂ)) := by
      rw [uniform01Measure]
      rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
    _ = ∫ u : ℝ in 0..1,
        ((2 * (∫ x : ℝ in 0..A,
          (Real.cos (t * bernoulliMark u / x) - 1)) : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro u _hu
      dsimp only
      rw [intervalIntegral.integral_ofReal,
        intervalIntegral.integral_const_mul]
    _ = ((2 * (∫ u : ℝ in 0..1,
        ∫ x : ℝ in 0..A,
          (Real.cos (t * bernoulliMark u / x) - 1)) : ℝ) : ℂ) := by
      rw [intervalIntegral.integral_ofReal,
        intervalIntegral.integral_const_mul]

/-- Exact finite-outer-cutoff exponent in the real cosine form used by the
Poisson--Cauchy calculation. -/
theorem signedAnnularPoissonExponent_zero_eq_cosine
    {A : ℝ} (hA : 0 < A) (t : ℝ) :
    signedAnnularPoissonExponent 0 A t =
      (((2 / (Real.pi ^ 2 / 6)) *
        (∫ u : ℝ in 0..1,
          ∫ x : ℝ in 0..A,
            (Real.cos (t * bernoulliMark u / x) - 1)) : ℝ) : ℂ) := by
  unfold signedAnnularPoissonExponent
  rw [integral_signedAnnularExponentIntegrand_zero_eq_cosine hA t]
  simp only [Complex.real_smul]
  push_cast
  ring

/-- The nonnegative positive-coordinate truncation used for monotone
convergence in the outer cutoff. -/
def positiveCosineTruncation (B t u : ℝ) : ℝ :=
  ∫ x : ℝ in Ioo 0 B, (1 - Real.cos (t * bernoulliMark u / x))

theorem integrableOn_positiveCosineIntegrand
    (B t u : ℝ) :
    IntegrableOn (fun x : ℝ ↦ 1 - Real.cos (t * bernoulliMark u / x))
      (Ioo 0 B) volume := by
  apply Measure.integrableOn_of_bounded (M := 2) measure_Ioo_lt_top.ne
    (measurable_const.sub
      (((measurable_const.mul
        (bernoulliMark_measurable.comp measurable_const)).div
          measurable_id).cos)).aestronglyMeasurable
  filter_upwards with x
  change ‖1 - Real.cos (t * bernoulliMark u / x)‖ ≤ (2 : ℝ)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
  linarith [Real.neg_one_le_cos (t * bernoulliMark u / x)]

theorem positiveCosineTruncation_eq_neg_intervalIntegral
    {B : ℝ} (hB : 0 ≤ B) (t u : ℝ) :
    positiveCosineTruncation B t u =
      -(∫ x : ℝ in 0..B,
        (Real.cos (t * bernoulliMark u / x) - 1)) := by
  unfold positiveCosineTruncation
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hB,
    ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro x _hx
  ring

theorem intervalIntegral_cosine_eq_abs_parameter
    (B t u : ℝ) :
    (∫ x : ℝ in 0..B,
      (Real.cos (t * bernoulliMark u / x) - 1)) =
      ∫ x : ℝ in 0..B,
        (Real.cos ((|t| * bernoulliMark u) / x) - 1) := by
  apply intervalIntegral.integral_congr
  intro x _hx
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · have ht' : t ≤ 0 := le_of_not_ge ht
    rw [abs_of_nonpos ht']
    dsimp only
    rw [show (-t * bernoulliMark u) / x =
      -(t * bernoulliMark u / x) by ring, Real.cos_neg]

theorem tendsto_positiveCosineTruncation_nat (t u : ℝ) :
    Tendsto (fun n : ℕ ↦ positiveCosineTruncation (n : ℝ) t u)
      atTop (nhds (Real.pi * |t| * bernoulliMark u / 2)) := by
  let a : ℝ := |t| * bernoulliMark u
  have ha : 0 ≤ a := mul_nonneg (abs_nonneg t) (bernoulliMark_nonneg u)
  have hbase := (tendsto_intervalIntegral_cos_inv_sub_one a ha).comp
    tendsto_natCast_atTop_atTop
  have hneg := hbase.neg
  have hseq : (fun n : ℕ ↦ positiveCosineTruncation (n : ℝ) t u) =
      (fun n : ℕ ↦ -(∫ x : ℝ in 0..(n : ℝ),
        (Real.cos (a / x) - 1))) := by
    funext n
    rw [positiveCosineTruncation_eq_neg_intervalIntegral (by positivity),
      intervalIntegral_cosine_eq_abs_parameter]
  rw [hseq]
  have hlim : -(-Real.pi * a / 2) =
      Real.pi * |t| * bernoulliMark u / 2 := by
    dsimp [a]
    ring
  simpa only [Function.comp_apply, hlim] using! hneg

theorem monotone_positiveCosineTruncation_nat (t u : ℝ) :
    Monotone (fun n : ℕ ↦ positiveCosineTruncation (n : ℝ) t u) := by
  intro n m hnm
  unfold positiveCosineTruncation
  apply setIntegral_mono_set
    (integrableOn_positiveCosineIntegrand (m : ℝ) t u)
  · filter_upwards with x
    exact sub_nonneg.mpr (Real.cos_le_one _)
  · filter_upwards with x hx
    have hcast : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    exact ⟨hx.1, hx.2.trans_le hcast⟩

theorem integrable_positiveCosineTruncation_nat (n : ℕ) (t : ℝ) :
    Integrable (fun u : ℝ ↦ positiveCosineTruncation (n : ℝ) t u)
      uniform01Measure := by
  let μn : Measure ℝ := volume.restrict (Ioo 0 (n : ℝ))
  let F : ℝ × ℝ → ℝ := fun ux ↦
    1 - Real.cos (t * bernoulliMark ux.1 / ux.2)
  have hF : Integrable F (uniform01Measure.prod μn) := by
    refine (integrable_const (2 : ℝ)).mono ?_ ?_
    · exact (measurable_const.sub
        (((measurable_const.mul
          (bernoulliMark_measurable.comp measurable_fst)).div
            measurable_snd).cos)).aestronglyMeasurable
    · filter_upwards with ux
      dsimp [F]
      rw [abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
      norm_num
      linarith [Real.neg_one_le_cos (t * bernoulliMark ux.1 / ux.2)]
  have hinner := hF.integral_prod_left
  refine hinner.congr (Filter.Eventually.of_forall fun u ↦ ?_)
  dsimp [F, μn, positiveCosineTruncation]

theorem integrable_poissonCosineLimit (t : ℝ) :
    Integrable (fun u : ℝ ↦ Real.pi * |t| * bernoulliMark u / 2)
      uniform01Measure := by
  refine (integrable_const (Real.pi * |t| / 16)).mono
    (((measurable_const.mul measurable_const).mul bernoulliMark_measurable).div_const
      2).aestronglyMeasurable ?_
  filter_upwards with u
  simp only [Real.norm_eq_abs]
  have hV := abs_bernoulliMark_le_one_eighth u
  rw [abs_of_nonneg (bernoulliMark_nonneg u)] at hV
  have hc : 0 ≤ Real.pi * |t| := mul_nonneg Real.pi_pos.le (abs_nonneg t)
  rw [abs_of_nonneg (div_nonneg (mul_nonneg hc (bernoulliMark_nonneg u)) (by norm_num)),
    abs_of_nonneg (div_nonneg hc (by norm_num))]
  calc
    Real.pi * |t| * bernoulliMark u / 2 ≤
        Real.pi * |t| * (1 / 8) / 2 := by gcongr
    _ = Real.pi * |t| / 16 := by ring

theorem integral_poissonCosineLimit (t : ℝ) :
    (∫ u : ℝ, Real.pi * |t| * bernoulliMark u / 2
      ∂uniform01Measure) = Real.pi * |t| / 24 := by
  have hfun : (fun u : ℝ ↦ Real.pi * |t| * bernoulliMark u / 2) =
      (fun u : ℝ ↦ (Real.pi * |t| / 2) * bernoulliMark u) := by
    funext u
    ring
  rw [hfun, uniform01Measure]
  change (∫ u : ℝ in Ioo 0 1,
    (Real.pi * |t| / 2) * bernoulliMark u) = _
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num),
    intervalIntegral.integral_const_mul, integral_bernoulliMark]
  ring

theorem tendsto_integral_positiveCosineTruncation_nat (t : ℝ) :
    Tendsto
      (fun n : ℕ ↦ ∫ u : ℝ, positiveCosineTruncation (n : ℝ) t u
        ∂uniform01Measure)
      atTop (nhds (Real.pi * |t| / 24)) := by
  have h := integral_tendsto_of_tendsto_of_monotone
    (fun n ↦ integrable_positiveCosineTruncation_nat n t)
    (integrable_poissonCosineLimit t)
    (Filter.Eventually.of_forall fun u ↦ monotone_positiveCosineTruncation_nat t u)
    (Filter.Eventually.of_forall fun u ↦ tendsto_positiveCosineTruncation_nat t u)
  rw [integral_poissonCosineLimit] at h
  exact h

theorem doubleCosineInterval_eq_neg_integral_positiveCosineTruncation
    (n : ℕ) (t : ℝ) :
    (∫ u : ℝ in 0..1,
      ∫ x : ℝ in 0..(n : ℝ),
        (Real.cos (t * bernoulliMark u / x) - 1)) =
      -(∫ u : ℝ, positiveCosineTruncation (n : ℝ) t u
        ∂uniform01Measure) := by
  have huniform :
      (∫ u : ℝ, positiveCosineTruncation (n : ℝ) t u
        ∂uniform01Measure) =
      ∫ u : ℝ in 0..1, positiveCosineTruncation (n : ℝ) t u := by
    rw [uniform01Measure]
    rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
  rw [huniform, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro u _hu
  dsimp only
  rw [positiveCosineTruncation_eq_neg_intervalIntegral (by positivity)]
  ring

theorem tendsto_doubleCosineInterval_nat (t : ℝ) :
    Tendsto
      (fun n : ℕ ↦ ∫ u : ℝ in 0..1,
        ∫ x : ℝ in 0..(n : ℝ),
          (Real.cos (t * bernoulliMark u / x) - 1))
      atTop (nhds (-Real.pi * |t| / 24)) := by
  have h := (tendsto_integral_positiveCosineTruncation_nat t).neg
  have h' := h.congr' (Filter.Eventually.of_forall fun n ↦
    (doubleCosineInterval_eq_neg_integral_positiveCosineTruncation n t).symm)
  simpa only [neg_div, neg_mul] using! h'

theorem tendsto_signedAnnularPoissonExponent_nat (t : ℝ) :
    Tendsto
      (fun A : ℕ ↦ signedAnnularPoissonExponent 0 (A : ℝ) t)
      atTop (nhds (((-|t| / (2 * Real.pi) : ℝ)) : ℂ)) := by
  have hscaled : Tendsto
      (fun A : ℕ ↦ (2 / (Real.pi ^ 2 / 6)) *
        (∫ u : ℝ in 0..1,
          ∫ x : ℝ in 0..(A : ℝ),
            (Real.cos (t * bernoulliMark u / x) - 1)))
      atTop (nhds (-|t| / (2 * Real.pi))) := by
    have h := (tendsto_doubleCosineInterval_nat t).const_mul
      (2 / (Real.pi ^ 2 / 6))
    convert! h using 1
    · field_simp [Real.pi_ne_zero]
      ring_nf
  have hcast := hscaled.ofReal
  apply hcast.congr'
  filter_upwards [eventually_ge_atTop 1] with A hA
  rw [signedAnnularPoissonExponent_zero_eq_cosine
    (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hA)) t]

/-- The fixed-outer-cutoff continuum laws converge to the exact centered
Cauchy law of scale `1/(2π)`. -/
theorem tendsto_cutoffCompoundPoissonProbability_cauchy :
    Tendsto (fun A : ℕ ↦ cutoffCompoundPoissonProbability (A : ℝ))
      atTop (nhds cauchyLimitProbability) := by
  apply levy_continuity_real
  intro t
  have hexp : Tendsto
      (fun A : ℕ ↦ Complex.exp (signedAnnularPoissonExponent 0 (A : ℝ) t))
      atTop (nhds (Complex.exp ((-|t| / (2 * Real.pi) : ℝ) : ℂ))) :=
    Complex.continuous_exp.continuousAt.tendsto.comp
      (tendsto_signedAnnularPoissonExponent_nat t)
  rw [charFun_cauchyLimitProbability]
  have htarget : Complex.exp (-((|t| / (2 * Real.pi) : ℝ) : ℂ)) =
      Complex.exp (((-|t| / (2 * Real.pi) : ℝ) : ℂ)) := by
    congr 1
    push_cast
    ring
  rw [htarget]
  exact hexp.congr' (by
    filter_upwards [eventually_ge_atTop 1] with A hA
    rw [cutoffCompoundPoissonProbability,
      charFun_annularCompoundPoissonProbability (le_refl 0)
        (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hA))])

end

end Erdos1002
