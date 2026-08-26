import ErdosProblems.Erdos1002.GaussMovingSignedMarkedFourierZero
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Measure.Portmanteau

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Continuous torus tests for moving signed marked tuples

The marked factorial argument first proves convergence of every torus
Fourier mode.  This file supplies the functional-analytic passage which is
often abbreviated as "by density of trigonometric polynomials".

We use the normalized Haar probability measure on each copy of `ℝ/ℤ`.
The finite marked statistic is Lipschitz in the sup norm, with Lipschitz
constant exactly its unmarked tuple mass.  Stone--Weierstrass then upgrades
the mode limits to every continuous test on the product torus.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance gaussMovingSignedMarkedContinuousPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

local instance unitAddCircleMeasureSpaceMarkedContinuous :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance unitAddCircleProbabilityMarkedContinuous :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## Literal continuous tests -/

/-- The vector of selected torus marks, regarded as a point of
`(ℝ/ℤ)^r`. -/
def gaussMovingUnitTorusPoint
    {r : ℕ} (N : ℕ) (times : Fin r → ℕ) (x : ℝ) :
    UnitAddTorus (Fin r) :=
  fun i ↦ (gaussSelectedPrefixTorusMark N (times i) x : UnitAddCircle)

theorem measurable_gaussMovingUnitTorusPoint
    {r : ℕ} (N : ℕ) (times : Fin r → ℕ) :
    Measurable (gaussMovingUnitTorusPoint N times) := by
  apply measurable_pi_lambda
  intro i
  exact (AddCircle.continuous_mk' (1 : ℝ)).measurable.comp
    (measurable_gaussSelectedPrefixTorusMark N (times i))

/-- A continuous torus test inserted into the exact signed tuple event and
summed over an arbitrary finite tuple family. -/
def movingSignedMarkedContinuousTupleSum
    {r : ℕ} (mu : Measure ℝ) (N : ℕ) (scale : ℝ)
    (lower upper : Fin r → ℝ)
    (f : C(UnitAddTorus (Fin r), ℂ))
    (tuples : Finset (Fin r → ℕ)) : ℂ :=
  ∑ times ∈ tuples,
    ∫ x in gaussSignedApproximationTupleEvent
        scale lower upper times,
      f (gaussMovingUnitTorusPoint N times x) ∂mu

/-- The positive finite measure on the product torus represented by the
same marked tuple statistic.  Introducing this literal measure makes the
subsequent use of weak convergence and continuity sets type-correct. -/
def movingSignedMarkedTupleFiniteMeasure
    {r : ℕ} (mu : Measure ℝ) [IsFiniteMeasure mu]
    (N : ℕ) (scale : ℝ) (lower upper : Fin r → ℝ)
    (tuples : Finset (Fin r → ℕ)) :
    FiniteMeasure (UnitAddTorus (Fin r)) :=
  ∑ times ∈ tuples,
    FiniteMeasure.map
      (FiniteMeasure.restrict
        (⟨mu, inferInstance⟩ : FiniteMeasure ℝ)
        (gaussSignedApproximationTupleEvent
          scale lower upper times))
      (gaussMovingUnitTorusPoint N times)

theorem integrableOn_continuous_comp_gaussMovingUnitTorusPoint
    {r : ℕ} (mu : Measure ℝ) [IsFiniteMeasure mu]
    (N : ℕ) (scale : ℝ) (lower upper : Fin r → ℝ)
    (f : C(UnitAddTorus (Fin r), ℂ)) (times : Fin r → ℕ) :
    IntegrableOn
      (fun x ↦ f (gaussMovingUnitTorusPoint N times x))
      (gaussSignedApproximationTupleEvent scale lower upper times) mu := by
  have hmeas : Measurable
      (fun x ↦ f (gaussMovingUnitTorusPoint N times x)) :=
    f.continuous.measurable.comp
      (measurable_gaussMovingUnitTorusPoint N times)
  exact (Integrable.of_bound hmeas.aestronglyMeasurable ‖f‖
    (Eventually.of_forall fun x ↦ f.norm_coe_le_norm _)).integrableOn

/-- Integration against the finite torus measure is exactly the original
finite sum of restricted tuple integrals. -/
theorem integral_movingSignedMarkedTupleFiniteMeasure
    {r : ℕ} (mu : Measure ℝ) [IsFiniteMeasure mu]
    (N : ℕ) (scale : ℝ) (lower upper : Fin r → ℝ)
    (f : C(UnitAddTorus (Fin r), ℂ))
    (tuples : Finset (Fin r → ℕ)) :
    (∫ z, f z ∂(movingSignedMarkedTupleFiniteMeasure
        mu N scale lower upper tuples :
          Measure (UnitAddTorus (Fin r)))) =
      movingSignedMarkedContinuousTupleSum
        mu N scale lower upper f tuples := by
  classical
  unfold movingSignedMarkedTupleFiniteMeasure
    movingSignedMarkedContinuousTupleSum
  rw [FiniteMeasure.toMeasure_sum,
    MeasureTheory.integral_finset_sum_measure]
  · apply Finset.sum_congr rfl
    intro times _htimes
    rw [FiniteMeasure.toMeasure_map,
      MeasureTheory.integral_map
        (measurable_gaussMovingUnitTorusPoint N times).aemeasurable
        f.continuous.measurable.aestronglyMeasurable]
    rfl
  · intro times _htimes
    exact Integrable.of_bound
      f.continuous.measurable.aestronglyMeasurable ‖f‖
      (Eventually.of_forall fun z ↦ f.norm_coe_le_norm z)

/-! ## Finite trigonometric polynomials on the quotient torus -/

/-- Bundled trigonometric polynomial on the quotient torus. -/
def unitTorusTrigPolynomial
    {r : ℕ} (p : (Fin r → ℤ) →₀ ℂ) :
    C(UnitAddTorus (Fin r), ℂ) :=
  p.sum fun mode coefficient ↦
    coefficient • UnitAddTorus.mFourier mode

/-- Evaluation on real representatives agrees with the explicit real
Fourier polynomial used in the marked coefficient. -/
theorem unitTorusTrigPolynomial_real_apply
    {r : ℕ} (p : (Fin r → ℤ) →₀ ℂ) (u : Fin r → ℝ) :
    unitTorusTrigPolynomial p (fun i ↦ (u i : UnitAddCircle)) =
      realTorusTrigPolynomial p u := by
  classical
  unfold unitTorusTrigPolynomial realTorusTrigPolynomial Finsupp.sum
  change (ContinuousMap.evalAlgHom ℂ ℂ
      (fun i ↦ (u i : UnitAddCircle)))
      (∑ mode ∈ p.support,
        p mode • UnitAddTorus.mFourier mode) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro mode _hmode
  rw [map_smul]
  simp only [smul_eq_mul]
  congr 1
  unfold UnitAddTorus.mFourier realTorusFourierCharacter
  change (∏ i, fourier (mode i) (u i : UnitAddCircle)) =
    ∏ i, paperExp ((mode i : ℝ) * u i)
  apply Finset.prod_congr rfl
  intro i _hi
  rw [fourier_coe_apply]
  unfold paperExp
  congr 1
  push_cast
  ring

/-- The quotient-torus formulation of a finite trigonometric test is
literally the real-representative formulation already used for the marked
Fourier coefficients. -/
theorem movingSignedMarkedContinuousTupleSum_unitTorusTrigPolynomial
    {r : ℕ} (mu : Measure ℝ) [IsFiniteMeasure mu]
    (N : ℕ) (scale : ℝ) (lower upper : Fin r → ℝ)
    (p : (Fin r → ℤ) →₀ ℂ)
    (tuples : Finset (Fin r → ℕ)) :
    movingSignedMarkedContinuousTupleSum
        mu N scale lower upper (unitTorusTrigPolynomial p) tuples =
      movingSignedMarkedTrigTupleSum
        mu N scale lower upper p tuples := by
  classical
  unfold movingSignedMarkedContinuousTupleSum
    movingSignedMarkedTrigTupleSum
  apply Finset.sum_congr rfl
  intro times _htimes
  let E : Set ℝ :=
    gaussSignedApproximationTupleEvent scale lower upper times
  have hE : MeasurableSet E :=
    measurableSet_gaussSignedApproximationTupleEvent
      scale lower upper times
  rw [← integral_indicator hE]
  apply integral_congr_ae
  filter_upwards with x
  change E.indicator
      (fun y ↦ (unitTorusTrigPolynomial p)
        (gaussMovingUnitTorusPoint N times y)) x =
    E.indicator
      (fun y ↦ realTorusTrigPolynomial p
        (fun i ↦ gaussSelectedPrefixTorusMark N (times i) y)) x
  by_cases hx : x ∈ E
  · simp only [Set.indicator_of_mem hx]
    simpa only [gaussMovingUnitTorusPoint] using!
      unitTorusTrigPolynomial_real_apply p
        (fun i ↦ gaussSelectedPrefixTorusMark N (times i) x)
  · simp only [Set.indicator_of_notMem hx]

/-! ## Uniform sup-norm control -/

/-- The finite marked statistic is Lipschitz in the torus test, with the
unmarked tuple mass as its exact operator-norm majorant. -/
theorem norm_movingSignedMarkedContinuousTupleSum_sub_le
    {r : ℕ} (mu : Measure ℝ) [IsFiniteMeasure mu]
    (N : ℕ) (scale : ℝ) (lower upper : Fin r → ℝ)
    (f g : C(UnitAddTorus (Fin r), ℂ))
    (tuples : Finset (Fin r → ℕ)) :
    ‖movingSignedMarkedContinuousTupleSum
          mu N scale lower upper f tuples -
        movingSignedMarkedContinuousTupleSum
          mu N scale lower upper g tuples‖ ≤
      ‖f - g‖ * movingSignedApproximationTupleMassSum
        mu scale lower upper tuples := by
  classical
  unfold movingSignedMarkedContinuousTupleSum
    movingSignedApproximationTupleMassSum
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ times ∈ tuples,
        ((∫ x in gaussSignedApproximationTupleEvent
            scale lower upper times,
            f (gaussMovingUnitTorusPoint N times x) ∂mu) -
          ∫ x in gaussSignedApproximationTupleEvent
            scale lower upper times,
            g (gaussMovingUnitTorusPoint N times x) ∂mu)‖ ≤
        ∑ times ∈ tuples,
          ‖(∫ x in gaussSignedApproximationTupleEvent
              scale lower upper times,
              f (gaussMovingUnitTorusPoint N times x) ∂mu) -
            ∫ x in gaussSignedApproximationTupleEvent
              scale lower upper times,
              g (gaussMovingUnitTorusPoint N times x) ∂mu‖ :=
      norm_sum_le _ _
    _ ≤ ∑ times ∈ tuples,
        ‖f - g‖ * mu.real
          (gaussSignedApproximationTupleEvent
            scale lower upper times) := by
      apply Finset.sum_le_sum
      intro times _htimes
      let E : Set ℝ :=
        gaussSignedApproximationTupleEvent scale lower upper times
      have hf := integrableOn_continuous_comp_gaussMovingUnitTorusPoint
        mu N scale lower upper f times
      have hg := integrableOn_continuous_comp_gaussMovingUnitTorusPoint
        mu N scale lower upper g times
      rw [← integral_sub hf hg]
      apply norm_setIntegral_le_of_norm_le_const (measure_lt_top mu _)
      intro x _hx
      change ‖f (gaussMovingUnitTorusPoint N times x) -
          g (gaussMovingUnitTorusPoint N times x)‖ ≤ ‖f - g‖
      rw [← ContinuousMap.sub_apply]
      exact (f - g).norm_coe_le_norm _
    _ = ‖f - g‖ *
        ∑ times ∈ tuples,
          mu.real (gaussSignedApproximationTupleEvent
            scale lower upper times) := by
      rw [Finset.mul_sum]

/-! ## Uniform density and Haar means -/

/-- Every continuous function on the finite product torus is uniformly
approximable by one explicitly finitely supported Fourier polynomial. -/
theorem exists_unitTorusTrigPolynomial_norm_sub_lt
    {r : ℕ} (f : C(UnitAddTorus (Fin r), ℂ))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ p : (Fin r → ℤ) →₀ ℂ,
      ‖f - unitTorusTrigPolynomial p‖ < epsilon := by
  have hfClosure : f ∈
      (Submodule.span ℂ
        (Set.range (UnitAddTorus.mFourier (d := Fin r)))).topologicalClosure := by
    rw [UnitAddTorus.span_mFourier_closure_eq_top]
    exact Submodule.mem_top
  obtain ⟨g, hgSpan, hfg⟩ :=
    Metric.mem_closure_iff.mp hfClosure epsilon hepsilon
  obtain ⟨p, hp⟩ :=
    Finsupp.mem_span_range_iff_exists_finsupp.mp hgSpan
  refine ⟨p, ?_⟩
  have hpoly : unitTorusTrigPolynomial p = g := by
    exact hp
  simpa only [hpoly, dist_eq_norm] using! hfg

private theorem integral_fourier_unitAddCircle (n : ℤ) :
    (∫ x : UnitAddCircle, fourier n x) =
      if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    simp only [fourier_zero]
    simp
  · rw [if_neg hn]
    exact integral_eq_zero_of_add_right_eq_neg
      (μ := AddCircle.haarAddCircle)
      (@fourier_add_half_inv_index (1 : ℝ) n hn (by norm_num))

/-- The normalized product-Haar mean of one multivariate Fourier monomial
is one at the zero mode and zero otherwise. -/
theorem integral_unitAddTorus_mFourier
    {r : ℕ} (mode : Fin r → ℤ) :
    (∫ z : UnitAddTorus (Fin r), UnitAddTorus.mFourier mode z) =
      if mode = 0 then 1 else 0 := by
  rw [UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    MeasureTheory.integral_fintype_prod_volume_eq_prod]
  simp_rw [integral_fourier_unitAddCircle]
  by_cases hmode : mode = 0
  · subst mode
    simp
  · rw [if_neg hmode]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hmode
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [Pi.zero_apply] at hi
    rw [if_neg hi]

/-- The Haar mean of a finite trigonometric polynomial is exactly its
constant Fourier coefficient. -/
theorem integral_unitTorusTrigPolynomial
    {r : ℕ} (p : (Fin r → ℤ) →₀ ℂ) :
    (∫ z : UnitAddTorus (Fin r), unitTorusTrigPolynomial p z) = p 0 := by
  classical
  unfold unitTorusTrigPolynomial Finsupp.sum
  rw [show (fun z : UnitAddTorus (Fin r) ↦
      ((∑ mode ∈ p.support,
        p mode • UnitAddTorus.mFourier mode) :
          C(UnitAddTorus (Fin r), ℂ)) z) =
      (fun z ↦ ∑ mode ∈ p.support,
        (p mode • UnitAddTorus.mFourier mode) z) by
    funext z
    change (ContinuousMap.evalAlgHom ℂ ℂ z)
      (∑ mode ∈ p.support,
        p mode • UnitAddTorus.mFourier mode) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro mode _hmode
    rw [map_smul]
    simp only [smul_eq_mul, ContinuousMap.smul_apply]
    rfl]
  rw [MeasureTheory.integral_finset_sum]
  · simp_rw [ContinuousMap.smul_apply, smul_eq_mul,
      integral_const_mul, integral_unitAddTorus_mFourier]
    by_cases hp : 0 ∈ p.support
    · rw [Finset.sum_eq_single 0]
      · simp
      · intro mode _hmode hmodeNe
        simp [hmodeNe]
      · intro hnot
        exact (hnot hp).elim
    · have hp0 : p 0 = 0 := by
        simpa only [Finsupp.mem_support_iff, not_ne_iff] using! hp
      calc
        ∑ mode ∈ p.support,
            p mode * (if mode = 0 then 1 else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro mode hmodeSupport
          have hmodeNe : mode ≠ 0 := by
            intro hzero
            subst mode
            exact hp hmodeSupport
          simp [hmodeNe]
        _ = p 0 := hp0.symm
  · intro mode _hmode
    apply Integrable.of_bound
      ((UnitAddTorus.mFourier mode).continuous.measurable.const_smul
        (p mode)).aestronglyMeasurable ‖p mode‖
    filter_upwards with z
    change ‖p mode • UnitAddTorus.mFourier mode z‖ ≤ ‖p mode‖
    have hmodeNorm : ‖UnitAddTorus.mFourier mode z‖ = 1 := by
      unfold UnitAddTorus.mFourier
      change ‖∏ i, fourier (mode i) (z i)‖ = 1
      rw [norm_prod]
      simp only [fourier_apply, Circle.norm_coe,
        Finset.prod_const_one]
    rw [norm_smul, hmodeNorm, mul_one]

/-- Every continuous complex-valued function on the compact probability
torus is Bochner integrable.  We record this explicitly so that the
density argument below never relies on an implicit integrability
side-condition. -/
theorem integrable_unitTorus_continuous
    {r : ℕ} (f : C(UnitAddTorus (Fin r), ℂ)) :
    Integrable f := by
  apply Integrable.of_bound f.continuous.measurable.aestronglyMeasurable ‖f‖
  filter_upwards with z
  exact f.norm_coe_le_norm z

/-- Haar integration on the normalized product torus has operator norm at
most one for the uniform norm. -/
theorem norm_integral_unitTorus_sub_le
    {r : ℕ} (f g : C(UnitAddTorus (Fin r), ℂ)) :
    ‖(∫ z, f z) - ∫ z, g z‖ ≤ ‖f - g‖ := by
  rw [← integral_sub
    (integrable_unitTorus_continuous f)
    (integrable_unitTorus_continuous g)]
  have h := norm_integral_le_of_norm_le_const
    (μ := (volume : Measure (UnitAddTorus (Fin r))))
    (f := fun z ↦ (f - g) z) (C := ‖f - g‖)
    (Eventually.of_forall fun z ↦ (f - g).norm_coe_le_norm z)
  simpa only [ContinuousMap.sub_apply, probReal_univ,
    mul_one] using! h

/-- A nonnegative real multiple of normalized Haar measure, bundled as a
finite measure.  `toNNReal` makes the definition total; applications below
prove nonnegativity of the limiting mass before identifying its integral. -/
def scaledUnitTorusHaarFiniteMeasure
    {r : ℕ} (mass : ℝ) : FiniteMeasure (UnitAddTorus (Fin r)) :=
  let haar : FiniteMeasure (UnitAddTorus (Fin r)) :=
    ⟨volume, inferInstance⟩
  mass.toNNReal • haar

/-- Normalized Haar probability on the finite product torus. -/
def unitTorusHaarProbabilityMeasure
    {r : ℕ} : ProbabilityMeasure (UnitAddTorus (Fin r)) :=
  ⟨volume, inferInstance⟩

@[simp] theorem scaledUnitTorusHaarFiniteMeasure_mass
    {r : ℕ} (mass : ℝ) :
    (scaledUnitTorusHaarFiniteMeasure (r := r) mass).mass =
      mass.toNNReal := by
  unfold scaledUnitTorusHaarFiniteMeasure FiniteMeasure.mass
  rw [FiniteMeasure.smul_apply, smul_eq_mul]
  change mass.toNNReal *
    (unitTorusHaarProbabilityMeasure
      (r := r)).toFiniteMeasure.mass = mass.toNNReal
  rw [ProbabilityMeasure.mass_toFiniteMeasure, mul_one]

theorem scaledUnitTorusHaarFiniteMeasure_ne_zero
    {r : ℕ} {mass : ℝ} (hmass : 0 < mass) :
    scaledUnitTorusHaarFiniteMeasure (r := r) mass ≠ 0 := by
  unfold scaledUnitTorusHaarFiniteMeasure
  apply smul_ne_zero
  · exact ne_of_gt (Real.toNNReal_pos.mpr hmass)
  · intro hzero
    have hzero' := congrArg
      (fun nu : FiniteMeasure (UnitAddTorus (Fin r)) ↦
        (nu : Measure (UnitAddTorus (Fin r))) Set.univ) hzero
    simp at hzero'

/-- A positive scalar multiple of Haar normalizes back to Haar exactly. -/
theorem scaledUnitTorusHaarFiniteMeasure_normalize
    {r : ℕ} {mass : ℝ} (hmass : 0 < mass) :
    (scaledUnitTorusHaarFiniteMeasure
      (r := r) mass).normalize =
        unitTorusHaarProbabilityMeasure (r := r) := by
  apply ProbabilityMeasure.eq_of_forall_apply_eq
  intro s hs
  rw [FiniteMeasure.normalize_eq_of_nonzero
    (scaledUnitTorusHaarFiniteMeasure (r := r) mass)
    (scaledUnitTorusHaarFiniteMeasure_ne_zero hmass) s]
  rw [scaledUnitTorusHaarFiniteMeasure_mass]
  unfold scaledUnitTorusHaarFiniteMeasure
  rw [FiniteMeasure.smul_apply, smul_eq_mul]
  have hcoeff : mass.toNNReal ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr hmass)
  rw [inv_mul_cancel_left₀ hcoeff]
  rfl

theorem integral_scaledUnitTorusHaarFiniteMeasure
    {r : ℕ} (mass : ℝ) (hmass : 0 ≤ mass)
    (f : C(UnitAddTorus (Fin r), ℂ)) :
    (∫ z, f z ∂(scaledUnitTorusHaarFiniteMeasure (r := r) mass :
        Measure (UnitAddTorus (Fin r)))) =
      (mass : ℂ) * ∫ z, f z := by
  unfold scaledUnitTorusHaarFiniteMeasure
  rw [FiniteMeasure.toMeasure_smul,
    MeasureTheory.integral_smul_nnreal_measure]
  simp only [NNReal.smul_def, Real.coe_toNNReal _ hmass,
    Complex.real_smul]
  rfl

/-- A limit of the nonnegative tuple masses is itself nonnegative. -/
theorem nonneg_massLimit_of_tendsto_movingSignedApproximationTupleMassSum
    {r : ℕ} (mu : Measure ℝ) [IsFiniteMeasure mu]
    (scale : ℕ → ℝ) (lower upper : Fin r → ℝ)
    (tuples : ℕ → Finset (Fin r → ℕ))
    (massLimit : ℝ)
    (hzero : Tendsto
      (fun n ↦ movingSignedApproximationTupleMassSum
        mu (scale n) lower upper (tuples n))
      atTop (nhds massLimit)) :
    0 ≤ massLimit := by
  apply ge_of_tendsto hzero
  filter_upwards with n
  unfold movingSignedApproximationTupleMassSum
  positivity

/-! ## Passage from Fourier modes to continuous marked tests -/

/-- If the unmarked tuple mass converges and every nonzero torus Fourier
mode vanishes, then the marked tuple statistic converges against every
continuous test to the product of the limiting mass and normalized Haar
measure.  The proof keeps the mass bound and both approximation errors
explicit; this is the density step needed for marked point-process
convergence. -/
theorem tendsto_movingSignedMarkedContinuousTupleSum_of_fourier
    {r : ℕ} (mu : Measure ℝ) [IsFiniteMeasure mu]
    (N : ℕ → ℕ) (scale : ℕ → ℝ)
    (lower upper : Fin r → ℝ)
    (f : C(UnitAddTorus (Fin r), ℂ))
    (tuples : ℕ → Finset (Fin r → ℕ))
    (massLimit : ℝ)
    (hzero : Tendsto
      (fun n ↦ movingSignedApproximationTupleMassSum
        mu (scale n) lower upper (tuples n))
      atTop (nhds massLimit))
    (hnonzero : ∀ mode : Fin r → ℤ, mode ≠ 0 →
      Tendsto
        (fun n ↦ movingSignedMarkedFourierTupleSum
          mu (N n) (scale n) lower upper mode (tuples n))
        atTop (nhds 0)) :
    Tendsto
      (fun n ↦ movingSignedMarkedContinuousTupleSum
        mu (N n) (scale n) lower upper f (tuples n))
      atTop
      (nhds ((massLimit : ℂ) *
        ∫ z : UnitAddTorus (Fin r), f z)) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  let K : ℝ := |massLimit| + 2
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  have hfourK : 0 < 4 * K := mul_pos (by norm_num) hK
  obtain ⟨p, hp⟩ :=
    exists_unitTorusTrigPolynomial_norm_sub_lt f
      (div_pos hepsilon hfourK)
  let g : C(UnitAddTorus (Fin r), ℂ) :=
    unitTorusTrigPolynomial p
  have hfg : ‖f - g‖ < epsilon / (4 * K) := by
    simpa only [g] using! hp
  have hKfg : K * ‖f - g‖ < epsilon / 4 := by
    calc
      K * ‖f - g‖ < K * (epsilon / (4 * K)) :=
        mul_lt_mul_of_pos_left hfg hK
      _ = epsilon / 4 := by
        field_simp [ne_of_gt hK]
  have htrigRaw :=
    tendsto_movingSignedMarkedTrigTupleSum_of_zero_and_nonzero
      mu N scale lower upper p tuples massLimit hzero
        (fun mode _hmodeSupport hmode ↦ hnonzero mode hmode)
  have htrig : Tendsto
      (fun n ↦ movingSignedMarkedContinuousTupleSum
        mu (N n) (scale n) lower upper g (tuples n))
      atTop
      (nhds ((massLimit : ℂ) *
        ∫ z : UnitAddTorus (Fin r), g z)) := by
    simpa only [g,
      movingSignedMarkedContinuousTupleSum_unitTorusTrigPolynomial,
      integral_unitTorusTrigPolynomial, mul_comm] using! htrigRaw
  obtain ⟨nMass, hnMass⟩ :=
    (Metric.tendsto_atTop.mp hzero) 1 zero_lt_one
  obtain ⟨nTrig, hnTrig⟩ :=
    (Metric.tendsto_atTop.mp htrig) (epsilon / 2) (half_pos hepsilon)
  refine ⟨max nMass nTrig, fun n hn ↦ ?_⟩
  have hnMass' : nMass ≤ n := (le_max_left _ _).trans hn
  have hnTrig' : nTrig ≤ n := (le_max_right _ _).trans hn
  let mass : ℝ := movingSignedApproximationTupleMassSum
    mu (scale n) lower upper (tuples n)
  have hmassDist : |mass - massLimit| < 1 := by
    simpa only [mass, Real.dist_eq] using! hnMass n hnMass'
  have hmassAbs : |mass| < |massLimit| + 1 := by
    calc
      |mass| = |(mass - massLimit) + massLimit| := by ring_nf
      _ ≤ |mass - massLimit| + |massLimit| := abs_add_le _ _
      _ < 1 + |massLimit| := by
        simpa only [add_comm] using!
          add_lt_add_right hmassDist |massLimit|
      _ = |massLimit| + 1 := by ring
  have hmassK : mass < K := by
    calc
      mass ≤ |mass| := le_abs_self mass
      _ < |massLimit| + 1 := hmassAbs
      _ < K := by
        dsimp only [K]
        linarith
  have hfirst :
      dist
        (movingSignedMarkedContinuousTupleSum
          mu (N n) (scale n) lower upper f (tuples n))
        (movingSignedMarkedContinuousTupleSum
          mu (N n) (scale n) lower upper g (tuples n)) <
        epsilon / 4 := by
    rw [dist_eq_norm]
    calc
      ‖movingSignedMarkedContinuousTupleSum
            mu (N n) (scale n) lower upper f (tuples n) -
          movingSignedMarkedContinuousTupleSum
            mu (N n) (scale n) lower upper g (tuples n)‖ ≤
          ‖f - g‖ * mass := by
        simpa only [mass] using!
          norm_movingSignedMarkedContinuousTupleSum_sub_le
            mu (N n) (scale n) lower upper f g (tuples n)
      _ ≤ ‖f - g‖ * K :=
        mul_le_mul_of_nonneg_left (le_of_lt hmassK) (norm_nonneg _)
      _ = K * ‖f - g‖ := mul_comm _ _
      _ < epsilon / 4 := hKfg
  have hcenter :
      dist
        (movingSignedMarkedContinuousTupleSum
          mu (N n) (scale n) lower upper g (tuples n))
        ((massLimit : ℂ) *
          ∫ z : UnitAddTorus (Fin r), g z) < epsilon / 2 :=
    hnTrig n hnTrig'
  have hmean :
      ‖(∫ z : UnitAddTorus (Fin r), g z) - ∫ z, f z‖ ≤
        ‖f - g‖ := by
    calc
      ‖(∫ z : UnitAddTorus (Fin r), g z) - ∫ z, f z‖ =
          ‖(∫ z : UnitAddTorus (Fin r), f z) - ∫ z, g z‖ :=
        norm_sub_rev _ _
      _ ≤ ‖f - g‖ := norm_integral_unitTorus_sub_le f g
  have habsMassK : |massLimit| ≤ K := by
    dsimp only [K]
    linarith
  have hthird :
      dist
        ((massLimit : ℂ) *
          ∫ z : UnitAddTorus (Fin r), g z)
        ((massLimit : ℂ) *
          ∫ z : UnitAddTorus (Fin r), f z) < epsilon / 4 := by
    rw [dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_real]
    calc
      |massLimit| *
          ‖(∫ z : UnitAddTorus (Fin r), g z) - ∫ z, f z‖ ≤
          |massLimit| * ‖f - g‖ :=
        mul_le_mul_of_nonneg_left hmean (abs_nonneg massLimit)
      _ ≤ K * ‖f - g‖ :=
        mul_le_mul_of_nonneg_right habsMassK (norm_nonneg _)
      _ < epsilon / 4 := hKfg
  calc
    dist
        (movingSignedMarkedContinuousTupleSum
          mu (N n) (scale n) lower upper f (tuples n))
        ((massLimit : ℂ) *
          ∫ z : UnitAddTorus (Fin r), f z) ≤
        dist
          (movingSignedMarkedContinuousTupleSum
            mu (N n) (scale n) lower upper f (tuples n))
          (movingSignedMarkedContinuousTupleSum
            mu (N n) (scale n) lower upper g (tuples n)) +
        dist
          (movingSignedMarkedContinuousTupleSum
            mu (N n) (scale n) lower upper g (tuples n))
          ((massLimit : ℂ) *
            ∫ z : UnitAddTorus (Fin r), f z) :=
      dist_triangle _ _ _
    _ ≤
        dist
          (movingSignedMarkedContinuousTupleSum
            mu (N n) (scale n) lower upper f (tuples n))
          (movingSignedMarkedContinuousTupleSum
            mu (N n) (scale n) lower upper g (tuples n)) +
        (dist
          (movingSignedMarkedContinuousTupleSum
            mu (N n) (scale n) lower upper g (tuples n))
          ((massLimit : ℂ) *
            ∫ z : UnitAddTorus (Fin r), g z) +
        dist
          ((massLimit : ℂ) *
            ∫ z : UnitAddTorus (Fin r), g z)
          ((massLimit : ℂ) *
            ∫ z : UnitAddTorus (Fin r), f z)) := by
      apply add_le_add_right
      exact dist_triangle _ _ _
    _ < epsilon / 4 + (epsilon / 2 + epsilon / 4) :=
      add_lt_add hfirst (add_lt_add hcenter hthird)
    _ = epsilon := by ring

/-- Measure-level formulation of the preceding theorem.  Thus the Fourier
calculation yields genuine weak convergence of the positive finite marked
tuple measures, rather than only an informal statement about test
functions. -/
theorem tendsto_movingSignedMarkedTupleFiniteMeasure_of_fourier
    {r : ℕ} (mu : Measure ℝ) [IsFiniteMeasure mu]
    (N : ℕ → ℕ) (scale : ℕ → ℝ)
    (lower upper : Fin r → ℝ)
    (tuples : ℕ → Finset (Fin r → ℕ))
    (massLimit : ℝ)
    (hzero : Tendsto
      (fun n ↦ movingSignedApproximationTupleMassSum
        mu (scale n) lower upper (tuples n))
      atTop (nhds massLimit))
    (hnonzero : ∀ mode : Fin r → ℤ, mode ≠ 0 →
      Tendsto
        (fun n ↦ movingSignedMarkedFourierTupleSum
          mu (N n) (scale n) lower upper mode (tuples n))
        atTop (nhds 0)) :
    Tendsto
      (fun n ↦ movingSignedMarkedTupleFiniteMeasure
        mu (N n) (scale n) lower upper (tuples n))
      atTop
      (nhds (scaledUnitTorusHaarFiniteMeasure (r := r) massLimit)) := by
  have hmass : 0 ≤ massLimit :=
    nonneg_massLimit_of_tendsto_movingSignedApproximationTupleMassSum
      mu scale lower upper tuples massLimit hzero
  rw [FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ]
  intro f
  have hcontinuous :=
    tendsto_movingSignedMarkedContinuousTupleSum_of_fourier
      mu N scale lower upper f.toContinuousMap tuples massLimit
        hzero hnonzero
  convert! hcontinuous using 1
  · funext n
    change
      (∫ z, f.toContinuousMap z
        ∂(movingSignedMarkedTupleFiniteMeasure
          mu (N n) (scale n) lower upper (tuples n) :
            Measure (UnitAddTorus (Fin r)))) = _
    exact integral_movingSignedMarkedTupleFiniteMeasure
      mu (N n) (scale n) lower upper f.toContinuousMap (tuples n)
  · congr 1
    change
      (∫ z, f.toContinuousMap z
        ∂(scaledUnitTorusHaarFiniteMeasure (r := r) massLimit :
          Measure (UnitAddTorus (Fin r)))) = _
    rw [integral_scaledUnitTorusHaarFiniteMeasure massLimit hmass]

/-! ## Continuity sets -/

/-- Weak convergence of nonzero finite measures implies convergence on
every continuity set.  Mathlib states the usual Portmanteau result for
probability measures; this lemma records the finite-measure consequence by
normalizing and multiplying back by the convergent total masses. -/
theorem tendsto_finiteMeasure_apply_of_null_frontier
    {Omega iota : Type*} [Nonempty Omega]
    [MeasurableSpace Omega] [TopologicalSpace Omega]
    [OpensMeasurableSpace Omega] [HasOuterApproxClosed Omega]
    {L : Filter iota} {nu : FiniteMeasure Omega}
    {nus : iota → FiniteMeasure Omega}
    (hnu : Tendsto nus L (nhds nu)) (hnuNonzero : nu ≠ 0)
    {E : Set Omega}
    (hfrontier : nu.normalize (frontier E) = 0) :
    Tendsto (fun i ↦ nus i E) L (nhds (nu E)) := by
  have hnormalized : Tendsto (fun i ↦ (nus i).normalize) L
      (nhds nu.normalize) :=
    nu.tendsto_normalize_of_tendsto hnu hnuNonzero
  have hset :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
      hnormalized hfrontier
  have hproduct := hnu.mass.mul hset
  rw [nu.self_eq_mass_mul_normalize E]
  apply hproduct.congr'
  filter_upwards with i
  exact ((nus i).self_eq_mass_mul_normalize E).symm

/-- Set-level consequence for the moving marked tuple measures.  This is
the precise bridge from Fourier cancellation to torus-cell counts; the
only remaining geometric obligation is that the chosen cell boundary has
zero normalized Haar measure. -/
theorem tendsto_movingSignedMarkedTupleFiniteMeasure_apply_of_fourier
    {r : ℕ} (mu : Measure ℝ) [IsFiniteMeasure mu]
    (N : ℕ → ℕ) (scale : ℕ → ℝ)
    (lower upper : Fin r → ℝ)
    (tuples : ℕ → Finset (Fin r → ℕ))
    (massLimit : ℝ) (hmassLimit : 0 < massLimit)
    (hzero : Tendsto
      (fun n ↦ movingSignedApproximationTupleMassSum
        mu (scale n) lower upper (tuples n))
      atTop (nhds massLimit))
    (hnonzero : ∀ mode : Fin r → ℤ, mode ≠ 0 →
      Tendsto
        (fun n ↦ movingSignedMarkedFourierTupleSum
          mu (N n) (scale n) lower upper mode (tuples n))
        atTop (nhds 0))
    {E : Set (UnitAddTorus (Fin r))}
    (hfrontier :
      unitTorusHaarProbabilityMeasure
        (r := r) (frontier E) = 0) :
    Tendsto
      (fun n ↦ movingSignedMarkedTupleFiniteMeasure
        mu (N n) (scale n) lower upper (tuples n) E)
      atTop
      (nhds (scaledUnitTorusHaarFiniteMeasure
        (r := r) massLimit E)) := by
  apply tendsto_finiteMeasure_apply_of_null_frontier
    (tendsto_movingSignedMarkedTupleFiniteMeasure_of_fourier
      mu N scale lower upper tuples massLimit hzero hnonzero)
  · exact scaledUnitTorusHaarFiniteMeasure_ne_zero hmassLimit
  · rw [scaledUnitTorusHaarFiniteMeasure_normalize hmassLimit]
    exact hfrontier

end

end Erdos1002
