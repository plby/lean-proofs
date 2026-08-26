import ErdosProblems.Erdos1002.UnitTorusContinuityBoxes
import ErdosProblems.Erdos1002.GaussHeterogeneousMovingScaleAggregate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Abstract Fourier criterion for finite measures on a product torus

This module separates the harmonic-analysis closure from the arithmetic
construction of the marked factorial measures.  For any sequence of
positive finite measures on a finite product torus, convergence of the
total masses together with vanishing of every nonzero Fourier coefficient
implies weak convergence to the corresponding multiple of Haar measure.

The result is useful for tagged aggregate tuple families: no individual
canonical-order density limit is required once their sum has been bundled
as one finite measure.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance unitAddCircleMeasureSpaceFourierMeasure :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance unitAddCircleProbabilityFourierMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## Exact integral identities -/

/-- The zero torus character integrates to the total real mass of a finite
measure. -/
theorem integral_unitAddTorus_mFourier_zero_finiteMeasure
    {r : ℕ} (nu : FiniteMeasure (UnitAddTorus (Fin r))) :
    (∫ z, UnitAddTorus.mFourier (fun _ : Fin r ↦ 0) z
      ∂(nu : Measure (UnitAddTorus (Fin r)))) =
      (((nu.mass : NNReal) : ℝ) : ℂ) := by
  have hcharacter :
      UnitAddTorus.mFourier (fun _ : Fin r ↦ 0) = 1 := by
    ext z
    simp [UnitAddTorus.mFourier]
  rw [hcharacter]
  simp only [ContinuousMap.one_apply, MeasureTheory.integral_const,
    Complex.real_smul, mul_one]
  congr 1

/-- Integral of a finite trigonometric polynomial against an arbitrary
finite measure, with every finite-sum interchange explicit. -/
theorem integral_unitTorusTrigPolynomial_finiteMeasure
    {r : ℕ} (nu : FiniteMeasure (UnitAddTorus (Fin r)))
    (p : (Fin r → ℤ) →₀ ℂ) :
    (∫ z, unitTorusTrigPolynomial p z
      ∂(nu : Measure (UnitAddTorus (Fin r)))) =
      p.sum fun mode coefficient ↦ coefficient *
        ∫ z, UnitAddTorus.mFourier mode z ∂(nu : Measure _) := by
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
  · apply Finset.sum_congr rfl
    intro mode _hmode
    change
      (∫ a, p mode * UnitAddTorus.mFourier mode a
        ∂(nu : Measure (UnitAddTorus (Fin r)))) = _
    rw [integral_const_mul]
  · intro mode _hmode
    exact Integrable.of_bound
      ((UnitAddTorus.mFourier mode).continuous.measurable.const_smul
        (p mode)).aestronglyMeasurable ‖p mode‖
      (Eventually.of_forall fun z ↦ by
        change ‖p mode • UnitAddTorus.mFourier mode z‖ ≤ ‖p mode‖
        have hmodeNorm : ‖UnitAddTorus.mFourier mode z‖ = 1 := by
          unfold UnitAddTorus.mFourier
          change ‖∏ i, fourier (mode i) (z i)‖ = 1
          rw [norm_prod]
          simp only [fourier_apply, Circle.norm_coe,
            Finset.prod_const_one]
        rw [norm_smul, hmodeNorm, mul_one])

/-- Haar integration is a norm-one functional for the uniform norm, and
the same estimate for a finite measure has operator norm equal to its
total mass. -/
theorem norm_integral_finiteMeasure_sub_le
    {r : ℕ} (nu : FiniteMeasure (UnitAddTorus (Fin r)))
    (f g : C(UnitAddTorus (Fin r), ℂ)) :
    ‖(∫ z, f z ∂(nu : Measure _)) -
        ∫ z, g z ∂(nu : Measure _)‖ ≤
      ‖f - g‖ * (nu.mass : ℝ) := by
  rw [← integral_sub
    (Integrable.of_bound f.continuous.measurable.aestronglyMeasurable
      ‖f‖ (Eventually.of_forall fun z ↦ f.norm_coe_le_norm z))
    (Integrable.of_bound g.continuous.measurable.aestronglyMeasurable
      ‖g‖ (Eventually.of_forall fun z ↦ g.norm_coe_le_norm z))]
  have h := norm_integral_le_of_norm_le_const
    (μ := (nu : Measure (UnitAddTorus (Fin r))))
    (f := fun z ↦ (f - g) z) (C := ‖f - g‖)
    (Eventually.of_forall fun z ↦ (f - g).norm_coe_le_norm z)
  calc
    ‖∫ (z : UnitAddTorus (Fin r)), (f - g) z ∂(nu : Measure _)‖ ≤
        ‖f - g‖ *
          (nu : Measure (UnitAddTorus (Fin r))).real univ := h
    _ = ‖f - g‖ * (nu.mass : ℝ) := by
      congr 1

/-! ## Fourier convergence -/

/-- Finite Fourier convergence for an arbitrary sequence of finite torus
measures. -/
theorem tendsto_integral_unitTorusTrigPolynomial_of_fourier
    {r : ℕ} (nu : ℕ → FiniteMeasure (UnitAddTorus (Fin r)))
    (massLimit : ℝ)
    (hmass : Tendsto (fun n ↦ ((nu n).mass : ℝ))
      atTop (nhds massLimit))
    (hnonzero : ∀ mode : Fin r → ℤ, mode ≠ 0 →
      Tendsto
        (fun n ↦ ∫ z, UnitAddTorus.mFourier mode z
          ∂(nu n : Measure (UnitAddTorus (Fin r))))
        atTop (nhds 0))
    (p : (Fin r → ℤ) →₀ ℂ) :
    Tendsto
      (fun n ↦ ∫ z, unitTorusTrigPolynomial p z
        ∂(nu n : Measure (UnitAddTorus (Fin r))))
      atTop (nhds (p 0 * (massLimit : ℂ))) := by
  let modeLimit : (Fin r → ℤ) → ℂ := fun mode ↦
    if mode = 0 then (massLimit : ℂ) else 0
  have hmassComplex : Tendsto
      (fun n ↦ (((nu n).mass : ℝ) : ℂ))
      atTop (nhds (massLimit : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hmass
  have hmode : ∀ mode ∈ p.support,
      Tendsto
        (fun n ↦ ∫ z, UnitAddTorus.mFourier mode z
          ∂(nu n : Measure (UnitAddTorus (Fin r))))
        atTop (nhds (modeLimit mode)) := by
    intro mode _hmodeSupport
    by_cases hzero : mode = 0
    · subst mode
      rw [show modeLimit 0 = (massLimit : ℂ) by simp [modeLimit]]
      apply hmassComplex.congr'
      filter_upwards with n
      exact
        (integral_unitAddTorus_mFourier_zero_finiteMeasure
          (nu n)).symm
    · simpa only [modeLimit, if_neg hzero] using!
        hnonzero mode hzero
  have hsum := tendsto_finset_sum p.support fun mode hmodeSupport ↦
    (hmode mode hmodeSupport).const_mul (p mode)
  have hintegral : Tendsto
      (fun n ↦ ∫ z, unitTorusTrigPolynomial p z
        ∂(nu n : Measure (UnitAddTorus (Fin r))))
      atTop
      (nhds (p.sum fun mode coefficient ↦
        coefficient * modeLimit mode)) := by
    apply hsum.congr'
    filter_upwards with n
    exact
      (integral_unitTorusTrigPolynomial_finiteMeasure
        (nu n) p).symm
  have hlimit : p.sum (fun mode coefficient ↦
      coefficient * modeLimit mode) =
      p 0 * (massLimit : ℂ) := by
    classical
    unfold Finsupp.sum
    by_cases hp : 0 ∈ p.support
    · rw [Finset.sum_eq_single 0]
      · simp [modeLimit]
      · intro mode _hmode hmodeNe
        simp [modeLimit, hmodeNe]
      · intro hnot
        exact (hnot hp).elim
    · have hp0 : p 0 = 0 := by
        simpa only [Finsupp.mem_support_iff, not_ne_iff] using! hp
      calc
        ∑ mode ∈ p.support,
            p mode * modeLimit mode = 0 := by
          apply Finset.sum_eq_zero
          intro mode hmodeSupport
          have hmodeNe : mode ≠ 0 := by
            intro hmodeZero
            subst mode
            exact hp hmodeSupport
          simp [modeLimit, hmodeNe]
        _ = p 0 * (massLimit : ℂ) := by simp [hp0]
  rw [hlimit] at hintegral
  exact hintegral

/-- Fourier convergence extends from trigonometric polynomials to every
continuous complex-valued test.  Positivity of the measures supplies the
uniform operator-norm bound: the error made by uniform approximation is
the sup-norm error times the total mass. -/
theorem tendsto_integral_unitTorusContinuous_of_fourier
    {r : ℕ} (nu : ℕ → FiniteMeasure (UnitAddTorus (Fin r)))
    (massLimit : ℝ)
    (hmass : Tendsto (fun n ↦ ((nu n).mass : ℝ))
      atTop (nhds massLimit))
    (hnonzero : ∀ mode : Fin r → ℤ, mode ≠ 0 →
      Tendsto
        (fun n ↦ ∫ z, UnitAddTorus.mFourier mode z
          ∂(nu n : Measure (UnitAddTorus (Fin r))))
        atTop (nhds 0))
    (f : C(UnitAddTorus (Fin r), ℂ)) :
    Tendsto
      (fun n ↦ ∫ z, f z
        ∂(nu n : Measure (UnitAddTorus (Fin r))))
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
    tendsto_integral_unitTorusTrigPolynomial_of_fourier
      nu massLimit hmass hnonzero p
  have htrig : Tendsto
      (fun n ↦ ∫ z, g z
        ∂(nu n : Measure (UnitAddTorus (Fin r))))
      atTop
      (nhds ((massLimit : ℂ) *
        ∫ z : UnitAddTorus (Fin r), g z)) := by
    simpa only [g, integral_unitTorusTrigPolynomial,
      mul_comm] using! htrigRaw
  obtain ⟨nMass, hnMass⟩ :=
    (Metric.tendsto_atTop.mp hmass) 1 zero_lt_one
  obtain ⟨nTrig, hnTrig⟩ :=
    (Metric.tendsto_atTop.mp htrig) (epsilon / 2) (half_pos hepsilon)
  refine ⟨max nMass nTrig, fun n hn ↦ ?_⟩
  have hnMass' : nMass ≤ n := (le_max_left _ _).trans hn
  have hnTrig' : nTrig ≤ n := (le_max_right _ _).trans hn
  let mass : ℝ := ((nu n).mass : ℝ)
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
        (∫ z, f z ∂(nu n : Measure (UnitAddTorus (Fin r))))
        (∫ z, g z ∂(nu n : Measure (UnitAddTorus (Fin r)))) <
        epsilon / 4 := by
    rw [dist_eq_norm]
    calc
      ‖(∫ z, f z ∂(nu n : Measure (UnitAddTorus (Fin r)))) -
          ∫ z, g z ∂(nu n : Measure (UnitAddTorus (Fin r)))‖ ≤
          ‖f - g‖ * mass := by
        simpa only [mass] using!
          norm_integral_finiteMeasure_sub_le (nu n) f g
      _ ≤ ‖f - g‖ * K :=
        mul_le_mul_of_nonneg_left (le_of_lt hmassK) (norm_nonneg _)
      _ = K * ‖f - g‖ := mul_comm _ _
      _ < epsilon / 4 := hKfg
  have hcenter :
      dist
        (∫ z, g z ∂(nu n : Measure (UnitAddTorus (Fin r))))
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
        (∫ z, f z ∂(nu n : Measure (UnitAddTorus (Fin r))))
        ((massLimit : ℂ) *
          ∫ z : UnitAddTorus (Fin r), f z) ≤
        dist
          (∫ z, f z ∂(nu n : Measure (UnitAddTorus (Fin r))))
          (∫ z, g z ∂(nu n : Measure (UnitAddTorus (Fin r)))) +
        dist
          (∫ z, g z ∂(nu n : Measure (UnitAddTorus (Fin r))))
          ((massLimit : ℂ) *
            ∫ z : UnitAddTorus (Fin r), f z) :=
      dist_triangle _ _ _
    _ ≤
        dist
          (∫ z, f z ∂(nu n : Measure (UnitAddTorus (Fin r))))
          (∫ z, g z ∂(nu n : Measure (UnitAddTorus (Fin r)))) +
        (dist
          (∫ z, g z ∂(nu n : Measure (UnitAddTorus (Fin r))))
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

/-- Abstract finite-measure Fourier criterion on a product torus.  It is
deliberately stated for an arbitrary sequence of positive finite measures,
so an arithmetic application may aggregate several tagged tuple families
before proving either the zero-mode asymptotic or nonzero-mode
cancellation. -/
theorem tendsto_finiteMeasure_of_unitTorusFourier
    {r : ℕ} (nu : ℕ → FiniteMeasure (UnitAddTorus (Fin r)))
    (massLimit : ℝ)
    (hmass : Tendsto (fun n ↦ ((nu n).mass : ℝ))
      atTop (nhds massLimit))
    (hnonzero : ∀ mode : Fin r → ℤ, mode ≠ 0 →
      Tendsto
        (fun n ↦ ∫ z, UnitAddTorus.mFourier mode z
          ∂(nu n : Measure (UnitAddTorus (Fin r))))
        atTop (nhds 0)) :
    Tendsto nu atTop
      (nhds (scaledUnitTorusHaarFiniteMeasure
        (r := r) massLimit)) := by
  have hmassNonneg : 0 ≤ massLimit := by
    apply ge_of_tendsto hmass
    filter_upwards with n
    exact NNReal.zero_le_coe
  rw [FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ]
  intro f
  have hcontinuous :=
    tendsto_integral_unitTorusContinuous_of_fourier
      nu massLimit hmass hnonzero f.toContinuousMap
  convert! hcontinuous using 1
  congr 1
  change
    (∫ z, f.toContinuousMap z
      ∂(scaledUnitTorusHaarFiniteMeasure (r := r) massLimit :
        Measure (UnitAddTorus (Fin r)))) = _
  rw [integral_scaledUnitTorusHaarFiniteMeasure
    massLimit hmassNonneg]

/-- Continuity-set consequence of the abstract Fourier criterion.  The
strict positivity hypothesis is used only to normalize the limiting finite
measure when invoking Portmanteau. -/
theorem tendsto_finiteMeasure_apply_of_unitTorusFourier
    {r : ℕ} (nu : ℕ → FiniteMeasure (UnitAddTorus (Fin r)))
    (massLimit : ℝ) (hmassLimit : 0 < massLimit)
    (hmass : Tendsto (fun n ↦ ((nu n).mass : ℝ))
      atTop (nhds massLimit))
    (hnonzero : ∀ mode : Fin r → ℤ, mode ≠ 0 →
      Tendsto
        (fun n ↦ ∫ z, UnitAddTorus.mFourier mode z
          ∂(nu n : Measure (UnitAddTorus (Fin r))))
        atTop (nhds 0))
    {E : Set (UnitAddTorus (Fin r))}
    (hfrontier : unitTorusHaarProbabilityMeasure
      (r := r) (frontier E) = 0) :
    Tendsto (fun n ↦ nu n E) atTop
      (nhds (scaledUnitTorusHaarFiniteMeasure
        (r := r) massLimit E)) := by
  apply tendsto_finiteMeasure_apply_of_null_frontier
    (tendsto_finiteMeasure_of_unitTorusFourier
      nu massLimit hmass hnonzero)
  · exact scaledUnitTorusHaarFiniteMeasure_ne_zero hmassLimit
  · rw [scaledUnitTorusHaarFiniteMeasure_normalize hmassLimit]
    exact hfrontier

/-- Fully concrete version for a product of half-open torus arcs. -/
theorem tendsto_finiteMeasure_halfOpenBox_of_unitTorusFourier
    {r : ℕ} (nu : ℕ → FiniteMeasure (UnitAddTorus (Fin r)))
    (massLimit : ℝ) (hmassLimit : 0 < massLimit)
    (hmass : Tendsto (fun n ↦ ((nu n).mass : ℝ))
      atTop (nhds massLimit))
    (hnonzero : ∀ mode : Fin r → ℤ, mode ≠ 0 →
      Tendsto
        (fun n ↦ ∫ z, UnitAddTorus.mFourier mode z
          ∂(nu n : Measure (UnitAddTorus (Fin r))))
        atTop (nhds 0))
    (torusLower torusUpper : Fin r → ℝ) :
    Tendsto
      (fun n ↦ nu n
        (unitTorusHalfOpenBox torusLower torusUpper))
      atTop
      (nhds (scaledUnitTorusHaarFiniteMeasure
        (r := r) massLimit
          (unitTorusHalfOpenBox torusLower torusUpper))) := by
  exact tendsto_finiteMeasure_apply_of_unitTorusFourier
    nu massLimit hmassLimit hmass hnonzero
      (unitTorusHaarProbabilityMeasure_frontier_halfOpenBox
        torusLower torusUpper)

/-! ## Exact tagged-aggregate bookkeeping -/

/-- A quotient-torus Fourier character evaluated at the literal marked
point is exactly the real-representative character used in the arithmetic
Fourier sum. -/
theorem unitAddTorus_mFourier_gaussMovingUnitTorusPoint
    {r : ℕ} (N : ℕ) (mode : Fin r → ℤ)
    (times : Fin r → ℕ) (x : ℝ) :
    UnitAddTorus.mFourier mode
        (gaussMovingUnitTorusPoint N times x) =
      gaussMovingMarkedTupleCharacter N mode times x := by
  classical
  unfold UnitAddTorus.mFourier gaussMovingUnitTorusPoint
    gaussMovingMarkedTupleCharacter
  change (∏ i, fourier (mode i)
      (gaussSelectedPrefixTorusMark N (times i) x : UnitAddCircle)) =
    ∏ i, paperExp ((mode i : ℝ) *
      gaussSelectedPrefixTorusMark N (times i) x)
  apply Finset.prod_congr rfl
  intro i _hi
  rw [fourier_coe_apply]
  unfold paperExp
  congr 1
  push_cast
  ring

/-- The Fourier coefficient of the literal positive marked tuple measure
is exactly the arithmetic marked Fourier tuple sum. -/
theorem integral_movingSignedMarkedTupleFiniteMeasure_mFourier
    {r : ℕ} (mu : Measure ℝ) [IsFiniteMeasure mu]
    (N : ℕ) (scale : ℝ) (lower upper : Fin r → ℝ)
    (mode : Fin r → ℤ)
    (tuples : Finset (Fin r → ℕ)) :
    (∫ z, UnitAddTorus.mFourier mode z
      ∂(movingSignedMarkedTupleFiniteMeasure
        mu N scale lower upper tuples :
          Measure (UnitAddTorus (Fin r)))) =
      movingSignedMarkedFourierTupleSum
        mu N scale lower upper mode tuples := by
  rw [integral_movingSignedMarkedTupleFiniteMeasure]
  classical
  unfold movingSignedMarkedContinuousTupleSum
    movingSignedMarkedFourierTupleSum
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
      (fun y ↦ UnitAddTorus.mFourier mode
        (gaussMovingUnitTorusPoint N times y)) x =
    E.indicator
      (gaussMovingMarkedTupleCharacter N mode times) x
  by_cases hx : x ∈ E
  · simp only [Set.indicator_of_mem hx]
    exact unitAddTorus_mFourier_gaussMovingUnitTorusPoint
      N mode times x
  · simp only [Set.indicator_of_notMem hx]

/-- The real mass of the literal marked tuple measure is exactly its
unmarked tuple mass. -/
theorem movingSignedMarkedTupleFiniteMeasure_real_mass
    {r : ℕ} (mu : Measure ℝ) [IsFiniteMeasure mu]
    (N : ℕ) (scale : ℝ) (lower upper : Fin r → ℝ)
    (tuples : Finset (Fin r → ℕ)) :
    ((movingSignedMarkedTupleFiniteMeasure
        mu N scale lower upper tuples).mass : ℝ) =
      movingSignedApproximationTupleMassSum
        mu scale lower upper tuples := by
  apply Complex.ofReal_injective
  calc
    ((((movingSignedMarkedTupleFiniteMeasure
          mu N scale lower upper tuples).mass : NNReal) : ℝ) : ℂ) =
        ∫ z, UnitAddTorus.mFourier (fun _ : Fin r ↦ 0) z
          ∂(movingSignedMarkedTupleFiniteMeasure
            mu N scale lower upper tuples :
              Measure (UnitAddTorus (Fin r))) :=
      (integral_unitAddTorus_mFourier_zero_finiteMeasure
        (movingSignedMarkedTupleFiniteMeasure
          mu N scale lower upper tuples)).symm
    _ = movingSignedMarkedFourierTupleSum
          mu N scale lower upper (fun _ : Fin r ↦ 0) tuples :=
      integral_movingSignedMarkedTupleFiniteMeasure_mFourier
        mu N scale lower upper (fun _ : Fin r ↦ 0) tuples
    _ = (movingSignedApproximationTupleMassSum
          mu scale lower upper tuples : ℂ) :=
      movingSignedMarkedFourierTupleSum_zero
        mu N scale lower upper tuples

/-- The positive marked measure obtained by summing a finite tagged
family over an arbitrary finite base measure. -/
def aggregateMovingSignedMarkedTupleFiniteMeasure
    {r : ℕ} {β : Type*} [Fintype β]
    (mu : Measure ℝ) [IsFiniteMeasure mu]
    (N : ℕ) (scale : ℝ)
    (signedLower signedUpper : β → Fin r → ℝ)
    (tuples : β → Finset (Fin r → ℕ)) :
    FiniteMeasure (UnitAddTorus (Fin r)) := by
  classical
  exact ∑ b, movingSignedMarkedTupleFiniteMeasure
    mu N scale (signedLower b) (signedUpper b) (tuples b)

/-- Tagged aggregate of the arithmetic marked Fourier coefficients over
an arbitrary finite base measure. -/
def aggregateMovingSignedMarkedFourierTupleSum
    {r : ℕ} {β : Type*} [Fintype β]
    (mu : Measure ℝ) [IsFiniteMeasure mu]
    (N : ℕ) (scale : ℝ)
    (signedLower signedUpper : β → Fin r → ℝ)
    (mode : Fin r → ℤ)
    (tuples : β → Finset (Fin r → ℕ)) : ℂ :=
  ∑ b, movingSignedMarkedFourierTupleSum
    mu N scale (signedLower b) (signedUpper b) mode (tuples b)

/-- Tagged aggregate of the unmarked tuple masses over an arbitrary
finite base measure. -/
def aggregateMovingSignedApproximationTupleMassSum
    {r : ℕ} {β : Type*} [Fintype β]
    (mu : Measure ℝ) [IsFiniteMeasure mu]
    (scale : ℝ)
    (signedLower signedUpper : β → Fin r → ℝ)
    (tuples : β → Finset (Fin r → ℕ)) : ℝ :=
  ∑ b, movingSignedApproximationTupleMassSum
    mu scale (signedLower b) (signedUpper b) (tuples b)

@[simp] theorem aggregateMovingSignedMarkedFourierTupleSum_zero
    {r : ℕ} {β : Type*} [Fintype β]
    (mu : Measure ℝ) [IsFiniteMeasure mu]
    (N : ℕ) (scale : ℝ)
    (signedLower signedUpper : β → Fin r → ℝ)
    (tuples : β → Finset (Fin r → ℕ)) :
    aggregateMovingSignedMarkedFourierTupleSum
        mu N scale signedLower signedUpper
          (fun _i : Fin r ↦ 0) tuples =
      (aggregateMovingSignedApproximationTupleMassSum
        mu scale signedLower signedUpper tuples : ℂ) := by
  unfold aggregateMovingSignedMarkedFourierTupleSum
    aggregateMovingSignedApproximationTupleMassSum
  simp only [movingSignedMarkedFourierTupleSum_zero,
    Complex.ofReal_sum]

theorem integral_aggregateMovingSignedMarkedTupleFiniteMeasure_mFourier
    {r : ℕ} {β : Type*} [Fintype β]
    (mu : Measure ℝ) [IsFiniteMeasure mu]
    (N : ℕ) (scale : ℝ)
    (signedLower signedUpper : β → Fin r → ℝ)
    (mode : Fin r → ℤ)
    (tuples : β → Finset (Fin r → ℕ)) :
    (∫ z, UnitAddTorus.mFourier mode z
      ∂(aggregateMovingSignedMarkedTupleFiniteMeasure
        mu N scale signedLower signedUpper tuples :
          Measure (UnitAddTorus (Fin r)))) =
      aggregateMovingSignedMarkedFourierTupleSum
        mu N scale signedLower signedUpper mode tuples := by
  classical
  unfold aggregateMovingSignedMarkedTupleFiniteMeasure
    aggregateMovingSignedMarkedFourierTupleSum
  rw [FiniteMeasure.toMeasure_sum,
    MeasureTheory.integral_finset_sum_measure]
  · apply Finset.sum_congr rfl
    intro b _hb
    exact integral_movingSignedMarkedTupleFiniteMeasure_mFourier
      mu N scale (signedLower b) (signedUpper b) mode (tuples b)
  · intro b _hb
    exact Integrable.of_bound
      (UnitAddTorus.mFourier mode).continuous.measurable.aestronglyMeasurable
      1 (Eventually.of_forall fun z ↦ by
        have hz := (UnitAddTorus.mFourier mode).norm_coe_le_norm z
        simpa only [UnitAddTorus.mFourier_norm] using! hz)

theorem aggregateMovingSignedMarkedTupleFiniteMeasure_real_mass
    {r : ℕ} {β : Type*} [Fintype β]
    (mu : Measure ℝ) [IsFiniteMeasure mu]
    (N : ℕ) (scale : ℝ)
    (signedLower signedUpper : β → Fin r → ℝ)
    (tuples : β → Finset (Fin r → ℕ)) :
    ((aggregateMovingSignedMarkedTupleFiniteMeasure
        mu N scale signedLower signedUpper tuples).mass : ℝ) =
      aggregateMovingSignedApproximationTupleMassSum
        mu scale signedLower signedUpper tuples := by
  apply Complex.ofReal_injective
  calc
    ((((aggregateMovingSignedMarkedTupleFiniteMeasure
          mu N scale signedLower signedUpper tuples).mass : NNReal) : ℝ) : ℂ) =
        ∫ z, UnitAddTorus.mFourier (fun _ : Fin r ↦ 0) z
          ∂(aggregateMovingSignedMarkedTupleFiniteMeasure
            mu N scale signedLower signedUpper tuples :
              Measure (UnitAddTorus (Fin r))) :=
      (integral_unitAddTorus_mFourier_zero_finiteMeasure
        (aggregateMovingSignedMarkedTupleFiniteMeasure
          mu N scale signedLower signedUpper tuples)).symm
    _ = aggregateMovingSignedMarkedFourierTupleSum
          mu N scale signedLower signedUpper
            (fun _ : Fin r ↦ 0) tuples :=
      integral_aggregateMovingSignedMarkedTupleFiniteMeasure_mFourier
        mu N scale signedLower signedUpper
          (fun _ : Fin r ↦ 0) tuples
    _ = (aggregateMovingSignedApproximationTupleMassSum
          mu scale signedLower signedUpper tuples : ℂ) :=
      aggregateMovingSignedMarkedFourierTupleSum_zero
        mu N scale signedLower signedUpper tuples

/-- Weak convergence for a tagged family over an arbitrary finite base
measure.  In particular this statement may be instantiated with
`uniform01Measure`; a Gauss-measure zero mode is not silently substituted
for the literal Lebesgue factorial moment. -/
theorem tendsto_aggregateMovingSignedMarkedTupleFiniteMeasure_of_fourier
    {r : ℕ} {β : Type*} [Fintype β]
    (mu : Measure ℝ) [IsFiniteMeasure mu]
    (N : ℕ → ℕ) (scale : ℕ → ℝ)
    (signedLower signedUpper : β → Fin r → ℝ)
    (tuples : ℕ → β → Finset (Fin r → ℕ))
    (massLimit : ℝ)
    (hmass : Tendsto
      (fun n ↦ aggregateMovingSignedApproximationTupleMassSum
        mu (scale n) signedLower signedUpper (tuples n))
      atTop (nhds massLimit))
    (hnonzero : ∀ mode : Fin r → ℤ, mode ≠ 0 →
      Tendsto
        (fun n ↦ aggregateMovingSignedMarkedFourierTupleSum
          mu (N n) (scale n) signedLower signedUpper mode (tuples n))
        atTop (nhds 0)) :
    Tendsto
      (fun n ↦ aggregateMovingSignedMarkedTupleFiniteMeasure
        mu (N n) (scale n) signedLower signedUpper (tuples n))
      atTop
      (nhds (scaledUnitTorusHaarFiniteMeasure
        (r := r) massLimit)) := by
  apply tendsto_finiteMeasure_of_unitTorusFourier
  · apply hmass.congr'
    filter_upwards with n
    exact (aggregateMovingSignedMarkedTupleFiniteMeasure_real_mass
      mu (N n) (scale n) signedLower signedUpper (tuples n)).symm
  · intro mode hmode
    apply (hnonzero mode hmode).congr'
    filter_upwards with n
    exact
      (integral_aggregateMovingSignedMarkedTupleFiniteMeasure_mFourier
        mu (N n) (scale n) signedLower signedUpper mode (tuples n)).symm

/-- Half-open torus-cell version over an arbitrary finite base measure. -/
theorem
    tendsto_aggregateMovingSignedMarkedTupleFiniteMeasure_halfOpenBox_of_fourier
    {r : ℕ} {β : Type*} [Fintype β]
    (mu : Measure ℝ) [IsFiniteMeasure mu]
    (N : ℕ → ℕ) (scale : ℕ → ℝ)
    (signedLower signedUpper : β → Fin r → ℝ)
    (tuples : ℕ → β → Finset (Fin r → ℕ))
    (massLimit : ℝ) (hmassLimit : 0 < massLimit)
    (hmass : Tendsto
      (fun n ↦ aggregateMovingSignedApproximationTupleMassSum
        mu (scale n) signedLower signedUpper (tuples n))
      atTop (nhds massLimit))
    (hnonzero : ∀ mode : Fin r → ℤ, mode ≠ 0 →
      Tendsto
        (fun n ↦ aggregateMovingSignedMarkedFourierTupleSum
          mu (N n) (scale n) signedLower signedUpper mode (tuples n))
        atTop (nhds 0))
    (torusLower torusUpper : Fin r → ℝ) :
    Tendsto
      (fun n ↦ aggregateMovingSignedMarkedTupleFiniteMeasure
        mu (N n) (scale n) signedLower signedUpper (tuples n)
          (unitTorusHalfOpenBox torusLower torusUpper))
      atTop
      (nhds (scaledUnitTorusHaarFiniteMeasure
        (r := r) massLimit
          (unitTorusHalfOpenBox torusLower torusUpper))) := by
  apply tendsto_finiteMeasure_apply_of_null_frontier
    (tendsto_aggregateMovingSignedMarkedTupleFiniteMeasure_of_fourier
      mu N scale signedLower signedUpper tuples massLimit hmass hnonzero)
  · exact scaledUnitTorusHaarFiniteMeasure_ne_zero hmassLimit
  · rw [scaledUnitTorusHaarFiniteMeasure_normalize hmassLimit]
    exact unitTorusHaarProbabilityMeasure_frontier_halfOpenBox
      torusLower torusUpper

/-- Positive marked tuple measures summed over a finite tag type.  The
tag remains present in the sum, so equal tuples in different canonical
order classes retain their intended multiplicity. -/
def aggregateGaussMovingSignedMarkedTupleFiniteMeasure
    {r : ℕ} {β : Type*} [Fintype β]
    (N : ℕ) (scale : ℝ)
    (signedLower signedUpper : β → Fin r → ℝ)
    (tuples : β → Finset (Fin r → ℕ)) :
    FiniteMeasure (UnitAddTorus (Fin r)) := by
  classical
  exact ∑ b, movingSignedMarkedTupleFiniteMeasure
    gaussMeasure N scale (signedLower b) (signedUpper b) (tuples b)

theorem aggregateGaussMovingSignedMarkedTupleFiniteMeasure_eq_generic
    {r : ℕ} {β : Type*} [Fintype β]
    (N : ℕ) (scale : ℝ)
    (signedLower signedUpper : β → Fin r → ℝ)
    (tuples : β → Finset (Fin r → ℕ)) :
    aggregateGaussMovingSignedMarkedTupleFiniteMeasure
        N scale signedLower signedUpper tuples =
      aggregateMovingSignedMarkedTupleFiniteMeasure
        gaussMeasure N scale signedLower signedUpper tuples := by
  rfl

theorem aggregateMovingSignedMarkedFourierTupleSum_gauss
    {r : ℕ} {β : Type*} [Fintype β]
    (N : ℕ) (scale : ℝ)
    (signedLower signedUpper : β → Fin r → ℝ)
    (mode : Fin r → ℤ)
    (tuples : β → Finset (Fin r → ℕ)) :
    aggregateMovingSignedMarkedFourierTupleSum
        gaussMeasure N scale signedLower signedUpper mode tuples =
      aggregateGaussMovingSignedMarkedFourierTupleSum
        N scale signedLower signedUpper (fun _b ↦ mode) tuples := by
  rfl

theorem aggregateMovingSignedApproximationTupleMassSum_gauss
    {r : ℕ} {β : Type*} [Fintype β]
    (scale : ℝ)
    (signedLower signedUpper : β → Fin r → ℝ)
    (tuples : β → Finset (Fin r → ℕ)) :
    aggregateMovingSignedApproximationTupleMassSum
        gaussMeasure scale signedLower signedUpper tuples =
      aggregateGaussMovingSignedApproximationTupleSum
        scale signedLower signedUpper tuples := by
  rfl

/-- Literal Lebesgue/uniform specialization of the tagged marked measure. -/
def aggregateUniformMovingSignedMarkedTupleFiniteMeasure
    {r : ℕ} {β : Type*} [Fintype β]
    (N : ℕ) (scale : ℝ)
    (signedLower signedUpper : β → Fin r → ℝ)
    (tuples : β → Finset (Fin r → ℕ)) :
    FiniteMeasure (UnitAddTorus (Fin r)) :=
  aggregateMovingSignedMarkedTupleFiniteMeasure
    uniform01Measure N scale signedLower signedUpper tuples

/-- Literal Lebesgue/uniform specialization of the aggregate Fourier
coefficient. -/
def aggregateUniformMovingSignedMarkedFourierTupleSum
    {r : ℕ} {β : Type*} [Fintype β]
    (N : ℕ) (scale : ℝ)
    (signedLower signedUpper : β → Fin r → ℝ)
    (mode : Fin r → ℤ)
    (tuples : β → Finset (Fin r → ℕ)) : ℂ :=
  aggregateMovingSignedMarkedFourierTupleSum
    uniform01Measure N scale signedLower signedUpper mode tuples

/-- Literal Lebesgue/uniform specialization of the aggregate zero-mode
mass. -/
def aggregateUniformMovingSignedApproximationTupleMassSum
    {r : ℕ} {β : Type*} [Fintype β]
    (scale : ℝ)
    (signedLower signedUpper : β → Fin r → ℝ)
    (tuples : β → Finset (Fin r → ℕ)) : ℝ :=
  aggregateMovingSignedApproximationTupleMassSum
    uniform01Measure scale signedLower signedUpper tuples

theorem aggregateUniformMovingSignedMarkedTupleFiniteMeasure_real_mass
    {r : ℕ} {β : Type*} [Fintype β]
    (N : ℕ) (scale : ℝ)
    (signedLower signedUpper : β → Fin r → ℝ)
    (tuples : β → Finset (Fin r → ℕ)) :
    ((aggregateUniformMovingSignedMarkedTupleFiniteMeasure
        N scale signedLower signedUpper tuples).mass : ℝ) =
      aggregateUniformMovingSignedApproximationTupleMassSum
        scale signedLower signedUpper tuples := by
  exact aggregateMovingSignedMarkedTupleFiniteMeasure_real_mass
    uniform01Measure N scale signedLower signedUpper tuples

theorem
    integral_aggregateUniformMovingSignedMarkedTupleFiniteMeasure_mFourier
    {r : ℕ} {β : Type*} [Fintype β]
    (N : ℕ) (scale : ℝ)
    (signedLower signedUpper : β → Fin r → ℝ)
    (mode : Fin r → ℤ)
    (tuples : β → Finset (Fin r → ℕ)) :
    (∫ z, UnitAddTorus.mFourier mode z
      ∂(aggregateUniformMovingSignedMarkedTupleFiniteMeasure
        N scale signedLower signedUpper tuples :
          Measure (UnitAddTorus (Fin r)))) =
      aggregateUniformMovingSignedMarkedFourierTupleSum
        N scale signedLower signedUpper mode tuples := by
  exact integral_aggregateMovingSignedMarkedTupleFiniteMeasure_mFourier
    uniform01Measure N scale signedLower signedUpper mode tuples

/-- Fourier integration commutes with the finite tagged aggregate and is
exactly the aggregate arithmetic coefficient with a common torus mode. -/
theorem
    integral_aggregateGaussMovingSignedMarkedTupleFiniteMeasure_mFourier
    {r : ℕ} {β : Type*} [Fintype β]
    (N : ℕ) (scale : ℝ)
    (signedLower signedUpper : β → Fin r → ℝ)
    (mode : Fin r → ℤ)
    (tuples : β → Finset (Fin r → ℕ)) :
    (∫ z, UnitAddTorus.mFourier mode z
      ∂(aggregateGaussMovingSignedMarkedTupleFiniteMeasure
        N scale signedLower signedUpper tuples :
          Measure (UnitAddTorus (Fin r)))) =
      aggregateGaussMovingSignedMarkedFourierTupleSum
        N scale signedLower signedUpper (fun _b ↦ mode) tuples := by
  classical
  unfold aggregateGaussMovingSignedMarkedTupleFiniteMeasure
    aggregateGaussMovingSignedMarkedFourierTupleSum
    gaussMovingSignedMarkedFourierTupleSum
  rw [FiniteMeasure.toMeasure_sum,
    MeasureTheory.integral_finset_sum_measure]
  · apply Finset.sum_congr rfl
    intro b _hb
    exact integral_movingSignedMarkedTupleFiniteMeasure_mFourier
      gaussMeasure N scale (signedLower b) (signedUpper b)
        mode (tuples b)
  · intro b _hb
    exact Integrable.of_bound
      (UnitAddTorus.mFourier mode).continuous.measurable.aestronglyMeasurable
      1 (Eventually.of_forall fun z ↦ by
        have hz := (UnitAddTorus.mFourier mode).norm_coe_le_norm z
        simpa only [UnitAddTorus.mFourier_norm] using! hz)

/-- The total real mass of the tagged positive measure is the exact
aggregate zero-mode mass, with tags and multiplicities preserved. -/
theorem aggregateGaussMovingSignedMarkedTupleFiniteMeasure_real_mass
    {r : ℕ} {β : Type*} [Fintype β]
    (N : ℕ) (scale : ℝ)
    (signedLower signedUpper : β → Fin r → ℝ)
    (tuples : β → Finset (Fin r → ℕ)) :
    ((aggregateGaussMovingSignedMarkedTupleFiniteMeasure
        N scale signedLower signedUpper tuples).mass : ℝ) =
      aggregateGaussMovingSignedApproximationTupleSum
        scale signedLower signedUpper tuples := by
  apply Complex.ofReal_injective
  calc
    ((((aggregateGaussMovingSignedMarkedTupleFiniteMeasure
          N scale signedLower signedUpper tuples).mass : NNReal) : ℝ) : ℂ) =
        ∫ z, UnitAddTorus.mFourier (fun _ : Fin r ↦ 0) z
          ∂(aggregateGaussMovingSignedMarkedTupleFiniteMeasure
            N scale signedLower signedUpper tuples :
              Measure (UnitAddTorus (Fin r))) :=
      (integral_unitAddTorus_mFourier_zero_finiteMeasure
        (aggregateGaussMovingSignedMarkedTupleFiniteMeasure
          N scale signedLower signedUpper tuples)).symm
    _ = aggregateGaussMovingSignedMarkedFourierTupleSum
          N scale signedLower signedUpper
            (fun _b _i ↦ 0) tuples :=
      integral_aggregateGaussMovingSignedMarkedTupleFiniteMeasure_mFourier
        N scale signedLower signedUpper
          (fun _ : Fin r ↦ 0) tuples
    _ = (aggregateGaussMovingSignedApproximationTupleSum
          scale signedLower signedUpper tuples : ℂ) :=
      aggregateGaussMovingSignedMarkedFourierTupleSum_zero
        N scale signedLower signedUpper tuples

/-- Aggregate-safe weak convergence theorem.  Both the mass hypothesis
and every Fourier hypothesis are imposed only after summing over tags. -/
theorem
    tendsto_aggregateGaussMovingSignedMarkedTupleFiniteMeasure_of_fourier
    {r : ℕ} {β : Type*} [Fintype β]
    (N : ℕ → ℕ) (scale : ℕ → ℝ)
    (signedLower signedUpper : β → Fin r → ℝ)
    (tuples : ℕ → β → Finset (Fin r → ℕ))
    (massLimit : ℝ)
    (hmass : Tendsto
      (fun n ↦ aggregateGaussMovingSignedApproximationTupleSum
        (scale n) signedLower signedUpper (tuples n))
      atTop (nhds massLimit))
    (hnonzero : ∀ mode : Fin r → ℤ, mode ≠ 0 →
      Tendsto
        (fun n ↦ aggregateGaussMovingSignedMarkedFourierTupleSum
          (N n) (scale n) signedLower signedUpper
            (fun _b ↦ mode) (tuples n))
        atTop (nhds 0)) :
    Tendsto
      (fun n ↦ aggregateGaussMovingSignedMarkedTupleFiniteMeasure
        (N n) (scale n) signedLower signedUpper (tuples n))
      atTop
      (nhds (scaledUnitTorusHaarFiniteMeasure
        (r := r) massLimit)) := by
  apply tendsto_finiteMeasure_of_unitTorusFourier
  · apply hmass.congr'
    filter_upwards with n
    exact (aggregateGaussMovingSignedMarkedTupleFiniteMeasure_real_mass
      (N n) (scale n) signedLower signedUpper (tuples n)).symm
  · intro mode hmode
    apply (hnonzero mode hmode).congr'
    filter_upwards with n
    exact
      (integral_aggregateGaussMovingSignedMarkedTupleFiniteMeasure_mFourier
        (N n) (scale n) signedLower signedUpper mode (tuples n)).symm

/-- Concrete half-open torus-cell consequence of the aggregate-safe
criterion. -/
theorem
    tendsto_aggregateGaussMovingSignedMarkedTupleFiniteMeasure_halfOpenBox_of_fourier
    {r : ℕ} {β : Type*} [Fintype β]
    (N : ℕ → ℕ) (scale : ℕ → ℝ)
    (signedLower signedUpper : β → Fin r → ℝ)
    (tuples : ℕ → β → Finset (Fin r → ℕ))
    (massLimit : ℝ) (hmassLimit : 0 < massLimit)
    (hmass : Tendsto
      (fun n ↦ aggregateGaussMovingSignedApproximationTupleSum
        (scale n) signedLower signedUpper (tuples n))
      atTop (nhds massLimit))
    (hnonzero : ∀ mode : Fin r → ℤ, mode ≠ 0 →
      Tendsto
        (fun n ↦ aggregateGaussMovingSignedMarkedFourierTupleSum
          (N n) (scale n) signedLower signedUpper
            (fun _b ↦ mode) (tuples n))
        atTop (nhds 0))
    (torusLower torusUpper : Fin r → ℝ) :
    Tendsto
      (fun n ↦ aggregateGaussMovingSignedMarkedTupleFiniteMeasure
        (N n) (scale n) signedLower signedUpper (tuples n)
          (unitTorusHalfOpenBox torusLower torusUpper))
      atTop
      (nhds (scaledUnitTorusHaarFiniteMeasure
        (r := r) massLimit
          (unitTorusHalfOpenBox torusLower torusUpper))) := by
  apply tendsto_finiteMeasure_apply_of_null_frontier
    (tendsto_aggregateGaussMovingSignedMarkedTupleFiniteMeasure_of_fourier
      N scale signedLower signedUpper tuples massLimit hmass hnonzero)
  · exact scaledUnitTorusHaarFiniteMeasure_ne_zero hmassLimit
  · rw [scaledUnitTorusHaarFiniteMeasure_normalize hmassLimit]
    exact unitTorusHaarProbabilityMeasure_frontier_halfOpenBox
      torusLower torusUpper

end

end Erdos1002
