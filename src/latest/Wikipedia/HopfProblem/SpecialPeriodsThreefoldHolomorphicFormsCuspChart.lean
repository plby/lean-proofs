import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspGeometry
import Wikipedia.HopfProblem.HolomorphicDifferentialFormsFlat

/-!
# The actual reference toric parametrization at the filled cusp

The reference affine chart is restricted to the original toric tube and
then mapped through the actual cusp quotient into the glued threefold.
The original monomial parameter is exactly the global cusp coordinate.
The three transverse axes extend across parameter zero in this same
native open-subset atlas.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp

open ToricCharts ToricFan HolomorphicDifferentialForms

local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] CuspGeometry.nativeChartedSpace Threefold.chartedSpace
  Threefold.space_isManifold

/-- The full reference-chart part of the actual chosen toric tube. -/
def referenceDomain : TopologicalSpace.Opens (CoordinateSpace 3) :=
  ⟨{w | ‖Triangle.time w‖ < CuspGeometry.data.radius},
    isOpen_lt Triangle.time_holomorphic.continuous.norm continuous_const⟩

@[simp] theorem mem_referenceDomain (w : CoordinateSpace 3) :
    w ∈ referenceDomain ↔ ‖Triangle.time w‖ < CuspGeometry.data.radius := Iff.rfl

/-- The unchanged inherited chart of this open subset is independent of its center. -/
theorem reference_chart_eq (x y : referenceDomain) :
    chartAt (CoordinateSpace 3) x = chartAt (CoordinateSpace 3) y := rfl

@[simp] theorem reference_chart_apply (x y : referenceDomain) :
    chartAt (CoordinateSpace 3) x y = (y : CoordinateSpace 3) := rfl

/-- The actual reference toric inclusion, codrestricted to the chosen open tube. -/
def referenceLift (w : referenceDomain) :
    ToricSpace.Tube (CuspQuotient.disc CuspGeometry.data.radius) :=
  ⟨ToricSpace.inclusion ToricSpace.referenceTriangle w, by
    change ToricSpace.time (ToricSpace.inclusion ToricSpace.referenceTriangle w) ∈
      Metric.ball 0 CuspGeometry.data.radius
    rw [ToricSpace.time_inclusion, Metric.mem_ball, dist_zero_right]
    exact w.property⟩

@[simp] theorem referenceLift_val (w : referenceDomain) :
    (referenceLift w : ToricSpace.Space) =
      ToricSpace.inclusion ToricSpace.referenceTriangle w := rfl

theorem referenceLift_holomorphic : ContMDiff I₃ I₃ ω referenceLift := by
  intro w
  have he : ContMDiffAt I₃ I₃ ω
      (fun v : referenceDomain => (referenceLift v : ToricSpace.Space)) w ↔
        ContMDiffAt I₃ I₃ ω referenceLift w :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (((ToricSpace.inclusion_holomorphic ToricSpace.referenceTriangle).comp
    contMDiff_subtype_val) w)

/-- The reference toric coordinates mapped to the full original cusp quotient. -/
def referenceQuotient : referenceDomain → CuspGeometry.LocalSpace :=
  CuspQuotient.quotientMap CuspGeometry.data.correction CuspGeometry.data.radius ∘ referenceLift

theorem referenceQuotient_holomorphic : ContMDiff I₃ I₃ ω referenceQuotient := by
  let := CuspQuotient.chartedSpace CuspGeometry.data.correction CuspGeometry.data.radius
    CuspGeometry.data.radius_pos CuspGeometry.data.radius_lt_one
    CuspGeometry.data.holomorphic CuspGeometry.data.smallDrift
  have hq : ContMDiff I₃ I₃ ω
      (CuspQuotient.quotientMap CuspGeometry.data.correction CuspGeometry.data.radius :
        ToricSpace.Tube (CuspQuotient.disc CuspGeometry.data.radius) → CuspGeometry.LocalSpace) :=
    CuspQuotient.quotientMap_holomorphic CuspGeometry.data.correction CuspGeometry.data.radius
      CuspGeometry.data.radius_pos CuspGeometry.data.radius_lt_one
      CuspGeometry.data.holomorphic CuspGeometry.data.smallDrift
  exact hq.comp referenceLift_holomorphic

/-- The actual map into the unchanged glued threefold, including the central fibre. -/
def referenceMap : referenceDomain → Threefold.Space :=
  CuspGeometry.inclusion ∘ referenceQuotient

theorem referenceMap_holomorphic : ContMDiff I₃ IF ω referenceMap :=
  CuspGeometry.inclusion_holomorphic.comp referenceQuotient_holomorphic

theorem referenceMap_continuous : Continuous referenceMap := referenceMap_holomorphic.continuous

@[simp] theorem parameter_referenceQuotient (w : referenceDomain) :
    CuspGeometry.parameter (referenceQuotient w) = Triangle.time w :=
  ToricSpace.time_inclusion ToricSpace.referenceTriangle w

/-- The global cusp coordinate is literally the native three-coordinate monomial. -/
@[simp] theorem cuspCoordinate_referenceMap (w : referenceDomain) :
    CuspGeometry.cuspCoordinate (referenceMap w) = Triangle.time w := by
  change CuspGeometry.cuspCoordinate (CuspGeometry.inclusion (referenceQuotient w)) = _
  rw [CuspGeometry.cuspCoordinate_inclusion, parameter_referenceQuotient]

@[simp] theorem sphereChart_projectionSphere_referenceMap (w : referenceDomain) :
    CuspGeometry.sphereChart (Threefold.projectionSphere (referenceMap w)) = Triangle.time w := by
  rw [CuspGeometry.sphereChart_projectionSphere, cuspCoordinate_referenceMap]

/-- The transverse coordinate axis with its other two coordinates fixed at one. -/
def axis (k : Fin 3) (q : ℂ) : CoordinateSpace 3 := fun j => if j = k then q else 1

@[simp] theorem axis_apply_same (k : Fin 3) (q : ℂ) : axis k q k = q := by simp [axis]

theorem axis_apply_ne (k j : Fin 3) (q : ℂ) (h : j ≠ k) : axis k q j = 1 := by
  simp [axis, h]

@[simp] theorem time_axis (k : Fin 3) (q : ℂ) : Triangle.time (axis k q) = q := by
  fin_cases k <;> simp [Triangle.time, axis]

theorem axis_holomorphic (k : Fin 3) : ContDiff ℂ ω (axis k) := by
  apply contDiff_pi.mpr
  intro j
  change ContDiff ℂ ω (fun q : ℂ => if j = k then q else 1)
  by_cases h : j = k
  · simp only [if_pos h]
    exact contDiff_id
  · simp only [if_neg h]
    exact contDiff_const

theorem axis_mem_referenceDomain (k : Fin 3) (q : ℂ)
    (hq : q ∈ Metric.ball 0 CuspGeometry.data.radius) : axis k q ∈ referenceDomain := by
  rw [mem_referenceDomain, time_axis]
  simpa only [Metric.mem_ball, dist_zero_right] using hq

/-- Each whole filled parameter disc maps holomorphically into the actual reference domain. -/
def axisInclusion (k : Fin 3) (q : CuspQuotient.disc CuspGeometry.data.radius) :
    referenceDomain := ⟨axis k q, axis_mem_referenceDomain k q q.property⟩

@[simp] theorem axisInclusion_val (k : Fin 3)
    (q : CuspQuotient.disc CuspGeometry.data.radius) :
    (axisInclusion k q : CoordinateSpace 3) = axis k q := rfl

theorem axisInclusion_holomorphic (k : Fin 3) : ContMDiff 𝓘(ℂ) I₃ ω (axisInclusion k) := by
  intro q
  have he : ContMDiffAt 𝓘(ℂ) I₃ ω
      (fun r : CuspQuotient.disc CuspGeometry.data.radius =>
        (axisInclusion k r : CoordinateSpace 3)) q ↔
      ContMDiffAt 𝓘(ℂ) I₃ ω (axisInclusion k) q :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (((axis_holomorphic k).contMDiff.comp contMDiff_subtype_val) q)

/-- The actual transverse disc in the glued threefold. -/
def axisMap (k : Fin 3) : CuspQuotient.disc CuspGeometry.data.radius → Threefold.Space :=
  referenceMap ∘ axisInclusion k

theorem axisMap_holomorphic (k : Fin 3) : ContMDiff 𝓘(ℂ) IF ω (axisMap k) :=
  referenceMap_holomorphic.comp (axisInclusion_holomorphic k)

@[simp] theorem cuspCoordinate_axisMap (k : Fin 3)
    (q : CuspQuotient.disc CuspGeometry.data.radius) :
    CuspGeometry.cuspCoordinate (axisMap k q) = (q : ℂ) := by
  change CuspGeometry.cuspCoordinate (referenceMap (axisInclusion k q)) = _
  rw [cuspCoordinate_referenceMap, axisInclusion_val, time_axis]

@[simp] theorem sphereChart_projectionSphere_axisMap (k : Fin 3)
    (q : CuspQuotient.disc CuspGeometry.data.radius) :
    CuspGeometry.sphereChart (Threefold.projectionSphere (axisMap k q)) = (q : ℂ) := by
  rw [CuspGeometry.sphereChart_projectionSphere, cuspCoordinate_axisMap]

/-- Pull back all genuine global holomorphic forms through the actual reference map. -/
def referencePullback {p : ℕ} :
    Form (ℂ × ComplexPlane₂) Threefold.Space p →ₗ[ℂ]
      Form (CoordinateSpace 3) referenceDomain p :=
  pullback referenceMap referenceMap_holomorphic

/-- The pulled-back native covector uses the actual manifold derivative. -/
@[simp] theorem referencePullback_apply {p : ℕ}
    (θ : Form (ℂ × ComplexPlane₂) Threefold.Space p) (w : referenceDomain) :
    referencePullback θ w =
      (θ (referenceMap w)).compContinuousLinearMap (mfderiv I₃ IF referenceMap w) := rfl

theorem referencePullback_evaluate {p : ℕ}
    (θ : Form (ℂ × ComplexPlane₂) Threefold.Space p) (w : referenceDomain)
    (v : Fin p → CoordinateSpace 3) :
    referencePullback θ w v =
      θ (referenceMap w) (fun i => mfderiv I₃ IF referenceMap w (v i)) := rfl

/-- Evaluation of the actual pulled-back native covector at a fixed tuple of model vectors. -/
def referenceCoefficient {p : ℕ} (θ : Form (ℂ × ComplexPlane₂) Threefold.Space p)
    (v : Fin p → CoordinateSpace 3) (w : referenceDomain) : ℂ :=
  nativeCoefficients (CoordinateSpace 3) referenceDomain (referencePullback θ) w v

@[simp] theorem referenceCoefficient_eq {p : ℕ}
    (θ : Form (ℂ × ComplexPlane₂) Threefold.Space p)
    (v : Fin p → CoordinateSpace 3) (w : referenceDomain) :
    referenceCoefficient θ v w = referencePullback θ w v :=
  nativeCoefficients_apply (CoordinateSpace 3) referenceDomain (referencePullback θ) w v

/-- Constant preferred charts and continuous linear evaluation give holomorphic coefficients. -/
theorem referenceCoefficient_holomorphic {p : ℕ}
    (θ : Form (ℂ × ComplexPlane₂) Threefold.Space p) (v : Fin p → CoordinateSpace 3) :
    ContMDiff I₃ 𝓘(ℂ) ω (referenceCoefficient θ v) :=
  (ContinuousAlternatingMap.apply ℂ (CoordinateSpace 3) ℂ v).contDiff.contMDiff.comp
    (nativeCoefficients_holomorphic_of_constant_charts (CoordinateSpace 3) referenceDomain
      reference_chart_eq (referencePullback θ))

/-- Restrict a native reference-chart coefficient to the entire filled transverse disc. -/
def axisCoefficient {p : ℕ} (θ : Form (ℂ × ComplexPlane₂) Threefold.Space p)
    (k : Fin 3) (v : Fin p → CoordinateSpace 3)
    (q : CuspQuotient.disc CuspGeometry.data.radius) : ℂ :=
  referenceCoefficient θ v (axisInclusion k q)

theorem axisCoefficient_holomorphic {p : ℕ}
    (θ : Form (ℂ × ComplexPlane₂) Threefold.Space p)
    (k : Fin 3) (v : Fin p → CoordinateSpace 3) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (axisCoefficient θ k v) :=
  (referenceCoefficient_holomorphic θ v).comp (axisInclusion_holomorphic k)

/-- A concrete ambient representative of this germ, extended by zero outside the disc. -/
def axisCoefficientExtension {p : ℕ} (θ : Form (ℂ × ComplexPlane₂) Threefold.Space p)
    (k : Fin 3) (v : Fin p → CoordinateSpace 3) (q : ℂ) : ℂ := by
  classical
  exact if hq : q ∈ CuspQuotient.disc CuspGeometry.data.radius then
    axisCoefficient θ k v ⟨q, hq⟩ else 0

@[simp] theorem axisCoefficientExtension_of_mem {p : ℕ}
    (θ : Form (ℂ × ComplexPlane₂) Threefold.Space p)
    (k : Fin 3) (v : Fin p → CoordinateSpace 3) {q : ℂ}
    (hq : q ∈ CuspQuotient.disc CuspGeometry.data.radius) :
    axisCoefficientExtension θ k v q = axisCoefficient θ k v ⟨q, hq⟩ := by
  simp [axisCoefficientExtension, hq]

/-- The ambient representative is analytic at every point of the original open cusp disc. -/
theorem axisCoefficientExtension_analyticAt {p : ℕ}
    (θ : Form (ℂ × ComplexPlane₂) Threefold.Space p)
    (k : Fin 3) (v : Fin p → CoordinateSpace 3) {q : ℂ}
    (hq : q ∈ CuspQuotient.disc CuspGeometry.data.radius) :
    AnalyticAt ℂ (axisCoefficientExtension θ k v) q := by
  have he : (fun z : CuspQuotient.disc CuspGeometry.data.radius =>
      axisCoefficientExtension θ k v z) = axisCoefficient θ k v :=
    funext fun z => axisCoefficientExtension_of_mem θ k v z.property
  have hs : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (fun z : CuspQuotient.disc CuspGeometry.data.radius =>
        axisCoefficientExtension θ k v z) ⟨q, hq⟩ := by
    rw [he]
    exact axisCoefficient_holomorphic θ k v ⟨q, hq⟩
  have ha : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (axisCoefficientExtension θ k v) q :=
    contMDiffAt_subtype_iff.mp hs
  exact ha.contDiffAt.analyticAt

/-- In particular the actual coefficient has a holomorphic germ at the filled cusp. -/
theorem axisCoefficientExtension_analyticAt_zero {p : ℕ}
    (θ : Form (ℂ × ComplexPlane₂) Threefold.Space p)
    (k : Fin 3) (v : Fin p → CoordinateSpace 3) :
    AnalyticAt ℂ (axisCoefficientExtension θ k v) 0 :=
  axisCoefficientExtension_analyticAt θ k v (by
    simpa [CuspQuotient.disc] using CuspGeometry.data.radius_pos)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp
