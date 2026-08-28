import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRegularGeometry
import Wikipedia.HopfProblem.HolomorphicDifferentialFormsFlat
import Wikipedia.HopfProblem.HolomorphicDifferentialFormsCoordinates

/-!
# Genuine form pullback to the regular period-vector cover

The map below is the original varying-lattice quotient, followed by the
original triangle quotient and the actual inclusion into the glued
threefold. Its source keeps the inherited regular upper-half-plane
coordinate and the original two complex period-vector coordinates.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover

open TrianglePeriodFamily

open HolomorphicDifferentialForms (Form)

abbrev Model := HolomorphicDifferentialForms.Coordinates.Model

local notation "IF" => modelWithCornersSelf ℂ Model

/-- The actual regular-family data from the constructed special periods. -/
abbrev data : TrianglePeriodFamily.Data ℂ TriangleRegularPoint :=
  regularData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- The original free regular base times the original complex fibre vectors. -/
abbrev Cover := TriangleRegularPoint × ComplexPlane₂

@[instance_reducible] def coverChartedSpace : ChartedSpace Model Cover :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) Cover)

attribute [local instance] chartedSpace specialRegularFamilyChartedSpace coverChartedSpace

theorem cover_isManifold : IsManifold IF ω Cover := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℂ, ℂ)) (I' := 𝓘(ℂ, ComplexPlane₂))
    TriangleRegularPoint ComplexPlane₂

attribute [local instance] cover_isManifold space_isManifold

/-- No point-dependent chart change is introduced on this open cover. -/
theorem cover_chart_eq (x y : Cover) : chartAt Model x = chartAt Model y := rfl

theorem cover_chart_apply (x y : Cover) :
    chartAt Model x y = ((y.1.val : ℂ), y.2) := rfl

/-- The actual period-vector projection to the global threefold. -/
def globalCover (x : Cover) : Threefold.Space :=
  regularFamilyInclusion (data.quotient (data.periods.quotientMap x))

@[simp] theorem globalCover_apply (x : Cover) :
    globalCover x = regularFamilyInclusion (data.quotient (data.periods.quotientMap x)) := rfl

theorem globalCover_holomorphic : ContMDiff IF IF ω globalCover := by
  let := data.periods.totalChartedSpace
  exact regularFamilyInclusion_holomorphic.comp
    ((data.quotient_holomorphic
      (regularCovering specialPeriodMap specialPeriodMap_generator₁
        specialPeriodMap_generator₂)).comp
      data.periods.quotientMap_holomorphic)

/-- Pull back any genuine holomorphic form using the actual derivative. -/
def globalCoverPullback {p : ℕ} (θ : Form Model Threefold.Space p) :
    Form Model Cover p :=
  HolomorphicDifferentialForms.pullback globalCover globalCover_holomorphic θ

theorem globalCoverPullback_apply {p : ℕ} (θ : Form Model Threefold.Space p)
    (x : Cover) (v : Fin p → Model) :
    globalCoverPullback θ x v =
      θ (globalCover x) (fun i => mfderiv IF IF globalCover x (v i)) := rfl

/-- All actual coefficient covectors of the pulled-back form. -/
def nativeCoefficients {p : ℕ} (θ : Form Model Threefold.Space p)
    (x : Cover) : Model [⋀^Fin p]→L[ℂ] ℂ :=
  HolomorphicDifferentialForms.nativeCoefficients Model Cover (globalCoverPullback θ) x

theorem nativeCoefficients_holomorphic {p : ℕ} (θ : Form Model Threefold.Space p) :
    ContMDiff IF 𝓘(ℂ, Model [⋀^Fin p]→L[ℂ] ℂ) ω (nativeCoefficients θ) :=
  HolomorphicDifferentialForms.nativeCoefficients_holomorphic_of_constant_charts
    Model Cover cover_chart_eq
    (globalCoverPullback θ)

@[simp] theorem nativeCoefficients_apply {p : ℕ} (θ : Form Model Threefold.Space p)
    (x : Cover) (v : Fin p → Model) :
    nativeCoefficients θ x v = globalCoverPullback θ x v :=
  HolomorphicDifferentialForms.nativeCoefficients_apply Model Cover (globalCoverPullback θ) x v

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover
