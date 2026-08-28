import Wikipedia.HopfProblem.EllipticCentralImmersion
import Wikipedia.HopfProblem.EllipticLocalModel
import Wikipedia.HopfProblem.EllipticBundleNormalLinear
import Wikipedia.HopfProblem.EllipticBundleNormalImmersionDerivative

/-!
# The actual tangent image of the central elliptic surface

The defining central hyperplane equation in the inherited filling atlas
forces the first coordinate of the differential of its inclusion to vanish.
The already proved immersion gives injectivity, so its image is the entire
vertical tangent space, not merely a subspace of it.  The same statement is
proved before the finite quotient, for the central torus in its period family.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic

namespace NormalCoordinates

variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

theorem mfderiv_eq_chart_fderiv {f : M → N} {x : M}
    (hf : MDifferentiableAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ F) f x) :
    mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ F) f x =
      fderiv ℂ (chartAt F (f x) ∘ f ∘ (chartAt E x).symm) (chartAt E x x) := by
  simpa [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend] using hf.mfderiv

theorem differentiableAt_chart {f : M → N} {x : M}
    (hf : MDifferentiableAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ F) f x) :
    DifferentiableAt ℂ (chartAt F (f x) ∘ f ∘ (chartAt E x).symm) (chartAt E x x) := by
  simpa [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend,
    differentiableWithinAt_univ] using
    hf.differentiableWithinAt_writtenInExtChartAt

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace P] [ChartedSpace (ℂ × V) P]

/-- A vanishing local first coordinate of a map forces its actual manifold
differential to be vertical. -/
theorem mfderiv_fst_eq_zero_of_eventually {f : M → P} {x : M}
    (hf : MDifferentiableAt (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ (ℂ × V)) f x)
    (hz : ∀ᶠ y in 𝓝 x, (chartAt (ℂ × V) (f x) (f y)).1 = 0) :
    ∀ v, (mfderiv (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ (ℂ × V)) f x v).1 = 0 := by
  let f₀ := chartAt (ℂ × V) (f x) ∘ f ∘ (chartAt E x).symm
  let u := chartAt E x x
  have hc : Filter.Tendsto (chartAt E x).symm (𝓝 u) (𝓝 x) := by
    simpa only [ContinuousAt, u, (chartAt E x).left_inv (mem_chart_source E x)] using
      (chartAt E x).symm.continuousAt (mem_chart_target E x)
  have he : (fun z => (f₀ z).1) =ᶠ[𝓝 u] (fun _ => (0 : ℂ)) := hc.eventually hz
  have hd : (ContinuousLinearMap.fst ℂ ℂ V).comp (fderiv ℂ f₀ u) = 0 :=
    ((ContinuousLinearMap.fst ℂ ℂ V).hasFDerivAt.comp u
      (differentiableAt_chart hf).hasFDerivAt).unique
        ((hasFDerivAt_const (0 : ℂ) u).congr_of_eventuallyEq he)
  intro v
  rw [mfderiv_eq_chart_fderiv hf]
  exact congrArg (fun L : E →L[ℂ] ℂ => L v) hd

end NormalCoordinates

local notation "IS" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ FamilyModel

/-- The first coordinate of a family chart is its actual base coordinate. -/
theorem familyProjection_chart (j : Kind) (a x : Family j) :
    letI := (familyPeriods j).totalChartedSpace
    x ∈ (chartAt FamilyModel a).source →
      ((familyPeriods j).projection x : ℂ) = (chartAt FamilyModel a x).1 := by
  let := (familyPeriods j).totalChartedSpace
  intro hx
  have h := familyProjection_chart_symm j a (chartAt FamilyModel a x)
    ((chartAt FamilyModel a).map_source hx)
  rwa [(chartAt FamilyModel a).left_inv hx] at h

/-- The actual derivative of the prequotient central torus inclusion has
zero transverse coordinate in the inherited period-family chart. -/
theorem centralInclusion_mfderiv_fst (j : Kind) (x : (centralPeriod j).val.Torus) :
    letI := (familyPeriods j).totalChartedSpace
    ∀ w, (mfderiv IS IF (centralInclusion j) x w).1 = 0 := by
  let := (familyPeriods j).totalChartedSpace
  apply NormalCoordinates.mfderiv_fst_eq_zero_of_eventually
    ((centralInclusion_holomorphic j).mdifferentiableAt (by simp))
  have hs : ∀ᶠ y in 𝓝 x,
      centralInclusion j y ∈ (chartAt FamilyModel (centralInclusion j x)).source :=
    (centralInclusion_continuous j).continuousAt
      ((chartAt FamilyModel (centralInclusion j x)).open_source.mem_nhds
        (mem_chart_source FamilyModel (centralInclusion j x)))
  filter_upwards [hs] with y hy
  rw [← familyProjection_chart j (centralInclusion j x) (centralInclusion j y) hy,
    centralInclusion_projection]
  rfl

/-- The actual tangent image of the central torus is exactly the vertical
subspace of the family tangent model. -/
theorem centralInclusion_mfderiv_range (j : Kind) (x : (centralPeriod j).val.Torus) :
    letI := (familyPeriods j).totalChartedSpace
    (mfderiv IS IF (centralInclusion j) x).range = NormalLinear.vertical ComplexPlane₂ := by
  let := (familyPeriods j).totalChartedSpace
  exact NormalLinear.range_eq_vertical_of_injective _ (centralInclusion_mfderiv_fst j x)
    (NormalImmersion.mfderiv_injective (centralInclusion_isImmersionOfComplement j x))

/-- The actual differential of the embedded quotient surface also has zero
first coordinate in the inherited filling atlas. -/
theorem centralFibreInclusion_mfderiv_fst (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (x : Surface j (centralPeriod j) v hv) :
    ∀ w, (mfderiv IS IF (centralFibreInclusion j v hv) x w).1 = 0 := by
  apply NormalCoordinates.mfderiv_fst_eq_zero_of_eventually
    ((centralFibreInclusion_holomorphic j v hv).mdifferentiableAt (by simp))
  have hs : ∀ᶠ y in 𝓝 x, centralFibreInclusion j v hv y ∈
      (chartAt FamilyModel (centralFibreInclusion j v hv x)).source :=
    (centralFibreInclusion_continuous j v hv).continuousAt
      ((chartAt FamilyModel (centralFibreInclusion j v hv x)).open_source.mem_nhds
        (mem_chart_source FamilyModel (centralFibreInclusion j v hv x)))
  filter_upwards [hs] with y hy
  exact (fillingCentral_chart_iff j v hv (centralFibreInclusion j v hv x)
    (centralFibreInclusion j v hv y) hy).mp (fillingProjection_centralFibreInclusion j v hv y)

/-- The genuine normal tangent quotient is by this proved tangent image. -/
theorem centralFibreInclusion_mfderiv_range (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (x : Surface j (centralPeriod j) v hv) :
    (mfderiv IS IF (centralFibreInclusion j v hv) x).range =
      NormalLinear.vertical ComplexPlane₂ :=
  NormalLinear.range_eq_vertical_of_injective _ (centralFibreInclusion_mfderiv_fst j v hv x)
    (NormalImmersion.mfderiv_injective (centralFibreInclusion_isImmersionOfComplement j v hv x))

end Wikipedia.HopfProblem.Elliptic
