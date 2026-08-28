import Wikipedia.HopfProblem.SpecialPeriodsCuspGlobalOverlapBase
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldBaseCoordinates
import Wikipedia.HopfProblem.CuspProper
import Wikipedia.HopfProblem.CuspTopology

/-!
# The actual full cusp piece over its chosen compact-base patch

The piece is the literal toric cusp quotient at the chosen filling
radius.  The existing cusp estimates give its Hausdorff, second-countable,
connected complex-manifold structure and proper surjective projection.
The base is identified with the actual filling patch by the inverse of
its original coordinate chart.
-/

noncomputable section

open Function Set Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspPiece

open ToricCharts ToricSpace

attribute [local instance] triangleCompactifiedChartedSpace

variable (D : CuspFamily.Data) (C : BaseCover)

/-- The same analytic cusp germs, restricted to the literal chosen
filling radius.  All analytic and small-drift properties are preserved. -/
def restrictedData (hcap : C.radius none ≤ D.radius) : CuspFamily.Data :=
  D.shrink (C.radius none) (C.radius_pos none) hcap

/-- The actual full toric cusp quotient, including its central fibre. -/
abbrev Space := CuspQuotient.QuotientSpace D.correction (C.radius none)

/-- Its original quotient atlas, in native three-coordinate notation. -/
@[instance_reducible] def nativeChartedSpace (hcap : C.radius none ≤ D.radius) :
    ChartedSpace (CoordinateSpace 3) (Space D C) :=
  CuspQuotient.chartedSpace D.correction (C.radius none) (C.radius_pos none)
    (restrictedData D C hcap).radius_lt_one
    (restrictedData D C hcap).holomorphic (restrictedData D C hcap).smallDrift

theorem space_t2Space (hcap : C.radius none ≤ D.radius) : T2Space (Space D C) :=
  CuspQuotient.quotient_t2Space D.correction (C.radius none) (C.radius_pos none)
    (restrictedData D C hcap).radius_lt_one
    (restrictedData D C hcap).holomorphic (restrictedData D C hcap).smallDrift

theorem space_secondCountable (hcap : C.radius none ≤ D.radius) :
    SecondCountableTopology (Space D C) :=
  CuspQuotient.quotient_secondCountable D.correction (C.radius none) (C.radius_pos none)
    (restrictedData D C hcap).radius_lt_one
    (restrictedData D C hcap).holomorphic (restrictedData D C hcap).smallDrift

theorem space_connected : ConnectedSpace (Space D C) :=
  CuspQuotient.quotient_connected D.correction (C.radius none) (C.radius_pos none)

theorem space_nonempty : Nonempty (Space D C) := by
  let := space_connected D C
  infer_instance

theorem native_isManifold (hcap : C.radius none ≤ D.radius) :
    letI := nativeChartedSpace D C hcap
    IsManifold (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (Space D C) :=
  CuspQuotient.isManifold D.correction (C.radius none) (C.radius_pos none)
    (restrictedData D C hcap).radius_lt_one
    (restrictedData D C hcap).holomorphic (restrictedData D C hcap).smallDrift

/-- The unchanged quotient coordinate in its literal small complex ball. -/
def coordinate : Space D C → coordinateBall (C.radius none) :=
  CuspQuotient.baseMap D.correction (C.radius none)

@[simp] theorem coordinate_coe (x : Space D C) :
    (coordinate D C x : ℂ) = CuspQuotient.projection D.correction (C.radius none) x := rfl

theorem coordinate_continuous : Continuous (coordinate D C) :=
  CuspQuotient.baseMap_continuous D.correction (C.radius none)

theorem coordinate_surjective : Surjective (coordinate D C) :=
  CuspQuotient.baseMap_surjective D.correction (C.radius none)

theorem coordinate_proper (hcap : C.radius none ≤ D.radius) :
    IsProperMap (coordinate D C) :=
  CuspQuotient.baseMap_proper D.correction (C.radius none) (C.radius_pos none)
    (restrictedData D C hcap).radius_lt_one
    (restrictedData D C hcap).holomorphic (restrictedData D C hcap).smallDrift

theorem coordinate_holomorphic_native (hcap : C.radius none ≤ D.radius) :
    letI := nativeChartedSpace D C hcap
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 3)) 𝓘(ℂ) ω (coordinate D C) :=
  CuspQuotient.baseMap_holomorphic D.correction (C.radius none) (C.radius_pos none)
    (restrictedData D C hcap).radius_lt_one
    (restrictedData D C hcap).holomorphic (restrictedData D C hcap).smallDrift

/-- The full cusp projection, expressed in the actual compact-base patch. -/
def projection : Space D C → C.fillingPatch none :=
  (C.fillingChart none).symm ∘ coordinate D C

@[simp] theorem projection_coe (x : Space D C) :
    (projection D C x : TriangleCompactifiedOrbitSpace) =
      (punctureChart none).symm (CuspQuotient.projection D.correction (C.radius none) x) := rfl

@[simp] theorem fillingChart_projection (x : Space D C) :
    C.fillingChart none (projection D C x) = coordinate D C x :=
  (C.fillingChart none).apply_symm_apply _

theorem projection_continuous : Continuous (projection D C) :=
  (C.fillingChart none).symm.continuous.comp (coordinate_continuous D C)

theorem projection_surjective : Surjective (projection D C) :=
  (C.fillingChart none).symm.surjective.comp (coordinate_surjective D C)

/-- Properness holds over the actual open filling patch, not merely in
an abstract coordinate disc. -/
theorem projection_proper (hcap : C.radius none ≤ D.radius) :
    IsProperMap (projection D C) :=
  (C.fillingChart none).symm.toHomeomorph.isProperMap.comp (coordinate_proper D C hcap)

theorem projection_holomorphic_native (hcap : C.radius none ≤ D.radius) :
    letI := nativeChartedSpace D C hcap
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 3)) 𝓘(ℂ) ω (projection D C) := by
  let := nativeChartedSpace D C hcap
  exact (C.fillingChart none).symm.contMDiff.comp (coordinate_holomorphic_native D C hcap)

/-- The same actual map with values in the entire compactified curve. -/
def projectionToBase : Space D C → TriangleCompactifiedOrbitSpace :=
  fun x => (projection D C x : TriangleCompactifiedOrbitSpace)

@[simp] theorem projectionToBase_apply (x : Space D C) :
    projectionToBase D C x =
      (punctureChart none).symm (CuspQuotient.projection D.correction (C.radius none) x) := rfl

theorem projectionToBase_holomorphic_native (hcap : C.radius none ≤ D.radius) :
    letI := nativeChartedSpace D C hcap
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 3)) 𝓘(ℂ) ω
      (projectionToBase D C) := by
  let := nativeChartedSpace D C hcap
  exact contMDiff_subtype_val.comp (projection_holomorphic_native D C hcap)

theorem range_projectionToBase :
    range (projectionToBase D C) =
      (C.fillingPatch none : Set TriangleCompactifiedOrbitSpace) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (projection D C y).property
  · intro hx
    obtain ⟨y, hy⟩ := projection_surjective D C ⟨x, hx⟩
    exact ⟨y, congrArg Subtype.val hy⟩

/-- The overlap with the regular base is precisely the nonzero locus
of the original toric quotient parameter. -/
theorem projectionToBase_mem_regular_iff (x : Space D C) :
    projectionToBase D C x ∈ regularPatch ↔
      CuspQuotient.projection D.correction (C.radius none) x ≠ 0 :=
  C.fillingEmbedding_mem_regular_iff none (coordinate D C x)

/-- The fibre over the marked cusp is exactly the original central fibre. -/
theorem projectionToBase_eq_cusp_iff (x : Space D C) :
    projectionToBase D C x = triangleCuspPoint ↔
      CuspQuotient.projection D.correction (C.radius none) x = 0 :=
  C.fillingEmbedding_eq_point_iff none (coordinate D C x)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspPiece
