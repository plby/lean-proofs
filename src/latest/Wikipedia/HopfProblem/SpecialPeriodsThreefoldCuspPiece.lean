import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspPieceSphere
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspPieceModelChange

/-!
# The actual full cusp piece in the common threefold model

The explicit complex-linear model change re-expresses the native toric
quotient atlas in `ℂ × ComplexPlane₂`.  The identity is biholomorphic, also
on inherited open submanifolds, so the native cusp projection and the
punctured cusp overlaps retain their actual analytic structures.
-/

noncomputable section

open Function Set Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspPiece

open ToricCharts

attribute [local instance] triangleCompactifiedChartedSpace

variable (D : CuspFamily.Data) (C : BaseCover)

/-- The native quotient atlas composed with the explicit complex-linear
reindexing to the common threefold model. -/
@[instance_reducible] def commonChartedSpace (hcap : C.radius none ≤ D.radius) :
    ChartedSpace (ℂ × ComplexPlane₂) (Space D C) := by
  let := nativeChartedSpace D C hcap
  exact ModelChange.chartedSpace cuspModelEquiv (Space D C)

theorem common_isManifold (hcap : C.radius none ≤ D.radius) :
    letI := commonChartedSpace D C hcap
    IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (Space D C) := by
  let := nativeChartedSpace D C hcap
  let := native_isManifold D C hcap
  exact ModelChange.isManifold cuspModelEquiv (Space D C) ω

/-- Identity on the actual quotient space, analytic for the native and
common coordinate models. -/
def nativeToCommon (hcap : C.radius none ≤ D.radius) :
    letI := nativeChartedSpace D C hcap
    letI := commonChartedSpace D C hcap
    Diffeomorph (modelWithCornersSelf ℂ (CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (Space D C) (Space D C) ω := by
  let := nativeChartedSpace D C hcap
  exact ModelChange.diffeomorph cuspModelEquiv (Space D C) ω

@[simp] theorem nativeToCommon_apply (hcap : C.radius none ≤ D.radius) (x : Space D C) :
    nativeToCommon D C hcap x = x := rfl

@[simp] theorem nativeToCommon_symm_apply (hcap : C.radius none ≤ D.radius)
    (x : Space D C) :
    letI := nativeChartedSpace D C hcap
    letI := commonChartedSpace D C hcap
    (nativeToCommon D C hcap).symm x = x := rfl

/-- The same identity on an open submanifold uses the atlases inherited
from the two full cusp atlases.  In particular it applies to the literal
nonzero-parameter cusp overlap. -/
def nativeToCommonOpen (hcap : C.radius none ≤ D.radius)
    (U : TopologicalSpace.Opens (Space D C)) :
    letI := nativeChartedSpace D C hcap
    letI := commonChartedSpace D C hcap
    Diffeomorph (modelWithCornersSelf ℂ (CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) U U ω := by
  let := nativeChartedSpace D C hcap
  exact ModelChange.openDiffeomorph cuspModelEquiv (Space D C) U ω

@[simp] theorem nativeToCommonOpen_apply (hcap : C.radius none ≤ D.radius)
    (U : TopologicalSpace.Opens (Space D C)) (x : U) :
    nativeToCommonOpen D C hcap U x = x := rfl

@[simp] theorem nativeToCommonOpen_symm_apply (hcap : C.radius none ≤ D.radius)
    (U : TopologicalSpace.Opens (Space D C)) (x : U) :
    letI := nativeChartedSpace D C hcap
    letI := commonChartedSpace D C hcap
    (nativeToCommonOpen D C hcap U).symm x = x := rfl

theorem coordinate_common_holomorphic (hcap : C.radius none ≤ D.radius) :
    letI := commonChartedSpace D C hcap
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) 𝓘(ℂ) ω (coordinate D C) := by
  let := nativeChartedSpace D C hcap
  let := commonChartedSpace D C hcap
  exact (coordinate_holomorphic_native D C hcap).comp
    (nativeToCommon D C hcap).symm.contMDiff

theorem projection_common_holomorphic (hcap : C.radius none ≤ D.radius) :
    letI := commonChartedSpace D C hcap
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) 𝓘(ℂ) ω (projection D C) := by
  let := commonChartedSpace D C hcap
  exact (C.fillingChart none).symm.contMDiff.comp (coordinate_common_holomorphic D C hcap)

theorem projectionToBase_common_holomorphic (hcap : C.radius none ≤ D.radius) :
    letI := commonChartedSpace D C hcap
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) 𝓘(ℂ) ω
      (projectionToBase D C) := by
  let := commonChartedSpace D C hcap
  exact contMDiff_subtype_val.comp (projection_common_holomorphic D C hcap)

section Sphere

variable (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
  TriangleCompactifiedOrbitSpace RiemannSphere ω)
  (hπ : π triangleCuspPoint = (∞ : RiemannSphere))
  (h₀ : π (triangleOpenInclusion triangleOrbitCenterOne) = ((0 : ℂ) : RiemannSphere))
  (h₁ : π (triangleOpenInclusion triangleOrbitCenterTwo) = ((1 : ℂ) : RiemannSphere))

/-- The actual constructed full cusp piece in the common threefold model. -/
@[instance_reducible] def commonChartedSpaceOfSphere :
    ChartedSpace (ℂ × ComplexPlane₂) (OfSphere π hπ h₀ h₁) :=
  commonChartedSpace (Construction.cuspDataOfSphere π hπ h₀ h₁)
    (baseCoverOfSphere π hπ h₀ h₁)
    (baseCoverOfSphere_radius_lt_cap π hπ h₀ h₁ none).le

theorem common_isManifoldOfSphere :
    letI := commonChartedSpaceOfSphere π hπ h₀ h₁
    IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (OfSphere π hπ h₀ h₁) :=
  common_isManifold (Construction.cuspDataOfSphere π hπ h₀ h₁)
    (baseCoverOfSphere π hπ h₀ h₁)
    (baseCoverOfSphere_radius_lt_cap π hπ h₀ h₁ none).le

theorem projectionOfSphere_common_holomorphic :
    letI := commonChartedSpaceOfSphere π hπ h₀ h₁
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) 𝓘(ℂ) ω
      (projectionOfSphere π hπ h₀ h₁) :=
  projection_common_holomorphic (Construction.cuspDataOfSphere π hπ h₀ h₁)
    (baseCoverOfSphere π hπ h₀ h₁)
    (baseCoverOfSphere_radius_lt_cap π hπ h₀ h₁ none).le

theorem projectionToBaseOfSphere_common_holomorphic :
    letI := commonChartedSpaceOfSphere π hπ h₀ h₁
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) 𝓘(ℂ) ω
      (projectionToBaseOfSphere π hπ h₀ h₁) :=
  projectionToBase_common_holomorphic (Construction.cuspDataOfSphere π hπ h₀ h₁)
    (baseCoverOfSphere π hπ h₀ h₁)
    (baseCoverOfSphere_radius_lt_cap π hπ h₀ h₁ none).le

/-- The actual cusp filling is a nonempty Hausdorff second-countable
complex threefold, proper and surjective over its original base patch.
All its analytic data and radius bounds have been constructed. -/
theorem ofSphere_common_properties :
    letI := commonChartedSpaceOfSphere π hπ h₀ h₁
    IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (OfSphere π hπ h₀ h₁) ∧
      T2Space (OfSphere π hπ h₀ h₁) ∧ SecondCountableTopology (OfSphere π hπ h₀ h₁) ∧
      Nonempty (OfSphere π hπ h₀ h₁) ∧ IsProperMap (projectionOfSphere π hπ h₀ h₁) ∧
      Surjective (projectionOfSphere π hπ h₀ h₁) ∧
      ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) 𝓘(ℂ) ω
        (projectionOfSphere π hπ h₀ h₁) :=
  ⟨common_isManifoldOfSphere π hπ h₀ h₁, ofSphere_t2Space π hπ h₀ h₁,
    ofSphere_secondCountable π hπ h₀ h₁, ofSphere_nonempty π hπ h₀ h₁,
    projectionOfSphere_proper π hπ h₀ h₁, projectionOfSphere_surjective π hπ h₀ h₁,
    projectionOfSphere_common_holomorphic π hπ h₀ h₁⟩

end Sphere

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspPiece
