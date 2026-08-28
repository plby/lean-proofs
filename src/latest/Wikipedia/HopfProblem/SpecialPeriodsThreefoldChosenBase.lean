import Wikipedia.HopfProblem.SpecialPeriodsThreefoldBaseCoordinates
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRegularFamily
import Wikipedia.HopfProblem.SpecialPeriodsExistence

/-!
# The unconditional chosen base cover and regular threefold piece

The actual normalized sphere uniformization and the actual special periods
now instantiate the small disjoint-disc construction and the regular torus
family.  There is no remaining uniformization or period-map input in this
file.  The regular piece retains its genuine diagonal-quotient complex atlas.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

open Triangle

attribute [local instance] triangleCompactifiedChartedSpace

/-- The chosen four-patch base cover, now without any supplied input. -/
def specialBaseCover : BaseCover :=
  baseCoverOfSphere triangleSphereUniformization triangleSphereUniformization_cusp
    triangleSphereUniformization_centerOne triangleSphereUniformization_centerTwo

theorem specialBaseCover_isOpenCover : TopologicalSpace.IsOpenCover specialBaseCover.patch :=
  specialBaseCover.isOpenCover

theorem specialBaseCover_cusp_radius_bounds :
    0 < specialBaseCover.radius none ∧
      specialBaseCover.radius none < specialCuspData.radius ∧
      specialBaseCover.radius none < cuspRadius width :=
  baseCoverOfSphere_cusp_radius_bounds triangleSphereUniformization
    triangleSphereUniformization_cusp triangleSphereUniformization_centerOne
    triangleSphereUniformization_centerTwo

/-- A genuine regular point is obtained from the finite sphere coordinate
two, distinct from all three normalized marked values. -/
def regularPatchPoint : regularPatch := by
  let x := triangleSphereUniformization.symm ((2 : ℂ) : RiemannSphere)
  have hx : triangleSphereUniformization x = ((2 : ℂ) : RiemannSphere) :=
    triangleSphereUniformization.apply_symm_apply _
  refine ⟨x, (mem_regularPatch x).mpr ⟨?_, ?_, ?_⟩⟩
  · intro h
    have he := congrArg triangleSphereUniformization h
    rw [hx, triangleSphereUniformization_cusp] at he
    exact OnePoint.coe_ne_infty (2 : ℂ) he
  · intro h
    have he := congrArg triangleSphereUniformization h
    change triangleSphereUniformization x =
      triangleSphereUniformization (triangleOpenInclusion triangleOrbitCenterOne) at he
    rw [hx, triangleSphereUniformization_centerOne] at he
    have he' := OnePoint.coe_injective he
    norm_num at he'
  · intro h
    have he := congrArg triangleSphereUniformization h
    change triangleSphereUniformization x =
      triangleSphereUniformization (triangleOpenInclusion triangleOrbitCenterTwo) at he
    rw [hx, triangleSphereUniformization_centerTwo] at he
    have he' := OnePoint.coe_injective he
    norm_num at he'

theorem regularPatch_nonempty : Nonempty regularPatch := ⟨regularPatchPoint⟩

/-- The actual regular quotient family of the unconditional special periods. -/
abbrev SpecialRegularFamily :=
  RegularFamily specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- The native analytic quotient atlas, not a transported complex structure. -/
@[instance_reducible] def specialRegularFamilyChartedSpace :
    ChartedSpace (ℂ × ComplexPlane₂) SpecialRegularFamily :=
  regularFamilyChartedSpace specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

def specialRegularFamilyProjection : SpecialRegularFamily → regularPatch :=
  regularFamilyProjection specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

def specialRegularFamilyProjectionToBase : SpecialRegularFamily → TriangleCompactifiedOrbitSpace :=
  regularFamilyProjectionToBase specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂

@[simp] theorem specialRegularFamilyProjectionToBase_eq (x : SpecialRegularFamily) :
    specialRegularFamilyProjectionToBase x =
      (specialRegularFamilyProjection x : TriangleCompactifiedOrbitSpace) := rfl

theorem specialRegularFamilyProjectionToBase_mem (x : SpecialRegularFamily) :
    specialRegularFamilyProjectionToBase x ∈ regularPatch :=
  (specialRegularFamilyProjection x).property

theorem specialRegularFamilyProjection_proper : IsProperMap specialRegularFamilyProjection :=
  regularFamilyProjection_proper specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂

theorem specialRegularFamilyProjection_surjective :
    Function.Surjective specialRegularFamilyProjection :=
  regularFamilyProjection_surjective specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂

theorem specialRegularFamilyProjectionToBase_continuous :
    Continuous specialRegularFamilyProjectionToBase :=
  continuous_subtype_val.comp (regularFamilyProjection_continuous specialPeriodMap
    specialPeriodMap_generator₁ specialPeriodMap_generator₂)

theorem specialRegularFamilyProjectionToBase_holomorphic :
    letI := specialRegularFamilyChartedSpace
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) 𝓘(ℂ) ω
      specialRegularFamilyProjectionToBase :=
  regularFamilyProjectionToBase_holomorphic specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂

theorem specialRegularFamily_t2Space : T2Space SpecialRegularFamily :=
  regularFamily_t2Space specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

theorem specialRegularFamily_secondCountable : SecondCountableTopology SpecialRegularFamily :=
  regularFamily_secondCountable specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂

theorem specialRegularFamily_isManifold :
    letI := specialRegularFamilyChartedSpace
    IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω SpecialRegularFamily :=
  regularFamily_isManifold specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- A point of the genuine regular piece is given by its actual zero
section over the selected regular point. -/
def specialRegularFamilyPoint : SpecialRegularFamily :=
  regularFamilyZeroSection specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂
    regularPatchPoint

theorem specialRegularFamily_nonempty : Nonempty SpecialRegularFamily :=
  ⟨specialRegularFamilyPoint⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
