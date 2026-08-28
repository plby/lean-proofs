import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicProjection
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsDetectionCover
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldConnected
import Wikipedia.HopfProblem.SpecialPeriodsTriangleRegularElliptic
import Wikipedia.HopfProblem.HolomorphicMeromorphicPullbackFunctor

/-!
# Genuine meromorphic functions on the actual regular vector cover

The source is the original regular upper-half-plane locus times the
original period vectors.  Its quotient map is the already constructed
locally biholomorphic map to the actual threefold, so the meromorphic
pullback uses the native holomorphic stalk maps.  The base-coordinate
identity is an identity of the original quotient projections.
-/

noncomputable section

open Set Topology TopologicalSpace UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.MeromorphicRegularCover

open HolomorphicForms.RegularCover

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  Threefold.space_connected coverChartedSpace cover_isManifold
  triangleRegularQuotientChartedSpace

/-- The actual regular vector-cover map, bundled with its native holomorphicity. -/
def toThreefold : ContMDiffMap IF IF Cover Threefold.Space ω :=
  ⟨globalCover, globalCover_holomorphic⟩

@[simp] theorem toThreefold_apply (x : Cover) : toThreefold x = globalCover x := rfl

theorem toThreefold_isOpenMap : IsOpenMap toThreefold :=
  globalCover_isLocalDiffeomorph.isOpenMap

/-- Pullback of arbitrary genuine global meromorphic functions to the
original regular period-vector cover. -/
def coverPullback :
    HolomorphicMeromorphic.Function IF Threefold.Space →ₐ[ℂ]
      HolomorphicMeromorphic.Function IF Cover :=
  HolomorphicMeromorphic.pullbackAlgHom IF IF toThreefold toThreefold_isOpenMap ⊤

@[simp] theorem coverPullback_apply
    (s : HolomorphicMeromorphic.Function IF Threefold.Space)
    (x : (⊤ : Opens Cover)) :
    coverPullback s x =
      HolomorphicMeromorphic.germPullback IF IF toThreefold toThreefold_isOpenMap x.val
        (s ⟨globalCover x.val, by trivial⟩) := rfl

/-- The connected threefold's genuine meromorphic function field injects
into that of the original, nonempty regular vector cover. -/
theorem coverPullback_injective : Function.Injective coverPullback := by
  let : ConnectedSpace (⊤ : Opens Threefold.Space) :=
    isConnected_iff_connectedSpace.mp isConnected_univ
  let : Nonempty (⊤ : Opens Cover) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty Cover), by trivial⟩⟩
  exact coverPullback.toRingHom.injective

/-- The sphere coordinate of an original free regular base point. -/
def sourceBase (z : TriangleRegularPoint) : RiemannSphere :=
  regularBaseSphere (triangleRegularProject z)

theorem sourceBase_isLocalDiffeomorph :
    IsLocalDiffeomorph I₁ I₁ ω sourceBase := by
  intro z
  exact (triangleRegularProject_isLocalDiffeomorph z).comp
    (K := I₁) (P := RiemannSphere)
    (regularBaseSphere_isLocalDiffeomorph (triangleRegularProject z))

theorem sourceBase_holomorphic : ContMDiff I₁ I₁ ω sourceBase :=
  sourceBase_isLocalDiffeomorph.contMDiff

theorem sourceBase_isOpenMap : IsOpenMap sourceBase :=
  sourceBase_isLocalDiffeomorph.isOpenMap

/-- The base of the actual cover is independent of its original fibre vector. -/
@[simp] theorem projectionSphere_toThreefold (z : TriangleRegularPoint) (v : ComplexPlane₂) :
    projectionSphere (toThreefold (z, v)) = sourceBase z := by
  change projectionSphere (regularFamilyInclusion (data.quotient
    (data.periods.quotientMap (z, v)))) = sourceBase z
  rw [regularFamilyInclusion_projectionSphere, data.projection_quotient]
  rfl

theorem sourceBase_mem_sphereRegularPatch (z : TriangleRegularPoint) :
    sourceBase z ∈ sphereRegularPatch := by
  rw [← projectionSphere_toThreefold z (0 : ComplexPlane₂)]
  exact (mem_regularLocus_iff_sphere _).mp (globalCover_mem_regularLocus (z, 0))

/-- Every original point of a regular fibre has an actual period-vector lift. -/
theorem exists_toThreefold_eq (x : Threefold.Space) (hx : x ∈ regularLocus) :
    ∃ u : Cover, toThreefold u = x := by
  have hx' : x ∈ range globalCover := by rwa [range_globalCover]
  exact hx'

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.MeromorphicRegularCover
