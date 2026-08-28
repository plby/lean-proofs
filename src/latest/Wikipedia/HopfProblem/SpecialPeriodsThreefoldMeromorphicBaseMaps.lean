import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicCover
import Wikipedia.HopfProblem.HolomorphicMeromorphicLocalDiffeomorph
import Wikipedia.HopfProblem.HolomorphicMeromorphicPullbackPointwise

/-!
# Actual base maps and native meromorphic germ comparison

The free regular base coordinate, its sphere covering, and the period
vector projection are all the original constructed maps.  Their
commuting square is proved directly from the original quotient
projection.  The sphere covering induces a genuine equivalence of
meromorphic fraction-field stalks at every free regular base point.
-/

noncomputable section

open Set Topology TopologicalSpace UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.MeromorphicRegularCover

open HolomorphicForms.RegularCover

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  coverChartedSpace cover_isManifold

/-- The inherited complex coordinate on the original free regular base. -/
def freeBaseCoordinateMap : ContMDiffMap I₁ I₁ TriangleRegularPoint ℂ ω :=
  ⟨fun z => (z.val : ℂ), UpperHalfPlane.contMDiff_coe.comp contMDiff_subtype_val⟩

@[simp] theorem freeBaseCoordinateMap_apply (z : TriangleRegularPoint) :
    freeBaseCoordinateMap z = (z.val : ℂ) := rfl

theorem freeBaseCoordinateMap_isOpenMap : IsOpenMap freeBaseCoordinateMap :=
  UpperHalfPlane.isOpenEmbedding_coe.isOpenMap.comp
    triangleRegularDomain.isOpen.isOpenMap_subtype_val

/-- The original free regular base covering of the regular sphere locus. -/
def sphereBaseMap : ContMDiffMap I₁ I₁ TriangleRegularPoint RiemannSphere ω :=
  ⟨sourceBase, sourceBase_holomorphic⟩

@[simp] theorem sphereBaseMap_apply (z : TriangleRegularPoint) :
    sphereBaseMap z = sourceBase z := rfl

theorem sphereBaseMap_isOpenMap : IsOpenMap sphereBaseMap := sourceBase_isOpenMap

/-- The original free-base projection of the period-vector cover. -/
def coverBaseProjection : ContMDiffMap IF I₁ Cover TriangleRegularPoint ω :=
  ⟨Prod.fst, by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_fst⟩

@[simp] theorem coverBaseProjection_apply (x : Cover) : coverBaseProjection x = x.1 := rfl

theorem coverBaseProjection_isOpenMap : IsOpenMap coverBaseProjection := isOpenMap_fst

/-- The genuine bundle of maps commutes, not just its values after a
set-theoretic identification of the base. -/
theorem sphereProjection_comp_toThreefold :
    sphereProjection.comp toThreefold = sphereBaseMap.comp coverBaseProjection :=
  ContMDiffMap.ext fun x => projectionSphere_toThreefold x.1 x.2

/-- Every genuine meromorphic germ on the free regular base comes
from a genuine sphere germ via the actual locally biholomorphic map. -/
theorem sphereBaseMap_germPullback_surjective (z : TriangleRegularPoint) :
    Function.Surjective
      (HolomorphicMeromorphic.germPullback I₁ I₁ sphereBaseMap sphereBaseMap_isOpenMap z) :=
  HolomorphicMeromorphic.germPullback_surjective_of_isLocalDiffeomorphAt I₁ I₁
    sphereBaseMap sphereBaseMap_isOpenMap z (sourceBase_isLocalDiffeomorph z)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.MeromorphicRegularCover
