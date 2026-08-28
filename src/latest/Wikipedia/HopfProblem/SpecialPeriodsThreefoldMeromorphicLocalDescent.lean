import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicBaseMaps
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicConnectedPreimages
import Wikipedia.HopfProblem.HolomorphicMeromorphicDescentGluing
import Mathlib.Topology.Connected.LocallyConnected

/-!
# Native local descent along the actual sphere projection

A local base fraction with one proved pullback germ gives equality over
the full inverse image of a smaller connected sphere neighborhood.
For the original regular cover, a germ in the inherited free complex
base coordinate transfers to a sphere germ using the actual local
biholomorphic base covering and the genuine functorial stalk maps.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- Genuine local descent of an original meromorphic function over a
neighborhood in the actual sphere. -/
def MeromorphicallyDescendsNear (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (b : RiemannSphere) : Prop :=
  ∃ (U : Opens RiemannSphere) (_hb : b ∈ U)
    (s : HolomorphicMeromorphic.Section I₁ RiemannSphere U),
    HolomorphicMeromorphic.pullbackSection IF I₁ sphereProjection sphereProjection_isOpenMap U s =
      HolomorphicMeromorphic.restrict IF Threefold.Space (show
        HolomorphicMeromorphic.pullbackOpen IF I₁ sphereProjection U ≤ ⊤ from le_top) g

/-- One actual fraction-germ equality extends across the full inverse
image of a connected base neighborhood. -/
theorem meromorphicallyDescendsNear_of_local_germ
    (g : HolomorphicMeromorphic.Function IF Threefold.Space) (U : Opens RiemannSphere)
    (s : HolomorphicMeromorphic.Section I₁ RiemannSphere U) (x : Threefold.Space)
    (hx : projectionSphere x ∈ U)
    (he : HolomorphicMeromorphic.germPullback IF I₁ sphereProjection
      sphereProjection_isOpenMap x (s ⟨projectionSphere x, hx⟩) = g ⟨x, by trivial⟩) :
    MeromorphicallyDescendsNear g (projectionSphere x) := by
  let : LocallyConnectedSpace RiemannSphere :=
    ChartedSpace.locallyConnectedSpace ℂ RiemannSphere
  obtain ⟨W, ⟨hWo, hxW, hWc⟩, hWU⟩ :=
    (LocallyConnectedSpace.open_connected_basis (projectionSphere x)).mem_iff.mp
      (U.isOpen.mem_nhds hx)
  let W' : Opens RiemannSphere := ⟨W, hWo⟩
  have hW'U : W' ≤ U := hWU
  let sW := HolomorphicMeromorphic.restrict I₁ RiemannSphere hW'U s
  refine ⟨W', hxW, sW, ?_⟩
  let : ConnectedSpace (HolomorphicMeromorphic.pullbackOpen IF I₁ sphereProjection W') :=
    isConnected_iff_connectedSpace.mp (projectionSphere_preimage_isConnected hWc)
  apply HolomorphicMeromorphic.section_eq_of_germ_eq IF Threefold.Space
    (x := ⟨x, hxW⟩)
  exact he

/-- Once genuine local descent is established at every actual sphere
point, its local fractions glue uniquely in the original meromorphic sheaf. -/
theorem existsUnique_sphere_descent_of_local
    (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (hlocal : ∀ b : RiemannSphere, MeromorphicallyDescendsNear g b) :
    ∃! s : HolomorphicMeromorphic.Function I₁ RiemannSphere, sphereMeromorphicPullback s = g :=
  HolomorphicMeromorphic.existsUnique_global_descent IF I₁ sphereProjection
    sphereProjection_isOpenMap projectionSphere_surjective g hlocal

namespace MeromorphicRegularCover

open HolomorphicForms.RegularCover

attribute [local instance] coverChartedSpace cover_isManifold

/-- A genuine factor germ in the original free complex coordinate
becomes an actual local sphere section with the same pullback germ. -/
theorem exists_local_sphere_section_of_coordinate_germ
    (g : HolomorphicMeromorphic.Function IF Threefold.Space) (x : Cover)
    (a : HolomorphicMeromorphic.Germ I₁ ℂ ((x.1.val : ℂ)))
    (ha : HolomorphicMeromorphic.germPullback IF I₁
      (freeBaseCoordinateMap.comp coverBaseProjection)
      (freeBaseCoordinateMap_isOpenMap.comp coverBaseProjection_isOpenMap) x a =
        coverPullback g ⟨x, by trivial⟩) :
    ∃ (U : Opens RiemannSphere) (hx : projectionSphere (toThreefold x) ∈ U)
      (s : HolomorphicMeromorphic.Section I₁ RiemannSphere U),
      HolomorphicMeromorphic.germPullback IF I₁ sphereProjection
        sphereProjection_isOpenMap (toThreefold x)
        (s ⟨projectionSphere (toThreefold x), hx⟩) = g ⟨toThreefold x, by trivial⟩ := by
  let b := HolomorphicMeromorphic.germPullback I₁ I₁ freeBaseCoordinateMap
    freeBaseCoordinateMap_isOpenMap x.1 a
  obtain ⟨c, hc⟩ := sphereBaseMap_germPullback_surjective x.1 b
  obtain ⟨U, hxU, s, hs⟩ := HolomorphicMeromorphic.exists_section_through_germ
    I₁ RiemannSphere (sourceBase x.1) c
  have hxU' : projectionSphere (toThreefold x) ∈ U :=
    (projectionSphere_toThreefold x.1 x.2).symm ▸ hxU
  refine ⟨U, hxU', s, ?_⟩
  apply (HolomorphicMeromorphic.germPullback IF IF toThreefold toThreefold_isOpenMap x).injective
  calc
    HolomorphicMeromorphic.germPullback IF IF toThreefold toThreefold_isOpenMap x
        (HolomorphicMeromorphic.germPullback IF I₁ sphereProjection
          sphereProjection_isOpenMap (toThreefold x)
          (s ⟨projectionSphere (toThreefold x), hxU'⟩)) =
        HolomorphicMeromorphic.germPullback IF I₁ (sphereProjection.comp toThreefold)
          (sphereProjection_isOpenMap.comp toThreefold_isOpenMap) x
          (s ⟨projectionSphere (toThreefold x), hxU'⟩) :=
      HolomorphicMeromorphic.germPullback_comp_apply IF IF I₁ toThreefold
        toThreefold_isOpenMap sphereProjection sphereProjection_isOpenMap x _
    _ = HolomorphicMeromorphic.germPullback IF I₁ (sphereBaseMap.comp coverBaseProjection)
        (sphereBaseMap_isOpenMap.comp coverBaseProjection_isOpenMap) x
        (s ⟨sourceBase x.1, hxU⟩) :=
      HolomorphicMeromorphic.germPullback_section_congr IF I₁
        (sphereProjection.comp toThreefold) (sphereBaseMap.comp coverBaseProjection)
        (sphereProjection_isOpenMap.comp toThreefold_isOpenMap)
        (sphereBaseMap_isOpenMap.comp coverBaseProjection_isOpenMap)
        (fun y => projectionSphere_toThreefold y.1 y.2) U s x hxU' hxU
    _ = HolomorphicMeromorphic.germPullback IF I₁ coverBaseProjection
        coverBaseProjection_isOpenMap x
        (HolomorphicMeromorphic.germPullback I₁ I₁ sphereBaseMap sphereBaseMap_isOpenMap x.1
          (s ⟨sourceBase x.1, hxU⟩)) :=
      (HolomorphicMeromorphic.germPullback_comp_apply IF I₁ I₁ coverBaseProjection
        coverBaseProjection_isOpenMap sphereBaseMap sphereBaseMap_isOpenMap x _).symm
    _ = HolomorphicMeromorphic.germPullback IF I₁ coverBaseProjection
        coverBaseProjection_isOpenMap x b := by
      exact congrArg (HolomorphicMeromorphic.germPullback IF I₁ coverBaseProjection
        coverBaseProjection_isOpenMap x)
        ((congrArg (HolomorphicMeromorphic.germPullback I₁ I₁ sphereBaseMap
          sphereBaseMap_isOpenMap x.1) hs).trans hc)
    _ = HolomorphicMeromorphic.germPullback IF I₁
        (freeBaseCoordinateMap.comp coverBaseProjection)
        (freeBaseCoordinateMap_isOpenMap.comp coverBaseProjection_isOpenMap) x a :=
      HolomorphicMeromorphic.germPullback_comp_apply IF I₁ I₁ coverBaseProjection
        coverBaseProjection_isOpenMap freeBaseCoordinateMap freeBaseCoordinateMap_isOpenMap x a
    _ = coverPullback g ⟨x, by trivial⟩ := ha
    _ = HolomorphicMeromorphic.germPullback IF IF toThreefold toThreefold_isOpenMap x
        (g ⟨toThreefold x, by trivial⟩) := rfl

end MeromorphicRegularCover

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
