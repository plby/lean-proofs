import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicRegularDescent

/-!
# Extending a proved local meromorphic descent across a connected neighborhood

The comparison germ may lie at a regular value different from the center
of the base neighborhood. Connectedness of the actual full inverse image
and the native meromorphic identity theorem extend that one equality to
the whole neighborhood, including every component of a special fibre.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

open HolomorphicMeromorphic

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- One comparison germ anywhere over a connected base neighborhood
proves genuine descent throughout that neighborhood. -/
theorem meromorphicallyDescendsNear_of_connected_local_germ
    (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (b : RiemannSphere) (U : Opens RiemannSphere) (hb : b ∈ U)
    (hU : IsConnected (U : Set RiemannSphere))
    (s : Section I₁ RiemannSphere U) (x : Threefold.Space)
    (hx : projectionSphere x ∈ U)
    (he : germPullback IF I₁ sphereProjection sphereProjection_isOpenMap x
      (s ⟨projectionSphere x, hx⟩) = g ⟨x, by trivial⟩) :
    MeromorphicallyDescendsNear g b := by
  refine ⟨U, hb, s, ?_⟩
  let : ConnectedSpace (pullbackOpen IF I₁ sphereProjection U) :=
    isConnected_iff_connectedSpace.mp (projectionSphere_preimage_isConnected hU)
  apply section_eq_of_germ_eq IF Threefold.Space (x := ⟨x, hx⟩)
  exact he

/-- A native local base extension agreeing with the actual regular
descent at one regular germ gives descent at its possibly special center. -/
theorem meromorphicallyDescendsNear_of_regular_overlap
    (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (hg : ¬ (MeromorphicRegularCover.constantRegularFibres g).Countable)
    (b : RiemannSphere) (U : Opens RiemannSphere) (hb : b ∈ U)
    (hU : IsConnected (U : Set RiemannSphere))
    (s : Section I₁ RiemannSphere U) (y : RiemannSphere)
    (hyU : y ∈ U) (hyR : y ∈ sphereRegularPatch)
    (he : s ⟨y, hyU⟩ = regularSphereDescent g hg ⟨y, hyR⟩) :
    MeromorphicallyDescendsNear g b := by
  obtain ⟨x, rfl⟩ := projectionSphere_surjective y
  apply meromorphicallyDescendsNear_of_connected_local_germ g b U hb hU s x hyU
  exact (congrArg (germPullback IF I₁ sphereProjection sphereProjection_isOpenMap x) he).trans
    (congrArg (fun a : Section IF Threefold.Space
      (pullbackOpen IF I₁ sphereProjection sphereRegularPatch) => a ⟨x, hyR⟩)
      (regularSphereDescent_pullback g hg))

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
