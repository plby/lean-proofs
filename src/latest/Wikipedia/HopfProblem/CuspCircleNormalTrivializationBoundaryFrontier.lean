import Wikipedia.HopfProblem.CuspCircleNormalTrivializationBoundaryMap
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationBoundaryInterior
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationClosedDisk

/-!
# The literal frontier of the closed normal neighborhood

The closed normal disk image is a closed subset of the original
threefold. Pulling its interior back through the actual open normal
chart gives the strict radius inequality. Thus its actual topological
frontier, in the original threefold, is exactly the image of the
positive radius level. The resulting homeomorphism intertwines the
unchanged global circle action.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

open SpecialPeriods SpecialPeriods.Threefold
open SpecialPeriods.Threefold.VerticalAction SpecialPeriods.Threefold.Homology

local notation "Circle" => AddCircle (1 : ℝ)

attribute [local instance] Threefold.space_t2Space Threefold.chartedSpace

/-- Membership in the actual compact image is exactly the closed radius inequality. -/
theorem roundProductMap_mem_closedDiskNeighborhood_iff (p : roundNormalProduct) :
    roundProductMap p ∈ closedDiskNeighborhood ↔ radiusSq p.val.2 ≤ closedRadius ^ 2 := by
  constructor
  · rintro ⟨q, hq⟩
    have hpq : closedProductIntoRound q = p := roundProductMap_injective hq
    rw [← hpq]
    exact q.2.property
  · intro hp
    refine ⟨(p.val.1, ⟨p.val.2, hp⟩), ?_⟩
    apply congrArg roundProductMap
    exact Subtype.ext rfl

/-- The original open chart pulls the literal closed disk image back to its radius sublevel. -/
theorem roundProductMap_preimage_closedDiskNeighborhood :
    roundProductMap ⁻¹' closedDiskNeighborhood =
      {p : roundNormalProduct | radiusSq p.val.2 ≤ closedRadius ^ 2} := by
  ext p
  exact roundProductMap_mem_closedDiskNeighborhood_iff p

/-- The interior is computed in the original threefold, not just in a named model. -/
theorem roundProductMap_mem_interior_closedDiskNeighborhood_iff (p : roundNormalProduct) :
    roundProductMap p ∈ interior closedDiskNeighborhood ↔
      radiusSq p.val.2 < closedRadius ^ 2 := by
  change p ∈ roundProductMap ⁻¹' interior closedDiskNeighborhood ↔ _
  rw [roundProductMap_isOpenMap.preimage_interior_eq_interior_preimage
    roundProductMap_contMDiff.continuous, roundProductMap_preimage_closedDiskNeighborhood,
    interior_round_radiusSq_sublevel closedRadius closedRadius_pos]
  rfl

/-- The true frontier in the original threefold is the exact radius level in normal coordinates. -/
theorem roundProductMap_mem_frontier_closedDiskNeighborhood_iff (p : roundNormalProduct) :
    roundProductMap p ∈ frontier closedDiskNeighborhood ↔
      radiusSq p.val.2 = closedRadius ^ 2 := by
  rw [closedDiskNeighborhood_isCompact.isClosed.frontier_eq]
  change (roundProductMap p ∈ closedDiskNeighborhood ∧
    roundProductMap p ∉ interior closedDiskNeighborhood) ↔ _
  rw [roundProductMap_mem_closedDiskNeighborhood_iff,
    roundProductMap_mem_interior_closedDiskNeighborhood_iff]
  exact ⟨fun h => le_antisymm h.1 (not_lt.mp h.2),
    fun h => ⟨h.le, not_lt.mpr h.ge⟩⟩

/-- Equality with the actual topological frontier of the original closed normal neighborhood. -/
theorem frontier_closedDiskNeighborhood :
    frontier closedDiskNeighborhood =
      boundaryImage closedRadius closedRadius_pos closedRadius_lt_injectiveRadius := by
  ext x
  constructor
  · intro hx
    obtain ⟨q, rfl⟩ := closedDiskNeighborhood_isCompact.isClosed.frontier_subset hx
    have hq : radiusSq q.2.val = closedRadius ^ 2 :=
      (roundProductMap_mem_frontier_closedDiskNeighborhood_iff
        (closedProductIntoRound q)).mp hx
    refine ⟨⟨(q.1, q.2.val), hq⟩, ?_⟩
    apply congrArg roundProductMap
    exact Subtype.ext rfl
  · rintro ⟨p, rfl⟩
    exact (roundProductMap_mem_frontier_closedDiskNeighborhood_iff
      (boundaryIntoRound closedRadius closedRadius_pos closedRadius_lt_injectiveRadius p)).mpr
      p.property

/-- The radius level is homeomorphic to the literal frontier in the original threefold. -/
def closedBoundaryHomeomorph :
    Conifold.ProductBoundary closedRadius ≃ₜ frontier closedDiskNeighborhood :=
  (boundaryHomeomorph closedRadius closedRadius_pos closedRadius_lt_injectiveRadius).trans
    (Homeomorph.setCongr frontier_closedDiskNeighborhood.symm)

@[simp] theorem closedBoundaryHomeomorph_coe (p : Conifold.ProductBoundary closedRadius) :
    (closedBoundaryHomeomorph p : Threefold.Space) =
      boundaryMap closedRadius closedRadius_pos closedRadius_lt_injectiveRadius p := rfl

theorem frontier_closedDiskNeighborhood_subset_open :
    frontier closedDiskNeighborhood ⊆ fixedCurveNeighborhood := by
  rw [frontier_closedDiskNeighborhood]
  exact boundaryImage_subset_neighborhood _ _ _

/-- No point of the original fixed curve lies on the positive-radius frontier. -/
theorem frontier_closedDiskNeighborhood_disjoint_doubleCurve :
    Disjoint (frontier closedDiskNeighborhood) (CuspGeometry.doubleCurve 1) := by
  rw [frontier_closedDiskNeighborhood]
  apply Set.disjoint_left.mpr
  rintro _ ⟨p, rfl⟩ hp
  exact boundaryMap_not_mem_doubleCurve _ _ _ p hp

/-- The original threefold circle action preserves the actual frontier. -/
theorem actionMap_mem_frontier_closedDiskNeighborhood (t : Circle) {x : Threefold.Space}
    (hx : x ∈ frontier closedDiskNeighborhood) :
    DeltaSweep.actionMap (t, x) ∈ frontier closedDiskNeighborhood := by
  rw [frontier_closedDiskNeighborhood] at hx ⊢
  exact actionMap_mem_boundaryImage _ _ _ t hx

/-- Restriction of the unchanged global circle action to the literal frontier. -/
def closedBoundaryCircleAction (t : Circle) (x : frontier closedDiskNeighborhood) :
    frontier closedDiskNeighborhood :=
  ⟨DeltaSweep.actionMap (t, x), actionMap_mem_frontier_closedDiskNeighborhood t x.property⟩

@[simp] theorem closedBoundaryCircleAction_coe (t : Circle)
    (x : frontier closedDiskNeighborhood) :
    (closedBoundaryCircleAction t x : Threefold.Space) = DeltaSweep.actionMap (t, x) := rfl

/-- The genuine frontier homeomorphism preserves the original period-one circle action. -/
theorem closedBoundaryHomeomorph_circleAction (t : Circle)
    (p : Conifold.ProductBoundary closedRadius) :
    closedBoundaryCircleAction t (closedBoundaryHomeomorph p) =
      closedBoundaryHomeomorph (Conifold.productBoundaryCircle
        (DeltaSweep.circleParameter t : ℂ)
        (FixedCoordinates.CircleOrbit.circleParameter_norm t) p) := by
  apply Subtype.ext
  exact boundaryMap_circleAction _ _ _ t p

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
