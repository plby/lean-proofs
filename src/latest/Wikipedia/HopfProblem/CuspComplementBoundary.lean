import Wikipedia.HopfProblem.CuspComplementOuterBoundaryFrontier
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationStandardBoundary

/-!
# The two genuine frontier pieces of the actual cusp complement

The fixed closed normal neighborhood is the closure of its interior in
the original threefold.  This follows from its actual open normal chart
and the closure of a Euclidean ball, without a regularity hypothesis.
Consequently, the compact cusp complement has exactly the original
outer parameter level and the existing normal frontier as its frontier.
The established standard boundary map is unchanged.
-/

noncomputable section

open Set Topology Metric

namespace Wikipedia.HopfProblem.CuspComplement

open CuspCircleNormalTrivialization SpecialPeriods SpecialPeriods.Threefold

attribute [local instance] Threefold.space_t2Space Threefold.chartedSpace

/-- Strict and weak radius sublevels have the expected closure in the
actual open normal coordinate domain. -/
theorem closure_round_radiusSq_strict_sublevel (r : ℝ) (hr : 0 < r) :
    closure {p : roundNormalProduct | radiusSq p.val.2 < r ^ 2} =
      {p : roundNormalProduct | radiusSq p.val.2 ≤ r ^ 2} := by
  let f : roundNormalProduct → RealFour.Space := fun p => RealFour.coordinateEquiv p.val.2
  have ho : IsOpenMap f :=
    RealFour.coordinateEquiv.isOpenMap.comp
      (isOpenMap_snd.comp
        roundNormalProduct.isOpen.isOpenEmbedding_subtypeVal.isOpenMap)
  have hc : Continuous f :=
    RealFour.coordinateEquiv.continuous.comp continuous_subtype_val.snd
  have hs : {p : roundNormalProduct | radiusSq p.val.2 < r ^ 2} =
      f ⁻¹' ball (0 : RealFour.Space) r := by
    ext p
    exact RealFour.radiusSq_lt_iff_mem_ball r hr.le p.val.2
  rw [hs, ← ho.preimage_closure_eq_closure_preimage hc,
    closure_ball (0 : RealFour.Space) hr.ne']
  ext p
  exact (RealFour.radiusSq_le_iff_mem_closedBall r hr.le p.val.2).symm

/-- The actual fixed compact normal neighborhood is regular closed;
no ambient regularity or collar assumption is introduced. -/
theorem closure_interior_closedDiskNeighborhood :
    closure (interior closedDiskNeighborhood) = closedDiskNeighborhood := by
  apply subset_antisymm
  · exact closure_minimal interior_subset closedDiskNeighborhood_isCompact.isClosed
  · have hpre : roundProductMap ⁻¹' interior closedDiskNeighborhood =
        {p : roundNormalProduct | radiusSq p.val.2 < closedRadius ^ 2} := by
      ext p
      exact roundProductMap_mem_interior_closedDiskNeighborhood_iff p
    have hcl : roundProductMap ⁻¹' closure (interior closedDiskNeighborhood) =
        {p : roundNormalProduct | radiusSq p.val.2 ≤ closedRadius ^ 2} := by
      rw [roundProductMap_isOpenMap.preimage_closure_eq_closure_preimage
        roundProductMap_contMDiff.continuous, hpre,
        closure_round_radiusSq_strict_sublevel closedRadius closedRadius_pos]
    rintro x ⟨p, rfl⟩
    have hp : closedProductIntoRound p ∈
        roundProductMap ⁻¹' closure (interior closedDiskNeighborhood) := by
      rw [hcl]
      exact p.2.property
    exact hp

/-- The interior is the literal strict cusp sublevel minus the fixed
closed normal neighborhood, in the original ambient topology. -/
theorem interior_capComplement :
    interior capComplement = (openCap : Set Threefold.Space) \ closedDiskNeighborhood := by
  change interior (cap ∩ (interior closedDiskNeighborhood)ᶜ) = _
  rw [interior_inter, interior_compl, closure_interior_closedDiskNeighborhood,
    OuterBoundary.interior_cap]
  rfl

/-- The complement has precisely the two existing, disjoint frontier
pieces, with no replacement of the cap or its fixed normal disk. -/
theorem frontier_capComplement :
    frontier capComplement = outerBoundary ∪ frontier closedDiskNeighborhood := by
  classical
  rw [capComplement_isCompact.isClosed.frontier_eq, interior_capComplement,
    ← OuterBoundary.frontier_cap, cap_isCompact.isClosed.frontier_eq,
    closedDiskNeighborhood_isCompact.isClosed.frontier_eq, OuterBoundary.interior_cap]
  ext x
  change ((x ∈ cap ∧ x ∉ interior closedDiskNeighborhood) ∧
      ¬(x ∈ (openCap : Set Threefold.Space) ∧ x ∉ closedDiskNeighborhood)) ↔
    ((x ∈ cap ∧ x ∉ (openCap : Set Threefold.Space)) ∨
      (x ∈ closedDiskNeighborhood ∧ x ∉ interior closedDiskNeighborhood))
  constructor
  · rintro ⟨⟨hcap, hnotint⟩, hnotdiff⟩
    by_cases hopen : x ∈ (openCap : Set Threefold.Space)
    · right
      refine ⟨?_, hnotint⟩
      by_contra hn
      exact hnotdiff ⟨hopen, hn⟩
    · exact Or.inl ⟨hcap, hopen⟩
  · rintro (⟨hcap, hnotopen⟩ | ⟨hn, hnotint⟩)
    · exact ⟨⟨hcap, fun hi =>
        hnotopen (closedDiskNeighborhood_subset_openCap (interior_subset hi))⟩,
        fun h => hnotopen h.1⟩
    · exact ⟨⟨openCap_subset_cap (closedDiskNeighborhood_subset_openCap hn), hnotint⟩,
        fun h => h.2 hn⟩

theorem outerBoundary_subset_frontier_capComplement :
    outerBoundary ⊆ frontier capComplement := by
  rw [frontier_capComplement]
  exact subset_union_left

theorem innerBoundary_subset_frontier_capComplement :
    frontier closedDiskNeighborhood ⊆ frontier capComplement := by
  rw [frontier_capComplement]
  exact subset_union_right

/-- The already established standard sphere-product boundary map lands
on the genuine inner frontier of the actual cusp complement. -/
theorem standardBoundaryMap_mem_frontier_capComplement (p : StandardNormalBoundary) :
    standardBoundaryMap p ∈ frontier capComplement :=
  innerBoundary_subset_frontier_capComplement (standardBoundaryMap_mem_frontier p)

end Wikipedia.HopfProblem.CuspComplement
