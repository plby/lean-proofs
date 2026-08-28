import Wikipedia.HopfProblem.CuspComplementRadius
import Wikipedia.HopfProblem.CuspProper

/-!
# The actual compact cusp cap with its fixed normal disk removed

The cap is the literal original cusp sublevel at half the filling radius,
included into the original threefold.  Its compact complement of the
normal disk's interior retains both the original outer parameter level
and the already fixed inner frontier.  No product or handle model is
assigned to this region.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspComplement

open CuspCircleNormalTrivialization SpecialPeriods SpecialPeriods.Threefold

local notation "CD" => CuspGeometry.data

attribute [local instance] Threefold.space_t2Space

/-- A closed sublevel of the original cusp quotient parameter. -/
def localCap : Set CuspGeometry.LocalSpace :=
  {q | ‖CuspGeometry.parameter q‖ ≤ capRadius}

/-- The corresponding strict sublevel, in the original topology. -/
def localOpenCap : TopologicalSpace.Opens CuspGeometry.LocalSpace :=
  ⟨{q | ‖CuspGeometry.parameter q‖ < capRadius},
    isOpen_lt CuspGeometry.parameter_continuous.norm continuous_const⟩

theorem localCap_isCompact : IsCompact localCap := by
  have h : IsCompact (CuspQuotient.projection (CD).correction (CD).radius ⁻¹'
      Metric.closedBall 0 capRadius : Set CuspGeometry.LocalSpace) :=
    CuspQuotient.closedDisc_preimage_compact (CD).correction (CD).radius
    (CD).radius_pos (CD).radius_lt_one (CD).holomorphic (CD).smallDrift
    capRadius_pos capRadius_lt_cuspRadius
  have he : (CuspQuotient.projection (CD).correction (CD).radius ⁻¹'
      Metric.closedBall 0 capRadius : Set CuspGeometry.LocalSpace) = localCap := by
    ext q
    change dist (CuspGeometry.parameter q) 0 ≤ capRadius ↔
      ‖CuspGeometry.parameter q‖ ≤ capRadius
    rw [dist_zero_right]
  exact he ▸ h

/-- The actual closed cusp cap as a subset of the unchanged threefold. -/
def cap : Set Threefold.Space := CuspGeometry.inclusion '' localCap

/-- The literal strict cusp sublevel in the actual open cusp image. -/
def openCap : TopologicalSpace.Opens Threefold.Space :=
  ⟨CuspGeometry.inclusion '' (localOpenCap : Set CuspGeometry.LocalSpace),
    CuspGeometry.inclusion_openEmbedding.isOpenMap _ localOpenCap.isOpen⟩

theorem cap_isCompact : IsCompact cap :=
  localCap_isCompact.image CuspGeometry.inclusion_continuous

theorem openCap_subset_cap : (openCap : Set Threefold.Space) ⊆ cap := by
  rintro x ⟨q, hq, rfl⟩
  exact ⟨q, (show ‖CuspGeometry.parameter q‖ < capRadius from hq).le, rfl⟩

theorem openCap_subset_interior_cap : (openCap : Set Threefold.Space) ⊆ interior cap :=
  interior_maximal openCap_subset_cap openCap.isOpen

/-- The entire already fixed compact normal disk lies strictly inside
this particular original cusp sublevel. -/
theorem closedDiskNeighborhood_subset_openCap :
    closedDiskNeighborhood ⊆ openCap := by
  rintro x ⟨p, rfl⟩
  let q : CuspGeometry.LocalSpace := CuspQuotient.quotientMap (CD).correction (CD).radius
    (toTube (roundToSmall (closedProductIntoRound p)))
  have hq : CuspGeometry.inclusion q = closedProductMap p := rfl
  refine ⟨q, ?_, hq⟩
  change ‖CuspGeometry.parameter q‖ < capRadius
  rw [← CuspGeometry.cuspCoordinate_inclusion q, hq]
  exact closedProductMap_time_lt_capRadius p

theorem closedDiskNeighborhood_subset_interior_cap :
    closedDiskNeighborhood ⊆ interior cap :=
  closedDiskNeighborhood_subset_openCap.trans openCap_subset_interior_cap

/-- The actual compact cusp region left after deleting the normal disk's
interior; the genuine attaching frontier remains in this region. -/
def capComplement : Set Threefold.Space := cap \ interior closedDiskNeighborhood

theorem capComplement_isCompact : IsCompact capComplement :=
  cap_isCompact.inter_right isOpen_interior.isClosed_compl

theorem capComplement_subset_cap : capComplement ⊆ cap := fun _ hx => hx.1

theorem capComplement_not_mem_doubleCurve {x : Threefold.Space} (hx : x ∈ capComplement) :
    x ∉ CuspGeometry.doubleCurve 1 :=
  fun hcurve => hx.2 (doubleCurve_subset_interior_closedDiskNeighborhood hcurve)

/-- The outer mark uses the original cusp parameter, not a chosen
coordinate on a replacement boundary. -/
def outerBoundary : Set Threefold.Space :=
  CuspGeometry.inclusion '' {q | ‖CuspGeometry.parameter q‖ = capRadius}

theorem outerBoundary_time {x : Threefold.Space} (hx : x ∈ outerBoundary) :
    ‖CuspGeometry.cuspCoordinate x‖ = capRadius := by
  obtain ⟨q, hq, rfl⟩ := hx
  rw [CuspGeometry.cuspCoordinate_inclusion]
  exact hq

theorem outerBoundary_subset_cap : outerBoundary ⊆ cap := by
  rintro x ⟨q, hq, rfl⟩
  exact ⟨q, hq.le, rfl⟩

theorem outerBoundary_not_mem_closedDiskNeighborhood {x : Threefold.Space}
    (hx : x ∈ outerBoundary) : x ∉ closedDiskNeighborhood := by
  intro hn
  have hlt := closedDiskNeighborhood_time_lt_capRadius hn
  rw [outerBoundary_time hx] at hlt
  exact lt_irrefl _ hlt

theorem outerBoundary_subset_capComplement : outerBoundary ⊆ capComplement :=
  fun _ hx => ⟨outerBoundary_subset_cap hx,
    fun hn => outerBoundary_not_mem_closedDiskNeighborhood hx (interior_subset hn)⟩

/-- The inner mark is precisely the existing ambient frontier. -/
theorem innerBoundary_subset_capComplement :
    frontier closedDiskNeighborhood ⊆ capComplement := by
  intro x hx
  rw [closedDiskNeighborhood_isCompact.isClosed.frontier_eq] at hx
  exact ⟨interior_subset (closedDiskNeighborhood_subset_interior_cap hx.1), hx.2⟩

theorem innerBoundary_disjoint_outerBoundary :
    Disjoint (frontier closedDiskNeighborhood) outerBoundary := by
  apply Set.disjoint_left.mpr
  intro x hx ho
  exact outerBoundary_not_mem_closedDiskNeighborhood ho
    (closedDiskNeighborhood_isCompact.isClosed.frontier_subset hx)

end Wikipedia.HopfProblem.CuspComplement
