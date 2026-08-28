import Wikipedia.NoExoticSixSphere.CompactChartRegion
import Wikipedia.NoExoticSixSphere.HalfLineCompactIntervals
import Mathlib.Topology.Order.IntermediateValue

/-!
# Actual compact interval neighborhoods in a half-line chart

The closed neighborhood is the image of an actual nondegenerate closed
interval under the inverse chart. Its interior region is open in the original
space, its closure is exactly that closed neighborhood, and its frontier lies
in the two distinct endpoint images. No abstract interval is substituted for
the original topology.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.CurveDecomposition

open InvolutionQuotient HalfLineIntervals

structure IntervalNeighborhood (X : Type*) [TopologicalSpace X] where
  chart : OpenPartialHomeomorph X HalfLine
  left : HalfLine
  right : HalfLine
  lt : left < right
  interval_target : Icc left right ⊆ chart.target

variable {X : Type*} [TopologicalSpace X]

def IntervalNeighborhood.openSet (d : IntervalNeighborhood X) : Set X :=
  CurveChart.region d.chart (interior (Icc d.left d.right))

def IntervalNeighborhood.closedSet (d : IntervalNeighborhood X) : Set X :=
  d.chart.symm '' Icc d.left d.right

def IntervalNeighborhood.endpoints (d : IntervalNeighborhood X) : Set X :=
  {d.chart.symm d.left, d.chart.symm d.right}

theorem IntervalNeighborhood.openSet_subset_closedSet (d : IntervalNeighborhood X) :
    d.openSet ⊆ d.closedSet := by
  rw [IntervalNeighborhood.openSet,
    CurveChart.region_eq_image d.chart (interior_subset.trans d.interval_target)]
  exact image_mono interior_subset

theorem IntervalNeighborhood.isOpen_openSet (d : IntervalNeighborhood X) :
    IsOpen d.openSet := CurveChart.isOpen_region d.chart isOpen_interior

theorem IntervalNeighborhood.isCompact_closedSet (d : IntervalNeighborhood X) :
    IsCompact d.closedSet :=
  (isCompact_interval d.left d.right).image_of_continuousOn
    (d.chart.continuousOn_symm.mono d.interval_target)

theorem IntervalNeighborhood.closedSet_subset_source (d : IntervalNeighborhood X) :
    d.closedSet ⊆ d.chart.source := by
  rintro x ⟨y, hy, rfl⟩
  exact d.chart.map_target (d.interval_target hy)

theorem IntervalNeighborhood.closure_openSet [T2Space X] (d : IntervalNeighborhood X) :
    closure d.openSet = d.closedSet := by
  have hc : IsCompact (closure (interior (Icc d.left d.right))) := by
    rw [closure_interior_interval d.lt]
    exact isCompact_interval _ _
  have ht : closure (interior (Icc d.left d.right)) ⊆ d.chart.target := by
    rw [closure_interior_interval d.lt]
    exact d.interval_target
  rw [IntervalNeighborhood.openSet, CurveChart.closure_region d.chart hc ht,
    closure_interior_interval d.lt]
  rfl

theorem IntervalNeighborhood.frontier_subset_endpoints [T2Space X]
    (d : IntervalNeighborhood X) : frontier d.openSet ⊆ d.endpoints := by
  have hc : IsCompact (closure (interior (Icc d.left d.right))) := by
    rw [closure_interior_interval d.lt]
    exact isCompact_interval _ _
  have ht : closure (interior (Icc d.left d.right)) ⊆ d.chart.target := by
    rw [closure_interior_interval d.lt]
    exact d.interval_target
  rw [IntervalNeighborhood.openSet, CurveChart.frontier_region d.chart hc ht]
  simpa only [image_pair, IntervalNeighborhood.endpoints] using image_mono
    (f := d.chart.symm) (frontier_interior_interval_subset d.lt)

theorem IntervalNeighborhood.endpoints_distinct (d : IntervalNeighborhood X) :
    d.chart.symm d.left ≠ d.chart.symm d.right := by
  intro he
  exact d.lt.ne (d.chart.symm.injOn (d.interval_target ⟨le_rfl, d.lt.le⟩)
    (d.interval_target ⟨d.lt.le, le_rfl⟩) he)

def IntervalNeighborhood.intervalMap (d : IntervalNeighborhood X) : Icc d.left d.right → X :=
  fun t ↦ d.chart.symm t.val

theorem IntervalNeighborhood.isClosedEmbedding_intervalMap [T2Space X]
    (d : IntervalNeighborhood X) : IsClosedEmbedding d.intervalMap := by
  let := isCompact_iff_compactSpace.mp (isCompact_interval d.left d.right)
  have hc : Continuous d.intervalMap :=
    (d.chart.continuousOn_symm.mono d.interval_target).domRestrict
  apply hc.isClosedEmbedding
  intro s t he
  exact Subtype.ext (d.chart.symm.injOn (d.interval_target s.property)
    (d.interval_target t.property) he)

theorem exists_interval_neighborhood (e : OpenPartialHomeomorph X HalfLine)
    (x : X) (hx : x ∈ e.source) :
    ∃ d : IntervalNeighborhood X, d.chart = e ∧ x ∈ d.openSet := by
  obtain ⟨a, b, hab, hxI, hI⟩ :=
    exists_interval_in_open e.open_target (e x) (e.map_source hx)
  exact ⟨⟨e, a, b, hab, hI⟩, rfl, hx, hxI⟩

end NoExoticSixSphere.CurveDecomposition
