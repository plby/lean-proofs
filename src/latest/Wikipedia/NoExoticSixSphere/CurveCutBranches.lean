import Wikipedia.NoExoticSixSphere.SmallCurveCutNeighborhood
import Wikipedia.NoExoticSixSphere.HalfLineIntervalBranches

/-!
# The actual left and right branches near a cut

Branches are inverse images of genuine open subintervals in the original
half-line chart. The right branch is always nonempty and connected. The left
branch is connected and nonempty at a positive coordinate, and is empty at
zero. Both lie in the original open interval neighborhood and are disjoint.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.CurveDecomposition

open InvolutionQuotient HalfLineIntervals

variable {X : Type*} [TopologicalSpace X]

def IntervalNeighborhood.leftBranch (d : IntervalNeighborhood X) (v : X) : Set X :=
  CurveChart.region d.chart (Ioo d.left (d.chart v))

def IntervalNeighborhood.rightBranch (d : IntervalNeighborhood X) (v : X) : Set X :=
  CurveChart.region d.chart (Ioo (d.chart v) d.right)

theorem IntervalNeighborhood.leftInterval_target (d : IntervalNeighborhood X) (v : X)
    (hv : v ∈ d.openSet) : Icc d.left (d.chart v) ⊆ d.chart.target := by
  intro z hz
  exact d.interval_target ⟨hz.1, hz.2.trans (interior_subset hv.2).2⟩

theorem IntervalNeighborhood.rightInterval_target (d : IntervalNeighborhood X) (v : X)
    (hv : v ∈ d.openSet) : Icc (d.chart v) d.right ⊆ d.chart.target := by
  intro z hz
  exact d.interval_target ⟨(interior_subset hv.2).1.trans hz.1, hz.2⟩

theorem IntervalNeighborhood.leftBranch_subset_openSet (d : IntervalNeighborhood X) (v : X)
    (hv : v ∈ d.openSet) : d.leftBranch v ⊆ d.openSet := by
  intro y hy
  refine ⟨hy.1, ?_⟩
  apply interior_maximal Ioo_subset_Icc_self isOpen_Ioo
  exact ⟨hy.2.1, hy.2.2.trans_le (interior_subset hv.2).2⟩

theorem IntervalNeighborhood.rightBranch_subset_openSet (d : IntervalNeighborhood X) (v : X)
    (hv : v ∈ d.openSet) : d.rightBranch v ⊆ d.openSet := by
  intro y hy
  refine ⟨hy.1, ?_⟩
  apply interior_maximal Ioo_subset_Icc_self isOpen_Ioo
  exact ⟨(interior_subset hv.2).1.trans_lt hy.2.1, hy.2.2⟩

theorem IntervalNeighborhood.branches_disjoint (d : IntervalNeighborhood X) (v : X) :
    Disjoint (d.leftBranch v) (d.rightBranch v) := by
  apply disjoint_left.mpr
  intro y hl hr
  exact (not_lt_of_gt hl.2.2) hr.2.1

theorem IntervalNeighborhood.not_mem_leftBranch (d : IntervalNeighborhood X) (v : X) :
    v ∉ d.leftBranch v := fun h ↦ lt_irrefl _ h.2.2

theorem IntervalNeighborhood.not_mem_rightBranch (d : IntervalNeighborhood X) (v : X) :
    v ∉ d.rightBranch v := fun h ↦ lt_irrefl _ h.2.1

theorem IntervalNeighborhood.isOpen_leftBranch (d : IntervalNeighborhood X) (v : X) :
    IsOpen (d.leftBranch v) := CurveChart.isOpen_region d.chart isOpen_Ioo

theorem IntervalNeighborhood.isOpen_rightBranch (d : IntervalNeighborhood X) (v : X) :
    IsOpen (d.rightBranch v) := CurveChart.isOpen_region d.chart isOpen_Ioo

theorem IntervalNeighborhood.isConnected_leftBranch (d : IntervalNeighborhood X) (v : X)
    (hv : v ∈ d.openSet) (hpos : 0 < (d.chart v).val) : IsConnected (d.leftBranch v) := by
  have hlt := left_lt_interior_interval hv.2 hpos
  have ht : Ioo d.left (d.chart v) ⊆ d.chart.target :=
    Ioo_subset_Icc_self.trans (d.leftInterval_target v hv)
  rw [IntervalNeighborhood.leftBranch, CurveChart.region_eq_image d.chart ht]
  exact (isConnected_open_interval hlt).image d.chart.symm (d.chart.continuousOn_symm.mono ht)

theorem IntervalNeighborhood.isPreconnected_leftBranch (d : IntervalNeighborhood X) (v : X)
    (hv : v ∈ d.openSet) : IsPreconnected (d.leftBranch v) := by
  have ht : Ioo d.left (d.chart v) ⊆ d.chart.target :=
    Ioo_subset_Icc_self.trans (d.leftInterval_target v hv)
  rw [IntervalNeighborhood.leftBranch, CurveChart.region_eq_image d.chart ht]
  exact (isPreconnected_open_interval _ _).image d.chart.symm
    (d.chart.continuousOn_symm.mono ht)

theorem IntervalNeighborhood.isConnected_rightBranch (d : IntervalNeighborhood X) (v : X)
    (hv : v ∈ d.openSet) : IsConnected (d.rightBranch v) := by
  have hlt := interior_interval_lt_right hv.2
  have ht : Ioo (d.chart v) d.right ⊆ d.chart.target :=
    Ioo_subset_Icc_self.trans (d.rightInterval_target v hv)
  rw [IntervalNeighborhood.rightBranch, CurveChart.region_eq_image d.chart ht]
  exact (isConnected_open_interval hlt).image d.chart.symm (d.chart.continuousOn_symm.mono ht)

theorem IntervalNeighborhood.leftBranch_eq_empty (d : IntervalNeighborhood X) (v : X)
    (hz : (d.chart v).val = 0) : d.leftBranch v = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hlt : (d.chart y).val < (d.chart v).val := hy.2.2
  rw [hz] at hlt
  exact not_lt_of_ge (d.chart y).property hlt

end NoExoticSixSphere.CurveDecomposition
