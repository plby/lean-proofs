import Wikipedia.NoExoticSixSphere.CurveCutBranches

/-!
# A cut neighborhood is exhausted by its actual branches and center

If the compact neighborhood contains no other cut and chart-zero points are
cuts, its puncture is exactly the disjoint union of the two actual branches.
The branches avoid every cut. Their nonempty sides genuinely approach the
center in the original topology, by the exact compact chart-closure formula.
-/

open Set Function Topology

namespace NoExoticSixSphere.CurveDecomposition

open HalfLineIntervals

variable {X : Type*} [TopologicalSpace X]

theorem IntervalNeighborhood.punctured_eq_branches (d : IntervalNeighborhood X) (v : X)
    (hv : v ∈ d.openSet) (S : Set X)
    (hcut : ∀ y ∈ d.closedSet, y ∈ S → y = v)
    (hzero : ∀ y ∈ d.chart.source, (d.chart y).val = 0 → y ∈ S) :
    d.openSet \ {v} = d.leftBranch v ∪ d.rightBranch v := by
  ext y
  constructor
  · rintro ⟨hy, hyne⟩
    have hpos : 0 < (d.chart y).val := by
      apply lt_of_le_of_ne (d.chart y).property
      intro he
      exact hyne (hcut y (d.openSet_subset_closedSet hy) (hzero y hy.1 he.symm))
    have hleft := left_lt_interior_interval hy.2 hpos
    have hright := interior_interval_lt_right hy.2
    have hne : d.chart y ≠ d.chart v := fun he ↦ hyne (d.chart.injOn hy.1 hv.1 he)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨hy.1, hleft, hlt⟩
    · exact Or.inr ⟨hy.1, hgt, hright⟩
  · rintro (hy | hy)
    · refine ⟨d.leftBranch_subset_openSet v hv hy, ?_⟩
      intro he
      exact d.not_mem_leftBranch v (he ▸ hy)
    · refine ⟨d.rightBranch_subset_openSet v hv hy, ?_⟩
      intro he
      exact d.not_mem_rightBranch v (he ▸ hy)

theorem IntervalNeighborhood.leftBranch_subset_compl (d : IntervalNeighborhood X) (v : X)
    (hv : v ∈ d.openSet) (S : Set X) (hcut : ∀ y ∈ d.closedSet, y ∈ S → y = v) :
    d.leftBranch v ⊆ Sᶜ := by
  intro y hy hyS
  have he := hcut y (d.openSet_subset_closedSet (d.leftBranch_subset_openSet v hv hy)) hyS
  exact d.not_mem_leftBranch v (he ▸ hy)

theorem IntervalNeighborhood.rightBranch_subset_compl (d : IntervalNeighborhood X) (v : X)
    (hv : v ∈ d.openSet) (S : Set X) (hcut : ∀ y ∈ d.closedSet, y ∈ S → y = v) :
    d.rightBranch v ⊆ Sᶜ := by
  intro y hy hyS
  have he := hcut y (d.openSet_subset_closedSet (d.rightBranch_subset_openSet v hv hy)) hyS
  exact d.not_mem_rightBranch v (he ▸ hy)

theorem IntervalNeighborhood.center_mem_closure_leftBranch [T2Space X]
    (d : IntervalNeighborhood X) (v : X) (hv : v ∈ d.openSet)
    (hpos : 0 < (d.chart v).val) : v ∈ closure (d.leftBranch v) := by
  have hlt := left_lt_interior_interval hv.2 hpos
  have hc : IsCompact (closure (Ioo d.left (d.chart v))) := by
    rw [closure_Ioo hlt.ne]
    exact isCompact_interval _ _
  have ht : closure (Ioo d.left (d.chart v)) ⊆ d.chart.target := by
    rw [closure_Ioo hlt.ne]
    exact d.leftInterval_target v hv
  rw [IntervalNeighborhood.leftBranch, CurveChart.closure_region d.chart hc ht,
    closure_Ioo hlt.ne]
  exact ⟨d.chart v, ⟨hlt.le, le_rfl⟩, d.chart.left_inv hv.1⟩

theorem IntervalNeighborhood.center_mem_closure_rightBranch [T2Space X]
    (d : IntervalNeighborhood X) (v : X) (hv : v ∈ d.openSet) :
    v ∈ closure (d.rightBranch v) := by
  have hlt := interior_interval_lt_right hv.2
  have hc : IsCompact (closure (Ioo (d.chart v) d.right)) := by
    rw [closure_Ioo hlt.ne]
    exact isCompact_interval _ _
  have ht : closure (Ioo (d.chart v) d.right) ⊆ d.chart.target := by
    rw [closure_Ioo hlt.ne]
    exact d.rightInterval_target v hv
  rw [IntervalNeighborhood.rightBranch, CurveChart.closure_region d.chart hc ht,
    closure_Ioo hlt.ne]
  exact ⟨d.chart v, ⟨le_rfl, hlt.le⟩, d.chart.left_inv hv.1⟩

end NoExoticSixSphere.CurveDecomposition
