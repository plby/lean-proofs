import StackExchange.Puzzling139335.DissectionTopology

/-!
# Local coverage by the two pieces incident at a corner

The neighborhood is obtained from closedness of the other pieces.  A boundary
point of one member lying inside the square must also lie on the other member's
boundary.  Both statements concern the actual pieces.
-/

open Set Metric

namespace Puzzling139335

theorem SquareDissection.two_piece_relative_neighborhood (d : SquareDissection)
    {p : Plane} {i k : Fin 4}
    (hother : ∀ j, j ≠ i → j ≠ k → p ∉ d.piece j) :
    ∃ ε : ℝ, 0 < ε ∧ ball p ε ∩ unitSquare ⊆ d.piece i ∪ d.piece k := by
  classical
  let U : Set Plane := ⋂ j : Fin 4,
    if j = i ∨ j = k then Set.univ else (d.piece j)ᶜ
  have hU : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro j
    split_ifs
    · exact isOpen_univ
    · exact (d.jordan j).isClosed.isOpen_compl
  have hpU : p ∈ U := by
    apply mem_iInter.mpr
    intro j
    split_ifs with hj
    · trivial
    · exact hother j (fun h => hj (Or.inl h)) (fun h => hj (Or.inr h))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hpU)
  refine ⟨ε, hε, ?_⟩
  intro x hx
  obtain ⟨j, hj⟩ := d.exists_piece_mem hx.2
  by_cases hji : j = i
  · exact Or.inl (hji ▸ hj)
  by_cases hjk : j = k
  · exact Or.inr (hjk ▸ hj)
  have hxU : x ∈ U := hball hx.1
  have hxnot : x ∉ d.piece j := by
    change x ∈ (d.piece j)ᶜ
    simpa only [if_neg (not_or.mpr ⟨hji, hjk⟩)] using mem_iInter.mp hxU j
  exact False.elim (hxnot hj)

namespace DoubleCorner

/-- A local two-piece cover leaves no isolated boundary point of one piece
in the ambient interior: the closed other piece must contain that point. -/
theorem mem_other_of_frontier_of_local_cover
    {P Q : Set Plane} (hP : IsClosed P) {v x : Plane} {ε : ℝ}
    (hcover : ball v ε ∩ unitSquare ⊆ P ∪ Q)
    (hxball : x ∈ ball v ε) (hxSquare : x ∈ interior unitSquare)
    (hx : x ∈ frontier Q) : x ∈ P := by
  by_contra hxP
  let U : Set Plane := ball v ε ∩ interior unitSquare ∩ Pᶜ
  have hU : IsOpen U := (isOpen_ball.inter isOpen_interior).inter hP.isOpen_compl
  have hxU : x ∈ U := ⟨⟨hxball, hxSquare⟩, hxP⟩
  have hUQ : U ⊆ Q := by
    intro y hy
    rcases hcover ⟨hy.1.1, interior_subset hy.1.2⟩ with hyP | hyQ
    · exact False.elim (hy.2 hyP)
    · exact hyQ
  have hxint : x ∈ interior Q := by
    apply interior_mono hUQ
    rw [hU.interior_eq]
    exact hxU
  exact hx.2 hxint

/-- An internal boundary point of either member of a local two-piece cover
belongs to both boundaries. -/
theorem frontier_switch_of_local_cover
    {P Q : Set Plane} (hP : IsClosed P) (hQ : IsClosed Q)
    (hdis : Disjoint (interior P) Q) {v x : Plane} {ε : ℝ}
    (hcover : ball v ε ∩ unitSquare ⊆ P ∪ Q)
    (hxball : x ∈ ball v ε) (hxSquare : x ∈ interior unitSquare)
    (hx : x ∈ frontier Q) : x ∈ frontier P := by
  rw [hP.frontier_eq]
  refine ⟨mem_other_of_frontier_of_local_cover hP hcover hxball hxSquare hx, ?_⟩
  intro hxint
  exact Set.disjoint_left.mp hdis hxint (hQ.closure_eq ▸ hx.1)

end DoubleCorner

end Puzzling139335
