import Wikipedia.HopfProblem.ToricRayIncidence

/-!
# Local equations of the three edge-direction loci

Each unoriented edge direction selects one coordinate axis in a triangular
chart. Two different directions can meet only at its origin. The statements
use the actual chart-independent branch vertices and do not assume an
orbit--cone correspondence.
-/

noncomputable section

open Set
open scoped Matrix

namespace Wikipedia.HopfProblem.ToricFan.Triangle

open ToricCharts

/-- The coordinate left free by the two ray components along an edge. -/
def axisIndex (s : Triangle) (i : Fin 3) : Fin 3 := if s.upper then i else i.rev

theorem axisIndex_injective (s : Triangle) : Function.Injective s.axisIndex := by
  intro i j h
  cases hs : s.upper <;> fin_cases i <;> fin_cases j <;> simp_all [axisIndex]

def edgeStart (s : Triangle) (i : Fin 3) : Fin 3 :=
  if s.upper then ![1, 0, 1] i else ![0, 0, 2] i

def edgeEnd (s : Triangle) (i : Fin 3) : Fin 3 :=
  if s.upper then ![2, 2, 0] i else ![1, 2, 1] i

theorem axis_complement (s : Triangle) (i j : Fin 3) :
    j ≠ s.axisIndex i ↔ j = s.edgeStart i ∨ j = s.edgeEnd i := by
  cases hs : s.upper <;> fin_cases i <;> fin_cases j <;>
    simp [axisIndex, edgeStart, edgeEnd, hs]

theorem vertex_reference_shift (s : Triangle) (j : Fin 3) :
    s.vertex j = (⟨0, 0, s.upper⟩ : Triangle).vertex j + ![s.a, s.b] := by
  have hs : (⟨0, 0, s.upper⟩ : Triangle).shift ![s.a, s.b] = s := by
    ext <;> simp [shift]
  simpa only [hs] using vertex_shift (⟨0, 0, s.upper⟩ : Triangle) ![s.a, s.b] j

theorem vertices_edge_iff (s : Triangle) (i j k : Fin 3) :
    s.vertex k = s.vertex j + edgeDirection i ↔ j = s.edgeStart i ∧ k = s.edgeEnd i := by
  rw [vertex_reference_shift s k, vertex_reference_shift s j,
    add_right_comm _ ![s.a, s.b] (edgeDirection i), add_left_inj]
  cases hs : s.upper <;> fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [edgeStart, edgeEnd, hs, vertex, rays, edgeDirection, funext_iff,
      Fin.forall_fin_succ, Matrix.vecHead, Matrix.vecTail]

theorem chartBranches_edge_iff (s : Triangle) (z : CoordinateSpace 3) (i : Fin 3) :
    (∃ v ∈ chartBranches s z, v + edgeDirection i ∈ chartBranches s z) ↔
      ∃ j k : Fin 3, z j = 0 ∧ z k = 0 ∧ s.vertex k = s.vertex j + edgeDirection i := by
  constructor
  · rintro ⟨v, ⟨j, hj, rfl⟩, k, hk, he⟩
    exact ⟨j, k, hj, hk, he⟩
  · rintro ⟨j, k, hj, hk, he⟩
    exact ⟨s.vertex j, ⟨j, hj, rfl⟩, k, hk, he⟩

theorem chartBranches_edge_endpoints (s : Triangle) (z : CoordinateSpace 3) (i : Fin 3) :
    (∃ v ∈ chartBranches s z, v + edgeDirection i ∈ chartBranches s z) ↔
      z (s.edgeStart i) = 0 ∧ z (s.edgeEnd i) = 0 := by
  rw [chartBranches_edge_iff]
  constructor
  · rintro ⟨j, k, hj, hk, he⟩
    obtain ⟨rfl, rfl⟩ := (vertices_edge_iff s i j k).mp he
    exact ⟨hj, hk⟩
  · rintro ⟨hj, hk⟩
    exact ⟨s.edgeStart i, s.edgeEnd i, hj, hk,
      (vertices_edge_iff s i _ _).mpr ⟨rfl, rfl⟩⟩

theorem chartBranches_edge_axis (s : Triangle) (z : CoordinateSpace 3) (i : Fin 3) :
    (∃ v ∈ chartBranches s z, v + edgeDirection i ∈ chartBranches s z) ↔
      ∀ j : Fin 3, j ≠ s.axisIndex i → z j = 0 := by
  rw [chartBranches_edge_endpoints]
  constructor
  · rintro ⟨hstart, hend⟩ j hj
    obtain h | h := (axis_complement s i j).mp hj
    · rwa [h]
    · rwa [h]
  · intro h
    exact ⟨h _ ((axis_complement s i _).mpr (Or.inl rfl)),
      h _ ((axis_complement s i _).mpr (Or.inr rfl))⟩

theorem two_edge_directions_force_origin (s : Triangle) (z : CoordinateSpace 3)
    (i j : Fin 3) (hij : i ≠ j)
    (hi : ∃ v ∈ chartBranches s z, v + edgeDirection i ∈ chartBranches s z)
    (hj : ∃ v ∈ chartBranches s z, v + edgeDirection j ∈ chartBranches s z) : z = 0 := by
  have hi' := (chartBranches_edge_axis s z i).mp hi
  have hj' := (chartBranches_edge_axis s z j).mp hj
  ext k
  by_cases hk : k = s.axisIndex i
  · exact hj' k (fun h => hij (axisIndex_injective s (hk.symm.trans h)))
  · exact hi' k hk

theorem origin_has_edge_direction (s : Triangle) (i : Fin 3) :
    ∃ v ∈ chartBranches s (0 : CoordinateSpace 3),
      v + edgeDirection i ∈ chartBranches s 0 :=
  (chartBranches_edge_axis s 0 i).mpr (fun _ _ => rfl)

end Wikipedia.HopfProblem.ToricFan.Triangle
