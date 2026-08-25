import StackExchange.Puzzling139335.Definitions
import StackExchange.Puzzling139335.CornerCounting

/-!
# Corner incidences of a square dissection

This file connects the finite incidence counting with the geometric definition
of a dissection.  The exclusion of opposite corners remains an explicit
hypothesis; it is not added to the definition of a dissection.
-/

open Set
open scoped BigOperators

namespace Puzzling139335

noncomputable section

/-- A square corner is never an interior point of the square. -/
theorem corner_not_mem_interior_unitSquare (j : Fin 4) :
    corner j ∉ interior unitSquare := by
  intro hj
  let f : ℝ → Plane := fun x => !₂[x, corner j 1]
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have hOpen : IsOpen (f ⁻¹' interior unitSquare) := isOpen_interior.preimage hf
  have hSubset : f ⁻¹' interior unitSquare ⊆ Icc (0 : ℝ) 1 := by
    intro x hx
    exact (interior_subset hx).1
  have hPoint : f (corner j 0) = corner j := by
    ext k
    fin_cases k <;> rfl
  have hMem : corner j 0 ∈ f ⁻¹' interior unitSquare := by
    change f (corner j 0) ∈ interior unitSquare
    rwa [hPoint]
  have hInterval := (hOpen.subset_interior_iff.mpr hSubset) hMem
  rw [interior_Icc] at hInterval
  by_cases hx : j = 1 ∨ j = 2 <;> simp [corner, hx] at hInterval

/-- A corner in any subset of the square lies on that subset's frontier.
Closedness is not needed: membership already implies membership in its closure. -/
theorem corner_mem_frontier_of_subset {P : Set Plane} (hP : P ⊆ unitSquare)
    {j : Fin 4} (hj : corner j ∈ P) : corner j ∈ frontier P := by
  refine ⟨subset_closure hj, ?_⟩
  intro hInterior
  exact corner_not_mem_interior_unitSquare j (interior_mono hP hInterior)

namespace SquareDissection

/-- Incidence means actual membership of a square corner in a piece. -/
def incidence (d : SquareDissection) : CornerCounting.Incidence :=
  fun i j => corner j ∈ d.piece i

@[simp] theorem incidence_iff (d : SquareDissection) (i j : Fin 4) :
    d.incidence i j ↔ corner j ∈ d.piece i := Iff.rfl

/-- Every square corner is incident with at least one piece. -/
theorem incidence_covers (d : SquareDissection) (j : Fin 4) :
    ∃ i, d.incidence i j :=
  d.exists_piece_mem (corner_mem_unitSquare j)

/-- The number of square corners in a piece. -/
def tileCornerCount (d : SquareDissection) (i : Fin 4) : ℕ := by
  classical
  exact CornerCounting.tileDegree d.incidence i

/-- The number of pieces containing a square corner. -/
def cornerTileCount (d : SquareDissection) (j : Fin 4) : ℕ := by
  classical
  exact CornerCounting.cornerMultiplicity d.incidence j

/-- The total number of incidences between pieces and square corners. -/
def cornerIncidenceCount (d : SquareDissection) : ℕ := by
  classical
  exact CornerCounting.totalIncidences d.incidence

theorem cornerTileCount_pos (d : SquareDissection) (j : Fin 4) :
    0 < d.cornerTileCount j := by
  classical
  exact CornerCounting.cornerMultiplicity_pos d.incidence j (d.incidence_covers j)

theorem cornerTileCount_le_four (d : SquareDissection) (j : Fin 4) :
    d.cornerTileCount j ≤ 4 := by
  classical
  exact CornerCounting.cornerMultiplicity_le_four d.incidence j

theorem cornerIncidenceCount_eq_sum_tileCornerCount (d : SquareDissection) :
    d.cornerIncidenceCount = ∑ i, d.tileCornerCount i := rfl

theorem cornerIncidenceCount_eq_sum_cornerTileCount (d : SquareDissection) :
    d.cornerIncidenceCount = ∑ j, d.cornerTileCount j := by
  classical
  exact CornerCounting.incidence_double_count d.incidence

theorem corner_not_mem_interior_piece (d : SquareDissection) (i j : Fin 4) :
    corner j ∉ interior (d.piece i) := by
  intro hj
  exact corner_not_mem_interior_unitSquare j (interior_mono (d.piece_subset i) hj)

/-- A square corner belonging to a piece belongs to its frontier. -/
theorem corner_mem_frontier (d : SquareDissection) {i j : Fin 4}
    (hj : corner j ∈ d.piece i) : corner j ∈ frontier (d.piece i) :=
  corner_mem_frontier_of_subset (d.piece_subset i) hj

/-- For the closed Jordan pieces, corner membership and frontier membership
are equivalent. -/
theorem corner_mem_frontier_iff (d : SquareDissection) (i j : Fin 4) :
    corner j ∈ frontier (d.piece i) ↔ corner j ∈ d.piece i := by
  constructor
  · have hClosed : IsClosed (d.piece i) := by
      obtain ⟨C, _, hPiece⟩ := d.jordan i
      rw [hPiece]
      exact isClosed_closure
    intro hj
    exact hClosed.frontier_subset hj
  · exact d.corner_mem_frontier

/-- Excluding opposite corners bounds the number of corners in each piece. -/
theorem tileCornerCount_le_two_of_no_opposite (d : SquareDissection)
    (hOpposite : ∀ i j, ¬ (corner j ∈ d.piece i ∧ corner (j + 2) ∈ d.piece i))
    (i : Fin 4) : d.tileCornerCount i ≤ 2 := by
  classical
  change (Finset.univ.filter (d.incidence i)).card ≤ 2
  apply CornerCounting.card_le_two_of_no_opposite
  intro j
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, incidence] using hOpposite i j

/-- The geometric incidence total lies between four and eight whenever no
piece contains an opposite pair of square corners. -/
theorem cornerIncidenceCount_bounds_of_no_opposite (d : SquareDissection)
    (hOpposite : ∀ i j, ¬ (corner j ∈ d.piece i ∧ corner (j + 2) ∈ d.piece i)) :
    4 ≤ d.cornerIncidenceCount ∧ d.cornerIncidenceCount ≤ 8 := by
  classical
  apply CornerCounting.totalIncidences_bounds_of_cover
  · exact d.tileCornerCount_le_two_of_no_opposite hOpposite
  · exact d.incidence_covers

end SquareDissection

end

end Puzzling139335
