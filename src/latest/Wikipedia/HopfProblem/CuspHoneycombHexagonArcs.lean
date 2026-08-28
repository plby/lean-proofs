import Wikipedia.HopfProblem.CuspHoneycombHexagon
import Wikipedia.HopfProblem.CuspHoneycombHexagonBoundary

/-!
# The six actual positive component intersections are boundary arcs

The interval parametrizations below have values in the literal
neighboring-component intersections. Their endpoints are the original
toric all-zero triple points. The intersection pattern is the six-cycle.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace Wikipedia.HopfProblem.CuspHoneycombHexagon

/-- An actual boundary arc, parametrized from the preceding toric triple
point to the current one. -/
def positiveBoundaryArc (k : Fin 6) : unitInterval ≃ₜ positiveBoundary k :=
  (sideIntervalHomeomorph k).trans (positiveBoundaryHexagonHomeomorph k).symm

/-- The arc is affine in the explicit hexagon coordinates. -/
@[simp] theorem positiveBoundaryArc_hexagon (k : Fin 6) (t : unitInterval) :
    (positiveE0HexagonHomeomorph (positiveBoundaryArc k t).1 : Plane) =
      (1 - (t : ℝ)) • vertex (k - 1) + (t : ℝ) • vertex k := by
  change (positiveBoundaryHexagonHomeomorph k
    ((positiveBoundaryHexagonHomeomorph k).symm (sideIntervalHomeomorph k t)) : Plane) = _
  rw [Homeomorph.apply_symm_apply]
  exact sideIntervalHomeomorph_apply k t

@[simp] theorem positiveBoundaryArc_zero (k : Fin 6) :
    (positiveBoundaryArc k 0).1 = squarePoint (k - 1) cornerZero := by
  apply positiveE0HexagonHomeomorph.injective
  apply Subtype.ext
  rw [positiveBoundaryArc_hexagon, positiveE0HexagonHomeomorph_cornerZero]
  simp

@[simp] theorem positiveBoundaryArc_one (k : Fin 6) :
    (positiveBoundaryArc k 1).1 = squarePoint k cornerZero := by
  apply positiveE0HexagonHomeomorph.injective
  apply Subtype.ext
  rw [positiveBoundaryArc_hexagon, positiveE0HexagonHomeomorph_cornerZero]
  simp

@[simp] theorem positiveBoundaryArc_zero_coe (k : Fin 6) :
    (((positiveBoundaryArc k 0).1 : ToricSpace.rayDivisor 0) : ToricSpace.Space) =
      ToricSpace.inclusion (ToricComponent.zeroTriangle (k - 1)) 0 := by
  rw [positiveBoundaryArc_zero, squarePoint_cornerZero_coe]

@[simp] theorem positiveBoundaryArc_one_coe (k : Fin 6) :
    (((positiveBoundaryArc k 1).1 : ToricSpace.rayDivisor 0) : ToricSpace.Space) =
      ToricSpace.inclusion (ToricComponent.zeroTriangle k) 0 := by
  rw [positiveBoundaryArc_one, squarePoint_cornerZero_coe]

theorem positiveBoundaryArc_next_endpoint (k : Fin 6) :
    (positiveBoundaryArc k 1).1 = (positiveBoundaryArc (k + 1) 0).1 := by
  rw [positiveBoundaryArc_one, positiveBoundaryArc_zero, add_sub_cancel_right]

/-- Consecutive actual component intersections meet only at their actual
toric triple point. -/
theorem positiveBoundary_inter_next (k : Fin 6) :
    positiveBoundary k ∩ positiveBoundary (k + 1) = {squarePoint k cornerZero} := by
  ext x
  constructor
  · intro hx
    have hy : (positiveE0HexagonHomeomorph x : Plane) ∈ side k ∩ side (k + 1) :=
      ⟨(positiveE0HexagonHomeomorph_mem_side_iff x k).mpr hx.1,
        (positiveE0HexagonHomeomorph_mem_side_iff x (k + 1)).mpr hx.2⟩
    rw [side_inter_next, Set.mem_singleton_iff] at hy
    change x = squarePoint k cornerZero
    apply positiveE0HexagonHomeomorph.injective
    apply Subtype.ext
    exact hy.trans (positiveE0HexagonHomeomorph_cornerZero k).symm
  · intro hx
    have hx' : x = squarePoint k cornerZero := hx
    subst x
    exact ⟨(squarePoint_cornerZero_mem_positiveBoundary_iff k k).mpr (Or.inl rfl),
      (squarePoint_cornerZero_mem_positiveBoundary_iff k (k + 1)).mpr (Or.inr rfl)⟩

/-- Distinct nonadjacent actual boundary arcs have no additional intersections. -/
theorem positiveBoundary_disjoint_nonadjacent {i j : Fin 6}
    (hij : i ≠ j) (hnext : j ≠ i + 1) (hprev : i ≠ j + 1) :
    Disjoint (positiveBoundary i) (positiveBoundary j) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact Set.disjoint_left.mp (side_disjoint_nonadjacent hij hnext hprev)
    ((positiveE0HexagonHomeomorph_mem_side_iff x i).mpr hx)
    ((positiveE0HexagonHomeomorph_mem_side_iff x j).mpr hy)

end Wikipedia.HopfProblem.CuspHoneycombHexagon
