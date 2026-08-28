import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedExtensionBasic
import Mathlib.Topology.Order.Lattice

/-!
# The least barycentric coordinate

The continuous minimum of the finitely many coordinates detects exactly
the union of the actual faces of the standard simplex.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

/-- The least of the actual barycentric coordinates. -/
def minimumCoordinate {n : ℕ} (s : Simplex n) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => s i)

theorem minimumCoordinate_nonneg {n : ℕ} (s : Simplex n) :
    0 ≤ minimumCoordinate s :=
  Finset.le_inf' _ _ fun i _ => stdSimplex.zero_le s i

theorem minimumCoordinate_le {n : ℕ} (s : Simplex n) (i : Fin (n + 1)) :
    minimumCoordinate s ≤ s i :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem exists_coordinate_eq_minimum {n : ℕ} (s : Simplex n) :
    ∃ i : Fin (n + 1), s i = minimumCoordinate s := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i => s i)
  exact ⟨i, hi.symm⟩

theorem continuous_minimumCoordinate (n : ℕ) :
    Continuous (minimumCoordinate (n := n)) :=
  Continuous.finset_inf'_apply _ fun i _ =>
    (continuous_apply i).comp continuous_subtype_val

theorem minimumCoordinate_eq_zero_of_mem_boundary {n : ℕ} {s : Simplex n}
    (hs : s ∈ simplexBoundary n) : minimumCoordinate s = 0 := by
  obtain ⟨i, hi⟩ := hs
  exact le_antisymm (hi ▸ minimumCoordinate_le s i) (minimumCoordinate_nonneg s)

theorem mem_boundary_iff_minimumCoordinate_eq_zero {n : ℕ} (s : Simplex n) :
    s ∈ simplexBoundary n ↔ minimumCoordinate s = 0 := by
  refine ⟨minimumCoordinate_eq_zero_of_mem_boundary, ?_⟩
  intro hs
  obtain ⟨i, hi⟩ := exists_coordinate_eq_minimum s
  exact ⟨i, hi.trans hs⟩

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
