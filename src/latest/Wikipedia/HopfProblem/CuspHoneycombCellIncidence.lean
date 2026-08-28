import Wikipedia.HopfProblem.CuspHoneycombCompatibleCell
import Wikipedia.HopfProblem.ToricRayIncidence

/-!
# Incidence of the compatible zero-cell map with every component

The six boundary formulas give all component incidences, because both
the actual ray divisor and the literal planar cell meet only their six
lattice neighbours.  This identifies membership in every translated
cell without assuming a global honeycomb map.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.ToricFan

open ToricComponent

/-- The source's cyclic hexagon rays enumerate exactly the six signed
edge directions of the triangular fan. -/
theorem areAdjacent_iff_hexagonRay (v w : Fin 2 → ℤ) :
    AreAdjacent v w ↔ ∃ k : Fin 6, w - v = hexagonRay k := by
  have hedges : ∀ i : Fin 3, ∃ k : Fin 6, edgeDirection i = hexagonRay k := by
    intro i
    fin_cases i <;> decide
  have hrays : ∀ k : Fin 6, ∃ i : Fin 3,
      hexagonRay k = edgeDirection i ∨ hexagonRay k = -edgeDirection i := by
    intro k
    fin_cases k <;> decide
  constructor
  · rintro ⟨i, hi | hi⟩
    · obtain ⟨k, hk⟩ := hedges i
      exact ⟨k, hi.trans hk⟩
    · obtain ⟨k, hk⟩ := hedges i
      refine ⟨k + 3, hi.trans ?_⟩
      rw [hk, hexagonRay_opposite]
  · rintro ⟨k, hk⟩
    obtain ⟨i, hi | hi⟩ := hrays k
    · exact ⟨i, Or.inl (hk.trans hi)⟩
    · exact ⟨i, Or.inr (hk.trans hi)⟩

end Wikipedia.HopfProblem.ToricFan

namespace Wikipedia.HopfProblem.CuspHoneycombTiling

open ToricComponent ToricFan

theorem baseCell_inter_cell_nonempty_iff_hexagonRay (v : Lattice) :
    (baseCell ∩ cell v).Nonempty ↔ v = 0 ∨ ∃ k : Fin 6, v = hexagonRay k := by
  rw [baseCell_inter_cell_nonempty_iff]
  simp [hexagonRay, Fin.exists_fin_succ, or_assoc, or_left_comm, or_comm]

theorem cell_inter_cell_nonempty_iff_adjacent (v w : Lattice) :
    (cell v ∩ cell w).Nonempty ↔ v = w ∨ AreAdjacent v w := by
  rw [cell_inter_cell_nonempty_iff_baseCell, baseCell_inter_cell_nonempty_iff_hexagonRay,
    ← areAdjacent_iff_hexagonRay, sub_eq_zero]
  exact or_congr eq_comm Iff.rfl

end Wikipedia.HopfProblem.CuspHoneycombTiling

namespace Wikipedia.HopfProblem.CuspHoneycombHexagon

open ToricFan ToricComponent ToricSpace

/-- The compatible zero-cell map respects every actual component label,
including the zero label and every label outside its six neighbours. -/
theorem compatibleCellHomeomorph_mem_rayDivisor_iff
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (x : CuspHoneycombTiling.baseCell) (v : Fin 2 → ℤ) :
    ((compatibleCellHomeomorph C₀ x).1 : Space) ∈ rayDivisor v ↔
      (x : Plane) ∈ CuspHoneycombTiling.cell v := by
  by_cases hv : v = 0
  · subst v
    exact iff_of_true (compatibleCellHomeomorph C₀ x).1.2
      (by simpa only [CuspHoneycombTiling.cell_zero] using x.2)
  constructor
  · intro hx
    have hmeet : (rayDivisor 0 ∩ rayDivisor v).Nonempty :=
      ⟨((compatibleCellHomeomorph C₀ x).1 : Space), (compatibleCellHomeomorph C₀ x).1.2, hx⟩
    have hadj : AreAdjacent 0 v :=
      (rayDivisor_inter_nonempty_iff 0 v (fun h => hv h.symm)).mp hmeet
    obtain ⟨k, hk⟩ := (areAdjacent_iff_hexagonRay 0 v).mp hadj
    have hvk : v = hexagonRay k := by simpa only [sub_zero] using hk
    subst v
    change compatibleCellHomeomorph C₀ x ∈ positiveBoundary k at hx
    exact (compatibleCellHomeomorph_mem_boundary_iff C₀ x k).mp hx
  · intro hx
    have hmeet : (CuspHoneycombTiling.baseCell ∩ CuspHoneycombTiling.cell v).Nonempty :=
      ⟨(x : Plane), x.2, hx⟩
    rcases (CuspHoneycombTiling.baseCell_inter_cell_nonempty_iff_hexagonRay v).mp hmeet with
      hzero | ⟨k, hk⟩
    · exact (hv hzero).elim
    · subst v
      exact (compatibleCellHomeomorph_mem_boundary_iff C₀ x k).mpr hx

end Wikipedia.HopfProblem.CuspHoneycombHexagon
