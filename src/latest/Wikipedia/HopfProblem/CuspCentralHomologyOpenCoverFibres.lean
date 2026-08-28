import Wikipedia.HopfProblem.CuspCentralHomologyFundamentalCell
import Wikipedia.HopfProblem.CuspHoneycomb

/-!
# Interior fibres of the actual compact phase-hexagon presentation

Over the interior of the central dual hexagon, no nonzero lattice
translation can identify two fundamental-cell representatives, and the
compact fibre torus has trivial stabilizer. Consequently every such
representative has a singleton fibre. All nontrivial identifications are
confined to the literal frontier of the hexagon.

These statements use the exact geometric fibre relation and need no
holomorphicity, small-drift, or Hausdorff assumptions.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction CuspCollapse CuspHoneycomb CuspHoneycombTiling

local notation "Plane" => CuspHoneycombTiling.Plane
local notation "Lattice" => CuspHoneycombTiling.Lattice

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- Every fundamental-cell representative over the open hexagon has a
singleton fibre in the original cusp central fibre. -/
theorem fundamentalCellMap_eq_of_interior (p q : FundamentalCell)
    (hp : (p.2 : Plane) ∈ interior baseCell)
    (h : fundamentalCellMap C ε hε p = fundamentalCellMap C ε hε q) : p = q := by
  obtain ⟨u, hb, hphase⟩ := (fundamentalCellMap_eq_iff C ε hε p q).mp h
  have hpcell : (p.2 : Plane) ∈ cell (cuspVector u) := by
    rw [hb, mem_cell, add_sub_cancel_right]
    exact q.2.2
  have hpinterior : (p.2 : Plane) ∈ interior (cell 0) := by
    simpa only [cell_zero] using hp
  have hcells := (containingCells_eq_singleton_iff (p.2 : Plane) 0).mpr hpinterior
  have hcu : cuspVector u = 0 := by
    have hu : cuspVector u ∈ {v : Lattice | (p.2 : Plane) ∈ cell v} := hpcell
    simpa only [hcells, Set.mem_singleton_iff] using hu
  have hu : u = 0 := cuspVector_injective (hcu.trans cuspVector_zero.symm)
  subst u
  have hb' : (p.2 : Plane) = (q.2 : Plane) := by
    simpa only [cuspVector_zero, latticePoint_zero, add_zero] using hb
  have hstab := honeycombHomeomorph_stabilizer_eq_bot_of_mem_interior
    (C 0) (p.2 : Plane) 0 hpinterior
  have hphase' : p.1 = q.1 := by
    simpa only [hstab, Subgroup.mem_bot, deckFibrePhase_zero, one_mul,
      inv_mul_eq_one] using hphase
  exact Prod.ext hphase' (Subtype.ext hb')

/-- Lying over the open hexagon is a saturated property for the actual
fundamental-cell presentation. -/
theorem fundamentalCellMap_interior_iff_of_eq (p q : FundamentalCell)
    (h : fundamentalCellMap C ε hε p = fundamentalCellMap C ε hε q) :
    (p.2 : Plane) ∈ interior baseCell ↔ (q.2 : Plane) ∈ interior baseCell := by
  constructor
  · intro hp
    have hpq := fundamentalCellMap_eq_of_interior C ε hε p q hp h
    simpa only [← hpq] using hp
  · intro hq
    have hqp := fundamentalCellMap_eq_of_interior C ε hε q p hq h.symm
    simpa only [← hqp] using hq

/-- Equally mapped representatives are either identical or both lie over
the literal boundary of the closed fundamental hexagon. -/
theorem fundamentalCellMap_eq_or_frontier (p q : FundamentalCell)
    (h : fundamentalCellMap C ε hε p = fundamentalCellMap C ε hε q) :
    p = q ∨ ((p.2 : Plane) ∈ frontier baseCell ∧ (q.2 : Plane) ∈ frontier baseCell) := by
  by_cases hp : (p.2 : Plane) ∈ interior baseCell
  · exact Or.inl (fundamentalCellMap_eq_of_interior C ε hε p q hp h)
  · right
    rw [baseCell_isClosed.frontier_eq]
    refine ⟨⟨p.2.2, hp⟩, q.2.2, ?_⟩
    intro hq
    exact hp ((fundamentalCellMap_interior_iff_of_eq C ε hε p q h).mpr hq)

/-- In particular, distinct base points can only be identified on the
frontier of the fundamental hexagon. -/
theorem fundamentalCellMap_eq_base_or_frontier (p q : FundamentalCell)
    (h : fundamentalCellMap C ε hε p = fundamentalCellMap C ε hε q) :
    (p.2 : Plane) = (q.2 : Plane) ∨
      ((p.2 : Plane) ∈ frontier baseCell ∧ (q.2 : Plane) ∈ frontier baseCell) := by
  rcases fundamentalCellMap_eq_or_frontier C ε hε p q h with hpq | hfrontier
  · exact Or.inl (congrArg (fun r : FundamentalCell => (r.2 : Plane)) hpq)
  · exact Or.inr hfrontier

/-- The frontier is saturated as well as the interior. -/
theorem fundamentalCellMap_frontier_iff_of_eq (p q : FundamentalCell)
    (h : fundamentalCellMap C ε hε p = fundamentalCellMap C ε hε q) :
    (p.2 : Plane) ∈ frontier baseCell ↔ (q.2 : Plane) ∈ frontier baseCell := by
  rw [mem_frontier_iff_notMem_interior p.2.2, mem_frontier_iff_notMem_interior q.2.2]
  exact not_congr (fundamentalCellMap_interior_iff_of_eq C ε hε p q h)

/-- The original fundamental-cell map is injective on phases over the
open hexagon. -/
theorem fundamentalCellMap_injOn_interior :
    Set.InjOn (fundamentalCellMap C ε hε)
      {p : FundamentalCell | (p.2 : Plane) ∈ interior baseCell} := by
  intro p hp q _hq h
  exact fundamentalCellMap_eq_of_interior C ε hε p q hp h

end Wikipedia.HopfProblem.CuspCentralHomology
