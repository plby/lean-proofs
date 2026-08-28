import Wikipedia.HopfProblem.CuspHoneycombHomeomorph
import Wikipedia.HopfProblem.CuspHoneycombHexagonConvex

/-!
# Actual branch strata of the honeycomb plane

The global honeycomb homeomorphism preserves the entire set of original
toric component labels through a point.  Thus its planar cell incidence
is exactly the branch incidence of the literal positive central fibre.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspHoneycomb

open ToricSpace ToricFan CuspPositiveRetraction CuspHoneycombPositive
open CuspHoneycombTiling

local notation "Plane" => CuspHoneycombTiling.Plane
local notation "Lattice" => CuspHoneycombTiling.Lattice

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ)

/-- The branches of the actual central fibre are precisely the literal
closed honeycomb cells containing the planar point, with the same labels. -/
theorem honeycombHomeomorph_branchVertices (y : Plane) :
    branchVertices ((honeycombHomeomorph C₀ y).1 : Space) =
      {v : Lattice | y ∈ cell v} := by
  ext v
  exact honeycombHomeomorph_mem_positiveCell_iff C₀ v y

/-- Branch count is the cardinality of actual closed-cell incidence. -/
theorem honeycombHomeomorph_branchCount (y : Plane) :
    branchCount ((honeycombHomeomorph C₀ y).1 : Space) =
      {v : Lattice | y ∈ cell v}.ncard := by
  rw [← branchVertices_ncard, honeycombHomeomorph_branchVertices]

theorem honeycombHomeomorph_branchCount_pos (y : Plane) :
    0 < branchCount ((honeycombHomeomorph C₀ y).1 : Space) :=
  (branchCount_pos_iff _).mpr (honeycombHomeomorph C₀ y).2

/-- Three branches occur exactly at the barycenters of the actual
integral triangles, not at an abstractly chosen set of vertices. -/
theorem honeycombHomeomorph_branchCount_eq_three_iff (y : Plane) :
    branchCount ((honeycombHomeomorph C₀ y).1 : Space) = 3 ↔
      ∃ s : Triangle, y = triangleBarycenter s := by
  rw [branchCount_eq_three]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, (honeycombHomeomorph C₀).injective ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hs.symm.trans (honeycombHomeomorph_triangleBarycenter_coe C₀ s).symm
  · rintro ⟨s, rfl⟩
    exact ⟨s, (honeycombHomeomorph_triangleBarycenter_coe C₀ s).symm⟩

/-- The exact labels, rather than just their number, identify a double
branch with the common part of two cells away from all remaining cells. -/
theorem honeycombHomeomorph_branchCount_eq_two_iff (y : Plane) :
    branchCount ((honeycombHomeomorph C₀ y).1 : Space) = 2 ↔
      ∃ v w : Lattice, v ≠ w ∧
        {u : Lattice | y ∈ cell u} = {v, w} := by
  rw [honeycombHomeomorph_branchCount, Set.ncard_eq_two]

end Wikipedia.HopfProblem.CuspHoneycomb

namespace Wikipedia.HopfProblem.CuspHoneycombTiling

open ToricSpace CuspHoneycomb

theorem containingCells_finite (y : Plane) : {v : Lattice | y ∈ cell v}.Finite := by
  rw [← honeycombHomeomorph_branchVertices (0 : Matrix (Fin 2) (Fin 2) ℂ)]
  exact branchVertices_finite _

theorem containingCells_ncard_pos (y : Plane) : 0 < {v : Lattice | y ∈ cell v}.ncard := by
  rw [← honeycombHomeomorph_branchCount (0 : Matrix (Fin 2) (Fin 2) ℂ)]
  exact honeycombHomeomorph_branchCount_pos _ y

theorem containingCells_ncard_le_three (y : Plane) :
    {v : Lattice | y ∈ cell v}.ncard ≤ 3 := by
  rw [← honeycombHomeomorph_branchCount (0 : Matrix (Fin 2) (Fin 2) ℂ)]
  exact branchCount_le_three _

theorem containingCells_ncard_eq_three_iff (y : Plane) :
    {v : Lattice | y ∈ cell v}.ncard = 3 ↔
      ∃ s : ToricFan.Triangle, y = triangleBarycenter s := by
  rw [← honeycombHomeomorph_branchCount (0 : Matrix (Fin 2) (Fin 2) ℂ)]
  exact honeycombHomeomorph_branchCount_eq_three_iff _ y

theorem frontier_baseCell :
    frontier baseCell = ⋃ k : Fin 6, baseCell ∩ cell (ToricComponent.hexagonRay k) := by
  have hpre : dualStandardPlaneHomeomorph ⁻¹' CuspHoneycombHexagon.Hexagon = baseCell :=
    Set.ext dualStandardPlaneHomeomorph_mem_hexagon
  calc
    frontier baseCell = dualStandardPlaneHomeomorph ⁻¹'
        frontier CuspHoneycombHexagon.Hexagon := by
      rw [dualStandardPlaneHomeomorph.preimage_frontier, hpre]
    _ = ⋃ k : Fin 6, dualStandardPlaneHomeomorph ⁻¹' CuspHoneycombHexagon.side k := by
      rw [CuspHoneycombHexagon.frontier_hexagon, Set.preimage_iUnion]
    _ = ⋃ k : Fin 6, baseCell ∩ cell (ToricComponent.hexagonRay k) := by
      apply iUnion_congr
      intro k
      rw [← dual_image_side, Homeomorph.image_eq_preimage_symm, Homeomorph.symm_symm]

/-- Every point of the frontier of the base cell lies in another actual
cell, and every intersection with a different cell is on this frontier. -/
theorem mem_frontier_baseCell_iff (y : Plane) :
    y ∈ frontier baseCell ↔ y ∈ baseCell ∧
      ∃ v : Lattice, v ≠ 0 ∧ y ∈ cell v := by
  rw [frontier_baseCell, mem_iUnion]
  constructor
  · rintro ⟨k, hy, hv⟩
    refine ⟨hy, ToricComponent.hexagonRay k, ?_, hv⟩
    fin_cases k <;> decide
  · rintro ⟨hy, v, hv, hyv⟩
    rcases (baseCell_inter_cell_nonempty_iff_hexagonRay v).mp ⟨y, hy, hyv⟩ with
      hz | ⟨k, rfl⟩
    · exact (hv hz).elim
    · exact ⟨k, hy, hyv⟩

theorem mem_interior_baseCell_iff (y : Plane) :
    y ∈ interior baseCell ↔ ∀ v : Lattice, y ∈ cell v ↔ v = 0 := by
  constructor
  · intro hy v
    constructor
    · intro hyv
      by_contra hv
      have hf := (mem_frontier_baseCell_iff y).mpr ⟨interior_subset hy, v, hv, hyv⟩
      exact ((mem_interior_iff_notMem_frontier (interior_subset hy)).mp hy) hf
    · rintro rfl
      simpa only [cell_zero] using interior_subset hy
  · intro hy
    have hbase : y ∈ baseCell := by
      simpa only [cell_zero] using (hy 0).mpr rfl
    apply (mem_interior_iff_notMem_frontier hbase).mpr
    intro hf
    obtain ⟨_, v, hv, hyv⟩ := (mem_frontier_baseCell_iff y).mp hf
    exact hv ((hy v).mp hyv)

/-- Interior here is the ordinary topology of the real plane.  It is
exactly membership in one cell and in no other cell. -/
theorem mem_interior_cell_iff (v : Lattice) (y : Plane) :
    y ∈ interior (cell v) ↔ ∀ w : Lattice, y ∈ cell w ↔ w = v := by
  have hpre : (Homeomorph.subRight (latticePoint v)) ⁻¹' baseCell = cell v := rfl
  have hint : y ∈ interior (cell v) ↔ y - latticePoint v ∈ interior baseCell := by
    rw [← hpre, ← Homeomorph.preimage_interior]
    rfl
  rw [hint, mem_interior_baseCell_iff]
  constructor
  · intro hy w
    have h := hy (w - v)
    rw [sub_latticePoint_mem_cell_iff, add_comm v (w - v), sub_add_cancel] at h
    exact h.trans sub_eq_zero
  · intro hy w
    rw [sub_latticePoint_mem_cell_iff, hy, add_eq_left]

theorem containingCells_eq_singleton_iff (y : Plane) (v : Lattice) :
    {w : Lattice | y ∈ cell w} = {v} ↔ y ∈ interior (cell v) := by
  rw [mem_interior_cell_iff]
  exact Set.ext_iff

theorem containingCells_ncard_eq_one_iff (y : Plane) :
    {v : Lattice | y ∈ cell v}.ncard = 1 ↔ ∃ v : Lattice, y ∈ interior (cell v) := by
  rw [Set.ncard_eq_one]
  exact exists_congr fun v => containingCells_eq_singleton_iff y v

end Wikipedia.HopfProblem.CuspHoneycombTiling

namespace Wikipedia.HopfProblem.CuspHoneycomb

open ToricSpace CuspHoneycombTiling

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ)

/-- The one-branch stratum is exactly the union of open cell interiors. -/
theorem honeycombHomeomorph_branchCount_eq_one_iff (y : Plane) :
    branchCount ((honeycombHomeomorph C₀ y).1 : Space) = 1 ↔
      ∃ v : CuspHoneycombTiling.Lattice, y ∈ interior (cell v) := by
  rw [honeycombHomeomorph_branchCount, containingCells_ncard_eq_one_iff]

/-- A specified sole toric branch corresponds to the interior of the
planar cell bearing that very same label. -/
theorem honeycombHomeomorph_branchVertices_eq_singleton_iff
    (y : Plane) (v : CuspHoneycombTiling.Lattice) :
    branchVertices ((honeycombHomeomorph C₀ y).1 : Space) = {v} ↔
      y ∈ interior (cell v) := by
  rw [honeycombHomeomorph_branchVertices, containingCells_eq_singleton_iff]

end Wikipedia.HopfProblem.CuspHoneycomb
