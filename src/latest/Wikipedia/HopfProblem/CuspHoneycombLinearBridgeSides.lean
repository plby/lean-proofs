import Wikipedia.HopfProblem.CuspHoneycombLinearBridge
import Wikipedia.HopfProblem.CuspHoneycombTilingIntersections

/-!
# The numbered sides become the literal neighboring-cell intersections

The linear bridge preserves the source's cyclic side labels. Its inverse
maps side `k` of the standard hexagon to the common closed edge of the base
dual cell and the cell centered at `hexagonRay k`.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.CuspHoneycombTiling

/-- On the base dual cell, membership in the numbered neighboring cell is
exactly the corresponding supporting-side equation in standard coordinates. -/
theorem mem_neighbor_cell_iff_sideFunctional (k : Fin 6) (x : Plane)
    (hx : x ∈ baseCell) :
    x ∈ cell (ToricComponent.hexagonRay k) ↔
      CuspHoneycombHexagon.sideFunctional k (dualStandardPlaneHomeomorph x) = 1 := by
  have h0 := abs_le.mp hx.1
  have h1 := abs_le.mp hx.2.1
  have h2 := abs_le.mp hx.2.2
  fin_cases k <;>
    norm_num [cell, baseCell, latticePoint, ToricComponent.hexagonRay,
      CuspHoneycombHexagon.sideFunctional, dualStandardPlaneHomeomorph_apply, abs_le]
  all_goals
    constructor
    · intro h
      linarith
    · intro h
      repeat' apply And.intro
      all_goals linarith

/-- The exact image of every numbered standard side under the inverse linear bridge. -/
theorem dual_image_side (k : Fin 6) :
    dualStandardPlaneHomeomorph.symm '' CuspHoneycombHexagon.side k =
      baseCell ∩ cell (ToricComponent.hexagonRay k) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hx : dualStandardPlaneHomeomorph.symm y ∈ baseCell :=
      (dualStandardPlaneHomeomorph_symm_mem_baseCell y).mpr hy.1
    refine ⟨hx, (mem_neighbor_cell_iff_sideFunctional k _ hx).mpr ?_⟩
    simpa only [Homeomorph.apply_symm_apply] using hy.2
  · intro hx
    refine ⟨dualStandardPlaneHomeomorph x, ?_,
      dualStandardPlaneHomeomorph.symm_apply_apply x⟩
    exact ⟨(dualStandardPlaneHomeomorph_mem_hexagon x).mpr hx.1,
      (mem_neighbor_cell_iff_sideFunctional k x hx.1).mp hx.2⟩

theorem standardHexagonDualHomeomorph_mem_cell_iff_side (k : Fin 6)
    (x : CuspHoneycombHexagon.Hexagon) :
    (standardHexagonDualHomeomorph x : Plane) ∈ cell (ToricComponent.hexagonRay k) ↔
      (x : Plane) ∈ CuspHoneycombHexagon.side k := by
  have h := mem_neighbor_cell_iff_sideFunctional k
    (standardHexagonDualHomeomorph x) (standardHexagonDualHomeomorph x).property
  simpa only [standardHexagonDualHomeomorph_coe, Homeomorph.apply_symm_apply,
    CuspHoneycombHexagon.side, mem_ofPred_eq, x.property, true_and] using h

end Wikipedia.HopfProblem.CuspHoneycombTiling
