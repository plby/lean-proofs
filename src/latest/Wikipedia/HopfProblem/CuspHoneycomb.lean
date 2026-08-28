import Wikipedia.HopfProblem.CuspHoneycombCollapse
import Wikipedia.HopfProblem.CuspHoneycombStrata
import Wikipedia.HopfProblem.CuspHoneycombStabilizers

/-!
# The genuine central honeycomb and its phase-collapse model

The actual positive central fibre is equivariantly homeomorphic to the
real plane with its literal dual hexagonal tiling. Cells and their
intersections map onto the original toric component intersections, and
every triangle barycenter maps to its original all-zero chart point.

The compact fibre-torus phase quotient over this plane is homeomorphic to
the actual toric central fibre and, after the explicit lattice relation,
to the original cusp central fibre. The stabilizers are computed on the
actual honeycomb strata. These are the central geometric constructions
of Lemma 7.7(iv) and the collapse description used in Lemma 7.10; no claim
is made here about prescribing a neighborhood retraction on a chosen
nonzero fibre.
-/

open Set

namespace Wikipedia.HopfProblem.CuspHoneycomb

open CuspHoneycombTiling CuspHoneycombPositive
open ToricSpace

/-- All double-component intersections, with their original topologies,
are the images of the actual shared honeycomb cells. -/
theorem honeycombHomeomorph_image_cell_inter
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v w : CuspHoneycombTiling.Lattice) :
    honeycombHomeomorph C₀ '' (cell v ∩ cell w) = positiveCell v ∩ positiveCell w := by
  rw [Set.image_inter (honeycombHomeomorph C₀).injective,
    honeycombHomeomorph_image_cell, honeycombHomeomorph_image_cell]

/-- The same statement for triple intersections. -/
theorem honeycombHomeomorph_image_cell_triple
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (u v w : CuspHoneycombTiling.Lattice) :
    honeycombHomeomorph C₀ '' (cell u ∩ cell v ∩ cell w) =
      positiveCell u ∩ positiveCell v ∩ positiveCell w := by
  rw [Set.image_inter (honeycombHomeomorph C₀).injective,
    honeycombHomeomorph_image_cell_inter, honeycombHomeomorph_image_cell]

/-- No phases are collapsed over an actual open hexagon. -/
theorem honeycombPolarMap_eq_iff_of_mem_interior
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (y : CuspHoneycombTiling.Plane)
    (v : CuspHoneycombTiling.Lattice) (hy : y ∈ interior (cell v))
    (u w : CompactFibreTorus) :
    honeycombPolarMap C₀ (u, y) = honeycombPolarMap C₀ (w, y) ↔ u = w := by
  have hstab := honeycombHomeomorph_stabilizer_eq_bot C₀ y v
    ((containingCells_eq_singleton_iff y v).mpr hy)
  simp only [honeycombPolarMap_eq_iff, hstab, Subgroup.mem_bot, inv_mul_eq_one,
    true_and]

/-- The actual phase-collapse map is injective on all points lying over
the interior of any one literal honeycomb cell. -/
theorem honeycombPolarMap_injOn_cell_interior
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : CuspHoneycombTiling.Lattice) :
    Set.InjOn (honeycombPolarMap C₀)
      ((Set.univ : Set CompactFibreTorus) ×ˢ interior (cell v)) := by
  rintro ⟨u, x⟩ hx ⟨w, y⟩ _hy h
  have hxy : x = y := (honeycombPolarMap_eq_iff C₀ (u, x) (w, y)).mp h |>.1
  subst y
  exact Prod.ext ((honeycombPolarMap_eq_iff_of_mem_interior C₀ x v hx.2 u w).mp h) rfl

/-- Precisely the embedded circle in the difference direction is collapsed
over a point belonging to exactly two actual honeycomb cells. -/
theorem honeycombPolarMap_eq_iff_of_two_cells
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (y : CuspHoneycombTiling.Plane)
    (v w : CuspHoneycombTiling.Lattice) (hvw : v ≠ w)
    (hy : {a : CuspHoneycombTiling.Lattice | y ∈ cell a} = {v, w})
    (u u' : CompactFibreTorus) :
    honeycombPolarMap C₀ (u, y) = honeycombPolarMap C₀ (u', y) ↔
      u⁻¹ * u' ∈ edgeCircle (w - v) := by
  have hstab := honeycombHomeomorph_stabilizer_eq_edgeCircle C₀ y v w hvw hy
  simp only [honeycombPolarMap_eq_iff, hstab, true_and]

/-- All compact fibre phases collapse to the single original triple point
over every actual honeycomb vertex. -/
theorem honeycombPolarMap_triangleBarycenter
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (s : ToricFan.Triangle)
    (u w : CompactFibreTorus) :
    honeycombPolarMap C₀ (u, triangleBarycenter s) =
      honeycombPolarMap C₀ (w, triangleBarycenter s) := by
  apply (honeycombPolarMap_eq_iff C₀ _ _).mpr
  refine ⟨rfl, ?_⟩
  rw [honeycombHomeomorph_stabilizer_triangleBarycenter]
  trivial

end Wikipedia.HopfProblem.CuspHoneycomb
