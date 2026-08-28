import Wikipedia.HopfProblem.CuspHoneycombCellMaps
import Wikipedia.HopfProblem.CuspHoneycombClosedCover
import Wikipedia.HopfProblem.CuspHoneycombTiling
import Mathlib.Analysis.Convex.Contractible

/-!
# The actual positive central fibre is the equivariant honeycomb plane

The compatible cell maps glue across the original locally finite closed
covers of the ordinary real plane and of the literal positive central
fibre. Their exact point identifications give a global homeomorphism.
Integral translations agree with the genuine positive-twist action.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspHoneycomb

open ToricSpace ToricFan CuspPositiveRetraction CuspCollapse
open CuspHoneycombTiling CuspHoneycombPositive

local notation "Plane" => CuspHoneycombTiling.Plane
local notation "Lattice" => CuspHoneycombTiling.Lattice

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ)

/-- The literal plane, tiled by its closed dual hexagons, is homeomorphic
to the literal positive central fibre with its inherited topology. -/
def honeycombHomeomorph : Plane ≃ₜ PositiveCentralFibre :=
  CuspHoneycombClosedCover.homeomorph cell positiveCell (cellHomeomorph C₀)
    iUnion_cell cell_isClosed cell_locallyFinite
    iUnion_positiveCell positiveCell_isClosed positiveCells_locallyFinite
    (fun v w x y => (cellHomeomorph_eq_iff C₀ v w x y).symm)

/-- The global map has exactly the prescribed map on every actual closed
cell, including its edges and vertices. -/
theorem honeycombHomeomorph_cell (v : Lattice) (x : cell v) :
    honeycombHomeomorph C₀ (x : Plane) = (cellHomeomorph C₀ v x : PositiveCentralFibre) :=
  CuspHoneycombClosedCover.homeomorph_apply cell positiveCell (cellHomeomorph C₀)
    iUnion_cell cell_isClosed cell_locallyFinite
    iUnion_positiveCell positiveCell_isClosed positiveCells_locallyFinite
    (fun v w x y => (cellHomeomorph_eq_iff C₀ v w x y).symm) v x

theorem honeycombHomeomorph_cell_coe (v : Lattice) (x : cell v) :
    ((honeycombHomeomorph C₀ (x : Plane)).1 : Space) =
      twistedTranslate (CuspPositive.positiveTwist C₀) (-cuspVector v)
        ((CuspHoneycombHexagon.compatibleCellHomeomorph C₀
          ((cellTranslationHomeomorph v).symm x)).1 : Space) := by
  rw [honeycombHomeomorph_cell, cellHomeomorph_coe]

theorem honeycombHomeomorph_symm_cell (v : Lattice) (q : positiveCell v) :
    (honeycombHomeomorph C₀).symm (q : PositiveCentralFibre) =
      ((cellHomeomorph C₀ v).symm q : Plane) := by
  apply (honeycombHomeomorph C₀).injective
  rw [Homeomorph.apply_symm_apply, honeycombHomeomorph_cell, Homeomorph.apply_symm_apply]

theorem honeycombHomeomorph_mem_positiveCell_iff (v : Lattice) (x : Plane) :
    honeycombHomeomorph C₀ x ∈ positiveCell v ↔ x ∈ cell v := by
  obtain ⟨w, hw⟩ := exists_mem_cell x
  rw [honeycombHomeomorph_cell C₀ w ⟨x, hw⟩]
  exact cellHomeomorph_mem_positiveCell_iff C₀ w v ⟨x, hw⟩

theorem honeycombHomeomorph_preimage_positiveCell (v : Lattice) :
    honeycombHomeomorph C₀ ⁻¹' positiveCell v = cell v :=
  Set.ext (honeycombHomeomorph_mem_positiveCell_iff C₀ v)

/-- Every displayed closed hexagon maps onto its original positive toric
component, with no relabeling of cells. -/
theorem honeycombHomeomorph_image_cell (v : Lattice) :
    honeycombHomeomorph C₀ '' cell v = positiveCell v := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (honeycombHomeomorph_mem_positiveCell_iff C₀ v x).mpr hx
  · intro hq
    refine ⟨(honeycombHomeomorph C₀).symm q, ?_, Homeomorph.apply_symm_apply _ q⟩
    apply (honeycombHomeomorph_mem_positiveCell_iff C₀ v _).mp
    simpa only [Homeomorph.apply_symm_apply] using hq

/-- Translation equivariance already holds for the genuine cell maps. -/
theorem cellHomeomorph_translate (u v : Lattice) (x : cell v) :
    (cellHomeomorph C₀ (v + cuspVector u)
      (cellShiftHomeomorph v (cuspVector u) x) : PositiveCentralFibre) =
      positiveCentralTranslate C₀ u (cellHomeomorph C₀ v x) := by
  have hnorm : (cellTranslationHomeomorph (v + cuspVector u)).symm
      (cellShiftHomeomorph v (cuspVector u) x) = (cellTranslationHomeomorph v).symm x := by
    apply Subtype.ext
    change ((x : Plane) + latticePoint (cuspVector u)) -
      latticePoint (v + cuspVector u) = (x : Plane) - latticePoint v
    rw [latticePoint_add]
    abel
  have hu : -cuspVector (v + cuspVector u) = u + -cuspVector v := by
    rw [cuspVector_add, cuspVector_cuspVector]
    abel
  apply Subtype.ext
  apply Subtype.ext
  simp only [cellHomeomorph_coe, positiveCentralTranslate_coe, hnorm]
  rw [twistedTranslate_add, hu]

/-- The source's actual lattice translation is conjugate to the actual
positive-twist action on the central fibre. -/
theorem honeycombHomeomorph_equivariant (u : Lattice) (x : Plane) :
    honeycombHomeomorph C₀ (x + latticePoint (cuspVector u)) =
      positiveCentralTranslate C₀ u (honeycombHomeomorph C₀ x) := by
  obtain ⟨v, hx⟩ := exists_mem_cell x
  let a : cell v := ⟨x, hx⟩
  have ha : (a : Plane) = x := rfl
  have hshift := honeycombHomeomorph_cell C₀ (v + cuspVector u)
    (cellShiftHomeomorph v (cuspVector u) a)
  have hbase := congrArg (positiveCentralTranslate C₀ u)
    (honeycombHomeomorph_cell C₀ v a).symm
  simpa only [cellShiftHomeomorph_coe, ha] using
    hshift.trans ((cellHomeomorph_translate C₀ u v a).trans hbase)

theorem honeycombHomeomorph_add_latticePoint (v : Lattice) (x : Plane) :
    honeycombHomeomorph C₀ (x + latticePoint v) =
      positiveCentralTranslate C₀ (-cuspVector v) (honeycombHomeomorph C₀ x) := by
  simpa only [cuspVector_neg, cuspVector_cuspVector, neg_neg] using
    honeycombHomeomorph_equivariant C₀ (-cuspVector v) x

theorem honeycombHomeomorph_symm_equivariant (u : Lattice) (q : PositiveCentralFibre) :
    (honeycombHomeomorph C₀).symm (positiveCentralTranslate C₀ u q) =
      (honeycombHomeomorph C₀).symm q + latticePoint (cuspVector u) := by
  apply (honeycombHomeomorph C₀).injective
  rw [Homeomorph.apply_symm_apply, honeycombHomeomorph_equivariant,
    Homeomorph.apply_symm_apply]

section Vertices

open ToricComponent CuspHoneycombHexagon

theorem standardHexagonDualHomeomorph_vertex_coe (i : Fin 6) :
    (standardHexagonDualHomeomorph
      ⟨vertex i, (vertex_mem_side_self i).1⟩ : Plane) =
        triangleBarycenter (zeroTriangle i) :=
  dual_standard_vertex i

theorem compatibleCellHomeomorph_vertex (i : Fin 6) :
    compatibleCellHomeomorph C₀
      (standardHexagonDualHomeomorph ⟨vertex i, (vertex_mem_side_self i).1⟩) =
        squarePoint i cornerZero := by
  simpa only [sideIntervalHomeomorph_one, compatibleBoundaryArc_one_point] using
    compatibleCellHomeomorph_sideInterval C₀ i 1

theorem triangleBarycenter_zeroTriangle_mem_baseCell (i : Fin 6) :
    triangleBarycenter (zeroTriangle i) ∈ baseCell := by
  rw [← standardHexagonDualHomeomorph_vertex_coe i]
  exact (standardHexagonDualHomeomorph ⟨vertex i, (vertex_mem_side_self i).1⟩).2

theorem compatibleCellHomeomorph_triangleBarycenter (i : Fin 6) :
    compatibleCellHomeomorph C₀
      ⟨triangleBarycenter (zeroTriangle i), triangleBarycenter_zeroTriangle_mem_baseCell i⟩ =
        squarePoint i cornerZero := by
  have hi : (⟨triangleBarycenter (zeroTriangle i),
      triangleBarycenter_zeroTriangle_mem_baseCell i⟩ : baseCell) =
      standardHexagonDualHomeomorph ⟨vertex i, (vertex_mem_side_self i).1⟩ := by
    apply Subtype.ext
    exact (standardHexagonDualHomeomorph_vertex_coe i).symm
  rw [hi, compatibleCellHomeomorph_vertex]

theorem compatibleCellHomeomorph_triangleBarycenter_coe (i : Fin 6) :
    ((compatibleCellHomeomorph C₀
      ⟨triangleBarycenter (zeroTriangle i), triangleBarycenter_zeroTriangle_mem_baseCell i⟩).1 :
        Space) = inclusion (zeroTriangle i) 0 := by
  rw [compatibleCellHomeomorph_triangleBarycenter, squarePoint_cornerZero_coe]

/-- The six vertices of the central dual hexagon map to the literal
all-zero points of the six original toric coordinate charts. -/
theorem honeycombHomeomorph_zeroTriangleBarycenter_coe (i : Fin 6) :
    ((honeycombHomeomorph C₀ (triangleBarycenter (zeroTriangle i))).1 : Space) =
      inclusion (zeroTriangle i) 0 := by
  let a : baseCell :=
    ⟨triangleBarycenter (zeroTriangle i), triangleBarycenter_zeroTriangle_mem_baseCell i⟩
  let x : cell 0 := cellTranslationHomeomorph 0 a
  have hx : (x : Plane) = triangleBarycenter (zeroTriangle i) := by
    change (a : Plane) + latticePoint 0 = triangleBarycenter (zeroTriangle i)
    rw [latticePoint_zero, add_zero]
  have hnorm : (cellTranslationHomeomorph 0).symm x = a :=
    (cellTranslationHomeomorph 0).symm_apply_apply a
  have h := honeycombHomeomorph_cell_coe C₀ 0 x
  rw [hx, hnorm, cuspVector_zero, neg_zero, twistedTranslate_zero] at h
  exact h.trans (compatibleCellHomeomorph_triangleBarycenter_coe C₀ i)

theorem triangle_eq_zeroTriangle_shift (s : Triangle) :
    ∃ i : Fin 6, ∃ v : Lattice, s = (zeroTriangle i).shift v := by
  rcases s with ⟨a, b, u⟩
  cases u
  · refine ⟨0, ![a, b], ?_⟩
    ext <;> simp [zeroTriangle, Triangle.shift]
  · refine ⟨1, ![a + 1, b], ?_⟩
    ext <;> simp [zeroTriangle, Triangle.shift]

/-- Every actual triangular-lattice barycenter maps to the all-zero point
of that same actual toric chart. -/
theorem honeycombHomeomorph_triangleBarycenter_coe (s : Triangle) :
    ((honeycombHomeomorph C₀ (triangleBarycenter s)).1 : Space) = inclusion s 0 := by
  obtain ⟨i, v, rfl⟩ := triangle_eq_zeroTriangle_shift s
  rw [triangleBarycenter_shift, honeycombHomeomorph_add_latticePoint,
    positiveCentralTranslate_coe, honeycombHomeomorph_zeroTriangleBarycenter_coe,
    twistedTranslate_origin, cuspVector_neg, cuspVector_cuspVector, neg_neg]

end Vertices

/-- Contractibility concerns the actual positive central fibre, and has
no parameter or geometric hypothesis. -/
theorem positiveCentralFibre_contractibleSpace : ContractibleSpace PositiveCentralFibre :=
  (honeycombHomeomorph (0 : Matrix (Fin 2) (Fin 2) ℂ)).symm.contractibleSpace

end Wikipedia.HopfProblem.CuspHoneycomb
