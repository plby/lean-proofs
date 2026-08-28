import Wikipedia.HopfProblem.CuspHoneycombLinearBridgeSides
import Wikipedia.HopfProblem.CuspHoneycombOppositeCoordinates

/-!
# Coordinates on every literal honeycomb cell

Integral translations give homeomorphisms between the actual closed dual
cells.  Composing with the standard-to-dual linear bridge supplies the
cellwise coordinates used to glue the global honeycomb map.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspHoneycombTiling

/-- Subtracting an integral vector shifts the cell index by the same
vector.  Both sides refer to the original subsets of the real plane. -/
theorem sub_latticePoint_mem_cell_iff (v w : Lattice) (x : Plane) :
    x - latticePoint v ∈ cell w ↔ x ∈ cell (v + w) := by
  simp only [mem_cell, latticePoint_add, sub_sub]

theorem add_latticePoint_mem_cell_iff_sub (v w : Lattice) (x : Plane) :
    x + latticePoint v ∈ cell w ↔ x ∈ cell (w - v) := by
  simpa only [sub_add_cancel] using add_latticePoint_mem_cell_iff (w - v) v x

/-- Translation from the central closed hexagon to any literal lattice cell. -/
def cellTranslationHomeomorph (v : Lattice) : baseCell ≃ₜ cell v where
  toFun x := ⟨(x : Plane) + latticePoint v, by
    simpa only [mem_cell, add_sub_cancel_right] using x.2⟩
  invFun y := ⟨(y : Plane) - latticePoint v, y.2⟩
  left_inv x := Subtype.ext (add_sub_cancel_right (x : Plane) (latticePoint v))
  right_inv y := Subtype.ext (sub_add_cancel (y : Plane) (latticePoint v))
  continuous_toFun := (continuous_subtype_val.add continuous_const).subtype_mk _
  continuous_invFun := (continuous_subtype_val.sub continuous_const).subtype_mk _

@[simp] theorem cellTranslationHomeomorph_coe (v : Lattice) (x : baseCell) :
    (cellTranslationHomeomorph v x : Plane) = (x : Plane) + latticePoint v := rfl

@[simp] theorem cellTranslationHomeomorph_symm_coe (v : Lattice) (y : cell v) :
    ((cellTranslationHomeomorph v).symm y : Plane) = (y : Plane) - latticePoint v := rfl

/-- The same translation between two arbitrary indexed closed cells. -/
def cellShiftHomeomorph (v w : Lattice) : cell v ≃ₜ cell (v + w) where
  toFun x := ⟨(x : Plane) + latticePoint w,
    (add_latticePoint_mem_cell_iff v w x).mpr x.2⟩
  invFun y := ⟨(y : Plane) - latticePoint w,
    (sub_latticePoint_mem_cell_iff w v y).mpr (by simpa only [add_comm w v] using y.2)⟩
  left_inv x := Subtype.ext (add_sub_cancel_right (x : Plane) (latticePoint w))
  right_inv y := Subtype.ext (sub_add_cancel (y : Plane) (latticePoint w))
  continuous_toFun := (continuous_subtype_val.add continuous_const).subtype_mk _
  continuous_invFun := (continuous_subtype_val.sub continuous_const).subtype_mk _

@[simp] theorem cellShiftHomeomorph_coe (v w : Lattice) (x : cell v) :
    (cellShiftHomeomorph v w x : Plane) = (x : Plane) + latticePoint w := rfl

@[simp] theorem cellShiftHomeomorph_symm_coe (v w : Lattice) (y : cell (v + w)) :
    ((cellShiftHomeomorph v w).symm y : Plane) = (y : Plane) - latticePoint w := rfl

/-- Translation across a common edge exchanges the base cell and its
neighbor, with the opposite neighbor as the new cell index. -/
def oppositeCellEdgeHomeomorph (v : Lattice) :
    ↥(baseCell ∩ cell v) ≃ₜ ↥(baseCell ∩ cell (-v)) where
  toFun x := ⟨(x : Plane) - latticePoint v, x.2.2, by
    simpa only [mem_cell, latticePoint_neg, sub_neg_eq_add, sub_add_cancel] using x.2.1⟩
  invFun y := ⟨(y : Plane) + latticePoint v,
    by simpa only [mem_cell, latticePoint_neg, sub_neg_eq_add] using y.2.2,
    by simpa only [mem_cell, add_sub_cancel_right] using y.2.1⟩
  left_inv x := Subtype.ext (sub_add_cancel (x : Plane) (latticePoint v))
  right_inv y := Subtype.ext (add_sub_cancel_right (y : Plane) (latticePoint v))
  continuous_toFun := (continuous_subtype_val.sub continuous_const).subtype_mk _
  continuous_invFun := (continuous_subtype_val.add continuous_const).subtype_mk _

@[simp] theorem oppositeCellEdgeHomeomorph_coe (v : Lattice) (x : ↥(baseCell ∩ cell v)) :
    (oppositeCellEdgeHomeomorph v x : Plane) = (x : Plane) - latticePoint v := rfl

@[simp] theorem oppositeCellEdgeHomeomorph_symm_coe (v : Lattice)
    (y : ↥(baseCell ∩ cell (-v))) :
    ((oppositeCellEdgeHomeomorph v).symm y : Plane) = (y : Plane) + latticePoint v := rfl

/-- The source's cyclic side labels turn the opposite edge into `k + 3`. -/
def dualOppositeEdgeHomeomorph (k : Fin 6) :
    ↥(baseCell ∩ cell (ToricComponent.hexagonRay k)) ≃ₜ
      ↥(baseCell ∩ cell (ToricComponent.hexagonRay (k + 3))) :=
  (oppositeCellEdgeHomeomorph (ToricComponent.hexagonRay k)).trans
    (Homeomorph.setCongr (by rw [ToricComponent.hexagonRay_opposite]))

@[simp] theorem dualOppositeEdgeHomeomorph_coe (k : Fin 6)
    (x : ↥(baseCell ∩ cell (ToricComponent.hexagonRay k))) :
    (dualOppositeEdgeHomeomorph k x : Plane) =
      (x : Plane) - latticePoint (ToricComponent.hexagonRay k) := rfl

@[simp] theorem dualOppositeEdgeHomeomorph_symm_coe (k : Fin 6)
    (y : ↥(baseCell ∩ cell (ToricComponent.hexagonRay (k + 3)))) :
    ((dualOppositeEdgeHomeomorph k).symm y : Plane) =
      (y : Plane) + latticePoint (ToricComponent.hexagonRay k) := rfl

/-- Standard hexagonal coordinates on every literal closed dual cell. -/
def standardHexagonCellHomeomorph (v : Lattice) : CuspHoneycombHexagon.Hexagon ≃ₜ cell v :=
  standardHexagonDualHomeomorph.trans (cellTranslationHomeomorph v)

@[simp] theorem standardHexagonCellHomeomorph_coe (v : Lattice)
    (x : CuspHoneycombHexagon.Hexagon) :
    (standardHexagonCellHomeomorph v x : Plane) =
      dualStandardPlaneHomeomorph.symm x + latticePoint v := rfl

@[simp] theorem standardHexagonCellHomeomorph_symm_coe (v : Lattice) (y : cell v) :
    ((standardHexagonCellHomeomorph v).symm y : Plane) =
      dualStandardPlaneHomeomorph ((y : Plane) - latticePoint v) := rfl

/-- The actual triangle barycenters translate with their integral vertices. -/
theorem triangleBarycenter_shift (s : ToricFan.Triangle) (v : Lattice) :
    triangleBarycenter (s.shift v) = triangleBarycenter s + latticePoint v := by
  funext i
  simp only [triangleBarycenter, ToricFan.Triangle.vertex_shift, Pi.add_apply,
    Int.cast_add, latticePoint_apply]
  ring

end Wikipedia.HopfProblem.CuspHoneycombTiling
