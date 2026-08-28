import Wikipedia.HopfProblem.CuspHoneycombHexagon
import Wikipedia.HopfProblem.CuspHoneycombHexagonConvex
import Wikipedia.HopfProblem.CuspHoneycombBoundaryExtension

/-!
# Extending maps of the actual positive component boundary

The union of the six neighboring-component intersections is identified
with the literal topological frontier of the hexagon.  A homeomorphism
of this actual boundary cycle therefore extends over the actual positive
toric component, by the proved radial extension for convex bodies.

This is the boundary-extension step in the honeycomb construction; it
does not assert that a compatible equivariant boundary map has already
been chosen.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspHoneycombHexagon

/-- The actual cycle formed by the six neighboring-component intersections. -/
abbrev PositiveE0Boundary := (⋃ k : Fin 6, positiveBoundary k)

/-- The original subspace topology on the boundary cycle agrees with the
topological frontier of the displayed closed hexagon. -/
def positiveE0BoundaryHexagonHomeomorph : PositiveE0Boundary ≃ₜ frontier Hexagon where
  toFun x := ⟨(positiveE0HexagonHomeomorph x.1 : Plane), by
    rw [frontier_hexagon]
    exact (positiveE0HexagonHomeomorph_mem_boundary_iff x.1).mpr x.2⟩
  invFun y := ⟨positiveE0HexagonHomeomorph.symm
    ⟨y.1, hexagon_isClosed.frontier_subset y.2⟩, by
    apply (positiveE0HexagonHomeomorph_mem_boundary_iff _).mp
    simpa only [Homeomorph.apply_symm_apply, ← frontier_hexagon] using y.2⟩
  left_inv x := Subtype.ext (positiveE0HexagonHomeomorph.symm_apply_apply x.1)
  right_inv y := by
    apply Subtype.ext
    change (positiveE0HexagonHomeomorph
      (positiveE0HexagonHomeomorph.symm
        ⟨y.1, hexagon_isClosed.frontier_subset y.2⟩) : Plane) = y.1
    rw [Homeomorph.apply_symm_apply]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp
      (positiveE0HexagonHomeomorph.continuous.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact positiveE0HexagonHomeomorph.symm.continuous.comp
      (continuous_subtype_val.subtype_mk _)

@[simp] theorem positiveE0BoundaryHexagonHomeomorph_coe (x : PositiveE0Boundary) :
    (positiveE0BoundaryHexagonHomeomorph x : Plane) =
      (positiveE0HexagonHomeomorph x.1 : Plane) := rfl

/-- The prescribed boundary map, expressed in actual polygon coordinates. -/
def polygonBoundaryConjugate (b : PositiveE0Boundary ≃ₜ PositiveE0Boundary) :
    frontier Hexagon ≃ₜ frontier Hexagon :=
  positiveE0BoundaryHexagonHomeomorph.symm.trans
    (b.trans positiveE0BoundaryHexagonHomeomorph)

@[simp] theorem polygonBoundaryConjugate_apply
    (b : PositiveE0Boundary ≃ₜ PositiveE0Boundary) (x : PositiveE0Boundary) :
    polygonBoundaryConjugate b (positiveE0BoundaryHexagonHomeomorph x) =
      positiveE0BoundaryHexagonHomeomorph (b x) := by
  change positiveE0BoundaryHexagonHomeomorph
    (b (positiveE0BoundaryHexagonHomeomorph.symm
      (positiveE0BoundaryHexagonHomeomorph x))) = _
  rw [Homeomorph.symm_apply_apply]

/-- A homeomorphism of the literal positive boundary cycle extends to the
literal positive component, not just to an abstract disk. -/
def positiveE0BoundaryExtension (b : PositiveE0Boundary ≃ₜ PositiveE0Boundary) :
    PositiveE0 ≃ₜ PositiveE0 :=
  positiveE0HexagonHomeomorph.trans
    ((CuspHoneycombRadial.boundarySetExtension hexagon_convex hexagon_isClosed
      hexagon_isBounded hexagon_interior_nonempty (polygonBoundaryConjugate b)).trans
        positiveE0HexagonHomeomorph.symm)

/-- The extension agrees exactly with the prescribed map on every actual
neighboring-component intersection, including the six triple points. -/
theorem positiveE0BoundaryExtension_boundary
    (b : PositiveE0Boundary ≃ₜ PositiveE0Boundary) (x : PositiveE0Boundary) :
    positiveE0BoundaryExtension b (x : PositiveE0) = (b x : PositiveE0) := by
  apply positiveE0HexagonHomeomorph.injective
  change positiveE0HexagonHomeomorph
    (positiveE0HexagonHomeomorph.symm
      (CuspHoneycombRadial.boundarySetExtension hexagon_convex hexagon_isClosed
        hexagon_isBounded hexagon_interior_nonempty (polygonBoundaryConjugate b)
          (positiveE0HexagonHomeomorph x.1))) = _
  rw [Homeomorph.apply_symm_apply]
  apply Subtype.ext
  have h := CuspHoneycombRadial.boundarySetExtension_frontier
    hexagon_convex hexagon_isClosed hexagon_isBounded hexagon_interior_nonempty
    (polygonBoundaryConjugate b) (positiveE0BoundaryHexagonHomeomorph x)
  simpa only [polygonBoundaryConjugate_apply,
    positiveE0BoundaryHexagonHomeomorph_coe] using h

theorem exists_positiveE0_boundary_extension
    (b : PositiveE0Boundary ≃ₜ PositiveE0Boundary) :
    ∃ F : PositiveE0 ≃ₜ PositiveE0,
      ∀ x : PositiveE0Boundary, F (x : PositiveE0) = (b x : PositiveE0) :=
  ⟨positiveE0BoundaryExtension b, positiveE0BoundaryExtension_boundary b⟩

end Wikipedia.HopfProblem.CuspHoneycombHexagon
