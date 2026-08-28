import Wikipedia.HopfProblem.CuspHoneycombCellBoundary
import Wikipedia.HopfProblem.CuspHoneycombBoundaryGluing
import Wikipedia.HopfProblem.CuspHoneycombCompatibleArcs
import Wikipedia.HopfProblem.CuspHoneycombLinearBridgeSides

/-!
# A genuine hexagonal cell map respecting opposite boundary gluing

The six constructed compatible arc maps glue on their actual common
endpoints. Their boundary homeomorphism is extended across the actual
positive zero component by the explicit radial construction. Thus the
resulting cell map uses the given positive twist, and no boundary map or
cell homeomorphism is supplied as an assumption.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspHoneycombHexagon

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ)

/-- The actual six compatible arcs glued into a boundary-cycle map. -/
def compatibleBoundaryHomeomorph : PositiveE0Boundary ≃ₜ PositiveE0Boundary :=
  boundaryGluingHomeomorph (compatibleBoundaryArc C₀)
    (fun k => congrArg Subtype.val (compatibleBoundaryArc_zero C₀ k))
    (fun k => congrArg Subtype.val (compatibleBoundaryArc_one C₀ k))

theorem compatibleBoundaryHomeomorph_arc (k : Fin 6) (t : unitInterval) :
    compatibleBoundaryHomeomorph C₀
      (boundaryArcInclusion k (positiveBoundaryArc k t)) =
        boundaryArcInclusion k (compatibleBoundaryArc C₀ k t) :=
  boundaryGluingHomeomorph_apply _ _ _ k t

/-- The boundary map extended over the literal positive toric component. -/
def compatibleComponentHomeomorph : PositiveE0 ≃ₜ PositiveE0 :=
  positiveE0BoundaryExtension (compatibleBoundaryHomeomorph C₀)

theorem compatibleComponentHomeomorph_arc (k : Fin 6) (t : unitInterval) :
    compatibleComponentHomeomorph C₀ (positiveBoundaryArc k t).1 =
      (compatibleBoundaryArc C₀ k t).1 := by
  exact (positiveE0BoundaryExtension_boundary (compatibleBoundaryHomeomorph C₀)
    (boundaryArcInclusion k (positiveBoundaryArc k t))).trans
      (congrArg Subtype.val (compatibleBoundaryHomeomorph_arc C₀ k t))

/-- Each original component intersection is preserved, not only their union. -/
theorem compatibleComponentHomeomorph_mem_boundary_iff (x : PositiveE0) (k : Fin 6) :
    compatibleComponentHomeomorph C₀ x ∈ positiveBoundary k ↔ x ∈ positiveBoundary k := by
  constructor
  · intro hx
    obtain ⟨t, ht⟩ := (compatibleBoundaryArc C₀ k).surjective
      ⟨compatibleComponentHomeomorph C₀ x, hx⟩
    have he : (positiveBoundaryArc k t).1 = x := by
      apply (compatibleComponentHomeomorph C₀).injective
      rw [compatibleComponentHomeomorph_arc]
      exact congrArg Subtype.val ht
    rw [← he]
    exact (positiveBoundaryArc k t).2
  · intro hx
    obtain ⟨t, ht⟩ := (positiveBoundaryArc k).surjective ⟨x, hx⟩
    have he : (positiveBoundaryArc k t).1 = x := congrArg Subtype.val ht
    rw [← he, compatibleComponentHomeomorph_arc]
    exact (compatibleBoundaryArc C₀ k t).2

/-- The closed standard polygon mapped to the actual component, with the
modified boundary required by the positive lattice action. -/
def compatibleHexagonHomeomorph : Hexagon ≃ₜ PositiveE0 :=
  positiveE0HexagonHomeomorph.symm.trans (compatibleComponentHomeomorph C₀)

theorem compatibleHexagonHomeomorph_sideInterval (k : Fin 6) (t : unitInterval) :
    compatibleHexagonHomeomorph C₀
      ⟨(sideIntervalHomeomorph k t : Plane), (sideIntervalHomeomorph k t).2.1⟩ =
        (compatibleBoundaryArc C₀ k t).1 :=
  compatibleComponentHomeomorph_arc C₀ k t

theorem compatibleHexagonHomeomorph_mem_boundary_iff (x : Hexagon) (k : Fin 6) :
    compatibleHexagonHomeomorph C₀ x ∈ positiveBoundary k ↔ (x : Plane) ∈ side k := by
  change compatibleComponentHomeomorph C₀ (positiveE0HexagonHomeomorph.symm x) ∈
    positiveBoundary k ↔ _
  rw [compatibleComponentHomeomorph_mem_boundary_iff]
  exact (positiveE0HexagonHomeomorph_mem_side_iff
    (positiveE0HexagonHomeomorph.symm x) k).symm.trans (by
      rw [Homeomorph.apply_symm_apply])

/-- The actual dual honeycomb cell, centered at zero, mapped onto the
actual positive zero component. -/
def compatibleCellHomeomorph : CuspHoneycombTiling.baseCell ≃ₜ PositiveE0 :=
  CuspHoneycombTiling.standardHexagonDualHomeomorph.symm.trans
    (compatibleHexagonHomeomorph C₀)

theorem compatibleCellHomeomorph_sideInterval (k : Fin 6) (t : unitInterval) :
    compatibleCellHomeomorph C₀
      (CuspHoneycombTiling.standardHexagonDualHomeomorph
        ⟨(sideIntervalHomeomorph k t : Plane), (sideIntervalHomeomorph k t).2.1⟩) =
      (compatibleBoundaryArc C₀ k t).1 := by
  change compatibleHexagonHomeomorph C₀
    (CuspHoneycombTiling.standardHexagonDualHomeomorph.symm
      (CuspHoneycombTiling.standardHexagonDualHomeomorph _)) = _
  rw [Homeomorph.symm_apply_apply]
  exact compatibleHexagonHomeomorph_sideInterval C₀ k t

theorem compatibleCellHomeomorph_mem_boundary_iff
    (x : CuspHoneycombTiling.baseCell) (k : Fin 6) :
    compatibleCellHomeomorph C₀ x ∈ positiveBoundary k ↔
      (x : Plane) ∈ CuspHoneycombTiling.cell (ToricComponent.hexagonRay k) := by
  change compatibleHexagonHomeomorph C₀
    (CuspHoneycombTiling.standardHexagonDualHomeomorph.symm x) ∈ positiveBoundary k ↔ _
  rw [compatibleHexagonHomeomorph_mem_boundary_iff]
  have h := CuspHoneycombTiling.standardHexagonDualHomeomorph_mem_cell_iff_side k
    (CuspHoneycombTiling.standardHexagonDualHomeomorph.symm x)
  simpa only [Homeomorph.apply_symm_apply] using h.symm

end Wikipedia.HopfProblem.CuspHoneycombHexagon
