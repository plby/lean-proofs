import Wikipedia.HopfProblem.CuspHoneycombCompatibleCell
import Wikipedia.HopfProblem.CuspHoneycombOppositeCoordinates

/-!
# Pointwise compatibility on every actual common cell edge

Every point on a shared dual-cell edge has an actual interval-side
parameter. Reversing that parameter subtracts the corresponding integral
ray in the plane and applies the corresponding positive-twist translation
in the toric space. Thus the constructed cell homeomorphism satisfies the
boundary identification at every edge point, including the endpoints.
-/

open Set Topology

namespace Wikipedia.HopfProblem.CuspHoneycombHexagon

open CuspHoneycombTiling ToricCharts ToricSpace ToricComponent CuspPositive

/-- The constructed cell homeomorphism respects the exact lattice gluing
on every point of each literal common edge. -/
theorem compatibleCellHomeomorph_opposite
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) (x : baseCell)
    (hx : (x : Plane) ∈ cell (hexagonRay k)) :
    ((compatibleCellHomeomorph C₀
      ⟨(x : Plane) - latticePoint (hexagonRay k), hx⟩).1 : Space) =
        twistedTranslate (positiveTwist C₀) (cuspVector (hexagonRay k))
          ((compatibleCellHomeomorph C₀ x).1 : Space) := by
  let y : Hexagon := standardHexagonDualHomeomorph.symm x
  have hy : (y : Plane) ∈ side k := by
    apply (standardHexagonDualHomeomorph_mem_cell_iff_side k y).mp
    simpa only [y, Homeomorph.apply_symm_apply] using hx
  obtain ⟨t, ht⟩ := (sideIntervalHomeomorph k).surjective ⟨y, hy⟩
  have hxt : standardHexagonDualHomeomorph
      ⟨(sideIntervalHomeomorph k t : Plane), (sideIntervalHomeomorph k t).2.1⟩ = x := by
    have hyt : (⟨(sideIntervalHomeomorph k t : Plane),
        (sideIntervalHomeomorph k t).2.1⟩ : Hexagon) = y :=
      Subtype.ext (congrArg (fun z : side k => (z : Plane)) ht)
    rw [hyt]
    exact standardHexagonDualHomeomorph.apply_symm_apply x
  have hshift : standardHexagonDualHomeomorph
      ⟨(sideIntervalHomeomorph (k + 3) (unitInterval.symm t) : Plane),
        (sideIntervalHomeomorph (k + 3) (unitInterval.symm t)).2.1⟩ =
      ⟨(x : Plane) - latticePoint (hexagonRay k), hx⟩ := by
    apply Subtype.ext
    change dualStandardPlaneHomeomorph.symm
      (sideIntervalHomeomorph (k + 3) (unitInterval.symm t) : Plane) =
        (x : Plane) - latticePoint (hexagonRay k)
    rw [dual_sideInterval_opposite]
    exact congrArg (fun z : baseCell => (z : Plane) - latticePoint (hexagonRay k)) hxt
  rw [← hshift, compatibleCellHomeomorph_sideInterval, ← hxt,
    compatibleCellHomeomorph_sideInterval]
  exact compatibleBoundaryArc_opposite_coe C₀ k t

/-- The same identity as an equality in the actual positive zero component. -/
theorem compatibleCellHomeomorph_shift_eq_opposite
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) (x : baseCell)
    (hx : (x : Plane) ∈ cell (hexagonRay k)) :
    compatibleCellHomeomorph C₀ ⟨(x : Plane) - latticePoint (hexagonRay k), hx⟩ =
      (oppositePositiveBoundaryHomeomorph C₀ k
        ⟨compatibleCellHomeomorph C₀ x,
          (compatibleCellHomeomorph_mem_boundary_iff C₀ x k).mpr hx⟩).1 := by
  apply Subtype.ext
  apply Subtype.ext
  exact compatibleCellHomeomorph_opposite C₀ k x hx

end Wikipedia.HopfProblem.CuspHoneycombHexagon
