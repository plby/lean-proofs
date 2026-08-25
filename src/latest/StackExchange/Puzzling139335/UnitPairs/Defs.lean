import StackExchange.Puzzling139335.SquareGeometry

/-!
# Actual placements of intrinsic unit pairs and full square corners
-/

open Set Metric

namespace Puzzling139335.UnitPairs

/-- The signed area, multiplied by two, of the oriented triangle `a b x`. -/
def sideDet (a b x : Plane) : ℝ :=
  (b 0 - a 0) * (x 1 - a 1) - (b 1 - a 1) * (x 0 - a 0)

/-- Both endpoints belong to the set, are one unit apart, and an actual
Euclidean placement of the entire set puts them at square corners.  Their
unit distance makes those two corners adjacent. -/
def IsUnitSidePair (P : Set Plane) (a b : Plane) : Prop :=
  a ∈ P ∧ b ∈ P ∧ dist a b = 1 ∧
    ∃ e : Plane ≃ᵃⁱ[ℝ] Plane, ∃ i j : Fin 4,
      e '' P ⊆ unitSquare ∧ e a = corner i ∧ e b = corner j

/-- An actual square placement in which the set contains a full relative
neighborhood of the specified corner. -/
def IsFullSquareCorner (P : Set Plane) (a : Plane) : Prop :=
  ∃ e : Plane ≃ᵃⁱ[ℝ] Plane, ∃ i : Fin 4, ∃ ε : ℝ,
    0 < ε ∧ e '' P ⊆ unitSquare ∧ e a = corner i ∧
      ball (corner i) ε ∩ unitSquare ⊆ e '' P

theorem IsUnitSidePair.symm {P : Set Plane} {a b : Plane}
    (h : IsUnitSidePair P a b) : IsUnitSidePair P b a := by
  obtain ⟨ha, hb, hd, e, i, j, he, hea, heb⟩ := h
  exact ⟨hb, ha, by simpa [dist_comm] using hd, e, j, i, he, heb, hea⟩

theorem IsUnitSidePair.ne {P : Set Plane} {a b : Plane}
    (h : IsUnitSidePair P a b) : a ≠ b := by
  intro hab
  have hd := h.2.2.1
  simp [hab] at hd

end Puzzling139335.UnitPairs
