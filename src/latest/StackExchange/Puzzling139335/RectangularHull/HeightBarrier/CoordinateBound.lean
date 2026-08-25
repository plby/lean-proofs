import StackExchange.Puzzling139335.Definitions
import Wikipedia.SchoenfliesTheorem.Bounded

/-!
# An upper coordinate bound for bounded complementary components

The open halfplane above a set is connected and unbounded. Consequently no
bounded complementary component can meet that halfplane. This argument does
not require the set to be a Jordan curve.
-/

open Set

namespace Puzzling139335.RectangularHull

private theorem not_isBounded_coord_one_gt (h : ℝ) :
    ¬ Bornology.IsBounded {p : Plane | h < p 1} := by
  intro hbounded
  obtain ⟨R, -, hR⟩ := Schoenflies.Plane.exists_closedSquare_of_isBounded hbounded
  have hp : Schoenflies.Plane.mk 0 (max R h + 1) ∈ {p : Plane | h < p 1} := by
    change h < max R h + 1
    linarith [le_max_right R h]
  have hbound := hR hp
  simp only [Schoenflies.Plane.closedSquare, mem_ofPred_eq,
    Schoenflies.Plane.supDist_zero, Schoenflies.Plane.supNorm,
    max_le_iff] at hbound
  have hcoord : |max R h + 1| ≤ R := hbound.2
  linarith [hcoord, le_abs_self (max R h + 1), le_max_left R h]

/-- Every bounded complementary component inherits an upper bound on the
second coordinate from the original set. -/
theorem inside_coord_one_le {C : Set Plane} {h : ℝ}
    (hC : ∀ p ∈ C, p 1 ≤ h) {p : Plane} (hp : p ∈ Schoenflies.inside C) :
    p 1 ≤ h := by
  by_contra hph
  have hpgt : h < p 1 := lt_of_not_ge hph
  have hsub : {q : Plane | h < q 1} ⊆ Cᶜ := by
    intro q hq hqC
    exact (not_lt_of_ge (hC q hqC)) hq
  have hcomponent : {q : Plane | h < q 1} ⊆ connectedComponentIn Cᶜ p :=
    (Schoenflies.Plane.convex_coord_gt 1 h).isPreconnected.subset_connectedComponentIn
      hpgt hsub
  exact not_isBounded_coord_one_gt h
    ((Schoenflies.mem_inside_iff.mp hp).2.subset hcomponent)

/-- The same upper bound holds on the closure of the bounded complementary
regions, since a coordinate halfspace is closed. -/
theorem closure_inside_coord_one_le {C : Set Plane} {h : ℝ}
    (hC : ∀ p ∈ C, p 1 ≤ h) {p : Plane} (hp : p ∈ closure (Schoenflies.inside C)) :
    p 1 ≤ h := by
  have hsub : Schoenflies.inside C ⊆ {q : Plane | q 1 ≤ h} :=
    fun _ hq => inside_coord_one_le hC hq
  exact closure_minimal hsub
    (isClosed_le (Schoenflies.Plane.continuous_coord 1) continuous_const) hp

end Puzzling139335.RectangularHull
