import Submission.TwoCirclesIntersectionsAtMostTwo

/-!
# Circles used in the proof of Erdős Problem 652

The radius is kept as part of the key.  This lets us count the circles even
when two different centers happen to determine the same numerical radius.
-/

open Classical
noncomputable section

namespace Erdos652

abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- A circle is keyed by its center and radius. -/
abbrev CircleKey := Point × ℝ

/-- The point set of a (possibly empty or degenerate) keyed circle. -/
def circle (a : CircleKey) : Set Point := {x | dist x a.1 = a.2}

@[simp] lemma mem_circle {a : CircleKey} {x : Point} :
    x ∈ circle a ↔ dist x a.1 = a.2 := Iff.rfl

/-- Two differently keyed circles have at most two common points. -/
lemma circle_intersection_atMostTwo {a b : CircleKey} (hab : a ≠ b) :
    (circle a ∩ circle b).Finite ∧ (circle a ∩ circle b).ncard ≤ 2 := by
  by_cases hc : a.1 = b.1
  · have hr : a.2 ≠ b.2 := by
      intro hr
      exact hab (Prod.ext hc hr)
    have hempty : circle a ∩ circle b = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, mem_circle, Set.mem_empty_iff_false, iff_false]
      rintro ⟨ha, hb⟩
      apply hr
      calc
        a.2 = dist x a.1 := ha.symm
        _ = dist x b.1 := by rw [hc]
        _ = b.2 := hb
    simp [hempty]
  · simpa [circle, Set.setOf_and] using
      (TwoCirclesIntersectionsAtMostTwo a.1 b.1 hc a.2 b.2)

end Erdos652
