import StackExchange.Puzzling139335.N4HalfLeg.Left
import StackExchange.Puzzling139335.N4HalfLeg.Reflection
import StackExchange.Puzzling139335.N4Axial.EqualRows
import StackExchange.Puzzling139335.N4OuterPair.Contacts

/-!
# Both outer side legs stop before the midline

A half-height left leg forces all nontrivial right contacts to pull back
to acute source faces whose horizontal normal component exceeds four
fifths. The actual right gap is too long for one such face, or for two
faces with distinct normals. Equal normals would make the relative middle
congruence axial and are excluded by the actual axial obstruction.

Vertical reflection gives the right-leg result. Consequently the actual
side-contact heights both lie strictly between zero and one half.
-/

open Set

namespace Puzzling139335.N4OuterPair.Configuration

open N4HalfLeg PlaneIsometries

variable {d : SquareDissection}

/-- The lower outer piece cannot reach the left side midpoint when the
center lies in the interior of one actual piece. -/
theorem left_halfleg_not_mem (h : Configuration d) (hc : d.HasProtectedCenter) :
    Schoenflies.Plane.mk 0 (1 / 2) ∉ d.piece 0 := by
  intro hleft
  apply left_halfleg_impossible_of_distinct_rows h hc hleft
  intro e f he hf htwo hthree heq
  exact h.false_of_middle_right_contact_equal_first_rows hc e f he hf
    htwo.nonempty hthree.nonempty (congrArg Prod.fst heq) (congrArg Prod.snd heq)

/-- The corresponding right side midpoint is excluded by reflecting the
whole actual dissection vertically. -/
theorem right_halfleg_not_mem (h : Configuration d) (hc : d.HasProtectedCenter) :
    Schoenflies.Plane.mk 1 (1 / 2) ∉ d.piece 0 := by
  intro hright
  exact (reflectedConfiguration h).left_halfleg_not_mem
    (reflectedConfiguration_protected hc) (left_halfleg_mem_of_right hright)

/-- Both actual outer side contacts have positive height strictly less
than one half. The two upper contacts are their horizontal reflections. -/
theorem exists_side_contact_heights_strict (h : Configuration d)
    (hc : d.HasProtectedCenter) :
    ∃ a b : ℝ, a ∈ Ioo (0 : ℝ) (1 / 2) ∧ b ∈ Ioo (0 : ℝ) (1 / 2) ∧
      (∀ y : ℝ, Schoenflies.Plane.mk 0 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) a) ∧
      (∀ y : ℝ, Schoenflies.Plane.mk 1 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) b) ∧
      (∀ y : ℝ, Schoenflies.Plane.mk 0 y ∈ d.piece 1 ↔ y ∈ Icc (1 - a) (1 : ℝ)) ∧
      (∀ y : ℝ, Schoenflies.Plane.mk 1 y ∈ d.piece 1 ↔ y ∈ Icc (1 - b) (1 : ℝ)) := by
  obtain ⟨a, b, ha, hb, hleft, hright, hupperLeft, hupperRight⟩ :=
    h.exists_side_contact_heights hc
  have haStrict : a < (1 / 2 : ℝ) := by
    by_contra hnot
    exact h.left_halfleg_not_mem hc ((hleft (1 / 2)).mpr
      ⟨by norm_num, le_of_not_gt hnot⟩)
  have hbStrict : b < (1 / 2 : ℝ) := by
    by_contra hnot
    exact h.right_halfleg_not_mem hc ((hright (1 / 2)).mpr
      ⟨by norm_num, le_of_not_gt hnot⟩)
  exact ⟨a, b, ⟨ha.1, haStrict⟩, ⟨hb.1, hbStrict⟩,
    hleft, hright, hupperLeft, hupperRight⟩

end Puzzling139335.N4OuterPair.Configuration
