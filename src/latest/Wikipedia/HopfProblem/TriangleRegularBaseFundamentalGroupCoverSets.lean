import Mathlib.Analysis.Complex.Convex
import Mathlib.Tactic.Linarith

/-!
# An explicit slit cover of the twice-punctured complex plane

Removing the downward rays at real coordinates zero and one gives the
upper slit domain; removing the upward rays gives the lower slit domain.
They cover exactly the plane punctured at zero and one.  Their overlap
is the complement of the two complete vertical lines.
-/

noncomputable section

open Set Complex
open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- The plane with the downward imaginary rays from zero and one removed. -/
def upperSlitPlane : Set ℂ := {z | 0 < z.im ∨ (z.re ≠ 0 ∧ z.re ≠ 1)}

/-- The plane with the upward imaginary rays from zero and one removed. -/
def lowerSlitPlane : Set ℂ := {z | z.im < 0 ∨ (z.re ≠ 0 ∧ z.re ≠ 1)}

theorem upperSlitPlane_isOpen : IsOpen upperSlitPlane :=
  (isOpen_lt continuous_const continuous_im).union
    ((isOpen_ne_fun continuous_re continuous_const).inter
      (isOpen_ne_fun continuous_re continuous_const))

theorem lowerSlitPlane_isOpen : IsOpen lowerSlitPlane :=
  (isOpen_lt continuous_im continuous_const).union
    ((isOpen_ne_fun continuous_re continuous_const).inter
      (isOpen_ne_fun continuous_re continuous_const))

theorem upperSlitPlane_subset_punctured : upperSlitPlane ⊆ {z : ℂ | z ≠ 0 ∧ z ≠ 1} := by
  intro z hz
  constructor
  · rintro rfl
    simp [upperSlitPlane] at hz
  · rintro rfl
    simp [upperSlitPlane] at hz

theorem lowerSlitPlane_subset_punctured : lowerSlitPlane ⊆ {z : ℂ | z ≠ 0 ∧ z ≠ 1} := by
  intro z hz
  constructor
  · rintro rfl
    simp [lowerSlitPlane] at hz
  · rintro rfl
    simp [lowerSlitPlane] at hz

/-- The two actual slit domains cover exactly the twice-punctured plane. -/
theorem slitPlanes_union :
    upperSlitPlane ∪ lowerSlitPlane = {z : ℂ | z ≠ 0 ∧ z ≠ 1} := by
  ext z
  constructor
  · rintro (hz | hz)
    · exact upperSlitPlane_subset_punctured hz
    · exact lowerSlitPlane_subset_punctured hz
  · rintro ⟨hzero, hone⟩
    by_cases hp : 0 < z.im
    · exact Or.inl (Or.inl hp)
    by_cases hn : z.im < 0
    · exact Or.inr (Or.inl hn)
    have hi : z.im = 0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
    apply Or.inl
    apply Or.inr
    constructor
    · intro hr
      apply hzero
      apply Complex.ext <;> simp_all
    · intro hr
      apply hone
      apply Complex.ext <;> simp_all

/-- Their overlap is exactly the complement of the two vertical lines. -/
theorem slitPlanes_inter :
    upperSlitPlane ∩ lowerSlitPlane = {z : ℂ | z.re ≠ 0 ∧ z.re ≠ 1} := by
  ext z
  constructor
  · rintro ⟨hp | hx, hn | hx'⟩
    · linarith
    · exact hx'
    · exact hx
    · exact hx
  · intro hx
    exact ⟨Or.inr hx, Or.inr hx⟩

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
