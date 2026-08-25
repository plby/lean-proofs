import StackExchange.Puzzling139335.Definitions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Ordering three separated corner directions

With one direction fixed at angle zero, the other two nonacute directions
lie in the opposite closed semicircle. Their mutual separation places the
earlier angle at most at π and the later angle at least π/2 beyond it.
-/

namespace Puzzling139335.ThreeCorners

/-- A nonnegative angle with nonpositive cosine is at least π/2.
No upper bound on the angle is needed for this implication. -/
theorem half_pi_le_of_cos_nonpos {δ : ℝ} (hδ : 0 ≤ δ)
    (hcos : Real.cos δ ≤ 0) : Real.pi / 2 ≤ δ := by
  by_contra h
  have hpos : 0 < Real.cos δ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], lt_of_not_ge h⟩
  exact (not_lt_of_ge hcos) hpos

/-- Two angles in the opposite closed semicircle with nonpositive cosine
of their difference admit one of the two quarter-turn-separated orderings. -/
theorem angular_order_of_cos_sub_nonpos (θ φ : ℝ)
    (hθlo : Real.pi / 2 ≤ θ) (hθhi : θ ≤ 3 * Real.pi / 2)
    (hφlo : Real.pi / 2 ≤ φ) (hφhi : φ ≤ 3 * Real.pi / 2)
    (hcos : Real.cos (φ - θ) ≤ 0) :
    ((Real.pi / 2 ≤ θ ∧ θ ≤ Real.pi) ∧
      (θ + Real.pi / 2 ≤ φ ∧ φ ≤ 3 * Real.pi / 2)) ∨
    ((Real.pi / 2 ≤ φ ∧ φ ≤ Real.pi) ∧
      (φ + Real.pi / 2 ≤ θ ∧ θ ≤ 3 * Real.pi / 2)) := by
  rcases le_total θ φ with hθφ | hφθ
  · have hgap := half_pi_le_of_cos_nonpos (sub_nonneg.mpr hθφ) hcos
    exact Or.inl ⟨⟨hθlo, by linarith⟩, ⟨by linarith, hφhi⟩⟩
  · have hcos' : Real.cos (θ - φ) ≤ 0 := by
      calc
        Real.cos (θ - φ) = Real.cos (-(θ - φ)) := (Real.cos_neg _).symm
        _ = Real.cos (φ - θ) := by congr 1; ring
        _ ≤ 0 := hcos
    have hgap := half_pi_le_of_cos_nonpos (sub_nonneg.mpr hφθ) hcos'
    exact Or.inr ⟨⟨hφlo, by linarith⟩, ⟨by linarith, hθhi⟩⟩

end Puzzling139335.ThreeCorners
