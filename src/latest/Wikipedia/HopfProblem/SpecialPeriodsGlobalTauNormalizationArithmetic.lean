import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

/-!
# Finite integral calculations for the modular normalization

Completed-square inequalities reduce the determinant and trace equations
to four integer pairs.  The remaining cases give exactly the three
matrices needed in the normalization argument.  We also record the six
integral unit pairs for the quadratic form `p² - p r + r²`.
-/

namespace Wikipedia.HopfProblem.SpecialPeriods.GlobalTauNormalization

/-- The determinant-one, trace-minus-two normalization equations have
exactly these three possible integer triples. -/
theorem trace_neg_two_triples (p q r : ℤ)
    (hdet : -p ^ 2 - q * r = 1) (htr : p + q - r = -2) :
    (p = 0 ∧ q = -1 ∧ r = 1) ∨
      (p = 1 ∧ q = -2 ∧ r = 1) ∨ (p = 1 ∧ q = -1 ∧ r = 2) := by
  have hq : q = r - p - 2 := by omega
  rw [hq] at hdet
  have hquad : p ^ 2 - p * r + r ^ 2 - 2 * r + 1 = 0 := by
    nlinarith only [hdet]
  have hp₀ : 0 ≤ p := by
    nlinarith only [hquad, sq_nonneg (2 * r - p - 2), sq_nonneg p]
  have hp_upper : 2 * p ≤ 3 := by
    nlinarith only [hquad, sq_nonneg (2 * r - p - 2), sq_nonneg (p - 1)]
  have hp₁ : p ≤ 1 := by omega
  have hr_lower : 4 ≤ 8 * r := by
    nlinarith only [hquad, sq_nonneg (2 * p - r), sq_nonneg r]
  have hr_upper : 10 * r ≤ 23 := by
    nlinarith only [hquad, sq_nonneg (2 * p - r), sq_nonneg (r - 3)]
  have hr₁ : 1 ≤ r := by omega
  have hr₂ : r ≤ 2 := by omega
  have hp_cases : p = 0 ∨ p = 1 := by omega
  have hr_cases : r = 1 ∨ r = 2 := by omega
  rcases hp_cases with rfl | rfl
  · rcases hr_cases with rfl | rfl
    · left
      omega
    · norm_num at hquad
  · rcases hr_cases with rfl | rfl
    · right
      left
      omega
    · right
      right
      omega

private theorem three_sq_le_four_bounds (x : ℤ) (hx : 3 * x ^ 2 ≤ 4) :
    -1 ≤ x ∧ x ≤ 1 := by
  have hl : -16 ≤ 12 * x := by
    nlinarith only [hx, sq_nonneg (x + 2)]
  have hu : 12 * x ≤ 16 := by
    nlinarith only [hx, sq_nonneg (x - 2)]
  omega

/-- The six integer unit pairs of the quadratic form of discriminant
`-3`, used for integral matrices fixing the elliptic point. -/
theorem norm_unit_pairs (p r : ℤ) (hnorm : p ^ 2 - p * r + r ^ 2 = 1) :
    (p = 1 ∧ r = 0) ∨ (p = -1 ∧ r = 0) ∨
      (p = 0 ∧ r = 1) ∨ (p = 0 ∧ r = -1) ∨
      (p = 1 ∧ r = 1) ∨ (p = -1 ∧ r = -1) := by
  have hp_sq : 3 * p ^ 2 ≤ 4 := by
    nlinarith only [hnorm, sq_nonneg (2 * r - p)]
  have hr_sq : 3 * r ^ 2 ≤ 4 := by
    nlinarith only [hnorm, sq_nonneg (2 * p - r)]
  obtain ⟨hp₁, hp₂⟩ := three_sq_le_four_bounds p hp_sq
  obtain ⟨hr₁, hr₂⟩ := three_sq_le_four_bounds r hr_sq
  interval_cases p <;> interval_cases r <;>
    first | decide | norm_num at hnorm

end Wikipedia.HopfProblem.SpecialPeriods.GlobalTauNormalization
