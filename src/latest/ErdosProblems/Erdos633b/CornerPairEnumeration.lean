import Mathlib.Data.Finset.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-! Exact finite exhaustion of lexicographically sorted nonzero corner pairs
whose two positive column totals are at most three. Every exclusion is
proved by integer arithmetic in Lean, not by an external enumeration oracle. -/

namespace Erdos633b

def cornerPairPatterns : Finset ((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) :=
  {((0, 1), (0, 2), (1, 0)),
    ((0, 1), (1, 0), (1, 1)),
    ((0, 1), (0, 2), (2, 0)),
    ((0, 1), (1, 0), (1, 2)),
    ((0, 2), (1, 0), (1, 1)),
    ((0, 1), (1, 0), (2, 0)),
    ((0, 1), (1, 0), (2, 1)),
    ((0, 1), (1, 1), (2, 0)),
    ((0, 2), (1, 0), (2, 0)),
    ((0, 1), (0, 2), (3, 0)),
    ((0, 1), (1, 0), (2, 2)),
    ((0, 1), (1, 1), (2, 1)),
    ((0, 1), (1, 2), (2, 0)),
    ((0, 2), (1, 0), (2, 1)),
    ((0, 2), (1, 1), (2, 0)),
    ((0, 3), (1, 0), (2, 0)),
    ((1, 0), (1, 1), (1, 2))}

theorem corner_pairs_zero_zero (p₂ q₀ q₁ q₂ : ℕ)
    (hq₀ : 0 < q₀) (hq₁ : q₀ < q₁) (hQ : q₀ + q₁ + q₂ ≤ 3)
    (hPpos : 0 < p₂) (hP : p₂ ≤ 3) :
    ((0, q₀), (0, q₁), (p₂, q₂)) ∈ cornerPairPatterns := by
  have he₀ : q₀ = 1 := by omega
  have he₁ : q₁ = 2 := by omega
  have he₂ : q₂ = 0 := by omega
  subst q₀ q₁ q₂
  interval_cases p₂ <;> norm_num [cornerPairPatterns]

theorem corner_pairs_zero_one_one (q₀ q₁ q₂ : ℕ)
    (hq₀ : 0 < q₀) (hq₁ : q₁ < q₂) (hQ : q₀ + q₁ + q₂ ≤ 3) :
    ((0, q₀), (1, q₁), (1, q₂)) ∈ cornerPairPatterns := by
  have he₁ : q₁ = 0 := by omega
  subst q₁
  have hq₀' : q₀ ≤ 2 := by omega
  interval_cases q₀
  · have hq₂lo : 1 ≤ q₂ := by omega
    have hq₂hi : q₂ ≤ 2 := by omega
    interval_cases q₂ <;> norm_num [cornerPairPatterns]
  · have he₂ : q₂ = 1 := by omega
    subst q₂
    norm_num [cornerPairPatterns]

theorem corner_pairs_zero_one_two (q₀ q₁ q₂ : ℕ)
    (hq₀ : 0 < q₀) (hQ : q₀ + q₁ + q₂ ≤ 3) :
    ((0, q₀), (1, q₁), (2, q₂)) ∈ cornerPairPatterns := by
  have hq₀' : q₀ ≤ 3 := by omega
  interval_cases q₀
  · have hq₁ : q₁ ≤ 2 := by omega
    interval_cases q₁
    · have hq₂ : q₂ ≤ 2 := by omega
      interval_cases q₂ <;> norm_num [cornerPairPatterns]
    · have hq₂ : q₂ ≤ 1 := by omega
      interval_cases q₂ <;> norm_num [cornerPairPatterns]
    · have hq₂ : q₂ = 0 := by omega
      subst q₂
      norm_num [cornerPairPatterns]
  · have hq₁ : q₁ ≤ 1 := by omega
    interval_cases q₁
    · have hq₂ : q₂ ≤ 1 := by omega
      interval_cases q₂ <;> norm_num [cornerPairPatterns]
    · have hq₂ : q₂ = 0 := by omega
      subst q₂
      norm_num [cornerPairPatterns]
  · have hq₁ : q₁ = 0 := by omega
    have hq₂ : q₂ = 0 := by omega
    subst q₁ q₂
    norm_num [cornerPairPatterns]

theorem sorted_corner_pairs_exhaustive (p₀ q₀ p₁ q₁ p₂ q₂ : ℕ)
    (hn₀ : 0 < p₀ + q₀) (hn₁ : 0 < p₁ + q₁) (hn₂ : 0 < p₂ + q₂)
    (h₀₁ : p₀ < p₁ ∨ p₀ = p₁ ∧ q₀ < q₁)
    (h₁₂ : p₁ < p₂ ∨ p₁ = p₂ ∧ q₁ < q₂)
    (hPpos : 0 < p₀ + p₁ + p₂) (hP : p₀ + p₁ + p₂ ≤ 3)
    (hQpos : 0 < q₀ + q₁ + q₂) (hQ : q₀ + q₁ + q₂ ≤ 3) :
    ((p₀, q₀), (p₁, q₁), (p₂, q₂)) ∈ cornerPairPatterns := by
  have hp₀ : p₀ ≤ 1 := by omega
  interval_cases p₀
  · have hp₁ : p₁ ≤ 1 := by omega
    interval_cases p₁
    · exact corner_pairs_zero_zero p₂ q₀ q₁ q₂ (by omega) (by omega) hQ
        (by omega) (by omega)
    · have hp₂ : p₂ = 1 ∨ p₂ = 2 := by omega
      rcases hp₂ with rfl | rfl
      · exact corner_pairs_zero_one_one q₀ q₁ q₂ (by omega) (by omega) hQ
      · exact corner_pairs_zero_one_two q₀ q₁ q₂ (by omega) hQ
  · have hp₁ : p₁ = 1 := by omega
    have hp₂ : p₂ = 1 := by omega
    subst p₁ p₂
    have hq₀ : q₀ = 0 := by omega
    have hq₁ : q₁ = 1 := by omega
    have hq₂ : q₂ = 2 := by omega
    subst q₀ q₁ q₂
    norm_num [cornerPairPatterns]

end Erdos633b
