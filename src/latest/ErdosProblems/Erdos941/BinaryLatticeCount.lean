import ErdosProblems.Erdos941.LatticeStripCount
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # A quadratic lattice-point bound with a square-root error -/

namespace Erdos941

theorem completed_square_lattice_count {A H : ℝ} (hA : 0 < A) (hH : 0 < H) (c : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℝ, 0 ≤ X → ∀ s : Finset (ℤ × ℤ),
      (∀ z ∈ s, A * ((z.1 : ℝ) + c * (z.2 : ℝ)) ^ 2 + H * (z.2 : ℝ) ^ 2 ≤ X) →
      (s.card : ℝ) ≤ 4 * X / (Real.sqrt A * Real.sqrt H) + K * Real.sqrt X + 1 := by
  let K : ℝ := 2 / Real.sqrt A + 2 / Real.sqrt H
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro X hX s hs
  have hstrip : ∀ z ∈ s, |(z.2 : ℝ)| ≤ Real.sqrt (X / H) ∧
      |(z.1 : ℝ) + c * (z.2 : ℝ)| ≤ Real.sqrt (X / A) := by
    intro z hz
    have hh := hs z hz
    constructor
    · apply Real.abs_le_sqrt
      apply (le_div_iff₀ hH).mpr
      nlinarith [mul_nonneg hA.le (sq_nonneg ((z.1 : ℝ) + c * z.2))]
    · apply Real.abs_le_sqrt
      apply (le_div_iff₀ hA).mpr
      nlinarith [mul_nonneg hH.le (sq_nonneg (z.2 : ℝ))]
  have hbound := integer_strip_count s (Real.sqrt_nonneg (X / A))
    (Real.sqrt_nonneg (X / H)) hstrip
  rw [Real.sqrt_div hX A, Real.sqrt_div hX H] at hbound
  apply hbound.trans_eq
  calc
    _ = 4 * Real.sqrt X ^ 2 / (Real.sqrt A * Real.sqrt H) + K * Real.sqrt X + 1 := by
      dsimp [K]
      ring
    _ = _ := by rw [Real.sq_sqrt hX]

theorem binary_lattice_count {A B C : ℝ} (hA : 0 < A) (hD : 0 < A * C - B ^ 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℝ, 0 ≤ X → ∀ s : Finset (ℤ × ℤ),
      (∀ z ∈ s, A * (z.1 : ℝ) ^ 2 + 2 * B * (z.1 : ℝ) * (z.2 : ℝ) +
        C * (z.2 : ℝ) ^ 2 ≤ X) →
      (s.card : ℝ) ≤ 4 * X / Real.sqrt (A * C - B ^ 2) + K * Real.sqrt X + 1 := by
  obtain ⟨K, hK, hcount⟩ := completed_square_lattice_count hA (div_pos hD hA) (B / A)
  refine ⟨K, hK, ?_⟩
  intro X hX s hs
  have hbound := hcount X hX s (by
    intro z hz
    have heq : A * ((z.1 : ℝ) + B / A * (z.2 : ℝ)) ^ 2 +
        ((A * C - B ^ 2) / A) * (z.2 : ℝ) ^ 2 =
        A * (z.1 : ℝ) ^ 2 + 2 * B * (z.1 : ℝ) * (z.2 : ℝ) + C * (z.2 : ℝ) ^ 2 := by
      field_simp
      ring
    rw [heq]
    exact hs z hz)
  have hsqrt : Real.sqrt A * Real.sqrt ((A * C - B ^ 2) / A) =
      Real.sqrt (A * C - B ^ 2) := by
    rw [← Real.sqrt_mul hA.le, mul_div_cancel₀ _ hA.ne']
  rwa [hsqrt] at hbound

end Erdos941
