import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

set_option maxHeartbeats 1000000

/-- Arithmetic core for the two new sum classes of a three-term critical
progression.  `pᵢ+dᵢ=f` are the occupied cardinalities in two `F`-cosets;
`k` is the vertical fibre size and `nᵢ` their integer projection sizes. -/
theorem progression_two_new_arithmetic
    (f k d₁ d₂ p₁ p₂ n₁ n₂ y₁₂ y₂₂ : ℕ)
    (hk : 0 < k) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hhalf : 2 * k ≤ f) (hdiv : k ∣ f)
    (hp₁ : p₁ + d₁ = f) (hp₂ : p₂ + d₂ = f)
    (hdef : 2 * (d₁ + d₂) ≤ f - 2)
    (hfib₁ : p₁ ≤ n₁ * k) (hfib₂ : p₂ ≤ n₂ * k)
    (hspan₁ : (n₁ - 1) * k ≤ f) (hspan₂ : (n₂ - 1) * k ≤ f)
    (hcross₁ : (n₁ + n₂ - 1) * p₁ ≤ n₁ * y₁₂)
    (hcross₂ : (n₁ + n₂ - 1) * p₂ ≤ n₂ * y₁₂)
    (hdouble : (2 * n₂ - 1) * p₂ ≤ n₂ * y₂₂) :
    3 * f ≤ 2 * (d₁ + d₂) + y₁₂ + y₂₂ := by
  have hf2 : 2 ≤ f := by omega
  have hdle : d₁ + d₂ ≤ f := by omega
  have hp₁eq : p₁ = f - d₁ := by omega
  have hp₂eq : p₂ = f - d₂ := by omega
  have hp₁k : k < p₁ := by omega
  have hp₂k : k < p₂ := by omega
  have hn₁2 : 2 ≤ n₁ := by
    by_contra h
    have : n₁ = 1 := by omega
    subst n₁
    omega
  have hn₂2 : 2 ≤ n₂ := by
    by_contra h
    have : n₂ = 1 := by omega
    subst n₂
    omega
  have hcross : p₁ + p₂ ≤ k + y₁₂ := by
    by_contra hbad
    have hy : y₁₂ + k < p₁ + p₂ := by omega
    have hs : n₁ + n₂ - 1 + 1 = n₁ + n₂ := by omega
    nlinarith
  have hdouble' : 2 * p₂ ≤ k + y₂₂ := by
    by_contra hbad
    have hy : k + y₂₂ < 2 * p₂ := by omega
    have hs : 2 * n₂ - 1 + 1 = 2 * n₂ := by omega
    nlinarith
  by_cases hlarge : 4 * k ≤ f
  · omega
  · obtain ⟨m, hm⟩ := hdiv
    have hmEq : f = k * m := hm
    have hm2 : 2 ≤ m := by
      have hh : k * 2 ≤ k * m := by simpa [hmEq, mul_comm] using hhalf
      exact Nat.le_of_mul_le_mul_left hh hk
    have hm4 : m < 4 := by
      by_contra h
      have hm4' : 4 ≤ m := by omega
      have hh : k * 4 ≤ k * m := Nat.mul_le_mul_left k hm4'
      have : 4 * k ≤ f := by simpa [hmEq, mul_comm] using hh
      omega
    have hmCases : m = 2 ∨ m = 3 := by omega
    rcases hmCases with rfl | rfl
    · have hn₁le : n₁ ≤ 3 := by
        have hh : (n₁ - 1) * k ≤ 2 * k := by simpa [hmEq, mul_comm] using hspan₁
        have hh' : n₁ - 1 ≤ 2 := Nat.le_of_mul_le_mul_right hh hk
        omega
      have hn₂le : n₂ ≤ 3 := by
        have hh : (n₂ - 1) * k ≤ 2 * k := by simpa [hmEq, mul_comm] using hspan₂
        have hh' : n₂ - 1 ≤ 2 := Nat.le_of_mul_le_mul_right hh hk
        omega
      interval_cases n₁ <;> interval_cases n₂ <;> norm_num at hcross₁ hcross₂ hdouble ⊢ <;> omega
    · have hn₁le : n₁ ≤ 4 := by
        have hh : (n₁ - 1) * k ≤ 3 * k := by simpa [hmEq, mul_comm] using hspan₁
        have hh' : n₁ - 1 ≤ 3 := Nat.le_of_mul_le_mul_right hh hk
        omega
      have hn₂le : n₂ ≤ 4 := by
        have hh : (n₂ - 1) * k ≤ 3 * k := by simpa [hmEq, mul_comm] using hspan₂
        have hh' : n₂ - 1 ≤ 3 := Nat.le_of_mul_le_mul_right hh hk
        omega
      interval_cases n₁ <;> interval_cases n₂ <;> norm_num at hcross₁ hcross₂ hdouble ⊢ <;> omega

end Erdos336
