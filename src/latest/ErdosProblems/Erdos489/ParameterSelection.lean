import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

/-- Mertens-free parameter selection for the affine progression argument.
The factorial progression modulus contains every small prime; choosing `C`
by an Archimedean ceiling preserves the cancellation of its square in the
coprime-pair error. -/
theorem exists_affine_sieve_parameters
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ Y Q C : ℕ,
      0 < Y ∧ 1 < Q ∧ 0 < C ∧
      (∀ p, Nat.Prime p → p ≤ Y → p ∣ Q) ∧
      (4 : ℝ) / (C : ℝ) ≤ ρ / (2 * (Q : ℝ)) ∧
      64 * C ^ 2 ≤ Q ^ 2 * Y := by
  obtain ⟨y, hy⟩ := exists_nat_ge (10000 / ρ ^ 2)
  let Y := max 2 y
  let Q := Y.factorial
  let C := ⌈(8 * (Q : ℝ)) / ρ⌉₊
  have hY2 : 2 ≤ Y := le_max_left 2 y
  have hY : 0 < Y := by omega
  have hQ : 1 < Q := by
    dsimp [Q]
    exact Nat.one_lt_factorial.mpr (by omega)
  have hQ0 : 0 < Q := hQ.trans' Nat.zero_lt_one
  have hYn : 10000 / ρ ^ 2 ≤ (Y : ℝ) := by
    exact hy.trans (by exact_mod_cast le_max_right 2 y)
  have hx0 : 0 ≤ (8 * (Q : ℝ)) / ρ := by positivity
  have hxpos : 0 < (8 * (Q : ℝ)) / ρ := by positivity
  have hceilLower : (8 * (Q : ℝ)) / ρ ≤ (C : ℝ) := by
    dsimp [C]
    exact Nat.le_ceil _
  have hC : 0 < C := by
    have hCR : (0 : ℝ) < C := hxpos.trans_le hceilLower
    exact_mod_cast hCR
  have hCposR : (0 : ℝ) < C := by exact_mod_cast hC
  have hsmall : ∀ p, Nat.Prime p → p ≤ Y → p ∣ Q := by
    intro p hp hpY
    dsimp [Q]
    exact Nat.dvd_factorial hp.pos hpY
  have hdensity : (4 : ℝ) / (C : ℝ) ≤ ρ / (2 * (Q : ℝ)) := by
    rw [div_le_div_iff₀ hCposR (by positivity : (0 : ℝ) < 2 * Q)]
    have hc := (div_le_iff₀ hρ).mp hceilLower
    nlinarith
  have hceilUpper : (C : ℝ) < (8 * (Q : ℝ)) / ρ + 1 := by
    dsimp [C]
    exact Nat.ceil_lt_add_one hx0
  have hρQ : ρ ≤ (Q : ℝ) := by
    have hQone : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
    exact hρ1.trans hQone
  have hone : (1 : ℝ) ≤ (Q : ℝ) / ρ :=
    (le_div_iff₀ hρ).2 (by simpa using hρQ)
  have hCupperDiv : (C : ℝ) ≤ 10 * (Q : ℝ) / ρ := by
    have h8 : (8 * (Q : ℝ)) / ρ = 8 * ((Q : ℝ) / ρ) := by ring
    have h10 : (10 * (Q : ℝ)) / ρ = 10 * ((Q : ℝ) / ρ) := by ring
    rw [h8] at hceilUpper
    rw [h10]
    have hratio0 : 0 ≤ (Q : ℝ) / ρ := by positivity
    linarith
  have hCupper : ρ * (C : ℝ) ≤ 10 * (Q : ℝ) := by
    have := (le_div_iff₀ hρ).mp hCupperDiv
    nlinarith
  have hCupper0 : 0 ≤ ρ * (C : ℝ) := by positivity
  have hQupper0 : 0 ≤ 10 * (Q : ℝ) := by positivity
  have hCsq : ρ ^ 2 * (C : ℝ) ^ 2 ≤ 100 * (Q : ℝ) ^ 2 := by
    have hs := (sq_le_sq₀ hCupper0 hQupper0).2 hCupper
    nlinarith
  have hYrho : (10000 : ℝ) ≤ (Y : ℝ) * ρ ^ 2 := by
    exact (div_le_iff₀ (sq_pos_of_pos hρ)).mp hYn
  have hleft := mul_le_mul_of_nonneg_left hCsq (show (0 : ℝ) ≤ 100 by positivity)
  have hright := mul_le_mul_of_nonneg_right hYrho
    (show (0 : ℝ) ≤ (Q : ℝ) ^ 2 by positivity)
  have hchain : ρ ^ 2 * (100 * (C : ℝ) ^ 2) ≤
      ρ ^ 2 * ((Q : ℝ) ^ 2 * (Y : ℝ)) := by
    calc
      ρ ^ 2 * (100 * (C : ℝ) ^ 2) =
          100 * (ρ ^ 2 * (C : ℝ) ^ 2) := by ring
      _ ≤ 100 * (100 * (Q : ℝ) ^ 2) := hleft
      _ = 10000 * (Q : ℝ) ^ 2 := by ring
      _ ≤ ((Y : ℝ) * ρ ^ 2) * (Q : ℝ) ^ 2 := hright
      _ = ρ ^ 2 * ((Q : ℝ) ^ 2 * (Y : ℝ)) := by ring
  have h100 : 100 * (C : ℝ) ^ 2 ≤ (Q : ℝ) ^ 2 * (Y : ℝ) :=
    le_of_mul_le_mul_left hchain (sq_pos_of_pos hρ)
  have h64R : (64 : ℝ) * (C : ℝ) ^ 2 ≤
      (Q : ℝ) ^ 2 * (Y : ℝ) := by
    have hC2 : (0 : ℝ) ≤ (C : ℝ) ^ 2 := by positivity
    nlinarith
  have h64 : 64 * C ^ 2 ≤ Q ^ 2 * Y := by exact_mod_cast h64R
  exact ⟨Y, Q, C, hY, hQ, hC, hsmall, hdensity, h64⟩

end Erdos489
