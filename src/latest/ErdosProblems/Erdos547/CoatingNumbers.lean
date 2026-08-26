import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Integer rounding and size estimates for tree padding
-/

namespace Erdos547

theorem coating_numbers (η ρ : ℝ) (hρ : 0 < ρ) (hρη : ρ ≤ η) (hη : η ≤ 1 / 10)
    (K n : ℕ) (hK : 720 ≤ ρ * K) (hn : 4 ≤ ρ * n)
    (hbudget : 4 * (K : ℝ) + 5 ≤ 2 * η * n) :
    ∃ m ℓ a : ℕ, 2 ≤ ℓ ∧ ℓ ≤ n + 4 * m + 1 ∧ 180 * (n + 4 * m + 1) ≤ ℓ * K ∧
      ℓ + K ≤ m ∧ a + K ≤ m ∧ η * n ≤ a ∧
      ((n + 4 * m + 1 : ℕ) : ℝ) ≤ (1 + 10 * η) * n ∧
      (ℓ : ℝ) ≤ ρ * (n + 4 * m + 1 : ℕ) := by
  let ℓ := Nat.floor (ρ * n)
  let a := Nat.ceil (η * n)
  let m := ℓ + K + a
  let N := n + 4 * m + 1
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hη0 : 0 ≤ η := hρ.le.trans hρη
  have hℓle : (ℓ : ℝ) ≤ ρ * n := Nat.floor_le (mul_nonneg hρ.le hn0)
  have hℓgt : ρ * n < (ℓ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hℓhalf : ρ * n / 2 ≤ (ℓ : ℝ) := by linarith only [hℓgt, hn]
  have hℓtwo : 2 ≤ ℓ := by
    have hh : (2 : ℝ) ≤ ℓ := by linarith only [hℓhalf, hn]
    exact_mod_cast hh
  have hale : η * n ≤ (a : ℝ) := Nat.le_ceil _
  have hagt : (a : ℝ) < η * n + 1 := Nat.ceil_lt_add_one (mul_nonneg hη0 hn0)
  have hN : (N : ℝ) = n + 4 * (ℓ : ℝ) + 4 * K + 4 * a + 1 := by
    dsimp [N, m]
    push_cast
    ring
  have hρηn := mul_le_mul_of_nonneg_right hρη hn0
  have hsize : (N : ℝ) ≤ (1 + 10 * η) * n := by
    nlinarith only [hN, hℓle, hagt, hρηn, hbudget]
  have hNtwo : (N : ℝ) ≤ 2 * n := by
    have hh := mul_le_mul_of_nonneg_right hη hn0
    nlinarith only [hsize, hh]
  have hmass : (180 : ℝ) * N ≤ (ℓ : ℝ) * K := by
    have h₁ := mul_le_mul_of_nonneg_right hℓhalf hK0
    have h₂ := mul_le_mul_of_nonneg_right hK hn0
    nlinarith only [hNtwo, h₁, h₂]
  have hmassNat : 180 * N ≤ ℓ * K := by exact_mod_cast hmass
  have hnN : n ≤ N := by dsimp [N]; omega
  have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hℓN : ℓ ≤ N := by
    have hρone : ρ ≤ 1 := by linarith only [hρη, hη]
    have hh := mul_le_mul_of_nonneg_right hρone hn0
    have he : (ℓ : ℝ) ≤ N := by linarith only [hℓle, hh, hnN']
    exact_mod_cast he
  have hsmall : (ℓ : ℝ) ≤ ρ * N :=
    hℓle.trans (mul_le_mul_of_nonneg_left hnN' hρ.le)
  exact ⟨m, ℓ, a, hℓtwo, hℓN, hmassNat, by dsimp [m]; omega,
    by dsimp [m]; omega, hale, hsize, hsmall⟩

theorem eventually_coating_numbers (η ρ : ℝ) (hρ : 0 < ρ) (hρη : ρ ≤ η)
    (hη : η ≤ 1 / 10) : ∃ K n₀ : ℕ, ∀ n ≥ n₀,
    ∃ m ℓ a : ℕ, 2 ≤ ℓ ∧ ℓ ≤ n + 4 * m + 1 ∧ 180 * (n + 4 * m + 1) ≤ ℓ * K ∧
      ℓ + K ≤ m ∧ a + K ≤ m ∧ η * n ≤ a ∧
      ((n + 4 * m + 1 : ℕ) : ℝ) ≤ (1 + 10 * η) * n ∧
      (ℓ : ℝ) ≤ ρ * (n + 4 * m + 1 : ℕ) := by
  let K := Nat.ceil (720 / ρ)
  have hK : 720 ≤ ρ * K := by
    have hh : 720 / ρ ≤ (K : ℝ) := Nat.le_ceil _
    exact (div_le_iff₀ hρ).mp hh |>.trans_eq (mul_comm _ _)
  have hηpos : 0 < 2 * η := by linarith only [hρ, hρη]
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge (max (4 / ρ) ((4 * (K : ℝ) + 5) / (2 * η)))
  refine ⟨K, n₀, ?_⟩
  intro n hn
  have hn' : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hfirst := (le_max_left (4 / ρ) ((4 * (K : ℝ) + 5) / (2 * η))).trans (hn₀.trans hn')
  have hsecond := (le_max_right (4 / ρ) ((4 * (K : ℝ) + 5) / (2 * η))).trans (hn₀.trans hn')
  have hnsize : 4 ≤ ρ * n := by
    have hh := (div_le_iff₀ hρ).mp hfirst
    nlinarith only [hh]
  have hbudget : 4 * (K : ℝ) + 5 ≤ 2 * η * n := by
    have hh := (div_le_iff₀ hηpos).mp hsecond
    nlinarith only [hh]
  exact coating_numbers η ρ hρ hρη hη K n hK hnsize hbudget

end Erdos547

#print axioms Erdos547.eventually_coating_numbers
