import ErdosProblems.Erdos587.DyadicScaleBudgets

/-! An explicit logarithmic enlargement supplies the cubic surplus. -/

namespace Erdos587

lemma dyadic_cube_identity (t e : ℕ) :
    (2 ^ (4 * t + e)) ^ 3 = 2 ^ (12 * t) * 2 ^ (3 * e) := by
  rw [← pow_mul, ← pow_add]
  congr 1
  ring

theorem dyadic_surplus_budgets (Z B e₀ t : ℕ)
    (he₀ : Z * 4 ^ (4 * B) + 4 * Z + 1 ≤ 2 ^ e₀) :
    let l := 12 * t + 1
    let e := e₀ + (4 * B) * (Nat.log 2 l + 1)
    let H := 2 ^ (4 * t + e)
    Z * (2 ^ (12 * t) + 1) < H ^ 3 ∧
      Z * 2 ^ (12 * t) * (4 * l) ^ (4 * B) ≤ H ^ 3 := by
  intro l e H
  have hN : 1 ≤ 2 ^ (12 * t) := one_le_pow₀ (by omega)
  have hl : 0 < l := by dsimp [l]; omega
  have hround := (dyadic_round_up_bounds hl).1
  have he₀e : e₀ ≤ 3 * e := by dsimp [e]; omega
  have hee : e ≤ 3 * e := by omega
  have hscale : Z * (4 * l) ^ (4 * B) ≤ 2 ^ e := by
    calc
      _ = (Z * 4 ^ (4 * B)) * l ^ (4 * B) := by rw [mul_pow]; ring
      _ ≤ 2 ^ e₀ * (2 ^ (Nat.log 2 l + 1)) ^ (4 * B) :=
        Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hround _)
      _ = 2 ^ e := by rw [← pow_mul, ← pow_add]; congr 1; dsimp [e]; ring
  constructor
  · calc
      Z * (2 ^ (12 * t) + 1) ≤ (2 * Z) * 2 ^ (12 * t) := by nlinarith only [hN]
      _ < 2 ^ e₀ * 2 ^ (12 * t) := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
      _ ≤ 2 ^ (3 * e) * 2 ^ (12 * t) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) he₀e)
      _ = H ^ 3 := by rw [mul_comm, ← dyadic_cube_identity]
  · calc
      Z * 2 ^ (12 * t) * (4 * l) ^ (4 * B) = 2 ^ (12 * t) * (Z * (4 * l) ^ (4 * B)) := by ring
      _ ≤ 2 ^ (12 * t) * 2 ^ e := Nat.mul_le_mul_left _ hscale
      _ ≤ 2 ^ (12 * t) * 2 ^ (3 * e) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hee)
      _ = H ^ 3 := by rw [← dyadic_cube_identity]

theorem dyadic_threshold_upper (Z d e₀ t : ℕ) :
    let l := 12 * t + 1
    let e := e₀ + d * (Nat.log 2 l + 1)
    Z * l ^ 2 * 2 ^ (4 * t + e) ≤
      (Z * 2 ^ (e₀ + d)) * 2 ^ (4 * t) * l ^ (d + 2) := by
  intro l e
  have hl : 0 < l := by dsimp [l]; omega
  have hround := (dyadic_round_up_bounds hl).2
  have hscale : 2 ^ e ≤ 2 ^ e₀ * (2 * l) ^ d := by
    calc
      _ = 2 ^ e₀ * (2 ^ (Nat.log 2 l + 1)) ^ d := by
        rw [← pow_mul, ← pow_add]; congr 1; dsimp [e]; ring
      _ ≤ 2 ^ e₀ * (2 * l) ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hround _)
  calc
    _ = Z * l ^ 2 * (2 ^ (4 * t) * 2 ^ e) := by rw [pow_add]
    _ ≤ Z * l ^ 2 * (2 ^ (4 * t) * (2 ^ e₀ * (2 * l) ^ d)) := by gcongr
    _ = (Z * 2 ^ (e₀ + d)) * 2 ^ (4 * t) * l ^ (d + 2) := by
      rw [pow_add, pow_add, mul_pow]
      ring

end Erdos587
