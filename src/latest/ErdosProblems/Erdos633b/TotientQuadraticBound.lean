import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! An elementary uniform bound n <= 2*phi(n)^2. Coprime induction
uses the stronger odd case, so the factor two is incurred only once. -/

namespace Erdos633b

theorem prime_power_totient_square_bounds (p k : ℕ) (hp : p.Prime) :
    (Odd (p ^ k) → p ^ k ≤ (p ^ k).totient ^ 2) ∧
      p ^ k ≤ 2 * (p ^ k).totient ^ 2 := by
  cases k with
  | zero => simp
  | succ k =>
    rw [Nat.totient_prime_pow_succ hp]
    have hpp : 0 < p ^ k := pow_pos hp.pos _
    have hpowsq : p ^ k ≤ (p ^ k) ^ 2 := by nlinarith
    have hp2 : 2 ≤ p := hp.two_le
    have hpred : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
    constructor
    · intro ho
      have hpo : Odd p := (Nat.odd_pow_iff (by omega : k + 1 ≠ 0)).mp ho
      have hp3 : 3 ≤ p := by
        have hne : p ≠ 2 := by
          intro he
          rw [he] at hpo
          obtain ⟨j, hj⟩ := hpo
          omega
        omega
      have hbase : p ≤ (p - 1) ^ 2 := by nlinarith
      calc
        p ^ (k + 1) = p ^ k * p := pow_succ _ _
        _ ≤ (p ^ k) ^ 2 * (p - 1) ^ 2 := Nat.mul_le_mul hpowsq hbase
        _ = (p ^ k * (p - 1)) ^ 2 := by ring
    · have hbase : p ≤ 2 * (p - 1) ^ 2 := by nlinarith
      calc
        p ^ (k + 1) = p ^ k * p := pow_succ _ _
        _ ≤ (p ^ k) ^ 2 * (2 * (p - 1) ^ 2) := Nat.mul_le_mul hpowsq hbase
        _ = 2 * (p ^ k * (p - 1)) ^ 2 := by ring

theorem totient_square_bounds (n : ℕ) :
    (Odd n → n ≤ n.totient ^ 2) ∧ n ≤ 2 * n.totient ^ 2 := by
  refine Nat.recOnPrimeCoprime ?_ ?_ ?_ n
  · simp
  · exact prime_power_totient_square_bounds
  · intro a b _ _ hab ha hb
    rw [Nat.totient_mul hab]
    constructor
    · intro ho
      obtain ⟨hao, hbo⟩ := Nat.odd_mul.mp ho
      calc
        a * b ≤ a.totient ^ 2 * b.totient ^ 2 := Nat.mul_le_mul (ha.1 hao) (hb.1 hbo)
        _ = (a.totient * b.totient) ^ 2 := by ring
    · have ho : Odd a ∨ Odd b := by
        rcases Nat.even_or_odd a with hae | hao
        · exact Or.inr (Nat.coprime_two_left.mp (Nat.Coprime.of_dvd_left hae.two_dvd hab))
        · exact Or.inl hao
      rcases ho with hao | hbo
      · calc
          a * b ≤ a.totient ^ 2 * (2 * b.totient ^ 2) := Nat.mul_le_mul (ha.1 hao) hb.2
          _ = 2 * (a.totient * b.totient) ^ 2 := by ring
      · calc
          a * b ≤ (2 * a.totient ^ 2) * b.totient ^ 2 := Nat.mul_le_mul ha.2 (hb.1 hbo)
          _ = 2 * (a.totient * b.totient) ^ 2 := by ring

theorem le_two_mul_totient_sq (n : ℕ) : n ≤ 2 * n.totient ^ 2 := (totient_square_bounds n).2

theorem le_288_of_totient_le_twelve (n : ℕ) (h : n.totient ≤ 12) : n ≤ 288 := by
  have hh := le_two_mul_totient_sq n
  nlinarith

end Erdos633b
