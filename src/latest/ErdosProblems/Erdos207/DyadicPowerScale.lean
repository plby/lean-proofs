/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PowerSeparatedVortex
import Mathlib.Data.Nat.Log

/-!
# An integer power scale for arbitrary ambient orders

For a fixed denominator `E`, `dyadicPowerScale E n` is the largest power of
two whose exponent is a multiple-quotient of `log₂ n`.  Its `E`-th power is
at most `n` and within the fixed factor `2^E` of `n`.  This avoids real roots
and floor/ceiling bookkeeping in the eventual parameter hierarchy.
-/

namespace Erdos207

/-- A power-of-two integer scale asymptotic to `n^(1/E)`. -/
def dyadicPowerScale (E n : ℕ) : ℕ :=
  2 ^ (Nat.log 2 n / E)

lemma one_le_dyadicPowerScale (E n : ℕ) :
    1 ≤ dyadicPowerScale E n := by
  exact Nat.one_le_pow _ _ (by omega)

lemma dyadicPowerScale_pow (E n k : ℕ) :
    (dyadicPowerScale E n) ^ k =
      2 ^ ((Nat.log 2 n / E) * k) := by
  simp only [dyadicPowerScale, ← pow_mul]

/-- The defining scale never overshoots the ambient order in its `E`-th
power. -/
lemma dyadicPowerScale_pow_le
    {E n : ℕ} (hn : n ≠ 0) :
    (dyadicPowerScale E n) ^ E ≤ n := by
  rw [dyadicPowerScale_pow]
  exact (Nat.pow_le_pow_right (by omega)
    (Nat.div_mul_le_self (Nat.log 2 n) E)).trans
      (Nat.pow_log_le_self 2 hn)

/-- Conversely, the ambient order is at most the defining power times the
fixed dyadic rounding factor. -/
lemma le_two_pow_mul_dyadicPowerScale_pow
    {E n : ℕ} (hE : 0 < E) :
    n ≤ 2 ^ E * (dyadicPowerScale E n) ^ E := by
  let l := Nat.log 2 n
  let a := l / E
  have hquot : l < (a + 1) * E := by
    exact (Nat.div_lt_iff_lt_mul hE).mp (by
      simpa only [a] using Nat.lt_succ_self (l / E))
  rw [Nat.add_mul] at hquot
  have hexp : l + 1 ≤ E + a * E := by omega
  have hnlt : n < 2 ^ (l + 1) := by
    simpa only [l, Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (by omega : 1 < 2) n
  calc
    n ≤ 2 ^ (l + 1) := hnlt.le
    _ ≤ 2 ^ (E + a * E) := Nat.pow_le_pow_right (by omega) hexp
    _ = 2 ^ E * (dyadicPowerScale E n) ^ E := by
      simp only [pow_add, dyadicPowerScale_pow, a, l]

/-- Any prescribed fixed power of two is eventually below the dyadic scale.
This is the convenient threshold form used to discharge constant lower
bounds on the root size. -/
lemma pow_le_dyadicPowerScale_of_pow_mul_le
    {E n k : ℕ} (hE : 0 < E) (h : 2 ^ (k * E) ≤ n) :
    2 ^ k ≤ dyadicPowerScale E n := by
  have hn : n ≠ 0 := by
    intro hn
    subst n
    have : 0 < 2 ^ (k * E) := pow_pos (by omega) _
    omega
  have hlog : k * E ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by omega) h
  have hdiv : k ≤ Nat.log 2 n / E :=
    (Nat.le_div_iff_mul_le hE).2 hlog
  exact Nat.pow_le_pow_right (by omega) hdiv

lemma dyadicPowerScale_monotone (E : ℕ) :
    Monotone (dyadicPowerScale E) := by
  intro m n hmn
  apply Nat.pow_le_pow_right (by omega)
  exact Nat.div_le_div_right (Nat.log_mono_right hmn)

/-- Explicit threshold form of divergence of the dyadic scale. -/
lemma eventually_le_dyadicPowerScale
    {E : ℕ} (hE : 0 < E) (K : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K ≤ dyadicPowerScale E n := by
  have hK : K ≤ 2 ^ K := by
    induction K with
    | zero => simp
    | succ K ih =>
        have hpow : 1 ≤ 2 ^ K := Nat.one_le_two_pow
        rw [pow_succ]
        omega
  refine ⟨2 ^ (K * E), ?_⟩
  intro n hn
  exact hK.trans
    (pow_le_dyadicPowerScale_of_pow_mul_le hE hn)

/-- Any property true above a fixed integer scale is true for the dyadic
scale at every sufficiently large ambient order. -/
lemma eventually_dyadicPowerScale
    {E : ℕ} (hE : 0 < E) {P : ℕ → Prop}
    (hP : ∃ K : ℕ, ∀ t : ℕ, K ≤ t → P t) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → P (dyadicPowerScale E n) := by
  obtain ⟨K, hK⟩ := hP
  obtain ⟨N, hN⟩ := eventually_le_dyadicPowerScale hE K
  exact ⟨N, fun n hn ↦ hK _ (hN n hn)⟩

end Erdos207
