/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.DivisibleSmallMass
import ErdosProblems.Erdos822.HarmonicElementary

/-!
# Reciprocal mass of integers whose predecessor is divisible
-/

namespace Erdos822

open scoped BigOperators

def predDivisibleUpTo (N p : ℕ) : Finset ℕ :=
  (Finset.Icc 2 N).filter fun l => p ∣ l - 1

theorem predDivisibleUpTo_eq_image
    {N p : ℕ} (hp : 0 < p) :
    predDivisibleUpTo N p =
      (Finset.Icc 1 ((N - 1) / p)).image fun j => p * j + 1 := by
  ext l
  simp only [predDivisibleUpTo, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_image]
  constructor
  · rintro ⟨⟨hl2, hlN⟩, hdiv⟩
    refine ⟨(l - 1) / p, ?_, ?_⟩
    · constructor
      · apply Nat.div_pos
        · have hple : p ≤ l - 1 := Nat.le_of_dvd (by omega) hdiv
          exact hple
        · exact hp
      · apply (Nat.le_div_iff_mul_le hp).2
        have hmul : p * ((l - 1) / p) = l - 1 :=
          Nat.mul_div_cancel' hdiv
        have hmul' : ((l - 1) / p) * p = l - 1 := by
          simpa [Nat.mul_comm] using hmul
        rw [hmul']
        omega
    · have hmul : p * ((l - 1) / p) = l - 1 :=
        Nat.mul_div_cancel' hdiv
      omega
  · rintro ⟨j, ⟨hj1, hjN⟩, rfl⟩
    constructor
    · constructor
      · have : 0 < p * j := Nat.mul_pos hp (by omega)
        omega
      · have hmul : p * j ≤ N - 1 :=
          by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp).1 hjN
        have hpos : 0 < p * j := Nat.mul_pos hp (by omega)
        omega
    · rw [Nat.add_sub_cancel]
      exact dvd_mul_right p j

theorem sum_inv_predDivisibleUpTo_le
    {N p : ℕ} (hp : 0 < p) :
    ∑ l ∈ predDivisibleUpTo N p, (1 : ℝ) / l ≤
      (harmonic N : ℝ) / p := by
  rw [predDivisibleUpTo_eq_image hp, Finset.sum_image]
  · calc
      (∑ j ∈ Finset.Icc 1 ((N - 1) / p),
          (1 : ℝ) / ((p * j + 1 : ℕ) : ℝ)) ≤
          ∑ j ∈ Finset.Icc 1 ((N - 1) / p),
            (1 : ℝ) / ((p * j : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have hpj : (0 : ℝ) < ((p * j : ℕ) : ℝ) := by
          exact_mod_cast Nat.mul_pos hp (Finset.mem_Icc.mp hj).1
        exact one_div_le_one_div_of_le hpj (by exact_mod_cast
          (Nat.le_add_right (p * j) 1))
      _ = (harmonic ((N - 1) / p) : ℝ) / p := by
        rw [harmonic_eq_sum_Icc, Rat.cast_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [Rat.cast_inv, Rat.cast_natCast]
        push_cast
        ring
      _ ≤ (harmonic N : ℝ) / p := by
        apply div_le_div_of_nonneg_right
          (harmonic_cast_mono ((Nat.div_le_self (N - 1) p).trans
            (Nat.sub_le N 1)))
        positivity
  · intro i hi j hj hij
    have : p * i = p * j := Nat.add_right_cancel hij
    exact Nat.eq_of_mul_eq_mul_left hp this

end Erdos822
