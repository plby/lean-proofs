/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Elementary power-value facts for Erdős Problem 477.
Formal author: Codex.
The existence of a tiling by sixth powers is not asserted in this file.
-/

import Mathlib

namespace Erdos477

/-- Nonnegative integral `d`th powers, regarded as a set of integers. -/
def PowerValues (d : ℕ) : Set ℤ := Set.range (fun n : ℕ => (n : ℤ) ^ d)

lemma even_power_range (d : ℕ) (hd : Even d) :
    Set.range (fun n : ℤ => n ^ d) = PowerValues d := by
  ext z
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n.natAbs, by simp only [Int.natCast_natAbs, hd.pow_abs]⟩
  · rintro ⟨n, rfl⟩
    exact ⟨(n : ℤ), rfl⟩

lemma sixth_power_value_range :
    Set.range (fun n : ℤ => (Polynomial.X ^ 6 : Polynomial ℤ).eval n) =
      PowerValues 6 := by
  simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
    even_power_range 6 (by decide)

lemma sixth_power_natDegree : (Polynomial.X ^ 6 : Polynomial ℤ).natDegree = 6 := by
  simp

/-- The last gap below a positive `d + 1`st power is at least its `d`th power. -/
lemma power_gap_lower_bound (u v d : ℕ) (hvu : v < u) :
    u ^ d + v ^ (d + 1) ≤ u ^ (d + 1) := by
  have hp : v ^ d ≤ u ^ d := Nat.pow_le_pow_left hvu.le d
  calc
    u ^ d + v ^ (d + 1) = u ^ d + v * v ^ d := by ring
    _ ≤ u ^ d + v * u ^ d := Nat.add_le_add_left (Nat.mul_le_mul_left v hp) _
    _ = (v + 1) * u ^ d := by ring
    _ ≤ u * u ^ d := Nat.mul_le_mul_right _ hvu
    _ = u ^ (d + 1) := by ring

/-- The factor measuring the gap between the inputs must be retained for the
unequal-sided boxes in Proposition 3.4 of the selected writeup. -/
lemma power_gap_mul_lower_bound (u v d : ℕ) (hvu : v ≤ u) :
    (u - v) * u ^ d + v ^ (d + 1) ≤ u ^ (d + 1) := by
  have hp : v ^ d ≤ u ^ d := Nat.pow_le_pow_left hvu d
  calc
    (u - v) * u ^ d + v ^ (d + 1) =
        (u - v) * u ^ d + v * v ^ d := by ring
    _ ≤ (u - v) * u ^ d + v * u ^ d :=
      Nat.add_le_add_left (Nat.mul_le_mul_left v hp) _
    _ = ((u - v) + v) * u ^ d := by ring
    _ = u ^ (d + 1) := by rw [Nat.sub_add_cancel hvu]; ring

lemma sixth_power_gap_separation (u v : ℕ) :
    |(u : ℤ) - (v : ℤ)| * ((max u v : ℕ) : ℤ) ^ 5 ≤
      |(u : ℤ) ^ 6 - (v : ℤ) ^ 6| := by
  wlog huv : v ≤ u generalizing u v
  · simpa only [abs_sub_comm, max_comm] using this v u (by omega)
  have hc : (v : ℤ) ≤ u := by exact_mod_cast huv
  have hg : ((u : ℤ) - v) * (u : ℤ) ^ 5 + (v : ℤ) ^ 6 ≤ (u : ℤ) ^ 6 := by
    exact_mod_cast power_gap_mul_lower_bound u v 5 huv
  have hp : (v : ℤ) ^ 6 ≤ (u : ℤ) ^ 6 := by
    exact_mod_cast Nat.pow_le_pow_left huv 6
  rw [max_eq_left huv, abs_of_nonneg (sub_nonneg.mpr hc),
    abs_of_nonneg (sub_nonneg.mpr hp)]
  linarith

/-- In particular, unequal sixth powers have a fifth-power lower bound on
their separation. This bounds the witnesses in a bad-shift equation. -/
lemma sixth_power_separation (u v : ℕ) (hne : u ≠ v) :
    ((max u v : ℕ) : ℤ) ^ 5 ≤ |(u : ℤ) ^ 6 - (v : ℤ) ^ 6| := by
  rcases lt_or_gt_of_ne hne with huv | hvu
  · have h : (v : ℤ) ^ 5 + (u : ℤ) ^ 6 ≤ (v : ℤ) ^ 6 := by
      exact_mod_cast power_gap_lower_bound v u 5 huv
    rw [max_eq_right huv.le]
    have hsign : (u : ℤ) ^ 6 - (v : ℤ) ^ 6 ≤ 0 := by
      have : 0 ≤ (v : ℤ) ^ 5 := by positivity
      omega
    rw [abs_of_nonpos hsign]
    omega
  · have h : (u : ℤ) ^ 5 + (v : ℤ) ^ 6 ≤ (u : ℤ) ^ 6 := by
      exact_mod_cast power_gap_lower_bound u v 5 hvu
    rw [max_eq_left hvu.le]
    have hsign : 0 ≤ (u : ℤ) ^ 6 - (v : ℤ) ^ 6 := by
      have : 0 ≤ (u : ℤ) ^ 5 := by positivity
      omega
    rw [abs_of_nonneg hsign]
    omega

#print axioms even_power_range
-- 'Erdos477.even_power_range' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms sixth_power_separation
-- 'Erdos477.sixth_power_separation' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos477
