/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SharpScheduledPairTrajectories

/-!
# Cross-multiplied bounds for the sharp pair rates

These lemmas keep all rounding in natural-number inequalities.  They expose
the two rational comparisons used by the quadratic barriers without asking
the eventual power arithmetic to manipulate inverses in `ℝ`.
-/

namespace Erdos207

noncomputable section

/-- A cross-multiplied lower bound for the scheduled upper drift. -/
lemma div_le_sharpScheduledPairUpperRate
    (P a b M d u : ℕ)
    (hP : 0 < P) (hb : 0 < b) (hM : 0 < M)
    (havailability : 3 * M ≤ P * u)
    (hloss : a * u ≤ b * (3 * d - 2 - u)) :
    ((3 * a * d : ℕ) : ℝ) / (b * P : ℕ) ≤
      sharpScheduledPairUpperRate M d u := by
  have hden : (0 : ℝ) < (b * P : ℕ) := by positivity
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  rw [sharpScheduledPairUpperRate]
  have hrhs : (M : ℝ)⁻¹ * d * (3 * d - 2 - u : ℕ) =
      ((d * (3 * d - 2 - u) : ℕ) : ℝ) / M := by
    rw [div_eq_mul_inv]
    push_cast
    ring
  rw [hrhs]
  rw [div_le_div_iff₀ hden hM']
  have havail : 3 * a * M ≤ a * P * u := by
    nlinarith [Nat.mul_le_mul_left a havailability]
  have hloss' : a * P * u ≤ b * P * (3 * d - 2 - u) := by
    nlinarith [Nat.mul_le_mul_left P hloss]
  have hnat : (3 * a * d) * M ≤
      (d * (3 * d - 2 - u)) * (b * P) := by
    nlinarith [Nat.mul_le_mul_left d (havail.trans hloss')]
  exact_mod_cast hnat

/-- A cross-multiplied upper bound for the scheduled lower drift. -/
lemma sharpScheduledPairLowerRate_le_div
    (P c D u Kinc : ℕ)
    (hP : 0 < P) (hDgap : u < D)
    (hscalar : P * (u * (2 * u) + Kinc) ≤ c * u * (D - u)) :
    sharpScheduledPairLowerRate D u Kinc ≤
      ((c * u : ℕ) : ℝ) / P := by
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  have hdenNat : 0 < D - u := Nat.sub_pos_of_lt hDgap
  have hden : (0 : ℝ) < (D - u : ℕ) := by exact_mod_cast hdenNat
  rw [sharpScheduledPairLowerRate]
  have hlhs : ((D - u : ℕ) : ℝ)⁻¹ *
      (((u : ℝ) * (2 * u : ℕ)) + Kinc) =
      ((u * (2 * u) + Kinc : ℕ) : ℝ) / (D - u : ℕ) := by
    rw [div_eq_mul_inv]
    push_cast
    ring
  rw [hlhs]
  rw [div_le_div_iff₀ hden hP']
  exact_mod_cast (by simpa [Nat.mul_comm] using hscalar)

/-- Rational cross-multiplied variant of
`sharpScheduledPairLowerRate_le_div`.  This avoids rounding a coefficient
which is asymptotic to six up to a vanishing error. -/
lemma sharpScheduledPairLowerRate_le_div_ratio
    (P a b D u Kinc : ℕ)
    (hP : 0 < P) (hb : 0 < b) (hDgap : u < D)
    (hscalar : b * P * (u * (2 * u) + Kinc) ≤
      a * u * (D - u)) :
    sharpScheduledPairLowerRate D u Kinc ≤
      ((a * u : ℕ) : ℝ) / (b * P : ℕ) := by
  have hP' : (0 : ℝ) < (b * P : ℕ) := by positivity
  have hdenNat : 0 < D - u := Nat.sub_pos_of_lt hDgap
  have hden : (0 : ℝ) < (D - u : ℕ) := by exact_mod_cast hdenNat
  rw [sharpScheduledPairLowerRate]
  have hlhs : ((D - u : ℕ) : ℝ)⁻¹ *
      (((u : ℝ) * (2 * u : ℕ)) + Kinc) =
      ((u * (2 * u) + Kinc : ℕ) : ℝ) / (D - u : ℕ) := by
    rw [div_eq_mul_inv]
    push_cast
    ring
  rw [hlhs]
  rw [div_le_div_iff₀ hden hP']
  exact_mod_cast (by simpa [Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using hscalar)

/-- A direct cross-multiplied criterion ordering the conservative upper and
lower deletion rates. -/
lemma sharpScheduledPairUpperRate_le_lowerRate
    (M D d u Kinc : ℕ)
    (hM : 0 < M) (hgap : u < D)
    (hscalar : d * (3 * d - 2 - u) * (D - u) ≤
      M * (u * (2 * u) + Kinc)) :
    sharpScheduledPairUpperRate M d u ≤
      sharpScheduledPairLowerRate D u Kinc := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hdenNat : 0 < D - u := Nat.sub_pos_of_lt hgap
  have hden : (0 : ℝ) < (D - u : ℕ) := by exact_mod_cast hdenNat
  rw [sharpScheduledPairUpperRate, sharpScheduledPairLowerRate]
  have hleft : (M : ℝ)⁻¹ * d * (3 * d - 2 - u : ℕ) =
      ((d * (3 * d - 2 - u) : ℕ) : ℝ) / M := by
    rw [div_eq_mul_inv]
    push_cast
    ring
  have hright : ((D - u : ℕ) : ℝ)⁻¹ *
      (((u : ℝ) * (2 * u : ℕ)) + Kinc) =
      ((u * (2 * u) + Kinc : ℕ) : ℝ) / (D - u : ℕ) := by
    rw [div_eq_mul_inv]
    push_cast
    ring
  rw [hleft, hright, div_le_div_iff₀ hM' hden]
  exact_mod_cast (by simpa [Nat.mul_comm] using hscalar)

end

end Erdos207
