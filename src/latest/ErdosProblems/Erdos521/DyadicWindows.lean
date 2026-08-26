/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Disjoint coefficient windows for separated dyadic spatial scales.
Formal proof: Codex.
-/
import Mathlib

namespace Erdos521

def dyadicCoefficientWindow (n k q : ℕ) : Finset ℕ :=
  Finset.Icc (2 ^ (k - q)) (min n (2 ^ (k + q)))

theorem same_mod_gap {i j m : ℕ} (hij : i < j) (hmod : i % m = j % m) : i + m ≤ j := by
  have hdiv : m ∣ j - i := (Nat.modEq_iff_dvd' hij.le).mp hmod
  have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt hij) hdiv
  omega

theorem dyadicCoefficientWindow_disjoint (n q i j : ℕ) (hgap : i + 2 * q + 1 ≤ j) :
    Disjoint (dyadicCoefficientWindow n i q) (dyadicCoefficientWindow n j q) := by
  have hexp : i + q < j - q := by omega
  have hpow : 2 ^ (i + q) < 2 ^ (j - q) := Nat.pow_lt_pow_right (by norm_num) hexp
  apply Finset.disjoint_left.mpr
  intro k hki hkj
  have hi := Finset.mem_Icc.mp hki
  have hj := Finset.mem_Icc.mp hkj
  have hle : k ≤ 2 ^ (i + q) := hi.2.trans (min_le_right _ _)
  omega

theorem dyadicCoefficientWindow_disjoint_same_color (n q : ℕ) {i j : ℕ}
    (hij : i ≠ j) (hmod : i % (2 * q + 1) = j % (2 * q + 1)) :
    Disjoint (dyadicCoefficientWindow n i q) (dyadicCoefficientWindow n j q) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact dyadicCoefficientWindow_disjoint n q i j (by have := same_mod_gap h hmod; omega)
  · exact (dyadicCoefficientWindow_disjoint n q j i (by have := same_mod_gap h hmod.symm; omega)).symm

end Erdos521
