import ErdosProblems.Erdos633b.NonnegativeEigenvectors
import Mathlib.Tactic.FinCases

/-! A nonnegative 3×3 matrix with a positive L-eigenvector and a nonzero
−L-eigenvector either has zero diagonal or contains a closed two-cycle. -/

namespace Erdos633b.NonnegativeMatrix

open Matrix

theorem three_diagonal_alternative {D : Matrix (Fin 3) (Fin 3) ℝ}
    (hD : ∀ i j, 0 ≤ D i j) {v w : Fin 3 → ℝ} {L : ℝ}
    (hv : ∀ i, 0 < v i) (hL : 0 < L) (hw : w ≠ 0)
    (hpos : D *ᵥ v = L • v) (hneg : D *ᵥ w = -L • w) :
    (∀ i, D i i = 0) ∨
      ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ 0 < D k k ∧
        0 < D i j ∧ 0 < D j i ∧
        (∀ l, l ≠ j → D i l = 0) ∧ (∀ l, l ≠ i → D j l = 0) := by
  classical
  by_cases hd : ∀ i, D i i = 0
  · exact Or.inl hd
  right
  push Not at hd
  obtain ⟨k, hk⟩ := hd
  have hkpos : 0 < D k k := lt_of_le_of_ne (hD k k) (Ne.symm hk)
  obtain ⟨i, j, hij, hii, hjj, hijpos, hi, hj, hmaxi, hmaxj⟩ :=
    exists_two_zero_diagonals hD hv hL hw hpos hneg
  have hik : i ≠ k := by intro h; subst i; exact hk hii
  have hjk : j ≠ k := by intro h; subst j; exact hk hjj
  have hik0 := positive_diagonal_excluded_of_max hD hv hpos hneg i hmaxi hi k hkpos
  have hjk0 := positive_diagonal_excluded_of_max hD hv hpos hneg j hmaxj hj k hkpos
  have hrowi (l : Fin 3) (hl : l ≠ j) : D i l = 0 := by
    by_cases hli : l = i
    · rwa [hli]
    · have hlk : l = k := by omega
      rwa [hlk]
  have hrowj (l : Fin 3) (hl : l ≠ i) : D j l = 0 := by
    by_cases hlj : l = j
    · rwa [hlj]
    · have hlk : l = k := by omega
      rwa [hlk]
  obtain ⟨l, hl⟩ := exists_positive_entry hD hv hL hpos j
  have hli : l = i := by
    by_contra hn
    exact hl.ne' (hrowj l hn)
  rw [hli] at hl
  exact ⟨i, j, k, hij, hik, hjk, hkpos, hijpos, hl, hrowi, hrowj⟩

end Erdos633b.NonnegativeMatrix
