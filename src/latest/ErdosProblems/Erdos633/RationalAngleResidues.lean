import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

/-!
# The elementary residue obstruction for rational-angle tilings

A reduced residue in the middle third is constructed explicitly, except at
denominators 4, 6, and 10. This is the arithmetic input to the conjugate-angle
argument: multiplicity at least three forces one of four reduced angles.
The geometric connection to arbitrary tilings is supplied separately by
`RationalTilingData`, `RationalResidueLifting`, and `RationalCornerConstraints`.
-/

namespace Erdos633

theorem exists_coprime_middle_third (n : ℕ) (hn : 3 ≤ n)
    (h4 : n ≠ 4) (h6 : n ≠ 6) (h10 : n ≠ 10) :
    ∃ r : ℕ, 0 < r ∧ r < n ∧ r.Coprime n ∧ n ≤ 3 * r ∧ 3 * r ≤ 2 * n := by
  by_cases heven : n % 2 = 0
  · by_cases hfour : n % 4 = 0
    · let r := 2 * (n / 4) - 1
      have hnrep : n = 2 * r + 2 := by dsimp [r]; omega
      have hodd : Odd r := Nat.odd_iff.mpr (by dsimp [r]; omega)
      have hc : r.Coprime n := by
        rw [hnrep]
        exact (Nat.coprime_mul_right_add_right r 2 2).mpr
          (Nat.coprime_two_right.mpr hodd)
      exact ⟨r, by dsimp [r]; omega, by omega, hc, by omega, by omega⟩
    · have hrem : n % 4 = 2 := by omega
      let r := 2 * (n / 4) - 1
      have hnrep : n = 2 * r + 4 := by dsimp [r]; omega
      have hodd : Odd r := Nat.odd_iff.mpr (by dsimp [r]; omega)
      have hc2 : r.Coprime 2 := Nat.coprime_two_right.mpr hodd
      have hc4 : r.Coprime 4 := by simpa using hc2.mul_right hc2
      have hc : r.Coprime n := by
        rw [hnrep]
        exact (Nat.coprime_mul_right_add_right r 4 2).mpr hc4
      exact ⟨r, by dsimp [r]; omega, by omega, hc, by dsimp [r]; omega, by omega⟩
  · let r := n / 2
    have hnrep : n = 2 * r + 1 := by dsimp [r]; omega
    have hc : r.Coprime n := by
      rw [hnrep]
      exact (Nat.coprime_mul_right_add_right r 1 2).mpr (by simp)
    exact ⟨r, by omega, by omega, hc, by omega, by omega⟩

/-- If every reduced residue lies strictly outside the middle third, only
the denominators 4, 6, and 10 remain. -/
theorem small_unit_residue_denominator (n : ℕ) (hn : 2 ≤ n)
    (h : ∀ r : ℕ, 0 < r → r < n → r.Coprime n →
      3 * r < n ∨ 3 * (n - r) < n) : n = 4 ∨ n = 6 ∨ n = 10 := by
  by_contra hbad
  push Not at hbad
  obtain ⟨h4, h6, h10⟩ := hbad
  by_cases h2 : n = 2
  · subst n
    have hbad := h 1 (by decide) (by decide) (by decide)
    omega
  · obtain ⟨r, hr, hrn, hc, hlo, hhi⟩ :=
      exists_coprime_middle_third n (by omega) h4 h6 h10
    rcases h r hr hrn hc with hlow | hhigh <;> omega

/-- Requiring every reduced residue to lie outside the middle half leaves
only denominator six. -/
theorem quarter_unit_residue_denominator (n : ℕ) (hn : 2 ≤ n)
    (h : ∀ r : ℕ, 0 < r → r < n → r.Coprime n →
      4 * r < n ∨ 4 * (n - r) < n) : n = 6 := by
  have hthird : ∀ r : ℕ, 0 < r → r < n → r.Coprime n →
      3 * r < n ∨ 3 * (n - r) < n := by
    intro r hr hrn hc
    rcases h r hr hrn hc with hlow | hhigh
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  rcases small_unit_residue_denominator n hn hthird with rfl | h6 | rfl
  · have hbad := h 1 (by decide) (by decide) (by decide)
    omega
  · exact h6
  · have hbad := h 3 (by decide) (by decide) (by decide)
    omega

/-- The only denominators at least three whose units are all signs are
three, four, and six. -/
theorem unit_residues_only_sign_denominator (n : ℕ) (hn : 3 ≤ n)
    (h : ∀ r : ℕ, 0 < r → r < n → r.Coprime n → r = 1 ∨ r + 1 = n) :
    n = 3 ∨ n = 4 ∨ n = 6 := by
  by_contra hbad
  push Not at hbad
  obtain ⟨h3, h4, h6⟩ := hbad
  have h10 : n ≠ 10 := by
    intro hn10
    subst n
    have hbad := h 3 (by decide) (by decide) (by decide)
    omega
  obtain ⟨r, hr, hrn, hc, hlo, hhi⟩ := exists_coprime_middle_third n hn h4 h6 h10
  rcases h r hr hrn hc with hlow | hhigh <;> omega

/-- The four reduced fractions that can occur for an angle with outer
multiplicity at least three, once all conjugate corner inequalities hold. -/
theorem multiplicity_three_reduced_angle (m n p : ℕ)
    (hm : 0 < m) (hmn : m < n) (hc : m.Coprime n) (hp : 3 ≤ p)
    (hangle : p * m < n)
    (hconj : ∀ r : ℕ, 0 < r → r < n → r.Coprime n →
      p * r < n ∨ p * (n - r) < n) :
    (n = 4 ∧ m = 1) ∨ (n = 6 ∧ m = 1) ∨
      (n = 10 ∧ m = 1) ∨ (n = 10 ∧ m = 3) := by
  have hthird : ∀ r : ℕ, 0 < r → r < n → r.Coprime n →
      3 * r < n ∨ 3 * (n - r) < n := by
    intro r hr hrn hrc
    rcases hconj r hr hrn hrc with hlow | hhigh
    · exact Or.inl (by nlinarith)
    · exact Or.inr (by nlinarith)
  have hsmall : 3 * m < n := by nlinarith
  rcases small_unit_residue_denominator n (by omega) hthird with rfl | rfl | rfl
  · exact Or.inl ⟨rfl, by omega⟩
  · exact Or.inr (Or.inl ⟨rfl, by omega⟩)
  · have hmcase : m = 1 ∨ m = 2 ∨ m = 3 := by omega
    rcases hmcase with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · norm_num at hc
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))

theorem rational_angle_outer_multiplicity_le_five (m n p : ℕ)
    (hm : 0 < m) (hmn : m < n) (hp : 3 ≤ p) (hangle : p * m < n)
    (hconj : ∀ r : ℕ, 0 < r → r < n → r.Coprime n →
      p * r < n ∨ p * (n - r) < n) : p ≤ 5 := by
  by_cases hp3 : p = 3
  · omega
  have hp4 : 4 ≤ p := by omega
  have hquarter : ∀ r : ℕ, 0 < r → r < n → r.Coprime n →
      4 * r < n ∨ 4 * (n - r) < n := by
    intro r hr hrn hc
    rcases hconj r hr hrn hc with hlow | hhigh
    · exact Or.inl (by nlinarith)
    · exact Or.inr (by nlinarith)
  have hn6 := quarter_unit_residue_denominator n (by omega) hquarter
  subst n
  nlinarith

end Erdos633
