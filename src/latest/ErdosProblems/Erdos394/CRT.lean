import ErdosProblems.Erdos394.Structural

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Nat Finset

namespace Erdos394

/-- The two-term consecutive product in expanded form. -/
theorem consecutiveProduct_two (m : ℕ) :
    consecutiveProduct 2 m = m * (m + 1) := by
  simp [consecutiveProduct, Finset.prod_range_succ]

/--
A modulus divides `m(m+1)` exactly when it splits into coprime factors assigned
to the two consecutive integers.
-/
theorem dvd_consecutiveProduct_two_iff {n m : ℕ} :
    n ∣ consecutiveProduct 2 m ↔
      ∃ a d : ℕ, a.Coprime d ∧ n = a * d ∧ a ∣ m ∧ d ∣ m + 1 := by
  rw [consecutiveProduct_two]
  constructor
  · intro h
    obtain ⟨a, d, ha, hd, hn⟩ := exists_dvd_and_dvd_of_dvd_mul h
    refine ⟨a, d, ?_, hn, ha, hd⟩
    apply Nat.Coprime.of_dvd ha hd
    simpa using (Nat.coprime_self_add_right : (m.Coprime (m + 1) ↔ m.Coprime 1))
  · rintro ⟨a, d, _, rfl, ha, hd⟩
    exact mul_dvd_mul ha hd

/-- Every two-term solution determines a unitary (coprime-factor) split. -/
theorem t_two_has_coprime_split {n : ℕ} (hn : 0 < n) :
    ∃ a d : ℕ, a.Coprime d ∧ n = a * d ∧ a ∣ t 2 n ∧ d ∣ t 2 n + 1 := by
  exact (dvd_consecutiveProduct_two_iff.mp (t_dvd (by omega) hn))

/-- The split may equivalently be written as a positive Bézout relation. -/
theorem t_two_has_bezout_coordinates {n : ℕ} (hn : 0 < n) :
    ∃ a d r s : ℕ, a.Coprime d ∧ n = a * d ∧
      t 2 n = a * r ∧ t 2 n + 1 = d * s := by
  obtain ⟨a, d, had, hn', ha, hd⟩ := t_two_has_coprime_split hn
  obtain ⟨r, hr⟩ := ha
  obtain ⟨s, hs⟩ := hd
  exact ⟨a, d, r, s, had, hn', hr, hs⟩

/-- Conversely, every coprime split with the displayed Bézout relation gives
an upper bound for `t₂`. -/
theorem t_two_le_of_bezout {n a d r s : ℕ} (hn : n = a * d)
    (hm : a * r + 1 = d * s) (har : 0 < a * r) :
    t 2 n ≤ a * r := by
  apply t_min har
  apply dvd_consecutiveProduct_two_iff.mpr
  refine ⟨a, d, ?_, hn, dvd_mul_right a r, ?_⟩
  · apply Nat.Coprime.of_dvd (dvd_mul_right a r) (hm ▸ dvd_mul_right d s)
    simpa using
      (Nat.coprime_self_add_right : ((a * r).Coprime (a * r + 1) ↔ (a * r).Coprime 1))
  · exact hm ▸ dvd_mul_right d s

end Erdos394
