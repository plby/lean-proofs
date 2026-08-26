import ErdosProblems.Erdos633b.EulerParameters

/-! A terminating integer descent; no rank or torsion calculation is assumed. -/

namespace Erdos633b.EulerDescent

theorem descent_step (u v : ℤ) (h : Solution u v) :
    u = 1 ∧ v = 1 ∨
      ∃ p q : ℤ, Solution p q ∧ q < v ∧ (p = 1 → q = 1 → u = 1 ∧ v = 1) := by
  obtain ⟨m, n, hn, hmn, hm3, hnv, hu, hv⟩ := first_parameter u v h.toCoreSolution
  obtain ⟨p, q, hq, hpq, hp3, hqn, hid, hpqn, hback⟩ :=
    second_parameter u v m n h.toCoreSolution hn hmn hm3 hu hv
  have hQ := Q_pos p q hq
  have hpqpos : 0 < p * q := by
    have hh : 0 < v * (p * q) := by
      rw [← mul_assoc, hid]
      exact mul_pos (sq_pos_of_pos hn) hQ
    exact pos_of_mul_pos_right hh (le_of_lt h.v_pos)
  have hp : 0 < p := pos_of_mul_pos_left hpqpos (le_of_lt hq)
  have hnp : p * q ≤ n := Int.le_of_dvd hn hpqn
  have hnv' : n ≤ v := Int.le_of_dvd h.v_pos hnv
  have hqn' : q ≤ n := Int.le_of_dvd hn hqn
  have hqv : q ≤ v := hqn'.trans hnv'
  have hs : IsSquare (p * q * Q p q) := by
    have he : ((p : ℚ) * q * Q p q) * (n : ℚ) ^ 2 =
        (v : ℚ) * ((p : ℚ) * q) ^ 2 := by
      have hh : (v : ℚ) * p * q = (n : ℚ) ^ 2 * Q p q := by exact_mod_cast hid
      linear_combination -((p : ℚ) * q) * hh
    have hvS : IsSquare (v : ℚ) := Rat.isSquare_intCast_iff.mpr h.v_square
    have hh : IsSquare ((p : ℚ) * q * Q p q) :=
      (isSquare_mul_sq_iff _ (n : ℚ) (by exact_mod_cast ne_of_gt hn)).mp
        (he.symm ▸ hvS.mul (IsSquare.sq ((p : ℚ) * q)))
    apply Rat.isSquare_intCast_iff.mp
    simpa only [Int.cast_mul] using hh
  have hs' := triple_square_factors p q hp hq hpq hp3 hs
  by_cases heq : q = v
  · left
    have hne : n = v := by omega
    have hp1 : p = 1 := by nlinarith [hnp]
    have hq1 : q = 1 := by
      rw [hp1, hne, heq] at hid
      dsimp [Q] at hid
      have hc : 1 = 1 - 3 * v + 3 * v ^ 2 := by
        apply mul_left_cancel₀ (ne_of_gt (sq_pos_of_pos h.v_pos))
        linear_combination hid
      have hv1 : v = 1 := by nlinarith [h.v_pos]
      omega
    exact hback hp1 hq1
  · right
    exact ⟨p, q, ⟨⟨hp, hq, hpq, hp3, hs'.1, hs'.2.2⟩, hs'.2.1⟩,
      lt_of_le_of_ne hqv heq, hback⟩

/-- Euler's primitive square-pair lemma, proved by strong induction on the positive denominator. -/
theorem solution_eq_one (u v : ℤ) (h : Solution u v) : u = 1 ∧ v = 1 := by
  have aux : ∀ N : ℕ, ∀ u v : ℤ, v.toNat = N → Solution u v → u = 1 ∧ v = 1 := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro u v hv h
      rcases descent_step u v h with hdone | ⟨p, q, hpq, hqv, hback⟩
      · exact hdone
      · have hlt : q.toNat < N := by
          rw [← hv]
          exact (Int.toNat_lt_toNat h.v_pos).mpr hqv
        obtain ⟨hp, hq⟩ := ih q.toNat hlt p q rfl hpq
        exact hback hp hq
  exact aux v.toNat u v rfl h

end Erdos633b.EulerDescent
