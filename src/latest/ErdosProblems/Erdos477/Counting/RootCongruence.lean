/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Uniqueness of a sixth root in a nonsingular prime-power residue class.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.LocalRoots

namespace Erdos477.Counting

lemma prime_pow_dvd_sub_of_sixth_pow_congr (p : ℕ) [Fact p.Prime]
    (h6 : p.Coprime 6) (x y : ℤ) (hx : ¬ (p : ℤ) ∣ x)
    (hxy : (p : ℤ) ∣ x - y) (r : ℕ)
    (hpow : (p : ℤ) ^ r ∣ x ^ 6 - y ^ 6) : (p : ℤ) ^ r ∣ x - y := by
  have hp : p.Prime := Fact.out
  have hcast : (x : ZMod p) = (y : ZMod p) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub y x p).mpr hxy |>.symm
  have hx0 : (x : ZMod p) ≠ 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd x p).not.mpr hx
  have h60 : (6 : ZMod p) ≠ 0 := by
    intro h
    have hdiv := (ZMod.intCast_zmod_eq_zero_iff_dvd (6 : ℤ) p).mp (by simpa using h)
    have hnot : ¬ p ∣ 6 := hp.coprime_iff_not_dvd.mp h6
    exact hnot (by exact_mod_cast hdiv)
  have hQcast : ((sixthQuotient x y : ℤ) : ZMod p) = 6 * (x : ZMod p) ^ 5 := by
    simp only [sixthQuotient, Int.cast_add, Int.cast_mul, Int.cast_pow, ← hcast]
    ring
  have hQ : ¬ (p : ℤ) ∣ sixthQuotient x y := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hQcast]
    exact mul_ne_zero h60 (pow_ne_zero _ hx0)
  have hcop : IsCoprime (p : ℤ) (sixthQuotient x y) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast]
    exact hp.coprime_iff_not_dvd.mpr (Int.natCast_dvd.not.mp hQ)
  apply hcop.pow_left.dvd_of_dvd_mul_right
  rwa [sixthQuotient_identity]

lemma sextic_has_nondvd_coordinate (p : ℕ) (c : ℤ) (hc : ¬ (p : ℤ) ∣ c)
    (z : Fin 3 → ℤ) (hz : z 0 ^ 6 + z 1 ^ 6 - z 2 ^ 6 = c) :
    ∃ k, ¬ (p : ℤ) ∣ z k := by
  by_contra h
  push Not at h
  have hzq : (z 0 : ZMod p) ^ 6 + (z 1 : ZMod p) ^ 6 - (z 2 : ZMod p) ^ 6 = c := by
    simpa only [Int.cast_sub, Int.cast_add, Int.cast_pow] using
      congrArg (fun t : ℤ => (t : ZMod p)) hz
  have hzero (k) : (z k : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (h k)
  simp only [hzero, zero_pow (by decide : 6 ≠ 0), add_zero, sub_self] at hzq
  exact hc ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzq.symm)

/-- Within a fixed residue class modulo `p`, two free coordinates determine
the remaining coordinate modulo `p^r`, provided that coordinate is a unit. -/
lemma sextic_chart_congruence (p : ℕ) [Fact p.Prime] (h6 : p.Coprime 6)
    (r : ℕ) (c : ℤ) (z w : Fin 3 → ℤ)
    (hz : z 0 ^ 6 + z 1 ^ 6 - z 2 ^ 6 = c)
    (hw : w 0 ^ 6 + w 1 ^ 6 - w 2 ^ 6 = c)
    (k : Fin 3) (hk : ¬ (p : ℤ) ∣ z k)
    (hres : ∀ j, (z j : ZMod p) = (w j : ZMod p))
    (hfree : ∀ j, j ≠ k → (z j : ZMod (p ^ r)) = (w j : ZMod (p ^ r))) :
    ∀ j, (z j : ZMod (p ^ r)) = (w j : ZMod (p ^ r)) := by
  have hzq : (z 0 : ZMod (p ^ r)) ^ 6 + (z 1 : ZMod (p ^ r)) ^ 6 -
      (z 2 : ZMod (p ^ r)) ^ 6 = c := by
    simpa only [Int.cast_sub, Int.cast_add, Int.cast_pow] using
      congrArg (fun t : ℤ => (t : ZMod (p ^ r))) hz
  have hwq : (w 0 : ZMod (p ^ r)) ^ 6 + (w 1 : ZMod (p ^ r)) ^ 6 -
      (w 2 : ZMod (p ^ r)) ^ 6 = c := by
    simpa only [Int.cast_sub, Int.cast_add, Int.cast_pow] using
      congrArg (fun t : ℤ => (t : ZMod (p ^ r))) hw
  have heq : (z k : ZMod (p ^ r)) ^ 6 = (w k : ZMod (p ^ r)) ^ 6 := by
    fin_cases k
    · change (z 0 : ZMod (p ^ r)) ^ 6 = (w 0 : ZMod (p ^ r)) ^ 6
      rw [hfree 1 (by decide), hfree 2 (by decide)] at hzq
      linear_combination hzq - hwq
    · change (z 1 : ZMod (p ^ r)) ^ 6 = (w 1 : ZMod (p ^ r)) ^ 6
      rw [hfree 0 (by decide), hfree 2 (by decide)] at hzq
      linear_combination hzq - hwq
    · change (z 2 : ZMod (p ^ r)) ^ 6 = (w 2 : ZMod (p ^ r)) ^ 6
      rw [hfree 0 (by decide), hfree 1 (by decide)] at hzq
      linear_combination hwq - hzq
  have hpow : (p : ℤ) ^ r ∣ z k ^ 6 - w k ^ 6 := by
    have hzero : ((z k ^ 6 - w k ^ 6 : ℤ) : ZMod (p ^ r)) = 0 := by
      push_cast
      exact sub_eq_zero.mpr heq
    simpa only [Nat.cast_pow] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  have hxy : (p : ℤ) ∣ z k - w k :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (hres k).symm
  have hlast := prime_pow_dvd_sub_of_sixth_pow_congr p h6 (z k) (w k) hk hxy r hpow
  intro j
  by_cases hj : j = k
  · subst j
    apply ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr ?_).symm
    simpa only [Nat.cast_pow] using hlast
  · exact hfree j hj

#print axioms prime_pow_dvd_sub_of_sixth_pow_congr
-- 'Erdos477.Counting.prime_pow_dvd_sub_of_sixth_pow_congr' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
