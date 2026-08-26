import ErdosProblems.Erdos633.Arithmetic
import Mathlib.NumberTheory.PythagoreanTriples

/-!
# Descent for two Pythagorean triples with one doubled leg

This development follows the elementary descent in Theorem 2.1 of
Gordon and Graham, *Comments on proofs that there are no four squares in
arithmetic progression*, Fibonacci Quarterly 53 (2015), 68–73.
Both parity cases and the coprime factor extraction are checked explicitly.
-/

namespace Erdos633

theorem three_dvd_sum_sq_iff (a b : ℕ) : 3 ∣ a ^ 2 + b ^ 2 ↔ 3 ∣ a ∧ 3 ∣ b := by
  constructor
  · intro h
    have hz : (a : ZMod 3) ^ 2 + (b : ZMod 3) ^ 2 = 0 := by
      have h' := (ZMod.natCast_eq_zero_iff (a ^ 2 + b ^ 2) 3).mpr h
      simpa only [Nat.cast_add, Nat.cast_pow] using h'
    have hmod : ∀ x y : ZMod 3, x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0 := by decide
    obtain ⟨ha, hb⟩ := hmod _ _ hz
    exact ⟨(ZMod.natCast_eq_zero_iff a 3).mp ha,
      (ZMod.natCast_eq_zero_iff b 3).mp hb⟩
  · rintro ⟨ha, hb⟩
    exact dvd_add (dvd_pow ha (by decide)) (dvd_pow hb (by decide))

theorem coprime_sq_add_four_sq (a b : ℕ) (hab : a.Coprime b) :
    (a ^ 2 + b ^ 2).Coprime (a ^ 2 + 4 * b ^ 2) := by
  by_contra h
  obtain ⟨p, hp, hpA, hpB⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hp3b : p ∣ 3 * b ^ 2 := by
    have heq : a ^ 2 + 4 * b ^ 2 = (a ^ 2 + b ^ 2) + 3 * b ^ 2 := by ring
    rw [heq] at hpB
    exact (Nat.dvd_add_iff_right hpA).mpr hpB
  rcases hp.dvd_mul.mp hp3b with hp3 | hpb
  · have hp_eq : p = 3 := (Nat.dvd_prime Nat.prime_three).mp hp3 |>.resolve_left hp.ne_one
    subst p
    obtain ⟨ha, hb⟩ := (three_dvd_sum_sq_iff a b).mp hpA
    exact Nat.not_coprime_of_dvd_of_dvd (by decide) ha hb hab
  · have hpb' : p ∣ b := hp.dvd_of_dvd_pow hpb
    have hpa2 : p ∣ a ^ 2 := (Nat.dvd_add_iff_left hpb).mpr hpA
    have hpa : p ∣ a := hp.dvd_of_dvd_pow hpa2
    exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpa hpb' hab

theorem nat_sq_mod_four (n : ℕ) : n ^ 2 % 4 = (n % 2) ^ 2 := by
  have hn : n % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [← Nat.mod_mod_of_dvd n (by decide : 2 ∣ 4), Nat.pow_mod]
  interval_cases h : n % 4 <;> norm_num

/-- Positive natural parameters for a primitive triple with odd first leg. -/
theorem pythagorean_parameters_nat (a b c : ℕ) (hb : 0 < b) (hc : 0 < c)
    (hab : a.Coprime b) (haodd : a % 2 = 1) (heq : a ^ 2 + b ^ 2 = c ^ 2) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ a + n ^ 2 = m ^ 2 ∧ b = 2 * m * n ∧
      c = m ^ 2 + n ^ 2 ∧ m.Coprime n ∧
      (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) := by
  have hT : PythagoreanTriple (a : ℤ) b c := by
    dsimp [PythagoreanTriple]
    exact_mod_cast (show a * a + b * b = c * c by nlinarith [heq])
  have hgcd : Int.gcd (a : ℤ) b = 1 := by exact_mod_cast hab
  have hodd : (a : ℤ) % 2 = 1 := by exact_mod_cast haodd
  have hcZ : (0 : ℤ) < c := by exact_mod_cast hc
  obtain ⟨m, n, hm, hn, hc', hcop, hpar, hm0⟩ := hT.coprime_classification' hgcd hodd hcZ
  have hbZ : (0 : ℤ) < b := by exact_mod_cast hb
  have hmpos : 0 < m := by
    by_contra hle
    have hz : m = 0 := by omega
    simp only [hz, mul_zero, zero_mul] at hn
    omega
  have hnpos : 0 < n := by
    have hprod : 0 < (2 * m) * n := by rw [← hn]; exact hbZ
    exact pos_of_mul_pos_right hprod (by linarith)
  lift m to ℕ using hmpos.le
  lift n to ℕ using hnpos.le
  refine ⟨m, n, by exact_mod_cast hmpos, by exact_mod_cast hnpos, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast (show (a : ℤ) + (n : ℤ) ^ 2 = (m : ℤ) ^ 2 by linarith [hm])
  · exact_mod_cast hn
  · exact_mod_cast hc'
  · exact_mod_cast hcop
  · exact_mod_cast hpar

/-- Choose the odd and even parameters consistently in the two triples. -/
theorem doubled_leg_parameters (a b c d : ℕ) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hab : a.Coprime b) (haodd : a % 2 = 1)
    (h₁ : a ^ 2 + b ^ 2 = c ^ 2) (h₂ : a ^ 2 + (2 * b) ^ 2 = d ^ 2) :
    ∃ u v x y : ℕ, 0 < u ∧ 0 < v ∧ 0 < x ∧ 0 < y ∧
      u.Coprime v ∧ x.Coprime y ∧ u % 2 = 1 ∧ x % 2 = 1 ∧ y % 2 = 0 ∧
      b = 2 * u * v ∧ b = x * y ∧ u ^ 2 + y ^ 2 = x ^ 2 + v ^ 2 := by
  have ha2 : a.Coprime 2 := Nat.coprime_two_right.mpr (Nat.odd_iff.mpr haodd)
  obtain ⟨m, n, hm, hn, han, hbn, _, hmn, hpar₁⟩ :=
    pythagorean_parameters_nat a b c hb hc hab haodd h₁
  obtain ⟨p, q, hp, hq, hap, hbp, _, hpq, hpar₂⟩ :=
    pythagorean_parameters_nat a (2 * b) d (by omega) hd (ha2.mul_right hab) haodd h₂
  have hbxy : b = p * q := by nlinarith only [hbp]
  have hmod₁ := congrArg (fun k : ℕ => k % 4) han
  have hmod₂ := congrArg (fun k : ℕ => k % 4) hap
  rw [Nat.add_mod, nat_sq_mod_four, nat_sq_mod_four] at hmod₁ hmod₂
  rcases hpar₁ with ⟨hm2, hn2⟩ | ⟨hm2, hn2⟩ <;>
    rcases hpar₂ with ⟨hp2, hq2⟩ | ⟨hp2, hq2⟩
  · refine ⟨n, m, q, p, hn, hm, hq, hp, hmn.symm, hpq.symm, hn2, hq2, hp2,
      ?_, ?_, ?_⟩
    · simpa only [mul_comm, mul_assoc, mul_left_comm] using hbn
    · simpa only [mul_comm] using hbxy
    · linarith only [han, hap]
  · simp only [hm2, hn2, hp2, hq2] at hmod₁ hmod₂
    omega
  · simp only [hm2, hn2, hp2, hq2] at hmod₁ hmod₂
    omega
  · refine ⟨m, n, p, q, hm, hn, hp, hq, hmn, hpq, hm2, hp2, hq2,
      hbn, hbxy, ?_⟩
    linarith only [han, hap]

end Erdos633
