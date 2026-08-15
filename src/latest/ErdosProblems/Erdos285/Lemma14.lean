import ErdosProblems.Erdos285.ExactCorrection

/-!
# Martin's two-inverse lemma

This file gives the source-faithful form of Lemma 14 in Greg Martin's
*Denser Egyptian fractions*.  If the odd prime power `q = p ^ ν` is at
least five, then every residue modulo its underlying prime is a sum of the
inverses of two distinct integers in `[(q - 3) / 2, q)`.

The prime-three case is the separate explicit construction from the paper.
For primes at least five we reuse the finite pigeonhole proof in
`Erdos285.ExactCorrection`.
-/

namespace Erdos285.MartinCorrection

private theorem martin_lemma14_three {q ν : ℕ} (hν : 0 < ν)
    (hqpow : q = 3 ^ ν) (hq5 : 5 ≤ q) (a : ZMod 3) :
    ∃ m₁ m₂ : ℕ,
      (q - 3) / 2 ≤ m₁ ∧
      m₁ < m₂ ∧ m₂ < q ∧
      ¬ 3 ∣ m₁ * m₂ ∧
      ((m₁ : ZMod 3)⁻¹ + (m₂ : ZMod 3)⁻¹) = a := by
  have hν2 : 2 ≤ ν := by
    by_contra h
    have hν1 : ν = 1 := by omega
    subst ν
    norm_num [hqpow] at hq5
  have hq9 : 9 ≤ q := by
    rw [hqpow]
    exact Nat.pow_le_pow_right (n := 3) (by omega) hν2
  have hqdiv : 3 ∣ q := by
    rw [hqpow]
    exact dvd_pow_self 3 (Nat.ne_zero_of_lt hν)
  have hqcast : (q : ZMod 3) = 0 :=
    (ZMod.natCast_eq_zero_iff q 3).2 hqdiv
  have hthree : (3 : ZMod 3) = 0 := ZMod.natCast_self 3
  have hinv_two : ((2 : ZMod 3)⁻¹) = 2 := by
    apply ZMod.inv_eq_of_mul_eq_one
    linear_combination hthree
  have hneg_one : (-((1 : ℕ) : ZMod 3)) = 2 := by
    linear_combination -hthree
  have hneg_two : (-((2 : ℕ) : ZMod 3)) = 1 := by
    linear_combination -hthree
  have hneg_four : (-((4 : ℕ) : ZMod 3)) = 2 := by
    linear_combination -2 * hthree
  have hneg_five : (-((5 : ℕ) : ZMod 3)) = 1 := by
    linear_combination -2 * hthree
  fin_cases a
  · refine ⟨q - 2, q - 1, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · intro hdvd
      have hz : (((q - 2) * (q - 1) : ℕ) : ZMod 3) = 0 :=
        (ZMod.natCast_eq_zero_iff ((q - 2) * (q - 1)) 3).2 hdvd
      push_cast at hz
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), hqcast] at hz
      have hdiv : 3 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 3).1 hz
      norm_num at hdiv
    · rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), hqcast]
      change (-((2 : ℕ) : ZMod 3))⁻¹ + (-((1 : ℕ) : ZMod 3))⁻¹ = 0
      simp only [hneg_two, hneg_one, ZMod.inv_one, hinv_two]
      exact hthree
  · refine ⟨q - 4, q - 1, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · intro hdvd
      have hz : (((q - 4) * (q - 1) : ℕ) : ZMod 3) = 0 :=
        (ZMod.natCast_eq_zero_iff ((q - 4) * (q - 1)) 3).2 hdvd
      push_cast at hz
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), hqcast] at hz
      have hdiv : 3 ∣ 4 := (ZMod.natCast_eq_zero_iff 4 3).1 hz
      norm_num at hdiv
    · rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), hqcast]
      change (-((4 : ℕ) : ZMod 3))⁻¹ + (-((1 : ℕ) : ZMod 3))⁻¹ = 1
      simp only [hneg_four, hneg_one, hinv_two]
      linear_combination hthree
  · refine ⟨q - 5, q - 2, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · intro hdvd
      have hz : (((q - 5) * (q - 2) : ℕ) : ZMod 3) = 0 :=
        (ZMod.natCast_eq_zero_iff ((q - 5) * (q - 2)) 3).2 hdvd
      push_cast at hz
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), hqcast] at hz
      have hdiv : 3 ∣ 10 := (ZMod.natCast_eq_zero_iff 10 3).1 hz
      norm_num at hdiv
    · rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), hqcast]
      change (-((5 : ℕ) : ZMod 3))⁻¹ + (-((2 : ℕ) : ZMod 3))⁻¹ = 2
      simp only [hneg_five, hneg_two, ZMod.inv_one]
      ring

/--
Martin's Lemma 14.  The congruence in the conclusion is modulo the underlying
prime `p`, rather than modulo the prime power `q`.
-/
theorem martin_lemma14 {p q ν : ℕ} (hp : p.Prime) (hν : 0 < ν)
    (hqpow : q = p ^ ν) (hqodd : Odd q) (hq5 : 5 ≤ q) (a : ZMod p) :
    ∃ m₁ m₂ : ℕ,
      (q - 3) / 2 ≤ m₁ ∧
      m₁ < m₂ ∧ m₂ < q ∧
      ¬ p ∣ m₁ * m₂ ∧
      ((m₁ : ZMod p)⁻¹ + (m₂ : ZMod p)⁻¹) = a := by
  by_cases hp3 : p = 3
  · subst p
    exact martin_lemma14_three hν hqpow hq5 a
  · have hp2 : p ≠ 2 := by
      intro hp2
      subst p
      have htwo_dvd : 2 ∣ q := by
        rw [hqpow]
        exact dvd_pow_self 2 (Nat.ne_zero_of_lt hν)
      exact (Nat.not_even_iff_odd.mpr hqodd) (even_iff_two_dvd.mpr htwo_dvd)
    have hp5 : 5 ≤ p := by
      have hp_one := hp.one_lt
      have hp_odd := hp.odd_of_ne_two hp2
      rcases hp_odd with ⟨k, hk⟩
      omega
    simpa [hqpow] using
      (Erdos285.ExactCorrection.martin_lemma14_of_five_le hp hp5 hν a)

#print axioms Erdos285.MartinCorrection.martin_lemma14

end Erdos285.MartinCorrection
