import ErdosProblems.Erdos248.Arithmetic
import Mathlib.Data.Nat.Log

/-!
# Prime powers in the divisor-tail criterion

The unconditional development for Problem 248 bounds distinct prime factors.
To use that development for Problem 258, one must also control repeated prime
factors.  These elementary lemmas reduce that extra requirement to prime-power
divisibility events below a fixed power of the interval endpoint.
-/

open scoped BigOperators ArithmeticFunction.omega ArithmeticFunction.Omega

namespace Erdos258b

/-- For positive `m`, the number of prime powers `p^j` dividing `m` with
`j ≥ 2` and `p^j ≤ R`.
The exponent formula avoids an unnecessarily large ambient set of integers. -/
def primePowerExcess (m R : ℕ) : ℕ :=
  ∑ p ∈ m.primeFactors, min (m.factorization p - 1) (Nat.log p R - 1)

theorem two_pow_cardFactors_le {m : ℕ} (hm : m ≠ 0) :
    2 ^ Ω m ≤ m := by
  rw [ArithmeticFunction.cardFactors_eq_sum_factorization, Finsupp.sum,
    ← Finset.prod_pow_eq_pow_sum]
  calc
    (∏ p ∈ m.factorization.support, 2 ^ m.factorization p) ≤
        ∏ p ∈ m.factorization.support, p ^ m.factorization p := by
      apply Finset.prod_le_prod'
      intro p hp
      exact Nat.pow_le_pow_left
        (Nat.prime_of_mem_primeFactors (by simpa using hp)).two_le _
    _ = m := by simpa using (Nat.prod_primeFactors_pow_factorization hm).symm

theorem cardFactors_add_le_two_mul_of_le_pow {n L k : ℕ}
    (hn : n ≤ 2 ^ L) (hLk : L ≤ k) (hk : 1 ≤ k) :
    Ω (n + k) ≤ 2 * k := by
  rw [← Nat.pow_le_pow_iff_right (by decide : 1 < 2)]
  calc
    2 ^ Ω (n + k) ≤ n + k := two_pow_cardFactors_le (by omega)
    _ ≤ 2 ^ k + 2 ^ k := Nat.add_le_add
      (hn.trans (Nat.pow_le_pow_right (by decide) hLk)) k.lt_two_pow_self.le
    _ = 2 ^ (k + 1) := by rw [pow_succ]; omega
    _ ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by decide) (by omega)

/-- The whole exponent of a prime is controlled by its truncated exponent,
provided `m` lies below a fixed power of the truncation radius. -/
theorem factorization_le_truncated {m R t p : ℕ}
    (hp : p.Prime) (ht : 1 ≤ t) (hm : m ≤ R ^ t) :
    m.factorization p ≤
      2 * t * (1 + min (m.factorization p - 1) (Nat.log p R - 1)) := by
  by_cases hpR : p ≤ R
  · have hlog : 1 ≤ Nat.log p R := Nat.log_pos hp.one_lt hpR
    have hR : R ≤ p ^ (Nat.log p R + 1) :=
      (Nat.lt_pow_succ_log_self hp.one_lt R).le
    have hexp : m.factorization p ≤ (Nat.log p R + 1) * t := by
      apply Nat.factorization_le_of_le_pow
      rw [pow_mul]
      exact hm.trans (Nat.pow_le_pow_left hR t)
    by_cases he : m.factorization p ≤ Nat.log p R
    · rw [min_eq_left (Nat.sub_le_sub_right he 1)]
      have hbase : m.factorization p ≤ 1 + (m.factorization p - 1) := by omega
      exact hbase.trans (Nat.le_mul_of_pos_left _ (by omega))
    · rw [min_eq_right (by omega)]
      have htwo : Nat.log p R + 1 ≤ 2 * Nat.log p R := by omega
      calc
        m.factorization p ≤ (Nat.log p R + 1) * t := hexp
        _ ≤ (2 * Nat.log p R) * t := Nat.mul_le_mul_right t htwo
        _ = 2 * t * (1 + (Nat.log p R - 1)) := by
          have hsucc : 1 + (Nat.log p R - 1) = Nat.log p R := by omega
          rw [hsucc]
          ring
  · have he : m.factorization p ≤ t := Nat.factorization_le_of_le_pow
      (hm.trans (Nat.pow_le_pow_left (by omega : R ≤ p) t))
    have hbase : 1 ≤ 1 + min (m.factorization p - 1) (Nat.log p R - 1) := by omega
    exact he.trans ((by omega : t ≤ 2 * t).trans
      (Nat.le_mul_of_pos_right _ hbase))

/-- Thus the only additional input needed beyond a bound for `ω` is a bound
for the truncated higher-prime-power count. -/
theorem cardFactors_le_omega_add_primePowerExcess {m R t : ℕ}
    (ht : 1 ≤ t) (hm : m ≤ R ^ t) :
    Ω m ≤ 2 * t * (ω m + primePowerExcess m R) := by
  rw [ArithmeticFunction.cardFactors_eq_sum_factorization, Finsupp.sum]
  have hsupport : m.factorization.support = m.primeFactors := by simp
  rw [hsupport]
  calc
    (∑ p ∈ m.primeFactors, m.factorization p) ≤
        ∑ p ∈ m.primeFactors,
          2 * t * (1 + min (m.factorization p - 1) (Nat.log p R - 1)) := by
      exact Finset.sum_le_sum fun p hp =>
        factorization_le_truncated (Nat.prime_of_mem_primeFactors hp) ht hm
    _ = 2 * t * (ω m + primePowerExcess m R) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      simp [primePowerExcess, Erdos248.omega_eq_primeFactors_card]

/-- Only the sixth and subsequent copies of each prime need probabilistic
control: the first five copies are charged to the distinct-prime count. -/
def highPrimePowerExcess (m R : ℕ) : ℕ :=
  ∑ p ∈ m.primeFactors, min (m.factorization p - 5) (Nat.log p R - 5)

theorem primePowerExcess_le_high (m R : ℕ) :
    primePowerExcess m R ≤ 4 * ω m + highPrimePowerExcess m R := by
  calc
    primePowerExcess m R ≤ ∑ p ∈ m.primeFactors,
        (4 + min (m.factorization p - 5) (Nat.log p R - 5)) := by
      apply Finset.sum_le_sum
      intro p hp
      omega
    _ = 4 * ω m + highPrimePowerExcess m R := by
      simp [Finset.sum_add_distrib, highPrimePowerExcess,
        Erdos248.omega_eq_primeFactors_card, mul_comm]

theorem cardFactors_le_omega_add_highPrimePowerExcess {m R t : ℕ}
    (ht : 1 ≤ t) (hm : m ≤ R ^ t) :
    Ω m ≤ 10 * t * (ω m + highPrimePowerExcess m R) := by
  have h := cardFactors_le_omega_add_primePowerExcess ht hm
  have hhigh := primePowerExcess_le_high m R
  calc
    Ω m ≤ 2 * t * (ω m + primePowerExcess m R) := h
    _ ≤ 2 * t * (ω m + (4 * ω m + highPrimePowerExcess m R)) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_left hhigh _)
    _ ≤ 10 * t * (ω m + highPrimePowerExcess m R) := by nlinarith

theorem highPrimePowerExcess_eq_sum {m R : ℕ} (hm : m ≠ 0) :
    highPrimePowerExcess m R = ∑ p ∈ m.primeFactors,
      ∑ j ∈ Finset.Icc 6 (Nat.log p R), if p ^ j ∣ m then 1 else 0 := by
  unfold highPrimePowerExcess
  apply Finset.sum_congr rfl
  intro p hp
  have hpprime := Nat.prime_of_mem_primeFactors hp
  have hset : (Finset.Icc 6 (Nat.log p R)).filter (fun j => p ^ j ∣ m) =
      Finset.Icc 6 (min (m.factorization p) (Nat.log p R)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, hpprime.pow_dvd_iff_le_factorization hm,
      le_min_iff]
    omega
  have hc := congrArg Finset.card hset
  rw [Nat.card_Icc] at hc
  simp only [Finset.sum_boole, Nat.cast_id]
  omega

/-- A fixed rectangular index set, useful when interchanging the divisor
count with the weighted sum over `m`. -/
def highPrimePowerCount (m R : ℕ) : ℕ :=
  ∑ p ∈ Finset.Icc 2 R, ∑ j ∈ Finset.Icc 6 R,
    if p.Prime ∧ p ^ j ≤ R ∧ p ^ j ∣ m then 1 else 0

theorem highPrimePowerExcess_le_count {m R : ℕ} (hm : m ≠ 0) :
    highPrimePowerExcess m R ≤ highPrimePowerCount m R := by
  by_cases hR : R = 0
  · subst R
    simp [highPrimePowerExcess, highPrimePowerCount]
  rw [highPrimePowerExcess_eq_sum hm]
  let f : ℕ → ℕ := fun p => ∑ j ∈ Finset.Icc 6 R,
    if p.Prime ∧ p ^ j ≤ R ∧ p ^ j ∣ m then 1 else 0
  calc
    (∑ p ∈ m.primeFactors, ∑ j ∈ Finset.Icc 6 (Nat.log p R),
        if p ^ j ∣ m then 1 else 0) ≤ ∑ p ∈ m.primeFactors, f p := by
      apply Finset.sum_le_sum
      intro p hp
      have hpprime := Nat.prime_of_mem_primeFactors hp
      calc
        (∑ j ∈ Finset.Icc 6 (Nat.log p R), if p ^ j ∣ m then 1 else 0) =
            ∑ j ∈ Finset.Icc 6 (Nat.log p R),
              if p.Prime ∧ p ^ j ≤ R ∧ p ^ j ∣ m then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          have hpow := Nat.pow_le_of_le_log hR (Finset.mem_Icc.mp hj).2
          simp [hpprime, hpow]
        _ ≤ f p := by
          apply Finset.sum_le_sum_of_subset
          exact Finset.Icc_subset_Icc le_rfl (Nat.log_le_self p R)
    _ ≤ ∑ p ∈ Finset.Icc 2 R, f p := by
      apply Finset.sum_le_sum_of_ne_zero
      intro p hp hf
      refine Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).two_le, ?_⟩
      by_contra hnot
      apply hf
      apply Finset.sum_eq_zero
      intro j hj
      have hjpos : 0 < j := by have := (Finset.mem_Icc.mp hj).1; omega
      have hpow : ¬ p ^ j ≤ R := by
        intro hle
        exact hnot ((Nat.le_pow hjpos).trans hle)
      simp [hpow]
    _ = highPrimePowerCount m R := rfl

end Erdos258b
