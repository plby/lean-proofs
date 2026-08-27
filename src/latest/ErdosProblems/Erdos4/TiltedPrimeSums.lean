import ErdosProblems.Erdos4.TiltedTargets
import ErdosProblems.Erdos4.SieveMajorant

/-!
# Elementary prime sums for the tilt

The bound for `sum log p / p` follows by counting prime divisors of each
integer. The product of its distinct prime divisors divides that integer,
so no prime-number theorem or asymptotic summation formula is needed.
-/

open scoped BigOperators

namespace Erdos4.Tilted

theorem prime_divisor_log_sum_le (S : Finset ℕ) {n : ℕ} (hn : 0 < n)
    (hprime : ∀ p ∈ S, p.Prime) (hdiv : ∀ p ∈ S, p ∣ n) :
    (∑ p ∈ S, Real.log (p : ℝ)) ≤ Real.log n := by
  have hsub : S ⊆ n.primeFactors := fun p hp =>
    Nat.mem_primeFactors.mpr ⟨hprime p hp, hdiv p hp, hn.ne'⟩
  have hprod : (∏ p ∈ S, p) ∣ n :=
    (Finset.prod_dvd_prod_of_subset S n.primeFactors id hsub).trans (Nat.prod_primeFactors_dvd n)
  have hpos : ∀ p ∈ S, (0 : ℝ) < p := fun p hp => by exact_mod_cast (hprime p hp).pos
  rw [← Real.log_prod (fun p hp => (hpos p hp).ne'), ← Nat.cast_prod]
  exact Real.log_le_log
    (by exact_mod_cast Finset.prod_pos (fun p hp => (hprime p hp).pos))
    (by exact_mod_cast Nat.le_of_dvd hn hprod)

theorem prime_floor_log_sum_le (N : ℕ) :
    (∑ p ∈ N.primesLE, Real.log (p : ℝ) * ((N / p : ℕ) : ℝ)) ≤ (N : ℝ) * Real.log N := by
  classical
  calc
    _ = ∑ p ∈ N.primesLE, ∑ n ∈ Finset.Icc 1 N, if p ∣ n then Real.log (p : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [← SieveMajorant.sum_dvd_indicator p N (Nat.prime_of_mem_primesLE hp).pos, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      split_ifs <;> simp
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ p ∈ N.primesLE, if p ∣ n then Real.log (p : ℝ) else 0 :=
      Finset.sum_comm
    _ ≤ ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [← Finset.sum_filter]
      exact prime_divisor_log_sum_le _ (Finset.mem_Icc.mp hn).1
        (fun p hp => Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1)
        (fun p hp => (Finset.mem_filter.mp hp).2)
    _ ≤ ∑ _n ∈ Finset.Icc 1 N, Real.log (N : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact Real.log_le_log (by exact_mod_cast (Finset.mem_Icc.mp hn).1)
        (by exact_mod_cast (Finset.mem_Icc.mp hn).2)
    _ = _ := by simp

theorem half_quotient_le_cast_div {N p : ℕ} (hp : 0 < p) (hpN : p ≤ N) :
    (N : ℝ) / (2 * (p : ℝ)) ≤ ((N / p : ℕ) : ℝ) := by
  have hq : 1 ≤ N / p := (Nat.le_div_iff_mul_le hp).mpr (by simpa using hpN)
  have hqR : (1 : ℝ) ≤ (N / p : ℕ) := by exact_mod_cast hq
  have hh := (abs_le.mp (SieveMajorant.abs_cast_div_sub_real_div_le_one N p hp)).1
  calc
    _ = ((N : ℝ) / p) / 2 := by ring
    _ ≤ _ := by linarith

theorem sum_prime_log_div_le (N : ℕ) (hN : 1 ≤ N) :
    (∑ p ∈ N.primesLE, Real.log (p : ℝ) / p) ≤ 2 * Real.log N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : ((N : ℝ) / 2) * (∑ p ∈ N.primesLE, Real.log (p : ℝ) / p) ≤
      (N : ℝ) * Real.log N := by
    calc
      _ = ∑ p ∈ N.primesLE, Real.log (p : ℝ) * ((N : ℝ) / (2 * (p : ℝ))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun p _ => by ring)
      _ ≤ ∑ p ∈ N.primesLE, Real.log (p : ℝ) * ((N / p : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact mul_le_mul_of_nonneg_left
          (half_quotient_le_cast_div (Nat.prime_of_mem_primesLE hp).pos (Nat.le_of_mem_primesLE hp))
          (Real.log_natCast_nonneg p)
      _ ≤ _ := prime_floor_log_sum_le N
  apply (mul_le_mul_iff_right₀ hNpos).mp
  calc
    _ = 2 * (((N : ℝ) / 2) * (∑ p ∈ N.primesLE, Real.log (p : ℝ) / p)) := by ring
    _ ≤ 2 * ((N : ℝ) * Real.log N) := mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = _ := by ring

end Erdos4.Tilted
