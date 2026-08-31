import ErdosProblems.Erdos1141.DivisibleIntervals
import ErdosProblems.Erdos1141.QuadraticReducedCharacter

/-!
# Inclusion-exclusion for an induced character

The unit restriction is expanded before estimating the resulting shorter
intervals. This argument is uniform in both the conductor and the modulus.
-/

namespace Pollack17.Burgess

open scoped BigOperators

theorem prod_divisibility_indicator (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (n : ℕ) :
    (∏ p ∈ s, (if p ∣ n then (1 : ℝ) else 0)) =
      if (∏ p ∈ s, p) ∣ n then 1 else 0 := by
  classical
  by_cases h : (∏ p ∈ s, p) ∣ n
  · rw [if_pos h]
    exact Finset.prod_eq_one fun p hp => if_pos ((prod_dvd_iff_all_prime_dvd s hs n).mp h p hp)
  · rw [if_neg h]
    have hn : ¬ ∀ p ∈ s, p ∣ n := by rwa [← prod_dvd_iff_all_prime_dvd s hs n]
    push Not at hn
    obtain ⟨p, hp, hpn⟩ := hn
    exact Finset.prod_eq_zero hp (if_neg hpn)

theorem coprime_indicator_eq_alternating {m : ℕ} (hm : m ≠ 0) (n : ℕ) :
    (if n.Coprime m then (1 : ℝ) else 0) =
      ∑ t ∈ m.primeFactors.powerset, (-1 : ℝ) ^ t.card *
        (if (∏ p ∈ t, p) ∣ n then 1 else 0) := by
  classical
  have hprod : (if n.Coprime m then (1 : ℝ) else 0) =
      ∏ p ∈ m.primeFactors, (1 - (if p ∣ n then (1 : ℝ) else 0)) := by
    by_cases hc : n.Coprime m
    · rw [if_pos hc]
      symm
      apply Finset.prod_eq_one
      intro p hp
      have hpc := hc.of_dvd_right (Nat.dvd_of_mem_primeFactors hp)
      have hpn := (Nat.prime_of_mem_primeFactors hp).coprime_iff_not_dvd.mp hpc.symm
      simp [hpn]
    · rw [if_neg hc]
      obtain ⟨p, hp, hpn, hpm⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
      symm
      exact Finset.prod_eq_zero (Nat.mem_primeFactors.mpr ⟨hp, hpm, hm⟩) (by simp [hpn])
  rw [hprod, Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.prod_const_one, mul_one, prod_divisibility_indicator t
    (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp ht hp))]

theorem changeLevel_natCast_eq_ite {d m : ℕ} (hd : d ∣ m)
    (φ : DirichletCharacter ℝ d) (n : ℕ) :
    DirichletCharacter.changeLevel hd φ (n : ZMod m) =
      if n.Coprime m then φ (n : ZMod d) else 0 := by
  by_cases hc : n.Coprime m
  · rw [if_pos hc]
    exact Pollack17.changeLevel_natCast hd φ n hc
  · rw [if_neg hc]
    exact MulChar.map_nonunit _ (by simpa only [ZMod.isUnit_iff_coprime] using hc)

theorem changeLevel_sum_eq_alternating {d m : ℕ} (hm : m ≠ 0) (hd : d ∣ m)
    (φ : DirichletCharacter ℝ d) (M H : ℕ) :
    (∑ i ∈ Finset.range H, DirichletCharacter.changeLevel hd φ (M + i : ℕ)) =
      ∑ t ∈ m.primeFactors.powerset, (-1 : ℝ) ^ t.card *
        ∑ i ∈ Finset.range H, if (∏ p ∈ t, p) ∣ M + i then φ (M + i : ℕ) else 0 := by
  classical
  have hpoint (n : ℕ) : DirichletCharacter.changeLevel hd φ (n : ℕ) =
      ∑ t ∈ m.primeFactors.powerset, (-1 : ℝ) ^ t.card *
        (if (∏ p ∈ t, p) ∣ n then φ (n : ℕ) else 0) := by
    rw [changeLevel_natCast_eq_ite]
    calc
      _ = φ (n : ℕ) * (if n.Coprime m then (1 : ℝ) else 0) := by split_ifs <;> simp
      _ = _ := by
        rw [coprime_indicator_eq_alternating hm, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        split_ifs <;> ring
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

theorem abs_changeLevel_sum_le {d m : ℕ} (hm : m ≠ 0) (hd : d ∣ m)
    (φ : DirichletCharacter ℝ d) (hφ : φ.IsQuadratic) (M H : ℕ) {B : ℝ}
    (hbound : ∀ K L : ℕ, L ≤ H → |∑ j ∈ Finset.range L, φ (K + j : ℕ)| ≤ B) :
    |∑ i ∈ Finset.range H, DirichletCharacter.changeLevel hd φ (M + i : ℕ)| ≤
      (2 : ℝ) ^ m.primeFactors.card * B := by
  classical
  rw [changeLevel_sum_eq_alternating hm hd φ M H]
  calc
    _ ≤ ∑ t ∈ m.primeFactors.powerset,
        |(-1 : ℝ) ^ t.card * ∑ i ∈ Finset.range H,
          if (∏ p ∈ t, p) ∣ M + i then φ (M + i : ℕ) else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ m.primeFactors.powerset, B := by
      apply Finset.sum_le_sum
      intro t ht
      rw [abs_mul, abs_neg_one_pow, one_mul]
      have htpos : 0 < ∏ p ∈ t, p := Finset.prod_pos fun p hp =>
        (Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp ht hp)).pos
      obtain ⟨K, L, hLH, heq⟩ := exists_divisible_sum_factorization
        (fun n => φ (n : ℕ)) (fun a b => by simp only [Nat.cast_mul, map_mul]) M H _ htpos
      rw [heq, abs_mul]
      have habs : |φ ((∏ p ∈ t, p) : ℕ)| ≤ 1 := by
        rcases hφ ((∏ p ∈ t, p) : ℕ) with h | h | h <;> rw [h] <;> norm_num
      exact (mul_le_mul habs (hbound K L hLH) (abs_nonneg _) (by norm_num)).trans_eq (one_mul B)
    _ = _ := by simp

end Pollack17.Burgess
