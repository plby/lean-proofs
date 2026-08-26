import ErdosProblems.Erdos491.SmallPrimes

/-! # Large primes in a short affine progression -/

open scoped BigOperators

namespace Erdos491

lemma PosCompletelyAdditive.sub_primePart {u : ℕ → ℝ}
    (hu : PosCompletelyAdditive u) {n N Y : ℕ} (hn : 0 < n)
    (hnY : n ≤ Y) (hNY : N ≤ Y) :
    u n - primePart u (Nat.primesLE N) n =
      primePart u (Nat.primesLE Y \ Nat.primesLE N) n := by
  classical
  rw [hu.eq_primePart hn hnY]
  unfold primePart
  have h := Finset.sum_sdiff (f := fun p ↦ u p * (n.factorization p : ℝ))
    (Nat.primesLE_mono hNY)
  linarith

lemma factorization_zero_one {p n : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hlt : n < p ^ 2) : n.factorization p = if p ∣ n then 1 else 0 := by
  have hfac : n.factorization p < 2 := by
    by_contra h
    have hd : p ^ 2 ∣ n := (hp.pow_dvd_iff_le_factorization hn.ne').mpr (by omega)
    exact (not_le_of_gt hlt) (Nat.le_of_dvd hn hd)
  by_cases hd : p ∣ n
  · rw [if_pos hd]
    have := (hp.dvd_iff_one_le_factorization hn.ne').mp hd
    omega
  · rw [if_neg hd]
    exact Nat.factorization_eq_zero_of_not_dvd hd

lemma sum_large_prime_factorization_le_one {a N Y q : ℕ}
    (ha : 0 < a) (haN : a < N) (hNY : a * N + 1 ≤ Y)
    (hY : Y < N ^ 2) (hq : q.Prime) (hNq : N < q) :
    (∑ m ∈ Finset.Icc 1 N, ((a * m + 1).factorization q : ℝ)) ≤ 1 := by
  have hcount : (∑ m ∈ Finset.Icc 1 N, ((a * m + 1).factorization q : ℝ)) =
      (affineCount a q N : ℝ) := by
    calc
      _ = ∑ m ∈ Finset.Icc 1 N, if q ∣ a * m + 1 then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro m hm
        have hlt : a * m + 1 < q ^ 2 := by
          have hmN := (Finset.mem_Icc.mp hm).2
          have hle := Nat.mul_le_mul_left a hmN
          have hsq : N ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hNq.le 2
          omega
        rw [factorization_zero_one hq (by omega) hlt]
        split_ifs <;> norm_num
      _ = _ := by simp only [← Finset.sum_filter, Finset.sum_const,
        nsmul_eq_mul, mul_one, affineCount]
  rw [hcount]
  exact_mod_cast affineCount_le_one a q N hq.pos
    (Nat.coprime_of_lt_prime ha.ne' (haN.trans hNq) hq).symm hNq

theorem large_prime_affine_sum_le (u : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hgrowth : ∀ p : ℕ, p.Prime → |u p| ≤ C * Real.log (p : ℝ))
    {a N Y : ℕ} (ha : 0 < a) (haN : a < N) (haY : a * N + 1 ≤ Y)
    (hY : Y < N ^ 2) :
    (∑ m ∈ Finset.Icc 1 N,
      primePart u (Nat.primesLE Y \ Nat.primesLE N) (a * m + 1)) ≤
      ((Nat.primesLE Y \ Nat.primesLE N).filter (fun q ↦ 0 < u q)).card *
        (C * Real.log (Y : ℝ)) := by
  classical
  have heq : (∑ m ∈ Finset.Icc 1 N,
      primePart u (Nat.primesLE Y \ Nat.primesLE N) (a * m + 1)) =
      ∑ q ∈ Nat.primesLE Y \ Nat.primesLE N,
        u q * ∑ m ∈ Finset.Icc 1 N, ((a * m + 1).factorization q : ℝ) := by
    unfold primePart
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  rw [heq]
  calc
    _ ≤ ∑ q ∈ Nat.primesLE Y \ Nat.primesLE N,
        if 0 < u q then C * Real.log (Y : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨hqY, hqN⟩ := Finset.mem_sdiff.mp hq
      obtain ⟨hqle, hprime⟩ := Nat.mem_primesLE.mp hqY
      have hNq : N < q := by
        by_contra h
        exact hqN (Nat.mem_primesLE.mpr ⟨by omega, hprime⟩)
      have hsum := sum_large_prime_factorization_le_one ha haN haY hY hprime hNq
      have hnonneg : (0 : ℝ) ≤ ∑ m ∈ Finset.Icc 1 N,
          ((a * m + 1).factorization q : ℝ) :=
        Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _)
      split_ifs with huq
      · calc
          _ ≤ u q * 1 := mul_le_mul_of_nonneg_left hsum huq.le
          _ = u q := mul_one _
          _ ≤ C * Real.log (q : ℝ) := (le_abs_self _).trans (hgrowth q hprime)
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (Real.log_le_log (by exact_mod_cast hprime.pos) (by exact_mod_cast hqle)) hC
      · exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt huq) hnonneg
    _ = _ := by rw [← Finset.sum_filter]; simp only [Finset.sum_const, nsmul_eq_mul]

end Erdos491
