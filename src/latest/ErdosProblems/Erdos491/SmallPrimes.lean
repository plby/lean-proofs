import ErdosProblems.Erdos491.AffineValuations

/-! # Uniform control of the small-prime part of an affine average -/

open Filter
open scoped BigOperators Topology

namespace Erdos491

noncomputable def primePart (u : ℕ → ℝ) (S : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ p ∈ S, u p * (n.factorization p : ℝ)

lemma PosCompletelyAdditive.map_prod {ι : Type*} {u : ℕ → ℝ}
    (hu : PosCompletelyAdditive u) (S : Finset ι) (a : ι → ℕ)
    (hpos : ∀ i ∈ S, 0 < a i) :
    u (∏ i ∈ S, a i) = ∑ i ∈ S, u (a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [hu.one_eq_zero]
  | @insert i S hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi,
        hu (hpos i (Finset.mem_insert_self _ _))
          (Finset.prod_pos (fun j hj ↦ hpos j (Finset.mem_insert_of_mem hj))),
        ih (fun j hj ↦ hpos j (Finset.mem_insert_of_mem hj))]

lemma PosCompletelyAdditive.eq_primePart {u : ℕ → ℝ}
    (hu : PosCompletelyAdditive u) {n Y : ℕ} (hn : 0 < n) (hnY : n ≤ Y) :
    u n = primePart u (Nat.primesLE Y) n := by
  classical
  have hfac : u n = ∑ p ∈ n.factorization.support, u p * (n.factorization p : ℝ) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn.ne']
    rw [Finsupp.prod, hu.map_prod]
    · apply Finset.sum_congr rfl
      intro p hp
      rw [hu.pow (Nat.prime_of_mem_primeFactors hp).pos, mul_comm]
    · intro p hp
      exact pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  rw [hfac, primePart]
  apply Finset.sum_subset
  · intro p hp
    exact Nat.mem_primesLE.mpr
      ⟨(Nat.le_of_mem_primeFactors hp).trans hnY, Nat.prime_of_mem_primeFactors hp⟩
  · intro p _ hp
    have hz : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
    simp [hz]

lemma primePart_union (u : ℕ → ℝ) (S U : Finset ℕ) (hdis : Disjoint S U) (n : ℕ) :
    primePart u (S ∪ U) n = primePart u S n + primePart u U n := by
  classical
  exact Finset.sum_union hdis

lemma primePart_sum_difference (u : ℕ → ℝ) (S : Finset ℕ) (a N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, (primePart u S (a * m + 1) - primePart u S m)) =
      ∑ p ∈ S, u p * (∑ m ∈ Finset.Icc 1 N,
        (((a * m + 1).factorization p : ℝ) - (m.factorization p : ℝ))) := by
  simp only [primePart, ← Finset.sum_sub_distrib, ← mul_sub]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

lemma prime_factorization_affine_pow_zero {p r : ℕ} (hp : p.Prime)
    (hr : 0 < r) (m : ℕ) : (p ^ r * m + 1).factorization p = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  apply hp.coprime_iff_not_dvd.mp
  exact (coprime_affine (p ^ r) m).of_dvd_left (dvd_pow_self p hr.ne')

lemma log_mul_natLog_le (p Y : ℕ) (hp : 1 < p) :
    Real.log (p : ℝ) * (Nat.log p Y : ℝ) ≤ Real.log (Y : ℝ) := by
  have hpR : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp)
  have h := Real.natLog_le_logb Y p
  rw [Real.logb, le_div_iff₀ hpR] at h
  simpa only [mul_comm] using h

/-- The error is independent of the exponent `r`. The prime dividing the
affine multiplier contributes with the favorable sign. -/
theorem small_prime_affine_error_le (u : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hgrowth : ∀ p : ℕ, p.Prime → |u p| ≤ C * Real.log (p : ℝ))
    {p r N Y : ℕ} (hp : p.Prime) (hr : 0 < r) (hup : 0 ≤ u p)
    (haY : p ^ r * N + 1 ≤ Y) (hNY : N ≤ Y) :
    (∑ m ∈ Finset.Icc 1 N,
      (primePart u (Nat.primesLE N) (p ^ r * m + 1) -
        primePart u (Nat.primesLE N) m)) ≤
      C * Real.log (Y : ℝ) * (Nat.primesLE N).card := by
  classical
  have hYpos : 0 < Y := by omega
  have hlogY : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast hYpos)
  rw [primePart_sum_difference]
  calc
    _ ≤ ∑ _q ∈ Nat.primesLE N, C * Real.log (Y : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      have hprime := Nat.prime_of_mem_primesLE hq
      by_cases heq : q = p
      · subst q
        have hsum : (∑ m ∈ Finset.Icc 1 N,
            (((p ^ r * m + 1).factorization p : ℝ) - (m.factorization p : ℝ))) ≤ 0 := by
          apply Finset.sum_nonpos
          intro m _
          rw [prime_factorization_affine_pow_zero hp hr m, Nat.cast_zero, zero_sub]
          exact neg_nonpos.mpr (Nat.cast_nonneg _)
        exact (mul_nonpos_of_nonneg_of_nonpos hup hsum).trans (mul_nonneg hC hlogY)
      · have hcop : (p ^ r).Coprime q :=
          ((Nat.coprime_primes hp hprime).mpr (Ne.symm heq)).pow_left _
        have herr := sum_affine_factorization_sub_bound hprime hcop haY hNY
        calc
          _ ≤ |u q| * |∑ m ∈ Finset.Icc 1 N,
              (((p ^ r * m + 1).factorization q : ℝ) - (m.factorization q : ℝ))| := by
            simpa only [abs_mul] using le_abs_self
              (u q * (∑ m ∈ Finset.Icc 1 N,
                (((p ^ r * m + 1).factorization q : ℝ) - (m.factorization q : ℝ))))
          _ ≤ (C * Real.log (q : ℝ)) * (Nat.log q Y : ℝ) :=
            mul_le_mul (hgrowth q hprime) herr (abs_nonneg _)
              (mul_nonneg hC (Real.log_nonneg (by exact_mod_cast hprime.one_le)))
          _ = C * (Real.log (q : ℝ) * (Nat.log q Y : ℝ)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (log_mul_natLog_le q Y hprime.one_lt) hC
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

lemma eventually_prime_count_log_bound :
    ∀ᶠ N : ℕ in atTop,
      ((Nat.primesLE N).card : ℝ) * Real.log (N : ℝ) ≤
        (Real.log 4 + 1) * N := by
  have h := (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).eventually
      (Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num))
  filter_upwards [h, eventually_ge_atTop (2 : ℕ)] with N hN hN2
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  rw [Nat.floor_natCast] at hN
  rw [Nat.primesLE_card_eq_primeCounting]
  exact (le_div_iff₀ hlog).mp hN

end Erdos491
