import ErdosProblems.Erdos394.PrimeSubset
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Nat Finset

namespace Erdos394

lemma nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hpow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
      omega

/-- Every positive `d≤N` divides the `N`th power of the product of all primes
at most `N`. -/
theorem dvd_primeProduct_primesLE_pow
    {d N : ℕ} (hd : d ∈ Finset.Icc 1 N) :
    d ∣ (primeProduct N.primesLE) ^ N := by
  have hdI := Finset.mem_Icc.mp hd
  have hd0 : d ≠ 0 := by omega
  have hNpos : 0 < N := lt_of_lt_of_le (by omega) hdI.2
  have hQ0 : primeProduct N.primesLE ≠ 0 := by
    unfold primeProduct
    exact Finset.prod_ne_zero_iff.mpr fun p hp ↦
      (Nat.mem_primesLE.mp hp).2.ne_zero
  apply (Nat.factorization_le_iff_dvd hd0 (pow_ne_zero N hQ0)).mp
  intro p
  by_cases hp : p.Prime
  · by_cases hpd : p ∣ d
    · have hp_le_d := Nat.le_of_dvd (by omega) hpd
      have hpN : p ∈ N.primesLE := Nat.mem_primesLE.mpr
        ⟨hp_le_d.trans hdI.2, hp⟩
      have hpQ : p ∣ primeProduct N.primesLE := by
        unfold primeProduct
        exact Finset.dvd_prod_of_mem (fun z : ℕ ↦ z) hpN
      have hfacQ : 1 ≤ (primeProduct N.primesLE).factorization p :=
        (hp.dvd_iff_one_le_factorization hQ0).mp hpQ
      have hpowdvd : p ^ (d.factorization p) ∣ d :=
        (hp.pow_dvd_iff_le_factorization hd0).mpr le_rfl
      have hpowle : p ^ (d.factorization p) ≤ d :=
        Nat.le_of_dvd (by omega) hpowdvd
      have htwo : 2 ^ (d.factorization p) ≤ p ^ (d.factorization p) :=
        Nat.pow_le_pow_left hp.two_le _
      have hfacN : d.factorization p ≤ N :=
        (nat_le_two_pow _).trans htwo |>.trans hpowle |>.trans hdI.2
      rw [Nat.factorization_pow]
      change d.factorization p ≤ N * (primeProduct N.primesLE).factorization p
      exact hfacN.trans (Nat.le_mul_of_pos_right N hfacQ)
    · rw [Nat.factorization_eq_zero_of_not_dvd hpd]
      exact Nat.zero_le _
  · rw [Nat.factorization_eq_zero_of_not_prime d hp]
    exact Nat.zero_le _

/-- Reciprocal divisor sum is the ordinary divisor sum divided by the
integer. -/
theorem sum_divisors_inv_eq_sigma_div {M : ℕ} (hM : 0 < M) :
    (∑ d ∈ M.divisors, (1 / (d : ℝ))) =
      ((ArithmeticFunction.sigma 1 M : ℕ) : ℝ) / (M : ℝ) := by
  rw [ArithmeticFunction.sigma_eq_sum_div]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hdmem := Nat.mem_divisors.mp hd
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdmem.1 hM
  have hmul : M / d * d = M := Nat.div_mul_cancel hdmem.1
  have hMR : (M : ℝ) ≠ 0 := by positivity
  have hdR : (d : ℝ) ≠ 0 := by positivity
  have hmulR : (((M / d : ℕ) : ℝ) * (d : ℝ)) = (M : ℝ) := by
    exact_mod_cast hmul
  field_simp
  simpa [mul_comm] using hmulR.symm

/-- One finite geometric Euler factor, multiplied by `1-1/p`, is at most
one. -/
theorem geom_euler_factor_le_one {p N : ℕ} (hp : p.Prime) :
    ((∑ i ∈ Finset.range (N + 1), ((p ^ i : ℕ) : ℝ)) /
        ((p ^ N : ℕ) : ℝ)) * (1 - 1 / (p : ℝ)) ≤ 1 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpowR : (0 : ℝ) < ((p ^ N : ℕ) : ℝ) := by
    exact_mod_cast pow_pos hp.pos N
  have hgeom :
      (∑ i ∈ Finset.range (N + 1), ((p ^ i : ℕ) : ℝ)) *
          ((p : ℝ) - 1) = (p : ℝ) ^ (N + 1) - 1 := by
    simpa only [Nat.cast_pow] using (geom_sum_mul (p : ℝ) (N + 1))
  have heq :
      ((∑ i ∈ Finset.range (N + 1), ((p ^ i : ℕ) : ℝ)) /
          ((p ^ N : ℕ) : ℝ)) * (1 - 1 / (p : ℝ)) =
        ((p : ℝ) ^ (N + 1) - 1) / ((p : ℝ) ^ (N + 1)) := by
    calc
      ((∑ i ∈ Finset.range (N + 1), ((p ^ i : ℕ) : ℝ)) /
          ((p ^ N : ℕ) : ℝ)) * (1 - 1 / (p : ℝ)) =
        ((∑ i ∈ Finset.range (N + 1), ((p ^ i : ℕ) : ℝ)) *
          ((p : ℝ) - 1)) / (((p : ℝ) ^ N) * (p : ℝ)) := by
            push_cast
            field_simp
      _ = ((p : ℝ) ^ (N + 1) - 1) / ((p : ℝ) ^ (N + 1)) := by
        rw [hgeom, pow_succ]
  rw [heq]
  exact (div_le_one (by positivity : (0 : ℝ) < (p : ℝ) ^ (N + 1))).2
    (sub_le_self _ (by norm_num))

/-- The reciprocal divisor sum of the universal smooth multiple, times its
finite Euler density, is at most one. -/
theorem sum_divisors_universal_mul_euler_le_one
    {N : ℕ} (hN : 0 < N) :
    (∑ d ∈ ((primeProduct N.primesLE) ^ N).divisors,
        (1 / (d : ℝ))) *
      localEulerProduct N.primesLE (fun p ↦ 1 / (p : ℝ)) ≤ 1 := by
  let P := N.primesLE
  let Q := primeProduct P
  let M := Q ^ N
  have hPprime : ∀ p ∈ P, p.Prime := fun p hp ↦ (Nat.mem_primesLE.mp hp).2
  have hQ0 : Q ≠ 0 := by
    dsimp [Q, primeProduct]
    exact Finset.prod_ne_zero_iff.mpr fun p hp ↦ (hPprime p hp).ne_zero
  have hMpos : 0 < M := pow_pos (Nat.pos_of_ne_zero hQ0) N
  have hpfM : M.primeFactors = P := by
    dsimp [M]
    rw [Nat.primeFactors_pow Q hN.ne', primeFactors_primeProduct P hPprime]
  have hfacM : ∀ p ∈ P, M.factorization p = N := by
    intro p hpP
    have hp := hPprime p hpP
    have hpQ : p ∣ Q := by
      dsimp [Q, primeProduct]
      exact Finset.dvd_prod_of_mem (fun z : ℕ ↦ z) hpP
    have hsq : Squarefree Q := squarefree_primeProduct P hPprime
    have hfacQ : Q.factorization p = 1 :=
      Nat.factorization_eq_one_of_squarefree hsq hp hpQ
    dsimp [M]
    rw [Nat.factorization_pow]
    change N * Q.factorization p = N
    rw [hfacQ, mul_one]
  rw [sum_divisors_inv_eq_sigma_div hMpos]
  rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hMpos.ne']
  rw [hpfM]
  have hprodFac :
      (∏ p ∈ P, ∑ i ∈ Finset.range (M.factorization p + 1), p ^ (i * 1)) =
        ∏ p ∈ P, ∑ i ∈ Finset.range (N + 1), p ^ i := by
    apply Finset.prod_congr rfl
    intro p hpP
    rw [hfacM p hpP]
    simp only [mul_one]
  rw [hprodFac]
  have hMprod : (M : ℝ) = ∏ p ∈ P, ((p ^ N : ℕ) : ℝ) := by
    dsimp [M, Q, primeProduct]
    rw [← Finset.prod_pow]
    push_cast
    rfl
  rw [hMprod]
  push_cast
  unfold localEulerProduct
  change ((∏ p ∈ P, ∑ i ∈ Finset.range (N + 1), ((p : ℝ) ^ i)) /
      ∏ p ∈ P, ((p : ℝ) ^ N)) *
    (∏ p ∈ P, (1 - 1 / (p : ℝ))) ≤ 1
  rw [← Finset.prod_div_distrib]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_one
  · intro p hpP
    have hsum0 : 0 ≤ ∑ i ∈ Finset.range (N + 1), ((p ^ i : ℕ) : ℝ) := by
      positivity
    have hfactor0 : 0 ≤ 1 - 1 / (p : ℝ) := by
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hPprime p hpP).one_le
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (hPprime p hpP).pos
      exact sub_nonneg.mpr ((div_le_one hp0).2 hp1)
    positivity
  · intro p hpP
    simpa only [Nat.cast_pow] using
      (geom_euler_factor_le_one (N := N) (hPprime p hpP))

/-- Sharp elementary Mertens upper bound: the Euler density over all primes
at most `N` is at most the reciprocal harmonic number. -/
theorem harmonic_mul_primeEuler_le_one {N : ℕ} (hN : 0 < N) :
    ((harmonic N : ℚ) : ℝ) *
      localEulerProduct N.primesLE (fun p ↦ 1 / (p : ℝ)) ≤ 1 := by
  let M := (primeProduct N.primesLE) ^ N
  have hsub : Finset.Icc 1 N ⊆ M.divisors := by
    intro d hd
    exact Nat.mem_divisors.mpr
      ⟨dvd_primeProduct_primesLE_pow hd, by
        dsimp [M, primeProduct]
        exact pow_ne_zero N (Finset.prod_ne_zero_iff.mpr fun p hp ↦
          (Nat.mem_primesLE.mp hp).2.ne_zero)⟩
  have hsum : (((harmonic N : ℚ) : ℝ)) ≤
      ∑ d ∈ M.divisors, (1 / (d : ℝ)) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    have hs := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun d : ℕ ↦ ((d : ℝ)⁻¹)) hsub (by
        intro d hd hnot
        positivity)
    simpa [one_div] using hs
  have hV0 : 0 ≤ localEulerProduct N.primesLE (fun p ↦ 1 / (p : ℝ)) := by
    apply localEulerProduct_nonneg
    · intro p hp; positivity
    · intro p hp
      have hp0 : (0 : ℝ) < p := by
        exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos
      exact (div_le_one hp0).2 (by
        exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le)
  apply (mul_le_mul_of_nonneg_right hsum hV0).trans
  dsimp [M]
  exact sum_divisors_universal_mul_euler_le_one hN

/-- Consequently the full finite prime Euler density is at most `1/log(N+1)`. -/
theorem primeEuler_le_inv_log_add_one {N : ℕ} (hN : 0 < N) :
    localEulerProduct N.primesLE (fun p ↦ 1 / (p : ℝ)) ≤
      1 / Real.log (N + 1 : ℕ) := by
  have hlog := log_add_one_le_harmonic N
  have hHV := harmonic_mul_primeEuler_le_one hN
  have hlogpos : 0 < Real.log (N + 1 : ℕ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N + 1 by omega))
  have hV0 : 0 ≤ localEulerProduct N.primesLE (fun p ↦ 1 / (p : ℝ)) := by
    apply localEulerProduct_nonneg
    · intro p hp; positivity
    · intro p hp
      have hp0 : (0 : ℝ) < p := by
        exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos
      exact (div_le_one hp0).2 (by
        exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le)
  rw [le_div_iff₀ hlogpos]
  calc
    localEulerProduct N.primesLE (fun p ↦ 1 / (p : ℝ)) *
        Real.log (N + 1 : ℕ) ≤
      localEulerProduct N.primesLE (fun p ↦ 1 / (p : ℝ)) *
        (((harmonic N : ℚ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog hV0
    _ = (((harmonic N : ℚ) : ℝ)) *
        localEulerProduct N.primesLE (fun p ↦ 1 / (p : ℝ)) := by ring
    _ ≤ 1 := hHV

end Erdos394
