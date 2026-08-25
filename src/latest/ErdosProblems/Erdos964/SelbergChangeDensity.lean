import ErdosProblems.Erdos964.SelbergDimension

/-!
# Changing the scalar sieve density for a semiprime value

The density changes from `3/p` to `2/(p-1)` after fixing one affine
value to be a product of two primes. These finite identities identify
the transformed coefficients in Section 6 of arXiv:math/0609615.
-/

namespace Erdos964

open scoped BigOperators ArithmeticFunction.Moebius

theorem sum_upper_divisors_reindex (P r t : ℕ) (hP : P ≠ 0)
    (hrt : r ∣ t) (ht : t ∣ P) (F : ℕ → ℝ) :
    (∑ d ∈ P.divisors, if r ∣ d ∧ d ∣ t then F d else 0) =
      ∑ m ∈ (t / r).divisors, F (r * m) := by
  classical
  have ht0 : t ≠ 0 := ne_zero_of_dvd_ne_zero hP ht
  have hr0 : 0 < r := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero ht0 hrt)
  have hq0 : t / r ≠ 0 := (Nat.div_pos
    (Nat.le_of_dvd (Nat.pos_of_ne_zero ht0) hrt) hr0).ne'
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun d _ => d / r)
  · intro d hd
    obtain ⟨_, hrd, hdt⟩ := Finset.mem_filter.mp hd
    apply Nat.mem_divisors.mpr
    refine ⟨?_, hq0⟩
    rw [Nat.dvd_div_iff_mul_dvd hrt, Nat.mul_div_cancel' hrd]
    exact hdt
  · intro d hd e he hde
    have hrd := (Finset.mem_filter.mp hd).2.1
    have hre := (Finset.mem_filter.mp he).2.1
    simpa only [Nat.mul_div_cancel' hrd, Nat.mul_div_cancel' hre] using
      congrArg (r * ·) hde
  · intro m hm
    have hmt : r * m ∣ t := by
      rw [← Nat.mul_div_cancel' hrt]
      exact Nat.mul_dvd_mul_left r (Nat.dvd_of_mem_divisors hm)
    refine ⟨r * m, Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨hmt.trans ht, hP⟩, dvd_mul_right r m, hmt⟩, ?_⟩
    exact Nat.mul_div_cancel_left m hr0
  · intro d hd
    rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hd).2.1]

theorem squarefree_totient_real_product (m : ℕ) (hm : Squarefree m) :
    (Nat.totient m : ℝ) = ∏ p ∈ m.primeFactors, ((p : ℝ) - 1) := by
  rw [Nat.totient_eq_div_primeFactors_mul, Nat.prod_primeFactors_of_squarefree hm,
    Nat.div_self (Nat.pos_of_ne_zero hm.ne_zero), one_mul, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]

theorem scalar_density_change_euler (s t : BoundingSieve)
    (hs : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (3 : ℝ) / p)
    (ht : ∀ p, p.Prime → p ∣ s.prodPrimes → t.nu p = (2 : ℝ) / ((p : ℝ) - 1))
    (m : ℕ) (hm : m ∣ s.prodPrimes) :
    s.selbergTerms m *
      (∑ d ∈ m.divisors, (μ d : ℝ) * (t.nu d / s.nu d)) =
        1 / Nat.totient m := by
  have hmsq := s.prodPrimes_squarefree.squarefree_of_dvd hm
  have hEuler := (t.nu_mult.pdiv s.nu_mult).prodPrimeFactors_one_sub_of_squarefree
    (t.nu.pdiv s.nu) hmsq
  simp only [ArithmeticFunction.pdiv_apply] at hEuler
  rw [← hEuler, selbergTerms_eq_dimensionWeight s 3 hs m hm,
    dimensionSelbergWeight_apply 3 m hmsq.ne_zero]
  rw [squarefree_totient_real_product m hmsq, ← Finset.prod_mul_distrib,
    one_div, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpprime := Nat.prime_of_mem_primeFactors hp
  have hpP := (Nat.dvd_of_mem_primeFactors hp).trans hm
  have hp3 : (3 : ℝ) < p := by
    have hlt := s.nu_lt_one_of_prime p hpprime hpP
    rw [hs p hpprime hpP] at hlt
    exact (div_lt_one (by exact_mod_cast hpprime.pos)).mp hlt
  rw [hs p hpprime hpP, ht p hpprime hpP]
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp3' : (p : ℝ) - 3 ≠ 0 := by linarith
  norm_num only [Nat.cast_ofNat]
  field_simp
  ring

theorem scalar_density_change_factor (s t : BoundingSieve)
    (hP : t.prodPrimes = s.prodPrimes)
    (hs : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (3 : ℝ) / p)
    (ht : ∀ p, p.Prime → p ∣ s.prodPrimes → t.nu p = (2 : ℝ) / ((p : ℝ) - 1))
    (r : ℕ) (hr : r ∣ s.prodPrimes) :
    s.selbergTerms r * (t.nu r / s.nu r) =
      t.selbergTerms r * ((r : ℝ) / Nat.totient r) := by
  have hrT : r ∣ t.prodPrimes := hP ▸ hr
  have hrsq := s.prodPrimes_squarefree.squarefree_of_dvd hr
  have ht' : ∀ p, p.Prime → p ∣ t.prodPrimes →
      t.nu p = ((3 : ℝ) - 1) / ((p : ℝ) - 1) := by
    intro p hp hpT
    norm_num only
    exact ht p hp (hP ▸ hpT)
  have hrprod : (r : ℝ) = ∏ p ∈ r.primeFactors, (p : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ))
      (Nat.prod_primeFactors_of_squarefree hrsq).symm
    simpa only [Nat.cast_prod] using h
  rw [selbergTerms_eq_dimensionWeight s 3 hs r hr,
    selbergTerms_eq_semiprimeWeight t 3 ht' r hrT,
    dimensionSelbergWeight_apply 3 r hrsq.ne_zero,
    semiprimeSelbergWeight, ArithmeticFunction.prodPrimeFactors_apply hrsq.ne_zero,
    ← BoundingSieve.prod_primeFactors_nu hr,
    ← BoundingSieve.prod_primeFactors_nu hrT,
    squarefree_totient_real_product r hrsq, hrprod,
    ← Finset.prod_div_distrib, ← Finset.prod_div_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpprime := Nat.prime_of_mem_primeFactors hp
  have hpP := (Nat.dvd_of_mem_primeFactors hp).trans hr
  rw [hs p hpprime hpP, ht p hpprime hpP]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpprime.ne_zero
  norm_num only [Nat.cast_ofNat]
  field_simp

theorem scalar_density_change_interval (s t : BoundingSieve)
    (hP : t.prodPrimes = s.prodPrimes)
    (hs : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (3 : ℝ) / p)
    (ht : ∀ p, p.Prime → p ∣ s.prodPrimes → t.nu p = (2 : ℝ) / ((p : ℝ) - 1))
    (r u : ℕ) (hru : r ∣ u) (hu : u ∣ s.prodPrimes) :
    s.selbergTerms u *
      (∑ d ∈ s.prodPrimes.divisors,
        if r ∣ d ∧ d ∣ u then (μ d : ℝ) * (t.nu d / s.nu d) else 0) =
      (μ r : ℝ) * t.selbergTerms r * ((r : ℝ) / Nat.totient r) /
        Nat.totient (u / r) := by
  have husq := s.prodPrimes_squarefree.squarefree_of_dvd hu
  have hmul : r * (u / r) = u := Nat.mul_div_cancel' hru
  have hcop : r.Coprime (u / r) := by
    apply Nat.coprime_of_squarefree_mul
    rwa [hmul]
  have hq : u / r ∣ s.prodPrimes := (Nat.div_dvd_of_dvd hru).trans hu
  rw [sum_upper_divisors_reindex s.prodPrimes r u s.prodPrimes_squarefree.ne_zero hru hu]
  have hsum : (∑ m ∈ (u / r).divisors,
      (μ (r * m) : ℝ) * (t.nu (r * m) / s.nu (r * m))) =
      ((μ r : ℝ) * (t.nu r / s.nu r)) *
        ∑ m ∈ (u / r).divisors, (μ m : ℝ) * (t.nu m / s.nu m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hcm := hcop.coprime_dvd_right (Nat.dvd_of_mem_divisors hm)
    have hmu := (ArithmeticFunction.isMultiplicative_moebius.intCast
      (R := ℝ)).map_mul_of_coprime hcm
    have hratio := (t.nu_mult.pdiv s.nu_mult).map_mul_of_coprime hcm
    simp only [ArithmeticFunction.pdiv_apply] at hratio
    change (μ (r * m) : ℝ) = (μ r : ℝ) * (μ m : ℝ) at hmu
    rw [hmu, hratio]
    ring
  have hgs : s.selbergTerms u = s.selbergTerms r * s.selbergTerms (u / r) :=
    (congrArg s.selbergTerms hmul).symm.trans
      (BoundingSieve.selbergTerms_isMultiplicative.map_mul_of_coprime hcop)
  rw [hsum, hgs]
  have heuler := scalar_density_change_euler s t hs ht (u / r) hq
  have hfactor := scalar_density_change_factor s t hP hs ht r (hru.trans hu)
  calc
    _ = (μ r : ℝ) * (s.selbergTerms r * (t.nu r / s.nu r)) *
        (s.selbergTerms (u / r) * ∑ m ∈ (u / r).divisors,
          (μ m : ℝ) * (t.nu m / s.nu m)) := by ring
    _ = _ := by rw [heuler, hfactor]; ring

noncomputable def scalarSemiprimeTransform (P : ℕ) (y : ℕ → ℝ) (r : ℕ) : ℝ :=
  ((r : ℝ) / Nat.totient r) *
    ∑ u ∈ P.divisors, if r ∣ u then y u / Nat.totient (u / r) else 0

theorem scalarSemiprimeTransform_eq_sum (P : ℕ) (y : ℕ → ℝ) (r : ℕ)
    (hP : P ≠ 0) (hr : r ∣ P) :
    scalarSemiprimeTransform P y r = ((r : ℝ) / Nat.totient r) *
      ∑ m ∈ (P / r).divisors, y (r * m) / Nat.totient m := by
  have hrpos : 0 < r := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP hr)
  have h := sum_upper_divisors_reindex P r P hP hr (dvd_refl P)
    (fun u => y u / Nat.totient (u / r))
  simp only [Nat.mul_div_cancel_left _ hrpos] at h
  unfold scalarSemiprimeTransform
  congr 1
  rw [← h]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [Nat.dvd_of_mem_divisors hu, and_true]

theorem scalarSemiprimeTransform_eq_zero_of_not_dvd (P : ℕ) (y : ℕ → ℝ) (r : ℕ)
    (hr : ¬ r ∣ P) : scalarSemiprimeTransform P y r = 0 := by
  unfold scalarSemiprimeTransform
  have hzero : (∑ u ∈ P.divisors,
      if r ∣ u then y u / Nat.totient (u / r) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    exact if_neg (fun hru => hr (hru.trans (Nat.dvd_of_mem_divisors hu)))
  rw [hzero, mul_zero]

theorem scalarSemiprimeTransform_eq_zero_of_radius (P R : ℕ) (y : ℕ → ℝ)
    (hy : ∀ u, R ≤ u → y u = 0) (r : ℕ) (hr : R ≤ r) :
    scalarSemiprimeTransform P y r = 0 := by
  unfold scalarSemiprimeTransform
  have hzero : (∑ u ∈ P.divisors,
      if r ∣ u then y u / Nat.totient (u / r) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    by_cases hru : r ∣ u
    · rw [if_pos hru, hy u (hr.trans (Nat.le_of_dvd (Nat.pos_of_mem_divisors hu) hru)),
        zero_div]
    · exact if_neg hru
  rw [hzero, mul_zero]

theorem scalarSelberg_forward_change_kernel (s t : BoundingSieve) (y : ℕ → ℝ) (r : ℕ) :
    (∑ d ∈ s.prodPrimes.divisors,
      if r ∣ d then t.nu d * scalarSelbergCoefficient s y d else 0) =
      ∑ u ∈ s.prodPrimes.divisors, (s.selbergTerms u * y u) *
        ∑ d ∈ s.prodPrimes.divisors,
          if r ∣ d ∧ d ∣ u then (μ d : ℝ) * (t.nu d / s.nu d) else 0 := by
  classical
  calc
    _ = ∑ d ∈ s.prodPrimes.divisors, ∑ u ∈ s.prodPrimes.divisors,
        (s.selbergTerms u * y u) *
          (if r ∣ d ∧ d ∣ u then (μ d : ℝ) * (t.nu d / s.nu d) else 0) := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases hrd : r ∣ d
      · simp only [if_pos hrd, scalarSelbergCoefficient, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        by_cases hdu : d ∣ u
        · simp only [hrd, hdu, and_self, ite_true]
          ring
        · simp [hrd, hdu]
      · simp [hrd]
    _ = _ := by rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]

theorem scalarSelberg_semiprime_forward (s t : BoundingSieve)
    (hP : t.prodPrimes = s.prodPrimes)
    (hs : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (3 : ℝ) / p)
    (ht : ∀ p, p.Prime → p ∣ s.prodPrimes → t.nu p = (2 : ℝ) / ((p : ℝ) - 1))
    (y : ℕ → ℝ) (r : ℕ) :
    (∑ d ∈ s.prodPrimes.divisors,
      if r ∣ d then t.nu d * scalarSelbergCoefficient s y d else 0) =
      (μ r : ℝ) * t.selbergTerms r * scalarSemiprimeTransform s.prodPrimes y r := by
  rw [scalarSelberg_forward_change_kernel, scalarSemiprimeTransform]
  conv_rhs => simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hru : r ∣ u
  · rw [if_pos hru]
    have h := scalar_density_change_interval s t hP hs ht r u hru
      (Nat.dvd_of_mem_divisors hu)
    calc
      _ = y u * (s.selbergTerms u * ∑ d ∈ s.prodPrimes.divisors,
          if r ∣ d ∧ d ∣ u then (μ d : ℝ) * (t.nu d / s.nu d) else 0) := by ring
      _ = _ := by rw [h]; ring
  · have hzero : (∑ d ∈ s.prodPrimes.divisors,
        if r ∣ d ∧ d ∣ u then (μ d : ℝ) * (t.nu d / s.nu d) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro d _
      exact if_neg (fun h => hru (h.1.trans h.2))
    rw [hzero, if_neg hru]
    ring

theorem scalarSelberg_semiprime_diagonal (s t : BoundingSieve)
    (hP : t.prodPrimes = s.prodPrimes)
    (hs : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (3 : ℝ) / p)
    (ht : ∀ p, p.Prime → p ∣ s.prodPrimes → t.nu p = (2 : ℝ) / ((p : ℝ) - 1))
    (y : ℕ → ℝ) :
    t.mainSum (BoundingSieve.lambdaSquared (scalarSelbergCoefficient s y)) =
      ∑ r ∈ s.prodPrimes.divisors,
        semiprimeSelbergWeight 3 r * (scalarSemiprimeTransform s.prodPrimes y r) ^ 2 := by
  rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq, hP]
  apply Finset.sum_congr rfl
  intro r hr
  have hrP := Nat.dvd_of_mem_divisors hr
  have hsq := s.prodPrimes_squarefree.squarefree_of_dvd hrP
  have hmu : (μ r : ℝ) ^ 2 = 1 := by
    exact_mod_cast (BoundedGaps.Maynard.squarefree_iff_moebius_sq_eq_one r).mp hsq
  have hg : t.selbergTerms r ≠ 0 := (BoundingSieve.selbergTerms_pos (hP ▸ hrP)).ne'
  have ht' : ∀ p, p.Prime → p ∣ t.prodPrimes →
      t.nu p = ((3 : ℝ) - 1) / ((p : ℝ) - 1) := by
    intro p hp hpT
    norm_num only
    exact ht p hp (hP ▸ hpT)
  have hgt := selbergTerms_eq_semiprimeWeight t 3 ht' r (hP ▸ hrP)
  rw [scalarSelberg_semiprime_forward s t hP hs ht y r, mul_pow, mul_pow, hmu]
  rw [← hgt]
  field_simp

end Erdos964
