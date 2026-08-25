import ErdosProblems.Erdos964.SelbergChangeDensity
import ErdosProblems.Erdos964.ScalarAffineS1

/-!
# Removing the smaller prime from the scalar sieve kernel

At a semiprime value with smaller prime `p`, the density kernel ignores
the factor `p`. Splitting squarefree divisors into `d` and `p*d` gives
the difference of transformed coefficients used in the GGPY second sum.
-/

namespace Erdos964

open scoped BigOperators ArithmeticFunction.Moebius

theorem sum_squarefree_divisors_split_prime (P p : ℕ) (hP : Squarefree P)
    (hp : p.Prime) (hpP : p ∣ P) (F : ℕ → ℝ) :
    (∑ d ∈ P.divisors, F d) = ∑ d ∈ (P / p).divisors, (F d + F (p * d)) := by
  classical
  have hmul : p * (P / p) = P := Nat.mul_div_cancel' hpP
  have hcop : p.Coprime (P / p) := by
    apply Nat.coprime_of_squarefree_mul
    rwa [hmul]
  have hdiv : P.divisors = (p.divisors ×ˢ (P / p).divisors).image (fun x => x.1 * x.2) := by
    rw [← Finset.mul_def, ← Nat.divisors_mul, hmul]
  rw [hdiv, Finset.sum_image hcop.mul_injOn_divisors, Finset.sum_product,
    hp.divisors, Finset.sum_pair (Ne.symm hp.ne_one)]
  simp only [one_mul, Finset.sum_add_distrib]

def removeSievePrime (s : BoundingSieve) (p : ℕ) (hpP : p ∣ s.prodPrimes) : BoundingSieve :=
  { s with
    prodPrimes := s.prodPrimes / p
    prodPrimes_squarefree := s.prodPrimes_squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd hpP)
    nu_pos_of_prime := fun q hq hqP => s.nu_pos_of_prime q hq
      (hqP.trans (Nat.div_dvd_of_dvd hpP))
    nu_lt_one_of_prime := fun q hq hqP => s.nu_lt_one_of_prime q hq
      (hqP.trans (Nat.div_dvd_of_dvd hpP)) }

theorem removeSievePrime_selbergTerms (s : BoundingSieve) (p : ℕ)
    (hpP : p ∣ s.prodPrimes) (d : ℕ) :
    (removeSievePrime s p hpP).selbergTerms d = s.selbergTerms d := rfl

theorem prime_dvd_divisor_iff_not_removed (P p d : ℕ) (hP : Squarefree P)
    (hp : p.Prime) (hpP : p ∣ P) (hd : d ∣ P) :
    d ∣ P / p ↔ ¬ p ∣ d := by
  have hmul : p * (P / p) = P := Nat.mul_div_cancel' hpP
  have hcop : p.Coprime (P / p) := by
    apply Nat.coprime_of_squarefree_mul
    rwa [hmul]
  constructor
  · intro hdq hpd
    exact (hp.coprime_iff_not_dvd.mp hcop) (hpd.trans hdq)
  · intro hpd
    have hcp := hp.coprime_iff_not_dvd.mpr hpd
    apply hcp.symm.dvd_of_dvd_mul_left
    rwa [hmul]

noncomputable def scalarPrimeRemovedKernel (s : BoundingSieve) (p : ℕ)
    (w : ℕ → ℝ) : ℝ :=
  ∑ d ∈ s.prodPrimes.divisors, ∑ e ∈ s.prodPrimes.divisors,
    s.nu (Nat.lcm (d / Nat.gcd d p) (e / Nat.gcd e p)) * (w d * w e)

theorem lcm_strip_gcd (d e p : ℕ) (hp : 0 < p) :
    Nat.lcm (d / Nat.gcd d p) (e / Nat.gcd e p) = Nat.lcm (Nat.lcm d e) p / p := by
  have hstrip (n : ℕ) : p * (n / Nat.gcd n p) = Nat.lcm n p := by
    rw [← Nat.mul_div_assoc p (Nat.gcd_dvd_left n p), Nat.mul_comm p n,
      Nat.lcm_eq_mul_div]
  have hmul : p * Nat.lcm (d / Nat.gcd d p) (e / Nat.gcd e p) =
      Nat.lcm (Nat.lcm d e) p := by
    rw [← Nat.lcm_mul_left, hstrip d, hstrip e, Nat.lcm_assoc,
      Nat.lcm_lcm_self_right_right, Nat.lcm_comm p e, ← Nat.lcm_assoc]
  rw [← hmul, Nat.mul_div_cancel_left _ hp]

theorem scalarPrimeRemovedKernel_eq_paper_kernel (s : BoundingSieve) (p : ℕ)
    (hp : 0 < p) (w : ℕ → ℝ) :
    scalarPrimeRemovedKernel s p w =
      ∑ d ∈ s.prodPrimes.divisors, ∑ e ∈ s.prodPrimes.divisors,
        s.nu (Nat.lcm (Nat.lcm d e) p / p) * (w d * w e) := by
  unfold scalarPrimeRemovedKernel
  simp_rw [lcm_strip_gcd _ _ p hp]

theorem scalarPrimeRemovedKernel_eq_main_of_not_dvd (s : BoundingSieve) (p : ℕ)
    (hp : p.Prime) (hpP : ¬ p ∣ s.prodPrimes) (w : ℕ → ℝ) :
    scalarPrimeRemovedKernel s p w = s.mainSum (BoundingSieve.lambdaSquared w) := by
  rw [scalarPrimeRemovedKernel, selberg_mainSum_eq_lcm_sum]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  have hdcp := (hp.coprime_iff_not_dvd.mpr
    (fun h => hpP (h.trans (Nat.dvd_of_mem_divisors hd)))).symm
  have hecp := (hp.coprime_iff_not_dvd.mpr
    (fun h => hpP (h.trans (Nat.dvd_of_mem_divisors he)))).symm
  rw [hdcp.gcd_eq_one, hecp.gcd_eq_one, Nat.div_one, Nat.div_one]

theorem divisors_quotient_prime_eq_filter (P p : ℕ) (hP : Squarefree P)
    (hp : p.Prime) (hpP : p ∣ P) :
    (P / p).divisors = P.divisors.filter (fun r => ¬ p ∣ r) := by
  ext r
  have hQ0 := (hP.squarefree_of_dvd (Nat.div_dvd_of_dvd hpP)).ne_zero
  simp only [Nat.mem_divisors, hQ0, hP.ne_zero, ne_eq, not_false_eq_true,
    and_true, Finset.mem_filter]
  constructor
  · intro hr
    have hrP := hr.trans (Nat.div_dvd_of_dvd hpP)
    exact ⟨hrP, (prime_dvd_divisor_iff_not_removed P p r hP hp hpP hrP).mp hr⟩
  · rintro ⟨hrP, hnot⟩
    exact (prime_dvd_divisor_iff_not_removed P p r hP hp hpP hrP).mpr hnot

theorem scalarPrimeRemovedKernel_eq_collapsed (s : BoundingSieve) (p : ℕ)
    (hp : p.Prime) (hpP : p ∣ s.prodPrimes) (w : ℕ → ℝ) :
    scalarPrimeRemovedKernel s p w =
      (removeSievePrime s p hpP).mainSum
        (BoundingSieve.lambdaSquared (fun d => w d + w (p * d))) := by
  have hmul : p * (s.prodPrimes / p) = s.prodPrimes := Nat.mul_div_cancel' hpP
  have hcop : p.Coprime (s.prodPrimes / p) := by
    apply Nat.coprime_of_squarefree_mul
    rw [hmul]
    exact s.prodPrimes_squarefree
  have hremove (d : ℕ) (hd : d ∈ (s.prodPrimes / p).divisors) : d / Nat.gcd d p = d := by
    rw [(hcop.coprime_dvd_right (Nat.dvd_of_mem_divisors hd)).symm.gcd_eq_one, Nat.div_one]
  have hremove_mul (d : ℕ) : (p * d) / Nat.gcd (p * d) p = d := by
    rw [Nat.gcd_eq_right (dvd_mul_right p d), Nat.mul_div_cancel_left d hp.pos]
  rw [scalarPrimeRemovedKernel, selberg_mainSum_eq_lcm_sum,
    sum_squarefree_divisors_split_prime s.prodPrimes p s.prodPrimes_squarefree hp hpP]
  change (∑ d ∈ (s.prodPrimes / p).divisors,
      ((∑ e ∈ s.prodPrimes.divisors,
        s.nu (Nat.lcm (d / Nat.gcd d p) (e / Nat.gcd e p)) * (w d * w e)) +
       (∑ e ∈ s.prodPrimes.divisors,
        s.nu (Nat.lcm ((p * d) / Nat.gcd (p * d) p) (e / Nat.gcd e p)) *
          (w (p * d) * w e)))) =
    ∑ d ∈ (s.prodPrimes / p).divisors, ∑ e ∈ (s.prodPrimes / p).divisors,
      s.nu (Nat.lcm d e) * ((w d + w (p * d)) * (w e + w (p * e)))
  apply Finset.sum_congr rfl
  intro d hd
  rw [hremove d hd, hremove_mul d,
    sum_squarefree_divisors_split_prime s.prodPrimes p s.prodPrimes_squarefree hp hpP,
    sum_squarefree_divisors_split_prime s.prodPrimes p s.prodPrimes_squarefree hp hpP,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  rw [hremove e he, hremove_mul e]
  ring

theorem selberg_prime_removed_forward_split (s : BoundingSieve) (w : ℕ → ℝ)
    (p : ℕ) (hp : p.Prime) (hpP : p ∣ s.prodPrimes) (r : ℕ)
    (hr : r ∣ s.prodPrimes / p) :
    (∑ d ∈ (s.prodPrimes / p).divisors,
      if r ∣ d then s.nu d * (w d + w (p * d)) else 0) =
      (∑ d ∈ s.prodPrimes.divisors, if r ∣ d then s.nu d * w d else 0) +
      (1 / s.nu p - 1) *
        ∑ d ∈ s.prodPrimes.divisors, if p * r ∣ d then s.nu d * w d else 0 := by
  classical
  have hmul : p * (s.prodPrimes / p) = s.prodPrimes := Nat.mul_div_cancel' hpP
  have hcop : p.Coprime (s.prodPrimes / p) := by
    apply Nat.coprime_of_squarefree_mul
    rw [hmul]
    exact s.prodPrimes_squarefree
  have hpr := (hcop.coprime_dvd_right hr).symm
  have hB : (∑ d ∈ s.prodPrimes.divisors, if r ∣ d then s.nu d * w d else 0) =
      ∑ d ∈ (s.prodPrimes / p).divisors,
        if r ∣ d then s.nu d * w d + s.nu p * s.nu d * w (p * d) else 0 := by
    rw [sum_squarefree_divisors_split_prime s.prodPrimes p s.prodPrimes_squarefree hp hpP]
    apply Finset.sum_congr rfl
    intro d hd
    have hpd := hcop.coprime_dvd_right (Nat.dvd_of_mem_divisors hd)
    simp only [hpr.dvd_mul_left, s.nu_mult.map_mul_of_coprime hpd]
    by_cases hrd : r ∣ d <;> simp [hrd]
  have hC : (∑ d ∈ s.prodPrimes.divisors, if p * r ∣ d then s.nu d * w d else 0) =
      ∑ d ∈ (s.prodPrimes / p).divisors,
        if r ∣ d then s.nu p * s.nu d * w (p * d) else 0 := by
    rw [sum_squarefree_divisors_split_prime s.prodPrimes p s.prodPrimes_squarefree hp hpP]
    apply Finset.sum_congr rfl
    intro d hd
    have hpd := hcop.coprime_dvd_right (Nat.dvd_of_mem_divisors hd)
    have hnot : ¬ p * r ∣ d := fun h => (hp.coprime_iff_not_dvd.mp hpd)
      ((dvd_mul_right p r).trans h)
    simp only [if_neg hnot, zero_add, Nat.mul_dvd_mul_iff_left hp.pos,
      s.nu_mult.map_mul_of_coprime hpd]
  rw [hB, hC, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hrd : r ∣ d
  · rw [if_pos hrd, if_pos hrd, if_pos hrd]
    have hnu := BoundingSieve.nu_ne_zero (s := s) hpP
    field_simp
    ring
  · simp [hrd]

theorem selberg_prime_removed_forward (s : BoundingSieve) (w z : ℕ → ℝ)
    (hforward : ∀ r, r ∣ s.prodPrimes →
      (∑ d ∈ s.prodPrimes.divisors, if r ∣ d then s.nu d * w d else 0) =
        (μ r : ℝ) * s.selbergTerms r * z r)
    (p : ℕ) (hp : p.Prime) (hpP : p ∣ s.prodPrimes) (r : ℕ)
    (hr : r ∣ s.prodPrimes / p) :
    (∑ d ∈ (s.prodPrimes / p).divisors,
      if r ∣ d then s.nu d * (w d + w (p * d)) else 0) =
      (μ r : ℝ) * s.selbergTerms r * (z r - z (p * r)) := by
  have hmul : p * (s.prodPrimes / p) = s.prodPrimes := Nat.mul_div_cancel' hpP
  have hcop : p.Coprime r := by
    have hcopQ : p.Coprime (s.prodPrimes / p) := by
      apply Nat.coprime_of_squarefree_mul
      rw [hmul]
      exact s.prodPrimes_squarefree
    exact hcopQ.coprime_dvd_right hr
  have hprP : p * r ∣ s.prodPrimes := by
    rw [← hmul]
    exact Nat.mul_dvd_mul_left p hr
  have hrP := hr.trans (Nat.div_dvd_of_dvd hpP)
  rw [selberg_prime_removed_forward_split s w p hp hpP r hr,
    hforward r hrP, hforward (p * r) hprP]
  have hmu : (μ (p * r) : ℝ) = -(μ r : ℝ) := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      ArithmeticFunction.moebius_apply_prime hp]
    push_cast
    ring
  have hg : (1 / s.nu p - 1) * s.selbergTerms p = 1 := by
    rw [BoundingSieve.selbergTerms_apply, hp.primeFactors, Finset.prod_singleton]
    have hnu := BoundingSieve.nu_ne_zero (s := s) hpP
    have hdiff : 1 - s.nu p ≠ 0 := (sub_pos.mpr (s.nu_lt_one_of_prime p hp hpP)).ne'
    field_simp
  rw [hmu, BoundingSieve.selbergTerms_isMultiplicative.map_mul_of_coprime hcop]
  calc
    _ = (μ r : ℝ) * s.selbergTerms r * z r -
        ((1 / s.nu p - 1) * s.selbergTerms p) *
          (μ r : ℝ) * s.selbergTerms r * z (p * r) := by ring
    _ = _ := by rw [hg]; ring

theorem selberg_prime_removed_diagonal (s : BoundingSieve) (w z : ℕ → ℝ)
    (hforward : ∀ r, r ∣ s.prodPrimes →
      (∑ d ∈ s.prodPrimes.divisors, if r ∣ d then s.nu d * w d else 0) =
        (μ r : ℝ) * s.selbergTerms r * z r)
    (p : ℕ) (hp : p.Prime) (hpP : p ∣ s.prodPrimes) :
    (removeSievePrime s p hpP).mainSum
      (BoundingSieve.lambdaSquared (fun d => w d + w (p * d))) =
      ∑ r ∈ (s.prodPrimes / p).divisors,
        s.selbergTerms r * (z r - z (p * r)) ^ 2 := by
  rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  change (∑ r ∈ (s.prodPrimes / p).divisors, (s.selbergTerms r)⁻¹ *
    (∑ d ∈ (s.prodPrimes / p).divisors,
      if r ∣ d then s.nu d * (w d + w (p * d)) else 0) ^ 2) = _
  apply Finset.sum_congr rfl
  intro r hr
  have hrQ := Nat.dvd_of_mem_divisors hr
  have hrP := hrQ.trans (Nat.div_dvd_of_dvd hpP)
  have hsq := s.prodPrimes_squarefree.squarefree_of_dvd hrP
  have hmu : (μ r : ℝ) ^ 2 = 1 := by
    exact_mod_cast (BoundedGaps.Maynard.squarefree_iff_moebius_sq_eq_one r).mp hsq
  have hg := (BoundingSieve.selbergTerms_pos (s := s) hrP).ne'
  rw [selberg_prime_removed_forward s w z hforward p hp hpP r hrQ,
    mul_pow, mul_pow, hmu]
  field_simp

theorem scalarSelberg_semiprime_prime_diagonal (s t : BoundingSieve)
    (hP : t.prodPrimes = s.prodPrimes)
    (hs : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (3 : ℝ) / p)
    (ht : ∀ p, p.Prime → p ∣ s.prodPrimes → t.nu p = (2 : ℝ) / ((p : ℝ) - 1))
    (y : ℕ → ℝ) (p : ℕ) (hp : p.Prime) (hpP : p ∣ t.prodPrimes) :
    (removeSievePrime t p hpP).mainSum
      (BoundingSieve.lambdaSquared (fun d =>
        scalarSelbergCoefficient s y d + scalarSelbergCoefficient s y (p * d))) =
      ∑ r ∈ (s.prodPrimes / p).divisors, semiprimeSelbergWeight 3 r *
        (scalarSemiprimeTransform s.prodPrimes y r -
          scalarSemiprimeTransform s.prodPrimes y (p * r)) ^ 2 := by
  have hforward : ∀ r, r ∣ t.prodPrimes →
      (∑ d ∈ t.prodPrimes.divisors,
        if r ∣ d then t.nu d * scalarSelbergCoefficient s y d else 0) =
        (μ r : ℝ) * t.selbergTerms r * scalarSemiprimeTransform s.prodPrimes y r := by
    intro r _
    rw [hP]
    exact scalarSelberg_semiprime_forward s t hP hs ht y r
  rw [selberg_prime_removed_diagonal t (scalarSelbergCoefficient s y)
    (scalarSemiprimeTransform s.prodPrimes y) hforward p hp hpP, hP]
  apply Finset.sum_congr rfl
  intro r hr
  have hrT : r ∣ t.prodPrimes := by
    rw [hP]
    exact (Nat.dvd_of_mem_divisors hr).trans (Nat.div_dvd_of_dvd (hP ▸ hpP))
  have ht' : ∀ q, q.Prime → q ∣ t.prodPrimes →
      t.nu q = ((3 : ℝ) - 1) / ((q : ℝ) - 1) := by
    intro q hq hqT
    norm_num only
    exact ht q hq (hP ▸ hqT)
  rw [selbergTerms_eq_semiprimeWeight t 3 ht' r hrT]

theorem scalarSelberg_semiprime_kernel_diagonal (s t : BoundingSieve)
    (hP : t.prodPrimes = s.prodPrimes)
    (hs : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (3 : ℝ) / p)
    (ht : ∀ p, p.Prime → p ∣ s.prodPrimes → t.nu p = (2 : ℝ) / ((p : ℝ) - 1))
    (y : ℕ → ℝ) (p : ℕ) (hp : p.Prime) (hpP : p ∣ t.prodPrimes) :
    scalarPrimeRemovedKernel t p (scalarSelbergCoefficient s y) =
      ∑ r ∈ (s.prodPrimes / p).divisors, semiprimeSelbergWeight 3 r *
        (scalarSemiprimeTransform s.prodPrimes y r -
          scalarSemiprimeTransform s.prodPrimes y (p * r)) ^ 2 := by
  rw [scalarPrimeRemovedKernel_eq_collapsed t p hp hpP]
  exact scalarSelberg_semiprime_prime_diagonal s t hP hs ht y p hp hpP

theorem scalarSelberg_semiprime_kernel_diagonal_all_primes (s t : BoundingSieve)
    (hP : t.prodPrimes = s.prodPrimes)
    (hs : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (3 : ℝ) / p)
    (ht : ∀ p, p.Prime → p ∣ s.prodPrimes → t.nu p = (2 : ℝ) / ((p : ℝ) - 1))
    (y : ℕ → ℝ) (p : ℕ) (hp : p.Prime) :
    scalarPrimeRemovedKernel t p (scalarSelbergCoefficient s y) =
      ∑ r ∈ s.prodPrimes.divisors, if p ∣ r then 0 else semiprimeSelbergWeight 3 r *
        (scalarSemiprimeTransform s.prodPrimes y r -
          scalarSemiprimeTransform s.prodPrimes y (p * r)) ^ 2 := by
  by_cases hpP : p ∣ t.prodPrimes
  · rw [scalarSelberg_semiprime_kernel_diagonal s t hP hs ht y p hp hpP,
      divisors_quotient_prime_eq_filter s.prodPrimes p s.prodPrimes_squarefree hp (hP ▸ hpP),
      Finset.sum_filter]
    simp only [ite_not]
  · rw [scalarPrimeRemovedKernel_eq_main_of_not_dvd t p hp hpP,
      scalarSelberg_semiprime_diagonal s t hP hs ht y]
    apply Finset.sum_congr rfl
    intro r hr
    have hnotS : ¬ p ∣ s.prodPrimes := by simpa only [hP] using hpP
    have hnotr : ¬ p ∣ r := fun h => hnotS (h.trans (Nat.dvd_of_mem_divisors hr))
    have hnotpr : ¬ p * r ∣ s.prodPrimes := fun h => hnotS ((dvd_mul_right p r).trans h)
    rw [if_neg hnotr, scalarSemiprimeTransform_eq_zero_of_not_dvd _ y _ hnotpr, sub_zero]

end Erdos964
