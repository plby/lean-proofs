import ErdosProblems.Erdos964.AffineSemiprimeCountError
import ErdosProblems.Erdos964.SelbergPrimeRemoval

/-!
# Identifying the second arithmetic main term with the scalar kernel

The restricted root count is `2^ω(u)`. After factoring the fixed leading
coefficient from the totient, the main term is exactly the density-changed
prime-removal kernel already diagonalized in `SelbergPrimeRemoval`.
-/

namespace Erdos964

open scoped BigOperators

theorem affineSemiprimeCountMain_eq_prime_sum (A B : Fin 3 → ℕ) (j : Fin 3)
    (P Q : Finset ℕ) (x y u : ℕ) (hP : ∀ p ∈ P, p.Prime) :
    affineSemiprimeCountMain A B j P Q x y u =
      ∑ p ∈ P, ((affineCoprimeProductRoots A B j (u / Nat.gcd u p)).card : ℝ) *
        ((primeSlice Q p x y).card / (A j * (u / Nat.gcd u p)).totient) := by
  let f (p : ℕ) : ℝ :=
    (affineCoprimeProductRoots A B j (u / Nat.gcd u p)).card *
      ((primeSlice Q p x y).card / (A j * (u / Nat.gcd u p)).totient)
  have hsplit := Finset.sum_filter_add_sum_filter_not P (fun p => ¬ p ∣ u) f
  simp only [not_not] at hsplit
  rw [← hsplit]
  unfold affineSemiprimeCountMain
  rw [Finset.sum_div, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hcop := ((hP p hp'.1).coprime_iff_not_dvd.mpr hp'.2).symm
    simp only [f, hcop.gcd_eq_one, Nat.div_one]
  · apply Finset.sum_congr rfl
    intro p hp
    simp only [f, Nat.gcd_eq_right (Finset.mem_filter.mp hp).2]

theorem selberg_nu_eq_semiprime_density (s : BoundingSieve)
    (hdensity : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (2 : ℝ) / ((p : ℝ) - 1))
    (u : ℕ) (hu : u ∣ s.prodPrimes) :
    s.nu u = (2 : ℝ) ^ u.primeFactors.card / u.totient := by
  rw [← BoundingSieve.prod_primeFactors_nu hu,
    squarefree_totient_real_product u (s.prodPrimes_squarefree.squarefree_of_dvd hu)]
  calc
    _ = ∏ p ∈ u.primeFactors, (2 : ℝ) / ((p : ℝ) - 1) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact hdensity p (Nat.prime_of_mem_primeFactors hp)
        ((Nat.dvd_of_mem_primeFactors hp).trans hu)
    _ = _ := by rw [Finset.prod_div_distrib, Finset.prod_const]

theorem affineSemiprimeCountMain_eq_density_sum (A B : Fin 3 → ℕ) (j : Fin 3)
    (P Q : Finset ℕ) (x y u : ℕ) (hP : ∀ p ∈ P, p.Prime)
    (s : BoundingSieve) (hu : u ∣ s.prodPrimes) (hcop : s.prodPrimes.Coprime (A j))
    (hdensity : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (2 : ℝ) / ((p : ℝ) - 1))
    (hroots : ∀ q, q ∣ s.prodPrimes →
      (affineCoprimeProductRoots A B j q).card = 2 ^ q.primeFactors.card) :
    affineSemiprimeCountMain A B j P Q x y u =
      1 / (A j).totient * ∑ p ∈ P,
        (primeSlice Q p x y).card * s.nu (u / Nat.gcd u p) := by
  rw [affineSemiprimeCountMain_eq_prime_sum A B j P Q x y u hP, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  have hdiv : u / Nat.gcd u p ∣ s.prodPrimes :=
    (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left u p)).trans hu
  have hcopq := (hcop.coprime_dvd_left hdiv).symm
  rw [hroots _ hdiv, Nat.cast_pow, Nat.cast_ofNat,
    Nat.totient_mul hcopq, Nat.cast_mul, selberg_nu_eq_semiprime_density s hdensity _ hdiv]
  ring

theorem normalized_affineSemiprimeCountMain_eq_density_sum (A B : Fin 3 → ℕ)
    (j : Fin 3) (v : ℕ) (P Q : Finset ℕ) (x y u : ℕ) (hP : ∀ p ∈ P, p.Prime)
    (s : BoundingSieve) (hu : u ∣ s.prodPrimes)
    (hcop : s.prodPrimes.Coprime (affineNormalizationModulus A B))
    (hdensity : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (2 : ℝ) / ((p : ℝ) - 1)) :
    affineSemiprimeCountMain (fun i => A i * affineNormalizationModulus A B)
      (fun i => A i * v + B i) j P Q x y u =
      1 / (A j * affineNormalizationModulus A B).totient * ∑ p ∈ P,
        (primeSlice Q p x y).card * s.nu (u / Nat.gcd u p) := by
  apply affineSemiprimeCountMain_eq_density_sum _ _ j P Q x y u hP s hu
    ((hcop.coprime_dvd_right (affine_leading_dvd_normalization A B j)).mul_right hcop) hdensity
  intro q hq
  exact normalized_affineCoprimeProductRoots_card_squarefree A B v q j
    (s.prodPrimes_squarefree.squarefree_of_dvd hq) (hcop.coprime_dvd_left hq)

theorem scalarPrimeRemovedKernel_eq_gcd_kernel (s : BoundingSieve) (p : ℕ)
    (hp : 0 < p) (w : ℕ → ℝ) :
    scalarPrimeRemovedKernel s p w =
      ∑ d ∈ s.prodPrimes.divisors, ∑ e ∈ s.prodPrimes.divisors,
        s.nu (Nat.lcm d e / Nat.gcd (Nat.lcm d e) p) * (w d * w e) := by
  rw [scalarPrimeRemovedKernel_eq_paper_kernel s p hp w]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro e _
  have hstrip (n : ℕ) : p * (n / Nat.gcd n p) = Nat.lcm n p := by
    rw [← Nat.mul_div_assoc p (Nat.gcd_dvd_left n p), Nat.mul_comm p n,
      Nat.lcm_eq_mul_div]
  rw [← hstrip (Nat.lcm d e), Nat.mul_div_cancel_left _ hp]

theorem scalar_prime_sum_pair_kernel (s : BoundingSieve) (P : Finset ℕ)
    (hP : ∀ p ∈ P, 0 < p) (c w : ℕ → ℝ) :
    (∑ d ∈ s.prodPrimes.divisors, ∑ e ∈ s.prodPrimes.divisors,
      (∑ p ∈ P, c p * s.nu (Nat.lcm d e / Nat.gcd (Nat.lcm d e) p)) * (w d * w e)) =
      ∑ p ∈ P, c p * scalarPrimeRemovedKernel s p w := by
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.sum_comm (t := P)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [scalarPrimeRemovedKernel_eq_gcd_kernel s p (hP p hp) w, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem normalized_scalar_second_main_eq_kernel (A B : Fin 3 → ℕ)
    (j : Fin 3) (v : ℕ) (P Q : Finset ℕ) (x y : ℕ) (hP : ∀ p ∈ P, p.Prime)
    (s : BoundingSieve) (w : ℕ → ℝ)
    (hcop : s.prodPrimes.Coprime (affineNormalizationModulus A B))
    (hdensity : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (2 : ℝ) / ((p : ℝ) - 1)) :
    (∑ d ∈ s.prodPrimes.divisors, ∑ e ∈ s.prodPrimes.divisors,
      affineSemiprimeCountMain (fun i => A i * affineNormalizationModulus A B)
        (fun i => A i * v + B i) j P Q x y (Nat.lcm d e) * (w d * w e)) =
      1 / (A j * affineNormalizationModulus A B).totient *
        ∑ p ∈ P, (primeSlice Q p x y).card * scalarPrimeRemovedKernel s p w := by
  calc
    _ = ∑ d ∈ s.prodPrimes.divisors, ∑ e ∈ s.prodPrimes.divisors,
        (1 / (A j * affineNormalizationModulus A B).totient *
          ∑ p ∈ P, (primeSlice Q p x y).card *
            s.nu (Nat.lcm d e / Nat.gcd (Nat.lcm d e) p)) * (w d * w e) := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      rw [normalized_affineSemiprimeCountMain_eq_density_sum A B j v P Q x y
        (Nat.lcm d e) hP s (Nat.lcm_dvd (Nat.dvd_of_mem_divisors hd)
          (Nat.dvd_of_mem_divisors he)) hcop hdensity]
    _ = 1 / (A j * affineNormalizationModulus A B).totient *
        ∑ d ∈ s.prodPrimes.divisors, ∑ e ∈ s.prodPrimes.divisors,
          (∑ p ∈ P, (primeSlice Q p x y).card *
            s.nu (Nat.lcm d e / Nat.gcd (Nat.lcm d e) p)) * (w d * w e) := by
      symm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = _ := by
      rw [scalar_prime_sum_pair_kernel s P (fun p hp => (hP p hp).pos)]

end Erdos964
