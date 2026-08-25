import ErdosProblems.Erdos964.SelbergChangeDensity
import BoundedGaps.Maynard.MaynardLambdaMajorant

/-!
# Logarithmic bounds for the scalar coefficients

These coarse bounds suffice for the weighted distribution errors. The
radius is not allowed to contribute a positive power to the coefficient
bound: arbitrary logarithmic savings can absorb a fixed logarithmic power.
-/

namespace Erdos964

open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.omega
open BoundedGaps.Maynard

noncomputable def scalarSelbergMass (s : BoundingSieve) (R : ℕ) : ℝ :=
  ∑ u ∈ Finset.Icc 1 R, if u ∣ s.prodPrimes then s.selbergTerms u else 0

theorem scalarSelbergMass_nonneg (s : BoundingSieve) (R : ℕ) :
    0 ≤ scalarSelbergMass s R := by
  apply Finset.sum_nonneg
  intro u _
  split_ifs with hu
  · exact (BoundingSieve.selbergTerms_pos hu).le
  · exact le_refl 0

theorem sum_selbergTerms_subset_le_mass (s : BoundingSieve) (R : ℕ) (D : Finset ℕ)
    (hD : ∀ u ∈ D, u ∈ Finset.Icc 1 R ∧ u ∣ s.prodPrimes) :
    (∑ u ∈ D, s.selbergTerms u) ≤ scalarSelbergMass s R := by
  classical
  calc
    _ = ∑ u ∈ D, if u ∣ s.prodPrimes then s.selbergTerms u else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [if_pos (hD u hu).2]
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (fun u hu => (hD u hu).1)
      intro u _ _
      split_ifs with hu
      · exact (BoundingSieve.selbergTerms_pos hu).le
      · exact le_refl 0

theorem selbergTerms_div_nu_le_mass (s : BoundingSieve) (R d : ℕ)
    (hd : d ∣ s.prodPrimes) (hdR : d ≤ R) :
    s.selbergTerms d / s.nu d ≤ scalarSelbergMass s R := by
  have h := BoundingSieve.sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv
    (s := s) hd
  rw [← Finset.sum_filter,
    Nat.divisors_filter_dvd_of_dvd s.prodPrimes_squarefree.ne_zero hd] at h
  rw [div_eq_mul_inv, ← h]
  apply sum_selbergTerms_subset_le_mass
  intro u hu
  exact ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hu,
    (Nat.le_of_dvd (Nat.pos_of_ne_zero
      (s.prodPrimes_squarefree.squarefree_of_dvd hd).ne_zero)
      (Nat.dvd_of_mem_divisors hu)).trans hdR⟩,
    (Nat.dvd_of_mem_divisors hu).trans hd⟩

theorem scalarSelbergCoefficient_quotient (s : BoundingSieve) (y : ℕ → ℝ)
    (d : ℕ) (hd : d ∣ s.prodPrimes) :
    scalarSelbergCoefficient s y d = (μ d : ℝ) * (s.selbergTerms d / s.nu d) *
      ∑ m ∈ (s.prodPrimes / d).divisors, s.selbergTerms m * y (d * m) := by
  have hmul : d * (s.prodPrimes / d) = s.prodPrimes := Nat.mul_div_cancel' hd
  have hcop : d.Coprime (s.prodPrimes / d) := by
    apply Nat.coprime_of_squarefree_mul
    rw [hmul]
    exact s.prodPrimes_squarefree
  have hsum := sum_upper_divisors_reindex s.prodPrimes d s.prodPrimes
    s.prodPrimes_squarefree.ne_zero hd (dvd_refl _)
    (fun r => s.selbergTerms r * y r)
  have hleft : (∑ r ∈ s.prodPrimes.divisors,
      if d ∣ r ∧ r ∣ s.prodPrimes then s.selbergTerms r * y r else 0) =
      ∑ r ∈ s.prodPrimes.divisors, if d ∣ r then s.selbergTerms r * y r else 0 := by
    apply Finset.sum_congr rfl
    intro r hr
    simp only [Nat.dvd_of_mem_divisors hr, and_true]
  rw [hleft] at hsum
  unfold scalarSelbergCoefficient
  rw [hsum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [BoundingSieve.selbergTerms_isMultiplicative.map_mul_of_coprime
    (hcop.coprime_dvd_right (Nat.dvd_of_mem_divisors hm))]
  ring

theorem scalarSelbergCoefficient_le_mass_sq (s : BoundingSieve) (R : ℕ)
    (y : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hy : ∀ u, |y u| ≤ B)
    (hcut : ∀ u, R ≤ u → y u = 0) (d : ℕ) :
    |scalarSelbergCoefficient s y d| ≤ B * (scalarSelbergMass s R) ^ 2 := by
  by_cases hd : d ∣ s.prodPrimes
  · by_cases hdR : R ≤ d
    · rw [scalarSelbergCoefficient_eq_zero_of_radius s y R d hcut hdR, abs_zero]
      positivity
    · have hdlt : d < R := Nat.lt_of_not_ge hdR
      have hdsq := s.prodPrimes_squarefree.squarefree_of_dvd hd
      have hdpos : 0 < d := Nat.pos_of_ne_zero hdsq.ne_zero
      have hmuabs : |(μ d : ℝ)| = 1 := by
        have hmusq : (μ d : ℝ) ^ 2 = 1 := by
          exact_mod_cast (squarefree_iff_moebius_sq_eq_one d).mp hdsq
        nlinarith [sq_abs (μ d : ℝ), abs_nonneg (μ d : ℝ)]
      have hquot : |∑ m ∈ (s.prodPrimes / d).divisors,
          s.selbergTerms m * y (d * m)| ≤ B * scalarSelbergMass s R := by
        calc
          _ ≤ ∑ m ∈ (s.prodPrimes / d).divisors,
              |s.selbergTerms m * y (d * m)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ m ∈ (s.prodPrimes / d).divisors,
              if m ≤ R then B * s.selbergTerms m else 0 := by
            apply Finset.sum_le_sum
            intro m hm
            have hmP := (Nat.dvd_of_mem_divisors hm).trans (Nat.div_dvd_of_dvd hd)
            by_cases hmR : m ≤ R
            · rw [if_pos hmR, abs_mul, abs_of_pos (BoundingSieve.selbergTerms_pos hmP)]
              simpa only [mul_comm B] using
                mul_le_mul_of_nonneg_left (hy (d * m))
                  (BoundingSieve.selbergTerms_pos hmP).le
            · have hRdm : R ≤ d * m := by nlinarith
              rw [if_neg hmR, hcut (d * m) hRdm, mul_zero, abs_zero]
          _ = B * ∑ m ∈ (s.prodPrimes / d).divisors.filter (fun m => m ≤ R),
              s.selbergTerms m := by
            simp only [Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
          _ ≤ B * scalarSelbergMass s R := by
            apply mul_le_mul_of_nonneg_left _ hB
            apply sum_selbergTerms_subset_le_mass
            intro m hm
            obtain ⟨hm, hmR⟩ := Finset.mem_filter.mp hm
            exact ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hm, hmR⟩,
              (Nat.dvd_of_mem_divisors hm).trans (Nat.div_dvd_of_dvd hd)⟩
      have hfactorpos : 0 ≤ s.selbergTerms d / s.nu d :=
        div_nonneg (BoundingSieve.selbergTerms_pos hd).le
          (BoundingSieve.nu_pos_of_dvd_prodPrimes hd).le
      rw [scalarSelbergCoefficient_quotient s y d hd, abs_mul, abs_mul,
        hmuabs, one_mul, abs_of_nonneg hfactorpos]
      calc
        _ ≤ (s.selbergTerms d / s.nu d) * (B * scalarSelbergMass s R) :=
          mul_le_mul_of_nonneg_left hquot hfactorpos
        _ ≤ scalarSelbergMass s R * (B * scalarSelbergMass s R) :=
          mul_le_mul_of_nonneg_right (selbergTerms_div_nu_le_mass s R d hd hdlt.le)
            (mul_nonneg hB (scalarSelbergMass_nonneg s R))
        _ = _ := by ring
  · rw [scalarSelbergCoefficient_eq_zero_of_not_dvd s y d hd, abs_zero]
    positivity

theorem dimension_three_selbergTerms_le_tau (s : BoundingSieve)
    (hs : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (3 : ℝ) / p)
    (u : ℕ) (hu : u ∣ s.prodPrimes) :
    s.selbergTerms u ≤ ((9 ^ ω u : ℕ) : ℝ) / Nat.totient u := by
  have husq := s.prodPrimes_squarefree.squarefree_of_dvd hu
  have hrhs : (∏ p ∈ u.primeFactors, (9 : ℝ) / ((p : ℝ) - 1)) =
      ((9 ^ ω u : ℕ) : ℝ) / Nat.totient u := by
    rw [Finset.prod_div_distrib, Finset.prod_const,
      squarefree_totient_real_product u husq, Nat.cast_pow, omega_eq_card_primeFactors]
    norm_num
  rw [← hrhs, selbergTerms_eq_dimensionWeight s 3 hs u hu,
    dimensionSelbergWeight_apply 3 u husq.ne_zero]
  apply Finset.prod_le_prod
  · intro p hp
    have hpprime := Nat.prime_of_mem_primeFactors hp
    have hpP := (Nat.dvd_of_mem_primeFactors hp).trans hu
    have hnu := s.nu_lt_one_of_prime p hpprime hpP
    rw [hs p hpprime hpP] at hnu
    have h3p := (div_lt_one (by exact_mod_cast hpprime.pos)).mp hnu
    exact div_nonneg (by norm_num) (by norm_num only [Nat.cast_ofNat]; linarith)
  · intro p hp
    have hpprime := Nat.prime_of_mem_primeFactors hp
    have hpP := (Nat.dvd_of_mem_primeFactors hp).trans hu
    have hnu := s.nu_lt_one_of_prime p hpprime hpP
    rw [hs p hpprime hpP] at hnu
    have h3p : (3 : ℝ) < p := (div_lt_one (by exact_mod_cast hpprime.pos)).mp hnu
    have hp4 : (4 : ℝ) ≤ p := by
      have hnat : 3 < p := by exact_mod_cast h3p
      exact_mod_cast (show 4 ≤ p by omega)
    norm_num only [Nat.cast_ofNat]
    apply (div_le_div_iff₀ (by linarith : (0 : ℝ) < p - 3)
      (by linarith : (0 : ℝ) < p - 1)).mpr
    nlinarith

theorem scalarSelbergMass_le_log (s : BoundingSieve)
    (hs : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (3 : ℝ) / p) (R : ℕ) :
    scalarSelbergMass s R ≤ (1 + Real.log R) ^ 162 := by
  calc
    _ ≤ squarefreeTauFirstMean 9 R := by
      unfold scalarSelbergMass squarefreeTauFirstMean
      apply Finset.sum_le_sum
      intro u _
      by_cases hu : u ∣ s.prodPrimes
      · rw [if_pos hu, if_pos (s.prodPrimes_squarefree.squarefree_of_dvd hu)]
        exact dimension_three_selbergTerms_le_tau s hs u hu
      · rw [if_neg hu]
        split_ifs <;> positivity
    _ ≤ _ := by
      simpa using (squarefreeTauFirstMean_le_one_add_log (k := 9) (Q := R) (by norm_num))

theorem abs_scalarSelbergCoefficient_le_log (s : BoundingSieve)
    (hs : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (3 : ℝ) / p)
    (R : ℕ) (y : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hy : ∀ u, |y u| ≤ B)
    (hcut : ∀ u, R ≤ u → y u = 0) (d : ℕ) :
    |scalarSelbergCoefficient s y d| ≤ B * (1 + Real.log R) ^ 324 := by
  calc
    _ ≤ B * (scalarSelbergMass s R) ^ 2 :=
      scalarSelbergCoefficient_le_mass_sq s R y B hB hy hcut d
    _ ≤ B * ((1 + Real.log R) ^ 162) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact pow_le_pow_left₀ (scalarSelbergMass_nonneg s R) (scalarSelbergMass_le_log s hs R) 2
    _ = _ := by rw [← pow_mul]

end Erdos964
