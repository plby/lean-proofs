import ErdosProblems.Erdos4.FGKMTNumericalGain

/-! Uniform cancellation of the presieve density against the large-prime window density. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open BoundedGaps.Maynard Classical

theorem prime_density_factor_nonneg {p : ℕ} (hp : p.Prime) :
    0 ≤ ((p : ℝ) - 1) / p := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  exact div_nonneg (sub_nonneg.mpr hp1) (Nat.cast_nonneg p)

theorem prime_density_factor_le_one {p : ℕ} (hp : p.Prime) :
    ((p : ℝ) - 1) / p ≤ 1 := by
  apply (div_le_one (by exact_mod_cast hp.pos)).mpr
  linarith

theorem sieveWindowDensity_eq_prod (W R : ℕ) :
    sieveWindowDensity (sievePrimeValue W R) =
      ∏ p ∈ sievePrimeSet W R, ((p : ℝ) - 1) / p := by
  exact Finset.prod_coe_sort (sievePrimeSet W R) (fun p => ((p : ℝ) - 1) / p)

theorem primorial_density_product (R : ℕ) :
    coprimeHarmonicDensity (primorial R) = ∏ p ∈ Nat.primesLE R, ((p : ℝ) - 1) / p := by
  unfold coprimeHarmonicDensity
  rw [totient_eq_prod_primeFactors_of_squarefree (squarefree_primorial R), primeFactors_primorial,
    primorial_eq_prod_primesLE, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hprime := Nat.prime_of_mem_primesLE hp
  rw [Nat.totient_prime hprime, Nat.cast_sub hprime.one_le, Nat.cast_one]

theorem sieveWindowDensity_mono {W V : ℕ} (hWV : W ∣ V) (R : ℕ) :
    sieveWindowDensity (sievePrimeValue W R) ≤ sieveWindowDensity (sievePrimeValue V R) := by
  rw [sieveWindowDensity_eq_prod, sieveWindowDensity_eq_prod]
  have hsub : sievePrimeSet V R ⊆ sievePrimeSet W R := by
    intro p hp
    have hs := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hs.1, hs.2.of_dvd_right hWV⟩
  apply Finset.prod_le_prod_of_subset_of_le_one hsub
  · intro p hp
    exact prime_density_factor_nonneg (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1)
  · intro p hp _
    exact prime_density_factor_le_one (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1)

theorem primorial_window_density_cancel {D R : ℕ} (hDR : D ≤ R) :
    sieveWindowDensity (sievePrimeValue (primorial D) R) * coprimeHarmonicDensity (primorial D) =
      coprimeHarmonicDensity (primorial R) := by
  have hlow : (Nat.primesLE R).filter (fun p => ¬p.Coprime (primorial D)) = Nat.primesLE D := by
    ext p
    constructor
    · intro hp
      have hs := Finset.mem_filter.mp hp
      have hprime := Nat.prime_of_mem_primesLE hs.1
      have hdiv : p ∣ primorial D := by
        simpa only [hprime.coprime_iff_not_dvd, not_not] using hs.2
      exact Nat.mem_primesLE.mpr ⟨hprime.dvd_primorial_iff.mp hdiv, hprime⟩
    · intro hp
      have hs := Nat.mem_primesLE.mp hp
      refine Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hs.1.trans hDR, hs.2⟩, ?_⟩
      rw [hs.2.coprime_iff_not_dvd, not_not]
      exact hs.2.dvd_primorial_iff.mpr hs.1
  rw [sieveWindowDensity_eq_prod, primorial_density_product, primorial_density_product, ← hlow]
  exact Finset.prod_filter_mul_prod_filter_not (Nat.primesLE R)
    (fun p => p.Coprime (primorial D)) (fun p => ((p : ℝ) - 1) / p)

theorem harmonic_window_density_lower {D R B : ℕ} (hDR : D ≤ R) (hB : B = 1 ∨ B.Prime) :
    coprimeHarmonicDensity (primorial R) / 2 ≤
      sieveWindowDensity (sievePrimeValue (harmonicModulus D B) R) *
        coprimeHarmonicDensity (harmonicModulus D B) := by
  have hδ := sieveWindowDensity_mono (primorial_dvd_harmonicModulus D B) R
  have hρ := harmonicModulus_density_lower D hB
  have hh := mul_le_mul hδ hρ (div_nonneg (harmonicDensity_nonneg (primorial D)) (by norm_num))
    (sieveWindowDensity_nonneg (sievePrimeValue (harmonicModulus D B) R)
      (fun p => (sievePrimeValue_prime _ _ p).one_le))
  rwa [← mul_div_assoc, primorial_window_density_cancel hDR] at hh

theorem exists_window_density_uniform_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ D R B : ℕ, D ≤ R → 2 ≤ R → (B = 1 ∨ B.Prime) →
      c ≤ sieveWindowDensity (sievePrimeValue (harmonicModulus D B) R) *
        coprimeHarmonicDensity (harmonicModulus D B) * Real.log (R : ℝ) := by
  obtain ⟨c, hc, hbound⟩ := exists_harmonicModulus_density_lower
  refine ⟨c / 2, by positivity, ?_⟩
  intro D R B hDR hR hB
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR)
  have hρ := hbound R 1 hR (Or.inl rfl)
  simp only [harmonicModulus, one_dvd, if_true] at hρ
  have hscalar := (div_le_iff₀ hlog).mp hρ
  have hmul := mul_le_mul_of_nonneg_right (harmonic_window_density_lower hDR hB) hlog.le
  linarith

end Erdos4.FGKMT
