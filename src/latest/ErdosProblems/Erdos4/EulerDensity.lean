import ErdosProblems.Erdos4.PrincipalGain
import UnitFractions.ForMathlib.BasicEstimates

/-!
# The Euler factor in the principal lower bound

The fixed small-prime density and the moving prime-window density
multiply to the complete Euler product. The existing proved weak
Mertens upper estimate for its inverse therefore supplies a positive
absolute lower bound after multiplication by the outer logarithm.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos4.EulerDensity

open ArithmeticFibers DivisorCoefficients RestrictedProductNorm

theorem density_primorial_eq (K : ℕ) :
    BoundedGaps.Maynard.coprimeHarmonicDensity (primorial K) =
      ∏ p ∈ K.primesLE, ((p : ℝ) - 1) / p := by
  unfold BoundedGaps.Maynard.coprimeHarmonicDensity
  rw [totient_eq_prod_of_squarefree (squarefree_primorial K), primeFactors_primorial,
    primorial_eq_prod_primesLE, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.cast_sub (Nat.prime_of_mem_primesLE hp).one_le, Nat.cast_one]

theorem window_density_mul_small {K R : ℕ} (hKR : K ≤ R) :
    UnitFourier.unitDensity (fun p : primeWindow K R => (p : ℕ)) *
      BoundedGaps.Maynard.coprimeHarmonicDensity (primorial K) =
      ∏ p ∈ R.primesLE, ((p : ℝ) - 1) / p := by
  rw [density_primorial_eq]
  unfold UnitFourier.unitDensity
  rw [Finset.prod_coe_sort (primeWindow K R) (fun p : ℕ => ((p : ℝ) - 1) / p)]
  have hsmall : R.primesLE.filter (fun p => ¬K < p) = K.primesLE := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE, not_lt]
    constructor
    · rintro ⟨⟨hpR, hp⟩, hpK⟩
      exact ⟨hpK, hp⟩
    · rintro ⟨hpK, hp⟩
      exact ⟨⟨hpK.trans hKR, hp⟩, hpK⟩
  rw [primeWindow, ← hsmall]
  exact Finset.prod_filter_mul_prod_filter_not R.primesLE (fun p => K < p) _

theorem full_density_eq_inverse (R : ℕ) :
    (∏ p ∈ R.primesLE, ((p : ℝ) - 1) / p) = (partial_euler_product R)⁻¹ := by
  have hset : (Finset.Icc 1 R).filter Nat.Prime = R.primesLE := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hp1, hpR⟩, hp⟩
      exact ⟨hpR, hp⟩
    · rintro ⟨hpR, hp⟩
      exact ⟨⟨hp.one_le, hpR⟩, hp⟩
  rw [partial_euler_product, hset, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).ne_zero
  rw [inv_inv]
  field_simp

theorem exists_uniform_density_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ K R : ℕ, K ≤ R → 2 ≤ R →
      c ≤ UnitFourier.unitDensity (fun p : primeWindow K R => (p : ℕ)) *
        BoundedGaps.Maynard.coprimeHarmonicDensity (primorial K) * Real.log R := by
  obtain ⟨C, hC, hupper⟩ := weak_mertens_third_upper_all
  refine ⟨C⁻¹, inv_pos.mpr hC, ?_⟩
  intro K R hKR hR
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR)
  have hprod : 0 < partial_euler_product R := zero_lt_one.trans_le partial_euler_trivial_lower_bound
  have hh : partial_euler_product R ≤ C * Real.log R := by
    simpa only [Nat.floor_natCast, Real.norm_eq_abs, abs_of_pos hprod, abs_of_pos hlog]
      using hupper (R : ℝ) (by exact_mod_cast hR)
  have hinv := one_div_le_one_div_of_le hprod hh
  rw [window_density_mul_small hKR, full_density_eq_inverse]
  have hmul := mul_le_mul_of_nonneg_right hinv hlog.le
  have heq : (1 / (C * Real.log (R : ℝ))) * Real.log R = C⁻¹ := by
    field_simp
  rw [heq] at hmul
  simpa only [one_div] using hmul

/-- Arbitrarily large normalized principal gain for the genuine
product-cutoff coefficients and the true local deletion masks. -/
theorem exists_arbitrary_principal_gain (A : ℝ) :
    ∃ (m : ℝ) (k K₀ : ℕ), 1 ≤ m ∧ 0 < k ∧ k + 2 ≤ K₀ ∧
      ∀ K : ℕ, K₀ ≤ K → ∀ᶠ R : ℕ in atTop, 2 ≤ R ∧
        A * energy (coefficient (k := k) m R (fun p : primeWindow K R => (p : ℕ))) ≤
        ∑ j : Fin k, restrictedForm (fun p : primeWindow K R => (p : ℝ))
          (fun s => ∏ p, LocalCharacterMatrix.deletionMask j (s p))
          (coefficient m R (fun p : primeWindow K R => (p : ℕ)))
          (coefficient m R (fun p : primeWindow K R => (p : ℕ))) := by
  obtain ⟨c, hc, hdensity⟩ := exists_uniform_density_lower
  let M : ℝ := (|A| + 1) / c
  have hM : 0 ≤ M := (div_pos (by positivity) hc).le
  obtain ⟨m, k, K₀, hm, hk, hK₀, hgain⟩ := PrincipalGain.exists_eventual_principal_lower hM
  refine ⟨m, k, K₀, hm, hk, hK₀, ?_⟩
  intro K hK₀K
  filter_upwards [hgain K hK₀K, eventually_ge_atTop K] with R hR hKR
  refine ⟨hR.1, ?_⟩
  let N := energy (coefficient (k := k) m R (fun p : primeWindow K R => (p : ℕ)))
  have hN : 0 ≤ N := energy_nonneg _
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hdensity K R hKR hR.1) hM) hN
  have hMc : M * c = |A| + 1 := by dsimp [M]; field_simp
  have hA := mul_le_mul_of_nonneg_right (le_abs_self A) hN
  rw [hMc] at hh
  have hactual := hR.2
  change _ * N - N ≤ _ at hactual
  nlinarith

end Erdos4.EulerDensity
