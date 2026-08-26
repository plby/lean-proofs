import ErdosProblems.Erdos4.WindowNormalization

/-!
# Asymptotic probability bounds without a divisor-function estimate

At the cutoffs `R = t⁵` and `Y ≥ t⁵⁰`, the elementary `R⁴` bound suffices.
The actual normalization is positive for every source prime above `R`,
and every probability atom is at most a fixed constant times `t⁻³⁰`.
All assertions are uniform in the upper interval endpoint and source.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos4.NormalizationAsymptotic

open ArithmeticFibers DivisorCoefficients AffineNormalization WindowNormalization

theorem eventually_power_error_small {W : ℕ} (hW : 0 < W) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop, 2 ≤ t ∧ ∀ Y : ℕ, t ^ 50 ≤ Y →
      Nat.totient W * Real.exp 1 ^ 2 * ((t ^ 5 : ℕ) : ℝ) ^ 4 ≤
        ε * BoundedGaps.Maynard.coprimeHarmonicDensity W * Y := by
  let ρ := BoundedGaps.Maynard.coprimeHarmonicDensity W
  have hρ : 0 < ρ := FiberAsymptotic.density_pos hW
  have hlim : Tendsto (fun t : ℕ => (t : ℝ) ^ 30) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (30 : ℕ) ≠ 0)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlarge : ∀ᶠ t : ℕ in atTop,
      Nat.totient W * Real.exp 1 ^ 2 / (ε * ρ) ≤ (t : ℝ) ^ 30 :=
    hlim.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop 2, hlarge] with t ht hlarge
  refine ⟨ht, ?_⟩
  intro Y hY
  have hconst := (div_le_iff₀ (mul_pos hε hρ)).mp hlarge
  have hYreal : (t : ℝ) ^ 50 ≤ Y := by exact_mod_cast hY
  calc
    _ = (Nat.totient W * Real.exp 1 ^ 2) * (t : ℝ) ^ 20 := by
      rw [Nat.cast_pow, ← pow_mul]
    _ ≤ ((t : ℝ) ^ 30 * (ε * ρ)) * (t : ℝ) ^ 20 :=
      mul_le_mul_of_nonneg_right hconst (by positivity)
    _ = (ε * ρ) * (t : ℝ) ^ 50 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hYreal (mul_pos hε hρ).le

theorem power_atom_bound {t Y : ℕ} (ht : 0 < t) (hY : t ^ 50 ≤ Y)
    {ρ : ℝ} (hρ : 0 < ρ) :
    2 * (Real.exp 1 ^ 2 * ((t ^ 5 : ℕ) : ℝ) ^ 4) / (ρ * Y) ≤
      (2 * Real.exp 1 ^ 2 / ρ) / (t : ℝ) ^ 30 := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hYreal : (t : ℝ) ^ 50 ≤ Y := by exact_mod_cast hY
  calc
    _ ≤ 2 * (Real.exp 1 ^ 2 * ((t ^ 5 : ℕ) : ℝ) ^ 4) / (ρ * (t : ℝ) ^ 50) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hYreal hρ.le)
    _ = _ := by
      rw [Nat.cast_pow]
      field_simp

/-- The actual weights become probability distributions, with uniformly
small atoms. No hypothesis about a missing normalization theorem remains. -/
theorem exists_eventual_probability_bounds {m : ℝ} (hm : 1 ≤ m) (k : ℕ) :
    ∃ K₀ : ℕ, k + 2 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K →
      ∀ᶠ t : ℕ in atTop, 2 ≤ t ∧ ∀ Y : ℕ, t ^ 50 ≤ Y →
        ∀ p : ℕ, p.Prime → t ^ 5 < p →
          0 < normalizer (fun l : primeWindow K (t ^ 5) => (l : ℕ)) m (t ^ 5) Y
            (primorial K) (AffineWeights.shift K : Fin k → ℕ) p ∧
          normalizer (fun l : primeWindow K (t ^ 5) => (l : ℕ)) m (t ^ 5) Y
            (primorial K) (AffineWeights.shift K : Fin k → ℕ) p ≤
              2 * BoundedGaps.Maynard.coprimeHarmonicDensity (primorial K) * Y *
                RestrictedProductNorm.energy (coefficient (k := k) m (t ^ 5)
                  (fun l : primeWindow K (t ^ 5) => (l : ℕ))) ∧
          (∑ n ∈ Finset.Icc 1 Y, probability (fun l : primeWindow K (t ^ 5) => (l : ℕ))
            m (t ^ 5) Y (primorial K) (AffineWeights.shift K : Fin k → ℕ) p n) = 1 ∧
          ∀ n : ℕ, probability (fun l : primeWindow K (t ^ 5) => (l : ℕ)) m (t ^ 5) Y
            (primorial K) (AffineWeights.shift K : Fin k → ℕ) p n ≤
              (2 * Real.exp 1 ^ 2 / BoundedGaps.Maynard.coprimeHarmonicDensity (primorial K)) /
                (t : ℝ) ^ 30 := by
  obtain ⟨K₀, hK₀, hraw⟩ := exists_uniform_normalization hm k
  refine ⟨K₀, hK₀, ?_⟩
  intro K hK
  filter_upwards [eventually_power_error_small (primorial_pos K)
    (by norm_num : (0 : ℝ) < 1 / 2)] with t ht
  refine ⟨ht.1, ?_⟩
  intro Y hY p hp hpR
  let ell : primeWindow K (t ^ 5) → ℕ := fun l => l
  have htpos : 0 < t := by omega
  have hR : 2 ≤ t ^ 5 := by
    have hh : t ≤ t ^ 5 := Nat.le_pow (by omega : 0 < (5 : ℕ))
    omega
  have hYpos : 0 < Y := lt_of_lt_of_le (pow_pos htpos 50) hY
  have hfinite := hraw K hK (t ^ 5) hR Y p hp hpR
  have herr : |normalizer ell m (t ^ 5) Y (primorial K) (AffineWeights.shift K : Fin k → ℕ) p -
      BoundedGaps.Maynard.coprimeHarmonicDensity (primorial K) * Y *
        RestrictedProductNorm.energy (coefficient (k := k) m (t ^ 5) ell)| ≤
      BoundedGaps.Maynard.coprimeHarmonicDensity (primorial K) * Y / 2 := by
    exact (hfinite.1.trans (ht.2 Y hY)).trans_eq (by ring)
  have hb := normalizer_bounds ell (primorial_pos K) hYpos (by omega : 1 ≤ t ^ 5)
    (AffineWeights.shift K) p herr
  refine ⟨hb.2.1, hb.2.2, sum_probability ell m (t ^ 5) Y (primorial K)
    (AffineWeights.shift K) p hb.2.1.ne', ?_⟩
  intro n
  exact (probability_le ell (primorial_pos K) hYpos (AffineWeights.shift K) p n hb.1
    (hfinite.2 n)).trans (power_atom_bound htpos hY (FiberAsymptotic.density_pos (primorial_pos K)))

end Erdos4.NormalizationAsymptotic
