import ErdosProblems.Erdos4.FGKMTGrowingTrueGain
import ErdosProblems.Erdos4.FGKMTGrowingCenterLaw
import ErdosProblems.Erdos4.FGKMTSourceLowerBound

/-! The growing principal gain in the normalizations used by the actual Fourier averages. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Filter BoundedGaps.Maynard RestrictedProductNorm

theorem growing_maskedFourierScale_pos (x B : ℕ) (β : ℝ)
    (hR : 1 ≤ growingRadius x) (h : Fin (sieveDimension (growingIndex x)) → ℕ)
    (hadm : ∀ p : ℕ, p.Prime → ∃ b : ZMod p, ∀ i, b + (h i : ZMod p) ≠ 0) :
    0 < maskedFourierScale (growingSmallPrimeValue x B) (growingLargePrimeValue x B)
      β (growingRadius x) (fun l i => (h i : ZMod (growingSmallPrimeValue x B l))) := by
  have hα := smallSieve_density_pos (growingPrecutoff x) B h hadm
  have hE := one_le_rationalCoefficient_energy (k := sieveDimension (growingIndex x))
    β hR (growingLargePrimeValue x B)
  unfold maskedFourierScale
  exact mul_pos
    (div_pos hα (UnitFourier.unitDensity_pos (growingSmallPrimeValue x B)))
    (div_pos (by linarith) (UnitFourier.unitDensity_pos (growingLargePrimeValue x B)))

theorem exists_growing_principal_scale_gain :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in atTop,
      ∀ a : ℝ, a ≤ 1 / 4 → ∀ B : ℕ, (B = 1 ∨ B.Prime) →
        B ≤ exponentialConductorCutoff a x →
        ∀ h : Fin (sieveDimension (growingIndex x)) → ℕ,
        let β := sieveSlope (growingIndex x) (growingRadius x)
        c * (growingIndex x : ℝ) *
          maskedFourierScale (growingSmallPrimeValue x B) (growingLargePrimeValue x B)
            β (growingRadius x) (fun l i => (h i : ZMod (growingSmallPrimeValue x B l))) ≤
          aggregatePrincipalMass (growingSmallPrimeValue x B) (growingLargePrimeValue x B)
            β (growingRadius x) (fun l i => (h i : ZMod (growingSmallPrimeValue x B l))) := by
  obtain ⟨c, hc, hdensity⟩ := exists_window_density_uniform_lower
  refine ⟨c / 12288, by positivity, ?_⟩
  filter_upwards [eventually_growing_true_gain, eventually_growing_pre_le_radius,
    eventually_growingRadius_bounds] with x hgain hDR hR
  intro a ha B hB hBx h
  let β := sieveSlope (growingIndex x) (growingRadius x)
  let F := maskedFourierScale (growingSmallPrimeValue x B) (growingLargePrimeValue x B)
    β (growingRadius x) (fun l i => (h i : ZMod (growingSmallPrimeValue x B l)))
  let A := sieveWindowDensity (growingLargePrimeValue x B) *
    coprimeHarmonicDensity (harmonicModulus (growingPrecutoff x) B) *
      Real.log (growingRadius x : ℝ)
  have hF : 0 ≤ F := maskedFourierScale_nonneg _ _ _ _ _
  have hA : c ≤ A := hdensity (growingPrecutoff x) (growingRadius x) B hDR hR.1 hB
  have hbase := aggregatePrincipalMass_gain (growingSmallPrimeValue x B) (growingLargePrimeValue x B)
    β (growingRadius x) (fun l i => (h i : ZMod (growingSmallPrimeValue x B l)))
    (hgain a ha B hB hBx)
  change (c / 12288) * (growingIndex x : ℝ) * F ≤ _
  calc
    _ = (c * (growingIndex x : ℝ) / 12288) * F := by ring
    _ ≤ (A * (growingIndex x : ℝ) / 12288) * F :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hA (Nat.cast_nonneg _)) (by norm_num)) hF
    _ ≤ _ := hbase

theorem eventually_growing_principal_density_gain :
    ∀ᶠ x : ℕ in atTop, ∀ a : ℝ, a ≤ 1 / 4 → ∀ B : ℕ,
      (B = 1 ∨ B.Prime) → B ≤ exponentialConductorCutoff a x →
      ∀ h : Fin (sieveDimension (growingIndex x)) → ℕ,
      let β := sieveSlope (growingIndex x) (growingRadius x)
      let α := smallProductDensity (growingSmallPrimeValue x B)
        (fun l i => (h i : ZMod (growingSmallPrimeValue x B l)))
      let E := energy (rationalCoefficient (k := sieveDimension (growingIndex x))
        β (growingRadius x) (growingLargePrimeValue x B))
      α * E * Real.log (growingRadius x : ℝ) * (growingIndex x : ℝ) / 24576 ≤
        aggregatePrincipalMass (growingSmallPrimeValue x B) (growingLargePrimeValue x B)
          β (growingRadius x) (fun l i => (h i : ZMod (growingSmallPrimeValue x B l))) := by
  filter_upwards [eventually_growing_true_gain, eventually_growingRadius_bounds] with x hgain hR
  intro a ha B hB hBx h
  let β := sieveSlope (growingIndex x) (growingRadius x)
  let α := smallProductDensity (growingSmallPrimeValue x B)
    (fun l i => (h i : ZMod (growingSmallPrimeValue x B l)))
  let E := energy (rationalCoefficient (k := sieveDimension (growingIndex x))
    β (growingRadius x) (growingLargePrimeValue x B))
  let ρ := sieveWindowDensity (growingSmallPrimeValue x B)
  let Δ := sieveWindowDensity (growingLargePrimeValue x B)
  let H := coprimeHarmonicDensity (harmonicModulus (growingPrecutoff x) B)
  have hρ : 0 < ρ := UnitFourier.unitDensity_pos _
  have hΔ : 0 < Δ := UnitFourier.unitDensity_pos _
  have hα : 0 ≤ α := smallProductDensity_nonneg _ _
  have hE : 0 ≤ E := energy_nonneg _
  have hlog : 0 ≤ Real.log (growingRadius x : ℝ) :=
    (Real.log_pos (by exact_mod_cast hR.1)).le
  have hratio : (1 / 2 : ℝ) ≤ H / ρ := smallSievePrime_density_ratio (growingPrecutoff x) hB
  have hbase := aggregatePrincipalMass_gain (growingSmallPrimeValue x B) (growingLargePrimeValue x B)
    β (growingRadius x) (fun l i => (h i : ZMod (growingSmallPrimeValue x B l)))
    (hgain a ha B hB hBx)
  change _ ≤ aggregatePrincipalMass _ _ β _ _
  apply le_trans _ hbase
  change α * E * Real.log (growingRadius x : ℝ) * (growingIndex x : ℝ) / 24576 ≤
    (Δ * H * Real.log (growingRadius x : ℝ) * (growingIndex x : ℝ) / 12288) *
      ((α / ρ) * (E / Δ))
  have hh := mul_le_mul_of_nonneg_right hratio
    (show 0 ≤ α * E * Real.log (growingRadius x : ℝ) * (growingIndex x : ℝ) by positivity)
  calc
    _ = ((1 / 2 : ℝ) * (α * E * Real.log (growingRadius x : ℝ) * (growingIndex x : ℝ))) /
        12288 := by ring
    _ ≤ ((H / ρ) * (α * E * Real.log (growingRadius x : ℝ) * (growingIndex x : ℝ))) /
        12288 := div_le_div_of_nonneg_right hh (by norm_num)
    _ = _ := by field_simp [hρ.ne', hΔ.ne']

end Erdos4.FGKMT
