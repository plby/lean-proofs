import ErdosProblems.Erdos4.FGKMTGrowingNormalizationBudget
import ErdosProblems.Erdos4.FGKMTGrowingWindow
import ErdosProblems.Erdos4.FGKMTSieveDivisorLaw
import ErdosProblems.Erdos4.ProductPrimeMeanSquare

/-! Actual growing-dimensional center laws, with no remaining CRT or tail hypotheses. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Filter ProductCharacterEncoding

noncomputable abbrev growingSmallPrimeValue (x B : ℕ) := smallSievePrimeValue (growingPrecutoff x) B

noncomputable abbrev growingLargePrimeValue (x B : ℕ) :=
  sievePrimeValue (harmonicModulus (growingPrecutoff x) B) (growingRadius x)

theorem eventually_growing_center_laws :
    ∀ᶠ x : ℕ in atTop, ∀ a : ℝ, a ≤ 1 / 4 → ∀ B : ℕ,
      (B = 1 ∨ B.Prime) → B ≤ exponentialConductorCutoff a x →
      ∀ h : Fin (sieveDimension (growingIndex x)) → ℕ,
        Function.Injective h → (∀ i, h i ≤ growingPrecutoff x) →
        (∀ p : ℕ, p.Prime → ∃ b : ZMod p, ∀ i, b + (h i : ZMod p) ≠ 0) →
        ∀ Y : ℕ, ∀ hY : 1 ≤ Y, x ≤ Y → ∀ p : ℕ, p.Prime → growingRadius x < p →
        let b := sieveSlope (growingIndex x) (growingRadius x)
        let α := smallProductDensity (growingSmallPrimeValue x B)
          (fun l i => (h i : ZMod (growingSmallPrimeValue x B l)))
        let E := RestrictedProductNorm.energy
          (rationalCoefficient (k := sieveDimension (growingIndex x)) b (growingRadius x)
            (growingLargePrimeValue x B))
        let Z := maskedTranslatedNormalizer (growingSmallPrimeValue x B) (growingLargePrimeValue x B)
          b (growingRadius x) h Y p
        (0 < Z ∧ α * Y * E ≤ Z ∧ Z ≤ 3 * (α * Y * E)) ∧
          ∀ n : TranslatedCenter Y,
            (rationalCenterLaw (growingSmallPrimeValue x B) (growingLargePrimeValue x B)
              b (growingRadius x) h hY p).weight n ≤ (x : ℝ) ^ (-9 / 10 : ℝ) := by
  filter_upwards [eventually_growing_normalization_budget, eventually_growing_weight_numerator,
    eventually_growingRadius_bounds, eventually_growing_pre_le_radius,
    growingIndex_tendsto.eventually (eventually_ge_atTop 1), eventually_ge_atTop 1]
    with x hbudget hnum hR hDR hj hx
  intro a ha B hB hBx h hinj hbound hadm Y hY hXY p hp hRp
  let ell₀ := growingSmallPrimeValue x B
  let ell₁ := growingLargePrimeValue x B
  let b := sieveSlope (growingIndex x) (growingRadius x)
  have hb : 0 ≤ b := (sieveSlope_pos hj hR.1).le
  have hR1 : 1 ≤ growingRadius x := by omega
  have hpre : ∀ q : ℕ, q.Prime → q ≤ growingPrecutoff x →
      q ∣ harmonicModulus (growingPrecutoff x) B :=
    fun q hq hqD => small_prime_dvd_harmonicModulus (growingPrecutoff x) B hq hqD
  have hlarge : ∀ l, Function.Injective (fun i => (h i : ZMod (ell₁ l))) :=
    sievePrimeShifts_injective h hinj hbound hpre
  have hcop₀ : Pairwise (fun l r => (ell₀ l).Coprime (ell₀ r)) :=
    pairwise_coprime_of_prime ell₀ (smallSievePrime_prime (growingPrecutoff x) B)
      (smallSievePrime_injective (growingPrecutoff x) B)
  have hcop₁ : Pairwise (fun l r => (ell₁ l).Coprime (ell₁ r)) :=
    pairwise_coprime_of_prime ell₁
      (sievePrimeValue_prime (harmonicModulus (growingPrecutoff x) B) (growingRadius x))
      (sievePrimeValue_injective (harmonicModulus (growingPrecutoff x) B) (growingRadius x))
  have hmod : modulus ell₀ = smallPresieveModulus (growingPrecutoff x) B :=
    smallSievePrime_product (growingPrecutoff x) B
  have hMdvd : modulus ell₀ ∣ harmonicModulus (growingPrecutoff x) B := by
    rw [hmod]
    exact (smallPresieveModulus_dvd_primorial (growingPrecutoff x) B).trans
      (primorial_dvd_harmonicModulus (growingPrecutoff x) B)
  have hcross : ∀ l, (modulus ell₀).Coprime (ell₁ l) := fun l =>
    (sievePrimeValue_coprime (harmonicModulus (growingPrecutoff x) B)
      (growingRadius x) l).symm.of_dvd_left hMdvd
  have hp₀mod : p.Coprime (modulus ell₀) :=
    ProductPrimeMeanSquare.coprime_modulus_of_prime_gt ell₀ hp
      (fun l => ((smallSievePrime_le (growingPrecutoff x) B l).trans hDR).trans_lt hRp)
  have hp₀ : ∀ l, (p : ZMod (ell₀ l)) ≠ 0 := unitPoint_natCast_ne_zero ell₀ p hp₀mod
  have hp₁ : p.Coprime (modulus ell₁) :=
    ProductPrimeMeanSquare.coprime_modulus_of_prime_gt ell₁ hp
      (fun l => (sievePrimeValue_le (harmonicModulus (growingPrecutoff x) B)
        (growingRadius x) l).trans_lt hRp)
  have hbud : (modulus ell₀ : ℝ) * (Real.exp 1 ^ 2 * (growingRadius x : ℝ) ^ 4) ≤ Y := by
    rw [hmod]
    exact hbudget a ha B hB hBx Y hXY
  have hbounds := maskedTranslatedNormalizer_bounds ell₀ ell₁ hb hR1
    (growing_sievePrime_size x B (growingRadius x))
    (growing_sievePrime_normalization_tail x B (growingRadius x))
    hcop₀ hcop₁ hcross h hlarge Y p hp₀ hp₁ hbud
  have hadm₀ : ∀ l, ∃ z, SmallPrimeGood (fun i => (h i : ZMod (ell₀ l))) z :=
    smallSieveShifts_admissible (growingPrecutoff x) B h hadm
  have hZpos := maskedTranslatedNormalizer_pos_of_lower ell₀ ell₁ b hR1 h hadm₀ hY p hbounds.1
  dsimp only
  refine ⟨⟨hZpos, hbounds.1, hbounds.2⟩, ?_⟩
  intro n
  have hatom := rationalCenterLaw_weight_le_modulus ell₀ ell₁ hb hR1
    (growing_sievePrime_size x B (growingRadius x))
    (growing_sievePrime_normalization_tail x B (growingRadius x)) h hadm₀ hY p hbounds.1 n
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hYr : (0 : ℝ) < Y := by exact_mod_cast hY
  have hXYr : (x : ℝ) ≤ Y := by exact_mod_cast hXY
  have hnumerator : (Real.exp 1 ^ 2 * (growingRadius x : ℝ) ^ 4) * (modulus ell₀ : ℝ) ≤
      (x : ℝ) ^ (1 / 10 : ℝ) := by
    rw [hmod, mul_comm]
    exact hnum a ha B hB hBx
  calc
    _ ≤ (Real.exp 1 ^ 2 * (growingRadius x : ℝ) ^ 4) * (modulus ell₀ : ℝ) / Y := hatom
    _ ≤ (x : ℝ) ^ (1 / 10 : ℝ) / Y := div_le_div_of_nonneg_right hnumerator hYr.le
    _ ≤ (x : ℝ) ^ (1 / 10 : ℝ) / x :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hxpos.le _) hxpos hXYr
    _ = _ := by
      have he : (-9 / 10 : ℝ) = 1 / 10 - 1 := by ring
      rw [he, Real.rpow_sub hxpos, Real.rpow_one]

end Erdos4.FGKMT
