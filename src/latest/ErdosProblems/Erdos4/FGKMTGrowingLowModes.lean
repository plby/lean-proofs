import ErdosProblems.Erdos4.FGKMTLowIntervalCancellation
import ErdosProblems.Erdos4.FGKMTSmallModulusAbsorption
import ErdosProblems.Erdos4.FGKMTGrowingCenterLaw

/-! Uniform low-mode cancellation for the actual growing sieve family and every source interval. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Filter ProductCharacterEncoding

theorem growing_large_local_unit_bound (x B : ℕ)
    (hk : 2 ≤ sieveDimension (growingIndex x))
    (l : SievePrime (harmonicModulus (growingPrecutoff x) B) (growingRadius x)) :
    20 * (sieveDimension (growingIndex x) : ℝ) ^ 3 ≤ growingLargePrimeValue x B l := by
  have hkR : (2 : ℝ) ≤ sieveDimension (growingIndex x) := by exact_mod_cast hk
  have hD : 20 * (sieveDimension (growingIndex x) : ℝ) ^ 3 ≤ growingPrecutoff x := by
    unfold growingPrecutoff
    push_cast
    have hh := mul_nonneg
      (show 0 ≤ 16 * (sieveDimension (growingIndex x) : ℝ) - 20 by linarith)
      (pow_nonneg (Nat.cast_nonneg (sieveDimension (growingIndex x))) 3)
    nlinarith
  have hl := sievePrimeValue_above_precut
    (fun p hp hpD => small_prime_dvd_harmonicModulus (growingPrecutoff x) B hp hpD) l
  exact hD.trans (by exact_mod_cast hl.le)

theorem exists_growing_low_mode_bound :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 4 ∧
      ∀ᶠ x : ℕ in atTop, ∃ B : ℕ,
        B ≤ exponentialConductorCutoff a x ∧ (B = 1 ∨ B.Prime) ∧
        ∀ β : ℝ, 0 ≤ β → ∀ h : Fin (sieveDimension (growingIndex x)) → ℕ,
          Function.Injective h → (∀ i, h i ≤ growingPrecutoff x) →
          ∀ M A Z : ℕ, growingRadius x ≤ A → A ≤ Z → Z ≤ x → ∀ q : ℕ,
          ‖ProductPrimeMeanSquare.weightedSourceError
            (Sum.elim (growingSmallPrimeValue x B) (growingLargePrimeValue x B)) M
            (lowMaskedCoefficient (growingSmallPrimeValue x B) (growingLargePrimeValue x B)
              β (growingRadius x) M
              (fun l i => (h i : ZMod (growingSmallPrimeValue x B l)))
              (fun l i => (h i : ZMod (growingLargePrimeValue x B l))))
            (ChebyshevIntervals.primeInterval A Z) (fun _ => 1) q‖ ≤
              maskedFourierScale (growingSmallPrimeValue x B) (growingLargePrimeValue x B)
                β (growingRadius x) (fun l i => (h i : ZMod (growingSmallPrimeValue x B l))) *
                  x / Real.log (x : ℝ) ^ 2 := by
  obtain ⟨a, C, ha, ha1, hC, hdist⟩ := exists_exponential_prime_distribution
  refine ⟨a, ha, ha1, ?_⟩
  have hlogTop := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hdist, eventually_smallPresieve_cubic_decay ha hC.le,
    eventually_growing_modulus_level, eventually_growingRadius_bounds,
    eventually_growing_pre_le_radius, eventually_growingDimension_bounds,
    growingDimension_tendsto.eventually (eventually_ge_atTop 2),
    hlogTop.eventually (eventually_ge_atTop 1)] with x hdist hdec hlevel hR hDR hdim hk hlog
  change 1 ≤ Real.log (x : ℝ) at hlog
  have hlogpos : 0 < Real.log (x : ℝ) := by linarith
  obtain ⟨B, hBR, hB, hdist⟩ := hdist
  refine ⟨B, hBR, hB, ?_⟩
  intro β hβ h hinj hbound M A Z hRA hAZ hZx q
  let ell₀ := growingSmallPrimeValue x B
  let ell₁ := growingLargePrimeValue x B
  let h₀ := fun l i => (h i : ZMod (ell₀ l))
  let h₁ := fun l i => (h i : ZMod (ell₁ l))
  let F := maskedFourierScale ell₀ ell₁ β (growingRadius x) h₀
  let K := (sieveDimension (growingIndex x) : ℝ) * F
  have hF : 0 ≤ F := maskedFourierScale_nonneg ell₀ ell₁ β (growingRadius x) h₀
  have hK : 0 ≤ K := mul_nonneg (Nat.cast_nonneg _) hF
  have hval : Sum.elim ell₀ ell₁ =
      combinedSievePrimeValue (growingPrecutoff x) (growingRadius x) B := by
    funext l
    cases l <;> rfl
  have hfamily : Function.Injective (Sum.elim ell₀ ell₁) := by
    rw [hval]
    exact combinedSievePrime_injective (growingPrecutoff x) (growingRadius x) B
  have hcop : ∀ l, (Sum.elim ell₀ ell₁ l).Coprime B := by
    rw [hval]
    exact combinedSievePrime_coprime_exception (growingPrecutoff x) (growingRadius x) hB
  have hlarge : ∀ l, Function.Injective (h₁ l) := sievePrimeShifts_injective h hinj hbound
    (fun p hp hpD => small_prime_dvd_harmonicModulus (growingPrecutoff x) B hp hpD)
  have hlocal : ∀ l, 20 * (sieveDimension (growingIndex x) : ℝ) ^ 3 ≤ 1 * ell₁ l := by
    intro l
    simpa only [one_mul] using growing_large_local_unit_bound x B hk l
  have hc : ∀ χ, ‖lowMaskedCoefficient ell₀ ell₁ β (growingRadius x) M h₀ h₁ χ‖ ≤ K :=
    lowMaskedCoefficient_norm_le ell₀ ell₁ hβ (growingRadius x) M
      (growing_sievePrime_size x B (growingRadius x)) (le_refl (1 : ℝ)) hlocal h₀ h₁ hlarge
  have hmod : modulus ell₀ = smallPresieveModulus (growingPrecutoff x) B :=
    smallSievePrime_product (growingPrecutoff x) B
  have hMle : modulus ell₀ ≤ harmonicModulus (growingPrecutoff x) B := by
    rw [hmod]
    exact Nat.le_of_dvd (harmonicModulus_pos (growingPrecutoff x) hB)
      ((smallPresieveModulus_dvd_primorial (growingPrecutoff x) B).trans
        (primorial_dvd_harmonicModulus (growingPrecutoff x) B))
  have hR8 : 1 ≤ growingRadius x ^ 8 := Nat.one_le_pow _ _ (by omega)
  have hN : modulus ell₀ ≤ powerDistributionLevel x := by
    apply hMle.trans
    apply (show harmonicModulus (growingPrecutoff x) B ≤
        harmonicModulus (growingPrecutoff x) B * growingRadius x ^ 8 from by
      simpa only [mul_one] using Nat.mul_le_mul_left (harmonicModulus (growingPrecutoff x) B) hR8).trans
    exact hlevel a ha1 B hB hBR
  have hs : ∀ p ∈ ChebyshevIntervals.primeInterval A Z,
      p.Coprime (modulus (Sum.elim ell₀ ell₁)) := by
    intro p hp
    have hrange := ChebyshevIntervals.mem_primeInterval.mp hp
    apply ProductPrimeMeanSquare.coprime_modulus_of_prime_gt (Sum.elim ell₀ ell₁) hrange.1
    intro l
    rw [hval]
    exact ((combinedSievePrime_le hDR B l).trans hRA).trans_lt hrange.2.1
  have hfinite := low_masked_interval_error ell₀ ell₁ β (growingRadius x) M h₀ h₁ hfamily
    (hR.1.trans hRA) hAZ hZx hN hcop hs q hK hc
  have hraw := hfinite.trans (mul_le_mul_of_nonneg_left hdist
    (show 0 ≤ 2 * (modulus ell₀ : ℝ) ^ 3 * K by positivity))
  have hdecB : 2 * (modulus ell₀ : ℝ) ^ 3 * C * Real.log (x : ℝ) ^ 3 *
      Real.exp (-(a / 2) * Real.sqrt (Real.log (x : ℝ))) ≤ 1 := by
    rw [hmod]
    exact hdec B
  have hlow : ‖ProductPrimeMeanSquare.weightedSourceError (Sum.elim ell₀ ell₁) M
      (lowMaskedCoefficient ell₀ ell₁ β (growingRadius x) M h₀ h₁)
      (ChebyshevIntervals.primeInterval A Z) (fun _ => 1) q‖ ≤ K * x / Real.log (x : ℝ) ^ 3 := by
    apply (le_div_iff₀ (pow_pos hlogpos 3)).mpr
    calc
      _ ≤ (2 * (modulus ell₀ : ℝ) ^ 3 * K *
          (C * ((x : ℝ) * Real.exp (-(a / 2) * Real.sqrt (Real.log (x : ℝ)))))) *
          Real.log (x : ℝ) ^ 3 := mul_le_mul_of_nonneg_right hraw (pow_nonneg hlogpos.le 3)
      _ = (K * x) * (2 * (modulus ell₀ : ℝ) ^ 3 * C * Real.log (x : ℝ) ^ 3 *
          Real.exp (-(a / 2) * Real.sqrt (Real.log (x : ℝ)))) := by ring
      _ ≤ (K * x) * 1 := mul_le_mul_of_nonneg_left hdecB (mul_nonneg hK (Nat.cast_nonneg x))
      _ = _ := mul_one _
  have hkL : (sieveDimension (growingIndex x) : ℝ) ≤ Real.log (x : ℝ) := by
    apply hdim.2.trans
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hlog (by norm_num : (1 / 100 : ℝ) ≤ 1)
  have hKx : K * x ≤ F * x * Real.log (x : ℝ) := by
    calc
      _ = (sieveDimension (growingIndex x) : ℝ) * (F * x) := by dsimp only [K]; ring
      _ ≤ Real.log (x : ℝ) * (F * x) :=
        mul_le_mul_of_nonneg_right hkL (mul_nonneg hF (Nat.cast_nonneg x))
      _ = _ := by ring
  exact hlow.trans ((div_le_div_of_nonneg_right hKx (pow_nonneg hlogpos.le 3)).trans_eq (by
    field_simp <;> ring))

end Erdos4.FGKMT
