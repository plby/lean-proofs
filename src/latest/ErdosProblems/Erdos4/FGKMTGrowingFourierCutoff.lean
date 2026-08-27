import ErdosProblems.Erdos4.FGKMTGrowingCenterLaw
import ErdosProblems.Erdos4.FGKMTCombinedPrimeFamily
import ErdosProblems.Erdos4.PrimeMeanSquare

/-! Concrete Fourier truncation and prime Gram cutoffs at every large endpoint. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Filter ProductCharacterEncoding

theorem eventually_growing_smallModulus_le_radius :
    ∀ᶠ x : ℕ in atTop, ∀ a : ℝ, a ≤ 1 / 4 → ∀ B : ℕ,
      (B = 1 ∨ B.Prime) → B ≤ exponentialConductorCutoff a x →
      modulus (growingSmallPrimeValue x B) ≤ growingRadius x := by
  filter_upwards [eventually_harmonicModulus_log_small, eventually_growingRadius_bounds]
    with x hW hR
  intro a ha B hB hBx
  have hmod : modulus (growingSmallPrimeValue x B) =
      smallPresieveModulus (growingPrecutoff x) B :=
    smallSievePrime_product (growingPrecutoff x) B
  have hMdvd : modulus (growingSmallPrimeValue x B) ∣ harmonicModulus (growingPrecutoff x) B := by
    rw [hmod]
    exact (smallPresieveModulus_dvd_primorial (growingPrecutoff x) B).trans
      (primorial_dvd_harmonicModulus (growingPrecutoff x) B)
  have hMle := Nat.le_of_dvd (harmonicModulus_pos (growingPrecutoff x) hB) hMdvd
  have hWpos : (0 : ℝ) < harmonicModulus (growingPrecutoff x) B := by
    exact_mod_cast harmonicModulus_pos (growingPrecutoff x) hB
  have hRpos : (0 : ℝ) < growingRadius x := by exact_mod_cast (by omega : 0 < growingRadius x)
  have hWR : (harmonicModulus (growingPrecutoff x) B : ℝ) ≤ growingRadius x := by
    calc
      _ = Real.exp (Real.log (harmonicModulus (growingPrecutoff x) B : ℝ)) :=
        (Real.exp_log hWpos).symm
      _ ≤ Real.exp (Real.log (growingRadius x : ℝ)) :=
        Real.exp_le_exp.mpr ((hW a ha B hB hBx).trans hR.2)
      _ = _ := Real.exp_log hRpos
  exact hMle.trans (by exact_mod_cast hWR)

theorem eventually_growing_fourier_cutoff :
    ∀ᶠ x : ℕ in atTop,
      (2 ≤ growingRadius x ∧
        Real.log (growingRadius x : ℝ) ≤
          SelbergCoefficients.harmonicMass (growingRadius x ^ 2)) ∧
      (growingRadius x ^ 2) ^ 2 ≤ growingRadius x ^ 10 ∧
      growingRadius x ^ 50 ≤ x ∧
      ∀ a : ℝ, a ≤ 1 / 4 → ∀ B : ℕ,
        (B = 1 ∨ B.Prime) → B ≤ exponentialConductorCutoff a x →
        (∏ l, growingSmallPrimeValue x B l) * growingRadius x ^ 2 ≤
          (growingRadius x ^ 2) ^ 2 := by
  filter_upwards [growingRadius_tendsto.eventually PrimeMeanSquare.eventually_good_cutoff,
    eventually_growing_smallModulus_le_radius] with x hgood hsmall
  have hR1 : 1 ≤ growingRadius x := by omega
  refine ⟨hgood, ?_, growingRadius_pow_fifty_le x, ?_⟩
  · simpa only [← pow_mul] using
      Nat.pow_le_pow_right hR1 (by norm_num : 2 * 2 ≤ 10)
  · intro a ha B hB hBx
    have hM := hsmall a ha B hB hBx
    change (∏ l, growingSmallPrimeValue x B l) ≤ growingRadius x at hM
    calc
      _ ≤ growingRadius x * growingRadius x ^ 2 := Nat.mul_le_mul_right _ hM
      _ = growingRadius x ^ 3 := by ring
      _ ≤ growingRadius x ^ 4 := Nat.pow_le_pow_right hR1 (by norm_num)
      _ = _ := by ring

theorem growing_combined_family_injective (x B : ℕ) :
    Function.Injective (Sum.elim (growingSmallPrimeValue x B) (growingLargePrimeValue x B)) := by
  have heq : Sum.elim (growingSmallPrimeValue x B) (growingLargePrimeValue x B) =
      combinedSievePrimeValue (growingPrecutoff x) (growingRadius x) B := by
    funext l
    cases l <;> rfl
  rw [heq]
  exact combinedSievePrime_injective (growingPrecutoff x) (growingRadius x) B

theorem growing_combined_family_le {x : ℕ} (hDR : growingPrecutoff x ≤ growingRadius x)
    (B : ℕ) (l) :
    Sum.elim (growingSmallPrimeValue x B) (growingLargePrimeValue x B) l ≤ growingRadius x := by
  cases l with
  | inl l => exact (smallSievePrime_le (growingPrecutoff x) B l).trans hDR
  | inr l => exact sievePrimeValue_le (harmonicModulus (growingPrecutoff x) B) (growingRadius x) l

theorem growing_prime_coprime_modulus {x B p : ℕ}
    (hDR : growingPrecutoff x ≤ growingRadius x) (hp : p.Prime) (hRp : growingRadius x < p) :
    p.Coprime (modulus (Sum.elim (growingSmallPrimeValue x B) (growingLargePrimeValue x B))) :=
  ProductPrimeMeanSquare.coprime_modulus_of_prime_gt _ hp
    (fun l => (growing_combined_family_le hDR B l).trans_lt hRp)

end Erdos4.FGKMT
