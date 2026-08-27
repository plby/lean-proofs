import ErdosProblems.Erdos4.FGKMTGrowingLowModes
import ErdosProblems.Erdos4.FGKMTMaskedPrimeMeanSquare
import ErdosProblems.Erdos4.FGKMTGrowingFourierCutoff

/-! The high Fourier coefficients have an absolute scale bound for the growing family. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Filter FiniteCharacterSupport ProductCharacterEncoding ProductPrimeMeanSquare

theorem growing_large_local_decay_bound (x B : ℕ)
    (hk : 2 ≤ sieveDimension (growingIndex x))
    (l : SievePrime (harmonicModulus (growingPrecutoff x) B) (growingRadius x)) :
    20 * (sieveDimension (growingIndex x) : ℝ) ^ 3 ≤
      (2 / (sieveDimension (growingIndex x) : ℝ)) * growingLargePrimeValue x B l := by
  have hkR : (2 : ℝ) ≤ sieveDimension (growingIndex x) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < sieveDimension (growingIndex x) := by linarith
  have hl := sievePrimeValue_above_precut
    (fun p hp hpD => small_prime_dvd_harmonicModulus (growingPrecutoff x) B hp hpD) l
  have hD : 16 * (sieveDimension (growingIndex x) : ℝ) ^ 4 ≤
      growingLargePrimeValue x B l := by
    have hh := hl.le
    unfold growingPrecutoff at hh
    exact_mod_cast hh
  calc
    _ ≤ (2 * (growingLargePrimeValue x B l : ℝ)) /
        (sieveDimension (growingIndex x) : ℝ) := by
      apply (le_div_iff₀ hkpos).mpr
      nlinarith [pow_nonneg (Nat.cast_nonneg (sieveDimension (growingIndex x)) :
        (0 : ℝ) ≤ sieveDimension (growingIndex x)) 4]
    _ = _ := by ring

theorem growing_highMaskedCoefficient_norm_le (x B M : ℕ)
    (hk : 2 ≤ sieveDimension (growingIndex x)) {β : ℝ} (hβ : 0 ≤ β)
    (h : Fin (sieveDimension (growingIndex x)) → ℕ) (hinj : Function.Injective h)
    (hbound : ∀ i, h i ≤ growingPrecutoff x)
    (χ : smallCharacters
      (Sum.elim (growingSmallPrimeValue x B) (growingLargePrimeValue x B)) M) :
    ‖highMaskedCoefficient (growingSmallPrimeValue x B) (growingLargePrimeValue x B)
      β (growingRadius x) M
      (fun l i => (h i : ZMod (growingSmallPrimeValue x B l)))
      (fun l i => (h i : ZMod (growingLargePrimeValue x B l))) χ‖ ≤
        2 * maskedFourierScale (growingSmallPrimeValue x B) (growingLargePrimeValue x B)
          β (growingRadius x) (fun l i => (h i : ZMod (growingSmallPrimeValue x B l))) := by
  have hkR : (2 : ℝ) ≤ sieveDimension (growingIndex x) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < sieveDimension (growingIndex x) := by linarith
  have hδ0 : 0 ≤ 2 / (sieveDimension (growingIndex x) : ℝ) := by positivity
  have hδ1 : 2 / (sieveDimension (growingIndex x) : ℝ) ≤ 1 :=
    (div_le_one hkpos).mpr hkR
  have hlarge := sievePrimeShifts_injective (R := growingRadius x) h hinj hbound
    (fun p hp hpD => small_prime_dvd_harmonicModulus (growingPrecutoff x) B hp hpD)
  have hh := highMaskedCoefficient_norm_le (growingSmallPrimeValue x B)
    (growingLargePrimeValue x B) hβ (growingRadius x) M
    (growing_sievePrime_size x B (growingRadius x)) hδ0 hδ1
    (growing_large_local_decay_bound x B hk)
    (fun l i => (h i : ZMod (growingSmallPrimeValue x B l)))
    (fun l i => (h i : ZMod (growingLargePrimeValue x B l))) hlarge χ
  apply hh.trans_eq
  field_simp [hkpos.ne']

theorem eventually_growing_high_error_mean_square :
    ∀ᶠ x : ℕ in atTop, ∀ B : ℕ, ∀ β : ℝ, 0 ≤ β →
      ∀ h : Fin (sieveDimension (growingIndex x)) → ℕ,
        Function.Injective h → (∀ i, h i ≤ growingPrecutoff x) →
        ∀ Y : ℕ, x ≤ Y → ∀ sources targets : Finset ℕ,
          (∀ p ∈ sources, p.Prime ∧ growingRadius x ^ 2 < p ∧ p ≤ x) →
          (∀ q ∈ targets, q.Prime ∧ growingRadius x ^ 2 < q ∧ q ≤ Y) →
          ∀ a : sources → ℝ, (∀ p, 0 ≤ a p) → (∀ p, a p ≤ 1) →
          (∑ q : targets, ‖weightedSourceError
            (Sum.elim (growingSmallPrimeValue x B) (growingLargePrimeValue x B))
            (growingRadius x ^ 2)
            (highMaskedCoefficient (growingSmallPrimeValue x B) (growingLargePrimeValue x B)
              β (growingRadius x) (growingRadius x ^ 2)
              (fun l i => (h i : ZMod (growingSmallPrimeValue x B l)))
              (fun l i => (h i : ZMod (growingLargePrimeValue x B l))))
            sources (fun p => (a p : ℂ)) q‖ ^ 2) ≤
            160000 * (Y : ℝ) * x *
              (maskedFourierScale (growingSmallPrimeValue x B) (growingLargePrimeValue x B)
                β (growingRadius x) (fun l i => (h i : ZMod (growingSmallPrimeValue x B l)))) ^ 2 *
                  (∑ p : sources, a p) / Real.log (x : ℝ) ^ 2 := by
  have hlogTop := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_growing_fourier_cutoff, eventually_growingRadius_bounds,
    eventually_growing_pre_le_radius, hlogTop.eventually (eventually_ge_atTop 1),
    growingDimension_tendsto.eventually (eventually_ge_atTop 2)]
    with x hcut hR hDR hlog hk
  intro B β hβ h hinj hbound Y hXY sources targets hs ht a ha0 ha1
  let ell₀ := growingSmallPrimeValue x B
  let ell₁ := growingLargePrimeValue x B
  let F := maskedFourierScale ell₀ ell₁ β (growingRadius x)
    (fun l i => (h i : ZMod (ell₀ l)))
  have hF : 0 ≤ F := maskedFourierScale_nonneg ell₀ ell₁ β (growingRadius x) _
  have hsum : 0 ≤ ∑ p : sources, a p := Finset.sum_nonneg (fun p _ => ha0 p)
  have hRtwo : growingRadius x ≤ growingRadius x ^ 2 := by nlinarith [hR.1]
  have hscop : ∀ p ∈ sources, p.Coprime (modulus (Sum.elim ell₀ ell₁)) := by
    intro p hp
    exact growing_prime_coprime_modulus hDR (hs p hp).1 (hRtwo.trans_lt (hs p hp).2.1)
  have htcop : ∀ q ∈ targets, q.Coprime (modulus (Sum.elim ell₀ ell₁)) := by
    intro q hq
    exact growing_prime_coprime_modulus hDR (ht q hq).1 (hRtwo.trans_lt (ht q hq).2.1)
  have hraw := activation_source_error_mean_square (Sum.elim ell₀ ell₁)
    hcut.1.1 hcut.1.2 (growing_combined_family_injective x B) hcut.2.1
    x Y hcut.2.2.1 (hcut.2.2.1.trans hXY) sources targets hs ht hscop htcop
    (highMaskedCoefficient ell₀ ell₁ β (growingRadius x) (growingRadius x ^ 2)
      (fun l i => (h i : ZMod (ell₀ l))) (fun l i => (h i : ZMod (ell₁ l))))
    (show 0 ≤ 2 * F from by positivity)
    (growing_highMaskedCoefficient_norm_le x B (growingRadius x ^ 2) hk hβ h hinj hbound)
    a ha0 ha1
  change 1 ≤ Real.log (x : ℝ) at hlog
  have hLpos : 0 < Real.log (x : ℝ) := by linarith
  have hRpos : 0 < Real.log (growingRadius x : ℝ) :=
    Real.log_pos (by exact_mod_cast hR.1)
  have hratio : ∀ N : ℕ, 2 * (N : ℝ) / Real.log (growingRadius x : ℝ) ≤
      200 * (N : ℝ) / Real.log (x : ℝ) := by
    intro N
    calc
      _ ≤ (2 * (N : ℝ)) / (Real.log (x : ℝ) / 100) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hR.2
      _ = _ := by field_simp; ring
  apply hraw.trans
  calc
    _ ≤ (200 * (Y : ℝ) / Real.log (x : ℝ)) * (2 * F) ^ 2 *
        ((200 * (x : ℝ) / Real.log (x : ℝ)) * ∑ p : sources, a p) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_right (hratio Y) (sq_nonneg _))
        (mul_le_mul_of_nonneg_right (hratio x) hsum)
        (by positivity) (by positivity)
    _ = _ := by dsimp only [F]; ring

end Erdos4.FGKMT
