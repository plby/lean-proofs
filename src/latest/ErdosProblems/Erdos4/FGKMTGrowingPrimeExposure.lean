import ErdosProblems.Erdos4.FGKMTArithmeticIncidence
import ErdosProblems.Erdos4.FGKMTGrowingPrincipalMass
import ErdosProblems.Erdos4.FGKMTGrowingHighModes
import ErdosProblems.Erdos4.FGKMTGrowingPrimeSupply
import ErdosProblems.Erdos4.FGKMTExposureBudgets

/-!
Unconditional growing-dimensional prime exposure outside a quantitatively small target set.
The source interval, prime averages, Fourier cutoffs, and actual center normalizers are discharged.
-/

open scoped BigOperators

namespace Erdos4.FGKMT

open Filter Classical ProductCharacterEncoding ProductPrimeMeanSquare RestrictedProductNorm

theorem exists_growing_prime_exposure :
    ∃ a C d : ℝ, 0 < a ∧ a ≤ 1 / 4 ∧ 0 < C ∧ 0 < d ∧
      ∀ᶠ x : ℕ in atTop, ∃ B : ℕ,
        B ≤ exponentialConductorCutoff a x ∧ (B = 1 ∨ B.Prime) ∧
        ∀ h : Fin (sieveDimension (growingIndex x)) → ℕ,
          Function.Injective h → (∀ i, h i ≤ growingPrecutoff x) →
          (∀ p : ℕ, p.Prime → ∃ b : ZMod p, ∀ i, b + (h i : ZMod p) ≠ 0) →
          ∀ Y : ℕ, ∀ hY : 1 ≤ Y, x ≤ Y → growingPrecutoff x * x ≤ Y →
          ∃ bad : Finset ℕ, bad ⊆ ChebyshevIntervals.primeInterval x Y ∧
            (bad.card : ℝ) ≤ C * Y /
              (Real.log (x : ℝ) * (growingIndex x : ℝ) ^ 2) ∧
            ∀ q ∈ ChebyshevIntervals.primeInterval x Y, q ∉ bad →
              d * (growingIndex x : ℝ) * x / Y ≤
                rationalSourceIncidence (growingSmallPrimeValue x B) (growingLargePrimeValue x B)
                  (sieveSlope (growingIndex x) (growingRadius x)) (growingRadius x)
                  h hY (growingSourcePrimes x) (fun _ => 1) q := by
  obtain ⟨a, ha, ha1, hlow⟩ := exists_growing_low_mode_bound
  obtain ⟨c, hc, hgain⟩ := exists_growing_principal_scale_gain
  let d₀ : ℝ := Real.log 2 / 64
  have hd₀ : 0 < d₀ := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  refine ⟨a, 2560000 / (c ^ 2 * d₀), d₀ / 14745600, ha, ha1, by positivity, by positivity, ?_⟩
  have hjTop : Tendsto (fun x => (growingIndex x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp growingIndex_tendsto
  filter_upwards [hlow, hgain, eventually_growing_principal_density_gain,
    eventually_growing_high_error_mean_square, eventually_growing_fourier_cutoff,
    eventually_growing_center_laws, eventually_growing_source_supply,
    eventually_growingRadius_bounds, eventually_growing_pre_le_radius,
    hjTop.eventually (eventually_ge_atTop (max 1 (4 / c)))]
    with x hlow hgain hprincipal hhigh hcut hcenter hsupply hR hDR hjlarge
  obtain ⟨B, hBx, hB, hlow⟩ := hlow
  refine ⟨B, hBx, hB, ?_⟩
  intro h hinj hbound hadm Y hY hXY hDY
  let ell₀ := growingSmallPrimeValue x B
  let ell₁ := growingLargePrimeValue x B
  let β := sieveSlope (growingIndex x) (growingRadius x)
  let sources := growingSourcePrimes x
  let targets := ChebyshevIntervals.primeInterval x Y
  let α := smallProductDensity ell₀ (fun l i => (h i : ZMod (ell₀ l)))
  let E := energy (rationalCoefficient (k := sieveDimension (growingIndex x)) β (growingRadius x) ell₁)
  let F := maskedFourierScale ell₀ ell₁ β (growingRadius x)
    (fun l i => (h i : ZMod (ell₀ l)))
  let P := aggregatePrincipalMass ell₀ ell₁ β (growingRadius x)
    (fun l i => (h i : ZMod (ell₀ l)))
  let η := (sources.card : ℝ) * c * (growingIndex x : ℝ) * F / 4
  let error : ℕ → ℂ := weightedSourceError (Sum.elim ell₀ ell₁) (growingRadius x ^ 2)
    (highMaskedCoefficient ell₀ ell₁ β (growingRadius x) (growingRadius x ^ 2)
      (fun l i => (h i : ZMod (ell₀ l))) (fun l i => (h i : ZMod (ell₁ l)))) sources (fun _ => 1)
  change max 1 (4 / c) ≤ (growingIndex x : ℝ) at hjlarge
  have hj1R : (1 : ℝ) ≤ growingIndex x := (le_max_left _ _).trans hjlarge
  have hjpos : (0 : ℝ) < growingIndex x := by linarith
  have hj1 : 1 ≤ growingIndex x := by exact_mod_cast hj1R
  have hcj : 4 ≤ c * (growingIndex x : ℝ) := by
    have hh := (div_le_iff₀ hc).mp ((le_max_right _ _).trans hjlarge)
    nlinarith
  have hR1 : 1 ≤ growingRadius x := by omega
  have hRtwo : growingRadius x ≤ growingRadius x ^ 2 := by nlinarith [hR.1]
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x from by have := hsupply.1; omega)
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast hY
  have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hsupply.1)
  have hβ : 0 ≤ β := (sieveSlope_pos hj1 hR.1).le
  have hα : 0 < α := smallSieve_density_pos (growingPrecutoff x) B h hadm
  have hE : 0 < E := zero_lt_one.trans_le (one_le_rationalCoefficient_energy β hR1 ell₁)
  have hF : 0 < F := growing_maskedFourierScale_pos x B β hR1 h hadm
  have hsource : d₀ * x / Real.log (x : ℝ) ≤ (sources.card : ℝ) := hsupply.2.2.1
  have hsourceWeak : (x : ℝ) / Real.log (x : ℝ) ^ 2 ≤ (sources.card : ℝ) := hsupply.2.2.2
  have hSpos : (0 : ℝ) < sources.card := (div_pos (mul_pos hd₀ hxpos) hlog).trans_le hsource
  have hη : 0 < η := by dsimp only [η]; positivity
  have hgainP : c * (growingIndex x : ℝ) * F ≤ P := hgain a ha1 B hB hBx h
  have hprincipalP : α * E * Real.log (growingRadius x : ℝ) * (growingIndex x : ℝ) / 24576 ≤ P :=
    hprincipal a ha1 B hB hBx h
  have hηupper : η ≤ (sources.card : ℝ) * P / 4 := by
    calc
      _ = (sources.card : ℝ) * (c * (growingIndex x : ℝ) * F) / 4 := by dsimp only [η]; ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hgainP hSpos.le) (by norm_num)
  have hs : ∀ p ∈ sources, p.Prime ∧ growingRadius x ^ 2 < p ∧ p ≤ x := by
    intro p hp
    have hh := mem_growingSourcePrimes.mp hp
    exact ⟨hh.1, hsupply.2.1.trans_lt hh.2.1, hh.2.2⟩
  have ht : ∀ q ∈ targets, q.Prime ∧ growingRadius x ^ 2 < q ∧ q ≤ Y := by
    intro q hq
    have hh := ChebyshevIntervals.mem_primeInterval.mp hq
    exact ⟨hh.1, (hsupply.2.1.trans (Nat.div_le_self x 32)).trans_lt hh.2.1, hh.2.2⟩
  have hscop : ∀ p ∈ sources, p.Coprime (modulus (Sum.elim ell₀ ell₁)) := by
    intro p hp
    exact growing_prime_coprime_modulus hDR (hs p hp).1 (hRtwo.trans_lt (hs p hp).2.1)
  have htcop : ∀ q ∈ targets, q.Coprime (modulus (Sum.elim ell₀ ell₁)) := by
    intro q hq
    exact growing_prime_coprime_modulus hDR (ht q hq).1 (hRtwo.trans_lt (ht q hq).2.1)
  have hms : (∑ q : targets, ‖error q‖ ^ 2) ≤
      160000 * (Y : ℝ) * x * F ^ 2 * sources.card / Real.log (x : ℝ) ^ 2 := by
    simpa only [Complex.ofReal_one, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
      nsmul_eq_mul, mul_one] using
      hhigh B β hβ h hinj hbound Y hXY sources targets hs ht
        (fun _ => 1) (fun _ => by norm_num) (fun _ => le_refl (1 : ℝ))
  obtain ⟨bad, hbad, hcard, hgood⟩ := exists_norm_exceptional_finset targets error hη hms
  refine ⟨bad, hbad, ?_, ?_⟩
  · exact hcard.trans (high_error_budget_cancel hxpos hYpos.le hlog hF hjpos hc hd₀ hsource)
  · intro q hq hqgood
    have hqrange := ht q hq
    have hlo := hlow β hβ h hinj hbound (growingRadius x ^ 2) (x / 32) x
      (hRtwo.trans hsupply.2.1) (Nat.div_le_self x 32) (le_refl x) q
    have hlobudget : F * x / Real.log (x : ℝ) ^ 2 ≤ η :=
      low_error_budget hF.le hSpos.le hsourceWeak hcj
    have hlarge : ∀ l, Function.Injective (fun i => (h i : ZMod (ell₁ l))) :=
      sievePrimeShifts_injective h hinj hbound
        (fun p hp hpD => small_prime_dvd_harmonicModulus (growingPrecutoff x) B hp hpD)
    have hshift : ∀ p : sources, ∀ i, h i * p.val ≤ Y := by
      intro p i
      exact (Nat.mul_le_mul (hbound i) (hs p p.property).2.2).trans hDY
    have hnorm : ∀ p : sources,
        (0 < maskedTranslatedNormalizer ell₀ ell₁ β (growingRadius x) h Y p.val) ∧
        maskedTranslatedNormalizer ell₀ ell₁ β (growingRadius x) h Y p.val ≤ 3 * (α * Y * E) := by
      intro p
      have hh := (hcenter a ha1 B hB hBx h hinj hbound hadm Y hY hXY p.val
        (hs p p.property).1 (hRtwo.trans_lt (hs p p.property).2.1)).1
      exact ⟨hh.1, hh.2.2⟩
    have hfourier := rationalSourceIncidence_fourier_lower ell₀ ell₁ β (growingRadius x)
      (growingRadius x ^ 2) (hcut.2.2.2 a ha1 B hB hBx) h hinj hlarge hY sources
      (fun p => (hs p p.property).1.pos) hshift hscop (fun _ => 1) (fun _ => by norm_num)
      q hqrange.1.one_le hqrange.2.2 (htcop q hq) (fun p => (hnorm p).1)
      (show 0 < 3 * (α * Y * E) by positivity) (fun p => (hnorm p).2)
      (hgood q hq hqgood) (hlo.trans hlobudget)
    have hlower : ((sources.card : ℝ) * P - η - η) / (3 * (α * Y * E)) ≤
        rationalSourceIncidence ell₀ ell₁ β (growingRadius x) h hY sources (fun _ => 1) q := by
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, mul_one]
        using hfourier
    exact (incidence_gain_budget hxpos.le hYpos hlog hα hE hjpos.le hd₀
      hsource hR.2 hprincipalP hηupper).trans hlower

end Erdos4.FGKMT
