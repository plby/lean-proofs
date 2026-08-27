/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTExactWeightNormalization
import ErdosProblems.Erdos4b.FGKMTPrimeCountBounds

/-! # Positivity and quantitative size of the exact common scalars -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

theorem commonWeightGain_bounds {m B W R x : ℕ}
    (hm : 1 ≤ m) (hlog : 10000 ≤ Real.log (m + 1 : ℕ))
    (hB : B = 1 ∨ B.Prime) (hW : 0 < W) (hx : 0 < x)
    (hL : 0 < Real.log (x : ℝ))
    (hRlo : (1 / 18 : ℝ) * Real.log (x : ℝ) ≤ Real.log (R : ℝ))
    (hRhi : Real.log (R : ℝ) ≤ Real.log (x : ℝ))
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ B * W)
    (hNlo : (x : ℝ) / (8 * Real.log (x : ℝ)) ≤ (commonPinnedPrimeSet (x / 2) x).card)
    (hNhi : ((commonPinnedPrimeSet (x / 2) x).card : ℝ) ≤ 2 * x / Real.log (x : ℝ)) :
    Real.log (m + 1 : ℕ) / 18432 ≤ commonWeightGain m B W R x ∧
      commonWeightGain m B W R x ≤ 12 * Real.exp 24 * Real.log (m + 1 : ℕ) := by
  have hBpos : 0 < B := hB.elim (by rintro rfl; omega) Nat.Prime.pos
  have hBposR : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hFLo := half_le_totientDensity_of_one_or_prime hB
  have hFHi : (B.totient : ℝ) / B ≤ 1 := by
    apply (div_le_iff₀ hBposR).mpr
    simpa only [one_mul] using (show (B.totient : ℝ) ≤ B by exact_mod_cast Nat.totient_le B)
  have hV := commonPinnedVariationalGain_bounds (R := R) hm hlog (Nat.mul_pos hBpos hW) hsmall
  have hlog0 : 0 ≤ Real.log (m + 1 : ℕ) := by linarith
  have hV0 : 0 ≤ commonPinnedVariationalGain m (B * W) R :=
    (div_nonneg hlog0 (by norm_num)).trans hV.1
  constructor
  · calc
      _ = ((1 / 2 : ℝ) * ((1 / 18 : ℝ) * Real.log (x : ℝ)) *
          (Real.log (m + 1 : ℕ) / 64) * ((x : ℝ) / (8 * Real.log (x : ℝ)))) / x := by
        field_simp
        ring
      _ ≤ _ := by
        unfold commonWeightGain
        gcongr
        exact hV.1
  · calc
      _ ≤ (1 * Real.log (x : ℝ) * (6 * Real.exp 24 * Real.log (m + 1 : ℕ)) *
          (2 * x / Real.log (x : ℝ))) / x := by
        unfold commonWeightGain
        gcongr
        exact hV.2
      _ = _ := by
        field_simp
        ring

theorem eventually_chosenWeightGain_bounds :
    ∀ᶠ x : ℕ in atTop, ∀ m B : ℕ,
      1 ≤ m → 10000 ≤ Real.log (m + 1 : ℕ) → (B = 1 ∨ B.Prime) →
      Real.log (m + 1 : ℕ) / 18432 ≤
        commonWeightGain m B (dimensionPreSieveModulus (m + 1) B) (dimensionSieveRadius x) x ∧
      commonWeightGain m B (dimensionPreSieveModulus (m + 1) B) (dimensionSieveRadius x) x ≤
        12 * Real.exp 24 * Real.log (m + 1 : ℕ) := by
  have hlogTop : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_dimensionSieveRadius_window,
    eventually_commonPinnedPrimeSet_card_bounds,
    hlogTop.eventually (eventually_ge_atTop (1 : ℝ)), eventually_ge_atTop (1 : ℕ)] with
      x hR hN hL hx
  intro m B hm hlog hB
  have hlogR : Real.log (dimensionSieveRadius x : ℝ) ≤ Real.log (x : ℝ) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < dimensionSieveRadius x))
      (by exact_mod_cast hR.2.1)
  exact commonWeightGain_bounds hm hlog hB (dimensionPreSieveModulus_pos _ _) (by omega)
    (by linarith) hR.2.2.2 hlogR (fun _p hp hpk => small_prime_dvd_dimensionPreSieve hp hpk)
    hN.1 hN.2

theorem eventually_commonWeightTau_ge_inv_rpow {e : ℝ} (he : 0 < e) :
    ∀ᶠ x : ℕ in atTop, ∀ k B : ℕ,
      2 ≤ k → 10000 ≤ Real.log k →
      (k : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) → (B = 1 ∨ B.Prime) →
      ∀ h : Fin k → ℕ, BoundedGaps.IsAdmissible (Finset.univ.image h) →
      (x : ℝ) ^ (-e) ≤ commonWeightTau k (dimensionPreSieveModulus k B)
        (B * dimensionPreSieveModulus k B) (dimensionSieveRadius x) x h := by
  have hlogTop : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_commonWeightMassScale_ge_inv_rpow he,
    hlogTop.eventually (eventually_ge_atTop (1 : ℝ))] with x hx hL
  intro k B hk hlog hdim hB h hadm
  have hmain := hx k B hk hlog hdim hB h hadm
  have hmain0 := (Real.rpow_nonneg (Nat.cast_nonneg x) (-e)).trans hmain
  have hpow := mul_le_mul_of_nonneg_left (one_le_pow₀ (n := k) hL) hmain0
  unfold commonWeightTau
  nlinarith

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.eventually_chosenWeightGain_bounds
#print axioms Erdos4b.FGKMT.eventually_commonWeightTau_ge_inv_rpow
