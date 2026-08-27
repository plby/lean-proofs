/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTTotalRelativeAlgebra
import ErdosProblems.Erdos4b.FGKMTWeightEnvelopeGrowth
import ErdosProblems.Erdos4b.FGKMTQuadraticScaleDecay

/-! # The centered total mass on the actual positive main scale -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

theorem eventually_commonPrimeSieveWeight_total_relative_decay {a : ℝ} (ha : 0 ≤ a) :
    ∀ᶠ x : ℕ in atTop, ∀ k B : ℕ,
      2 ≤ k → 10000 ≤ Real.log k →
      (k : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) → (B = 1 ∨ B.Prime) →
      (B : ℝ) ≤ Real.exp (a * Real.sqrt (Real.log (x : ℝ))) →
      ∀ P : ℕ, P.Prime → x / 2 < P →
      ∀ h : Fin k → ℕ, Function.Injective h →
      BoundedGaps.IsAdmissible (Finset.univ.image h) →
      (∀ i, h i < 2 * k ^ 2) → ∀ y : ℝ, (x : ℝ) ≤ y →
      let W := dimensionPreSieveModulus k B
      let R := dimensionSieveRadius x
      let S := commonWeightMassScale k W (B * W) R h
      |(∑' n : ℤ, commonPrimeSieveWeight k W (B * W) R y h P n) - 2 * y * S| /
        (2 * y * S) ≤ 3 * Real.log (x : ℝ) ^ (-1 / 4 : ℝ) := by
  obtain ⟨C, hC, htotal⟩ := exists_commonPrimeSieveWeight_centered_totalMass_error
  have hlogTop : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_dimensionSieveRadius_window,
    eventually_dimensionPreSieve_radius_range, eventually_dimensionPrimeCutoff_le_half,
    eventually_commonWeightMassScale_ge_inv_rpow (by norm_num : (0 : ℝ) < 1 / 4),
    eventually_dimensionWeightEnvelope_le_rpow (by norm_num : (0 : ℝ) < 1 / 6),
    eventually_uniform_sieveQuadraticError_small ha (by norm_num : (0 : ℝ) ≤ 8)
      (by norm_num : (0 : ℝ) < 1 / 18) hC,
    hlogTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with x hR hmod hcut hmain hE hquad hL hx
  intro k B hk hlog hdim hB hBsize P hP hPlower h hinj hadm hshift y hxy
  let W := dimensionPreSieveModulus k B
  let R := dimensionSieveRadius x
  let S := commonWeightMassScale k W (B * W) R h
  have hW : 0 < W := dimensionPreSieveModulus_pos k B
  have hBpos : 0 < B := hB.elim (by rintro rfl; omega) Nat.Prime.pos
  have hW1 : 1 ≤ W := hW
  have hRange := hmod k B (by omega) hdim
  have hRhalf : R ≤ x / 2 := by
    have hRR : R ≤ R ^ 2 := by dsimp only [R]; nlinarith [hR.1]
    have hRprod : R ^ 2 ≤ W * R ^ 2 := by
      simpa only [one_mul] using Nat.mul_le_mul_right (R ^ 2) hW1
    exact hRR.trans (hRprod.trans hRange.1)
  have hcutoff := hcut k hdim
  have hPW : P.Coprime W := prime_coprime_dimensionPreSieve hP (hcutoff.trans_lt hPlower)
  have hsmall : ∀ q : ℕ, q.Prime → q ≤ 2 * k ^ 2 → q ∣ B * W :=
    fun _q hq hqk => small_prime_dvd_dimensionPreSieve hq hqk
  have hq := hquad k B W R hBpos hW (by dsimp only [R]; omega) hR.2.1 hBsize
    (dimensionPreSieveModulus_le_exp k B) hdim hR.2.2.2
  have hSlow : (x : ℝ) ^ (-1 / 4 : ℝ) ≤ S := by
    simpa only [neg_div] using hmain k B hk hlog hdim hB h hadm
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hlogpos : 0 < Real.log (x : ℝ) := by linarith
  have hbudget := total_main_and_log_power_budget hxR hlogpos hxy hSlow
  have hy : 1 ≤ y := hxR.trans hxy
  have hboundary : (W : ℝ) * ((R : ℝ) ^ 3 * (1 + Real.log R) ^ (2 * k)) ≤
      y * S * Real.log (x : ℝ) ^ (-1 / 4 : ℝ) := by
    have he := hE k B (by omega) hdim
    norm_num at he
    exact he.trans hbudget.2.2
  have hm := htotal hk hlog (Nat.mul_pos hBpos hW) hR.1 hW (dvd_mul_left W B)
    hsmall hP (hRhalf.trans_lt hPlower) hPW h hinj hshift y (by linarith) hq.2
  exact centered_total_relative_error_le hbudget.1 hy
    (Real.rpow_nonneg (Real.log_natCast_nonneg x) _) hq.1 hbudget.2.1 hboundary hm

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.eventually_commonPrimeSieveWeight_total_relative_decay
