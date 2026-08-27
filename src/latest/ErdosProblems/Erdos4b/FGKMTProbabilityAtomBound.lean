/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTWeightProbability

/-! # Uniform subpower bounds for individual probability atoms -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

theorem CommonWeightEstimates.probability_atom_bound {x m B : ℕ} {y e : ℝ}
    {h : Fin (m + 1) → ℕ} (H : CommonWeightEstimates x m B y h e)
    (hx : 0 < x) (hxy : (x : ℝ) ≤ y) (hL : 0 < Real.log (x : ℝ))
    (herror : 1 / Real.log (Real.log (x : ℝ)) ^ 10 ≤ (1 / 2 : ℝ))
    (hscale : (x : ℝ) ^ (-e) ≤ commonWeightMassScale (m + 1)
      (dimensionPreSieveModulus (m + 1) B) (B * dimensionPreSieveModulus (m + 1) B)
      (dimensionSieveRadius x) h)
    {p : ℕ} (hp : p ∈ commonPinnedPrimeSet (x / 2) x) (n : ℤ) :
    commonPrimeSieveProbability (m + 1) (dimensionPreSieveModulus (m + 1) B)
      (B * dimensionPreSieveModulus (m + 1) B) (dimensionSieveRadius x) y h p n ≤
        (x : ℝ) ^ (-2 / 3 + 2 * e : ℝ) := by
  let S := commonWeightMassScale (m + 1) (dimensionPreSieveModulus (m + 1) B)
    (B * dimensionPreSieveModulus (m + 1) B) (dimensionSieveRadius x) h
  let M := commonPrimeSieveTotalMass (m + 1) (dimensionPreSieveModulus (m + 1) B)
    (B * dimensionPreSieveModulus (m + 1) B) (dimensionSieveRadius x) y h p
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hy : 0 < y := hxR.trans_le hxy
  have hS : 0 < S := (Real.rpow_pos_of_pos hxR _).trans_le hscale
  have hmain : y * S ≤ M := H.totalMass_ge_massScale hy hL herror hp
  have hMpos : 0 < M := (mul_pos hy hS).trans_le hmain
  have hMlow : (x : ℝ) ^ (1 - e : ℝ) ≤ M := by
    calc
      _ = (x : ℝ) * (x : ℝ) ^ (-e) := by
        rw [sub_eq_add_neg, Real.rpow_add hxR, Real.rpow_one]
      _ ≤ y * S := mul_le_mul hxy hscale (Real.rpow_nonneg hxR.le _) hy.le
      _ ≤ M := hmain
  obtain ⟨_htau, _hu, _htlow, _hulow, _huup, _hnonneg, _hsupp, hpoint, _htotal, _hpin⟩ := H
  calc
    _ ≤ (x : ℝ) ^ (1 / 3 + e : ℝ) / M :=
      div_le_div_of_nonneg_right (hpoint p n) hMpos.le
    _ ≤ (x : ℝ) ^ (1 / 3 + e : ℝ) / (x : ℝ) ^ (1 - e : ℝ) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hxR.le _)
        (Real.rpow_pos_of_pos hxR _) hMlow
    _ = _ := by
      rw [← Real.rpow_sub hxR]
      congr 1
      ring

theorem eventually_weightProbability_atom_bound {e : ℝ} (he : 0 < e) :
    ∀ᶠ x : ℕ in atTop, ∀ m B : ℕ,
      1 ≤ m → 10000 ≤ Real.log (m + 1 : ℕ) →
      (m + 1 : ℕ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) → (B = 1 ∨ B.Prime) →
      ∀ y : ℝ, (x : ℝ) ≤ y → ∀ h : Fin (m + 1) → ℕ,
      BoundedGaps.IsAdmissible (Finset.univ.image h) →
      CommonWeightEstimates x m B y h (e / 2) →
      ∀ p ∈ commonPinnedPrimeSet (x / 2) x, ∀ n : ℤ,
        commonPrimeSieveProbability (m + 1) (dimensionPreSieveModulus (m + 1) B)
          (B * dimensionPreSieveModulus (m + 1) B) (dimensionSieveRadius x) y h p n ≤
            (x : ℝ) ^ (-2 / 3 + e : ℝ) := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog := Real.tendsto_log_atTop.comp hlog
  filter_upwards [eventually_commonWeightMassScale_ge_inv_rpow (by positivity : 0 < e / 2),
    eventually_ge_atTop (1 : ℕ), hlog.eventually (eventually_ge_atTop (1 : ℝ)),
    hloglog.eventually (eventually_ge_atTop (2 : ℝ))] with x hscale hx hL hLL
  change 2 ≤ Real.log (Real.log (x : ℝ)) at hLL
  have herror : 1 / Real.log (Real.log (x : ℝ)) ^ 10 ≤ (1 / 2 : ℝ) := by
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hLL 10
    apply (div_le_iff₀ (by positivity : 0 < Real.log (Real.log (x : ℝ)) ^ 10)).mpr
    norm_num at hpow
    linarith
  intro m B hm hlogk hdim hB y hxy h hadm H p hp n
  have hs := hscale (m + 1) B (by omega) hlogk hdim hB h hadm
  have hb := H.probability_atom_bound (by omega) hxy (by linarith) herror hs hp n
  have heq : (-2 / 3 + 2 * (e / 2) : ℝ) = -2 / 3 + e := by ring
  simpa only [heq] using hb

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.CommonWeightEstimates.probability_atom_bound
#print axioms Erdos4b.FGKMT.eventually_weightProbability_atom_bound
