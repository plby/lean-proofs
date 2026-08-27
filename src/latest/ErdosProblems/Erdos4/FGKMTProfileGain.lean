import ErdosProblems.Erdos4.FGKMTSieveDivisorLaw

/-! Explicit lower and upper masses giving logarithmic gain in the sieve dimension. -/

namespace Erdos4.FGKMT

open BoundedGaps.Maynard

theorem rationalMass_lower {W T : ℕ} (hW : 0 < W) (hSq : Squarefree W) (hT : 1 ≤ T)
    {b : ℝ} (hb : 0 < b) :
    coprimeHarmonicDensity W * (Real.log (1 + b * Real.log (T : ℝ)) / b) -
      harmonicTransferError W ≤ rationalMass W b T := by
  have hh := (abs_le.mp (reciprocal_harmonic_mass_error hW hSq hT hb)).1
  change _ ≤ rationalMass W b T - _ at hh
  linarith

theorem rationalSquareMass_upper {W R : ℕ} (hW : 0 < W) (hSq : Squarefree W) (hR : 1 ≤ R)
    {b : ℝ} (hb : 0 ≤ b) :
    rationalSquareMass W b R ≤ coprimeHarmonicDensity W *
      (Real.log (R : ℝ) / (1 + b * Real.log (R : ℝ))) + harmonicTransferError W := by
  have hh := (abs_le.mp (reciprocal_sq_harmonic_mass_error hW hSq hR hb)).2
  change rationalSquareMass W b R - _ ≤ _ at hh
  linarith

theorem harmonic_error_le_density_over_slope {ρ b L E : ℝ} (hρ : 0 ≤ ρ) (hb : 0 < b)
    (hL : 0 ≤ L) (hE : E ≤ ρ * L / (2 * (1 + b * L))) : E ≤ ρ / (2 * b) := by
  apply hE.trans
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * (1 + b * L)) (by positivity : 0 < 2 * b)).mpr
  nlinarith

theorem rationalSquareMass_slope_upper {W R : ℕ} (hW : 0 < W) (hSq : Squarefree W) (hR : 1 ≤ R)
    {b : ℝ} (hb : 0 < b)
    (hE : harmonicTransferError W ≤ coprimeHarmonicDensity W / (2 * b)) :
    rationalSquareMass W b R ≤ 3 * coprimeHarmonicDensity W / (2 * b) := by
  have hL : 0 ≤ Real.log (R : ℝ) := Real.log_natCast_nonneg R
  have hρ := harmonicDensity_nonneg W
  have hquot : Real.log (R : ℝ) / (1 + b * Real.log (R : ℝ)) ≤ 1 / b := by
    apply (div_le_div_iff₀ (by positivity : 0 < 1 + b * Real.log (R : ℝ)) hb).mpr
    nlinarith
  have hh := rationalSquareMass_upper hW hSq hR hb.le
  have hmain := mul_le_mul_of_nonneg_left hquot hρ
  calc
    _ ≤ coprimeHarmonicDensity W * (1 / b) + coprimeHarmonicDensity W / (2 * b) := by linarith
    _ = _ := by ring

theorem sieveProfileScale_third_log_lower {j : ℕ} (hj : 1 ≤ j) :
    (j : ℝ) / 2 ≤ Real.log (1 + sieveProfileScale j / 3) := by
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hk : (0 : ℝ) < sieveDimension j := by exact_mod_cast sieveDimension_pos j
  have harg : (sieveDimension j : ℝ) ≤ 1 + sieveProfileScale j / 3 := by
    unfold sieveProfileScale
    nlinarith
  have hh := Real.log_le_log hk harg
  rw [log_sieveDimension] at hh
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hmul := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
  linarith

theorem rationalMass_face_lower {W R T j : ℕ} (hW : 0 < W) (hSq : Squarefree W)
    (hR : 2 ≤ R) (hT : 1 ≤ T) (hj : 2 ≤ j)
    (hface : Real.log (R : ℝ) / 3 ≤ Real.log (T : ℝ))
    (hE : harmonicTransferError W ≤ coprimeHarmonicDensity W / (2 * sieveSlope j R)) :
    coprimeHarmonicDensity W * (j : ℝ) / (4 * sieveSlope j R) ≤
      rationalMass W (sieveSlope j R) T := by
  have hb := sieveSlope_pos (by omega : 1 ≤ j) hR
  have hρ := harmonicDensity_nonneg W
  have hmul := mul_le_mul_of_nonneg_left hface hb.le
  have hz : sieveProfileScale j / 3 ≤ sieveSlope j R * Real.log (T : ℝ) := by
    have heq := sieveSlope_mul_log hR j
    nlinarith
  have hbase : 0 < 1 + sieveProfileScale j / 3 := by
    have hh := sieveProfileScale_ge_one (by omega : 1 ≤ j)
    linarith
  have hlog := (sieveProfileScale_third_log_lower (by omega : 1 ≤ j)).trans
    (Real.log_le_log hbase (by linarith : 1 + sieveProfileScale j / 3 ≤
      1 + sieveSlope j R * Real.log (T : ℝ)))
  have hscaled := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlog hb.le) hρ
  have hmass := rationalMass_lower hW hSq hT hb
  have hjR : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hquarter : coprimeHarmonicDensity W * (j : ℝ) / (4 * sieveSlope j R) ≤
      coprimeHarmonicDensity W * (((j : ℝ) / 2) / sieveSlope j R) -
        coprimeHarmonicDensity W / (2 * sieveSlope j R) := by
    apply (le_sub_iff_add_le).mpr
    field_simp
    nlinarith
  linarith

end Erdos4.FGKMT
