import ErdosProblems.Erdos4.FGKMTRationalMoments

/-! A numerical sufficient condition for concentration of the actual divisor law. -/

namespace Erdos4.FGKMT

open BoundedGaps.Maynard

theorem rational_mass_budget_scalar {M₁ M₂ H z k : ℝ}
    (hH : 0 < H) (hz : 1 ≤ z) (hk : 0 ≤ k)
    (hfirst : M₁ ≤ H * (Real.log (1 + z) + 1) / z)
    (hsecond : H / (4 * z) ≤ M₂)
    (hgain : 32 * k * (Real.log (1 + z) + 1) ≤ z) :
    k * M₁ ≤ z * M₂ / 8 := by
  have hz0 : 0 < z := zero_lt_one.trans_le hz
  have hfrac : k * (Real.log (1 + z) + 1) / z ≤ 1 / 32 := by
    apply (div_le_iff₀ hz0).mpr
    linarith
  calc
    _ ≤ k * (H * (Real.log (1 + z) + 1) / z) := mul_le_mul_of_nonneg_left hfirst hk
    _ = H * (k * (Real.log (1 + z) + 1) / z) := by ring
    _ ≤ H * (1 / 32) := mul_le_mul_of_nonneg_left hfrac hH.le
    _ = z * (H / (4 * z)) / 8 := by field_simp; ring
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsecond hz0.le) (by norm_num)

theorem rationalMass_moment_budget {W R k : ℕ} (hW : 0 < W) (hSq : Squarefree W) (hR : 2 ≤ R)
    {b : ℝ} (hb : 0 < b) (hz : 1 ≤ b * Real.log (R : ℝ))
    (herror : harmonicTransferError W ≤ coprimeHarmonicDensity W * Real.log (R : ℝ) /
      (2 * (1 + b * Real.log (R : ℝ))))
    (hgain : 32 * (k : ℝ) * (Real.log (1 + b * Real.log (R : ℝ)) + 1) ≤
      b * Real.log (R : ℝ)) :
    (k : ℝ) * rationalMass W b R ≤
      (1 / 4) * (b * rationalSquareMass W b R * (Real.log (R : ℝ) / 2)) := by
  let z := b * Real.log (R : ℝ)
  let H := coprimeHarmonicDensity W * Real.log (R : ℝ)
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR)
  have hρ : 0 < coprimeHarmonicDensity W := by
    unfold coprimeHarmonicDensity
    exact div_pos (by exact_mod_cast Nat.totient_pos.mpr hW) (by exact_mod_cast hW)
  have hH : 0 < H := mul_pos hρ hlog
  have hz0 : 0 < z := mul_pos hb hlog
  change 1 ≤ z at hz
  change harmonicTransferError W ≤ H / (2 * (1 + z)) at herror
  have hE : harmonicTransferError W ≤ H / z := herror.trans
    (div_le_div_of_nonneg_left hH.le hz0 (by linarith))
  have hfirst : rationalMass W b R ≤ H * (Real.log (1 + z) + 1) / z := by
    have hh := rationalMass_upper hW hSq (by omega : 1 ≤ R) hb
    have heq : coprimeHarmonicDensity W * (Real.log (1 + b * Real.log (R : ℝ)) / b) =
        H * Real.log (1 + z) / z := by
      unfold H z
      field_simp
    rw [heq] at hh
    exact (hh.trans (add_le_add le_rfl hE)).trans_eq (by ring)
  have hsecond : H / (4 * z) ≤ rationalSquareMass W b R := by
    have hlower := rationalSquareMass_lower hW hSq (by omega : 1 ≤ R) hb.le
    have heq : coprimeHarmonicDensity W * (Real.log (R : ℝ) / (1 + b * Real.log (R : ℝ))) =
        H / (1 + z) := by unfold H z; ring
    rw [heq] at hlower
    have hmain : H / (2 * (1 + z)) ≤ rationalSquareMass W b R := by
      have hsplit : H / (1 + z) = 2 * (H / (2 * (1 + z))) := by field_simp
      rw [hsplit] at hlower
      linarith
    exact (div_le_div_of_nonneg_left hH.le (by positivity : 0 < 2 * (1 + z))
      (by linarith : 2 * (1 + z) ≤ 4 * z)).trans hmain
  have hh := rational_mass_budget_scalar hH hz (Nat.cast_nonneg k) hfirst hsecond hgain
  exact hh.trans_eq (by unfold z; ring)

end Erdos4.FGKMT
