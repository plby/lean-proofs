import ErdosProblems.Erdos4.FGKMTFaceTuples
import Mathlib.Data.Nat.Sqrt

/-! An explicit face radius satisfying both the product cutoff and the logarithmic lower bound. -/

namespace Erdos4.FGKMT

def sieveFaceRadius (R : ℕ) : ℕ := Nat.sqrt R

theorem sieveFaceRadius_sq_le (R : ℕ) : sieveFaceRadius R ^ 2 ≤ R := Nat.sqrt_le' R

theorem sieveFaceRadius_le (R : ℕ) : sieveFaceRadius R ≤ R := Nat.sqrt_le_self R

theorem sieveFaceRadius_ge_four {R : ℕ} (hR : 16 ≤ R) : 4 ≤ sieveFaceRadius R := by
  apply Nat.le_sqrt'.mpr
  norm_num
  exact hR

theorem sieveFaceRadius_cube_ge {R : ℕ} (hR : 16 ≤ R) : R ≤ sieveFaceRadius R ^ 3 := by
  have hT := sieveFaceRadius_ge_four hR
  have hs : R < (sieveFaceRadius R + 1) ^ 2 := Nat.lt_succ_sqrt' R
  have hpow : 4 * sieveFaceRadius R ^ 2 ≤ sieveFaceRadius R ^ 3 := by
    have hh := Nat.mul_le_mul_right (sieveFaceRadius R ^ 2) hT
    nlinarith
  nlinarith

theorem sieveFaceRadius_log_lower {R : ℕ} (hR : 16 ≤ R) :
    Real.log (R : ℝ) / 3 ≤ Real.log (sieveFaceRadius R : ℝ) := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  have hcube : (R : ℝ) ≤ (sieveFaceRadius R : ℝ) ^ 3 := by
    exact_mod_cast sieveFaceRadius_cube_ge hR
  have hh := Real.log_le_log hRpos hcube
  rw [Real.log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  linarith

end Erdos4.FGKMT
