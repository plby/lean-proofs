import ErdosProblems.Erdos4.FGKMTHarmonicModulus
import ErdosProblems.Erdos4.FGKMTRationalMass
import ErdosProblems.Erdos4.FGKMTDistributionCutoffs

/-! Explicit harmonic-error control for the modulus selected by prime excision. -/

namespace Erdos4.FGKMT

theorem log_primorial_le (D : ℕ) : Real.log (primorial D : ℝ) ≤ Real.log 4 * (D : ℝ) := by
  have hh := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg D)
  rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast] at hh
  exact hh

theorem harmonicModulus_log_le (D : ℕ) {B : ℕ} (hB : B = 1 ∨ B.Prime) :
    Real.log (harmonicModulus D B : ℝ) ≤ Real.log 4 * (D : ℝ) + Real.log (B : ℝ) := by
  have hBpos : 0 < B := by rcases hB with rfl | hp; norm_num; exact hp.pos
  unfold harmonicModulus
  split_ifs
  · exact (log_primorial_le D).trans (le_add_of_nonneg_right (Real.log_natCast_nonneg B))
  · rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast (primorial_pos D).ne')
      (by exact_mod_cast hBpos.ne')]
    exact add_le_add (log_primorial_le D) le_rfl

theorem harmonicModulus_log_le_excision (D : ℕ) {B x : ℕ} {a : ℝ}
    (hB : B = 1 ∨ B.Prime) (hBx : B ≤ exponentialConductorCutoff a x) :
    Real.log (harmonicModulus D B : ℝ) ≤
      Real.log 4 * (D : ℝ) + a * Real.sqrt (Real.log (x : ℝ)) := by
  have hBpos : (0 : ℝ) < B := by
    rcases hB with rfl | hp
    · norm_num
    · exact_mod_cast hp.pos
  have hBexp : (B : ℝ) ≤ Real.exp (a * Real.sqrt (Real.log (x : ℝ))) :=
    (show (B : ℝ) ≤ exponentialConductorCutoff a x by exact_mod_cast hBx).trans
      (Nat.floor_le (Real.exp_pos _).le)
  have hlog : Real.log (B : ℝ) ≤ a * Real.sqrt (Real.log (x : ℝ)) := by
    simpa only [Real.log_exp] using Real.log_le_log hBpos hBexp
  exact (harmonicModulus_log_le D hB).trans (add_le_add le_rfl hlog)

theorem harmonicTransferError_excision (D : ℕ) {B x : ℕ} {a : ℝ}
    (hB : B = 1 ∨ B.Prime) (hBx : B ≤ exponentialConductorCutoff a x) :
    harmonicTransferError (harmonicModulus D B) ≤
      2 * (uniformHarmonicConstant + 1) *
        (1 + Real.log 4 * (D : ℝ) + a * Real.sqrt (Real.log (x : ℝ))) := by
  unfold harmonicTransferError
  have hcoef : 0 ≤ 2 * (uniformHarmonicConstant + 1) := by
    have hh := uniformHarmonicConstant_pos
    positivity
  apply mul_le_mul_of_nonneg_left _ hcoef
  have hh := harmonicModulus_log_le_excision D hB hBx
  linarith

end Erdos4.FGKMT
