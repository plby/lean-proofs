import ErdosProblems.Erdos421.BuchstabExtension
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Calculus of the prime weights in the Buchstab induction -/

namespace Erdos421

noncomputable def logarithmicBuchstabArgument (X t : ℝ) : ℝ := Real.log X / Real.log t - 1

noncomputable def reciprocalLogSquare (t : ℝ) : ℝ := 1 / (t * (Real.log t) ^ 2)

noncomputable def buchstabPrimeWeight (X : ℝ) (F : ℝ → ℝ) (t : ℝ) : ℝ :=
  F (logarithmicBuchstabArgument X t) * reciprocalLogSquare t

theorem logarithmicBuchstabArgument_hasDerivAt (X : ℝ) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (logarithmicBuchstabArgument X)
      (-Real.log X / (t * (Real.log t) ^ 2)) t := by
  have htp : 0 < t := by linarith
  have hlog := Real.log_pos ht
  have hd := ((hasDerivAt_const t (Real.log X)).div
    (Real.hasDerivAt_log htp.ne') hlog.ne').sub_const 1
  dsimp only [Pi.div_apply, Pi.sub_apply] at hd
  convert hd using 1 <;> first | rfl | (field_simp; ring)

theorem reciprocalLogSquare_hasDerivAt {t : ℝ} (ht : 1 < t) :
    HasDerivAt reciprocalLogSquare
      (-(Real.log t + 2) / (t ^ 2 * (Real.log t) ^ 3)) t := by
  have htp : 0 < t := by linarith
  have hlog := Real.log_pos ht
  have hden : t * (Real.log t) ^ 2 ≠ 0 := by positivity
  have hd := (hasDerivAt_const t (1 : ℝ)).div
    ((hasDerivAt_id t).mul ((Real.hasDerivAt_log htp.ne').pow 2)) hden
  dsimp only [Pi.mul_apply, Pi.pow_apply, id_eq] at hd
  norm_num only [Nat.reduceSub, Nat.cast_ofNat] at hd
  convert hd using 1 <;> first | rfl | (field_simp; ring)

theorem buchstabPrimeWeight_hasDerivAt {X t : ℝ} {F : ℝ → ℝ} (ht : 1 < t)
    (hF : DifferentiableAt ℝ F (logarithmicBuchstabArgument X t)) :
    HasDerivAt (buchstabPrimeWeight X F)
      (deriv F (logarithmicBuchstabArgument X t) *
          (-Real.log X / (t * (Real.log t) ^ 2)) * reciprocalLogSquare t +
        F (logarithmicBuchstabArgument X t) *
          (-(Real.log t + 2) / (t ^ 2 * (Real.log t) ^ 3))) t := by
  exact (hF.hasDerivAt.comp t (logarithmicBuchstabArgument_hasDerivAt X ht)).mul
    (reciprocalLogSquare_hasDerivAt ht)

theorem logarithmicBuchstabArgument_continuousOn (X : ℝ) :
    ContinuousOn (logarithmicBuchstabArgument X) (Set.Ioi 1) := by
  intro t ht
  exact (logarithmicBuchstabArgument_hasDerivAt X ht).continuousAt.continuousWithinAt

theorem reciprocalLogSquare_continuousOn : ContinuousOn reciprocalLogSquare (Set.Ioi 1) := by
  intro t ht
  exact (reciprocalLogSquare_hasDerivAt ht).continuousAt.continuousWithinAt

end Erdos421
