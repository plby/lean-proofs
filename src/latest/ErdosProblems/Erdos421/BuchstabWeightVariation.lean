import ErdosProblems.Erdos421.BuchstabPrimeDerivativeBounds
import ErdosProblems.Erdos421.BuchstabWeightRegularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Bounded variation norm for the Buchstab prime weights -/

namespace Erdos421

open MeasureTheory

theorem reciprocalLogSquare_integral_le_one {a b : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (hlog : 1 ≤ Real.log a) : (∫ t in a..b, reciprocalLogSquare t) ≤ 1 := by
  have heq : reciprocalLogSquare = fun t : ℝ ↦ t⁻¹ / (Real.log t) ^ 2 := by
    funext t
    dsimp only [reciprocalLogSquare]
    ring
  rw [heq, integral_inv_div_log_sq ha (ha.trans_le hab)]
  have hlo : 0 ≤ (Real.log b)⁻¹ := inv_nonneg.mpr (Real.log_pos (ha.trans_le hab)).le
  have hhi : (Real.log a)⁻¹ ≤ 1 := (inv_le_one₀ (Real.log_pos ha)).mpr hlog
  linarith

theorem buchstabPrimeWeight_variation_le {X a b K : ℝ} {F : ℝ → ℝ}
    (hX : 1 < X) (ha : 1 < a) (hab : a ≤ b) (hlog : 1 ≤ Real.log a)
    (hK : 0 ≤ K) (hscale : Real.log X ≤ K * Real.log a)
    (hFd : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ F (logarithmicBuchstabArgument X t))
    (hFc : ContinuousOn (fun t ↦ deriv F (logarithmicBuchstabArgument X t)) (Set.Icc a b))
    (hF : ∀ t ∈ Set.Icc a b, |F (logarithmicBuchstabArgument X t)| ≤ 1)
    (hF' : ∀ t ∈ Set.Icc a b, |deriv F (logarithmicBuchstabArgument X t)| ≤ 2) :
    b * |buchstabPrimeWeight X F b| + a * |buchstabPrimeWeight X F a| +
      (∫ t in a..b, t * |deriv (buchstabPrimeWeight X F) t|) ≤ 2 * K + 5 := by
  have hap : 0 < a := by linarith
  have hsub : Set.Icc a b ⊆ Set.Ioi 1 := fun _ ht ↦ ha.trans_le ht.1
  have hlogt : ∀ t ∈ Set.Icc a b, 1 ≤ Real.log t :=
    fun _ ht ↦ hlog.trans (Real.log_le_log hap ht.1)
  have hend : ∀ t ∈ Set.Icc a b, t * |buchstabPrimeWeight X F t| ≤ 1 := by
    intro t ht
    have htp : 0 < t := by have ht1 : 1 < t := hsub ht; linarith
    have hlt := Real.log_pos (hsub ht)
    calc
      _ ≤ t * reciprocalLogSquare t :=
        mul_le_mul_of_nonneg_left (buchstabPrimeWeight_abs_le (hsub ht) (hF t ht)) htp.le
      _ = 1 / (Real.log t) ^ 2 := by dsimp only [reciprocalLogSquare]; field_simp
      _ ≤ 1 := (div_le_one (sq_pos_of_pos hlt)).mpr (one_le_pow₀ (hlogt t ht))
  have hder : ∀ t ∈ Set.Icc a b, t * |deriv (buchstabPrimeWeight X F) t| ≤
      (2 * K + 3) * reciprocalLogSquare t := by
    intro t ht
    have htp : 0 < t := by have ht1 : 1 < t := hsub ht; linarith
    have hlt := Real.log_pos (hsub ht)
    have hs := hscale.trans (mul_le_mul_of_nonneg_left (Real.log_le_log hap ht.1) hK)
    have hd := buchstabPrimeWeight_deriv_abs_le hX (hsub ht) (hlogt t ht) hK hs
      (hFd t ht) (hF t ht) (hF' t ht)
    calc
      _ ≤ t * ((2 * K + 3) / (t ^ 2 * (Real.log t) ^ 2)) :=
        mul_le_mul_of_nonneg_left hd htp.le
      _ = _ := by dsimp only [reciprocalLogSquare]; field_simp
  have hreg := (buchstabPrimeWeight_regular ha hFd hFc).2
  have hm := intervalIntegral.integral_mono_on (μ := volume) hab
    (ContinuousOn.intervalIntegrable_of_Icc hab (continuousOn_id.mul hreg.abs))
    (ContinuousOn.intervalIntegrable_of_Icc hab
      (continuousOn_const.mul (reciprocalLogSquare_continuousOn.mono hsub)))
    (fun t ht ↦ hder t ht)
  dsimp only [Pi.mul_apply, id_eq] at hm
  rw [intervalIntegral.integral_const_mul] at hm
  have hi : (∫ t in a..b, t * |deriv (buchstabPrimeWeight X F) t|) ≤ 2 * K + 3 := by
    exact hm.trans ((mul_le_mul_of_nonneg_left (reciprocalLogSquare_integral_le_one ha hab hlog)
      (by linarith : 0 ≤ 2 * K + 3)).trans_eq (by ring))
  linarith [hend a ⟨le_rfl, hab⟩, hend b ⟨hab, le_rfl⟩]

end Erdos421
