import Util.Bernays.CharacterKernelLimit
import Util.Bernays.CharacterNormLimit
import Util.Bernays.WirsingRecurrence
import Util.Bernays.Normalization

/-!
# Exact counting asymptotic for quadratic-character local conditions

This counts positive integers in which each prime with character value `-1`
has even valuation. The result concerns local conditions; representing a number
by a specified quadratic form requires the separate form-class argument.
-/

open Filter Topology Real Asymptotics
open scoped Classical

namespace Bernays

theorem localParity_ordinarySum_limit {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ₂ : χ ^ 2 = 1) (hχ : χ ≠ 1) :
    Tendsto (fun N : ℕ => ordinarySum (localParity (fun p : ℕ => χ p = -1)) N /
      ((N : ℝ) / sqrt (log (N : ℝ)))) atTop (𝓝 (characterLocalConstant χ / sqrt π)) := by
  have hH : Tendsto (fun N : ℕ => reciprocalSum (localParity (fun p : ℕ => χ p = -1)) N /
      sqrt (log (N : ℝ))) atTop (𝓝 (2 * characterLocalConstant χ / sqrt π)) := by
    simpa only [Function.comp_def, Nat.floor_natCast] using
      (localParity_reciprocal_asymptotic χ hχ₂ hχ).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hC := (characterLocalConstant_pos χ hχ).le
  have h := ordinarySum_asymptotic_of_recurrence (localParity_nonneg _) (localParity_le_one _)
    (localParity_logarithmic_convolution _) (by positivity : 0 ≤ 2 * characterLocalConstant χ / sqrt π)
    (localLogMass_div_tendsto_half χ hχ₂ hχ) hH
  have heq : (1 / 2 : ℝ) * (2 * characterLocalConstant χ / sqrt π) =
      characterLocalConstant χ / sqrt π := by ring
  rwa [heq] at h

theorem localParity_ordinarySum_isEquivalent {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ₂ : χ ^ 2 = 1) (hχ : χ ≠ 1) :
    (fun N : ℕ => ordinarySum (localParity (fun p : ℕ => χ p = -1)) N) ~[atTop]
      (fun N : ℕ => (characterLocalConstant χ / sqrt π) * (N : ℝ) / sqrt (log (N : ℝ))) := by
  have hC : characterLocalConstant χ / sqrt π ≠ 0 :=
    (div_pos (characterLocalConstant_pos χ hχ) (sqrt_pos.mpr pi_pos)).ne'
  apply isEquivalent_of_tendsto_one
  have h := (localParity_ordinarySum_limit χ hχ₂ hχ).div_const (characterLocalConstant χ / sqrt π)
  rw [div_self hC] at h
  apply h.congr'
  exact Filter.Eventually.of_forall fun N => by
    change ordinarySum (localParity (fun p : ℕ => χ p = -1)) N /
      ((N : ℝ) / sqrt (log (N : ℝ))) / (characterLocalConstant χ / sqrt π) =
      ordinarySum (localParity (fun p : ℕ => χ p = -1)) N /
        ((characterLocalConstant χ / sqrt π) * (N : ℝ) / sqrt (log (N : ℝ)))
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring

noncomputable def localCount (S : ℕ → Prop) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter fun n => ParityAdmissible S n).card

theorem localCount_eq_ordinarySum (S : ℕ → Prop) (N : ℕ) :
    (localCount S N : ℝ) = ordinarySum (localParity S) N := by
  rw [localCount, ordinarySum, ← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro n hn
  have hn₀ : 0 < n := by have := (Finset.mem_Icc.mp hn).1; omega
  simp only [localParity, hn₀, true_and]

theorem localCount_isEquivalent {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ₂ : χ ^ 2 = 1) (hχ : χ ≠ 1) :
    (fun x : ℝ => (localCount (fun p : ℕ => χ p = -1) ⌊x⌋₊ : ℝ)) ~[atTop]
      (fun x : ℝ => (characterLocalConstant χ / sqrt π) * x / sqrt (log x)) := by
  have h := (localParity_ordinarySum_isEquivalent χ hχ₂ hχ).comp_tendsto
    (tendsto_nat_floor_atTop (α := ℝ))
  have h' := h.trans (constant_scale_natFloor_isEquivalent (characterLocalConstant χ / sqrt π))
  simpa only [localCount_eq_ordinarySum, Function.comp_def] using h'

end Bernays
