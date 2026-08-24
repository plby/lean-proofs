import ErdosProblems.Erdos587.AlternativeDensity

/-!
# A lower bound for a quadratic fiber integral

A fixed plateau in the physical weight gives a root interval of length
at least its squared length divided by twice the ambient root scale.
-/

open MeasureTheory
open scoped BigOperators SchwartzMap

namespace Erdos587

lemma quadratic_root_interval_length {w D L α β : ℝ}
    (hL : 0 < L) (hD : 0 < D) (hw : 0 ≤ w) (hα : 0 ≤ α)
    (hαβ : α ≤ β) (hupper : w + D * β ≤ L ^ 2) :
    D * (β - α) / (2 * L) ≤ Real.sqrt (w + D * β) - Real.sqrt (w + D * α) := by
  have ha : 0 ≤ w + D * α := by positivity
  have hab : w + D * α ≤ w + D * β := by nlinarith
  have hb := ha.trans hab
  have hs := Real.sqrt_le_sqrt hab
  have hLa : Real.sqrt (w + D * α) ≤ L :=
    (Real.sqrt_le_iff).mpr ⟨hL.le, hab.trans hupper⟩
  have hLb : Real.sqrt (w + D * β) ≤ L :=
    (Real.sqrt_le_iff).mpr ⟨hL.le, hupper⟩
  have hprod : (Real.sqrt (w + D * β) - Real.sqrt (w + D * α)) *
      (Real.sqrt (w + D * β) + Real.sqrt (w + D * α)) = D * (β - α) := by
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb]
  apply (div_le_iff₀ (by positivity : 0 < 2 * L)).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hs)
    (show 0 ≤ 2 * L - (Real.sqrt (w + D * β) + Real.sqrt (w + D * α)) by linarith)]

lemma quadratic_argument_mem_plateau {w D α β z : ℝ}
    (hD : 0 < D) (hw : 0 ≤ w) (hα : 0 ≤ α) (hαβ : α ≤ β)
    (hz : z ∈ Set.Icc (Real.sqrt (w + D * α)) (Real.sqrt (w + D * β))) :
    (z ^ 2 - w) / D ∈ Set.Icc α β := by
  have ha : 0 ≤ w + D * α := by positivity
  have hb : 0 ≤ w + D * β := by nlinarith
  have hz0 := (Real.sqrt_nonneg (w + D * α)).trans hz.1
  constructor
  · apply (le_div_iff₀ hD).mpr
    nlinarith [Real.sq_sqrt ha,
      pow_le_pow_left₀ (Real.sqrt_nonneg (w + D * α)) hz.1 2]
  · apply (div_le_iff₀ hD).mpr
    nlinarith [Real.sq_sqrt hb, pow_le_pow_left₀ hz0 hz.2 2]

theorem quadratic_fiber_integral_lower (f g : 𝓢(ℝ, ℂ)) {w D L α β : ℝ}
    (hL : 0 < L) (hD : 0 < D) (hw : 0 ≤ w) (hα : 0 ≤ α)
    (hαβ : α ≤ β) (hupper : w + D * β ≤ L ^ 2)
    (hf : ∀ x : ℝ, (f x).im = 0)
    (hfpos : ∀ x : ℝ, 0 ≤ (f x).re) (hgpos : ∀ x : ℝ, 0 ≤ (g x).re)
    (hfplateau : ∀ z ∈ Set.Icc (Real.sqrt (w + D * α)) (Real.sqrt (w + D * β)),
      1 ≤ (f (L⁻¹ * z)).re)
    (hgplateau : ∀ x ∈ Set.Icc α β, 1 ≤ (g x).re) :
    D * (β - α) / (2 * L) ≤
      ∫ z : ℝ, (f (L⁻¹ * z)).re * (g ((z ^ 2 - w) / D)).re := by
  let a := Real.sqrt (w + D * α)
  let b := Real.sqrt (w + D * β)
  let F (z : ℝ) := (f (L⁻¹ * z)).re * (g ((z ^ 2 - w) / D)).re
  have hInt : Integrable F := by
    apply integrable_real_schwartz_weighted_comp f g (inv_pos.mpr hL) _ _ hf
    fun_prop
  have hab : a ≤ b := Real.sqrt_le_sqrt (by nlinarith)
  have hplateau : ∀ z ∈ Set.Icc a b, (1 : ℝ) ≤ F z := by
    intro z hz
    exact one_le_mul_of_one_le_of_one_le (hfplateau z hz)
      (hgplateau _ (quadratic_argument_mem_plateau hD hw hα hαβ hz))
  have hlower := setIntegral_ge_of_const_le_real measurableSet_Icc
    (isCompact_Icc.measure_lt_top.ne) hplateau hInt.integrableOn
  rw [Real.volume_real_Icc_of_le hab, one_mul] at hlower
  calc
    D * (β - α) / (2 * L) ≤ b - a :=
      quadratic_root_interval_length hL hD hw hα hαβ hupper
    _ ≤ ∫ z in Set.Icc a b, F z := hlower
    _ ≤ ∫ z : ℝ, F z := setIntegral_le_integral hInt
      (Filter.Eventually.of_forall (fun z => mul_nonneg (hfpos _) (hgpos _)))

end Erdos587
