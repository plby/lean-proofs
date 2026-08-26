import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter MeasureTheory Set
open scoped ENNReal

namespace Erdos
namespace Problem520

theorem le_pow_of_rpow_inv_natCast_le {x L : ℝ} {r : ℕ}
    (hx : 0 ≤ x) (hr : 0 < r)
    (h : x ^ (1 / (r : ℝ)) ≤ L) :
    x ≤ L ^ r := by
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hx _) h r
  have hr0 : r ≠ 0 := Nat.ne_of_gt hr
  simpa [one_div, Real.rpow_inv_natCast_pow hx hr0] using! hpow

/-- Conditional Markov in the exact form used after equation (25).  On an
event visible to the old sigma-algebra, a conditional `r`th-moment bound
gives the corresponding joint tail bound. -/
theorem pow_mul_measureReal_inter_le_of_condExp
    {Ω : Type*} {m m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    {U : Ω → ℝ} {E : Set Ω} (hE : MeasurableSet[m] E)
    {r : ℕ} (hr : 0 < r) {B L : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hU : ∀ omega, 0 ≤ U omega)
    (hInt : Integrable (fun omega => U omega ^ r) μ)
    (hcond : μ[(fun omega => U omega ^ r) | m] ≤ᵐ[μ.restrict E]
      fun _ => L ^ r) :
    B ^ r * μ.real ({omega | B ≤ U omega} ∩ E) ≤ L ^ r := by
  have hpow_nonneg : 0 ≤ fun omega => U omega ^ r := fun omega =>
    pow_nonneg (hU omega) r
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ.restrict E) (Eventually.of_forall hpow_nonneg)
    hInt.integrableOn (B ^ r)
  have hset : {omega | B ^ r ≤ U omega ^ r} = {omega | B ≤ U omega} := by
    ext omega
    simpa only [Set.mem_setOf_eq] using!
      (pow_le_pow_iff_left₀ hB (hU omega) (Nat.ne_of_gt hr))
  rw [hset, measureReal_restrict_apply' (hm E hE)] at hmarkov
  refine hmarkov.trans ?_
  calc
    (∫ omega, U omega ^ r ∂μ.restrict E)
        = ∫ omega in E, μ[(fun omega => U omega ^ r) | m] omega ∂μ := by
          symm
          exact setIntegral_condExp hm hInt hE
    _ ≤ ∫ _omega in E, L ^ r ∂μ := by
      exact integral_mono_ae integrable_condExp.integrableOn
        (integrable_const (L ^ r)) hcond
    _ = μ.real E * L ^ r := by simp
    _ ≤ L ^ r := by
      have hmeasure : μ.real E ≤ 1 := measureReal_le_one
      have hmeasure0 : 0 ≤ μ.real E := measureReal_nonneg
      nlinarith [hmeasure, hmeasure0, pow_nonneg hL r]

/-- Ratio form of conditional Markov. -/
theorem measureReal_inter_le_ratio_pow_of_condExp
    {Ω : Type*} {m m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    {U : Ω → ℝ} {E : Set Ω} (hE : MeasurableSet[m] E)
    {r : ℕ} (hr : 0 < r) {B L : ℝ} (hB : 0 < B) (hL : 0 ≤ L)
    (hU : ∀ omega, 0 ≤ U omega)
    (hInt : Integrable (fun omega => U omega ^ r) μ)
    (hcond : μ[(fun omega => U omega ^ r) | m] ≤ᵐ[μ.restrict E]
      fun _ => L ^ r) :
    μ.real ({omega | B ≤ U omega} ∩ E) ≤ (L / B) ^ r := by
  have hmain := pow_mul_measureReal_inter_le_of_condExp hm hE hr hB.le hL
    hU hInt hcond
  rw [div_pow]
  exact (le_div_iff₀ (pow_pos hB r)).mpr (by simpa [mul_comm] using! hmain)

/-- The `2⁻ell` specialization used in equation (26). -/
theorem measureReal_inter_le_two_pow_of_condExp
    {Ω : Type*} {m m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    {U : Ω → ℝ} {E : Set Ω} (hE : MeasurableSet[m] E)
    {ell : ℕ} (hell : 0 < ell) {A B C0 : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hC0 : 0 ≤ C0) (hBC : 2 * C0 ≤ B)
    (hU : ∀ omega, 0 ≤ U omega)
    (hInt : Integrable (fun omega => U omega ^ ell) μ)
    (hcond : μ[(fun omega => U omega ^ ell) | m] ≤ᵐ[μ.restrict E]
      fun _ => (C0 * A) ^ ell) :
    μ.real ({omega | B * A ≤ U omega} ∩ E) ≤ (1 / 2 : ℝ) ^ ell := by
  have htail := measureReal_inter_le_ratio_pow_of_condExp hm hE hell
    (mul_pos hB hA) (mul_nonneg hC0 hA.le) hU hInt hcond
  refine htail.trans ?_
  have hratio : C0 / B ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hB).mpr
    linarith
  have hratio0 : 0 ≤ C0 / B := div_nonneg hC0 hB.le
  have hcancel : (C0 * A) / (B * A) = C0 / B := by
    field_simp
  rw [hcancel]
  exact pow_le_pow_left₀ hratio0 hratio ell

/-- Equation (25) in root-moment form implies equation (26) on any
old-measurable small-energy event. -/
theorem measureReal_inter_le_two_pow_of_condExp_rpow_on_event
    {Ω : Type*} {m m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    {U I : Ω → ℝ} {E : Set Ω} (hE : MeasurableSet[m] E)
    {ell : ℕ} (hell : 0 < ell) {A B C0 : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hC0 : 0 ≤ C0) (hBC : 2 * C0 ≤ B)
    (hU : ∀ omega, 0 ≤ U omega)
    (hI_on : ∀ omega ∈ E, I omega ≤ A)
    (hInt : Integrable (fun omega => U omega ^ ell) μ)
    (hroot : ∀ᵐ omega ∂μ,
      (μ[(fun omega => U omega ^ ell) | m] omega) ^ (1 / (ell : ℝ))
        ≤ C0 * I omega) :
    μ.real ({omega | B * A ≤ U omega} ∩ E) ≤ (1 / 2 : ℝ) ^ ell := by
  have hcondNonneg :
      0 ≤ᵐ[μ] μ[(fun omega => U omega ^ ell) | m] :=
    condExp_nonneg (Eventually.of_forall fun omega => pow_nonneg (hU omega) ell)
  have hcond :
      μ[(fun omega => U omega ^ ell) | m] ≤ᵐ[μ.restrict E]
        fun _ => (C0 * A) ^ ell := by
    filter_upwards [ae_restrict_of_ae hcondNonneg, ae_restrict_of_ae hroot,
      ae_restrict_mem (hm E hE)] with omega hnonneg hmoment hmem
    apply le_pow_of_rpow_inv_natCast_le hnonneg hell
    exact hmoment.trans (mul_le_mul_of_nonneg_left (hI_on omega hmem) hC0)
  exact measureReal_inter_le_two_pow_of_condExp hm hE hell hA hB hC0 hBC
    hU hInt hcond

end Problem520
end Erdos
