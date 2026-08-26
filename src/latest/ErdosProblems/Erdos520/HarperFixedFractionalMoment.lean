import ErdosProblems.Erdos520.HarperWeightedAssembly

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open MeasureTheory Set

namespace Erdos
namespace Problem520

/-!
# The fixed `2/3` good--bad moment split

This file records the direct good--bad algebra at the target exponent.  It is
a useful endpoint once the bad event is polynomially small.  In the sharp
Harper route the fair-measure bad event is only exponentially small in the
barrier parameter, so `HarperFractionalRecursion` supplies the genuine
iteration through exponents tending to one.
-/

theorem integral_rpow_twoThird_le_rpow_integral
    {alpha : Type*} [MeasurableSpace alpha] {nu : Measure alpha}
    [IsProbabilityMeasure nu] {Z : alpha -> Real}
    (hZ : Integrable Z nu) (hZnonneg : forall omega, 0 <= Z omega) :
    (integral nu (fun omega => Z omega ^ harperTwoThird)) <=
      (integral nu Z) ^ harperTwoThird := by
  let g : Real -> Real := fun x => x ^ harperTwoThird
  have hZq : Integrable (g ∘ Z) nu := by
    simpa only [g, Function.comp_apply] using!
      integrable_rpow_of_integrable_nonneg hZ hZnonneg
        (by norm_num [harperTwoThird]) (by norm_num [harperTwoThird])
  have hJ :=
    (Real.concaveOn_rpow
      (by norm_num [harperTwoThird])
      (by norm_num [harperTwoThird])).le_map_integral
      (Real.continuous_rpow_const
        (by norm_num [harperTwoThird])).continuousOn
      isClosed_Ici (ae_of_all nu hZnonneg) hZ hZq
  simpa only [g, Function.comp_apply] using! hJ

theorem integralOn_rpow_twoThird_le_rpow_integralOn
    {alpha : Type*} [MeasurableSpace alpha] {nu : Measure alpha}
    [IsProbabilityMeasure nu] {Z : alpha -> Real} {G : Set alpha}
    (hG : MeasurableSet G) (hZ : Integrable Z nu)
    (hZnonneg : forall omega, 0 <= Z omega) :
    (integral (nu.restrict G) (fun omega => Z omega ^ harperTwoThird)) <=
      (integral (nu.restrict G) Z) ^ harperTwoThird := by
  let W : alpha -> Real := G.indicator Z
  have hW : Integrable W nu := hZ.indicator hG
  have hWnonneg : forall omega, 0 <= W omega := by
    intro omega
    by_cases homega : omega ∈ G
    · simp [W, homega, hZnonneg omega]
    · simp [W, homega]
  have h := integral_rpow_twoThird_le_rpow_integral hW hWnonneg
  have hpowIndicator : (fun omega => W omega ^ harperTwoThird) =
      G.indicator (fun omega => Z omega ^ harperTwoThird) := by
    funext omega
    by_cases homega : omega ∈ G
    · simp [W, homega]
    · simp [W, homega, harperTwoThird]
  rw [hpowIndicator, integral_indicator hG] at h
  simpa only [W, integral_indicator hG] using! h

theorem integralOn_compl_rpow_twoThird_le
    {alpha : Type*} [MeasurableSpace alpha] {nu : Measure alpha}
    [IsProbabilityMeasure nu] {Z : alpha -> Real} {G : Set alpha}
    (hG : MeasurableSet G) (hZ : Integrable Z nu)
    (hZnonneg : forall omega, 0 <= Z omega) :
    (integral (nu.restrict Gᶜ) (fun omega => Z omega ^ harperTwoThird)) <=
      (nu.real Gᶜ) ^ ((1 : Real) / 3) *
        (integral nu Z) ^ harperTwoThird := by
  let f : alpha -> Real := Gᶜ.indicator (fun _ => (1 : Real))
  let g : alpha -> Real := fun omega => Z omega ^ harperTwoThird
  have hf_nonneg : 0 ≤ᵐ[nu] f := by
    exact Filter.Eventually.of_forall fun omega => Set.indicator_nonneg
      (fun _ _ => by positivity) omega
  have hg_nonneg : 0 ≤ᵐ[nu] g := by
    exact Filter.Eventually.of_forall fun omega => Real.rpow_nonneg (hZnonneg omega) _
  have hf : MemLp f (ENNReal.ofReal (3 : Real)) nu := by
    exact memLp_indicator_const _ hG.compl (1 : Real)
      (Or.inr (measure_ne_top nu _))
  have hZLp : MemLp Z 1 nu := memLp_one_iff_integrable.mpr hZ
  have hg : MemLp g (ENNReal.ofReal ((3 : Real) / 2)) nu := by
    have hpow := hZLp.norm_rpow_div (ENNReal.ofReal harperTwoThird)
    have hfun : (fun omega => ‖Z omega‖ ^
        (ENNReal.ofReal harperTwoThird).toReal) = g := by
      funext omega
      rw [ENNReal.toReal_ofReal (by norm_num [harperTwoThird])]
      simp only [g, Real.norm_eq_abs, abs_of_nonneg (hZnonneg omega)]
    rw [hfun] at hpow
    have hexponent : ENNReal.ofReal ((3 : Real) / 2) =
        (ENNReal.ofReal harperTwoThird)⁻¹ := by
      rw [show ((3 : Real) / 2) = harperTwoThird⁻¹ by
        norm_num [harperTwoThird], ENNReal.ofReal_inv_of_pos]
      norm_num [harperTwoThird]
    simpa only [hexponent, one_div] using! hpow
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (p := (3 : Real)) (q := (3 : Real) / 2) (μ := nu)
    (Real.holderConjugate_iff.mpr (by norm_num))
    hf_nonneg hg_nonneg hf hg
  have hleft : (integral (nu.restrict Gᶜ)
      (fun omega => Z omega ^ harperTwoThird)) =
      integral nu (fun omega => f omega * g omega) := by
    rw [← integral_indicator hG.compl]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun omega => by
      by_cases homega : omega ∈ Gᶜ
      · simp [f, g, homega]
      · simp [f, g, homega]
  rw [← hleft] at hholder
  have hfint : (integral nu (fun omega => f omega ^ (3 : Real))) =
      nu.real Gᶜ := by
    rw [show (fun omega => f omega ^ (3 : Real)) =
        Gᶜ.indicator (fun _ => (1 : Real)) by
      funext omega
      by_cases homega : omega ∈ Gᶜ <;> simp [f, homega]]
    simp [hG.compl]
  have hgint : (integral nu (fun omega => g omega ^ ((3 : Real) / 2))) =
      integral nu Z := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun omega => by
      simp only [g, harperTwoThird]
      rw [← Real.rpow_mul (hZnonneg omega)]
      norm_num
  rw [hfint, hgint] at hholder
  norm_num at hholder ⊢
  simpa only [harperTwoThird] using! hholder

/-- Fixed-exponent good--bad decomposition.  This is the exact abstract
moment estimate used by the unconditional Problem 520 route. -/
theorem integral_rpow_twoThird_le_of_good_bad
    {alpha : Type*} [MeasurableSpace alpha] {nu : Measure alpha}
    [IsProbabilityMeasure nu] {Z : alpha -> Real} {G : Set alpha}
    (hG : MeasurableSet G) (hZ : Integrable Z nu)
    (hZnonneg : forall omega, 0 <= Z omega)
    {A B epsilon : Real} (hepsilon : 0 <= epsilon)
    (hgood : integral (nu.restrict G) Z <= A)
    (hmean : integral nu Z <= B)
    (hbad : nu.real Gᶜ <= epsilon) :
    integral nu (fun omega => Z omega ^ harperTwoThird) <=
      A ^ harperTwoThird + epsilon ^ ((1 : Real) / 3) *
        B ^ harperTwoThird := by
  have hqnonneg : forall omega, 0 <= Z omega ^ harperTwoThird :=
    fun omega => Real.rpow_nonneg (hZnonneg omega) _
  have hZq : Integrable (fun omega => Z omega ^ harperTwoThird) nu :=
    integrable_rpow_of_integrable_nonneg hZ hZnonneg
      (by norm_num [harperTwoThird]) (by norm_num [harperTwoThird])
  have hsplit : integral nu (fun omega => Z omega ^ harperTwoThird) =
      integral (nu.restrict G) (fun omega => Z omega ^ harperTwoThird) +
        integral (nu.restrict Gᶜ) (fun omega => Z omega ^ harperTwoThird) := by
    have hmeasure : nu.restrict G + nu.restrict Gᶜ = nu :=
      Measure.restrict_add_restrict_compl hG
    calc
      integral nu (fun omega => Z omega ^ harperTwoThird) =
          integral (nu.restrict G + nu.restrict Gᶜ)
            (fun omega => Z omega ^ harperTwoThird) := by rw [hmeasure]
      _ = _ := integral_add_measure hZq.integrableOn hZq.integrableOn
  rw [hsplit]
  apply add_le_add
  · exact (integralOn_rpow_twoThird_le_rpow_integralOn hG hZ hZnonneg).trans
      (Real.rpow_le_rpow (integral_nonneg hZnonneg) hgood
        (by norm_num [harperTwoThird]))
  · have hcompl := integralOn_compl_rpow_twoThird_le hG hZ hZnonneg
    exact hcompl.trans (mul_le_mul
      (Real.rpow_le_rpow measureReal_nonneg hbad (by norm_num))
      (Real.rpow_le_rpow (integral_nonneg hZnonneg) hmean
        (by norm_num [harperTwoThird]))
      (Real.rpow_nonneg (integral_nonneg hZnonneg) _)
      (Real.rpow_nonneg hepsilon _))

end Problem520
end Erdos
