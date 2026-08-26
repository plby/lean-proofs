import ErdosProblems.Erdos1002.GaussPrefixLateMeasurability

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Monotonicity of denominator-good prefix events in the cutoff depth

Passing a simultaneous denominator bound at a deeper cutoff implies
passing the same bound at every shallower cutoff.  Because selected
continued-fraction words have a null terminating exceptional set, the
event inclusion is stated under both measures actually used in the late
argument.
-/

open Filter MeasureTheory Set

namespace Erdos1002

noncomputable section

/-- A deeper prefix-good event is almost surely contained in the
corresponding shallower event under the original uniform law. -/
theorem gaussDenominatorPrefixGoodEvent_ae_mono_uniform
    {d b L : ℕ} {Delta : ℝ} (hdb : d ≤ b) :
    gaussDenominatorPrefixGoodEvent b L Delta
      ≤ᵐ[uniform01Measure]
        gaussDenominatorPrefixGoodEvent d L Delta := by
  filter_upwards [ae_nonterminating_uniform01] with x hx
  intro hxb
  apply
    (mem_gaussDenominatorPrefixGoodEvent_iff
      hx.1 hx.2).2
  have hdeep :=
    (mem_gaussDenominatorPrefixGoodEvent_iff
      hx.1 hx.2).1 hxb
  intro n hn
  exact hdeep n (hn.trans hdb)

/-- The same cutoff monotonicity under Gauss measure. -/
theorem gaussDenominatorPrefixGoodEvent_ae_mono_gauss
    {d b L : ℕ} {Delta : ℝ} (hdb : d ≤ b) :
    gaussDenominatorPrefixGoodEvent b L Delta
      ≤ᵐ[gaussMeasure]
        gaussDenominatorPrefixGoodEvent d L Delta := by
  filter_upwards [ae_nonterminating_gaussMeasure] with x hx
  intro hxb
  apply
    (mem_gaussDenominatorPrefixGoodEvent_iff
      hx.1 (by simpa only [gaussOrbit] using! hx.2)).2
  have hdeep :=
    (mem_gaussDenominatorPrefixGoodEvent_iff
      hx.1 (by simpa only [gaussOrbit] using! hx.2)).1 hxb
  intro n hn
  exact hdeep n (hn.trans hdb)

end

end Erdos1002
