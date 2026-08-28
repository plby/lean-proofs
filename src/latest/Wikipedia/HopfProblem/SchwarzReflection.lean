import Wikipedia.HopfProblem.SchwarzReflectionMorera
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Schwarz reflection across a straight boundary

Continuous holomorphic maps with real boundary values extend by conjugation.
The unit-circle version extends by reciprocal conjugation.  Both assertions
use the proved Morera gluing theorem, so no derivative at the boundary is
assumed.  These lemmas do not supply continuity of an arbitrary Riemann map
at its boundary; that is a separate extension problem.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology ComplexConjugate

namespace Wikipedia.HopfProblem.SchwarzReflection

/-- Paste the upper and lower functions, keeping the upper value on the axis. -/
def pasteUpper (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  if 0 ≤ z.im then f z else g z

@[simp] theorem pasteUpper_of_nonneg (f g : ℂ → ℂ) {z : ℂ} (hz : 0 ≤ z.im) :
    pasteUpper f g z = f z := if_pos hz

@[simp] theorem pasteUpper_of_neg (f g : ℂ → ℂ) {z : ℂ} (hz : z.im < 0) :
    pasteUpper f g z = g z := if_neg (not_le.mpr hz)

theorem continuousOn_pasteUpper {U : Set ℂ} {f g : ℂ → ℂ}
    (hf : ContinuousOn f (U ∩ {z | 0 ≤ z.im}))
    (hg : ContinuousOn g (U ∩ {z | z.im ≤ 0}))
    (hfg : ∀ z ∈ U, z.im = 0 → f z = g z) :
    ContinuousOn (pasteUpper f g) U := by
  change ContinuousOn (fun z => if 0 ≤ z.im then f z else g z) U
  apply ContinuousOn.if
  · intro z hz
    exact hfg z hz.1 ((frontier_le_subset_eq continuous_const continuous_im hz.2).symm)
  · simpa only [closure_le_eq continuous_const continuous_im] using hf
  · apply hg.mono
    intro z hz
    refine ⟨hz.1, ?_⟩
    apply closure_lt_subset_le continuous_im continuous_const
    simpa only [not_le] using hz.2

/-- Holomorphic functions on two half-domains glue across their common
real boundary whenever their continuous boundary traces agree. -/
theorem analyticOnNhd_pasteUpper {U : Set ℂ} (hU : IsOpen U) {f g : ℂ → ℂ}
    (hfc : ContinuousOn f (U ∩ {z | 0 ≤ z.im}))
    (hgc : ContinuousOn g (U ∩ {z | z.im ≤ 0}))
    (hfd : ∀ z ∈ U, 0 < z.im → DifferentiableAt ℂ f z)
    (hgd : ∀ z ∈ U, z.im < 0 → DifferentiableAt ℂ g z)
    (hfg : ∀ z ∈ U, z.im = 0 → f z = g z) :
    AnalyticOnNhd ℂ (pasteUpper f g) U := by
  apply analyticOnNhd_of_continuousOn_off_real hU
    (continuousOn_pasteUpper hfc hgc hfg)
  intro z hz hn
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · apply (hgd z hz hneg).congr_of_eventuallyEq
    filter_upwards [continuous_im.continuousAt.eventually_lt continuousAt_const hneg] with w hw
    exact pasteUpper_of_neg f g hw
  · apply (hfd z hz hpos).congr_of_eventuallyEq
    filter_upwards [continuousAt_const.eventually_lt continuous_im.continuousAt hpos] with w hw
    exact pasteUpper_of_nonneg f g hw.le

/-- The literal Schwarz-reflected function. -/
def realReflect (f : ℂ → ℂ) : ℂ → ℂ :=
  pasteUpper f (fun z => conj (f (conj z)))

theorem continuousOn_conjugate_lower {U : Set ℂ} {f : ℂ → ℂ}
    (hUc : ∀ z ∈ U, conj z ∈ U)
    (hf : ContinuousOn f (U ∩ {z | 0 ≤ z.im})) :
    ContinuousOn (fun z => conj (f (conj z))) (U ∩ {z | z.im ≤ 0}) := by
  apply continuous_conj.continuousOn.comp
  · apply hf.comp continuous_conj.continuousOn
    intro z hz
    exact ⟨hUc z hz.1, by simpa only [mem_ofPred_eq, conj_im, neg_nonneg] using hz.2⟩
  · exact mapsTo_univ _ _

/-- **Schwarz reflection principle**, with the actual conjugation formula. -/
theorem analyticOnNhd_realReflect {U : Set ℂ} (hU : IsOpen U)
    (hUc : ∀ z ∈ U, conj z ∈ U) {f : ℂ → ℂ}
    (hfc : ContinuousOn f (U ∩ {z | 0 ≤ z.im}))
    (hfd : ∀ z ∈ U, 0 < z.im → DifferentiableAt ℂ f z)
    (hreal : ∀ z ∈ U, z.im = 0 → (f z).im = 0) :
    AnalyticOnNhd ℂ (realReflect f) U := by
  apply analyticOnNhd_pasteUpper hU hfc (continuousOn_conjugate_lower hUc hfc) hfd
  · intro z hz hneg
    have h := (hfd (conj z) (hUc z hz) (by simpa using hneg)).conj_conj
    simpa only [Function.comp_def, starRingEnd_self_apply] using h
  · intro z hz hzero
    rw [conj_eq_iff_im.mpr hzero, conj_eq_iff_im.mpr (hreal z hz hzero)]

@[simp] theorem realReflect_eq_of_nonneg (f : ℂ → ℂ) {z : ℂ} (hz : 0 ≤ z.im) :
    realReflect f z = f z := pasteUpper_of_nonneg _ _ hz

theorem realReflect_conj {U : Set ℂ} {f : ℂ → ℂ}
    (hreal : ∀ z ∈ U, z.im = 0 → (f z).im = 0) {z : ℂ} (hz : z ∈ U) :
    realReflect f (conj z) = conj (realReflect f z) := by
  rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
  · simp only [realReflect, pasteUpper_of_neg _ _ hneg,
      pasteUpper_of_nonneg _ _ (show 0 ≤ (conj z).im by simpa using hneg.le),
      starRingEnd_self_apply]
  · rw [conj_eq_iff_im.mpr hzero, realReflect_eq_of_nonneg f (le_of_eq hzero.symm),
      conj_eq_iff_im.mpr (hreal z hz hzero)]
  · rw [realReflect_eq_of_nonneg f hpos.le]
    change pasteUpper f (fun w => conj (f (conj w))) (conj z) = conj (f z)
    rw [pasteUpper_of_neg _ _ (show (conj z).im < 0 by simpa using hpos)]
    simp

/-- Reflection in the unit circle on the target. -/
def circleReflect (f : ℂ → ℂ) : ℂ → ℂ :=
  pasteUpper f (fun z => (conj (f (conj z)))⁻¹)

/-- The unit-circle reflection principle.  Nonvanishing is required only
on the upper half-domain where the original function is evaluated. -/
theorem analyticOnNhd_circleReflect {U : Set ℂ} (hU : IsOpen U)
    (hUc : ∀ z ∈ U, conj z ∈ U) {f : ℂ → ℂ}
    (hfc : ContinuousOn f (U ∩ {z | 0 ≤ z.im}))
    (hfd : ∀ z ∈ U, 0 < z.im → DifferentiableAt ℂ f z)
    (hnz : ∀ z ∈ U, 0 ≤ z.im → f z ≠ 0)
    (hcircle : ∀ z ∈ U, z.im = 0 → ‖f z‖ = 1) :
    AnalyticOnNhd ℂ (circleReflect f) U := by
  have hcnz : ∀ z ∈ U, z.im ≤ 0 → conj (f (conj z)) ≠ 0 := by
    intro z hz hle hzero
    apply hnz (conj z) (hUc z hz) (by simpa using hle)
    simpa using congrArg (conj : ℂ → ℂ) hzero
  apply analyticOnNhd_pasteUpper hU hfc
    ((continuousOn_conjugate_lower hUc hfc).inv₀ (fun z hz => hcnz z hz.1 hz.2)) hfd
  · intro z hz hneg
    have h := (hfd (conj z) (hUc z hz) (by simpa using hneg)).conj_conj
    have h' : DifferentiableAt ℂ (fun w => conj (f (conj w))) z := by
      simpa only [Function.comp_def, starRingEnd_self_apply] using h
    exact h'.inv (hcnz z hz hneg.le)
  · intro z hz hzero
    change f z = (conj (f (conj z)))⁻¹
    rw [conj_eq_iff_im.mpr hzero, ← inv_eq_conj (hcircle z hz hzero), inv_inv]

@[simp] theorem circleReflect_eq_of_nonneg (f : ℂ → ℂ) {z : ℂ} (hz : 0 ≤ z.im) :
    circleReflect f z = f z := pasteUpper_of_nonneg _ _ hz

end Wikipedia.HopfProblem.SchwarzReflection
