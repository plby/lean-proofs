import Wikipedia.HopfProblem.DegreeCollapseNativeFieldTransition
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The actual transverse map and time phase of a vertical transition

Unit vertical derivative makes the transverse coordinate constant along
each time line and the time displacement constant along that line. A
constructed open product neighborhood therefore gives an exact smooth
transverse map and scalar phase, not only their derivatives at the axis.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The transition equals a transverse map plus a transverse-dependent
time translation on any connected open time interval in its domain. -/
theorem vertical_transition_formula
    (R : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, ℝ × Z) (ℝ × Z) (ℝ × Z) ∞)
    (hvertical : ∀ p ∈ R.source, fderiv ℝ R p (1, 0) = (1, 0))
    {I : Set ℝ} (hI : IsOpen I) (hconn : IsPreconnected I) {U : Set Z}
    (hsub : I ×ˢ U ⊆ R.source) {t₀ t : ℝ} (h₀ : t₀ ∈ I) (ht : t ∈ I)
    {z : Z} (hz : z ∈ U) :
    R (t, z) = (t + ((R (t₀, z)).1 - t₀), (R (t₀, z)).2) := by
  let γ : ℝ → ℝ × Z := fun s => R (s, z) - (s, 0)
  have hd (s : ℝ) (hs : s ∈ I) : HasDerivAt γ 0 s := by
    have hp := hsub (show (s, z) ∈ I ×ˢ U from ⟨hs, hz⟩)
    have hR := (R.contMDiffOn_toFun.contDiffOn.contDiffAt
      (R.open_source.mem_nhds hp)).differentiableAt (by simp)
    have hh := hR.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s z))
    have hh' : HasDerivAt (fun u => R (u, z)) (1, (0 : Z)) s := by
      convert! hh using 1
      exact (hvertical (s, z) hp).symm
    have hdiff := hh'.sub ((hasDerivAt_id s).prodMk (hasDerivAt_const s (0 : Z)))
    convert! hdiff using 1 <;> simp [γ]
  have heq : γ t = γ t₀ := hI.is_const_of_deriv_eq_zero hconn
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hd s hs).deriv) ht h₀
  apply Prod.ext
  · have hh : (R (t, z)).1 - t = (R (t₀, z)).1 - t₀ := congrArg Prod.fst heq
    linarith
  · have hh : (R (t, z)).2 - 0 = (R (t₀, z)).2 - 0 := congrArg Prod.snd heq
    simpa only [sub_zero] using hh

/-- A constructed product neighborhood contains the exact smooth phase
and transverse map of the actual vertical coordinate transition. -/
theorem exists_vertical_transition_phase
    (R : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, ℝ × Z) (ℝ × Z) (ℝ × Z) ∞)
    (hvertical : ∀ p ∈ R.source, fderiv ℝ R p (1, 0) = (1, 0))
    {t₀ : ℝ} (hp : (t₀, (0 : Z)) ∈ R.source) (hfix : R (t₀, 0) = (t₀, 0)) :
    ∃ (ε : ℝ) (P : Z → Z) (v : Z → ℝ), 0 < ε ∧
      ContDiffOn ℝ ∞ P (ball 0 ε) ∧ ContDiffOn ℝ ∞ v (ball 0 ε) ∧ P 0 = 0 ∧ v 0 = 0 ∧
      Ioo (t₀ - ε) (t₀ + ε) ×ˢ ball (0 : Z) ε ⊆ R.source ∧
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), ∀ z ∈ ball (0 : Z) ε,
        R (t, z) = (t + v z, P z) := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (R.open_source.mem_nhds hp)
  have hsub : Ioo (t₀ - ε) (t₀ + ε) ×ˢ ball (0 : Z) ε ⊆ R.source := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    apply hball
    rw [← ball_prod_same]
    refine ⟨?_, hz⟩
    rw [mem_ball, Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  let P : Z → Z := fun z => (R (t₀, z)).2
  let v : Z → ℝ := fun z => (R (t₀, z)).1 - t₀
  have hc : ContDiffOn ℝ ∞ (fun z : Z => R (t₀, z)) (ball 0 ε) :=
    R.contMDiffOn_toFun.contDiffOn.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun z hz => hsub ⟨ht₀, hz⟩)
  refine ⟨ε, P, v, hε, contDiff_snd.comp_contDiffOn hc,
    (contDiff_fst.comp_contDiffOn hc).sub contDiffOn_const, ?_, ?_, hsub, ?_⟩
  · change (R (t₀, 0)).2 = 0
    rw [hfix]
  · change (R (t₀, 0)).1 - t₀ = 0
    rw [hfix, sub_self]
  · intro t ht z hz
    exact vertical_transition_formula R hvertical isOpen_Ioo isPreconnected_Ioo hsub ht₀ ht hz

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
