import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Smooth parameter dependence of a locally contracting fixed point

This is the Banach-space implicit-function step for the Picard operator.
The derivative in the unknown has norm less than one, so the derivative
of the fixed-point equation is invertible. Both existence of a smooth
solution germ and its identification with any continuous solution are
proved. Applying this to the actual path-space Picard operator remains
a separate construction.
-/

noncomputable section

open Set Function Filter
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SmoothODE

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The local fixed-point germ is smooth and unique under the derivative norm bound. -/
theorem exists_smooth_fixedPoint_germ {F : P × E → E} {p : P} {x : E}
    (hF : ContDiffAt ℝ ∞ F (p, x)) (hfix : F (p, x) = x)
    (hsmall : ‖(fderiv ℝ F (p, x)).comp (ContinuousLinearMap.inr ℝ P E)‖ < 1) :
    ∃ g : P → E, g p = x ∧ ContDiffAt ℝ ∞ g p ∧
      (∀ᶠ q in 𝓝 p, F (q, g q) = g q) ∧
      ∀ᶠ v in 𝓝 (p, x), F v = v.2 ↔ g v.1 = v.2 := by
  let G : P × E → E := fun v => v.2 - F v
  have hG : ContDiffAt ℝ ∞ G (p, x) := contDiffAt_snd.sub hF
  have hdG : HasFDerivAt G (ContinuousLinearMap.snd ℝ P E - fderiv ℝ F (p, x)) (p, x) :=
    (ContinuousLinearMap.snd ℝ P E).hasFDerivAt.sub
      (hF.differentiableAt (by simp)).hasFDerivAt
  have hpartial : (fderiv ℝ G (p, x)).comp (ContinuousLinearMap.inr ℝ P E) =
      1 - (fderiv ℝ F (p, x)).comp (ContinuousLinearMap.inr ℝ P E) := by
    rw [hdG.fderiv]
    ext z
    rfl
  have hinv : ((fderiv ℝ G (p, x)).comp (ContinuousLinearMap.inr ℝ P E)).IsInvertible := by
    rw [hpartial]
    obtain ⟨u, hu⟩ := isUnit_one_sub_of_norm_lt_one hsmall
    exact ⟨ContinuousLinearEquiv.ofUnit u, hu⟩
  let g := hG.implicitFunction (by simp) hinv
  have hgp : g p = x := hG.implicitFunction_apply_self (by simp) hinv
  have hg : ContDiffAt ℝ ∞ g p := hG.contDiffAt_implicitFunction (by simp) hinv
  refine ⟨g, hgp, hg, ?_, ?_⟩
  · filter_upwards [hG.eventually_apply_implicitFunction (by simp) hinv] with q hq
    change g q - F (q, g q) = x - F (p, x) at hq
    rw [hfix, sub_self] at hq
    exact (sub_eq_zero.mp hq).symm
  · filter_upwards [hG.eventually_apply_eq_iff_implicitFunction (by simp) hinv] with v hv
    change (v.2 - F v = x - F (p, x) ↔ g v.1 = v.2) at hv
    rw [hfix, sub_self, sub_eq_zero] at hv
    exact eq_comm.trans hv

/-- Any existing continuous fixed-point selection is the smooth implicit-function germ. -/
theorem contDiffAt_of_continuous_fixedPoint {F : P × E → E} {p : P} {x : E}
    (hF : ContDiffAt ℝ ∞ F (p, x)) (hfix : F (p, x) = x)
    (hsmall : ‖(fderiv ℝ F (p, x)).comp (ContinuousLinearMap.inr ℝ P E)‖ < 1)
    {g : P → E} (hg : ContinuousAt g p) (hgp : g p = x)
    (heq : ∀ᶠ q in 𝓝 p, F (q, g q) = g q) : ContDiffAt ℝ ∞ g p := by
  obtain ⟨ψ, -, hψ, -, huniq⟩ := exists_smooth_fixedPoint_germ hF hfix hsmall
  have hgraph : Tendsto (fun q => (q, g q)) (𝓝 p) (𝓝 (p, x)) := by
    have hh : Tendsto (fun q => (q, g q)) (𝓝 p) (𝓝 (p, g p)) :=
      continuousAt_id.prodMk hg
    rwa [hgp] at hh
  apply hψ.congr_of_eventuallyEq
  filter_upwards [hgraph huniq, heq] with q hq hfixq
  exact ((hq.mp hfixq).symm)

/-- A smooth equation gives one open neighborhood with a smooth fixed-point map. -/
theorem exists_smooth_fixedPoint_neighborhood {F : P × E → E} {p : P} {x : E}
    (hF : ContDiff ℝ ∞ F) (hfix : F (p, x) = x)
    (hsmall : ‖(fderiv ℝ F (p, x)).comp (ContinuousLinearMap.inr ℝ P E)‖ < 1) :
    ∃ (U : Set P) (g : P → E), IsOpen U ∧ p ∈ U ∧ g p = x ∧
      ContDiffOn ℝ ∞ g U ∧ ∀ q ∈ U, F (q, g q) = g q := by
  obtain ⟨g, hgp, hg, heq, -⟩ := exists_smooth_fixedPoint_germ hF.contDiffAt hfix hsmall
  let A (v : P × E) := (fderiv ℝ F v).comp (ContinuousLinearMap.inr ℝ P E)
  have hA : Continuous A := (hF.continuous_fderiv (by simp)).clm_comp continuous_const
  have hgraph : ContinuousAt (fun q => (q, g q)) p := continuousAt_id.prodMk hg.continuousAt
  have hn : ContinuousAt (fun q => ‖A (q, g q)‖) p := (hA.continuousAt.comp hgraph).norm
  have hbase : ‖A (p, g p)‖ < 1 := by simpa only [hgp, A] using hsmall
  have hsmall' : ∀ᶠ q in 𝓝 p, ‖A (q, g q)‖ < 1 := hn (eventually_lt_nhds hbase)
  have hg₁ : ContDiffAt ℝ 1 g p := hg.of_le (by simp)
  have hcont : ∀ᶠ q in 𝓝 p, ContinuousAt g q :=
    (hg₁.eventually (by simp)).mono (fun _ h => h.continuousAt)
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp ((heq.and hsmall').and hcont)
  refine ⟨U, g, hU, hpU, hgp, ?_, fun q hq => (hUsub hq).1.1⟩
  intro q hq
  apply (contDiffAt_of_continuous_fixedPoint hF.contDiffAt (hUsub hq).1.1
    (hUsub hq).1.2 (hUsub hq).2 rfl ?_).contDiffWithinAt
  filter_upwards [hU.mem_nhds hq] with r hr
  exact (hUsub hr).1.1

end Wikipedia.HopfProblem.DegreeCollapse.SmoothODE
