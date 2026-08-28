import Wikipedia.HopfProblem.DegreeCollapseEmbeddedReturnArc
import Mathlib.Algebra.Order.ToIntervalMod

/-!
# Smooth periodic extension from matching endpoint germs

Reduction modulo the period introduces no singularity when the two endpoint
germs agree. Every germ of the extension is an actual translate of a germ
on the fundamental interval, preserving smoothness and immersion.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CircleGluing

variable {N : Type*} {T : ℝ}

def periodicExtension (hT : 0 < T) (f : ℝ → N) (t : ℝ) : N :=
  f (toIcoMod hT 0 t)

theorem periodicExtension_periodic (hT : 0 < T) (f : ℝ → N) :
    Periodic (periodicExtension hT f) T :=
  fun t => congrArg f (toIcoMod_add_right hT 0 t)

theorem periodicExtension_germ_in_fundamental_interval (hT : 0 < T) {f : ℝ → N}
    (hmatch : (fun t => f (t + T)) =ᶠ[𝓝 (0 : ℝ)] f)
    {x : ℝ} (hx : x ∈ Ico (0 : ℝ) T) :
    periodicExtension hT f =ᶠ[𝓝 x] f := by
  by_cases hx0 : x = 0
  · subst x
    filter_upwards [hmatch, Ioo_mem_nhds (neg_lt_zero.mpr hT) hT] with t ht htn
    change f (toIcoMod hT 0 t) = f t
    by_cases ht0 : 0 ≤ t
    · rw [(toIcoMod_eq_self hT).mpr ⟨ht0, by simpa only [zero_add] using htn.2⟩]
    · have hmod : toIcoMod hT 0 t = t + T := by
        apply (toIcoMod_eq_iff hT).mpr
        refine ⟨⟨by linarith [htn.1], by linarith⟩, -1, ?_⟩
        simp
      rw [hmod]
      exact ht
  · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    filter_upwards [Ioo_mem_nhds hxpos hx.2] with t ht
    change f (toIcoMod hT 0 t) = f t
    rw [(toIcoMod_eq_self hT).mpr ⟨ht.1.le, by simpa only [zero_add] using ht.2⟩]

theorem periodicExtension_germ (hT : 0 < T) {f : ℝ → N}
    (hmatch : (fun t => f (t + T)) =ᶠ[𝓝 (0 : ℝ)] f) (x : ℝ) :
    ∃ c : ℝ, x + c ∈ Ico (0 : ℝ) T ∧
      periodicExtension hT f =ᶠ[𝓝 x] (fun t => f (t + c)) := by
  let n : ℤ := toIcoDiv hT 0 x
  let c : ℝ := -(n • T)
  have hx : x + c = toIcoMod hT 0 x := by
    change x - n • T = toIcoMod hT 0 x
    rfl
  have hxc : x + c ∈ Ico (0 : ℝ) T := by
    rw [hx]
    simpa only [zero_add] using toIcoMod_mem_Ico hT 0 x
  have hg := periodicExtension_germ_in_fundamental_interval hT hmatch hxc
  have ht : Tendsto (fun t : ℝ => t + c) (𝓝 x) (𝓝 (x + c)) :=
    (continuous_id.add continuous_const).continuousAt
  refine ⟨c, hxc, ?_⟩
  filter_upwards [hg.comp_tendsto ht] with t ht
  have heq : periodicExtension hT f (t + c) = periodicExtension hT f t :=
    congrArg f (toIcoMod_sub_zsmul hT 0 t n)
  exact heq.symm.trans ht

variable {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
  [TopologicalSpace N] [ChartedSpace H N]

theorem periodicExtension_contMDiff (hT : 0 < T) {f : ℝ → N}
    (hmatch : (fun t => f (t + T)) =ᶠ[𝓝 (0 : ℝ)] f)
    (hf : ∀ t ∈ Ico (0 : ℝ) T, ContMDiffAt 𝓘(ℝ, ℝ) J ∞ f t) :
    ContMDiff 𝓘(ℝ, ℝ) J ∞ (periodicExtension hT f) := by
  intro x
  obtain ⟨c, hc, heq⟩ := periodicExtension_germ hT hmatch x
  exact ((hf (x + c) hc).comp x
    (contMDiff_id.add contMDiff_const).contMDiffAt).congr_of_eventuallyEq heq

theorem periodicExtension_derivative_injective (hT : 0 < T) {f : ℝ → N}
    (hmatch : (fun t => f (t + T)) =ᶠ[𝓝 (0 : ℝ)] f)
    (hf : ∀ t ∈ Ico (0 : ℝ) T, MDifferentiableAt 𝓘(ℝ, ℝ) J f t)
    (hi : ∀ t ∈ Ico (0 : ℝ) T, Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) (x : ℝ) :
    Injective (mfderiv 𝓘(ℝ, ℝ) J (periodicExtension hT f) x) := by
  obtain ⟨c, hc, heq⟩ := periodicExtension_germ hT hmatch x
  rw [heq.mfderiv_eq]
  exact MorseCancellation.injective_mfderiv_curve_translate (hf (x + c) hc) (hi (x + c) hc)

end Wikipedia.HopfProblem.DegreeCollapse.CircleGluing
