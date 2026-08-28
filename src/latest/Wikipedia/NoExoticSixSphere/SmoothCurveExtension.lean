import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Global representatives of locally smooth maps

A map smooth on an open neighborhood has a globally smooth representative
agreeing with it near a specified point. Multiplication by a genuine smooth
cutoff permits the global first-variation theorem to be applied to local
logarithmic coordinates, without any global smoothness assumption on the
chosen logarithm outside its chart.
-/

open Set Filter Metric
open scoped Topology ContDiff

namespace NoExoticSixSphere.SmoothCurveExtension

variable {X F : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_global {f : X → F} {U : Set X} {s : X}
    (hU : IsOpen U) (hs : s ∈ U) (hf : ContDiffOn ℝ ∞ f U) :
    ∃ g : X → F, ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 s] f := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hs)
  let χ : ContDiffBump s :=
    { rIn := ε / 4
      rOut := ε / 2
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  have hsupport : tsupport χ ⊆ U := by
    rw [χ.tsupport_eq]
    intro x hx
    apply hball
    exact lt_of_le_of_lt hx (by change ε / 2 < ε; linarith)
  refine ⟨fun t ↦ χ t • f t, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro t
    by_cases ht : t ∈ U
    · exact χ.contDiff.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds ht))
    · have hχ : χ =ᶠ[𝓝 t] 0 :=
        notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ ht (hsupport h))
      have heq : (fun r ↦ χ r • f r) =ᶠ[𝓝 t] (fun _ ↦ (0 : F)) := by
        filter_upwards [hχ] with r hr
        simp only [hr, Pi.zero_apply, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  · filter_upwards [χ.eventuallyEq_one] with t ht
    simp only [ht, Pi.one_apply, one_smul]

end NoExoticSixSphere.SmoothCurveExtension
