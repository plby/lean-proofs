import Wikipedia.SmoothSixDPoincare.SmoothEuclideanLocalFlow
import Wikipedia.SmoothSixDPoincare.StarConvexSmoothExtension

/-!
# Smooth local flows for fields defined on an open coordinate domain

A finite-dimensional smooth extension keeps the original field germ.
The constructed trajectories remain in the region of exact agreement,
so their derivative is the original local field.
-/

noncomputable section

open Set Metric Filter Topology
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_smooth_localFlow_on_open {v : E → E} {U : Set E}
    (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U) {x₀ : E} (hxU : x₀ ∈ U) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ α : E × ℝ → E,
      ContDiffOn ℝ ∞ α (ball x₀ r ×ˢ Ioo (-ε) ε) ∧
      ∀ x ∈ ball x₀ r, α (x, 0) = x ∧
        ∀ t ∈ Ioo (-ε) ε, α (x, t) ∈ U ∧
          HasDerivAt (fun s => α (x, s)) (v (α (x, t))) t := by
  obtain ⟨w, hw, heq⟩ := exists_smooth_extension_near_point hv.contMDiffOn hU hxU
  obtain ⟨V, hVsub, hV, hxV⟩ := _root_.mem_nhds_iff.mp
    (inter_mem heq (hU.mem_nhds hxU))
  obtain ⟨r, hr, ε, hε, α, hαsmooth, hα⟩ :=
    exists_smooth_localFlow_in_open hw.contDiff hV hxV
  refine ⟨r, hr, ε, hε, α, hαsmooth, ?_⟩
  intro x hx
  refine ⟨(hα x hx).1, ?_⟩
  intro t ht
  have h := (hα x hx).2 t ht
  refine ⟨(hVsub h.1).2, ?_⟩
  have hd := h.2
  rwa [(hVsub h.1).1] at hd

end Wikipedia.SmoothSixDPoincare.FlowConstruction
