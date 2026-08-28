import Wikipedia.SmoothSixDPoincare.NativeLocalDegreeBoundary
import Wikipedia.SmoothSixDPoincare.LocalDegreeNeighborhoodData

/-!
# Regular-zero neighborhoods constructed in the original centered native chart

The existing native linearization provides the actual invertible coordinate
derivative. Its full-ball remainder estimate constructs a neighborhood with
only the original zero and a strictly interior local-degree boundary.
-/

noncomputable section

open Set Metric Topology Filter ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.LocalDegree

variable {E F M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem exists_native_neighborhoodData {f : M → F} (x : M)
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x) (hzero : f x = 0)
    (hA : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).IsInvertible)
    (W : Set M) (hW : W ∈ 𝓝 x) :
    ∃ L : E ≃L[ℝ] F,
      L.toContinuousLinearMap = fderiv ℝ (f ∘ NativeParametrization.centered (D := E) x) 0 ∧
      Nonempty (NeighborhoodData (f ∘ NativeParametrization.centered (D := E) x) L
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' W)) := by
  obtain ⟨L, hL, _⟩ := exists_native_boundaryData x hf hzero hA W hW
  let c := NativeParametrization.centered (D := E) x
  have hc0 : (0 : E) ∈ c.source := NativeParametrization.zero_mem_centered_source x
  have hcx : c 0 = x := NativeParametrization.centered_zero x
  have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c 0 :=
    c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hc0)
  have hcf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f (c 0) := hcx.symm ▸ hf
  have hcomp : ContDiffAt ℝ ∞ (f ∘ c) 0 := (hcf.comp 0 hc).contDiffAt
  have hd : HasFDerivAt (f ∘ c) L.toContinuousLinearMap 0 := by
    rw [hL]
    exact (hcomp.differentiableAt (by simp)).hasFDerivAt
  have hs : c.source ∩ c ⁻¹' W ∈ 𝓝 (0 : E) :=
    inter_mem (c.open_source.mem_nhds hc0) (hc.continuousAt (hcx.symm ▸ hW))
  refine ⟨L, hL, nonempty_neighborhoodData_of_contDiffAt L hd ?_ hs hcomp⟩
  change f (c 0) = 0
  rw [hcx]
  exact hzero

end Wikipedia.SmoothSixDPoincare.LocalDegree
