import Wikipedia.SmoothSixDPoincare.LocalDegreeBoundaryHomology
import Wikipedia.SmoothSixDPoincare.CenteredParametrization

/-!
# Small local-degree boundaries in the original native manifold charts

Center the native chart at the actual regular zero. Its derivative and the
original map's derivative construct the invertible linear model. The small
boundary is then produced inside any prescribed neighborhood of that point.
-/

noncomputable section

open Set Metric Topology Function Filter ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.LocalDegree

variable {E F M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ F] in
/-- The linear model is the actual derivative in the constructed original centered chart. -/
theorem exists_native_boundaryData {f : M → F} (x : M)
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x) (hzero : f x = 0)
    (hA : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).IsInvertible)
    (W : Set M) (hW : W ∈ 𝓝 x) :
    ∃ L : E ≃L[ℝ] F,
      L.toContinuousLinearMap = fderiv ℝ (f ∘ NativeParametrization.centered (D := E) x) 0 ∧
      Nonempty (BoundaryData (f ∘ NativeParametrization.centered (D := E) x) L
        ((NativeParametrization.centered (D := E) x).source ∩
          NativeParametrization.centered (D := E) x ⁻¹' W)) := by
  let c := NativeParametrization.centered (D := E) x
  have hc0 : (0 : E) ∈ c.source := NativeParametrization.zero_mem_centered_source x
  have hcx : c 0 = x := NativeParametrization.centered_zero x
  have hcf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f (c 0) := hcx.symm ▸ hf
  have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c 0 :=
    c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hc0)
  have hcomp : ContDiffAt ℝ ∞ (f ∘ c) 0 := (hcf.comp 0 hc).contDiffAt
  let A : E →L[ℝ] F := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (c 0)
  let C : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c 0
  have hAi : A.IsInvertible := by
    change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (c 0)).IsInvertible
    rw [hcx]
    exact hA
  have hCi : C.IsInvertible :=
    ⟨(LinearEquiv.ofBijective C.toLinearMap
      (PartialChart.bijective_mfderiv c hc0)).toContinuousLinearEquiv, rfl⟩
  have hder : HasFDerivAt (f ∘ c) (A.comp C) 0 :=
    ((hcf.mdifferentiableAt (by simp)).hasMFDerivAt.comp 0
      (hc.mdifferentiableAt (by simp)).hasMFDerivAt).hasFDerivAt
  obtain ⟨L, hL⟩ := hAi.comp hCi
  have hdL : HasFDerivAt (f ∘ c) L.toContinuousLinearMap 0 := hL.symm ▸ hder
  have hs : c.source ∩ c ⁻¹' W ∈ 𝓝 (0 : E) :=
    inter_mem (c.open_source.mem_nhds hc0) (hc.continuousAt (hcx.symm ▸ hW))
  refine ⟨L, hdL.fderiv.symm, ?_⟩
  apply nonempty_boundaryData_of_contDiffAt L hdL _ hs hcomp
  change f (c 0) = 0
  rw [hcx]
  exact hzero

end Wikipedia.SmoothSixDPoincare.LocalDegree
