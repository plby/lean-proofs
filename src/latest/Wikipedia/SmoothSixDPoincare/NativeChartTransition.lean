import Wikipedia.SmoothSixDPoincare.NativePointCoordinates
import Wikipedia.SmoothSixDPoincare.LocalDegreeNeighborhoodData

/-!
# Actual centered coordinate transitions for a native diffeomorphism

Compose the original centered chart, the original global diffeomorphism,
and the original target chart inverse. Their partial-diffeomorphism
composition supplies smoothness and the actual invertible derivative.
The whole-ball local-degree construction can then be applied to this
literal coordinate transition inside any prescribed source neighborhood.
-/

noncomputable section

open Set Metric Topology Filter ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.NativeChartTransition

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (x y : M) (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)

def chart : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
  ((NativeParametrization.centered (D := E) x).trans e.toPartialDiffeomorph).trans
    (NativeParametrization.centered (D := E) y).symm

theorem chart_apply (u : E) : chart x y e u =
    (NativeParametrization.centered (D := E) y).symm
      (e (NativeParametrization.centered (D := E) x u)) := rfl

variable (he : e x = y)

include he in
theorem zero_mem_source : (0 : E) ∈ (chart x y e).source := by
  change (0 ∈ (NativeParametrization.centered (D := E) x).source ∧
    NativeParametrization.centered (D := E) x 0 ∈ (univ : Set M)) ∧
      e (NativeParametrization.centered (D := E) x 0) ∈
        (NativeParametrization.centered (D := E) y).target
  refine ⟨⟨NativeParametrization.zero_mem_centered_source x, mem_univ _⟩, ?_⟩
  rw [NativeParametrization.centered_zero, he]
  exact NativeParametrization.mem_centered_target y

include he in
theorem chart_zero : chart x y e (0 : E) = 0 := by
  rw [chart_apply, NativeParametrization.centered_zero, he,
    NativeParametrization.centered_symm_self]

include he in
theorem contDiffAt_chart : ContDiffAt ℝ ∞ (chart x y e) (0 : E) :=
  ((chart x y e).contMDiffOn_toFun.contMDiffAt
    ((chart x y e).open_source.mem_nhds (zero_mem_source x y e he))).contDiffAt

include he in
theorem bijective_derivative : Function.Bijective (fderiv ℝ (chart x y e) (0 : E)) := by
  have h := PartialChart.bijective_mfderiv (chart x y e) (zero_mem_source x y e he)
  rwa [mfderiv_eq_fderiv] at h

variable [FiniteDimensional ℝ E]

def linear : E ≃L[ℝ] E :=
  (LinearEquiv.ofBijective (fderiv ℝ (chart x y e) (0 : E)).toLinearMap
    (bijective_derivative x y e he)).toContinuousLinearEquiv

theorem linear_eq_derivative : (linear x y e he).toContinuousLinearMap =
    fderiv ℝ (chart x y e) (0 : E) := rfl

theorem hasFDerivAt_chart :
    HasFDerivAt (chart x y e) (linear x y e he).toContinuousLinearMap 0 := by
  rw [linear_eq_derivative]
  exact ((contDiffAt_chart x y e he).differentiableAt (by simp)).hasFDerivAt

theorem nonempty_neighborhoodData (W : Set M) (hW : W ∈ 𝓝 x) :
    Nonempty (LocalDegree.NeighborhoodData
      (((NativeParametrization.centered (D := E) y).symm ∘ e) ∘
        NativeParametrization.centered (D := E) x) (linear x y e he)
      ((NativeParametrization.centered (D := E) x).source ∩
        NativeParametrization.centered (D := E) x ⁻¹' W)) := by
  let c := NativeParametrization.centered (D := E) x
  have hc0 : (0 : E) ∈ c.source := NativeParametrization.zero_mem_centered_source x
  have hcx : c 0 = x := NativeParametrization.centered_zero x
  have hc : ContinuousAt c (0 : E) :=
    c.contMDiffOn_toFun.continuousOn.continuousAt (c.open_source.mem_nhds hc0)
  have hs : c.source ∩ c ⁻¹' W ∈ 𝓝 (0 : E) :=
    inter_mem (c.open_source.mem_nhds hc0) (hc (hcx.symm ▸ hW))
  exact LocalDegree.nonempty_neighborhoodData_of_contDiffAt (linear x y e he)
    (hasFDerivAt_chart x y e he) (chart_zero x y e he) hs (contDiffAt_chart x y e he)

end Wikipedia.SmoothSixDPoincare.NativeChartTransition
