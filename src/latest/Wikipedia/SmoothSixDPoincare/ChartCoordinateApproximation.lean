import Wikipedia.SmoothSixDPoincare.ChartMapPerturbation
import Mathlib.Geometry.Manifold.SmoothApprox

/-!
# Smooth relative approximation of a localized coordinate expression

A target-chart expression is multiplied by a cutoff supported over that
chart. The resulting vector-valued function is globally continuous, even
though the chart is only locally continuous. Euclidean-target smoothing can
then preserve a closed set on whose neighborhood the original map is smooth.
-/

noncomputable section

open Set Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ChartMapPerturbation

variable {E G F H K X N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
  [TopologicalSpace X] [ChartedSpace H X]
  [TopologicalSpace N] [ChartedSpace K N]
  (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (χ : X → ℝ)

/-- The global vector-valued coordinate expression, vanishing off the cutoff support. -/
def cutoffCoordinates (x : X) : F := χ x • c (f x)

omit [TopologicalSpace X] in
theorem cutoffCoordinates_eq_of_one {x : X} (hx : χ x = 1) :
    cutoffCoordinates c f χ x = c (f x) := by simp only [cutoffCoordinates, hx, one_smul]

variable {f χ}

/-- The chart's discontinuous values outside its source are killed on a whole neighborhood. -/
theorem continuous_cutoffCoordinates (hf : Continuous f) (hχ : Continuous χ)
    (hsupport : tsupport χ ⊆ f ⁻¹' c.source) : Continuous (cutoffCoordinates c f χ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.continuousAt.smul
      ((c.contMDiffOn_toFun.continuousOn.continuousAt
        (c.open_source.mem_nhds (hsupport hx))).comp hf.continuousAt)
  · have hz : χ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
    apply (continuousAt_const (y := (0 : F))).congr
    filter_upwards [hz] with y hy
    simp only [cutoffCoordinates, hy, zero_smul, Pi.zero_apply]

/-- Local smoothness of the original map is retained by the cutoff coordinate expression. -/
theorem contMDiffAt_cutoffCoordinates (hsupport : tsupport χ ⊆ f ⁻¹' c.source)
    {x : X} (hf : ContMDiffAt I J ∞ f x) (hχ : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ χ x) :
    ContMDiffAt I 𝓘(ℝ, F) ∞ (cutoffCoordinates c f χ) x := by
  by_cases hx : x ∈ tsupport χ
  · exact hχ.smul ((c.contMDiffOn_toFun.contMDiffAt
      (c.open_source.mem_nhds (hsupport hx))).comp x hf)
  · have hz : χ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
    apply (contMDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    simp only [cutoffCoordinates, hy, zero_smul, Pi.zero_apply]

variable [FiniteDimensional ℝ E] [IsManifold I ∞ X] [SigmaCompactSpace X] [T2Space X]

/-- Approximate actual coordinates smoothly, exactly preserving the prescribed closed set. -/
theorem exists_smooth_coordinate_approximation (hf : Continuous f)
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ) (hsupport : tsupport χ ⊆ f ⁻¹' c.source)
    {C U : Set X} (hC : IsClosed C) (hU : IsOpen U) (hCU : C ⊆ U)
    (hfU : ContMDiffOn I J ∞ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : X → F, ContMDiff I 𝓘(ℝ, F) ∞ g ∧
      (∀ x, dist (g x) (cutoffCoordinates c f χ x) < ε) ∧ EqOn g (cutoffCoordinates c f χ) C := by
  have hk := continuous_cutoffCoordinates c hf hχ.continuous hsupport
  have hkU : ContMDiffOn I 𝓘(ℝ, F) ∞ (cutoffCoordinates c f χ) U := by
    intro x hx
    exact (contMDiffAt_cutoffCoordinates c hsupport
      ((hfU x hx).contMDiffAt (hU.mem_nhds hx)) hχ.contMDiffAt).contMDiffWithinAt
  have hUn : U ∈ 𝓝ˢ C := mem_nhdsSet_iff_forall.mpr (fun x hx => hU.mem_nhds (hCU hx))
  obtain ⟨g, hg, hgeq, _⟩ := hk.exists_contMDiff_approx_and_eqOn I ⊤
    (continuous_const (y := ε)) (fun _ => hε) hC hUn hkU
  exact ⟨g, g.contMDiff, hg, hgeq⟩

end Wikipedia.SmoothSixDPoincare.ChartMapPerturbation
