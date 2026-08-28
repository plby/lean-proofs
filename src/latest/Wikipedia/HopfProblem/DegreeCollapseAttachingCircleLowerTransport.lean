import Wikipedia.HopfProblem.DegreeCollapseEmbeddedLevelTransport
import Wikipedia.HopfProblem.DegreeCollapseCircleStandardParametrization

/-!
# Transporting an actual attaching circle to a lower critical-value cut

The native attaching basin gives the backward endpoint. Every forward
endpoint has smaller critical value and hence lies below the chosen cut.
Actual complete-flow crossing then transports the entire embedded immersive
attaching circle into the original regular level, with exact inverse data.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.attachingSphere_reaches_lower_cut
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) {a : ℝ} (hap : a < f p)
    (hgap : ∀ q : criticalPoints E f, f q < f p → f q < a)
    (u : sphere (0 : (S.data p).chart.NegativeCoordinates) 1) :
    ((S.data p).surgery.attachingSphere u).val ∈ FlowCancellation.levelBasin S.flow f a := by
  let x := (S.data p).surgery.attachingSphere u
  have hback := (S.attaching_basin_iff hf p x).mpr ⟨u, rfl⟩
  obtain ⟨r, hr, q, hq, -, hforward, hheights⟩ := FlowCancellation.exists_native_descent_endpoints
    hf S.smooth S.flow S.integral S.zero S.descent S.distinct x.val
  have hxreg : x.val ∉ criticalPoints E f := (S.data p).lower_regular x.val x.property
  have hxp : f x.val < f p := by
    have hh := x.property
    change f x.val = f p - (S.data p).radius ^ 2 at hh
    rw [hh]
    nlinarith [(S.data p).radius_pos]
  have hqa : f q < a := hgap ⟨q, hq⟩ ((hheights hxreg).1.trans hxp)
  exact FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous
    hback hforward hap hqa

open Classical in
theorem AdaptedSurgeryWindows.exists_attaching_circle_lower_transport
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f)
    [Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 1 + 1)]
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f) (hap : a < f p)
    (hgap : ∀ q : criticalPoints E f, f q < f p → f q < a) :
    let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
    let _ := RegularLevel.chartedSpace hf ha
    ∃ e : Diffeomorph (𝓡 1) (𝓡 1) (Hemisphere.Sphere 1)
        (sphere (0 : (S.data p).chart.NegativeCoordinates) 1) ∞,
      ∃ D : PartialDiffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
          (S.data p).LowerLevel {y : M // f y = a} ∞,
        D.source = {x | x.val ∈ FlowCancellation.levelBasin S.flow f a} ∧
        D.target = {y | y.val ∈ FlowCancellation.levelBasin S.flow f (S.toSurgeryWindows.lower p)} ∧
        ∃ Γ : C(Hemisphere.Sphere 1, {y : M // f y = a}),
          ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ Γ ∧ Injective Γ ∧
          (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) Γ z)) ∧
          (∀ z, D ((S.data p).surgery.attachingSphere (e z)) = Γ z) ∧
          (∀ z, D.symm (Γ z) = (S.data p).surgery.attachingSphere (e z)) ∧
          ∀ z, ∃ t : ℝ, S.flow t ((S.data p).surgery.attachingSphere (e z)).val = (Γ z).val := by
  let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.isManifold hf (S.data p).lower_regular
  let _ := RegularLevel.isManifold hf ha
  let e := SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates 1
  let γ : C(Hemisphere.Sphere 1, (S.data p).LowerLevel) :=
    ⟨(S.data p).surgery.attachingSphere ∘ e,
      ((S.data p).attaching_smooth hf 1).continuous.comp e.continuous⟩
  have hγ : ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ :=
    ((S.data p).attaching_smooth hf 1).comp e.contMDiff
  have hγi : Injective γ := (S.data p).attaching_isClosedEmbedding.injective.comp e.injective
  have hγd : ∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z) := by
    intro z
    change Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E)
      ((S.data p).surgery.attachingSphere ∘ e) z)
    rw [mfderiv_comp z (((S.data p).attaching_smooth hf 1).mdifferentiableAt (by simp))
      (e.contMDiff.mdifferentiableAt (by simp))]
    exact ((S.data p).attaching_derivative_injective hf 1 (e z)).comp
      (e.mfderivToContinuousLinearEquiv (by simp) z).injective
  have hreach (z : Hemisphere.Sphere 1) : (γ z).val ∈ FlowCancellation.levelBasin S.flow f a :=
    S.attachingSphere_reaches_lower_cut hf p hap hgap (e z)
  obtain ⟨D, hsource, htarget, Γ, hΓ, hΓi, hΓd, hD, hiD, hflow⟩ :=
    S.exists_embedded_level_transport hf (S.data p).lower_regular ha γ
      (standardCircleParametrization.symm (1 : Circle)) hγ hγi hγd hreach
  exact ⟨e, D, hsource, htarget, Γ, hΓ, hΓi, hΓd, hD, hiD, hflow⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
