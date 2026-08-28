import Wikipedia.HopfProblem.DegreeCollapseMiddleFamilyDescent
import Wikipedia.HopfProblem.DegreeCollapseAttachingCircleLowerTransport

/-!
# The whole actual attaching sphere on any cut immediately below its critical value

Generalize the existing circle transport to every native sphere dimension.
The transported parametrization is a smooth closed embedding and immersion,
and its image is exactly the original backward basin on the chosen cut.
The cut may come from a different surgery system for the same height.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_native_attaching_lower_cut
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) (n : ℕ)
    [Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = n + 1)]
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f) (hap : a < f p)
    (hgap : ∀ q : criticalPoints E f, f q < f p → f q < a) :
    let _ := RegularLevel.chartedSpace hf ha
    ∃ Γ : C(Hemisphere.Sphere n, {y : M // f y = a}),
      ContMDiff (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞ Γ ∧ IsClosedEmbedding Γ ∧
      (∀ z, Injective (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) Γ z)) ∧
      (∀ z, ∃ t : ℝ,
        S.flow t ((S.data p).surgery.attachingSphere
          (SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates n z)).val =
            (Γ z).val) ∧
      ∀ y : {x : M // f x = a}, y ∈ range Γ ↔
        Tendsto (fun t => S.flow t y.val) atBot (𝓝 p.val) := by
  let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
  let _ := RegularLevel.chartedSpace hf ha
  let e := SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates n
  let γ : C(Hemisphere.Sphere n, (S.data p).LowerLevel) :=
    ⟨(S.data p).surgery.attachingSphere ∘ e,
      ((S.data p).attaching_smooth hf n).continuous.comp e.continuous⟩
  have hγ : ContMDiff (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞ γ :=
    ((S.data p).attaching_smooth hf n).comp e.contMDiff
  have hγi : Injective γ := (S.data p).attaching_isClosedEmbedding.injective.comp e.injective
  have hγd : ∀ z, Injective (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) γ z) := by
    intro z
    change Injective (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E)
      ((S.data p).surgery.attachingSphere ∘ e) z)
    rw [mfderiv_comp z (((S.data p).attaching_smooth hf n).mdifferentiableAt (by simp))
      (e.contMDiff.mdifferentiableAt (by simp))]
    exact ((S.data p).attaching_derivative_injective hf n (e z)).comp
      (e.mfderivToContinuousLinearEquiv (by simp) z).injective
  have hreach (z : Hemisphere.Sphere n) : (γ z).val ∈ FlowCancellation.levelBasin S.flow f a :=
    S.attachingSphere_reaches_lower_cut hf p hap hgap (e z)
  let x₀ : Hemisphere.Sphere n := Hemisphere.point true ⟨0, by simp [DiskDouble.Disk]⟩
  obtain ⟨D, -, -, Γ, hΓ, hΓi, hΓd, -, -, hflow⟩ :=
    S.exists_embedded_level_transport hf (S.data p).lower_regular ha γ x₀ hγ hγi hγd hreach
  refine ⟨Γ, hΓ, hΓ.continuous.isClosedEmbedding hΓi, hΓd, hflow, ?_⟩
  intro y
  exact S.transported_attaching_range_iff hf p ha e e.surjective Γ hflow y

theorem AdaptedSurgeryWindows.not_backward_basin_on_upper_level
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) (x : (S.data p).UpperLevel) :
    ¬Tendsto (fun t => S.flow t x.val) atBot (𝓝 p.val) := by
  intro hx
  obtain ⟨q, hq, r, hr, hback, _, hheights⟩ :=
    FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral
      S.zero S.descent S.distinct x.val
  have heq : q = p.val := tendsto_nhds_unique hback hx
  have hh := (hheights ((S.data p).upper_regular x.val x.property)).2
  rw [heq, x.property] at hh
  exact (not_lt_of_ge (S.toSurgeryWindows.value_lt_upper p).le) hh

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
