import Wikipedia.HopfProblem.DegreeCollapseAttachingCircleLowerTransport

/-!
# Native attaching-sphere transport in every source dimension

The original complete flow transports the entire parametrized attaching
sphere to the lower regular cut. Its actual inverse, native immersion,
embedding, and orbit data are retained. The source dimension is arbitrary;
no separate attaching section is supplied.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

open Classical in
theorem AdaptedSurgeryWindows.exists_attaching_sphere_lower_transport
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) (k : ℕ)
    [Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = k + 1)]
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f) (hap : a < f p)
    (hgap : ∀ q : criticalPoints E f, f q < f p → f q < a) :
    let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
    let _ := RegularLevel.chartedSpace hf ha
    ∃ e : Diffeomorph (𝓡 k) (𝓡 k) (Hemisphere.Sphere k)
        (sphere (0 : (S.data p).chart.NegativeCoordinates) 1) ∞,
      ∃ D : PartialDiffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
          (S.data p).LowerLevel {y : M // f y = a} ∞,
        D.source = {x | x.val ∈ FlowCancellation.levelBasin S.flow f a} ∧
        D.target = {y | y.val ∈ FlowCancellation.levelBasin S.flow f (S.toSurgeryWindows.lower p)} ∧
        ∃ Γ : C(Hemisphere.Sphere k, {y : M // f y = a}),
          ContMDiff (𝓡 k) 𝓘(ℝ, RegularLevel.Model E) ∞ Γ ∧ Injective Γ ∧
          (∀ z, Injective (mfderiv (𝓡 k) 𝓘(ℝ, RegularLevel.Model E) Γ z)) ∧
          (∀ z, D ((S.data p).surgery.attachingSphere (e z)) = Γ z) ∧
          (∀ z, D.symm (Γ z) = (S.data p).surgery.attachingSphere (e z)) ∧
          ∀ z, ∃ t : ℝ, S.flow t ((S.data p).surgery.attachingSphere (e z)).val = (Γ z).val := by
  let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.isManifold hf (S.data p).lower_regular
  let _ := RegularLevel.isManifold hf ha
  let e := SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates k
  let γ : C(Hemisphere.Sphere k, (S.data p).LowerLevel) :=
    ⟨(S.data p).surgery.attachingSphere ∘ e,
      ((S.data p).attaching_smooth hf k).continuous.comp e.continuous⟩
  have hγ : ContMDiff (𝓡 k) 𝓘(ℝ, RegularLevel.Model E) ∞ γ :=
    ((S.data p).attaching_smooth hf k).comp e.contMDiff
  have hγi : Injective γ := (S.data p).attaching_isClosedEmbedding.injective.comp e.injective
  have hγd : ∀ z, Injective (mfderiv (𝓡 k) 𝓘(ℝ, RegularLevel.Model E) γ z) := by
    intro z
    change Injective (mfderiv (𝓡 k) 𝓘(ℝ, RegularLevel.Model E)
      ((S.data p).surgery.attachingSphere ∘ e) z)
    rw [mfderiv_comp z (((S.data p).attaching_smooth hf k).mdifferentiableAt (by simp))
      (e.contMDiff.mdifferentiableAt (by simp))]
    exact ((S.data p).attaching_derivative_injective hf k (e z)).comp
      (e.mfderivToContinuousLinearEquiv (by simp) z).injective
  have hreach (z : Hemisphere.Sphere k) : (γ z).val ∈ FlowCancellation.levelBasin S.flow f a :=
    S.attachingSphere_reaches_lower_cut hf p hap hgap (e z)
  obtain ⟨D, hsource, htarget, Γ, hΓ, hΓi, hΓd, hD, hiD, hflow⟩ :=
    S.exists_embedded_level_transport hf (S.data p).lower_regular ha γ
      (Hemisphere.point true ⟨0, by simp⟩) hγ hγi hγd hreach
  exact ⟨e, D, hsource, htarget, Γ, hΓ, hΓi, hΓd, hD, hiD, hflow⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
