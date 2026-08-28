import Wikipedia.HopfProblem.DegreeCollapseEqualLevelCircleIsotopy
import Wikipedia.HopfProblem.DegreeCollapseAttachingCircleBasinSection

/-!
# Placement of the actual new two-handle basin on any middle-level circle

The new attaching circle is transported by its actual complete flow and
proved to be the entire backward-basin section. The old function's middle
index cut then constructs a native ambient isotopy to any supplied embedded
immersive target circle in the unchanged level. The endpoint retains an
exact equivalence for every point of the whole level.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f g : M → ℝ}

open Classical in
theorem exists_new_attaching_circle_placement
    (S : AdaptedSurgeryWindows E f) (T : AdaptedSurgeryWindows E g)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (e : M ≃ₕ SixSphere) (hdim : Module.finrank ℝ E = 6)
    {a : ℝ} (hfr : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ criticalPoints E g) (heq : ∀ y, g y = a ↔ f y = a)
    (hhigh : ∀ q : criticalPoints E f, a ≤ f q → 3 ≤ nativeMorseIndex E f q)
    (hlow : ∀ q : criticalPoints E f, f q ≤ a → nativeMorseIndex E f q ≤ 3)
    (p : criticalPoints E g)
    [Fact (Module.finrank ℝ (T.data p).chart.NegativeCoordinates = 1 + 1)]
    (hap : a < g p) (hgap : ∀ q : criticalPoints E g, g q < g p → g q < a)
    (δ : C(Hemisphere.Sphere 1, {y : M // g y = a})) :
    let _ := RegularLevel.chartedSpace hg hgr
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ δ → Injective δ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) δ z)) →
    ∃ Γ : C(Hemisphere.Sphere 1, {y : M // g y = a}),
      ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ Γ ∧ Injective Γ ∧
      (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) Γ z)) ∧
      (∀ x, x ∈ range Γ ↔ Tendsto (fun t => T.flow t x.val) atBot (𝓝 p.val)) ∧
      ∃ P : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
          {y : M // g y = a} {y : M // g y = a} ∞,
        IsotopicToIdentity P ∧ (∀ z, P (Γ z) = δ z) ∧
        ∀ x, Tendsto (fun t => T.flow t x.val) atBot (𝓝 p.val) ↔ P x ∈ range δ := by
  let _ := RegularLevel.chartedSpace hg hgr
  let _ := RegularLevel.chartedSpace hg (T.data p).lower_regular
  let _ := RegularLevel.isManifold hg hgr
  let _ := RegularLevel.isManifold hg (T.data p).lower_regular
  change ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ δ → Injective δ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) δ z)) → _
  intro hδ hδi hδd
  obtain ⟨σ, D, -, -, Γ, hΓ, hΓi, hΓd, -, -, hflow⟩ :=
    T.exists_attaching_circle_lower_transport hg p hgr hap hgap
  have hrange (x : {y : M // g y = a}) :
      x ∈ range Γ ↔ Tendsto (fun t => T.flow t x.val) atBot (𝓝 p.val) :=
    T.transported_attaching_range_iff hg p hgr σ σ.surjective Γ hflow x
  obtain ⟨P, hP, hformula⟩ := exists_equal_level_circle_isotopy S hf hg e hdim
    hfr hgr heq hhigh hlow Γ δ hΓ hΓi hΓd hδ hδi hδd
  refine ⟨Γ, hΓ, hΓi, hΓd, hrange, P, hP, hformula, ?_⟩
  intro x
  rw [← hrange]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, (hformula z).symm⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, P.injective ((hformula z).trans hz)⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
