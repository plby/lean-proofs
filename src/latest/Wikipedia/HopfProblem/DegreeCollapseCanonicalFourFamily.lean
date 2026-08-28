import Wikipedia.HopfProblem.DegreeCollapseCompactBasinSection
import Wikipedia.HopfProblem.DegreeCollapseIndexFourBasinFamily

/-!
# Restore every original index-four attaching parameter in the common-level family

Compact full basin images force all native attaching directions to reach
the common cut. Transport the original parametrized three-spheres through
the actual level flow cylinders. Their images are exactly the old images,
so disjointness is retained, while each parameter now has the exact orbit
formula needed to identify its integral attaching class.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

local notation "S₃" => Hemisphere.Sphere 3

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

omit [CompactSpace M] in
theorem nativeIndexFourAttachingSphere_regular
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) (hp : nativeMorseIndex E f p = 4) :
    let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
    ContMDiff (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) ∞ (nativeIndexFourAttachingSphere S p hp) ∧
      IsClosedEmbedding (nativeIndexFourAttachingSphere S p hp) ∧
      ∀ x, Injective (mfderiv (𝓡 3) 𝓘(ℝ, RegularLevel.Model E)
        (nativeIndexFourAttachingSphere S p hp) x) := by
  let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
  let _ : Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 3 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp⟩
  let e := SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates 3
  have hs : ContMDiff (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) ∞
      (nativeIndexFourAttachingSphere S p hp) :=
    ((S.data p).attaching_smooth hf 3).comp e.contMDiff
  have hi : Injective (nativeIndexFourAttachingSphere S p hp) :=
    (S.data p).attaching_isClosedEmbedding.injective.comp e.injective
  refine ⟨hs, hs.continuous.isClosedEmbedding hi, ?_⟩
  intro x
  change Injective (mfderiv (𝓡 3) 𝓘(ℝ, RegularLevel.Model E)
    ((S.data p).surgery.attachingSphere ∘ e) x)
  rw [mfderiv_comp x (((S.data p).attaching_smooth hf 3).mdifferentiableAt (by simp))
    (e.contMDiff.mdifferentiableAt (by simp))]
  exact ((S.data p).attaching_derivative_injective hf 3 (e x)).comp
    (e.mfderivToContinuousLinearEquiv (by simp) x).injective

theorem AdaptedSurgeryWindows.exists_canonical_four_basin_sphere
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) (hp : nativeMorseIndex E f p = 4)
    {X : Type} [TopologicalSpace X] [CompactSpace X]
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (α : C(X, {y : M // f y = a})) (x₀ : X)
    (hfull : ∀ y, y ∈ range α ↔ Tendsto (fun t => S.flow t y.val) atBot (𝓝 p.val)) :
    let _ := RegularLevel.chartedSpace hf ha
    ∃ γ : C(S₃, {y : M // f y = a}),
      ContMDiff (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) ∞ γ ∧ IsClosedEmbedding γ ∧
      (∀ x, Injective (mfderiv (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) γ x)) ∧
      range γ = range α ∧
      (∀ x, ∃ t : ℝ, S.flow t (nativeIndexFourAttachingSphere S p hp x).val = (γ x).val) ∧
      ∀ y, y ∈ range γ ↔ Tendsto (fun t => S.flow t y.val) atBot (𝓝 p.val) := by
  let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
  let _ := RegularLevel.chartedSpace hf ha
  let _ : Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 3 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp⟩
  have hreach := S.attaching_sphere_reaches_of_compact_basin_section hf p 3 ha α x₀ hfull
  obtain ⟨hs, he, hi⟩ := nativeIndexFourAttachingSphere_regular S hf p hp
  let z₀ : S₃ := Hemisphere.point true ⟨0, by simp⟩
  obtain ⟨D, -, -, γ, hγ, hγi, hγd, -, -, horbit⟩ :=
    S.exists_embedded_level_transport hf (S.data p).lower_regular ha
      (nativeIndexFourAttachingSphere S p hp) z₀ hs he.injective hi (fun z => hreach _)
  have hγfull (y : {x : M // f x = a}) : y ∈ range γ ↔
      Tendsto (fun t => S.flow t y.val) atBot (𝓝 p.val) :=
    S.transported_attaching_range_iff hf p ha
      (SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates 3)
      (SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates 3).surjective
      γ horbit y
  exact ⟨γ, hγ, hγ.continuous.isClosedEmbedding hγi, hγd,
    Set.ext (fun y => (hγfull y).trans (hfull y).symm), horbit, hγfull⟩

theorem AdaptedSurgeryWindows.exists_canonical_four_family
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    {n : ℕ} (p : Fin n → criticalPoints E f)
    (hp : ∀ j, nativeMorseIndex E f (p j) = 4)
    (α : Fin n → S₃ → {y : M // f y = a})
    (hα : IsNativeFourBasinFamily S hf ha p α) :
    ∃ γ : Fin n → S₃ → {y : M // f y = a},
      IsNativeFourBasinFamily S hf ha p γ ∧ (∀ j, range (γ j) = range (α j)) ∧
      ∀ j x, ∃ t : ℝ,
        S.flow t (nativeIndexFourAttachingSphere S (p j) (hp j) x).val = (γ j x).val := by
  let _ := RegularLevel.chartedSpace hf ha
  obtain ⟨hαs, -, -, hαpair, hαfull⟩ := hα
  let x₀ : S₃ := Hemisphere.point true ⟨0, by simp⟩
  have hex (j : Fin n) := S.exists_canonical_four_basin_sphere hf (p j) (hp j) ha
    ⟨α j, (hαs j).continuous⟩ x₀ (hαfull j)
  choose γ hγs hγe hγi hγrange hγflow hγfull using hex
  refine ⟨fun j => γ j, ⟨hγs, hγe, hγi, ?_, hγfull⟩, hγrange, hγflow⟩
  intro i j hij
  rw [hγrange i, hγrange j]
  exact hαpair hij

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
