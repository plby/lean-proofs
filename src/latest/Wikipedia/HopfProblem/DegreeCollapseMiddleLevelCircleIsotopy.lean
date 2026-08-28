import Wikipedia.HopfProblem.DegreeCollapsePathDiskIsotopy
import Wikipedia.HopfProblem.DegreeCollapseRegularLevelPaths
import Wikipedia.HopfProblem.DegreeCollapseRegularLevelEmbeddedDisk

/-!
# Actual native isotopy between arbitrary embedded middle-level circles

Each circle bounds a constructed embedded immersive disk in the original
regular level. Endpoint-basin avoidance proves that level path connected.
The disk isotopy theorem then gives the exact parametrized circle identity,
with no ambient-isotopy or disk-identification assumption.
-/

noncomputable section

open Set Function Metric Manifold ContinuousMap
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem exists_native_middle_level_circle_disk
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (e : M ≃ₕ SixSphere) (hdim : Module.finrank ℝ E = 6)
    {a : ℝ} (hreg : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hhigh : ∀ p : criticalPoints E f, a ≤ f p → 3 ≤ nativeMorseIndex E f p)
    (hlow : ∀ p : criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ 3)
    (γ : C(Hemisphere.Sphere 1, {y : M // f y = a})) :
    let _ := RegularLevel.chartedSpace hf hreg
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ → Injective γ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z)) →
    ∃ g : C(Hemisphere.Ambient 2, {y : M // f y = a}),
      ContMDiff 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g ∧
      (∀ z : Hemisphere.Sphere 1, g z.val = γ z) ∧
      Topology.IsClosedEmbedding (fun z : Hemisphere.Ball 2 => g z.val) ∧
      (∀ z : Hemisphere.Ball 2,
        Injective (mfderiv 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, RegularLevel.Model E) g z.val)) := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  change ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ → Injective γ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z)) → _
  intro hγ hγi hγd
  let γM : C(Hemisphere.Sphere 1, M) :=
    ⟨Subtype.val ∘ γ, continuous_subtype_val.comp γ.continuous⟩
  have hγM : ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ γM :=
    (RegularLevel.contMDiff_inclusion hf hreg).comp hγ
  have hγMi : Injective γM := Subtype.val_injective.comp hγi
  have hγMd : ∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) γM z) := by
    intro z
    change Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) (Subtype.val ∘ γ) z)
    rw [mfderiv_comp z ((RegularLevel.contMDiff_inclusion hf hreg).mdifferentiableAt (by simp))
      (hγ.mdifferentiableAt (by simp))]
    exact (RegularLevel.injective_mfderiv_inclusion hf hreg (γ z)).comp (hγd z)
  obtain ⟨g, hg, hb, hemb, hgd⟩ := exists_embedded_regular_level_disk_of_index_cut S hf e hdim
    hreg hhigh hlow γM hγM hγMi hγMd (fun z => (γ z).property)
  exact ⟨g, hg, fun z => Subtype.ext (hb z), hemb, hgd⟩

theorem exists_native_middle_level_circle_isotopy [PathConnectedSpace M]
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (e : M ≃ₕ SixSphere) (hdim : Module.finrank ℝ E = 6)
    {a : ℝ} (hreg : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hhigh : ∀ p : criticalPoints E f, a ≤ f p → 3 ≤ nativeMorseIndex E f p)
    (hlow : ∀ p : criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ 3)
    (γ δ : C(Hemisphere.Sphere 1, {y : M // f y = a})) :
    let _ := RegularLevel.chartedSpace hf hreg
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ → Injective γ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z)) →
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ δ → Injective δ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) δ z)) →
    ∃ P : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        {y : M // f y = a} {y : M // f y = a} ∞,
      IsotopicToIdentity P ∧ ∀ z, P (γ z) = δ z := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  let _ : CompactSpace {y : M // f y = a} :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  change ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ → Injective γ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z)) →
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ δ → Injective δ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) δ z)) → _
  intro hγ hγi hγd hδ hδi hδd
  obtain ⟨g, hg, hgb, hge, hgd⟩ :=
    exists_native_middle_level_circle_disk S hf e hdim hreg hhigh hlow γ hγ hγi hγd
  obtain ⟨h, hh, hhb, hhe, hhd⟩ :=
    exists_native_middle_level_circle_disk S hf e hdim hreg hhigh hlow δ hδ hδi hδd
  let _ := S.pathConnectedSpace_middle_level hf hdim hreg hhigh hlow (g 0)
  have hgi : InjOn g (closedBall (0 : Hemisphere.Ambient 2) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hge.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hhi : InjOn h (closedBall (0 : Hemisphere.Ambient 2) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hhe.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hcodim : Module.finrank ℝ (Hemisphere.Ambient 2) + 3 =
      Module.finrank ℝ (RegularLevel.Model E) := by
    simp only [Hemisphere.Ambient, RegularLevel.Model, finrank_euclideanSpace_fin, hdim]
  have hmodel : 2 ≤ Module.finrank ℝ (RegularLevel.Model E) := by
    simp only [RegularLevel.Model, finrank_euclideanSpace_fin, hdim]
    omega
  obtain ⟨P, hP, hformula⟩ := DiskShrinking.exists_embedded_disk_isotopy hg hh hgi hhi
    (fun x hx => hgd ⟨x, hx⟩) (fun x hx => hhd ⟨x, hx⟩) 3 (by omega) hcodim hmodel
  refine ⟨P, hP, ?_⟩
  intro z
  rw [← hgb z, hformula z.val (sphere_subset_closedBall z.property), hhb z]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
