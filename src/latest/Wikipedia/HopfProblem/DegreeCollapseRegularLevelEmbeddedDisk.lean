import Wikipedia.HopfProblem.DegreeCollapseRegularLevelDiskFilling
import Wikipedia.HopfProblem.DegreeCollapseDiskFillingSmoothing

/-!
# Smooth embedded fillings in the original regular level

The actual continuous filling obtained by basin avoidance is smoothed and
made embedded within the original five-dimensional level manifold. Every
point of the given ambient smooth circle is retained as its exact boundary,
and the native level derivatives of the disk are injective everywhere on
the closed disk. No abstract replacement of the regular level is used.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem exists_embedded_regular_level_disk_of_index_cut
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (e : M ≃ₕ SixSphere) (hdim : Module.finrank ℝ E = 6)
    {a : ℝ} (hreg : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hhigh : ∀ p : criticalPoints E f, a ≤ f p → 3 ≤ nativeMorseIndex E f p)
    (hlow : ∀ p : criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ 3)
    (γ : C(Hemisphere.Sphere 1, M)) (hγ : ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ γ)
    (hγinj : Injective γ) (hγderiv : ∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) γ z))
    (hlevel : ∀ z, f (γ z) = a) :
    let _ := RegularLevel.chartedSpace hf hreg
    ∃ g : C(Hemisphere.Ambient 2, {y : M // f y = a}),
      ContMDiff 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g ∧
      (∀ z : Hemisphere.Sphere 1, (g z.val).val = γ z) ∧
      Topology.IsClosedEmbedding (fun z : Hemisphere.Ball 2 => g z.val) ∧
      ∀ z : Hemisphere.Ball 2,
        Injective (mfderiv 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, RegularLevel.Model E) g z.val) := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  obtain ⟨D, hD⟩ := exists_actual_regular_level_disk_of_index_cut S hf e hdim hreg
    hhigh hlow γ hγ hγinj hγderiv hlevel
  let γL : C(Hemisphere.Sphere 1, {y : M // f y = a}) :=
    ⟨fun z => ⟨γ z, hlevel z⟩, γ.continuous.subtype_mk _⟩
  have hγL : ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γL :=
    (RegularLevel.contMDiff_iff_inclusion hf hreg (𝓡 1) γL).mpr hγ
  have hinj : Injective γL := fun x y hxy => hγinj (congrArg Subtype.val hxy)
  have hderiv (z : Hemisphere.Sphere 1) :
      Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γL z) :=
    RegularLevel.injective_mfderiv_of_inclusion hf hreg (𝓡 1) γL z hγ.contMDiffAt (hγderiv z)
  have hdimL : 5 ≤ Module.finrank ℝ (RegularLevel.Model E) := by
    simp only [RegularLevel.Model, finrank_euclideanSpace_fin, hdim]
    norm_num
  have hboundary (z : Hemisphere.Sphere 1) :
      D ⟨z.val, sphere_subset_closedBall z.property⟩ = γL z := Subtype.ext (hD z)
  obtain ⟨g, hg, hboundaryg, hemb, hderivg⟩ :=
    exists_smooth_embedded_disk_of_continuous_filling γL hγL hinj hderiv hdimL D hboundary
  exact ⟨g, hg, fun z => congrArg Subtype.val (hboundaryg z), hemb, hderivg⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
