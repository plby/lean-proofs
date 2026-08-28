import Wikipedia.HopfProblem.DegreeCollapsePositiveLevelAvoidance
import Wikipedia.HopfProblem.DegreeCollapseSimplyConnectedLevelDisks

/-!
# Actual regular-level disks above an untouched lower half

Simple connectivity is used only in the actual strict superlevel. A smooth
embedded ambient disk is constructed there and perturbed away from the full
endpoint obstruction there. The original flow cylinder projects it to the
original regular level with the entire prescribed circle fixed. Native
relative smoothing and general position then give an embedded disk in that
level. Critical points below the lower cut have no index restrictions.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap TopologicalSpace
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem exists_disk_in_level_basin_above_cut
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {b a : ℝ} (U : Opens M) [SimplyConnectedSpace U]
    (hU : ∀ x, x ∈ U ↔ b < f x)
    (hreg : ∀ y, f y = a → y ∉ criticalPoints E f) {d : ℕ}
    (hhigh : ∀ p : criticalPoints E f, a ≤ f p →
      Module.finrank ℝ E - nativeMorseIndex E f p ≤ d)
    (hlow : ∀ p : criticalPoints E f, b < f p → f p ≤ a → nativeMorseIndex E f p ≤ d)
    (hdim : 5 ≤ Module.finrank ℝ E) (hobstacle : 2 + d < Module.finrank ℝ E)
    (γ : C(Hemisphere.Sphere 1, U)) (hγ : ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ γ)
    (hγinj : Injective γ) (hγderiv : ∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) γ z))
    (hlevel : ∀ z, f (γ z).val = a) :
    ∃ g : C(Hemisphere.Ambient 2, U), ContMDiff 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, E) ∞ g ∧
      (∀ z : Hemisphere.Sphere 1, g z.val = γ z) ∧
      Topology.IsClosedEmbedding (fun z : Hemisphere.Ball 2 => g z.val) ∧
      (∀ z : Hemisphere.Ball 2, Injective (mfderiv 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, E) g z.val)) ∧
      ∀ z : Hemisphere.Ball 2, (g z.val).val ∈ FlowCancellation.levelBasin S.flow f a := by
  obtain ⟨g₀, hg₀, hboundary, hemb, hderiv⟩ :=
    SimplyConnected.exists_embedded_disk γ hγ hγinj hγderiv hdim
  let K : Set (Hemisphere.Ambient 2) := closedBall 0 1
  let C : Set (Hemisphere.Ambient 2) := sphere 0 1
  have hK : IsCompact K := isCompact_closedBall _ _
  have hC : IsClosed C := isClosed_sphere
  have hinj : InjOn g₀ K := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hfixed (z : Hemisphere.Ambient 2) (hz : z ∈ K ∩ C) :
      (g₀ z).val ∈ FlowCancellation.levelBasin S.flow f a := by
    refine ⟨0, ?_⟩
    rw [S.flow.map_zero_apply, hboundary ⟨z, hz.2⟩, hlevel]
  obtain ⟨g, hg, hhom, hembg, hderg, _, hbasin⟩ :=
    exists_embedded_avoidance_into_level_basin_above_cut S hf U hU hreg hhigh hlow g₀ hg₀
      (by simp only [Hemisphere.Ambient, finrank_euclideanSpace_fin]; omega)
      (by simpa only [Hemisphere.Ambient, finrank_euclideanSpace_fin] using hobstacle)
      hK hK hC hinj (fun z hz => hderiv ⟨z, hz⟩) hfixed
  refine ⟨g, hg, ?_, hembg, fun z => hderg z.val z.property, ?_⟩
  · intro z
    exact (hhom.fst_eq_snd z.property).symm.trans (hboundary z)
  · intro z
    exact hbasin z.val (Or.inr z.property)

theorem exists_actual_regular_level_disk_above_cut
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {b a : ℝ} (U : Opens M) [SimplyConnectedSpace U]
    (hU : ∀ x, x ∈ U ↔ b < f x) (hba : b < a)
    (hreg : ∀ y, f y = a → y ∉ criticalPoints E f) {d : ℕ}
    (hhigh : ∀ p : criticalPoints E f, a ≤ f p →
      Module.finrank ℝ E - nativeMorseIndex E f p ≤ d)
    (hlow : ∀ p : criticalPoints E f, b < f p → f p ≤ a → nativeMorseIndex E f p ≤ d)
    (hdim : 5 ≤ Module.finrank ℝ E) (hobstacle : 2 + d < Module.finrank ℝ E)
    (γ : C(Hemisphere.Sphere 1, M)) (hγ : ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ γ)
    (hγinj : Injective γ) (hγderiv : ∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) γ z))
    (hlevel : ∀ z, f (γ z) = a) :
    ∃ D : C(Hemisphere.Ball 2, {y : M // f y = a}),
      ∀ z : Hemisphere.Sphere 1, (D ⟨z.val, sphere_subset_closedBall z.property⟩).val = γ z := by
  let γU : C(Hemisphere.Sphere 1, U) :=
    ⟨fun z => ⟨γ z, (hU (γ z)).mpr (by rw [hlevel]; exact hba)⟩,
      γ.continuous.subtype_mk _⟩
  have hγU : ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ γU :=
    (ContMDiff.subtypeVal_comp_iff U γU).mp hγ
  have hiU : Injective γU := fun x y h => hγinj (congrArg Subtype.val h)
  have hdU (z : Hemisphere.Sphere 1) : Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) γU z) := by
    have hval : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (Subtype.val : U → M) :=
      contMDiff_subtype_val
    have hi : Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) ((Subtype.val : U → M) ∘ γU) z) :=
      hγderiv z
    rw [mfderiv_comp z (hval.mdifferentiableAt (by simp))
      (hγU.mdifferentiableAt (by simp))] at hi
    intro v w hvw
    exact hi (congrArg (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → M) (γU z)) hvw)
  obtain ⟨g, _, hboundary, _, _, hbasin⟩ := exists_disk_in_level_basin_above_cut
    S hf U hU hreg hhigh hlow hdim hobstacle γU hγU hiU hdU hlevel
  let z₀ : {y : M // f y = a} := ⟨γ (SphereCube.point 1), hlevel (SphereCube.point 1)⟩
  let _ := RegularLevel.chartedSpace hf hreg
  obtain ⟨Φ, hsource, htarget, hformula, _⟩ := FlowCancellation.exists_native_level_flow_cylinder
    hf hreg S.smooth S.flow S.integral (fun y hy => S.descent y (hreg y hy)) z₀
  have hcont : Continuous (fun z : Hemisphere.Ball 2 => Φ.symm (g z.val).val) :=
    Φ.contMDiffOn_invFun.continuousOn.comp_continuous
      (continuous_subtype_val.comp (g.continuous.comp continuous_subtype_val))
      (fun z => htarget.symm ▸ hbasin z)
  let D : C(Hemisphere.Ball 2, {y : M // f y = a}) :=
    ⟨fun z => (Φ.symm (g z.val).val).1, continuous_fst.comp hcont⟩
  refine ⟨D, ?_⟩
  intro z
  let p : {y : M // f y = a} := ⟨γ z, hlevel z⟩
  have hp : (p, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; trivial
  have hφ : Φ (p, 0) = γ z := by rw [hformula, S.flow.map_zero_apply]
  have hi : Φ.symm (Φ (p, 0)) = (p, 0) := Φ.left_inv' hp
  rw [hφ] at hi
  change (Φ.symm (g z.val).val).1.val = γ z
  rw [hboundary z]
  exact congrArg (fun q : {y : M // f y = a} × ℝ => q.1.val) hi

theorem exists_embedded_regular_level_disk_above_cut
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {b a : ℝ} (U : Opens M) [SimplyConnectedSpace U]
    (hU : ∀ x, x ∈ U ↔ b < f x) (hba : b < a)
    (hreg : ∀ y, f y = a → y ∉ criticalPoints E f) {d : ℕ}
    (hhigh : ∀ p : criticalPoints E f, a ≤ f p →
      Module.finrank ℝ E - nativeMorseIndex E f p ≤ d)
    (hlow : ∀ p : criticalPoints E f, b < f p → f p ≤ a → nativeMorseIndex E f p ≤ d)
    (hdim : 6 ≤ Module.finrank ℝ E) (hobstacle : 2 + d < Module.finrank ℝ E)
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
  obtain ⟨D, hD⟩ := exists_actual_regular_level_disk_above_cut S hf U hU hba hreg
    hhigh hlow (by omega) hobstacle γ hγ hγinj hγderiv hlevel
  let γL : C(Hemisphere.Sphere 1, {y : M // f y = a}) :=
    ⟨fun z => ⟨γ z, hlevel z⟩, γ.continuous.subtype_mk _⟩
  have hγL : ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γL :=
    (RegularLevel.contMDiff_iff_inclusion hf hreg (𝓡 1) γL).mpr hγ
  have hinj : Injective γL := fun x y hxy => hγinj (congrArg Subtype.val hxy)
  have hderiv (z : Hemisphere.Sphere 1) :
      Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γL z) :=
    RegularLevel.injective_mfderiv_of_inclusion hf hreg (𝓡 1) γL z hγ.contMDiffAt (hγderiv z)
  have hdimL : 5 ≤ Module.finrank ℝ (RegularLevel.Model E) := by
    simp only [RegularLevel.Model, finrank_euclideanSpace_fin]
    omega
  have hboundary (z : Hemisphere.Sphere 1) :
      D ⟨z.val, sphere_subset_closedBall z.property⟩ = γL z := Subtype.ext (hD z)
  obtain ⟨g, hg, hboundaryg, hemb, hderivg⟩ :=
    exists_smooth_embedded_disk_of_continuous_filling γL hγL hinj hderiv hdimL D hboundary
  exact ⟨g, hg, fun z => congrArg Subtype.val (hboundaryg z), hemb, hderivg⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
