import Wikipedia.HopfProblem.DegreeCollapseRegularLevelEmbeddedDisk
import Wikipedia.HopfProblem.DegreeCollapseSmoothBigonFromLoops

/-!
# Regular-level disk fillings from simple connectivity

Simple connectivity supplies an actual circle nullhomotopy. Its cone is a
continuous disk with the exact prescribed boundary. Relative smoothing and
general position produce the ambient embedded disk. The existing endpoint
avoidance and native flow projection then produce an embedded disk in the
actual middle regular level. No homotopy-sphere equivalence is supplied.
The geometric avoidance proof is the one used in RegularLevelDiskFilling;
only its ambient filling input is weakened here.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.SimplyConnected

theorem exists_continuous_disk {N : Type*} [TopologicalSpace N]
    [SimplyConnectedSpace N] (γ : C(Hemisphere.Sphere 1, N)) :
    ∃ D : C(Hemisphere.Ball 2, N),
      ∀ z : Hemisphere.Sphere 1, D ⟨z.val, sphere_subset_closedBall z.property⟩ = γ z := by
  obtain ⟨c, ⟨H⟩⟩ := ImmersedSource.circle_nullhomotopic_of_simplyConnected γ
  let : Nonempty (Hemisphere.Sphere 1) := ⟨SphereCube.point 1⟩
  exact ⟨DiskCone.extension γ c H, DiskCone.extension_boundary γ c H⟩

theorem exists_embedded_disk
    {G N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [TopologicalSpace N] [ChartedSpace G N] [IsManifold 𝓘(ℝ, G) ∞ N] [T2Space N]
    [SimplyConnectedSpace N]
    (γ : C(Hemisphere.Sphere 1, N)) (hγ : ContMDiff (𝓡 1) 𝓘(ℝ, G) ∞ γ)
    (hγinj : Injective γ) (hγderiv : ∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, G) γ z))
    (hdim : 5 ≤ Module.finrank ℝ G) :
    ∃ g : C(Hemisphere.Ambient 2, N), ContMDiff 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, G) ∞ g ∧
      (∀ z : Hemisphere.Sphere 1, g z.val = γ z) ∧
      Topology.IsClosedEmbedding (fun z : Hemisphere.Ball 2 => g z.val) ∧
      ∀ z : Hemisphere.Ball 2, Injective (mfderiv 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, G) g z.val) := by
  obtain ⟨D, hD⟩ := exists_continuous_disk γ
  exact exists_smooth_embedded_disk_of_continuous_filling γ hγ hγinj hγderiv hdim D hD


variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [SimplyConnectedSpace M] {f : M → ℝ}

theorem exists_disk_in_level_basin_of_index_cut
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
    {a : ℝ} (hreg : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hhigh : ∀ p : criticalPoints E f, a ≤ f p → 3 ≤ nativeMorseIndex E f p)
    (hlow : ∀ p : criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ 3)
    (γ : C(Hemisphere.Sphere 1, M)) (hγ : ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ γ)
    (hγinj : Injective γ) (hγderiv : ∀ x, Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) γ x))
    (hlevel : ∀ z, f (γ z) = a) :
    ∃ g : C(Hemisphere.Ambient 2, M), ContMDiff 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, E) ∞ g ∧
      (∀ z : Hemisphere.Sphere 1, g z.val = γ z) ∧
      Topology.IsClosedEmbedding (fun z : Hemisphere.Ball 2 => g z.val) ∧
      (∀ z : Hemisphere.Ball 2, Injective (mfderiv 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, E) g z.val)) ∧
      ∀ z : Hemisphere.Ball 2, g z.val ∈ FlowCancellation.levelBasin S.flow f a := by
  obtain ⟨g₀, hg₀, hboundary, hemb, hderiv⟩ :=
    exists_embedded_disk γ hγ hγinj hγderiv (by omega)
  let K : Set (Hemisphere.Ambient 2) := closedBall 0 1
  let C : Set (Hemisphere.Ambient 2) := sphere 0 1
  have hK : IsCompact K := isCompact_closedBall _ _
  have hC : IsClosed C := isClosed_sphere
  have hinj : InjOn g₀ K := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hfixed (z : Hemisphere.Ambient 2) (hz : z ∈ K ∩ C) :
      g₀ z ∈ FlowCancellation.levelBasin S.flow f a := by
    refine ⟨0, ?_⟩
    rw [S.flow.map_zero_apply, hboundary ⟨z, hz.2⟩, hlevel]
  have hhigh' (p : criticalPoints E f) (hp : a ≤ f p) :
      Module.finrank ℝ E - nativeMorseIndex E f p ≤ 3 := by
    have hh := hhigh p hp
    omega
  obtain ⟨g, hg, hhom, hembg, hderg, -, hbasin⟩ :=
    exists_embedded_avoidance_into_level_basin S hf hreg hhigh' hlow g₀ hg₀
      (by simp only [Hemisphere.Ambient, finrank_euclideanSpace_fin]; omega)
      (by simp only [Hemisphere.Ambient, finrank_euclideanSpace_fin]; omega)
      hK hK hC hinj (fun z hz => hderiv ⟨z, hz⟩) hfixed
  refine ⟨g, hg, ?_, hembg, fun z => hderg z.val z.property, ?_⟩
  · intro z
    exact (hhom.fst_eq_snd z.property).symm.trans (hboundary z)
  · intro z
    exact hbasin z.val (Or.inr z.property)

theorem exists_actual_regular_level_disk_of_index_cut
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
    {a : ℝ} (hreg : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hhigh : ∀ p : criticalPoints E f, a ≤ f p → 3 ≤ nativeMorseIndex E f p)
    (hlow : ∀ p : criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ 3)
    (γ : C(Hemisphere.Sphere 1, M)) (hγ : ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ γ)
    (hγinj : Injective γ) (hγderiv : ∀ x, Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) γ x))
    (hlevel : ∀ z, f (γ z) = a) :
    ∃ D : C(Hemisphere.Ball 2, {y : M // f y = a}),
      ∀ z : Hemisphere.Sphere 1, (D ⟨z.val, sphere_subset_closedBall z.property⟩).val = γ z := by
  obtain ⟨g, hg, hboundary, -, -, hbasin⟩ :=
    exists_disk_in_level_basin_of_index_cut S hf hdim hreg hhigh hlow γ hγ hγinj hγderiv hlevel
  obtain ⟨v, hv⟩ : (sphere (0 : Hemisphere.Ambient 2) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  let z₀ : {y : M // f y = a} := ⟨γ ⟨v, hv⟩, hlevel ⟨v, hv⟩⟩
  let _ := RegularLevel.chartedSpace hf hreg
  obtain ⟨Φ, hsource, htarget, hformula, -⟩ := FlowCancellation.exists_native_level_flow_cylinder
    hf hreg S.smooth S.flow S.integral (fun y hy => S.descent y (hreg y hy)) z₀
  have hcont : Continuous (fun z : Hemisphere.Ball 2 => Φ.symm (g z.val)) :=
    Φ.contMDiffOn_invFun.continuousOn.comp_continuous
      (g.continuous.comp continuous_subtype_val) (fun z => htarget.symm ▸ hbasin z)
  let D : C(Hemisphere.Ball 2, {y : M // f y = a}) :=
    ⟨fun z => (Φ.symm (g z.val)).1, continuous_fst.comp hcont⟩
  refine ⟨D, ?_⟩
  intro z
  let p : {y : M // f y = a} := ⟨γ z, hlevel z⟩
  have hp : (p, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; trivial
  have hφ : Φ (p, 0) = γ z := by rw [hformula, S.flow.map_zero_apply]
  have hi : Φ.symm (Φ (p, 0)) = (p, 0) := Φ.left_inv' hp
  rw [hφ] at hi
  change (Φ.symm (g z.val)).1.val = γ z
  rw [hboundary z]
  exact congrArg (fun q : {y : M // f y = a} × ℝ => q.1.val) hi

theorem exists_embedded_regular_level_disk_of_index_cut
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
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
  obtain ⟨D, hD⟩ := exists_actual_regular_level_disk_of_index_cut S hf hdim hreg
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

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.SimplyConnected
