import Wikipedia.HopfProblem.OrbitPairNativeImmersionStability
import Wikipedia.SmoothSixDPoincare.ImmersionLocalInjectivity

/-!
# Local injectivity and compact embedding neighborhoods in the native source atlas

An injective native derivative gives a genuine injective neighborhood.
Source charts reduce this to the proved Euclidean-source inverse-function
argument. Compact embedded immersive sets then have one common open
injectivity neighborhood, with no change of manifold structure.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.NativeImmersion

open Wikipedia.SmoothSixDPoincare

variable {E G H K X N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ G K} [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]

theorem exists_open_injOn_on {f : X → N} {W : Set X} (hW : IsOpen W)
    (hf : ContMDiffOn I J ∞ f W) {x : X} (hx : x ∈ W)
    (hinj : Injective (mfderiv I J f x)) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ W ∧ InjOn f V := by
  let c := NoExoticSixSphere.modelChartPartialDiffeomorph (I := I) x
  have hxc : x ∈ c.source := mem_extChartAt_source x
  have hcx : c x ∈ c.target := c.map_source' hxc
  have hleft : c.symm (c x) = x := c.left_inv' hxc
  let U : Set E := c.target ∩ c.symm ⁻¹' W
  have hU : IsOpen U := c.toOpenPartialHomeomorph.isOpen_inter_preimage_symm hW
  have hcU : ContMDiffOn 𝓘(ℝ, E) J ∞ (f ∘ c.symm) U :=
    hf.comp (c.contMDiffOn_invFun.mono inter_subset_left) (fun _ hz => hz.2)
  have hcxW : c.symm (c x) ∈ W := by
    rw [hleft]
    exact hx
  have hxU : c x ∈ U := ⟨hcx, hcxW⟩
  have hfs : MDifferentiableAt I J f (c.symm (c x)) :=
    (hf.contMDiffAt (hW.mem_nhds hcxW)).mdifferentiableAt (by simp)
  have hi : Injective (mfderiv 𝓘(ℝ, E) J (f ∘ c.symm) (c x)) := by
    apply (injective_sourceChart_iff c hcx hfs).mpr
    rw [hleft]
    exact hinj
  obtain ⟨V, hV, hxV, hVU, hVi⟩ :=
    ManifoldImmersion.exists_open_injOn_of_injective_nativeDerivative_on hU hcU hxU hi
  refine ⟨c.symm '' V, c.toOpenPartialHomeomorph.isOpen_image_symm_of_subset_target
    hV (hVU.trans inter_subset_left), ⟨c x, hxV, hleft⟩, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact (hVU hz).2
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ huv
    exact congrArg c.symm (hVi hu hv huv)

variable [T2Space N]

theorem exists_open_injOn_near_compact {f : X → N} {W : Set X} (hW : IsOpen W)
    (hf : ContMDiffOn I J ∞ f W) {S : Set X} (hS : IsCompact S)
    (hSW : S ⊆ W) (hinj : InjOn f S)
    (hi : ∀ x ∈ S, Injective (mfderiv I J f x)) :
    ∃ V : Set X, IsOpen V ∧ S ⊆ V ∧ V ⊆ W ∧ InjOn f V := by
  have hc : ∀ x ∈ S, ContinuousAt f x := fun x hx =>
    hf.continuousOn.continuousAt (hW.mem_nhds (hSW hx))
  have hlocal : ∀ x ∈ S, ∃ V ∈ 𝓝 x, InjOn f V := by
    intro x hx
    obtain ⟨V, hV, hxV, -, hVi⟩ := exists_open_injOn_on hW hf (hSW hx) (hi x hx)
    exact ⟨V, hV.mem_nhds hxV, hVi⟩
  obtain ⟨V, hV, hSV, hVi⟩ := hinj.exists_isOpen_superset hS hc hlocal
  exact ⟨V ∩ W, hV.inter hW, fun x hx => ⟨hSV hx, hSW hx⟩,
    inter_subset_right, hVi.mono inter_subset_left⟩

end Wikipedia.HopfProblem.OrbitPair.NativeImmersion
