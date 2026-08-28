import Wikipedia.SmoothSixDPoincare.NativeImmersionChart
import Wikipedia.SmoothSixDPoincare.ManifoldImmersionStability
import Wikipedia.NoExoticSixSphere.LocalInverse
import Mathlib.Analysis.Normed.Module.ContinuousInverse

/-!
# Injective differentials give actual locally injective maps

A continuous linear left inverse of the differential reduces the claim to
the inverse-function theorem in the source dimension. A target chart then
transfers this local injectivity to the original manifold-valued map.
-/

noncomputable section

open Set
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldImmersion

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- A smooth map with injective derivative is injective on an actual open neighborhood. -/
theorem exists_open_injOn_of_injective_fderiv {f : E → F} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (hinj : Function.Injective (fderiv ℝ f x)) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ InjOn f V := by
  obtain ⟨L, hL⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hinj
  have hdf := (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hderiv : HasFDerivAt (L ∘ f) (ContinuousLinearMap.id ℝ E) x := by
    convert L.hasFDerivAt.comp x hdf.hasFDerivAt using 1
    ext v
    exact (hL v).symm
  have hcomp : ContDiffOn ℝ ∞ (L ∘ f) U := L.contDiff.comp_contDiffOn hf
  have hinv : (fderiv ℝ (L ∘ f) x).IsInvertible := by
    rw [hderiv.fderiv]
    exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩
  obtain ⟨φ, hxφ, hφU, hφeq⟩ :=
    NoExoticSixSphere.exists_partialDiffeomorph_of_contDiffOn hU hx hcomp hinv
  refine ⟨φ.source, φ.open_source, hxφ, hφU, ?_⟩
  intro y hy z hz hyz
  apply φ.toPartialEquiv.injOn hy hz
  rw [hφeq]
  exact congrArg L hyz

variable {G H N : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N]

/-- Local smoothness and an injective native derivative give an injective neighborhood. -/
theorem exists_open_injOn_of_injective_nativeDerivative_on {f : E → N} {W : Set E}
    (hW : IsOpen W) (hf : ContMDiffOn 𝓘(ℝ, E) J ∞ f W) {x : E} (hxW : x ∈ W)
    (hinj : Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ W ∧ InjOn f V := by
  let c := NoExoticSixSphere.modelChartPartialDiffeomorph (I := J) (f x)
  have hx : f x ∈ c.source := mem_extChartAt_source (f x)
  let U := W ∩ f ⁻¹' c.source
  have hU : IsOpen U := hf.continuousOn.isOpen_inter_preimage hW c.open_source
  have hc : ContDiffOn ℝ ∞ (c ∘ f) U :=
    (c.contMDiffOn_toFun.comp (hf.mono inter_subset_left) (fun _ h => h.2)).contDiffOn
  have hfx := hf.contMDiffAt (hW.mem_nhds hxW)
  have hi := (injective_fderiv_chart_iff c (hfx.mdifferentiableAt (by simp)) hx).mpr hinj
  obtain ⟨V, hV, hxV, hVU, hinjV⟩ :=
    exists_open_injOn_of_injective_fderiv hU ⟨hxW, hx⟩ hc hi
  exact ⟨V, hV, hxV, hVU.trans inter_subset_left,
    fun _ hy _ hz heq => hinjV hy hz (congrArg c heq)⟩

/-- An injective native derivative gives an injective neighborhood in the original target. -/
theorem exists_open_injOn_of_injective_nativeDerivative {f : E → N}
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) {x : E}
    (hinj : Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ InjOn f V := by
  obtain ⟨V, hV, hxV, _, hinjV⟩ := exists_open_injOn_of_injective_nativeDerivative_on
    isOpen_univ hf.contMDiffOn (mem_univ x) hinj
  exact ⟨V, hV, hxV, hinjV⟩

/-- A locally smooth compact embedded immersive locus has an injective open neighborhood. -/
theorem exists_open_injOn_near_compact_on [T2Space N] {f : E → N} {W : Set E}
    (hW : IsOpen W) (hf : ContMDiffOn 𝓘(ℝ, E) J ∞ f W)
    {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W) (hinj : InjOn f K)
    (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ V ⊆ W ∧ InjOn f V := by
  have hc : ∀ x ∈ K, ContinuousAt f x := fun x hx =>
    hf.continuousOn.continuousAt (hW.mem_nhds (hKW hx))
  have hlocal : ∀ x ∈ K, ∃ V ∈ nhds x, InjOn f V := by
    intro x hx
    obtain ⟨V, hV, hxV, _, hinjV⟩ :=
      exists_open_injOn_of_injective_nativeDerivative_on hW hf (hKW hx) (hi x hx)
    exact ⟨V, hV.mem_nhds hxV, hinjV⟩
  obtain ⟨V, hV, hKV, hinjV⟩ := hinj.exists_isOpen_superset hK hc hlocal
  exact ⟨V ∩ W, hV.inter hW, fun _ hx => ⟨hKV hx, hKW hx⟩,
    inter_subset_right, hinjV.mono inter_subset_left⟩

/-- A compact embedded immersive locus has a single open injectivity neighborhood. -/
theorem exists_open_embedded_immersive_neighborhood [T2Space N] {f : E → N} {W : Set E}
    (hW : IsOpen W) (hf : ContMDiffOn 𝓘(ℝ, E) J ∞ f W)
    {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W) (hinj : InjOn f K)
    (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ V ⊆ W ∧ InjOn f V ∧
      ∀ x ∈ V, Function.Injective (mfderiv 𝓘(ℝ, E) J f x) := by
  let O := {x : E | x ∈ W ∧ Function.Injective (mfderiv 𝓘(ℝ, E) J f x)}
  have hO : IsOpen O := isOpen_injective_derivative_on hW hf
  have hOW : O ⊆ W := fun _ hx => hx.1
  obtain ⟨V, hV, hKV, hVO, hinjV⟩ := exists_open_injOn_near_compact_on hO (hf.mono hOW)
    hK (fun x hx => ⟨hKW hx, hi x hx⟩) hinj hi
  exact ⟨V, hV, hKV, hVO.trans hOW, hinjV, fun x hx => (hVO hx).2⟩

/-- A compact embedded immersive locus has a single open injectivity neighborhood. -/
theorem exists_open_injOn_near_compact [T2Space N] {f : E → N}
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) {K : Set E} (hK : IsCompact K) (hinj : InjOn f K)
    (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ InjOn f V := by
  apply hinj.exists_isOpen_superset hK (fun _ _ => hf.continuous.continuousAt)
  intro x hx
  obtain ⟨V, hV, hxV, hinjV⟩ := exists_open_injOn_of_injective_nativeDerivative hf (hi x hx)
  exact ⟨V, hV.mem_nhds hxV, hinjV⟩

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion
