import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Separation.Hausdorff

/-!
# One injective local-diffeomorphism neighborhood of a compact embedded locus

The local-diffeomorphism locus is open by its actual partial-diffeomorphism
witnesses. Local injectivity and compactness give one common injectivity
neighborhood, retaining any specified open neighborhood of the compact locus.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere

variable {E F H H' X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]

theorem isOpen_localDiffeomorphLocus (f : X → Y) :
    IsOpen {x | IsLocalDiffeomorphAt I J ∞ f x} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨Φ, hx, heq⟩
  exact Filter.mem_of_superset (Φ.open_source.mem_nhds hx) (fun y hy ↦ ⟨Φ, hy, heq⟩)

theorem exists_injective_localDiffeomorph_neighborhood [T2Space Y]
    {f : X → Y} {K U : Set X} (hK : IsCompact K) (hinj : InjOn f K)
    (hl : ∀ x ∈ K, IsLocalDiffeomorphAt I J ∞ f x)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ V : Set X, IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ InjOn f V ∧
      ∀ x ∈ V, IsLocalDiffeomorphAt I J ∞ f x := by
  have hlocal : ∀ x ∈ K, ∃ W ∈ nhds x, InjOn f W := by
    intro x hx
    obtain ⟨Φ, hxΦ, heq⟩ := hl x hx
    refine ⟨Φ.source, Φ.open_source.mem_nhds hxΦ, ?_⟩
    intro y hy z hz he
    apply Φ.injOn hy hz
    rw [← heq hy, ← heq hz]
    exact he
  obtain ⟨V, hV, hKV, hVi⟩ := hinj.exists_isOpen_superset hK
    (fun x hx ↦ (hl x hx).contMDiffAt.continuousAt) hlocal
  refine ⟨V ∩ ({x | IsLocalDiffeomorphAt I J ∞ f x} ∩ U),
    hV.inter ((isOpen_localDiffeomorphLocus f).inter hU),
    fun x hx ↦ ⟨hKV hx, hl x hx, hKU hx⟩,
    fun _ hx ↦ hx.2.2, hVi.mono inter_subset_left, fun _ hx ↦ hx.2.1⟩

end NoExoticSixSphere
