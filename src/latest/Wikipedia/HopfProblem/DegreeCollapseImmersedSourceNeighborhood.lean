import Wikipedia.NoExoticSixSphere.ImmersedSphereDoublePoints
import Mathlib.Topology.Separation.Regular

/-!
# Embedded source neighborhoods inside an actual immersed sphere

Closedness of the genuine off-diagonal coincidence set excludes local
self-overlap. Compactness then thickens any injective compact source locus
to a neighborhood whose whole compact closure is still embedded. No global
injectivity of the original immersion is assumed.
-/

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

omit [TopologicalSpace Y] in
theorem exists_open_injOn_of_closed_pairs {f : X → Y}
    (hp : IsClosed {p : X × X | p.1 ≠ p.2 ∧ f p.1 = f p.2}) (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ InjOn f U := by
  have hx : (x, x) ∈ {p : X × X | p.1 ≠ p.2 ∧ f p.1 = f p.2}ᶜ := by
    simp
  obtain ⟨U, V, hU, hxU, hV, hxV, hUV⟩ :=
    mem_nhds_prod_iff'.mp (hp.isOpen_compl.mem_nhds hx)
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, ?_⟩
  intro y hy z hz he
  by_contra hne
  exact hUV (a := (y, z)) ⟨hy.1, hz.2⟩ ⟨hne, he⟩

theorem exists_compact_embedded_neighborhood
    [LocallyCompactSpace X] [RegularSpace X] [T2Space Y] {f : X → Y}
    (hf : Continuous f) (hp : IsClosed {p : X × X | p.1 ≠ p.2 ∧ f p.1 = f p.2})
    {K W : Set X} (hK : IsCompact K) (hinj : InjOn f K)
    (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧ closure U ⊆ W ∧
      IsCompact (closure U) ∧ InjOn f (closure U) ∧
      IsClosedEmbedding (fun x : closure U => f x) := by
  obtain ⟨V, hV, hKV, hiV⟩ := hinj.exists_isOpen_superset hK
    (fun _ _ => hf.continuousAt) (fun x _ => by
      obtain ⟨O, hO, hxO, hiO⟩ := exists_open_injOn_of_closed_pairs hp x
      exact ⟨O, hO.mem_nhds hxO, hiO⟩)
  obtain ⟨U, hU, hKU, hUV, hUc⟩ := exists_open_between_and_isCompact_closure
    hK (hV.inter hW) (fun x hx => ⟨hKV hx, hKW hx⟩)
  have hiU : InjOn f (closure U) := hiV.mono (hUV.trans inter_subset_left)
  let : CompactSpace (closure U) := isCompact_iff_compactSpace.mp hUc
  refine ⟨U, hU, hKU, hUV.trans inter_subset_right, hUc, hiU, ?_⟩
  exact (hf.comp continuous_subtype_val).isClosedEmbedding
    (fun x y hxy => Subtype.ext (hiU x.property y.property hxy))

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (NoExoticSixSphere.GLOrthonormalization.Vector 6) M]
  [IsManifold (𝓡 6) ∞ M]

/-- The compact embedded neighborhood is constructed in the original sphere atlas. -/
theorem exists_sphere_source_neighborhood {f : Sphere 3 → M}
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) f x))
    {K W : Set (Sphere 3)} (hK : IsCompact K) (hinj : InjOn f K)
    (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ U : Set (Sphere 3), IsOpen U ∧ K ⊆ U ∧ closure U ⊆ W ∧
      IsCompact (closure U) ∧ InjOn f (closure U) ∧
      IsClosedEmbedding (fun x : closure U => f x) :=
  exists_compact_embedded_neighborhood hf.continuous
    (NoExoticSixSphere.SphereSelfIntersections.isClosed_pairs hf hi) hK hinj hW hKW

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource
