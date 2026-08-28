import Wikipedia.HopfProblem.DegreeCollapseEmbeddedFirstMeridian

/-!
# Embed a meridian inside a prescribed open set while retaining the whole belt relation

On the compact complement of the small pole cap, retain both the given
open condition and avoidance of the entire belt. Outside that compact set
the original sphere is fixed. This gives open containment of the whole
embedded sphere, without altering its original pole germ.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.BeltMeridianSphere

open NoExoticSixSphere GLOrthonormalization EuclideanEmbedding

theorem exists_embedded_preserving_belt_in_open
    {n : ℕ} {N : Type} [TopologicalSpace N] [ChartedSpace (Vector n) N]
    [IsManifold (𝓡 n) ∞ N] [T2Space N] [CompactSpace N]
    {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (e : EuclideanEmbedding n N) (r : TubularRetraction e) (hdim : 5 < n)
    (f : C(Hemisphere.Sphere 2, N)) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (hinj : InjOn f {x | poleCutoff x = 0})
    (hderiv : ∀ x, poleCutoff x = 0 → Injective (mfderiv (𝓡 2) (𝓡 n) f x))
    (β : C(Y, N)) (honly : ∀ x y, f x = β y → x = pole)
    {O : Set N} (hO : IsOpen O) (hfO : ∀ x, f x ∈ O) :
    ∃ g : C(Hemisphere.Sphere 2, N), ContMDiff (𝓡 2) (𝓡 n) ∞ g ∧
      IsClosedEmbedding g ∧ (∀ x, Injective (mfderiv (𝓡 2) (𝓡 n) g x)) ∧
      f.HomotopicRel g {x | poleCutoff x = 0} ∧
      (∀ x y, g x = β y ↔ f x = β y) ∧ ∀ x, g x ∈ O := by
  let V : Set N := (range β)ᶜ
  have hV : IsOpen V := (isCompact_range β.continuous).isClosed.isOpen_compl
  have hfV : MapsTo f awayPoleCap V := by
    rintro x hx ⟨y, hy⟩
    exact pole_not_mem_awayPoleCap ((honly x y hy.symm) ▸ hx)
  have hfU : MapsTo f awayPoleCap (O ∩ V) := fun x hx => ⟨hfO x, hfV hx⟩
  obtain ⟨g, hg, hgi, hgd, H, hHU⟩ :=
    RelativeTwoSphere.exists_relative_embedding_in_open_on_compact e r hdim f hf
      poleCutoff poleCutoff_smooth poleCutoff_nonneg poleCutoff_norm_le_one hinj hderiv
      awayPoleCap awayPoleCap_compact (O ∩ V) (hO.inter hV) hfU
  have hrel : f.HomotopicRel g {x | poleCutoff x = 0} := ⟨H⟩
  have hgU : MapsTo g awayPoleCap (O ∩ V) := by
    intro x hx
    exact (H.map_one_left x) ▸ hHU 1 x hx
  refine ⟨g, hg, hgi, hgd, hrel, ?_, ?_⟩
  · intro x y
    by_cases hx : x ∈ awayPoleCap
    · constructor
      · intro hxy
        exact ((hgU hx).2 ⟨y, hxy.symm⟩).elim
      · intro hxy
        exact (hfV hx ⟨y, hxy.symm⟩).elim
    · rw [← hrel.fst_eq_snd (poleCutoff_zero_outside x hx)]
  · intro x
    by_cases hx : x ∈ awayPoleCap
    · exact (hgU hx).1
    · rw [← hrel.fst_eq_snd (poleCutoff_zero_outside x hx)]
      exact hfO x

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.BeltMeridianSphere
