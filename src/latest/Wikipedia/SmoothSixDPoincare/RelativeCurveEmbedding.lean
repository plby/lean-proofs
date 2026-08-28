import Wikipedia.SmoothSixDPoincare.FiniteCurveImmersion
import Wikipedia.SmoothSixDPoincare.RelativeImmersionPatch
import Wikipedia.SmoothSixDPoincare.CompactImmersionEmbedding

/-!
# Embedded curves relative to prescribed neighborhoods

Construct the finite family of native perturbation patches, improve the
derivative on a compact real parameter region, and then remove all distinct
self-intersections. A prescribed closed set is fixed through the actual
homotopy. Only its intersection with the compact region need initially be
embedded and immersive. This permits preserving whole endpoint neighborhoods
when constructing the arcs joining Whitney corners.
-/

noncomputable section

open Set Filter ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldImmersion

open ManifoldSmoothing (MapSmoothingPatch)

variable {G H N : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]

omit [T2Space N] in
/-- Improve an arbitrary compact curve region away from a fixed closed set, preserving
the native injective derivative on a previously immersive compact region. -/
theorem exists_curve_immersion_on_compact_rel_within_target (f : C(ℝ, N))
    (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f) (hdim : 3 ≤ Module.finrank ℝ G)
    {K L C : Set ℝ} (hK : IsCompact K) (hL : IsCompact L)
    (hinj : ∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t))
    (hC : IsClosed C) (hdis : Disjoint L C)
    {D : Set ℝ} {O : Set N} (hO : IsOpen O) (hLO : MapsTo f L O) (hmaps : MapsTo f D O) :
    ∃ g : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧ HomotopicRelWithin f g C D O ∧
      ∀ t ∈ K ∪ L, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  classical
  have hp (t : L) := exists_relative_immersion_patch_at_in_open (J := J) f hC
    (show (t : ℝ) ∉ C from fun ht => Set.disjoint_left.mp hdis t.property ht) hO (hLO t.property)
  choose p T hcompatible hT hn hsub hfixed hsource using hp
  have hcover : L ⊆ ⋃ t : L, interior (T t) := by
    intro t ht
    exact mem_iUnion.mpr ⟨⟨t, ht⟩, mem_interior_iff_mem_nhds.mpr (hn ⟨t, ht⟩)⟩
  obtain ⟨s, hs⟩ := hL.elim_finite_subcover (fun t : L => interior (T t))
    (fun _ => isOpen_interior) hcover
  obtain ⟨g, hg, -, hhom, hderiv⟩ := exists_finite_curve_patch_immersion_within_target
    (fun i : s => p i.1) (fun i : s => T i.1) (fun i => hT i.1) (fun i => hsub i.1)
    f hf (fun i => hcompatible i.1) hdim hK hinj (fun i => hfixed i.1)
      (fun i => hsource i.1) hmaps Finset.univ
  refine ⟨g, hg, hhom, ?_⟩
  intro t ht
  apply hderiv t
  rcases ht with ht | ht
  · exact Or.inl ht
  · obtain ⟨i, his, hti⟩ := mem_iUnion₂.mp (hs ht)
    exact Or.inr (mem_iUnion₂.mpr ⟨⟨i, his⟩, Finset.mem_univ _, interior_subset hti⟩)

omit [T2Space N] in
/-- The original compact relative immersion theorem, forgetting target containment. -/
theorem exists_curve_immersion_on_compact_rel (f : C(ℝ, N))
    (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f) (hdim : 3 ≤ Module.finrank ℝ G)
    {K L C : Set ℝ} (hK : IsCompact K) (hL : IsCompact L)
    (hinj : ∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t))
    (hC : IsClosed C) (hdis : Disjoint L C) :
    ∃ g : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧ f.HomotopicRel g C ∧
      ∀ t ∈ K ∪ L, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  obtain ⟨g, hg, hrel, hi⟩ :=
    exists_curve_immersion_on_compact_rel_within_target f hf hdim hK hL hinj hC hdis
      isOpen_univ (mapsTo_univ f L) (mapsTo_univ f univ)
  exact ⟨g, hg, hrel.homotopicRel, hi⟩

/-- A smooth curve becomes an embedded immersion on a compact parameter region, fixing any
closed set already embedded and immersive there. In particular entire endpoint germs can be kept. -/
theorem exists_relative_compact_curve_embedding_within_target (f : C(ℝ, N))
    (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f) (hdim : 3 ≤ Module.finrank ℝ G)
    {K C : Set ℝ} (hK : IsCompact K) (hC : IsClosed C)
    (hfixed : InjOn f (K ∩ C))
    (hderiv : ∀ t ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t))
    {O : Set N} (hO : IsOpen O) (hmaps : MapsTo f (K \ C) O) :
    ∃ g : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧ HomotopicRelWithin f g C (K \ C) O ∧
      Topology.IsClosedEmbedding (fun t : K => g t) ∧
      ∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  let U : Set ℝ := {t | Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)}
  have hU : IsOpen U := isOpen_injective_derivative hf
  have hCU : K ∩ C ⊆ U := fun t ht => hderiv t ht
  obtain ⟨D, hD, hCD, hDU⟩ := exists_compact_between (hK.inter_right hC) hU hCU
  let L := K \ interior D
  have hL : IsCompact L := hK.inter_right isOpen_interior.isClosed_compl
  have hdis : Disjoint L C := disjoint_left.mpr (fun _ ht htC => ht.2 (hCD ⟨ht.1, htC⟩))
  have hLO : MapsTo f L O := fun t ht =>
    hmaps ⟨ht.1, fun htC => ht.2 (hCD ⟨ht.1, htC⟩)⟩
  obtain ⟨g₁, hg₁, hhom₁, hinj₁⟩ :=
    exists_curve_immersion_on_compact_rel_within_target f hf hdim hD hL
      (fun t ht => hDU ht) hC hdis hO hLO hmaps
  have hKinj : ∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g₁ t) := by
    intro t ht
    apply hinj₁ t
    by_cases htD : t ∈ D
    · exact Or.inl htD
    · exact Or.inr ⟨ht, fun hi => htD (interior_subset hi)⟩
  have hfixed₁ : InjOn g₁ (K ∩ C) := by
    intro t ht s hs hts
    apply hfixed ht hs
    rw [hhom₁.homotopicRel.fst_eq_snd ht.2, hhom₁.homotopicRel.fst_eq_snd hs.2]
    exact hts
  have hd : 2 * Module.finrank ℝ ℝ < Module.finrank ℝ G := by
    simp only [Module.finrank_self]
    omega
  obtain ⟨g₂, hg₂, hhom₂, hemb, hinj₂⟩ :=
    exists_compact_embedding_of_immersion_within_target g₁ hg₁ hd hK hKinj hC hfixed₁
      hO hhom₁.mapsTo_right
  exact ⟨g₂, hg₂, hhom₁.trans hhom₂, hemb, hinj₂⟩

/-- The original relative compact-curve embedding API, forgetting target containment. -/
theorem exists_relative_compact_curve_embedding (f : C(ℝ, N))
    (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f) (hdim : 3 ≤ Module.finrank ℝ G)
    {K C : Set ℝ} (hK : IsCompact K) (hC : IsClosed C)
    (hfixed : InjOn f (K ∩ C))
    (hderiv : ∀ t ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) :
    ∃ g : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧ f.HomotopicRel g C ∧
      Topology.IsClosedEmbedding (fun t : K => g t) ∧
      ∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  obtain ⟨g, hg, hrel, he, hi⟩ :=
    exists_relative_compact_curve_embedding_within_target f hf hdim hK hC hfixed hderiv
      isOpen_univ (mapsTo_univ f (K \ C))
  exact ⟨g, hg, hrel.homotopicRel, he, hi⟩

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion
