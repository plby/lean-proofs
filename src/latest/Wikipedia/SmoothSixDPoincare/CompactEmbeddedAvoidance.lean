import Wikipedia.SmoothSixDPoincare.FiniteEmbeddedAvoidance
import Wikipedia.SmoothSixDPoincare.GlobalImageAvoidance

/-!
# Constructed obstacle avoidance on compact regions while retaining an embedded immersion

Closedness of the obstacle image makes the bad source region compact. A
finite family of actual chart-supported bumps covers it outside the fixed
closed set. The simultaneous good-parameter construction avoids the obstacle
there without creating new source coincidences or losing native immersion.
-/

noncomputable section

open Set ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldImmersion

open GeneralPosition (MapAvoidancePatch)

variable {E E' G H H' Y N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace H']
  {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y]
  [LindelofSpace (E × Y)]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]

/-- Improve avoidance on a compact region `L`, retaining an embedded immersion on `K` and
fixing `C`. Every originally avoiding point remains avoiding, even outside both compact sets. -/
theorem exists_embedded_avoidance_on_compact_of_isClosed_image_controlled
    (f : C(E, N)) (g : C(Y, N)) (A : Set Y)
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hclosed : IsClosed (g '' A))
    (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G)
    {K L C : Set E} (hK : IsCompact K) (hL : IsCompact L) (hC : IsClosed C)
    (hinj : InjOn f K) (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hfixed : ∀ x ∈ L ∩ C, f x ∉ g '' A)
    {O : Set N} (hO : IsOpen O) (hmaps : MapsTo f K O) :
    ∃ f' : C(E, N), ContMDiff 𝓘(ℝ, E) J ∞ f' ∧ HomotopicRelWithin f f' C K O ∧
      Topology.IsClosedEmbedding (fun x : K => f' x) ∧
      (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
      (∀ x y, f' x = f' y → f x = f y) ∧ MapsTo f' K O ∧
      ∀ x, (f x ∉ g '' A ∨ x ∈ L) → f' x ∉ g '' A := by
  classical
  let bad : Set E := L ∩ f ⁻¹' g '' A
  have hbad : IsCompact bad :=
    hL.inter_right (hclosed.preimage f.continuous)
  have hp (x : bad) :
      ∃ p : MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C,
        p.Compatible f ∧ p.cutoff x.1 ≠ 0 :=
    GeneralPosition.exists_avoidance_patch_at (I := 𝓘(ℝ, E)) (J := J) f hC
      (fun hx => hfixed x.1 ⟨x.property.1, hx⟩ x.property.2)
  choose p hpcompatible hpactive using hp
  have hopen (x : bad) : IsOpen (Function.support (p x).cutoff) :=
    isOpen_ne_fun (p x).smooth.continuous continuous_const
  have hcover : bad ⊆ ⋃ x : bad, Function.support (p x).cutoff := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hpactive ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ := hbad.elim_finite_subcover (fun x : bad => Function.support (p x).cutoff)
    hopen hcover
  obtain ⟨f', hf', -, hhom, hderiv', hnoNew, hmaps', havoid⟩ :=
    exists_finite_embedded_image_avoidance_controlled (fun i : s => p i.1) f g A hf hg
      (fun i => hpcompatible i.1) hself hobstacle hK hderiv hO hmaps Finset.univ
  refine ⟨f', hf', hhom, ?_, hderiv', hnoNew, hmaps', ?_⟩
  · let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    apply (f'.continuous.comp continuous_subtype_val).isClosedEmbedding
    intro x y hxy
    exact Subtype.ext (hinj x.property y.property (hnoNew x y hxy))
  · intro x hx
    apply havoid x
    rcases hx with hold | hxL
    · exact Or.inl hold
    · by_cases hxg : f x ∈ g '' A
      · have hx : x ∈ bad := ⟨hxL, hxg⟩
        obtain ⟨i, hi, hix⟩ := mem_iUnion₂.mp (hs hx)
        exact Or.inr ⟨⟨i, hi⟩, Finset.mem_univ _, hix⟩
      · exact Or.inl hxg

/-- The original compact avoidance statement follows by forgetting homotopy containment. -/
theorem exists_embedded_avoidance_on_compact_of_isClosed_image
    (f : C(E, N)) (g : C(Y, N)) (A : Set Y)
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hclosed : IsClosed (g '' A))
    (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G)
    {K L C : Set E} (hK : IsCompact K) (hL : IsCompact L) (hC : IsClosed C)
    (hinj : InjOn f K) (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hfixed : ∀ x ∈ L ∩ C, f x ∉ g '' A)
    {O : Set N} (hO : IsOpen O) (hmaps : MapsTo f K O) :
    ∃ f' : C(E, N), ContMDiff 𝓘(ℝ, E) J ∞ f' ∧ f.HomotopicRel f' C ∧
      Topology.IsClosedEmbedding (fun x : K => f' x) ∧
      (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
      (∀ x y, f' x = f' y → f x = f y) ∧ MapsTo f' K O ∧
      ∀ x, (f x ∉ g '' A ∨ x ∈ L) → f' x ∉ g '' A := by
  obtain ⟨f', hf', hhom, hemb, hd, hnoNew, hmaps', havoid⟩ :=
    exists_embedded_avoidance_on_compact_of_isClosed_image_controlled f g A hf hg
      hclosed hself hobstacle hK hL hC hinj hderiv hfixed hO hmaps
  exact ⟨f', hf', hhom.homotopicRel, hemb, hd, hnoNew, hmaps', havoid⟩

/-- Closed full-image avoidance without an additional compact-region target constraint. -/
theorem exists_embedded_avoidance_on_compact_of_isClosed_range (f : C(E, N)) (g : C(Y, N))
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hclosed : IsClosed (range g))
    (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G)
    {K L C : Set E} (hK : IsCompact K) (hL : IsCompact L) (hC : IsClosed C)
    (hinj : InjOn f K) (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hfixed : ∀ x ∈ L ∩ C, f x ∉ range g) :
    ∃ f' : C(E, N), ContMDiff 𝓘(ℝ, E) J ∞ f' ∧ f.HomotopicRel f' C ∧
      Topology.IsClosedEmbedding (fun x : K => f' x) ∧
      (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
      (∀ x y, f' x = f' y → f x = f y) ∧
      ∀ x, (f x ∉ range g ∨ x ∈ L) → f' x ∉ range g := by
  obtain ⟨f', hf', hhom, hemb, hd, hnoNew, -, havoid⟩ :=
    exists_embedded_avoidance_on_compact_of_isClosed_image f g univ hf hg
      (by simpa only [image_univ] using hclosed) hself hobstacle hK hL hC hinj hderiv
      (by simpa only [image_univ] using hfixed) isOpen_univ (fun _ _ => mem_univ _)
  refine ⟨f', hf', hhom, hemb, hd, hnoNew, ?_⟩
  simpa only [image_univ] using havoid

variable [CompactSpace Y]

/-- Improve avoidance on a compact region `L`, retaining an embedded immersion on `K` and
fixing `C`. Every originally avoiding point remains avoiding, even outside both compact sets. -/
theorem exists_embedded_avoidance_on_compact (f : C(E, N)) (g : C(Y, N))
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G)
    {K L C : Set E} (hK : IsCompact K) (hL : IsCompact L) (hC : IsClosed C)
    (hinj : InjOn f K) (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hfixed : ∀ x ∈ L ∩ C, f x ∉ range g) :
    ∃ f' : C(E, N), ContMDiff 𝓘(ℝ, E) J ∞ f' ∧ f.HomotopicRel f' C ∧
      Topology.IsClosedEmbedding (fun x : K => f' x) ∧
      (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
      (∀ x y, f' x = f' y → f x = f y) ∧
      ∀ x, (f x ∉ range g ∨ x ∈ L) → f' x ∉ range g :=
  exists_embedded_avoidance_on_compact_of_isClosed_range f g hf hg
    (isCompact_range g.continuous).isClosed hself hobstacle hK hL hC hinj hderiv hfixed

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion
