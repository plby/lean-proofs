import Wikipedia.SmoothSixDPoincare.FiniteSelfIntersectionRemoval
import Wikipedia.SmoothSixDPoincare.SeparatingCollisionPatch
import Wikipedia.SmoothSixDPoincare.CompactDoublePoints

/-!
# Turning a compact immersive region into an embedded one, relative to a fixed set

The original distinct collision set is compact. A separating smooth cutoff
is constructed at every collision, moving a point outside the fixed set.
A finite subcover supplies the chart perturbations. Their no-new-collision
property eliminates every distinct collision while preserving immersion.
-/

noncomputable section

open Set ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldImmersion

open GeneralPosition (MapAvoidancePatch)

variable {E G H N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]

/-- In target dimension greater than twice the source dimension, a compact immersive region
can be made embedded, fixing a closed set already injective on that region. All separating
patches and perturbations are constructed from the original smooth map. -/
theorem exists_compact_embedding_of_immersion_within_target (f : C(E, N))
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f)
    (hdim : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    {K C : Set E} (hK : IsCompact K)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hC : IsClosed C) (hfixed : InjOn f (K ∩ C))
    {O : Set N} (hO : IsOpen O) (hmaps : MapsTo f (K \ C) O) :
    ∃ g : C(E, N), ContMDiff 𝓘(ℝ, E) J ∞ g ∧ HomotopicRelWithin f g C (K \ C) O ∧
      Topology.IsClosedEmbedding (fun x : K => g x) ∧
      ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J g x) := by
  classical
  let bad := doublePoints f K
  have hbad : IsCompact bad := isCompact_doublePoints_of_injective_nativeDerivative hf hK hinj
  have hp (q : bad) :
      ∃ p : MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C,
        p.Compatible f ∧ p.cutoff q.1.1 ≠ p.cutoff q.1.2 ∧ p.chart.source ⊆ O := by
    have hq := q.property
    rcases hq with ⟨hx, hy, hne, heq⟩
    have hnot : ¬ (q.1.1 ∈ C ∧ q.1.2 ∈ C) := by
      rintro ⟨hxC, hyC⟩
      exact hne (hfixed ⟨hx, hxC⟩ ⟨hy, hyC⟩ heq)
    exact exists_separating_patch_of_not_both_fixed_in_open f hC hne hnot hO
      (fun hxC => hmaps ⟨hx, hxC⟩) (fun hyC => hmaps ⟨hy, hyC⟩)
  choose p hpcompatible hpactive hpsource using hp
  let U (q : bad) : Set (E × E) := {r | (p q).cutoff r.1 ≠ (p q).cutoff r.2}
  have hU (q : bad) : IsOpen (U q) := isOpen_ne_fun
    ((p q).smooth.continuous.comp continuous_fst) ((p q).smooth.continuous.comp continuous_snd)
  have hcover : bad ⊆ ⋃ q : bad, U q := by
    intro q hq
    exact mem_iUnion.mpr ⟨⟨q, hq⟩, hpactive ⟨q, hq⟩⟩
  obtain ⟨s, hs⟩ := hbad.elim_finite_subcover U hU hcover
  refine exists_embedding_of_finite_separating_patches_within_target
    (fun i : s => p i.1) f hf (fun i => hpcompatible i.1) hdim hK hinj ?_
    (fun i => hpsource i.1) hmaps
  intro x hx y hy hne heq
  have hxy : (x, y) ∈ bad := ⟨hx, hy, hne, heq⟩
  obtain ⟨i, hi, hsep⟩ := mem_iUnion₂.mp (hs hxy)
  exact ⟨⟨i, hi⟩, hsep⟩

/-- The original compact embedding theorem, forgetting the controlled target. -/
theorem exists_compact_embedding_of_immersion (f : C(E, N))
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f)
    (hdim : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    {K C : Set E} (hK : IsCompact K)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hC : IsClosed C) (hfixed : InjOn f (K ∩ C)) :
    ∃ g : C(E, N), ContMDiff 𝓘(ℝ, E) J ∞ g ∧ f.HomotopicRel g C ∧
      Topology.IsClosedEmbedding (fun x : K => g x) ∧
      ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J g x) := by
  obtain ⟨g, hg, hrel, he, hi⟩ :=
    exists_compact_embedding_of_immersion_within_target f hf hdim hK hinj hC hfixed
      isOpen_univ (mapsTo_univ f (K \ C))
  exact ⟨g, hg, hrel.homotopicRel, he, hi⟩

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion
