import Wikipedia.HopfProblem.OrbitPairPlaneFamilyStability
import Wikipedia.SmoothSixDPoincare.RelativeImmersionPatch

/-!
# Relative immersion regularization on compact cylinder regions

The local patches are chosen from the original map and the fixed closed set.
A finite induction preserves old spatial immersion loci and every future
target-chart constraint. Thus a smooth family of plane maps into a manifold
of dimension at least five can be made immersive on any compact cylinder
region disjoint from the fixed set. Previously immersive compact regions
are retained. All endpoints lying in the fixed set remain exactly fixed.

This does not claim that slice double points disappear.
-/

noncomputable section

open Set Filter ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.PlaneFamily

open Wikipedia.SmoothSixDPoincare
open PlaneImmersion (Plane)
open ManifoldSmoothing (MapSmoothingPatch)

variable {G H N : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]

theorem exists_immersion_patch_step {ι : Type*} [Finite ι]
    (p : ι → MapSmoothingPatch 𝓘(ℝ, ℝ × Plane) J (X := ℝ × Plane) (N := N)) (i : ι)
    (f : C(ℝ × Plane, N)) (hf : ContMDiff 𝓘(ℝ, ℝ × Plane) J ∞ f)
    (hcompatible : ∀ j, (p j).Compatible f) (hdim : 5 ≤ Module.finrank ℝ G)
    {K L C : Set (ℝ × Plane)} (hK : IsCompact K)
    (hinj : ∀ q ∈ K,
      Function.Injective (mfderiv 𝓘(ℝ, Plane) J (fun x => f (q.1, x)) q.2))
    (hLsub : L ⊆ (p i).plateau) (hfixed : ∀ q ∈ C, (p i).cutoff q = 0) :
    ∃ g : C(ℝ × Plane, N), ContMDiff 𝓘(ℝ, ℝ × Plane) J ∞ g ∧
      (∀ j, (p j).Compatible g) ∧ f.HomotopicRel g C ∧
      ∀ q ∈ K ∪ L,
        Function.Injective (mfderiv 𝓘(ℝ, Plane) J (fun x => g (q.1, x)) q.2) := by
  have hinner := (p i).inner_compatible (hcompatible i)
  have hkeep : ∀ᶠ A : G × G in 𝓝 0,
      ∀ j, (p j).Compatible (affinePatch (p i).chart f (p i).cutoff A) := by
    apply eventually_all.mpr
    intro j
    exact eventually_affinePatch_maps_compact_into_open (p i).chart hf (p i).smooth.contDiff
      hinner (p j).outer_compact.isCompact (p j).chart.open_source (hcompatible j)
  have hold := eventually_affinePatch_injective_spatialDerivative (p i).chart hf
    (p i).smooth.contDiff (p i).compact hinner hK hinj
  let Q : (ℝ × Plane → N) → Prop := fun g => (∀ j, (p j).Compatible g) ∧
    ∀ q ∈ K, Function.Injective (mfderiv 𝓘(ℝ, Plane) J (fun x => g (q.1, x)) q.2)
  have hQ : ∀ᶠ A : G × G in 𝓝 0, Q (affinePatch (p i).chart f (p i).cutoff A) :=
    hkeep.and hold
  obtain ⟨g, hg, ⟨hc, hKnew⟩, ⟨Hrel⟩, hplateau⟩ :=
    exists_affine_family_patch_with_property (p i).chart f hf
      (p i).smooth.contDiff (p i).outer_smooth.contDiff (p i).compact
      (hcompatible i) (p i).nested hdim Q hQ
  refine ⟨g, hg, hc, ?_, ?_⟩
  · exact ⟨{ Hrel.toHomotopy with prop' := fun t q hq => Hrel.eq_fst t (hfixed q hq) }⟩
  · intro q hq
    rcases hq with hq | hq
    · exact hKnew q hq
    · exact hplateau q (hLsub hq)

theorem exists_finite_patch_immersion {ι : Type*} [Finite ι]
    (p : ι → MapSmoothingPatch 𝓘(ℝ, ℝ × Plane) J (X := ℝ × Plane) (N := N))
    (L : ι → Set (ℝ × Plane)) (hL : ∀ i, IsCompact (L i))
    (hLsub : ∀ i, L i ⊆ (p i).plateau)
    (f : C(ℝ × Plane, N)) (hf : ContMDiff 𝓘(ℝ, ℝ × Plane) J ∞ f)
    (hcompatible : ∀ i, (p i).Compatible f) (hdim : 5 ≤ Module.finrank ℝ G)
    {K C : Set (ℝ × Plane)} (hK : IsCompact K)
    (hinj : ∀ q ∈ K,
      Function.Injective (mfderiv 𝓘(ℝ, Plane) J (fun x => f (q.1, x)) q.2))
    (hfixed : ∀ i q, q ∈ C → (p i).cutoff q = 0) (s : Finset ι) :
    ∃ g : C(ℝ × Plane, N), ContMDiff 𝓘(ℝ, ℝ × Plane) J ∞ g ∧
      (∀ i, (p i).Compatible g) ∧ f.HomotopicRel g C ∧
      ∀ q ∈ K ∪ ⋃ i ∈ s, L i,
        Function.Injective (mfderiv 𝓘(ℝ, Plane) J (fun x => g (q.1, x)) q.2) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨f, hf, hcompatible, HomotopicRel.refl f, ?_⟩
    simpa only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, union_empty] using hinj
  | @insert i s _ ih =>
    obtain ⟨g₁, hg₁, hc₁, hhom₁, hinj₁⟩ := ih
    have hKold : IsCompact (K ∪ ⋃ j ∈ s, L j) :=
      hK.union (s.isCompact_biUnion (fun j _ => hL j))
    obtain ⟨g₂, hg₂, hc₂, hhom₂, hinj₂⟩ := exists_immersion_patch_step p i g₁ hg₁ hc₁
      hdim hKold hinj₁ (hLsub i) (hfixed i)
    refine ⟨g₂, hg₂, hc₂, hhom₁.trans hhom₂, ?_⟩
    intro q hq
    apply hinj₂ q
    rcases hq with hq | hq
    · exact Or.inl (Or.inl hq)
    · obtain ⟨j, hj, hqj⟩ := mem_iUnion₂.mp hq
      rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact Or.inr hqj
      · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨j, hjs, hqj⟩))

/-- All local data are constructed; the fixed closed set and the new compact region are
arbitrary disjoint subsets of the original time-space cylinder. -/
theorem exists_immersion_on_compact_rel (f : C(ℝ × Plane, N))
    (hf : ContMDiff 𝓘(ℝ, ℝ × Plane) J ∞ f) (hdim : 5 ≤ Module.finrank ℝ G)
    {K L C : Set (ℝ × Plane)} (hK : IsCompact K) (hL : IsCompact L)
    (hinj : ∀ q ∈ K,
      Function.Injective (mfderiv 𝓘(ℝ, Plane) J (fun x => f (q.1, x)) q.2))
    (hC : IsClosed C) (hdis : Disjoint L C) :
    ∃ g : C(ℝ × Plane, N), ContMDiff 𝓘(ℝ, ℝ × Plane) J ∞ g ∧ f.HomotopicRel g C ∧
      ∀ q ∈ K ∪ L,
        Function.Injective (mfderiv 𝓘(ℝ, Plane) J (fun x => g (q.1, x)) q.2) := by
  classical
  have hp (q : L) := ManifoldImmersion.exists_relative_immersion_patch_at (J := J) f hC
    (show (q : ℝ × Plane) ∉ C from fun hq => Set.disjoint_left.mp hdis q.property hq)
  choose p T hcompatible hT hn hsub hfixed using hp
  have hcover : L ⊆ ⋃ q : L, interior (T q) := by
    intro q hq
    exact mem_iUnion.mpr ⟨⟨q, hq⟩, mem_interior_iff_mem_nhds.mpr (hn ⟨q, hq⟩)⟩
  obtain ⟨s, hs⟩ := hL.elim_finite_subcover (fun q : L => interior (T q))
    (fun _ => isOpen_interior) hcover
  obtain ⟨g, hg, -, hhom, hderiv⟩ := exists_finite_patch_immersion
    (fun i : s => p i.1) (fun i : s => T i.1) (fun i => hT i.1) (fun i => hsub i.1)
    f hf (fun i => hcompatible i.1) hdim hK hinj (fun i => hfixed i.1) Finset.univ
  refine ⟨g, hg, hhom, ?_⟩
  intro q hq
  apply hderiv q
  rcases hq with hq | hq
  · exact Or.inl hq
  · obtain ⟨i, his, hqi⟩ := mem_iUnion₂.mp (hs hq)
    exact Or.inr (mem_iUnion₂.mpr ⟨⟨i, his⟩, Finset.mem_univ _, interior_subset hqi⟩)

theorem exists_immersion_on_compact (f : C(ℝ × Plane, N))
    (hf : ContMDiff 𝓘(ℝ, ℝ × Plane) J ∞ f) (hdim : 5 ≤ Module.finrank ℝ G)
    {L C : Set (ℝ × Plane)} (hL : IsCompact L) (hC : IsClosed C) (hdis : Disjoint L C) :
    ∃ g : C(ℝ × Plane, N), ContMDiff 𝓘(ℝ, ℝ × Plane) J ∞ g ∧ f.HomotopicRel g C ∧
      ∀ q ∈ L,
        Function.Injective (mfderiv 𝓘(ℝ, Plane) J (fun x => g (q.1, x)) q.2) := by
  obtain ⟨g, hg, hhom, hderiv⟩ := exists_immersion_on_compact_rel f hf hdim
    isCompact_empty hL (fun _ hq => False.elim hq) hC hdis
  exact ⟨g, hg, hhom, fun q hq => hderiv q (Or.inr hq)⟩

end Wikipedia.HopfProblem.OrbitPair.PlaneFamily
