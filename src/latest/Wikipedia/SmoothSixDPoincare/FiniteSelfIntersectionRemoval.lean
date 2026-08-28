import Wikipedia.SmoothSixDPoincare.SelfIntersectionRemovalStep

/-!
# Finite self-intersection removal in the original target manifold

Every new coincidence is an old coincidence, so previously obtained pair
separations are preserved exactly. Compact immersion stability and the finite
future-chart constraints are retained at each step.
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
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N]

/-- After finitely many steps, all remaining coincidences have equal values for every treated
cutoff, and the native derivatives on the prescribed compact region remain injective. -/
theorem exists_finite_selfIntersection_removal_within_target
    {ι : Type*} [Finite ι] {C K : Set E}
    (p : ι → MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C)
    (f : C(E, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f)
    (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hK : IsCompact K) (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    {D : Set E} {O : Set N} (hsource : ∀ i, (p i).chart.source ⊆ O)
    (hmaps : MapsTo f D O) (s : Finset ι) :
    ∃ g : C(E, N), ContMDiff 𝓘(ℝ, E) J ∞ g ∧ (∀ j, (p j).Compatible g) ∧
      HomotopicRelWithin f g C D O ∧
      (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J g x)) ∧
      ∀ x y, g x = g y → f x = f y ∧ ∀ i ∈ s, (p i).cutoff x = (p i).cutoff y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨f, hf, hcompatible, HomotopicRelWithin.refl f C hmaps, hinj,
      fun _ _ hxy => ⟨hxy, fun _ hi => False.elim (Finset.notMem_empty _ hi)⟩⟩
  | @insert i s _ ih =>
    obtain ⟨g₁, hg₁, hc₁, hhom₁, hinj₁, hpair₁⟩ := ih
    obtain ⟨g₂, hg₂, hc₂, hhom₂, hinj₂, hpair₂⟩ :=
      exists_selfIntersection_removal_step_within_target p i g₁ hg₁ hc₁ hdim hK hinj₁
        (hsource i) hhom₁.mapsTo_right
    refine ⟨g₂, hg₂, hc₂, hhom₁.trans hhom₂, hinj₂, ?_⟩
    intro x y hxy
    have hnew := hpair₂ x y hxy
    have hold := hpair₁ x y hnew.1
    refine ⟨hold.1, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hjs
    · exact hnew.2
    · exact hold.2 j hjs

/-- The original finite collision-removal API follows by forgetting target containment. -/
theorem exists_finite_selfIntersection_removal {ι : Type*} [Finite ι] {C K : Set E}
    (p : ι → MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C)
    (f : C(E, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f)
    (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hK : IsCompact K) (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (s : Finset ι) :
    ∃ g : C(E, N), ContMDiff 𝓘(ℝ, E) J ∞ g ∧ (∀ j, (p j).Compatible g) ∧
      f.HomotopicRel g C ∧ (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J g x)) ∧
      ∀ x y, g x = g y → f x = f y ∧ ∀ i ∈ s, (p i).cutoff x = (p i).cutoff y := by
  obtain ⟨g, hg, hc, hrel, hi, hp⟩ :=
    exists_finite_selfIntersection_removal_within_target p f hf hcompatible hdim hK hinj
      (fun _ => subset_univ _) (mapsTo_univ f univ) s
  exact ⟨g, hg, hc, hrel.homotopicRel, hi, hp⟩

variable [T2Space N]

/-- A finite patch family separating every original distinct collision gives a genuine compact
embedding and still-injective native derivatives, through a relative homotopy. -/
theorem exists_embedding_of_finite_separating_patches_within_target
    {ι : Type*} [Finite ι] {C K : Set E}
    (p : ι → MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C)
    (f : C(E, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f)
    (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hK : IsCompact K) (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hseparate : ∀ x ∈ K, ∀ y ∈ K, x ≠ y → f x = f y →
      ∃ i, (p i).cutoff x ≠ (p i).cutoff y)
    {D : Set E} {O : Set N} (hsource : ∀ i, (p i).chart.source ⊆ O)
    (hmaps : MapsTo f D O) :
    ∃ g : C(E, N), ContMDiff 𝓘(ℝ, E) J ∞ g ∧ HomotopicRelWithin f g C D O ∧
      Topology.IsClosedEmbedding (fun x : K => g x) ∧
      ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J g x) := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨g, hg, -, hhom, hinjg, hpairs⟩ :=
    exists_finite_selfIntersection_removal_within_target p f hf hcompatible hdim hK hinj
      hsource hmaps Finset.univ
  refine ⟨g, hg, hhom, ?_, hinjg⟩
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply (g.continuous.comp continuous_subtype_val).isClosedEmbedding
  intro x y hxy
  apply Subtype.ext
  by_contra hne
  obtain ⟨hold, hcutoffs⟩ := hpairs x y hxy
  obtain ⟨i, hi⟩ := hseparate x x.property y y.property hne hold
  exact hi (hcutoffs i (Finset.mem_univ i))

/-- The original finite-patch embedding statement, forgetting its controlled target. -/
theorem exists_embedding_of_finite_separating_patches {ι : Type*} [Finite ι] {C K : Set E}
    (p : ι → MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C)
    (f : C(E, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f)
    (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hK : IsCompact K) (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hseparate : ∀ x ∈ K, ∀ y ∈ K, x ≠ y → f x = f y →
      ∃ i, (p i).cutoff x ≠ (p i).cutoff y) :
    ∃ g : C(E, N), ContMDiff 𝓘(ℝ, E) J ∞ g ∧ f.HomotopicRel g C ∧
      Topology.IsClosedEmbedding (fun x : K => g x) ∧
      ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J g x) := by
  obtain ⟨g, hg, hrel, he, hi⟩ :=
    exists_embedding_of_finite_separating_patches_within_target p f hf hcompatible hdim
      hK hinj hseparate (fun _ => subset_univ _) (mapsTo_univ f univ)
  exact ⟨g, hg, hrel.homotopicRel, he, hi⟩

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion
