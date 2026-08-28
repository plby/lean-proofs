import Wikipedia.HopfProblem.DegreeCollapseImmersedDoublePairCancellation
import Wikipedia.HopfProblem.DegreeCollapseDoublePointCounting

/-!
# Finite Whitney reduction for an actual immersion with simple double fibers

Every step constructs a new map, retains its native smooth immersion and
self-transversality, and removes exactly two actual unordered double points.
Induction terminates with at most one double point. If the original unordered
parity is zero, the endpoint is injective. Neither the fiber condition nor
the initial parity is inferred from self-transversality alone.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open SphereSelfIntersections DoublePointCounting

variable {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (Vector 6) M] [IsManifold (𝓡 6) ∞ M] [SimplyConnectedSpace M]

theorem exists_cancellation_decreasing_unordered (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) f x))
    (ht : ∀ x y, x ≠ y → f x = f y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) f y)))
    (hd : HasOnlyDoubleFibers f) (hcard : 1 < Nat.card (Unordered f)) :
    ∃ g : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ g ∧ f.Homotopic g ∧
      (∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) g x)) ∧
      (∀ x y, x ≠ y → g x = g y → Surjective
        ((mfderiv (𝓡 3) (𝓡 6) g x).coprod (mfderiv (𝓡 3) (𝓡 6) g y))) ∧
      HasOnlyDoubleFibers g ∧ pairs g ⊆ pairs f ∧
      Nat.card (Unordered g) + 2 = Nat.card (Unordered f) ∧
      unorderedParity g = unorderedParity f := by
  have hfin := finite_pairs hf ht hi
  obtain ⟨p, q, hpq⟩ := exists_distinct_double_values hd hfin hcard
  have hp := hd p.val.1 p.val.2 p.property.1 p.property.2
  have hq := hd q.val.1 q.val.2 q.property.1 q.property.2
  obtain ⟨g, hg, hrel, hgi, hgt, hpair⟩ := exists_cancellation_of_two_double_points f hf hi ht
    p.property.1 q.property.1 p.property.2 q.property.2 hpq hp hq
  have hsub : pairs g ⊆ pairs f := hpair ▸ sdiff_subset
  have hcount : Nat.card (Unordered g) + 2 = Nat.card (Unordered f) :=
    unordered_card_after_two_value_removal hfin p.property.1 q.property.1 p.property.2
      q.property.2 hpq hp hq hpair
  exact ⟨g, hg, hrel, hgi, hgt, onlyDoubleFibers_of_pairs_subset hd hsub, hsub,
    hcount, unorderedParity_eq_of_card_drop_two hcount⟩

theorem exists_reduction_to_at_most_one_double_point (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) f x))
    (ht : ∀ x y, x ≠ y → f x = f y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) f y)))
    (hd : HasOnlyDoubleFibers f) :
    ∃ g : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ g ∧ f.Homotopic g ∧
      (∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) g x)) ∧
      (∀ x y, x ≠ y → g x = g y → Surjective
        ((mfderiv (𝓡 3) (𝓡 6) g x).coprod (mfderiv (𝓡 3) (𝓡 6) g y))) ∧
      HasOnlyDoubleFibers g ∧ pairs g ⊆ pairs f ∧
      Nat.card (Unordered g) ≤ 1 ∧ unorderedParity g = unorderedParity f := by
  generalize hn : Nat.card (Unordered f) = n
  induction n using Nat.strong_induction_on generalizing f with
  | h n ih =>
    by_cases hsmall : n ≤ 1
    · exact ⟨f, hf, ContinuousMap.Homotopic.refl f, hi, ht, hd, subset_rfl,
        hn ▸ hsmall, rfl⟩
    have hlarge : 1 < Nat.card (Unordered f) := by omega
    obtain ⟨g, hg, hrel, hgi, hgt, hgd, hsub, hcount, hparity⟩ :=
      exists_cancellation_decreasing_unordered f hf hi ht hd hlarge
    have hless : Nat.card (Unordered g) < n := by omega
    obtain ⟨k, hk, hrel', hki, hkt, hkd, hsub', hsmall', hparity'⟩ :=
      ih (Nat.card (Unordered g)) hless g hg hgi hgt hgd rfl
    exact ⟨k, hk, hrel.trans hrel', hki, hkt, hkd, hsub'.trans hsub, hsmall',
      hparity'.trans hparity⟩

theorem exists_injective_immersion_of_even_double_points (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) f x))
    (ht : ∀ x y, x ≠ y → f x = f y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) f y)))
    (hd : HasOnlyDoubleFibers f) (heven : unorderedParity f = 0) :
    ∃ g : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ g ∧ f.Homotopic g ∧
      (∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) g x)) ∧ Injective g := by
  obtain ⟨g, hg, hrel, hgi, hgt, _, _, hsmall, hparity⟩ :=
    exists_reduction_to_at_most_one_double_point f hf hi ht hd
  exact ⟨g, hg, hrel, hgi, injective_of_small_even_unordered_card
    (finite_pairs hg hgt hgi) hsmall (hparity.trans heven)⟩

theorem exists_embedded_representative_of_even_double_points (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) f x))
    (ht : ∀ x y, x ≠ y → f x = f y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) f y)))
    (hd : HasOnlyDoubleFibers f) (heven : unorderedParity f = 0) :
    ∃ g : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ g ∧ f.Homotopic g ∧
      (∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) g x)) ∧ IsClosedEmbedding g := by
  obtain ⟨g, hg, hrel, hgi, hinj⟩ :=
    exists_injective_immersion_of_even_double_points f hf hi ht hd heven
  exact ⟨g, hg, hrel, hgi, g.continuous.isClosedEmbedding hinj⟩

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource
