import Wikipedia.HopfProblem.DegreeCollapseImmersedArcPairCancellation
import Wikipedia.HopfProblem.DegreeCollapseImmersedCrossingOrder
import Wikipedia.NoExoticSixSphere.Topology.SimplyConnectedSphere

/-!
# Cancel two original double points without a supplied disk, chart, or sign

Choose the second branch ordering before constructing the source arcs.
Simple connectivity supplies coherent orientations, and the standard
three-sphere supplies paths and nonzero endpoint directions. The entire
Whitney construction gives an actual smooth self-transverse endpoint,
homotopic to the original immersion, with exactly the original pairs over
the two selected values removed. The two-preimage fiber hypotheses remain
explicit; pairwise transversality alone does not exclude triple values.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open Wikipedia.SmoothSixDPoincare WhitneyPairModel
open OrbitPair.DeterminantSignCover

variable {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (Vector 6) M] [IsManifold (𝓡 6) ∞ M] [SimplyConnectedSpace M]
  (oN : Orientation (tangentBundleCore (𝓡 3) (Sphere 3)))
  (oM : Orientation (tangentBundleCore (𝓡 6) M))
  (J : Sheet ≃L[ℝ] Vector 3) (K : (Vector 3 × Vector 3) ≃L[ℝ] Vector 6)

include J

theorem exists_cancellation_of_opposite_ordered_pairs (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) f x))
    (ht : ∀ x y, x ≠ y → f x = f y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) f y)))
    {x₀ x₁ y₀ y₁ : Sphere 3} (h₀ : x₀ ≠ y₀) (h₁ : x₁ ≠ y₁)
    (hc₀ : f x₀ = f y₀) (hc₁ : f x₁ = f y₁) (hvalues : f x₀ ≠ f x₁)
    (hfib₀ : ∀ z, f z = f x₀ → z = x₀ ∨ z = y₀)
    (hfib₁ : ∀ z, f z = f x₁ → z = x₁ ∨ z = y₁)
    (hsign : ImmersedCorner.intersectionSign oN oM K f x₀ y₀ ≠
      ImmersedCorner.intersectionSign oN oM K f x₁ y₁) :
    ∃ g : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ g ∧ f.Homotopic g ∧
      (∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) g x)) ∧
      (∀ x y, x ≠ y → g x = g y → Surjective
        ((mfderiv (𝓡 3) (𝓡 6) g x).coprod (mfderiv (𝓡 3) (𝓡 6) g y))) ∧
      SphereSelfIntersections.pairs g = SphereSelfIntersections.pairs f \
        {p : Sphere 3 × Sphere 3 | f p.1 ∈ ({f x₀, f x₁} : Set M)} := by
  obtain ⟨u, hu⟩ := exists_ne (0 : Vector 3)
  obtain ⟨a, b, hab, _⟩ := exists_disjoint_clean_joining_arcs hf hi ht h₀ h₁ hc₀ hc₁ hvalues
    (PathConnectedSpace.somePath x₀ x₁) (PathConnectedSpace.somePath y₀ y₁) hu hu hu hu
  exact exists_cancellation_from_clean_arc_pair oN oM J K f hf hi ht a b hab hc₀ hc₁
    hu hu hu hu hfib₀ hfib₁ hsign

include oN oM K

theorem exists_cancellation_of_two_double_points_oriented (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) f x))
    (ht : ∀ x y, x ≠ y → f x = f y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) f y)))
    {x₀ x₁ y₀ y₁ : Sphere 3} (h₀ : x₀ ≠ y₀) (h₁ : x₁ ≠ y₁)
    (hc₀ : f x₀ = f y₀) (hc₁ : f x₁ = f y₁) (hvalues : f x₀ ≠ f x₁)
    (hfib₀ : ∀ z, f z = f x₀ → z = x₀ ∨ z = y₀)
    (hfib₁ : ∀ z, f z = f x₁ → z = x₁ ∨ z = y₁) :
    ∃ g : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ g ∧ f.Homotopic g ∧
      (∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) g x)) ∧
      (∀ x y, x ≠ y → g x = g y → Surjective
        ((mfderiv (𝓡 3) (𝓡 6) g x).coprod (mfderiv (𝓡 3) (𝓡 6) g y))) ∧
      SphereSelfIntersections.pairs g = SphereSelfIntersections.pairs f \
        {p : Sphere 3 × Sphere 3 | f p.1 ∈ ({f x₀, f x₁} : Set M)} := by
  obtain ⟨u, v, huv, hsign⟩ := ImmersedCorner.exists_ordering_with_opposite_sign oN oM K
    (by simp) x₀ y₀ hc₁ (ht y₁ x₁ (Ne.symm h₁) hc₁.symm)
  rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · rw [hu, hv] at hsign
    exact exists_cancellation_of_opposite_ordered_pairs oN oM J K f hf hi ht
      h₀ h₁ hc₀ hc₁ hvalues hfib₀ hfib₁ hsign
  · rw [hu, hv] at hsign
    have hvalues' : f x₀ ≠ f y₁ := by rwa [← hc₁]
    have hfib₁' : ∀ z, f z = f y₁ → z = y₁ ∨ z = x₁ := by
      intro z hz
      exact (hfib₁ z (hz.trans hc₁.symm)).symm
    obtain ⟨g, hg, hrel, hgi, hgt, hpairs⟩ := exists_cancellation_of_opposite_ordered_pairs
      oN oM J K f hf hi ht h₀ (Ne.symm h₁) hc₀ hc₁.symm hvalues' hfib₀ hfib₁' hsign
    rw [← hc₁] at hpairs
    exact ⟨g, hg, hrel, hgi, hgt, hpairs⟩

omit oN oM J K in
theorem exists_cancellation_of_two_double_points (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) f x))
    (ht : ∀ x y, x ≠ y → f x = f y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) f y)))
    {x₀ x₁ y₀ y₁ : Sphere 3} (h₀ : x₀ ≠ y₀) (h₁ : x₁ ≠ y₁)
    (hc₀ : f x₀ = f y₀) (hc₁ : f x₁ = f y₁) (hvalues : f x₀ ≠ f x₁)
    (hfib₀ : ∀ z, f z = f x₀ → z = x₀ ∨ z = y₀)
    (hfib₁ : ∀ z, f z = f x₁ → z = x₁ ∨ z = y₁) :
    ∃ g : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ g ∧ f.Homotopic g ∧
      (∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) g x)) ∧
      (∀ x y, x ≠ y → g x = g y → Surjective
        ((mfderiv (𝓡 3) (𝓡 6) g x).coprod (mfderiv (𝓡 3) (𝓡 6) g y))) ∧
      SphereSelfIntersections.pairs g = SphereSelfIntersections.pairs f \
        {p : Sphere 3 × Sphere 3 | f p.1 ∈ ({f x₀, f x₁} : Set M)} := by
  let : SimplyConnectedSpace (Sphere 3) := EuclideanSphere.simplyConnectedSpace 1
  let : LocallyPathConnectedSpace (Sphere 3) :=
    ChartedSpace.locallyPathConnectedSpace (Vector 3) (Sphere 3)
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace (Vector 6) M
  obtain ⟨oN⟩ := nonempty_orientation (tangentBundleCore (𝓡 3) (Sphere 3))
  obtain ⟨oM⟩ := nonempty_orientation (tangentBundleCore (𝓡 6) M)
  let J : Sheet ≃L[ℝ] Vector 3 := ContinuousLinearEquiv.ofFinrankEq
    (by simp [Sheet, Plane, Module.finrank_prod])
  let K : (Vector 3 × Vector 3) ≃L[ℝ] Vector 6 := ContinuousLinearEquiv.ofFinrankEq
    (by simp [Module.finrank_prod])
  exact exists_cancellation_of_two_double_points_oriented oN oM J K f hf hi ht
    h₀ h₁ hc₀ hc₁ hvalues hfib₀ hfib₁

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource
