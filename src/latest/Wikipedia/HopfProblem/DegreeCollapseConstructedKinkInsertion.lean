import Wikipedia.HopfProblem.DegreeCollapseKinkInsertionCounting

/-!
# Native kink insertion without supplied chart or support hypotheses

Starting with the original smooth self-transverse immersion, construct its
globally isolated branch chart, a cutoff, and one positive fitting scale.
The actual new immersion is homotopic to the original, remains
self-transverse with simple fibers, and gains exactly one unordered point.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open SphereSelfIntersections DoublePointCounting

variable {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (Vector 6) M] [IsManifold (𝓡 6) ∞ M]

theorem exists_insertion_increasing_unordered (F : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ F)
    (hi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) F x))
    (ht : ∀ x y, x ≠ y → F x = F y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) F x).coprod (mfderiv (𝓡 3) (𝓡 6) F y)))
    (hd : HasOnlyDoubleFibers F) :
    ∃ g : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ g ∧ F.Homotopic g ∧
      (∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) g x)) ∧
      (∀ x y, x ≠ y → g x = g y → Surjective
        ((mfderiv (𝓡 3) (𝓡 6) g x).coprod (mfderiv (𝓡 3) (𝓡 6) g y))) ∧
      HasOnlyDoubleFibers g ∧ Nat.card (Unordered g) = Nat.card (Unordered F) + 1 := by
  obtain ⟨P⟩ := nonempty_kinkPatchData F hf hi ht
  obtain ⟨g, hg, H, hgi, heq, _⟩ := KinkPatchData.exists_native_immersed_insertion F P hf hi
  have he : (g : Sphere 3 → M) = P.insertedMap := funext heq
  refine ⟨g, hg, H, hgi, ?_, ?_, ?_⟩
  · rw [he]
    exact P.selfTransverse_insertedMap hf ht
  · rw [he]
    exact P.onlyDoubleFibers_insertedMap hd
  · rw [he]
    exact P.unordered_card_insertedMap (finite_pairs hf ht hi)

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource
