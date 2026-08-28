import Wikipedia.HopfProblem.OrbitPairSubdivisionPrefixSimplex

/-!
# The native barycentric subdivision of a standard simplex is homeomorphic to it

Sorting the coordinates supplies an explicit prefix simplex and explicit
nonnegative weights for every point. This proves surjectivity of the actual
barycentric map. Combined with its checked closed embedding, it gives a
homeomorphism, also transported to mathlib's actual `SSet.sd.obj Δ[n]`.
-/

noncomputable section

universe u

open CategoryTheory Simplicial

namespace Wikipedia.HopfProblem.OrbitPair.Subdivision

open FirstHurewicz RealizationSimplex

theorem barycentricMap_surjective (n : ℕ) : Function.Surjective (barycentricMap.{u} n) := by
  classical
  intro t
  let p := Tuple.sort (fun i : Fin (n + 1) ↦ OrderDual.toDual (t i))
  let r : Fin (n + 1) → ℝ := fun j ↦ t (p j)
  have hr : Antitone r := Tuple.monotone_sort (fun i ↦ OrderDual.toDual (t i))
  have h0 : ∀ j, 0 ≤ r j := fun j ↦ stdSimplex.zero_le t (p j)
  have h1 : ∑ j, r j = 1 :=
    (Equiv.sum_comp p (fun i ↦ t i)).trans (stdSimplex.sum_eq_one t)
  refine ⟨characteristic (SimplexCategory.sd.{u}.obj ⦋n⦌) n (prefixSimplex p)
    (sortedWeights r hr h0 h1), ?_⟩
  apply Subtype.ext
  funext i
  exact (barycentricMap_prefixSimplex p r hr h0 h1 i).trans
    (congrArg (fun j ↦ t j) (p.apply_symm_apply i))

def barycentricHomeomorph (n : ℕ) :
    SSet.toTop.obj (SimplexCategory.sd.{u}.obj ⦋n⦌) ≃ₜ Simplex n :=
  (barycentricMap_isClosedEmbedding n).isEmbedding.toHomeomorphOfSurjective
    (barycentricMap_surjective n)

theorem barycentricHomeomorph_apply (n : ℕ)
    (z : SSet.toTop.obj (SimplexCategory.sd.{u}.obj ⦋n⦌)) :
    barycentricHomeomorph n z = barycentricMap n z := rfl

def stdSimplexSubdivisionHomeomorph (n : ℕ) :
    SSet.toTop.obj (SSet.sd.obj (SSet.stdSimplex.{u}.obj ⦋n⦌)) ≃ₜ Simplex n :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso (SSet.stdSimplex.sdIso.app ⦋n⦌))).trans
    (barycentricHomeomorph n)

end Wikipedia.HopfProblem.OrbitPair.Subdivision
