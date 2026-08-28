import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexQuotientFacesExtended
import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexQuotientFacesSkeleton

/-!
# Exact facet identities for the native simplex quotient

Every upper cube facet is the original simplex face with the matching
index. The final lower cube facet is the final simplex face. All other
lower facets land in the actual codimension-two simplex boundary.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry

open FirstHurewicz CubicalBoundary

theorem simplexQuotient_cubeFacet_one_apply (n : ℕ) (i : Fin (n + 1))
    (u : Fin n → I) :
    simplexQuotient (n + 1) (cubeFacet n i 1 u) =
      simplexFace n i.castSucc (simplexQuotient n u) := by
  apply Subtype.ext
  funext k
  change simplexQuotient (n + 1) (cubeFacet n i 1 u) k =
    simplexFace n i.castSucc (simplexQuotient n u) k
  refine Fin.succAboveCases i.castSucc ?_ (fun j => ?_) k
  · rw [simplexFace_apply_self]
    exact simplexQuotient_castSucc_eq_zero_of_one _ i (cubeFacet_apply_self n i 1 u)
  · rw [simplexFace_apply_succAbove]
    by_cases hji : j < i
    · rw [Fin.succAbove_of_castSucc_lt i.castSucc j
        (show j.castSucc < i.castSucc from hji)]
      simp only [simplexQuotient_apply, Fin.val_castSucc]
      rw [extendedMinimum_cubeFacet_one_le i u j.val (le_of_lt hji),
        extendedMinimum_cubeFacet_one_le i u (j.val + 1) (Nat.succ_le_of_lt hji)]
    · rw [Fin.succAbove_of_le_castSucc i.castSucc j
        (show i.castSucc ≤ j.castSucc from le_of_not_gt hji)]
      simp only [simplexQuotient_apply, Fin.val_succ]
      rw [extendedMinimum_cubeFacet_one_succ i u j.val (le_of_not_gt hji),
        extendedMinimum_cubeFacet_one_succ i u (j.val + 1)
          ((show i.val ≤ j.val from le_of_not_gt hji).trans (Nat.le_succ j.val))]

/-- Equality of the actual continuous facet compositions, with the original
cosimplicial simplex face map. -/
theorem simplexQuotient_cubeFacet_one (n : ℕ) (i : Fin (n + 1)) :
    (simplexQuotient (n + 1)).comp (cubeFacet n i 1) =
      (simplexFace n i.castSucc).comp (simplexQuotient n) :=
  ContinuousMap.ext (simplexQuotient_cubeFacet_one_apply n i)

theorem simplexQuotient_cubeFacet_last_zero_apply (n : ℕ) (u : Fin n → I) :
    simplexQuotient (n + 1) (cubeFacet n (Fin.last n) 0 u) =
      simplexFace n (Fin.last (n + 1)) (simplexQuotient n u) := by
  apply Subtype.ext
  funext k
  change simplexQuotient (n + 1) (cubeFacet n (Fin.last n) 0 u) k =
    simplexFace n (Fin.last (n + 1)) (simplexQuotient n u) k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · rw [simplexFace_apply_self]
    exact simplexQuotient_last_eq_zero_of_zero _ (Fin.last n)
      (cubeFacet_apply_self n (Fin.last n) 0 u)
  · rw [show j.castSucc = (Fin.last (n + 1)).succAbove j by simp,
      simplexFace_apply_succAbove]
    simp only [Fin.succAbove_last, simplexQuotient_apply, Fin.val_castSucc,
      extendedMinimum_cubeFacet_last_zero]

/-- The last lower cube facet is exactly the last original simplex face. -/
theorem simplexQuotient_cubeFacet_last_zero (n : ℕ) :
    (simplexQuotient (n + 1)).comp (cubeFacet n (Fin.last n) 0) =
      (simplexFace n (Fin.last (n + 1))).comp (simplexQuotient n) :=
  ContinuousMap.ext (simplexQuotient_cubeFacet_last_zero_apply n)

end Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry
