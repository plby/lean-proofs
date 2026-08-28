import Wikipedia.HopfProblem.FourthHurewiczChainClassHomology
import Wikipedia.HopfProblem.FourthHurewiczNormalizationFiveSimplex
import Wikipedia.HopfProblem.FourthHurewiczFiveSimplex

/-!
# The actual native fourth-homotopy assignment annihilates every five-boundary

The normalized five-simplex has the normalized original four-dimensional
faces. The genuine native signed six-face relation annihilates its
boundary, and linearity gives the result for every original singular
five-chain.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.FourthHurewicz

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]

/-- The six normalized original faces satisfy the genuine native homotopy relation. -/
theorem normalizedFourSimplex_boundary_relation (smp : SingularSimplex X 5) :
    ∑ i : Fin 6, (-1 : ℤ) ^ i.val •
      basedFourSimplexClass (normalizedFourSimplex x (smp.comp (simplexFace 4 i))) = 0 := by
  simpa only [normalizedFiveSimplex_face] using
    basedFiveSimplex_signed_relation (normalizedFiveSimplex x smp)

/-- Every original singular five-boundary has zero image in the actual native fourth homotopy. -/
theorem fourSimplexClassOperator_boundary (b : Chains X 5) :
    fourSimplexClassOperator x (((singularComplex X).d 5 4).hom b) = 0 := by
  have h : (fourSimplexClassOperator x).comp ((singularComplex X).d 5 4).hom = 0 := by
    apply chainMap_ext X 5
    intro smp
    simp only [LinearMap.comp_apply, boundary_simplex, map_sum, map_zsmul,
      fourSimplexClassOperator_simplex, LinearMap.zero_apply]
    exact normalizedFourSimplex_boundary_relation x smp
  exact LinearMap.congr_fun h b

end Wikipedia.HopfProblem.FourthHurewicz
