import Wikipedia.HopfProblem.FifthHurewiczChainClasses
import Wikipedia.HopfProblem.FifthHurewiczNormalizationSixSimplex

/-!
# The native fifth-homotopy assignment annihilates original six-boundaries

The normalized six-simplex has the normalized original five-dimensional
faces. The genuine native signed seven-face relation annihilates its
boundary, and linearity gives the result for every original singular
six-chain.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.FifthHurewicz

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)]

/-- The seven normalized original faces satisfy the genuine native homotopy relation. -/
theorem normalizedFiveSimplex_boundary_relation (smp : SingularSimplex X 6) :
    ∑ i : Fin 7, (-1 : ℤ) ^ i.val •
      basedFiveSimplexClass (normalizedFiveSimplex x (smp.comp (simplexFace 5 i))) = 0 := by
  simpa only [normalizedSixSimplex_face] using
    basedSixSimplex_signed_relation (normalizedSixSimplex x smp)

/-- Every original singular six-boundary has zero image in actual native fifth homotopy. -/
theorem fiveSimplexClassOperator_boundary (b : Chains X 6) :
    fiveSimplexClassOperator x (((singularComplex X).d 6 5).hom b) = 0 := by
  have h : (fiveSimplexClassOperator x).comp ((singularComplex X).d 6 5).hom = 0 := by
    apply chainMap_ext X 6
    intro smp
    simp only [LinearMap.comp_apply, boundary_simplex, map_sum, map_zsmul,
      fiveSimplexClassOperator_simplex, LinearMap.zero_apply]
    exact normalizedFiveSimplex_boundary_relation x smp
  exact LinearMap.congr_fun h b

end Wikipedia.HopfProblem.FifthHurewicz
