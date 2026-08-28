import Wikipedia.HopfProblem.SixthHurewiczChainClasses
import Wikipedia.HopfProblem.SixthHurewiczNormalizationSevenSimplex

/-!
# The native sixth-homotopy assignment annihilates original seven-boundaries

The normalized seven-simplex has the normalized original six-dimensional
faces. The genuine native signed eight-face relation annihilates its
boundary, and linearity gives the result for every original singular
seven-chain.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.SixthHurewicz

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]

/-- The eight normalized original faces satisfy the genuine native homotopy relation. -/
theorem normalizedSixSimplex_boundary_relation (smp : SingularSimplex X 7) :
    ∑ i : Fin 8, (-1 : ℤ) ^ i.val •
      basedSixSimplexClass (normalizedSixSimplex x (smp.comp (simplexFace 6 i))) = 0 := by
  simpa only [normalizedSevenSimplex_face] using
    basedSevenSimplex_signed_relation (normalizedSevenSimplex x smp)

/-- Every original singular seven-boundary has zero image in actual native sixth homotopy. -/
theorem sixSimplexClassOperator_boundary (b : Chains X 7) :
    sixSimplexClassOperator x (((singularComplex X).d 7 6).hom b) = 0 := by
  have h : (sixSimplexClassOperator x).comp ((singularComplex X).d 7 6).hom = 0 := by
    apply chainMap_ext X 7
    intro smp
    simp only [LinearMap.comp_apply, boundary_simplex, map_sum, map_zsmul,
      sixSimplexClassOperator_simplex, LinearMap.zero_apply]
    exact normalizedSixSimplex_boundary_relation x smp
  exact LinearMap.congr_fun h b

end Wikipedia.HopfProblem.SixthHurewicz
