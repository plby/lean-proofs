import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.ChainClasses
import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.NormalizationEightSimplex

/-!
# The native seventh-homotopy assignment annihilates original eight-boundaries

The normalized eight-simplex has the normalized original seven-dimensional
faces. The genuine native signed nine-face relation annihilates its
boundary, and linearity gives the result for every original singular
eight-chain.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz

open Wikipedia.HopfProblem

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] [Subsingleton (π_ 6 X x)]

/-- The nine normalized original faces satisfy the genuine native homotopy relation. -/
theorem normalizedSevenSimplex_boundary_relation (smp : SingularSimplex X 8) :
    ∑ i : Fin 9, (-1 : ℤ) ^ i.val •
      basedSevenSimplexClass (normalizedSevenSimplex x (smp.comp (simplexFace 7 i))) = 0 := by
  simpa only [normalizedEightSimplex_face] using
    basedEightSimplex_signed_relation (normalizedEightSimplex x smp)

/-- Every original singular eight-boundary has zero image in actual native seventh homotopy. -/
theorem sevenSimplexClassOperator_boundary (b : Chains X 8) :
    sevenSimplexClassOperator x (((singularComplex X).d 8 7).hom b) = 0 := by
  have h : (sevenSimplexClassOperator x).comp ((singularComplex X).d 8 7).hom = 0 := by
    apply chainMap_ext X 8
    intro smp
    simp only [LinearMap.comp_apply, boundary_simplex, map_sum, map_zsmul,
      sevenSimplexClassOperator_simplex, LinearMap.zero_apply]
    exact normalizedSevenSimplex_boundary_relation x smp
  exact LinearMap.congr_fun h b

end Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz
