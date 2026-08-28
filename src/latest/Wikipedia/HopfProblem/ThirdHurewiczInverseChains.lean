import Wikipedia.HopfProblem.ThirdHurewiczChainClassHomology
import Wikipedia.HopfProblem.ThirdHurewiczNormalizationFourSimplex
import Wikipedia.HopfProblem.ThirdHurewiczFourSimplex

/-!
# The constructed native third-homotopy assignment kills every boundary

The genuine normalized four-simplex has exactly the normalized original
three-dimensional faces. Its native signed five-face relation therefore
annihilates the original singular four-boundary. Linearization proves the
statement for every actual four-chain, without a comparison hypothesis.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)]

/-- The five normalized original faces satisfy the actual native homotopy relation. -/
theorem normalizedThreeSimplex_boundary_relation (smp : SingularSimplex X 4) :
    ∑ i : Fin 5, (-1 : ℤ) ^ i.val •
      basedThreeSimplexClass (normalizedThreeSimplex x (smp.comp (simplexFace 3 i))) = 0 := by
  simpa only [normalizedFourSimplex_face] using
    basedFourSimplex_signed_relation (normalizedFourSimplex x smp)

/-- Every genuine singular four-boundary has zero image in the original native `π₃`. -/
theorem threeSimplexClassOperator_boundary (b : Chains X 4) :
    threeSimplexClassOperator x (((singularComplex X).d 4 3).hom b) = 0 := by
  have h : (threeSimplexClassOperator x).comp ((singularComplex X).d 4 3).hom = 0 := by
    apply chainMap_ext X 4
    intro smp
    simp only [LinearMap.comp_apply, boundary_simplex, map_sum, map_zsmul,
      threeSimplexClassOperator_simplex, LinearMap.zero_apply]
    exact normalizedThreeSimplex_boundary_relation x smp
  exact LinearMap.congr_fun h b

end Wikipedia.HopfProblem.ThirdHurewicz
