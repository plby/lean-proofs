import Wikipedia.HopfProblem.FourthHurewiczFourSimplexSimplexSum
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChains
import Wikipedia.HopfProblem.FourthHurewiczMap

/-!
# The exact fourth Hurewicz image of a based four-simplex

The original recursively constructed native cube chain is its signed
twenty-four-simplex chain.  The explicit quotient recovers the original
simplex on the identity cell and is constant on all other cells.  Thus
the chain itself is the original simplex minus the constant four-simplex.
-/

noncomputable section

namespace Wikipedia.HopfProblem.FourthHurewicz

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] {x : X}

/-- Exact equality in the original unnormalized singular four-chain group. -/
theorem cubeChain_basedFourSimplexLoop (τ : BasedFourSimplex x) :
    cubeChain (basedFourSimplexLoop τ) = basedFourSimplexChain τ := by
  rw [CubeSubdivision.cubeChain_eq_sum_simplices, basedFourSimplex_simplexChain_sum]

/-- The actual native cube cycle is the actual corrected simplex cycle. -/
theorem cubeCycle_basedFourSimplexLoop (τ : BasedFourSimplex x) :
    cubeCycle (basedFourSimplexLoop τ) = basedFourSimplexCycle τ := by
  apply Subtype.ext
  exact cubeChain_basedFourSimplexLoop τ

/-- The genuine fourth Hurewicz homomorphism sends the native simplex class
to the actual homology class of the original simplex minus the constant. -/
theorem hurewicz_basedFourSimplexClass (τ : BasedFourSimplex x) :
    hurewiczMap x (basedFourSimplexClass τ) =
      ModuleHomology.cycleClass (singularComplex X) 4 (basedFourSimplexCycle τ) := by
  change ModuleHomology.cycleClass (singularComplex X) 4
    (cubeCycle (basedFourSimplexLoop τ)) = _
  rw [cubeCycle_basedFourSimplexLoop]

end Wikipedia.HopfProblem.FourthHurewicz
