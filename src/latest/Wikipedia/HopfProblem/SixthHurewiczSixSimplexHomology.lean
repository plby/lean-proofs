import Wikipedia.HopfProblem.SixthHurewiczSixSimplexCycles
import Wikipedia.HopfProblem.SixthHurewiczCubeSubdivisionChains
import Wikipedia.HopfProblem.SixthHurewiczMap

/-!
# The exact sixth Hurewicz image of a based six-simplex

The original recursive six-cube chain is its signed 720-simplex chain.
The existing quotient calculation identifies this actual chain with the
original singular six-simplex minus the constant six-simplex.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SixthHurewicz

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] {x : X}

/-- Exact equality in the original singular six-chain group. -/
theorem cubeChain_basedSixSimplexLoop (τ : BasedSixSimplex x) :
    cubeChain (basedSixSimplexLoop τ) = basedSixSimplexChain τ := by
  rw [CubeSubdivision.cubeChain_eq_sum_simplices, basedSixSimplex_simplexChain_sum]

/-- The actual native cube cycle is the actual corrected simplex cycle. -/
theorem cubeCycle_basedSixSimplexLoop (τ : BasedSixSimplex x) :
    cubeCycle (basedSixSimplexLoop τ) = basedSixSimplexCycle τ := by
  apply Subtype.ext
  exact cubeChain_basedSixSimplexLoop τ

/-- The genuine sixth Hurewicz homomorphism sends the native simplex class
to the homology class of the original simplex minus the actual constant. -/
theorem hurewicz_basedSixSimplexClass (τ : BasedSixSimplex x) :
    hurewiczMap x (basedSixSimplexClass τ) =
      ModuleHomology.cycleClass (singularComplex X) 6 (basedSixSimplexCycle τ) := by
  change ModuleHomology.cycleClass (singularComplex X) 6
    (cubeCycle (basedSixSimplexLoop τ)) = _
  rw [cubeCycle_basedSixSimplexLoop]

end Wikipedia.HopfProblem.SixthHurewicz
