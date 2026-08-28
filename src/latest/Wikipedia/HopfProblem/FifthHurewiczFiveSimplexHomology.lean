import Wikipedia.HopfProblem.FifthHurewiczFiveSimplexCycles
import Wikipedia.HopfProblem.FifthHurewiczCubeSubdivisionChains
import Wikipedia.HopfProblem.FifthHurewiczMap

/-!
# The exact fifth Hurewicz image of a based five-simplex

The genuine recursively constructed native five-cube chain expands into
its 120 oriented permutation simplices.  The generic quotient calculation
then identifies it with the original simplex minus the constant simplex.
-/

noncomputable section

namespace Wikipedia.HopfProblem.FifthHurewicz

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] {x : X}

/-- Exact equality in the original singular five-chain group. -/
theorem cubeChain_basedFiveSimplexLoop (τ : BasedFiveSimplex x) :
    cubeChain (basedFiveSimplexLoop τ) = basedFiveSimplexChain τ := by
  rw [CubeSubdivision.cubeChain_eq_sum_simplices, basedFiveSimplex_simplexChain_sum]

/-- The actual native cube cycle is the actual corrected simplex cycle. -/
theorem cubeCycle_basedFiveSimplexLoop (τ : BasedFiveSimplex x) :
    cubeCycle (basedFiveSimplexLoop τ) = basedFiveSimplexCycle τ := by
  apply Subtype.ext
  exact cubeChain_basedFiveSimplexLoop τ

/-- The genuine fifth Hurewicz homomorphism sends the native simplex class
to the homology class of the original simplex minus the actual constant. -/
theorem hurewicz_basedFiveSimplexClass (τ : BasedFiveSimplex x) :
    hurewiczMap x (basedFiveSimplexClass τ) =
      ModuleHomology.cycleClass (singularComplex X) 5 (basedFiveSimplexCycle τ) := by
  change ModuleHomology.cycleClass (singularComplex X) 5
    (cubeCycle (basedFiveSimplexLoop τ)) = _
  rw [cubeCycle_basedFiveSimplexLoop]

end Wikipedia.HopfProblem.FifthHurewicz
