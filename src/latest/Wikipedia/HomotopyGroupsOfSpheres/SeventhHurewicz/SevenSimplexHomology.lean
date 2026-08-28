import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.SevenSimplexCycles
import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.CubeSubdivisionChains
import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.Map

/-!
# The exact seventh Hurewicz image of a based seven-simplex

The original recursive seven-cube chain is its signed 5040-simplex chain.
The existing quotient calculation identifies this actual chain with the
original singular seven-simplex minus the constant seven-simplex.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz

open Wikipedia.HopfProblem

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] {x : X}

/-- Exact equality in the original singular seven-chain group. -/
theorem cubeChain_basedSevenSimplexLoop (τ : BasedSevenSimplex x) :
    cubeChain (basedSevenSimplexLoop τ) = basedSevenSimplexChain τ := by
  rw [CubeSubdivision.cubeChain_eq_sum_simplices, basedSevenSimplex_simplexChain_sum]

/-- The actual native cube cycle is the actual corrected simplex cycle. -/
theorem cubeCycle_basedSevenSimplexLoop (τ : BasedSevenSimplex x) :
    cubeCycle (basedSevenSimplexLoop τ) = basedSevenSimplexCycle τ := by
  apply Subtype.ext
  exact cubeChain_basedSevenSimplexLoop τ

/-- The genuine seventh Hurewicz homomorphism sends the native simplex class
to the homology class of the original simplex minus the actual constant. -/
theorem hurewicz_basedSevenSimplexClass (τ : BasedSevenSimplex x) :
    hurewiczMap x (basedSevenSimplexClass τ) =
      ModuleHomology.cycleClass (singularComplex X) 7 (basedSevenSimplexCycle τ) := by
  change ModuleHomology.cycleClass (singularComplex X) 7
    (cubeCycle (basedSevenSimplexLoop τ)) = _
  rw [cubeCycle_basedSevenSimplexLoop]

end Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz
