import Wikipedia.HopfProblem.ThirdHurewiczThreeSimplexTetrahedronSum
import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionChains
import Wikipedia.HopfProblem.ThirdHurewiczMap

/-!
# The exact third Hurewicz image of a based three-simplex

The original native cube chain is exactly the signed six-tetrahedron chain.
The PL simplex quotient sends its principal tetrahedron identically onto
the original simplex and the other five into its based boundary. Hence the
actual chain, not only its homology class, is `simplex - constant`.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] {x : X}

/-- Exact equality in the original unnormalized singular three-chain group. -/
theorem cubeChain_basedThreeSimplexLoop (τ : BasedThreeSimplex x) :
    cubeChain (basedThreeSimplexLoop τ) = basedThreeSimplexChain τ := by
  rw [CubeSubdivision.cubeChain_eq_sum_tetrahedra, basedThreeSimplex_tetrahedronChain_sum]

/-- The native cube cycle is the original corrected singular-simplex cycle. -/
theorem cubeCycle_basedThreeSimplexLoop (τ : BasedThreeSimplex x) :
    cubeCycle (basedThreeSimplexLoop τ) = basedThreeSimplexCycle τ := by
  apply Subtype.ext
  exact cubeChain_basedThreeSimplexLoop τ

/-- The actual third Hurewicz homomorphism sends the native based-simplex
class to the actual cycle class of the original simplex minus the constant. -/
theorem hurewicz_basedThreeSimplexClass (τ : BasedThreeSimplex x) :
    hurewiczMap x (basedThreeSimplexClass τ) =
      ModuleHomology.cycleClass (singularComplex X) 3 (basedThreeSimplexCycle τ) := by
  change ModuleHomology.cycleClass (singularComplex X) 3
    (cubeCycle (basedThreeSimplexLoop τ)) = _
  rw [cubeCycle_basedThreeSimplexLoop]

end Wikipedia.HopfProblem.ThirdHurewicz
