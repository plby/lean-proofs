import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedFaceCover
import Wikipedia.HopfProblem.SingularMayerVietorisSmallChainsInclusions
import Wikipedia.HopfProblem.SingularMayerVietorisQuasiIsoCriteria

/-!
# The original signed simplex-boundary cycle

The chain lives in the actual boundary subspace, not merely in the
ambient simplex. Its image under the injective inclusion chain map is
the boundary of the identity simplex. The original differential squares
to zero, proving the cycle condition in the boundary subspace itself.
-/

noncomputable section

open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris
open SecondHurewicz.SimplyConnected

namespace NoExoticSixSphere.SimplexBoundaryChains

def chain (n : ℕ) : Chains (SimplexBoundary (n + 1)) n :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
    simplexChain (SimplexBoundary (n + 1)) n (simplexFaceBoundary n i)

theorem inclusion_chain (n : ℕ) :
    inducedChain (subtypeInclusion (simplexBoundary (n + 1))) n (chain n) =
      ((singularComplex (Simplex (n + 1))).d (n + 1) n).hom
        (simplexChain (Simplex (n + 1)) (n + 1) (ContinuousMap.id _)) := by
  simp only [chain, map_sum, map_zsmul, inducedChain_simplex, boundary_simplex,
    ContinuousMap.id_comp]
  rfl

theorem boundary_chain (n : ℕ) :
    ((singularComplex (SimplexBoundary (n + 2))).d (n + 1) n).hom (chain (n + 1)) = 0 := by
  apply subtypeInclusion_chain_injective (simplexBoundary (n + 2)) n
  rw [inducedChain_boundary, inclusion_chain, map_zero]
  exact ModuleHomology.cycle_condition (singularComplex (Simplex (n + 2))) (n + 1)
    (ModuleHomology.boundaryCycle (singularComplex (Simplex (n + 2))) (n + 1)
      (simplexChain (Simplex (n + 2)) (n + 2) (ContinuousMap.id _)))

def cycle (n : ℕ) : ModuleHomology.Cycle (singularComplex (SimplexBoundary (n + 2))) (n + 1) :=
  ModuleHomology.mkCycle _ (n + 1) (chain (n + 1)) (boundary_chain n)

theorem cycle_val (n : ℕ) : (cycle n).val = chain (n + 1) := rfl

end NoExoticSixSphere.SimplexBoundaryChains
