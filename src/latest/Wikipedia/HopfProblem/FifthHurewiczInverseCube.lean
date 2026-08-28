import Wikipedia.HopfProblem.FifthHurewiczInverseCubeBasic
import Wikipedia.HopfProblem.FifthHurewiczInverseCubeChains
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionRecovery

/-!
# Native fifth-homotopy recovery from the actual cubical chain

The original loop is homotopic, relative to the entire cube boundary, to
the coherently normalized cube. Genuine native subdivision recovers its
class from its actual permutation simplices. Those simplices are exactly
the normalized restrictions occurring in the original cubical chain.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.FifthHurewicz

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)]

/-- The actual chain assignment recovers the class of every original native five-loop. -/
theorem fiveSimplexClassOperator_cubeChain (p : GenLoop (Fin 5) X x) :
    fiveSimplexClassOperator x (cubeChain p) = Additive.ofMul (⟦p⟧ : π_ 5 X x) := by
  rw [fiveSimplexClassOperator_cubeChain_sum]
  calc
    _ = Additive.ofMul (⟦normalizedCube x p⟧ : π_ 5 X x) := by
      simpa only [normalizedCube_simplex, basedFiveSimplexClass] using
        (HigherHurewicz.NativeSubdivision.nativeCubeSubdivision_class (normalizedCube x p)
          (normalizedCube_internalBased x p)).symm
    _ = _ := congrArg Additive.ofMul
      (Quotient.sound (show GenLoop.Homotopic (normalizedCube x p) p from
        ⟨(normalizationCubeHomotopy x p).symm⟩))

end Wikipedia.HopfProblem.FifthHurewicz
