import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.InverseCubeBasic
import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.InverseCubeChains
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionRecovery

/-!
# Native seventh-homotopy recovery from the actual cubical chain

The original loop is homotopic, relative to the entire cube boundary, to
the coherently normalized cube. Genuine native subdivision recovers its
class from its actual permutation simplices. Those simplices are exactly
the normalized restrictions occurring in the original cubical chain.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz

open Wikipedia.HopfProblem

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] [Subsingleton (π_ 6 X x)]

/-- The actual chain assignment recovers the class of every original native seven-loop. -/
theorem sevenSimplexClassOperator_cubeChain (p : GenLoop (Fin 7) X x) :
    sevenSimplexClassOperator x (cubeChain p) = Additive.ofMul (⟦p⟧ : π_ 7 X x) := by
  rw [sevenSimplexClassOperator_cubeChain_sum]
  calc
    _ = Additive.ofMul (⟦normalizedCube x p⟧ : π_ 7 X x) := by
      simpa only [normalizedCube_simplex, basedSevenSimplexClass] using
        (HigherHurewicz.NativeSubdivision.nativeCubeSubdivision_class (normalizedCube x p)
          (normalizedCube_internalBased x p)).symm
    _ = _ := congrArg Additive.ofMul
      (Quotient.sound (show GenLoop.Homotopic (normalizedCube x p) p from
        ⟨(normalizationCubeHomotopy x p).symm⟩))

end Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz
