import Wikipedia.HopfProblem.SixthHurewiczNaturality
import Wikipedia.NoExoticSixSphere.BasedHomotopyNativeMap

/-!
# Sixth Hurewicz naturality for the original based native maps

The basepoint equality is retained explicitly. On actual cube
representatives the statement is the already proved singular-chain
naturality identity, with no connectivity assumptions on either space.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.SixthHurewiczNative

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem natural (f : C(X, Y)) (x : X) (y : Y) (h : f x = y) (c : π_ 6 X x) :
    singularHomologyMap f 6 (SixthHurewicz.hurewiczFunction x c) =
      SixthHurewicz.hurewiczFunction y (HigherHomotopy.map (N := Fin 6) f h c) := by
  cases h
  refine Quotient.inductionOn c fun p ↦ ?_
  exact SixthHurewicz.cubeHomologyClass_natural f x p

end NoExoticSixSphere.SixthHurewiczNative
