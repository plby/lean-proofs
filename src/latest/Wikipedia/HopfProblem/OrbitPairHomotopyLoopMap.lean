import Wikipedia.NoExoticSixSphere.PathFamilyCurrying
import Wikipedia.NoExoticSixSphere.LoopSpaceDimensionShift
import Wikipedia.NoExoticSixSphere.InducedHomotopyMap

/-!
# The actual induced map of based loop spaces

Composition with a continuous map is continuous for the native path topology.
The native cube-currying dimension shift commutes exactly with this map.
-/

noncomputable section

namespace Wikipedia.HopfProblem.OrbitPair.HomotopyFiber

open NoExoticSixSphere

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def loopMap (f : C(X, Y)) (x : X) : C(Path x x, Path (f x) (f x)) where
  toFun p := p.map f.continuous
  continuous_toFun := Path.continuous_uncurry_iff.mp (f.continuous.comp continuous_eval)

theorem loopMap_base (f : C(X, Y)) (x : X) :
    loopMap f x (Path.refl x) = Path.refl (f x) := rfl

theorem loopMap_apply (f : C(X, Y)) (x : X) (p : Path x x) (t : unitInterval) :
    loopMap f x p t = f (p t) := rfl

theorem uncurry_loopMap (d : ℕ) (f : C(X, Y)) (x : X)
    (p : GenLoop (Fin d) (Path x x) (Path.refl x)) :
    GeneralizedLoopCurrying.uncurry
      (HigherHomotopy.genLoopMap (loopMap f x) (loopMap_base f x) p) =
        HigherHomotopy.genLoopMap f rfl (GeneralizedLoopCurrying.uncurry p) := rfl

theorem homotopyEquiv_loopMap (d : ℕ) (f : C(X, Y)) (x : X)
    (p : HomotopyGroup (Fin d) (Path x x) (Path.refl x)) :
    GeneralizedLoopCurrying.homotopyEquiv d (f x)
      (HigherHomotopy.map (loopMap f x) (loopMap_base f x) p) =
        HigherHomotopy.map f rfl (GeneralizedLoopCurrying.homotopyEquiv d x p) := by
  refine Quotient.inductionOn p ?_
  intro p
  rfl

end Wikipedia.HopfProblem.OrbitPair.HomotopyFiber
