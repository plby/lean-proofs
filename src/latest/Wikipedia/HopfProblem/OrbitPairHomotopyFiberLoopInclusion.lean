import Wikipedia.HopfProblem.OrbitPairHomotopyFiberLiftedFamily
import Wikipedia.HopfProblem.OrbitPairHomotopyFiberKernel

/-!
# The based loop space inside the actual homotopy fibre

The inclusion keeps the source point fixed and uses the loop as its fibre
path. Conversely, a continuous fibre family with constant projection gives
a continuous native based-loop family, with exact reconstruction.
-/

noncomputable section

namespace Wikipedia.HopfProblem.OrbitPair.HomotopyFiber

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def loopInclusion (f : C(X, Y)) (x : X) : C(Path (f x) (f x), Space f (f x)) where
  toFun p := ⟨(x, p.toContinuousMap), p.source, p.target⟩
  continuous_toFun := (continuous_const.prodMk
    (show Continuous (fun p : Path (f x) (f x) ↦ p.toContinuousMap) from
      continuous_induced_dom)).subtype_mk _

theorem loopInclusion_base (f : C(X, Y)) (x : X) :
    loopInclusion f x (Path.refl (f x)) = basepoint f x := rfl

theorem projection_loopInclusion (f : C(X, Y)) (x : X) :
    (projection f (f x)).comp (loopInclusion f x) = ContinuousMap.const _ x := rfl

theorem loopInclusion_injective (f : C(X, Y)) (x : X) :
    Function.Injective (loopInclusion f x) := by
  intro p q h
  apply Path.ext
  funext t
  exact congrArg (fun z : Space f (f x) ↦ z.val.2 t) h

def loopFamily (f : C(X, Y)) (x : X) (p : C(Z, Space f (f x)))
    (hp : ∀ z, projection f (f x) (p z) = x) : C(Z, Path (f x) (f x)) where
  toFun z := {
    toContinuousMap := (p z).val.2
    source' := (p z).property.1.trans (congrArg f (hp z))
    target' := (p z).property.2 }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact continuous_eval.comp
      ((continuous_snd.comp (continuous_subtype_val.comp
        (p.continuous.comp continuous_fst))).prodMk continuous_snd)

theorem loopInclusion_loopFamily (f : C(X, Y)) (x : X) (p : C(Z, Space f (f x)))
    (hp : ∀ z, projection f (f x) (p z) = x) :
    (loopInclusion f x).comp (loopFamily f x p hp) = p := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  exact Prod.ext (hp z).symm rfl

end Wikipedia.HopfProblem.OrbitPair.HomotopyFiber
