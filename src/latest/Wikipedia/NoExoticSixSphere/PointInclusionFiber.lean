import Wikipedia.NoExoticSixSphere.RelativeFiberHomology
import Wikipedia.NoExoticSixSphere.NativeHomotopyBasepointVanishing
import Wikipedia.HopfProblem.OrbitPairHigherHomotopyHomeomorph

/-!
# The actual fiber of a point inclusion is the native based loop space

The only source coordinate is the point itself. Keeping the original
compact-open path coordinate gives a homeomorphism, with the native
constant loop as the image of the actual fiber basepoint.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem SingularMayerVietoris OrbitPair

namespace NoExoticSixSphere.PointInclusionFiber

open RelativeFiberHomology

variable {X : Type} [TopologicalSpace X] (x : X) (a : ({x} : Set X))

def loopsHomeomorph : Fiber ({x} : Set X) a ≃ₜ Path a.val a.val where
  toFun p := {
    toContinuousMap := p.val.2
    source' := p.property.1.trans (congrArg Subtype.val (Subsingleton.elim p.val.1 a))
    target' := p.property.2 }
  invFun q := ⟨(a, q.toContinuousMap), q.source, q.target⟩
  left_inv p := Subtype.ext (Prod.ext (Subsingleton.elim _ _) rfl)
  right_inv q := Path.ext rfl
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact continuous_eval.comp
      ((continuous_snd.comp (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_const.prodMk
      (show Continuous (fun q : Path a.val a.val ↦ q.toContinuousMap) from continuous_induced_dom)

theorem loopsHomeomorph_basepoint :
    loopsHomeomorph x a (HomotopyFiber.basepoint (subtypeInclusion ({x} : Set X)) a) =
      Path.refl a.val := rfl

theorem pi_subsingleton [SimplyConnectedSpace X] (n : ℕ) (hn : 0 < n)
    [Subsingleton (π_ (n + 1) X a.val)] (p : Fiber ({x} : Set X) a) :
    Subsingleton (π_ n (Fiber ({x} : Set X) a) p) := by
  let := NativeHomotopyBasepointVanishing.loops_subsingleton n hn a.val
    (loopsHomeomorph x a p)
  let e := HigherHomotopyCoordinates.homeomorphEquiv (Fin n) (loopsHomeomorph x a) p
  exact e.injective.subsingleton

end NoExoticSixSphere.PointInclusionFiber
