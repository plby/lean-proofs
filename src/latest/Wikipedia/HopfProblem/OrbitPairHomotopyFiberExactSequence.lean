import Wikipedia.HopfProblem.OrbitPairHomotopyFiberConnectingKernel
import Wikipedia.HopfProblem.OrbitPairHomotopyFiberLoopKernel

/-!
# Three consecutive exact terms of the native homotopy-fibre sequence

The connecting map is the actual loop inclusion composed with the inverse
native cube-currying dimension shift. Exactness is proved at the target group,
the fibre group, and the source group. All spaces and homotopy groups retain
their original topologies and definitions; no long exact sequence is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.OrbitPair.HomotopyFiber

open NoExoticSixSphere

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def boundaryMap (d : ℕ) (f : C(X, Y)) (x : X) :
    HomotopyGroup (Fin (d + 1)) Y (f x) →
      HomotopyGroup (Fin d) (Space f (f x)) (basepoint f x) :=
  HigherHomotopy.map (loopInclusion f x) (loopInclusion_base f x) ∘
    (GeneralizedLoopCurrying.homotopyEquiv d (f x)).symm

def boundaryHom (d : ℕ) [NeZero d] (f : C(X, Y)) (x : X) :
    HomotopyGroup (Fin (d + 1)) Y (f x) →*
      HomotopyGroup (Fin d) (Space f (f x)) (basepoint f x) :=
  (HigherHomotopy.mapMonoidHom (loopInclusion f x) (loopInclusion_base f x)).comp
    (GeneralizedLoopCurrying.homotopyMulEquiv d (f x)).symm.toMonoidHom

theorem boundaryHom_apply (d : ℕ) [NeZero d] (f : C(X, Y)) (x : X)
    (c : HomotopyGroup (Fin (d + 1)) Y (f x)) :
    boundaryHom d f x c = boundaryMap d f x c := rfl

theorem boundary_eq_const_iff_exists_source_class (d : ℕ) (f : C(X, Y)) (x : X)
    (c : HomotopyGroup (Fin (d + 1)) Y (f x)) :
    boundaryMap d f x c =
      (Quotient.mk' GenLoop.const : HomotopyGroup (Fin d) (Space f (f x)) (basepoint f x)) ↔
        ∃ q : HomotopyGroup (Fin (d + 1)) X x, HigherHomotopy.map f rfl q = c := by
  let eX := GeneralizedLoopCurrying.homotopyEquiv d x
  let eY := GeneralizedLoopCurrying.homotopyEquiv d (f x)
  change HigherHomotopy.map (loopInclusion f x) (loopInclusion_base f x) (eY.symm c) = _ ↔ _
  rw [loopInclusion_eq_const_iff_exists_sourceLoop_class]
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨eX q, (homotopyEquiv_loopMap d f x q).symm.trans
      ((congrArg eY hq).trans (eY.apply_symm_apply c))⟩
  · rintro ⟨q, rfl⟩
    refine ⟨eX.symm q, ?_⟩
    apply eY.injective
    change GeneralizedLoopCurrying.homotopyEquiv d (f x)
      (HigherHomotopy.map (loopMap f x) (loopMap_base f x) (eX.symm q)) = _
    rw [homotopyEquiv_loopMap, eX.apply_symm_apply, eY.apply_symm_apply]

theorem projection_eq_const_iff_exists_boundary_class (d : ℕ) (f : C(X, Y)) (x : X)
    (c : HomotopyGroup (Fin d) (Space f (f x)) (basepoint f x)) :
    HigherHomotopy.map (projection f (f x)) rfl c =
      (Quotient.mk' GenLoop.const : HomotopyGroup (Fin d) X x) ↔
        ∃ q : HomotopyGroup (Fin (d + 1)) Y (f x), boundaryMap d f x q = c := by
  let e := GeneralizedLoopCurrying.homotopyEquiv d (f x)
  rw [projection_eq_const_iff_exists_loop_class]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨e q, ?_⟩
    change HigherHomotopy.map (loopInclusion f x) (loopInclusion_base f x) (e.symm (e q)) = c
    rw [e.symm_apply_apply]
    exact hq
  · rintro ⟨q, hq⟩
    exact ⟨e.symm q, hq⟩

theorem source_range_eq_boundary_ker (d : ℕ) [NeZero d] (f : C(X, Y)) (x : X) :
    (HigherHomotopy.mapMonoidHom (N := Fin (d + 1)) f (y := x) rfl).range =
      (boundaryHom d f x).ker := by
  ext c
  exact (boundary_eq_const_iff_exists_source_class d f x c).symm

theorem boundary_range_eq_projection_ker (d : ℕ) [NeZero d] (f : C(X, Y)) (x : X) :
    (boundaryHom d f x).range =
      (HigherHomotopy.mapMonoidHom (N := Fin d) (projection f (f x)) rfl).ker := by
  ext c
  exact (projection_eq_const_iff_exists_boundary_class d f x c).symm

end Wikipedia.HopfProblem.OrbitPair.HomotopyFiber
