import Wikipedia.HopfProblem.OrbitPairHomotopyFiberExactSequence
import Wikipedia.NoExoticSixSphere.ContractibleNativeHomotopy

/-!
# The original loop inclusion for a contractible fiber source

The checked native fiber sequence makes its boundary map bijective when
the source is contractible. Canceling the original cube-currying
equivalence proves bijectivity of the literal loop inclusion, at the
specified source point and in every positive degree.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.HomotopyFiberContractibleSource

open HomotopyFiber

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [ContractibleSpace X]
  (f : C(X, Y)) (x : X)

theorem boundary_bijective (d : ℕ) [NeZero d] :
    Function.Bijective (boundaryHom d f x) := by
  let : Subsingleton (π_ d X x) := ContractibleNativeHomotopy.subsingleton d x
  let : Subsingleton (π_ (d + 1) X x) := ContractibleNativeHomotopy.subsingleton (d + 1) x
  constructor
  · apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [← source_range_eq_boundary_ker d f x]
    apply MonoidHom.range_eq_bot_iff.mpr
    ext c
    exact (congrArg (HigherHomotopy.mapMonoidHom (N := Fin (d + 1)) f (y := x) rfl)
      (Subsingleton.elim c 1)).trans (map_one _)
  · intro c
    apply (projection_eq_const_iff_exists_boundary_class d f x c).mp
    exact @Subsingleton.elim (π_ d X x) inferInstance _ _

theorem loopInclusion_map_bijective (d : ℕ) [NeZero d] :
    Function.Bijective (HigherHomotopy.map (N := Fin d) (loopInclusion f x)
      (loopInclusion_base f x)) := by
  have hb : Function.Bijective (HigherHomotopy.map (N := Fin d) (loopInclusion f x)
      (loopInclusion_base f x) ∘ (GeneralizedLoopCurrying.homotopyEquiv d (f x)).symm) :=
    boundary_bijective f x d
  exact (Function.Bijective.of_comp_iff _
    (GeneralizedLoopCurrying.homotopyEquiv d (f x)).symm.bijective).mp hb

end NoExoticSixSphere.HomotopyFiberContractibleSource
