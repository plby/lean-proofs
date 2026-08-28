import Wikipedia.NoExoticSixSphere.LoopSpaceDimensionShift
import Wikipedia.NoExoticSixSphere.BasedHomotopyNativeMap

/-!
# Actual path reversal acts by inversion on native loop-space homotopy

Uncurrying makes path reversal literal reversal in the first cube
coordinate. The original native inverse law and currying equivalence
give the result in every positive parameter dimension.
-/

noncomputable section

open scoped Topology unitInterval

namespace NoExoticSixSphere.GeneralizedLoopCurrying

variable {X : Type*} [TopologicalSpace X] (x : X)

def reverseMap : C(Path x x, Path x x) := ⟨Path.symm, Path.continuous_symm⟩

theorem reverseMap_refl : reverseMap x (Path.refl x) = Path.refl x := by
  apply Path.ext
  rfl

variable {x} {d : ℕ}

theorem uncurry_reverse (p : GenLoop (Fin d) (Path x x) (Path.refl x)) :
    uncurry (HigherHomotopy.genLoopMap (reverseMap x) (reverseMap_refl x) p) =
      GenLoop.symmAt (0 : Fin (d + 1)) (uncurry p) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro u
  change p (Fin.tail u) (σ (u 0)) =
    p (Fin.tail (fun j ↦ if j = 0 then σ (u 0) else u j)) (σ (u 0))
  congr 2

theorem reverse_native [NeZero d] (c : π_ d (Path x x) (Path.refl x)) :
    HigherHomotopy.map (N := Fin d) (reverseMap x) (reverseMap_refl x) c = c⁻¹ := by
  apply (homotopyMulEquiv d x).injective
  rw [map_inv]
  refine Quotient.inductionOn c fun p ↦ ?_
  exact (congrArg (fun q : GenLoop (Fin (d + 1)) X x ↦
    (Quotient.mk' q : HomotopyGroup (Fin (d + 1)) X x)) (uncurry_reverse p)).trans
      (HomotopyGroup.inv_spec (i := (0 : Fin (d + 1))) (p := uncurry p)).symm

end NoExoticSixSphere.GeneralizedLoopCurrying
