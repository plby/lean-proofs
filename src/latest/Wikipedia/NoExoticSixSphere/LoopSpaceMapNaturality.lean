import Wikipedia.NoExoticSixSphere.NativeHomotopyTargetEquality
import Wikipedia.NoExoticSixSphere.LoopSpaceDimensionShift

/-!
# Native currying is natural for the original map of loop spaces

The loop map is literal postcomposition. Its naturality square is proved
on the original cubical representatives, keeping the first-coordinate
convention of the checked dimension shift.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.LoopSpaceMap

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def map (f : C(X, Y)) (x : X) : C(Path x x, Path (f x) (f x)) where
  toFun p := p.map f.continuous
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact f.continuous.comp (Path.continuous_uncurry_iff.mpr continuous_id)

theorem map_refl (f : C(X, Y)) (x : X) : map f x (Path.refl x) = Path.refl (f x) := by
  apply Path.ext
  rfl

theorem homotopy_natural (f : C(X, Y)) (x : X) (d : ℕ)
    (c : π_ d (Path x x) (Path.refl x)) :
    GeneralizedLoopCurrying.homotopyEquiv d (f x)
      (HigherHomotopy.map (N := Fin d) (map f x) (map_refl f x) c) =
        HigherHomotopy.map (N := Fin (d + 1)) f (y := x) rfl
          (GeneralizedLoopCurrying.homotopyEquiv d x c) := by
  refine Quotient.inductionOn c fun p ↦ ?_
  apply congrArg (fun q : GenLoop (Fin (d + 1)) Y (f x) ↦
    (Quotient.mk' q : π_ (d + 1) Y (f x)))
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  rfl

theorem pi_bijective_of_loopMap (f : C(X, Y)) (x : X) (d : ℕ)
    (h : Function.Bijective
      (HigherHomotopy.map (N := Fin d) (map f x) (map_refl f x))) :
    Function.Bijective (HigherHomotopy.map (N := Fin (d + 1)) f (y := x) rfl) := by
  have hs : GeneralizedLoopCurrying.homotopyEquiv d (f x) ∘
      HigherHomotopy.map (N := Fin d) (map f x) (map_refl f x) =
        HigherHomotopy.map (N := Fin (d + 1)) f (y := x) rfl ∘
          GeneralizedLoopCurrying.homotopyEquiv d x := funext (homotopy_natural f x d)
  have hb := (GeneralizedLoopCurrying.homotopyEquiv d (f x)).bijective.comp h
  rw [hs] at hb
  exact (Function.Bijective.of_comp_iff _
    (GeneralizedLoopCurrying.homotopyEquiv d x).bijective).mp hb

end NoExoticSixSphere.LoopSpaceMap
