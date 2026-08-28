import Wikipedia.NoExoticSixSphere.MappingCylinderNativeHomotopy

/-!
# Native homotopy transport along literal basepoint equality

These maps only transport along an equality of points, not along a chosen
path. Their formulas retain the original induced native homotopy maps.
This is used when the image of the James sphere pole is the unit word.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.NativeHomotopyTargetEquality

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def equiv (d : ℕ) [NeZero d] {x y : X} (h : x = y) : π_ d X x ≃* π_ d X y := by
  subst y
  exact MulEquiv.refl _

theorem equiv_map (d : ℕ) [NeZero d] (f : C(X, Y)) {x : X} {y : Y} (h : f x = y)
    (c : π_ d X x) :
    equiv d h (HigherHomotopy.map (N := Fin d) f (y := x) rfl c) =
      HigherHomotopy.map (N := Fin d) f h c := by
  subst y
  rfl

theorem map_equiv (d : ℕ) [NeZero d] (f : C(X, Y)) {x x' : X} {y : Y}
    (h : x = x') (hy : f x' = y) (c : π_ d X x) :
    HigherHomotopy.map (N := Fin d) f hy (equiv d h c) =
      HigherHomotopy.map (N := Fin d) f ((congrArg f h).trans hy) c := by
  subst x'
  rfl

theorem map_injective_iff (d : ℕ) (f : C(X, Y)) {x : X} {y : Y} (h : f x = y) :
    Function.Injective (HigherHomotopy.map (N := Fin d) f h) ↔
      Function.Injective (HigherHomotopy.map (N := Fin d) f (y := x) rfl) := by
  subst y
  rfl

theorem map_surjective_iff (d : ℕ) (f : C(X, Y)) {x : X} {y : Y} (h : f x = y) :
    Function.Surjective (HigherHomotopy.map (N := Fin d) f h) ↔
      Function.Surjective (HigherHomotopy.map (N := Fin d) f (y := x) rfl) := by
  subst y
  rfl

theorem map_bijective_iff (d : ℕ) (f : C(X, Y)) {x : X} {y : Y} (h : f x = y) :
    Function.Bijective (HigherHomotopy.map (N := Fin d) f h) ↔
      Function.Bijective (HigherHomotopy.map (N := Fin d) f (y := x) rfl) := by
  subst y
  rfl

end NoExoticSixSphere.NativeHomotopyTargetEquality
