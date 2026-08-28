import Wikipedia.NoExoticSixSphere.JamesSphereAttachingSmashCube
import Wikipedia.NoExoticSixSphere.SphereSixCubeSymmetry

/-!
# The original sphere pairing respects the actual cubical symmetries

Surjectivity of the original sphere-cube quotients reduces each formula
to its six literal coordinates, including collapsed faces. Reflecting
the first coordinate of either S3 factor reflects coordinate zero or
three of S6; exchanging factors exchanges the two three-coordinate
blocks. Thus the previously proved homology signs apply to this pairing.
-/

noncomputable section

open scoped Topology unitInterval

namespace NoExoticSixSphere.JamesSphere.PairingSixSigns

abbrev reflection : C(Sphere 3, Sphere 3) := SmoothCube.reflection 3 (by decide) 0

theorem pairing_cubes (u v : Fin 3 → I) :
    pairing 3 (SmoothCube.quotient 3 u, SmoothCube.quotient 3 v) =
      SmoothCube.quotient 6 (AttachingSquare.tailCoordinates 3 ![u, v]) :=
  AttachingSquare.pairing_tail_cube ![u, v]

theorem pairing_reflection_left (x y : Sphere 3) :
    pairing 3 (reflection x, y) =
      SmoothCube.reflection 6 (by decide) 0 (pairing 3 (x, y)) := by
  obtain ⟨u, rfl⟩ := SmoothCube.quotient_surjective (by decide : 0 < 3) x
  obtain ⟨v, rfl⟩ := SmoothCube.quotient_surjective (by decide : 0 < 3) y
  rw [SmoothCube.reflection_quotient, pairing_cubes, pairing_cubes,
    SmoothCube.reflection_quotient]
  apply congrArg (SmoothCube.quotient 6)
  funext j
  fin_cases j <;> rfl

theorem pairing_reflection_right (x y : Sphere 3) :
    pairing 3 (x, reflection y) =
      SmoothCube.reflection 6 (by decide) 3 (pairing 3 (x, y)) := by
  obtain ⟨u, rfl⟩ := SmoothCube.quotient_surjective (by decide : 0 < 3) x
  obtain ⟨v, rfl⟩ := SmoothCube.quotient_surjective (by decide : 0 < 3) y
  rw [SmoothCube.reflection_quotient, pairing_cubes, pairing_cubes,
    SmoothCube.reflection_quotient]
  apply congrArg (SmoothCube.quotient 6)
  funext j
  fin_cases j <;> rfl

theorem pairing_swap (x y : Sphere 3) :
    pairing 3 (y, x) = SphereSixCube.permutation SphereSixCube.blockSwap (pairing 3 (x, y)) := by
  obtain ⟨u, rfl⟩ := SmoothCube.quotient_surjective (by decide : 0 < 3) x
  obtain ⟨v, rfl⟩ := SmoothCube.quotient_surjective (by decide : 0 < 3) y
  rw [pairing_cubes, pairing_cubes, SphereSixCube.permutation_quotient]
  apply congrArg (SmoothCube.quotient 6)
  funext j
  fin_cases j <;> rfl

theorem pairing_reflection_both (x y : Sphere 3) :
    pairing 3 (reflection x, reflection y) =
      SmoothCube.reflection 6 (by decide) 0
        (SmoothCube.reflection 6 (by decide) 3 (pairing 3 (x, y))) := by
  rw [pairing_reflection_left, pairing_reflection_right]

theorem pairing_reverse_reflection (x y : Sphere 3) :
    pairing 3 (y, reflection x) =
      SmoothCube.reflection 6 (by decide) 3
        (SphereSixCube.permutation SphereSixCube.blockSwap (pairing 3 (x, y))) := by
  rw [pairing_reflection_right, pairing_swap x y]

end NoExoticSixSphere.JamesSphere.PairingSixSigns
