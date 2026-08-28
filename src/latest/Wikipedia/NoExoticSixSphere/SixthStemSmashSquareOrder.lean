import Wikipedia.NoExoticSixSphere.SphereSmashSquare
import Wikipedia.NoExoticSixSphere.SuspendedSphereTargetSigns
import Wikipedia.NoExoticSixSphere.StableThirdCompositionSquare

/-!
# The actual S8-to-S5 smash square has order at most two

Exchanging the two source eight-coordinate blocks has positive sign;
exchanging the two target five-coordinate blocks has negative sign.
The exact smash-square swap identity and the checked stable-range
target sign imply that its ORIGINAL native class is its own inverse.

This constructs a genuine order-at-most-two sixth-stem class from the
checked third-stem generator. Nontriviality, generation, Arf detection,
and comparison with the separately constructed composition square are
not asserted here.
-/

noncomputable section

open scoped Topology unitInterval

namespace NoExoticSixSphere.SixthStemSmashSquare

open SmoothCube SphereComposition

def blockEight : Equiv.Perm (Fin 16) :=
  ((((((Equiv.swap 0 8 * Equiv.swap 1 9) * Equiv.swap 2 10) * Equiv.swap 3 11) *
    Equiv.swap 4 12) * Equiv.swap 5 13) * Equiv.swap 6 14) * Equiv.swap 7 15

def blockFive : Equiv.Perm (Fin 10) :=
  (((Equiv.swap 0 5 * Equiv.swap 1 6) * Equiv.swap 2 7) * Equiv.swap 3 8) * Equiv.swap 4 9

theorem blockEight_sign : ((Equiv.Perm.sign blockEight : ℤˣ) : ℤ) = 1 := by
  norm_num [blockEight, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap (show (0 : Fin 16) ≠ 8 by decide),
    Equiv.Perm.sign_swap (show (1 : Fin 16) ≠ 9 by decide),
    Equiv.Perm.sign_swap (show (2 : Fin 16) ≠ 10 by decide),
    Equiv.Perm.sign_swap (show (3 : Fin 16) ≠ 11 by decide),
    Equiv.Perm.sign_swap (show (4 : Fin 16) ≠ 12 by decide),
    Equiv.Perm.sign_swap (show (5 : Fin 16) ≠ 13 by decide),
    Equiv.Perm.sign_swap (show (6 : Fin 16) ≠ 14 by decide),
    Equiv.Perm.sign_swap (show (7 : Fin 16) ≠ 15 by decide)]

theorem blockFive_sign : ((Equiv.Perm.sign blockFive : ℤˣ) : ℤ) = -1 := by
  norm_num [blockFive, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap (show (0 : Fin 10) ≠ 5 by decide),
    Equiv.Perm.sign_swap (show (1 : Fin 10) ≠ 6 by decide),
    Equiv.Perm.sign_swap (show (2 : Fin 10) ≠ 7 by decide),
    Equiv.Perm.sign_swap (show (3 : Fin 10) ≠ 8 by decide),
    Equiv.Perm.sign_swap (show (4 : Fin 10) ≠ 9 by decide)]

theorem blockEight_coordinates (u v : Fin 8 → I) :
    Fin.append v u = fun j ↦ Fin.append u v (blockEight j) := by
  funext j
  fin_cases j <;> rfl

theorem blockFive_coordinates (u v : Fin 5 → I) :
    Fin.append v u = fun j ↦ Fin.append u v (blockFive j) := by
  funext j
  fin_cases j <;> rfl

theorem square_native_pow_two (f : Based 8 5) :
    sphereClass (SphereSmash.basedSquare f) ^ 2 = 1 := by
  let F := SphereSmash.basedSquare f
  have hm : HigherHomotopy.map (N := Fin 16) (permutation 10 (by decide) blockFive)
      (permutation_pole 10 (by decide) blockFive) (sphereClass F) =
      sphereClass (permuted (by decide) blockEight F) := by
    apply congrArg (fun p : GenLoop (Fin 16) (Sphere 10) (spherePole 10) ↦
      (Quotient.mk' p : π_ 16 (Sphere 10) (spherePole 10)))
    apply GenLoop.ext
    intro u
    exact SphereSmash.square_swap f (by decide) (by decide) blockEight blockFive
      blockEight_coordinates blockFive_coordinates (SmoothCube.quotient 16 u)
  have h := CubicalSphereSuspension.permutation_native_negative (d := 15) (n := 9)
    (by decide) blockFive blockFive_sign (sphereClass F)
  rw [hm, permuted_sphereClass, blockEight_sign, zpow_one] at h
  change sphereClass F ^ 2 = 1
  rw [pow_two]
  exact (congrArg (fun x ↦ sphereClass F * x) h).trans (mul_inv_cancel _)

def nativeClass : StableSixSphereMaps.NativeStage 8 :=
  sphereClass (SphereSmash.basedSquare (StableThirdComposition.representative 0))

theorem nativeClass_pow_two : nativeClass ^ 2 = 1 :=
  square_native_pow_two (StableThirdComposition.representative 0)

def stableClass : CubicalStableSix.Group := CubicalStableSix.ofNative nativeClass

theorem stableClass_pow_two : stableClass ^ 2 = 1 := by
  change CubicalStableSix.ofNativeHom 8 nativeClass ^ 2 = 1
  rw [← map_pow, nativeClass_pow_two, map_one]

theorem stableClass_eq_one_iff : stableClass = 1 ↔ nativeClass = 1 :=
  CubicalStableSix.ofNative_eq_one_iff_native (by decide) nativeClass

end NoExoticSixSphere.SixthStemSmashSquare
