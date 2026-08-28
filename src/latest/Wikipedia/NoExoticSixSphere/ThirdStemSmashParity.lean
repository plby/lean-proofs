import Wikipedia.NoExoticSixSphere.SphereSmashNativeBilinear
import Wikipedia.NoExoticSixSphere.SixthStemCompositionSquareOrder

/-!
# The original Hopf-coordinate lifts have the same sixth-stem square

The actual native smash pairing is bilinear. In the checked cyclic
third stem its value therefore depends only on the parity of each
coordinate, because the actual generator square has square one.
The intrinsic twelfth-power test proves that every original
Hopf-coordinate-one lift has odd coordinate, including lifts of order
eight. Their actual square is the previously constructed native class.

This proves independence of these choices, not nontriviality of the
square, generation of the sixth stem, or geometric Arf detection.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.SphereSmashNative

open SmoothCube SphereComposition

def coordinate (x : Source) : ZMod 24 := (StableThirdAttaching.groupEquiv 0 x).toAdd

theorem generator_pow_coordinate (x : Source) :
    StableThirdComposition.generator 0 ^ (coordinate x).val = x := by
  apply (StableThirdAttaching.groupEquiv 0).injective
  rw [map_pow, StableThirdComposition.generator_coordinate]
  change Multiplicative.ofAdd ((coordinate x).val • (1 : ZMod 24)) =
    Multiplicative.ofAdd (coordinate x)
  simp only [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

theorem generator_product : product (StableThirdComposition.generator 0)
    (StableThirdComposition.generator 0) = SixthStemSmashSquare.nativeClass := by
  rw [← StableThirdComposition.representative_class 0]
  exact product_sphereClass_square (StableThirdComposition.representative 0)

theorem product_coordinates (x y : Source) :
    product x y = SixthStemSmashSquare.nativeClass ^ ((coordinate x).val * (coordinate y).val) := by
  calc
    product x y = product
        (StableThirdComposition.generator 0 ^ (coordinate x).val)
        (StableThirdComposition.generator 0 ^ (coordinate y).val) :=
      congrArg₂ product (generator_pow_coordinate x).symm (generator_pow_coordinate y).symm
    _ = _ := by rw [product_pow_right, product_pow_left, generator_product, ← pow_mul]

theorem twelve_nsmul_eq_zero_iff (z : ZMod 24) :
    (12 : ℕ) • z = 0 ↔ z.val % 2 = 0 := by
  fin_cases z <;> decide

theorem twelfth_power_eq_one_iff (x : Source) :
    x ^ 12 = 1 ↔ (coordinate x).val % 2 = 0 := by
  rw [← (StableThirdAttaching.groupEquiv 0).map_eq_one_iff, map_pow]
  change (12 : ℕ) • coordinate x = 0 ↔ (coordinate x).val % 2 = 0
  exact twelve_nsmul_eq_zero_iff (coordinate x)

theorem coordinate_odd_of_twelfth_power_ne_one (x : Source) (hx : x ^ 12 ≠ 1) :
    (coordinate x).val % 2 = 1 := by
  have hn : (coordinate x).val % 2 ≠ 0 := fun h ↦ hx ((twelfth_power_eq_one_iff x).mpr h)
  omega

theorem pow_eq_mod_two {G : Type*} [Monoid G] (x : G) (hx : x ^ 2 = 1) (k : ℕ) :
    x ^ k = x ^ (k % 2) := by
  calc
    x ^ k = x ^ (k % 2 + 2 * (k / 2)) := congrArg (fun n ↦ x ^ n) (Nat.mod_add_div k 2).symm
    _ = _ := by rw [pow_add, pow_mul, hx, one_pow, mul_one]

theorem product_eq_of_twelfth_powers_ne_one (x y : Source) (hx : x ^ 12 ≠ 1)
    (hy : y ^ 12 ≠ 1) : product x y = SixthStemSmashSquare.nativeClass := by
  rw [product_coordinates, pow_eq_mod_two _ SixthStemSmashSquare.nativeClass_pow_two,
    Nat.mul_mod, coordinate_odd_of_twelfth_power_ne_one x hx,
    coordinate_odd_of_twelfth_power_ne_one y hy]
  simp only [mul_one, Nat.one_mod, pow_one]

theorem product_eq_one_of_twelfth_power_eq_one_left (x y : Source) (hx : x ^ 12 = 1) :
    product x y = 1 := by
  rw [product_coordinates, pow_eq_mod_two _ SixthStemSmashSquare.nativeClass_pow_two,
    Nat.mul_mod, (twelfth_power_eq_one_iff x).mp hx, zero_mul, Nat.zero_mod, pow_zero]

theorem product_eq_one_of_twelfth_power_eq_one_right (x y : Source) (hy : y ^ 12 = 1) :
    product x y = 1 := by
  rw [product_coordinates, pow_eq_mod_two _ SixthStemSmashSquare.nativeClass_pow_two,
    Nat.mul_mod, (twelfth_power_eq_one_iff y).mp hy, mul_zero, Nat.zero_mod, pow_zero]

theorem original_lift_product (b c : ZMod 12) :
    product (SphereFiveEighth.projection (Multiplicative.ofAdd 1, Multiplicative.ofAdd b))
      (SphereFiveEighth.projection (Multiplicative.ofAdd 1, Multiplicative.ofAdd c)) =
        SixthStemSmashSquare.nativeClass := by
  apply product_eq_of_twelfth_powers_ne_one
  · rw [SphereFiveEighth.projection_twelfth_power]
    exact SphereFiveEighth.integerLift_twelfth_power_ne_one
  · rw [SphereFiveEighth.projection_twelfth_power]
    exact SphereFiveEighth.integerLift_twelfth_power_ne_one

theorem sphereClass_square_eq_of_twelfth_power_ne_one (f : Based 8 5)
    (hf : sphereClass f ^ 12 ≠ 1) :
    sphereClass (SphereSmash.basedSquare f) = SixthStemSmashSquare.nativeClass := by
  rw [← product_sphereClass_square]
  exact product_eq_of_twelfth_powers_ne_one _ _ hf hf

theorem sphereClass_square_eq_of_original_lift (f : Based 8 5) (b : ZMod 12)
    (hf : sphereClass f =
      SphereFiveEighth.projection (Multiplicative.ofAdd 1, Multiplicative.ofAdd b)) :
    sphereClass (SphereSmash.basedSquare f) = SixthStemSmashSquare.nativeClass := by
  rw [← product_sphereClass_square, hf]
  exact original_lift_product b b

end NoExoticSixSphere.SphereSmashNative
