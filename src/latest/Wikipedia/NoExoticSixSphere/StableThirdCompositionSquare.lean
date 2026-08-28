import Wikipedia.NoExoticSixSphere.NativeSphereComposition
import Wikipedia.NoExoticSixSphere.StableThirdCyclicGroup
import Wikipedia.NoExoticSixSphere.CubicalStableSixEquivalence

/-!
# An actual sixth-stem composition from the checked third-stem generator

Choose one genuine based representative of the order-twenty-four
generator in pi8(S5), and use the ORIGINAL product suspensions for all
later representatives. Their composites define actual maps S(k+14)
to S(k+8). Exact suspension naturality identifies their stable classes.

Only the order bound twenty-four is established here. Nontriviality,
order two, generation of the sixth stem, and Arf detection are separate
proof obligations; they are not built into this definition.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.StableThirdComposition

open SmoothCube SphereComposition CubicalSphereSuspension

def generator (k : ℕ) : StableThirdAttaching.Stage k :=
  (StableThirdAttaching.groupEquiv k).symm (Multiplicative.ofAdd (1 : ZMod 24))

theorem generator_coordinate (k : ℕ) :
    StableThirdAttaching.groupEquiv k (generator k) = Multiplicative.ofAdd (1 : ZMod 24) :=
  (StableThirdAttaching.groupEquiv k).apply_symm_apply _

theorem generator_step (k : ℕ) : StableThirdAttaching.stepHom k (generator k) =
    generator (k + 1) := by
  apply (StableThirdAttaching.groupEquiv (k + 1)).injective
  rw [StableThirdAttaching.groupEquiv_stepHom, generator_coordinate, generator_coordinate]

theorem orderOf_generator (k : ℕ) : orderOf (generator k) = 24 := by
  rw [← orderOf_injective (StableThirdAttaching.groupEquiv k).toMonoidHom
    (StableThirdAttaching.groupEquiv k).injective (generator k)]
  change orderOf (StableThirdAttaching.groupEquiv k (generator k)) = 24
  rw [generator_coordinate]
  exact ZMod.addOrderOf_one 24

def representative : (k : ℕ) → Based (k + 8) (k + 5)
  | 0 => (sphereClass_surjective (by decide : 0 < 8) (generator 0)).choose
  | k + 1 => productBasedMap (representative k)

theorem representative_succ (k : ℕ) :
    representative (k + 1) = productBasedMap (representative k) := rfl

theorem representative_class (k : ℕ) : sphereClass (representative k) = generator k := by
  induction k with
  | zero => exact (sphereClass_surjective (by decide : 0 < 8) (generator 0)).choose_spec
  | succ k ih =>
    rw [representative_succ, ← hom_sphereClass, ih]
    exact generator_step k

def squareMap (k : ℕ) : Based (k + 14) (k + 8) :=
  comp (representative (k + 3)) (representative (k + 6))

theorem squareMap_suspension (k : ℕ) :
    productBasedMap (squareMap k) = squareMap (k + 1) := by
  change productBasedMap (comp (representative (k + 3)) (representative (k + 6))) = _
  rw [productBasedMap_comp]
  rfl

def squareClass (k : ℕ) : StableSixSphereMaps.NativeStage (k + 6) :=
  sphereClass (squareMap k)

theorem squareClass_postcompose (k : ℕ) :
    squareClass k = mapHom (representative (k + 3)) (k + 14) (generator (k + 6)) := by
  change sphereClass (comp (representative (k + 3)) (representative (k + 6))) = _
  rw [← mapHom_sphereClass, representative_class]

theorem squareClass_step (k : ℕ) :
    CubicalStableSix.stepHom (k + 6) (squareClass k) = squareClass (k + 1) := by
  change hom (k + 14) (k + 8) (sphereClass (squareMap k)) = _
  rw [hom_sphereClass, squareMap_suspension]
  rfl

theorem squareClass_pow_twentyFour (k : ℕ) : squareClass k ^ 24 = 1 := by
  rw [squareClass_postcompose, ← map_pow,
    StableThirdAttaching.pow_twentyFour (k + 6), map_one]

def stableSquare : CubicalStableSix.Group := CubicalStableSix.ofNative (squareClass 0)

theorem stableSquare_eq_stage (k : ℕ) :
    CubicalStableSix.ofNative (squareClass k) = stableSquare := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← squareClass_step, CubicalStableSix.ofNative_stepHom]
    exact ih

theorem stableSquare_pow_twentyFour : stableSquare ^ 24 = 1 := by
  change CubicalStableSix.ofNativeHom 6 (squareClass 0) ^ 24 = 1
  rw [← map_pow, squareClass_pow_twentyFour, map_one]

theorem stableSquare_eq_one_iff : stableSquare = 1 ↔ squareClass 0 = 1 :=
  CubicalStableSix.ofNative_eq_one_iff_native (by decide) (squareClass 0)

end NoExoticSixSphere.StableThirdComposition
