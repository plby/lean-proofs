import ErdosProblems.Erdos941.PairLocal.SpecialOrbits
import ErdosProblems.Erdos941.PadicSumSquares

/-! # An explicit integral change from three squares to the split ternary form -/

namespace Erdos941

def normThree {R : Type*} [CommRing R] (v : R × R × R) : R :=
  v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2

def dotThree {R : Type*} [CommRing R] (v w : R × R × R) : R :=
  v.1 * w.1 + v.2.1 * w.2.1 + v.2.2 * w.2.2

def sphereSplitLinear {R : Type*} [CommRing R] (a b t : R) :
    (R × R × R) →ₗ[R] (R × R × R) where
  toFun v := (t * (v.2.2 - a * v.1 - b * v.2.1),
    b * v.1 - a * v.2.1, t * (v.2.2 + a * v.1 + b * v.2.1))
  map_add' v w := by ext <;> dsimp <;> ring
  map_smul' r v := by ext <;> dsimp <;> ring

def sphereUnsplitLinear {R : Type*} [CommRing R] (a b : R) :
    (R × R × R) →ₗ[R] (R × R × R) where
  toFun v := (a * (v.1 - v.2.2) - b * v.2.1,
    b * (v.1 - v.2.2) + a * v.2.1, v.1 + v.2.2)
  map_add' v w := by ext <;> dsimp <;> ring
  map_smul' r v := by ext <;> dsimp <;> ring

theorem sphereSplitLinear_apply {R : Type*} [CommRing R] (a b t : R) (v : R × R × R) :
    sphereSplitLinear a b t v = (t * (v.2.2 - a * v.1 - b * v.2.1),
      b * v.1 - a * v.2.1, t * (v.2.2 + a * v.1 + b * v.2.1)) := rfl

theorem sphereUnsplitLinear_apply {R : Type*} [CommRing R] (a b : R) (v : R × R × R) :
    sphereUnsplitLinear a b v = (a * (v.1 - v.2.2) - b * v.2.1,
      b * (v.1 - v.2.2) + a * v.2.1, v.1 + v.2.2) := rfl

theorem sphereUnsplit_split {R : Type*} [CommRing R] {a b t : R}
    (hab : a ^ 2 + b ^ 2 = -1) (ht : 2 * t = 1) (v : R × R × R) :
    sphereUnsplitLinear a b (sphereSplitLinear a b t v) = v := by
  rw [sphereUnsplitLinear_apply, sphereSplitLinear_apply]
  apply Prod.ext
  · dsimp
    linear_combination -v.1 * hab - a * (a * v.1 + b * v.2.1) * ht
  · apply Prod.ext
    · dsimp
      linear_combination -v.2.1 * hab - b * (a * v.1 + b * v.2.1) * ht
    · dsimp
      linear_combination v.2.2 * ht

theorem sphereSplit_unsplit {R : Type*} [CommRing R] {a b t : R}
    (hab : a ^ 2 + b ^ 2 = -1) (ht : 2 * t = 1) (v : R × R × R) :
    sphereSplitLinear a b t (sphereUnsplitLinear a b v) = v := by
  rw [sphereSplitLinear_apply, sphereUnsplitLinear_apply]
  apply Prod.ext
  · dsimp
    linear_combination -t * (v.1 - v.2.2) * hab + v.1 * ht
  · apply Prod.ext
    · dsimp
      linear_combination -v.2.1 * hab
    · dsimp
      linear_combination t * (v.1 - v.2.2) * hab + v.2.2 * ht

def sphereSplitEquiv {R : Type*} [CommRing R] {a b t : R}
    (hab : a ^ 2 + b ^ 2 = -1) (ht : 2 * t = 1) :
    (R × R × R) ≃ₗ[R] (R × R × R) :=
  { sphereSplitLinear a b t with
    invFun := sphereUnsplitLinear a b
    left_inv := sphereUnsplit_split hab ht
    right_inv := sphereSplit_unsplit hab ht }

theorem normThree_unsplit {R : Type*} [CommRing R] {a b : R}
    (hab : a ^ 2 + b ^ 2 = -1) (v : R × R × R) :
    normThree (sphereUnsplitLinear a b v) = -PairLocal.discr v := by
  rw [sphereUnsplitLinear_apply]
  dsimp [normThree, PairLocal.discr]
  linear_combination ((v.1 - v.2.2) ^ 2 + v.2.1 ^ 2) * hab

theorem discr_sphereSplitEquiv {R : Type*} [CommRing R] {a b t : R}
    (hab : a ^ 2 + b ^ 2 = -1) (ht : 2 * t = 1) (v : R × R × R) :
    PairLocal.discr (sphereSplitEquiv hab ht v) = -normThree v := by
  have h := normThree_unsplit hab (sphereSplitLinear a b t v)
  rw [sphereUnsplit_split hab ht] at h
  change PairLocal.discr (sphereSplitLinear a b t v) = -normThree v
  linear_combination h

end Erdos941
