import ErdosProblems.Erdos941.SphereBaseChange
import ErdosProblems.Erdos941.Rotations

/-! # Linear rotations and words over finite coefficient rings -/

namespace Erdos941

open PairLocal

def linearTurn {R : Type*} [CommRing R] (t : R) (a : Axis) :
    (R × R × R) →ₗ[R] (R × R × R) where
  toFun v :=
    let d := v.1 + (sign a.1 : R) * v.2.1 + (sign a.2 : R) * v.2.2
    (2 * t * d - v.1, 2 * (sign a.1 : R) * t * d - v.2.1,
      2 * (sign a.2 : R) * t * d - v.2.2)
  map_add' v w := by ext <;> dsimp <;> ring
  map_smul' r v := by ext <;> dsimp <;> ring

theorem linearTurn_apply {R : Type*} [CommRing R] (t : R) (a : Axis) (v : R × R × R) :
    linearTurn t a v =
      (2 * t * (v.1 + (sign a.1 : R) * v.2.1 + (sign a.2 : R) * v.2.2) - v.1,
        2 * (sign a.1 : R) * t *
          (v.1 + (sign a.1 : R) * v.2.1 + (sign a.2 : R) * v.2.2) - v.2.1,
        2 * (sign a.2 : R) * t *
          (v.1 + (sign a.1 : R) * v.2.1 + (sign a.2 : R) * v.2.2) - v.2.2) := rfl

theorem linearTurn_involutive {R : Type*} [CommRing R] {t : R} (ht : 3 * t = 1)
    (a : Axis) : Function.Involutive (linearTurn t a) := by
  intro v
  have hs : (sign a.1 : R) ^ 2 = 1 := by rw [← Int.cast_pow, sign_sq, Int.cast_one]
  have hu : (sign a.2 : R) ^ 2 = 1 := by rw [← Int.cast_pow, sign_sq, Int.cast_one]
  let d := v.1 + (sign a.1 : R) * v.2.1 + (sign a.2 : R) * v.2.2
  apply Prod.ext
  · simp only [linearTurn_apply]
    linear_combination (4 * t * d) * ht + (4 * t ^ 2 * d) * hs + (4 * t ^ 2 * d) * hu
  · apply Prod.ext
    · simp only [linearTurn_apply]
      linear_combination (4 * (sign a.1 : R) * t * d) * ht +
        (4 * (sign a.1 : R) * t ^ 2 * d) * hs + (4 * (sign a.1 : R) * t ^ 2 * d) * hu
    · simp only [linearTurn_apply]
      linear_combination (4 * (sign a.2 : R) * t * d) * ht +
        (4 * (sign a.2 : R) * t ^ 2 * d) * hs + (4 * (sign a.2 : R) * t ^ 2 * d) * hu

def linearWord {R : Type*} [CommRing R] (t : R) : List Axis →
    (R × R × R) →ₗ[R] (R × R × R)
  | [] => LinearMap.id
  | a :: w => (linearWord t w).comp (linearTurn t a)

@[simp] theorem linearWord_nil {R : Type*} [CommRing R] (t : R) (v : R × R × R) :
    linearWord t [] v = v := rfl

@[simp] theorem linearWord_cons {R : Type*} [CommRing R] (t : R) (a : Axis)
    (w : List Axis) (v : R × R × R) :
    linearWord t (a :: w) v = linearWord t w (linearTurn t a v) := rfl

theorem linearWord_append {R : Type*} [CommRing R] (t : R) (u w : List Axis)
    (v : R × R × R) : linearWord t (u ++ w) v = linearWord t w (linearWord t u v) := by
  induction u generalizing v with
  | nil => rfl
  | cons a u ih => exact ih (linearTurn t a v)

theorem linearWord_injective {R : Type*} [CommRing R] {t : R} (ht : 3 * t = 1)
    (w : List Axis) : Function.Injective (linearWord t w) := by
  induction w with
  | nil => exact Function.injective_id
  | cons a w ih => exact ih.comp (linearTurn_involutive ht a).injective

theorem linearTurn_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (t : R) (a : Axis) (v : R × R × R) :
    mapCoeffs φ (linearTurn t a v) = linearTurn (φ t) a (mapCoeffs φ v) := by
  ext <;> simp [linearTurn_apply, mapCoeffs, map_ofNat]

theorem linearWord_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (t : R) (w : List Axis) (v : R × R × R) :
    mapCoeffs φ (linearWord t w v) = linearWord (φ t) w (mapCoeffs φ v) := by
  induction w generalizing v with
  | nil => rfl
  | cons a w ih => rw [linearWord_cons, ih, linearTurn_map, linearWord_cons]

end Erdos941
