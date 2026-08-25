import Mathlib.Data.Complex.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring

/-!
# Iteration in affine complex coordinates

These algebraic identities apply to any map whose chosen complex coordinates
have the form `z ↦ a * z + b`.  No continuity, isometry, or coordinate
surjectivity is needed.  Coordinate injectivity is used only to recover an
identity of the original maps or distinctness of coordinate values.
-/

namespace Puzzling139335.CentralRotation.RotationAlgebra

variable {X : Type*} {f : X → X} {coord : X → ℂ} {a b : ℂ}

/-- Translation cancels from coordinate differences, so iteration multiplies
each difference by the corresponding power of the linear coefficient. -/
theorem iterate_coordinate_sub
    (hf : ∀ x, coord (f x) = a * coord x + b)
    (n : ℕ) (x y : X) :
    coord (f^[n] x) - coord (f^[n] y) = a ^ n * (coord x - coord y) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        coord (f^[n + 1] x) - coord (f^[n + 1] y) =
            a * (coord (f^[n] x) - coord (f^[n] y)) := by
          simp only [Function.iterate_succ_apply', hf]
          ring
        _ = a ^ (n + 1) * (coord x - coord y) := by
          rw [ih, pow_succ]
          ring

/-- The iterate of an affine map with a fixed point is multiplication by a
power of its coefficient about that fixed point in complex coordinates. -/
theorem iterate_coordinate_of_fixed
    (hf : ∀ x, coord (f x) = a * coord x + b)
    {c : X} (hc : f c = c) (n : ℕ) (x : X) :
    coord (f^[n] x) = coord c + a ^ n * (coord x - coord c) := by
  have hsub := iterate_coordinate_sub hf n x c
  rw [Function.iterate_fixed hc n] at hsub
  calc
    coord (f^[n] x) = coord c + (coord (f^[n] x) - coord c) := by ring
    _ = coord c + a ^ n * (coord x - coord c) := by rw [hsub]

/-- An affine map with a fixed point has identity `n`th iterate whenever its
linear coefficient has `n`th power one. -/
theorem iterate_eq_id_of_fixed_of_pow_eq_one
    (hf : ∀ x, coord (f x) = a * coord x + b)
    (hcoord : Function.Injective coord) {c : X} (hc : f c = c)
    {n : ℕ} (hn : a ^ n = 1) : f^[n] = id := by
  funext x
  apply hcoord
  change coord (f^[n] x) = coord x
  rw [iterate_coordinate_of_fixed hf hc n x, hn, one_mul]
  ring

/-- If an iterate fixes two points with distinct coordinates, its linear
coefficient has the corresponding power equal to one. -/
theorem pow_eq_one_of_iterate_fixed_pair
    (hf : ∀ x, coord (f x) = a * coord x + b)
    {n : ℕ} {p q : X} (hpq : coord p ≠ coord q)
    (hp : f^[n] p = p) (hq : f^[n] q = q) : a ^ n = 1 := by
  apply mul_right_cancel₀ (sub_ne_zero.mpr hpq)
  have hsub := iterate_coordinate_sub hf n p q
  rw [hp, hq] at hsub
  simpa only [one_mul] using hsub.symm

/-- A direct affine map fixing two distinct points has coefficient one. -/
theorem coefficient_eq_one_of_two_fixed
    (hf : ∀ x, coord (f x) = a * coord x + b)
    (hcoord : Function.Injective coord) {p q : X} (hpq : p ≠ q)
    (hp : f p = p) (hq : f q = q) : a = 1 := by
  simpa only [pow_one] using
    pow_eq_one_of_iterate_fixed_pair hf (n := 1)
      (fun h => hpq (hcoord h)) hp hq

/-- A direct affine map fixing two distinct points is the identity, provided
the complex coordinates distinguish points. -/
theorem eq_id_of_two_fixed
    (hf : ∀ x, coord (f x) = a * coord x + b)
    (hcoord : Function.Injective coord) {p q : X} (hpq : p ≠ q)
    (hp : f p = p) (hq : f q = q) : f = id := by
  have ha := coefficient_eq_one_of_two_fixed hf hcoord hpq hp hq
  have hpow : a ^ 1 = 1 := by simpa only [pow_one] using ha
  simpa only [Function.iterate_one] using
    iterate_eq_id_of_fixed_of_pow_eq_one hf hcoord hp hpow

/-- A direct affine map interchanging two distinct points has coefficient
minus one.  In geometric applications this is the half-turn coefficient. -/
theorem coefficient_eq_neg_one_of_swap
    (hf : ∀ x, coord (f x) = a * coord x + b)
    (hcoord : Function.Injective coord) {p q : X} (hpq : p ≠ q)
    (hp : f p = q) (hq : f q = p) : a = -1 := by
  have hdelta : coord p - coord q ≠ 0 :=
    sub_ne_zero.mpr (fun h => hpq (hcoord h))
  apply mul_right_cancel₀ hdelta
  have hsub := iterate_coordinate_sub hf 1 p q
  simp only [Function.iterate_one, pow_one, hp, hq] at hsub
  calc
    a * (coord p - coord q) = coord q - coord p := hsub.symm
    _ = -1 * (coord p - coord q) := by ring

/-- Two affine formulas agreeing at two distinct coordinate values have the
same linear and translation coefficients. -/
theorem affine_coordinate_coefficients_unique
    {a' b' : ℂ} {p q : X} (hpq : coord p ≠ coord q)
    (h : ∀ x, a * coord x + b = a' * coord x + b') :
    a = a' ∧ b = b' := by
  have hmul : a * (coord p - coord q) = a' * (coord p - coord q) := by
    calc
      a * (coord p - coord q) =
          (a * coord p + b) - (a * coord q + b) := by ring
      _ = (a' * coord p + b') - (a' * coord q + b') := by rw [h p, h q]
      _ = a' * (coord p - coord q) := by ring
  have ha : a = a' := mul_right_cancel₀ (sub_ne_zero.mpr hpq) hmul
  refine ⟨ha, ?_⟩
  have hp := h p
  rw [ha] at hp
  exact add_left_cancel hp

/-- Uniqueness of the two coefficients in an affine map on the complex plane. -/
theorem complex_affine_coefficients_unique {a' b' : ℂ}
    (h : ∀ z : ℂ, a * z + b = a' * z + b') : a = a' ∧ b = b' := by
  exact affine_coordinate_coefficients_unique
    (coord := id) (p := (0 : ℂ)) (q := 1) zero_ne_one h

end Puzzling139335.CentralRotation.RotationAlgebra
