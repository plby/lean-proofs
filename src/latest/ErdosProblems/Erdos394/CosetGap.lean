import ErdosProblems.Erdos394.CRT

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The square-root-of-one coordinate for the two-term problem

This file begins the formalization of the coset-gap argument.  It proves the
algebraic change of variables and the resulting admissible-start construction.
The finite coset-gap summation identity will be added separately.
-/

namespace Erdos394

/-- In any commutative ring where `2` and `h` are units, the roots of
`j(hj+1)=0` are carried bijectively to square roots of one by
`u=2hj+1`. -/
theorem affine_square_eq_one_iff {R : Type*} [CommRing R]
    (h j : R) (h2 : IsUnit (2 : R)) (hh : IsUnit h) :
    (2 * h * j + 1) ^ 2 = 1 ↔ j * (h * j + 1) = 0 := by
  have h4 : IsUnit (4 : R) := by
    convert h2.mul h2 using 1 <;> norm_num
  have hunit : IsUnit (4 * h : R) := h4.mul hh
  constructor
  · intro hs
    have hz : (4 * h) * (j * (h * j + 1)) = 0 := by
      calc
        (4 * h) * (j * (h * j + 1)) = (2 * h * j + 1) ^ 2 - 1 := by ring
        _ = 0 := by rw [hs]; ring
    apply hunit.mul_left_cancel
    simpa using hz
  · intro hz
    calc
      (2 * h * j + 1) ^ 2 = (4 * h) * (j * (h * j + 1)) + 1 := by ring
      _ = 1 := by rw [hz, mul_zero, zero_add]

/-- A restricted CRT root `j` for the medium-prime part `q` gives the actual
start `m*j` for modulus `m*q`. -/
theorem t_two_mul_le_of_restricted_root {m q j : ℕ} (hm : 0 < m) (hj : 0 < j)
    (hroot : q ∣ j * (m * j + 1)) :
    t 2 (m * q) ≤ m * j := by
  apply t_min (mul_pos hm hj)
  rw [consecutiveProduct_two]
  obtain ⟨w, hw⟩ := hroot
  refine ⟨w, ?_⟩
  calc
    m * j * (m * j + 1) = m * (j * (m * j + 1)) := by ring
    _ = m * (q * w) := by rw [hw]
    _ = m * q * w := by ring

end Erdos394
