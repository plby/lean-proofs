import Wikipedia.NoExoticSixSphere.RankSixSkewMatrix
import Mathlib.Data.Complex.Basic

/-!
# The explicit four-dimensional spin matrix of a skew-six matrix

The Hermitian, trace-zero matrix below depends linearly on the fifteen real
skew coordinates. Its quadratic identity is checked entry by entry and
relates it to the explicit Pfaffian cofactor matrix.
-/

namespace NoExoticSixSphere.RankSixSkewMatrix

abbrev Matrix4 := Matrix (Fin 4) (Fin 4) ℂ

def spin (A : Matrix6) : Matrix4 :=
  !![⟨-A 0 1 - A 2 3 - A 4 5, 0⟩,
      ⟨-A 0 3 - A 1 2, -A 0 2 + A 1 3⟩,
      ⟨-A 0 5 - A 1 4, -A 0 4 + A 1 5⟩,
      ⟨-A 2 5 - A 3 4, -A 2 4 + A 3 5⟩;
     ⟨-A 0 3 - A 1 2, A 0 2 - A 1 3⟩,
      ⟨A 0 1 + A 2 3 - A 4 5, 0⟩,
      ⟨A 2 5 - A 3 4, A 2 4 + A 3 5⟩,
      ⟨-A 0 5 + A 1 4, -A 0 4 - A 1 5⟩;
     ⟨-A 0 5 - A 1 4, A 0 4 - A 1 5⟩,
      ⟨A 2 5 - A 3 4, -A 2 4 - A 3 5⟩,
      ⟨A 0 1 - A 2 3 + A 4 5, 0⟩,
      ⟨A 0 3 - A 1 2, A 0 2 + A 1 3⟩;
     ⟨-A 2 5 - A 3 4, A 2 4 - A 3 5⟩,
      ⟨-A 0 5 + A 1 4, A 0 4 + A 1 5⟩,
      ⟨A 0 3 - A 1 2, -A 0 2 - A 1 3⟩,
      ⟨-A 0 1 + A 2 3 + A 4 5, 0⟩]

theorem spin_hermitian (A : Matrix6) : (spin A).conjTranspose = spin A := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · apply Complex.ext
    · change (-A 0 1 - A 2 3 - A 4 5) = (-A 0 1 - A 2 3 - A 4 5)
      ring
    · change -(0) = (0)
      ring
  · apply Complex.ext
    · change (-A 0 3 - A 1 2) = (-A 0 3 - A 1 2)
      ring
    · change -(A 0 2 - A 1 3) = (-A 0 2 + A 1 3)
      ring
  · apply Complex.ext
    · change (-A 0 5 - A 1 4) = (-A 0 5 - A 1 4)
      ring
    · change -(A 0 4 - A 1 5) = (-A 0 4 + A 1 5)
      ring
  · apply Complex.ext
    · change (-A 2 5 - A 3 4) = (-A 2 5 - A 3 4)
      ring
    · change -(A 2 4 - A 3 5) = (-A 2 4 + A 3 5)
      ring
  · apply Complex.ext
    · change (-A 0 3 - A 1 2) = (-A 0 3 - A 1 2)
      ring
    · change -(-A 0 2 + A 1 3) = (A 0 2 - A 1 3)
      ring
  · apply Complex.ext
    · change (A 0 1 + A 2 3 - A 4 5) = (A 0 1 + A 2 3 - A 4 5)
      ring
    · change -(0) = (0)
      ring
  · apply Complex.ext
    · change (A 2 5 - A 3 4) = (A 2 5 - A 3 4)
      ring
    · change -(-A 2 4 - A 3 5) = (A 2 4 + A 3 5)
      ring
  · apply Complex.ext
    · change (-A 0 5 + A 1 4) = (-A 0 5 + A 1 4)
      ring
    · change -(A 0 4 + A 1 5) = (-A 0 4 - A 1 5)
      ring
  · apply Complex.ext
    · change (-A 0 5 - A 1 4) = (-A 0 5 - A 1 4)
      ring
    · change -(-A 0 4 + A 1 5) = (A 0 4 - A 1 5)
      ring
  · apply Complex.ext
    · change (A 2 5 - A 3 4) = (A 2 5 - A 3 4)
      ring
    · change -(A 2 4 + A 3 5) = (-A 2 4 - A 3 5)
      ring
  · apply Complex.ext
    · change (A 0 1 - A 2 3 + A 4 5) = (A 0 1 - A 2 3 + A 4 5)
      ring
    · change -(0) = (0)
      ring
  · apply Complex.ext
    · change (A 0 3 - A 1 2) = (A 0 3 - A 1 2)
      ring
    · change -(-A 0 2 - A 1 3) = (A 0 2 + A 1 3)
      ring
  · apply Complex.ext
    · change (-A 2 5 - A 3 4) = (-A 2 5 - A 3 4)
      ring
    · change -(-A 2 4 + A 3 5) = (A 2 4 - A 3 5)
      ring
  · apply Complex.ext
    · change (-A 0 5 + A 1 4) = (-A 0 5 + A 1 4)
      ring
    · change -(-A 0 4 - A 1 5) = (A 0 4 + A 1 5)
      ring
  · apply Complex.ext
    · change (A 0 3 - A 1 2) = (A 0 3 - A 1 2)
      ring
    · change -(A 0 2 + A 1 3) = (-A 0 2 - A 1 3)
      ring
  · apply Complex.ext
    · change (-A 0 1 + A 2 3 + A 4 5) = (-A 0 1 + A 2 3 + A 4 5)
      ring
    · change -(0) = (0)
      ring

theorem sum_four {R : Type*} [AddCommMonoid R] (f : Fin 4 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + 0))) = _
  simp only [add_zero, add_assoc]

theorem spin_trace (A : Matrix6) : (spin A).trace = 0 := by
  simp only [Matrix.trace, Matrix.diag_apply, sum_four]
  apply Complex.ext
  · change
      (-A 0 1 - A 2 3 - A 4 5) + (A 0 1 + A 2 3 - A 4 5) + (A 0 1 - A 2 3 + A 4 5) + (-A 0 1 + A 2
      3 + A 4 5) = 0
    ring
  · change (0 : ℝ) + 0 + 0 + 0 = 0
    ring

theorem spin_real_smul (c : ℝ) (A : Matrix6) : spin (c • A) = (c : ℂ) • spin A := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · apply Complex.ext
    · change
        (-(c * A 0 1) - (c * A 2 3) - (c * A 4 5)) = c * (-A 0 1 - A 2 3 - A 4 5) - 0 * (0)
      ring
    · change
        (0) = c * (0) + 0 * (-A 0 1 - A 2 3 - A 4 5)
      ring
  · apply Complex.ext
    · change
        (-(c * A 0 3) - (c * A 1 2)) = c * (-A 0 3 - A 1 2) - 0 * (-A 0 2 + A 1 3)
      ring
    · change
        (-(c * A 0 2) + (c * A 1 3)) = c * (-A 0 2 + A 1 3) + 0 * (-A 0 3 - A 1 2)
      ring
  · apply Complex.ext
    · change
        (-(c * A 0 5) - (c * A 1 4)) = c * (-A 0 5 - A 1 4) - 0 * (-A 0 4 + A 1 5)
      ring
    · change
        (-(c * A 0 4) + (c * A 1 5)) = c * (-A 0 4 + A 1 5) + 0 * (-A 0 5 - A 1 4)
      ring
  · apply Complex.ext
    · change
        (-(c * A 2 5) - (c * A 3 4)) = c * (-A 2 5 - A 3 4) - 0 * (-A 2 4 + A 3 5)
      ring
    · change
        (-(c * A 2 4) + (c * A 3 5)) = c * (-A 2 4 + A 3 5) + 0 * (-A 2 5 - A 3 4)
      ring
  · apply Complex.ext
    · change
        (-(c * A 0 3) - (c * A 1 2)) = c * (-A 0 3 - A 1 2) - 0 * (A 0 2 - A 1 3)
      ring
    · change
        ((c * A 0 2) - (c * A 1 3)) = c * (A 0 2 - A 1 3) + 0 * (-A 0 3 - A 1 2)
      ring
  · apply Complex.ext
    · change
        ((c * A 0 1) + (c * A 2 3) - (c * A 4 5)) = c * (A 0 1 + A 2 3 - A 4 5) - 0 * (0)
      ring
    · change
        (0) = c * (0) + 0 * (A 0 1 + A 2 3 - A 4 5)
      ring
  · apply Complex.ext
    · change
        ((c * A 2 5) - (c * A 3 4)) = c * (A 2 5 - A 3 4) - 0 * (A 2 4 + A 3 5)
      ring
    · change
        ((c * A 2 4) + (c * A 3 5)) = c * (A 2 4 + A 3 5) + 0 * (A 2 5 - A 3 4)
      ring
  · apply Complex.ext
    · change
        (-(c * A 0 5) + (c * A 1 4)) = c * (-A 0 5 + A 1 4) - 0 * (-A 0 4 - A 1 5)
      ring
    · change
        (-(c * A 0 4) - (c * A 1 5)) = c * (-A 0 4 - A 1 5) + 0 * (-A 0 5 + A 1 4)
      ring
  · apply Complex.ext
    · change
        (-(c * A 0 5) - (c * A 1 4)) = c * (-A 0 5 - A 1 4) - 0 * (A 0 4 - A 1 5)
      ring
    · change
        ((c * A 0 4) - (c * A 1 5)) = c * (A 0 4 - A 1 5) + 0 * (-A 0 5 - A 1 4)
      ring
  · apply Complex.ext
    · change
        ((c * A 2 5) - (c * A 3 4)) = c * (A 2 5 - A 3 4) - 0 * (-A 2 4 - A 3 5)
      ring
    · change
        (-(c * A 2 4) - (c * A 3 5)) = c * (-A 2 4 - A 3 5) + 0 * (A 2 5 - A 3 4)
      ring
  · apply Complex.ext
    · change
        ((c * A 0 1) - (c * A 2 3) + (c * A 4 5)) = c * (A 0 1 - A 2 3 + A 4 5) - 0 * (0)
      ring
    · change
        (0) = c * (0) + 0 * (A 0 1 - A 2 3 + A 4 5)
      ring
  · apply Complex.ext
    · change
        ((c * A 0 3) - (c * A 1 2)) = c * (A 0 3 - A 1 2) - 0 * (A 0 2 + A 1 3)
      ring
    · change
        ((c * A 0 2) + (c * A 1 3)) = c * (A 0 2 + A 1 3) + 0 * (A 0 3 - A 1 2)
      ring
  · apply Complex.ext
    · change
        (-(c * A 2 5) - (c * A 3 4)) = c * (-A 2 5 - A 3 4) - 0 * (A 2 4 - A 3 5)
      ring
    · change
        ((c * A 2 4) - (c * A 3 5)) = c * (A 2 4 - A 3 5) + 0 * (-A 2 5 - A 3 4)
      ring
  · apply Complex.ext
    · change
        (-(c * A 0 5) + (c * A 1 4)) = c * (-A 0 5 + A 1 4) - 0 * (A 0 4 + A 1 5)
      ring
    · change
        ((c * A 0 4) + (c * A 1 5)) = c * (A 0 4 + A 1 5) + 0 * (-A 0 5 + A 1 4)
      ring
  · apply Complex.ext
    · change
        ((c * A 0 3) - (c * A 1 2)) = c * (A 0 3 - A 1 2) - 0 * (-A 0 2 - A 1 3)
      ring
    · change
        (-(c * A 0 2) - (c * A 1 3)) = c * (-A 0 2 - A 1 3) + 0 * (A 0 3 - A 1 2)
      ring
  · apply Complex.ext
    · change
        (-(c * A 0 1) + (c * A 2 3) + (c * A 4 5)) = c * (-A 0 1 + A 2 3 + A 4 5) - 0 * (0)
      ring
    · change
        (0) = c * (0) + 0 * (-A 0 1 + A 2 3 + A 4 5)
      ring

theorem spin_square_row0 (A : Matrix6) (j : Fin 4) :
    (spin A * spin A) 0 j =
      ((energy A : ℂ) • (1 : Matrix4) + (2 : ℂ) • spin (coPfaffian A)) 0 j := by
  fin_cases j
  · simp only [Matrix.mul_apply, sum_four]
    apply Complex.ext
    · change
        ((-A 0 1 - A 2 3 - A 4 5) * (-A 0 1 - A 2 3 - A 4 5) - (0) * (0)) + ((-A 0 3 - A 1 2) *
        (-A 0 3 - A 1 2) - (-A 0 2 + A 1 3) * (A 0 2 - A 1 3)) + ((-A 0 5 - A 1 4) * (-A 0 5 - A 1
        4) - (-A 0 4 + A 1 5) * (A 0 4 - A 1 5)) + ((-A 2 5 - A 3 4) * (-A 2 5 - A 3 4) - (-A 2 4
        + A 3 5) * (A 2 4 - A 3 5)) = (energy A * 1 - 0 * 0) + (2 * (-(-A 2 3 * A 4 5 + A 2 4 * A
        3 5 - A 2 5 * A 3 4) - (-A 0 1 * A 4 5 + A 0 4 * A 1 5 - A 0 5 * A 1 4) - (-A 0 1 * A 2 3
        + A 0 2 * A 1 3 - A 0 3 * A 1 2)) - 0 * (0))
      dsimp only [energy]
      ring
    · change
        ((-A 0 1 - A 2 3 - A 4 5) * (0) + (0) * (-A 0 1 - A 2 3 - A 4 5)) + ((-A 0 3 - A 1 2) * (A
        0 2 - A 1 3) + (-A 0 2 + A 1 3) * (-A 0 3 - A 1 2)) + ((-A 0 5 - A 1 4) * (A 0 4 - A 1 5)
        + (-A 0 4 + A 1 5) * (-A 0 5 - A 1 4)) + ((-A 2 5 - A 3 4) * (A 2 4 - A 3 5) + (-A 2 4 + A
        3 5) * (-A 2 5 - A 3 4)) = (energy A * 0 + 0 * 1) + (2 * (0) + 0 * (-(-A 2 3 * A 4 5 + A 2
        4 * A 3 5 - A 2 5 * A 3 4) - (-A 0 1 * A 4 5 + A 0 4 * A 1 5 - A 0 5 * A 1 4) - (-A 0 1 *
        A 2 3 + A 0 2 * A 1 3 - A 0 3 * A 1 2)))
      ring
  · simp only [Matrix.mul_apply, sum_four]
    apply Complex.ext
    · change
        ((-A 0 1 - A 2 3 - A 4 5) * (-A 0 3 - A 1 2) - (0) * (-A 0 2 + A 1 3)) + ((-A 0 3 - A 1 2)
        * (A 0 1 + A 2 3 - A 4 5) - (-A 0 2 + A 1 3) * (0)) + ((-A 0 5 - A 1 4) * (A 2 5 - A 3 4)
        - (-A 0 4 + A 1 5) * (-A 2 4 - A 3 5)) + ((-A 2 5 - A 3 4) * (-A 0 5 + A 1 4) - (-A 2 4 +
        A 3 5) * (A 0 4 + A 1 5)) = (energy A * 0 - 0 * 0) + (2 * (-(-A 1 2 * A 4 5 + A 1 4 * A 2
        5 - A 1 5 * A 2 4) - (-A 0 3 * A 4 5 + A 0 4 * A 3 5 - A 0 5 * A 3 4)) - 0 * (-(A 1 3 * A
        4 5 - A 1 4 * A 3 5 + A 1 5 * A 3 4) + (A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4)))
      dsimp only [energy]
      ring
    · change
        ((-A 0 1 - A 2 3 - A 4 5) * (-A 0 2 + A 1 3) + (0) * (-A 0 3 - A 1 2)) + ((-A 0 3 - A 1 2)
        * (0) + (-A 0 2 + A 1 3) * (A 0 1 + A 2 3 - A 4 5)) + ((-A 0 5 - A 1 4) * (-A 2 4 - A 3 5)
        + (-A 0 4 + A 1 5) * (A 2 5 - A 3 4)) + ((-A 2 5 - A 3 4) * (A 0 4 + A 1 5) + (-A 2 4 + A
        3 5) * (-A 0 5 + A 1 4)) = (energy A * 0 + 0 * 0) + (2 * (-(A 1 3 * A 4 5 - A 1 4 * A 3 5
        + A 1 5 * A 3 4) + (A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4)) + 0 * (-(-A 1 2 * A 4
        5 + A 1 4 * A 2 5 - A 1 5 * A 2 4) - (-A 0 3 * A 4 5 + A 0 4 * A 3 5 - A 0 5 * A 3 4)))
      ring
  · simp only [Matrix.mul_apply, sum_four]
    apply Complex.ext
    · change
        ((-A 0 1 - A 2 3 - A 4 5) * (-A 0 5 - A 1 4) - (0) * (-A 0 4 + A 1 5)) + ((-A 0 3 - A 1 2)
        * (A 2 5 - A 3 4) - (-A 0 2 + A 1 3) * (A 2 4 + A 3 5)) + ((-A 0 5 - A 1 4) * (A 0 1 - A 2
        3 + A 4 5) - (-A 0 4 + A 1 5) * (0)) + ((-A 2 5 - A 3 4) * (A 0 3 - A 1 2) - (-A 2 4 + A 3
        5) * (-A 0 2 - A 1 3)) = (energy A * 0 - 0 * 0) + (2 * (-(-A 1 2 * A 3 4 + A 1 3 * A 2 4 -
        A 1 4 * A 2 3) - (-A 0 2 * A 3 5 + A 0 3 * A 2 5 - A 0 5 * A 2 3)) - 0 * (-(A 1 2 * A 3 5
        - A 1 3 * A 2 5 + A 1 5 * A 2 3) + (A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3)))
      dsimp only [energy]
      ring
    · change
        ((-A 0 1 - A 2 3 - A 4 5) * (-A 0 4 + A 1 5) + (0) * (-A 0 5 - A 1 4)) + ((-A 0 3 - A 1 2)
        * (A 2 4 + A 3 5) + (-A 0 2 + A 1 3) * (A 2 5 - A 3 4)) + ((-A 0 5 - A 1 4) * (0) + (-A 0
        4 + A 1 5) * (A 0 1 - A 2 3 + A 4 5)) + ((-A 2 5 - A 3 4) * (-A 0 2 - A 1 3) + (-A 2 4 + A
        3 5) * (A 0 3 - A 1 2)) = (energy A * 0 + 0 * 0) + (2 * (-(A 1 2 * A 3 5 - A 1 3 * A 2 5 +
        A 1 5 * A 2 3) + (A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3)) + 0 * (-(-A 1 2 * A 3 4
        + A 1 3 * A 2 4 - A 1 4 * A 2 3) - (-A 0 2 * A 3 5 + A 0 3 * A 2 5 - A 0 5 * A 2 3)))
      ring
  · simp only [Matrix.mul_apply, sum_four]
    apply Complex.ext
    · change
        ((-A 0 1 - A 2 3 - A 4 5) * (-A 2 5 - A 3 4) - (0) * (-A 2 4 + A 3 5)) + ((-A 0 3 - A 1 2)
        * (-A 0 5 + A 1 4) - (-A 0 2 + A 1 3) * (-A 0 4 - A 1 5)) + ((-A 0 5 - A 1 4) * (A 0 3 - A
        1 2) - (-A 0 4 + A 1 5) * (A 0 2 + A 1 3)) + ((-A 2 5 - A 3 4) * (-A 0 1 + A 2 3 + A 4 5)
        - (-A 2 4 + A 3 5) * (0)) = (energy A * 0 - 0 * 0) + (2 * (-(-A 0 1 * A 3 4 + A 0 3 * A 1
        4 - A 0 4 * A 1 3) - (-A 0 1 * A 2 5 + A 0 2 * A 1 5 - A 0 5 * A 1 2)) - 0 * (-(A 0 1 * A
        3 5 - A 0 3 * A 1 5 + A 0 5 * A 1 3) + (A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2)))
      dsimp only [energy]
      ring
    · change
        ((-A 0 1 - A 2 3 - A 4 5) * (-A 2 4 + A 3 5) + (0) * (-A 2 5 - A 3 4)) + ((-A 0 3 - A 1 2)
        * (-A 0 4 - A 1 5) + (-A 0 2 + A 1 3) * (-A 0 5 + A 1 4)) + ((-A 0 5 - A 1 4) * (A 0 2 + A
        1 3) + (-A 0 4 + A 1 5) * (A 0 3 - A 1 2)) + ((-A 2 5 - A 3 4) * (0) + (-A 2 4 + A 3 5) *
        (-A 0 1 + A 2 3 + A 4 5)) = (energy A * 0 + 0 * 0) + (2 * (-(A 0 1 * A 3 5 - A 0 3 * A 1 5
        + A 0 5 * A 1 3) + (A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2)) + 0 * (-(-A 0 1 * A 3
        4 + A 0 3 * A 1 4 - A 0 4 * A 1 3) - (-A 0 1 * A 2 5 + A 0 2 * A 1 5 - A 0 5 * A 1 2)))
      ring

theorem spin_square_row1 (A : Matrix6) (j : Fin 4) :
    (spin A * spin A) 1 j =
      ((energy A : ℂ) • (1 : Matrix4) + (2 : ℂ) • spin (coPfaffian A)) 1 j := by
  fin_cases j
  · simp only [Matrix.mul_apply, sum_four]
    apply Complex.ext
    · change
        ((-A 0 3 - A 1 2) * (-A 0 1 - A 2 3 - A 4 5) - (A 0 2 - A 1 3) * (0)) + ((A 0 1 + A 2 3 -
        A 4 5) * (-A 0 3 - A 1 2) - (0) * (A 0 2 - A 1 3)) + ((A 2 5 - A 3 4) * (-A 0 5 - A 1 4) -
        (A 2 4 + A 3 5) * (A 0 4 - A 1 5)) + ((-A 0 5 + A 1 4) * (-A 2 5 - A 3 4) - (-A 0 4 - A 1
        5) * (A 2 4 - A 3 5)) = (energy A * 0 - 0 * 0) + (2 * (-(-A 1 2 * A 4 5 + A 1 4 * A 2 5 -
        A 1 5 * A 2 4) - (-A 0 3 * A 4 5 + A 0 4 * A 3 5 - A 0 5 * A 3 4)) - 0 * ((A 1 3 * A 4 5 -
        A 1 4 * A 3 5 + A 1 5 * A 3 4) - (A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4)))
      dsimp only [energy]
      ring
    · change
        ((-A 0 3 - A 1 2) * (0) + (A 0 2 - A 1 3) * (-A 0 1 - A 2 3 - A 4 5)) + ((A 0 1 + A 2 3 -
        A 4 5) * (A 0 2 - A 1 3) + (0) * (-A 0 3 - A 1 2)) + ((A 2 5 - A 3 4) * (A 0 4 - A 1 5) +
        (A 2 4 + A 3 5) * (-A 0 5 - A 1 4)) + ((-A 0 5 + A 1 4) * (A 2 4 - A 3 5) + (-A 0 4 - A 1
        5) * (-A 2 5 - A 3 4)) = (energy A * 0 + 0 * 0) + (2 * ((A 1 3 * A 4 5 - A 1 4 * A 3 5 + A
        1 5 * A 3 4) - (A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4)) + 0 * (-(-A 1 2 * A 4 5 +
        A 1 4 * A 2 5 - A 1 5 * A 2 4) - (-A 0 3 * A 4 5 + A 0 4 * A 3 5 - A 0 5 * A 3 4)))
      ring
  · simp only [Matrix.mul_apply, sum_four]
    apply Complex.ext
    · change
        ((-A 0 3 - A 1 2) * (-A 0 3 - A 1 2) - (A 0 2 - A 1 3) * (-A 0 2 + A 1 3)) + ((A 0 1 + A 2
        3 - A 4 5) * (A 0 1 + A 2 3 - A 4 5) - (0) * (0)) + ((A 2 5 - A 3 4) * (A 2 5 - A 3 4) -
        (A 2 4 + A 3 5) * (-A 2 4 - A 3 5)) + ((-A 0 5 + A 1 4) * (-A 0 5 + A 1 4) - (-A 0 4 - A 1
        5) * (A 0 4 + A 1 5)) = (energy A * 1 - 0 * 0) + (2 * ((-A 2 3 * A 4 5 + A 2 4 * A 3 5 - A
        2 5 * A 3 4) + (-A 0 1 * A 4 5 + A 0 4 * A 1 5 - A 0 5 * A 1 4) - (-A 0 1 * A 2 3 + A 0 2
        * A 1 3 - A 0 3 * A 1 2)) - 0 * (0))
      dsimp only [energy]
      ring
    · change
        ((-A 0 3 - A 1 2) * (-A 0 2 + A 1 3) + (A 0 2 - A 1 3) * (-A 0 3 - A 1 2)) + ((A 0 1 + A 2
        3 - A 4 5) * (0) + (0) * (A 0 1 + A 2 3 - A 4 5)) + ((A 2 5 - A 3 4) * (-A 2 4 - A 3 5) +
        (A 2 4 + A 3 5) * (A 2 5 - A 3 4)) + ((-A 0 5 + A 1 4) * (A 0 4 + A 1 5) + (-A 0 4 - A 1
        5) * (-A 0 5 + A 1 4)) = (energy A * 0 + 0 * 1) + (2 * (0) + 0 * ((-A 2 3 * A 4 5 + A 2 4
        * A 3 5 - A 2 5 * A 3 4) + (-A 0 1 * A 4 5 + A 0 4 * A 1 5 - A 0 5 * A 1 4) - (-A 0 1 * A
        2 3 + A 0 2 * A 1 3 - A 0 3 * A 1 2)))
      ring
  · simp only [Matrix.mul_apply, sum_four]
    apply Complex.ext
    · change
        ((-A 0 3 - A 1 2) * (-A 0 5 - A 1 4) - (A 0 2 - A 1 3) * (-A 0 4 + A 1 5)) + ((A 0 1 + A 2
        3 - A 4 5) * (A 2 5 - A 3 4) - (0) * (A 2 4 + A 3 5)) + ((A 2 5 - A 3 4) * (A 0 1 - A 2 3
        + A 4 5) - (A 2 4 + A 3 5) * (0)) + ((-A 0 5 + A 1 4) * (A 0 3 - A 1 2) - (-A 0 4 - A 1 5)
        * (-A 0 2 - A 1 3)) = (energy A * 0 - 0 * 0) + (2 * ((-A 0 1 * A 3 4 + A 0 3 * A 1 4 - A 0
        4 * A 1 3) - (-A 0 1 * A 2 5 + A 0 2 * A 1 5 - A 0 5 * A 1 2)) - 0 * ((A 0 1 * A 3 5 - A 0
        3 * A 1 5 + A 0 5 * A 1 3) + (A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2)))
      dsimp only [energy]
      ring
    · change
        ((-A 0 3 - A 1 2) * (-A 0 4 + A 1 5) + (A 0 2 - A 1 3) * (-A 0 5 - A 1 4)) + ((A 0 1 + A 2
        3 - A 4 5) * (A 2 4 + A 3 5) + (0) * (A 2 5 - A 3 4)) + ((A 2 5 - A 3 4) * (0) + (A 2 4 +
        A 3 5) * (A 0 1 - A 2 3 + A 4 5)) + ((-A 0 5 + A 1 4) * (-A 0 2 - A 1 3) + (-A 0 4 - A 1
        5) * (A 0 3 - A 1 2)) = (energy A * 0 + 0 * 0) + (2 * ((A 0 1 * A 3 5 - A 0 3 * A 1 5 + A
        0 5 * A 1 3) + (A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2)) + 0 * ((-A 0 1 * A 3 4 + A
        0 3 * A 1 4 - A 0 4 * A 1 3) - (-A 0 1 * A 2 5 + A 0 2 * A 1 5 - A 0 5 * A 1 2)))
      ring
  · simp only [Matrix.mul_apply, sum_four]
    apply Complex.ext
    · change
        ((-A 0 3 - A 1 2) * (-A 2 5 - A 3 4) - (A 0 2 - A 1 3) * (-A 2 4 + A 3 5)) + ((A 0 1 + A 2
        3 - A 4 5) * (-A 0 5 + A 1 4) - (0) * (-A 0 4 - A 1 5)) + ((A 2 5 - A 3 4) * (A 0 3 - A 1
        2) - (A 2 4 + A 3 5) * (A 0 2 + A 1 3)) + ((-A 0 5 + A 1 4) * (-A 0 1 + A 2 3 + A 4 5) -
        (-A 0 4 - A 1 5) * (0)) = (energy A * 0 - 0 * 0) + (2 * (-(-A 1 2 * A 3 4 + A 1 3 * A 2 4
        - A 1 4 * A 2 3) + (-A 0 2 * A 3 5 + A 0 3 * A 2 5 - A 0 5 * A 2 3)) - 0 * (-(A 1 2 * A 3
        5 - A 1 3 * A 2 5 + A 1 5 * A 2 3) - (A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3)))
      dsimp only [energy]
      ring
    · change
        ((-A 0 3 - A 1 2) * (-A 2 4 + A 3 5) + (A 0 2 - A 1 3) * (-A 2 5 - A 3 4)) + ((A 0 1 + A 2
        3 - A 4 5) * (-A 0 4 - A 1 5) + (0) * (-A 0 5 + A 1 4)) + ((A 2 5 - A 3 4) * (A 0 2 + A 1
        3) + (A 2 4 + A 3 5) * (A 0 3 - A 1 2)) + ((-A 0 5 + A 1 4) * (0) + (-A 0 4 - A 1 5) * (-A
        0 1 + A 2 3 + A 4 5)) = (energy A * 0 + 0 * 0) + (2 * (-(A 1 2 * A 3 5 - A 1 3 * A 2 5 + A
        1 5 * A 2 3) - (A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3)) + 0 * (-(-A 1 2 * A 3 4 +
        A 1 3 * A 2 4 - A 1 4 * A 2 3) + (-A 0 2 * A 3 5 + A 0 3 * A 2 5 - A 0 5 * A 2 3)))
      ring

theorem spin_square_row2 (A : Matrix6) (j : Fin 4) :
    (spin A * spin A) 2 j =
      ((energy A : ℂ) • (1 : Matrix4) + (2 : ℂ) • spin (coPfaffian A)) 2 j := by
  fin_cases j
  · simp only [Matrix.mul_apply, sum_four]
    apply Complex.ext
    · change
        ((-A 0 5 - A 1 4) * (-A 0 1 - A 2 3 - A 4 5) - (A 0 4 - A 1 5) * (0)) + ((A 2 5 - A 3 4) *
        (-A 0 3 - A 1 2) - (-A 2 4 - A 3 5) * (A 0 2 - A 1 3)) + ((A 0 1 - A 2 3 + A 4 5) * (-A 0
        5 - A 1 4) - (0) * (A 0 4 - A 1 5)) + ((A 0 3 - A 1 2) * (-A 2 5 - A 3 4) - (A 0 2 + A 1
        3) * (A 2 4 - A 3 5)) = (energy A * 0 - 0 * 0) + (2 * (-(-A 1 2 * A 3 4 + A 1 3 * A 2 4 -
        A 1 4 * A 2 3) - (-A 0 2 * A 3 5 + A 0 3 * A 2 5 - A 0 5 * A 2 3)) - 0 * ((A 1 2 * A 3 5 -
        A 1 3 * A 2 5 + A 1 5 * A 2 3) - (A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3)))
      dsimp only [energy]
      ring
    · change
        ((-A 0 5 - A 1 4) * (0) + (A 0 4 - A 1 5) * (-A 0 1 - A 2 3 - A 4 5)) + ((A 2 5 - A 3 4) *
        (A 0 2 - A 1 3) + (-A 2 4 - A 3 5) * (-A 0 3 - A 1 2)) + ((A 0 1 - A 2 3 + A 4 5) * (A 0 4
        - A 1 5) + (0) * (-A 0 5 - A 1 4)) + ((A 0 3 - A 1 2) * (A 2 4 - A 3 5) + (A 0 2 + A 1 3)
        * (-A 2 5 - A 3 4)) = (energy A * 0 + 0 * 0) + (2 * ((A 1 2 * A 3 5 - A 1 3 * A 2 5 + A 1
        5 * A 2 3) - (A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3)) + 0 * (-(-A 1 2 * A 3 4 + A
        1 3 * A 2 4 - A 1 4 * A 2 3) - (-A 0 2 * A 3 5 + A 0 3 * A 2 5 - A 0 5 * A 2 3)))
      ring
  · simp only [Matrix.mul_apply, sum_four]
    apply Complex.ext
    · change
        ((-A 0 5 - A 1 4) * (-A 0 3 - A 1 2) - (A 0 4 - A 1 5) * (-A 0 2 + A 1 3)) + ((A 2 5 - A 3
        4) * (A 0 1 + A 2 3 - A 4 5) - (-A 2 4 - A 3 5) * (0)) + ((A 0 1 - A 2 3 + A 4 5) * (A 2 5
        - A 3 4) - (0) * (-A 2 4 - A 3 5)) + ((A 0 3 - A 1 2) * (-A 0 5 + A 1 4) - (A 0 2 + A 1 3)
        * (A 0 4 + A 1 5)) = (energy A * 0 - 0 * 0) + (2 * ((-A 0 1 * A 3 4 + A 0 3 * A 1 4 - A 0
        4 * A 1 3) - (-A 0 1 * A 2 5 + A 0 2 * A 1 5 - A 0 5 * A 1 2)) - 0 * (-(A 0 1 * A 3 5 - A
        0 3 * A 1 5 + A 0 5 * A 1 3) - (A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2)))
      dsimp only [energy]
      ring
    · change
        ((-A 0 5 - A 1 4) * (-A 0 2 + A 1 3) + (A 0 4 - A 1 5) * (-A 0 3 - A 1 2)) + ((A 2 5 - A 3
        4) * (0) + (-A 2 4 - A 3 5) * (A 0 1 + A 2 3 - A 4 5)) + ((A 0 1 - A 2 3 + A 4 5) * (-A 2
        4 - A 3 5) + (0) * (A 2 5 - A 3 4)) + ((A 0 3 - A 1 2) * (A 0 4 + A 1 5) + (A 0 2 + A 1 3)
        * (-A 0 5 + A 1 4)) = (energy A * 0 + 0 * 0) + (2 * (-(A 0 1 * A 3 5 - A 0 3 * A 1 5 + A 0
        5 * A 1 3) - (A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2)) + 0 * ((-A 0 1 * A 3 4 + A 0
        3 * A 1 4 - A 0 4 * A 1 3) - (-A 0 1 * A 2 5 + A 0 2 * A 1 5 - A 0 5 * A 1 2)))
      ring
  · simp only [Matrix.mul_apply, sum_four]
    apply Complex.ext
    · change
        ((-A 0 5 - A 1 4) * (-A 0 5 - A 1 4) - (A 0 4 - A 1 5) * (-A 0 4 + A 1 5)) + ((A 2 5 - A 3
        4) * (A 2 5 - A 3 4) - (-A 2 4 - A 3 5) * (A 2 4 + A 3 5)) + ((A 0 1 - A 2 3 + A 4 5) * (A
        0 1 - A 2 3 + A 4 5) - (0) * (0)) + ((A 0 3 - A 1 2) * (A 0 3 - A 1 2) - (A 0 2 + A 1 3) *
        (-A 0 2 - A 1 3)) = (energy A * 1 - 0 * 0) + (2 * ((-A 2 3 * A 4 5 + A 2 4 * A 3 5 - A 2 5
        * A 3 4) - (-A 0 1 * A 4 5 + A 0 4 * A 1 5 - A 0 5 * A 1 4) + (-A 0 1 * A 2 3 + A 0 2 * A
        1 3 - A 0 3 * A 1 2)) - 0 * (0))
      dsimp only [energy]
      ring
    · change
        ((-A 0 5 - A 1 4) * (-A 0 4 + A 1 5) + (A 0 4 - A 1 5) * (-A 0 5 - A 1 4)) + ((A 2 5 - A 3
        4) * (A 2 4 + A 3 5) + (-A 2 4 - A 3 5) * (A 2 5 - A 3 4)) + ((A 0 1 - A 2 3 + A 4 5) *
        (0) + (0) * (A 0 1 - A 2 3 + A 4 5)) + ((A 0 3 - A 1 2) * (-A 0 2 - A 1 3) + (A 0 2 + A 1
        3) * (A 0 3 - A 1 2)) = (energy A * 0 + 0 * 1) + (2 * (0) + 0 * ((-A 2 3 * A 4 5 + A 2 4 *
        A 3 5 - A 2 5 * A 3 4) - (-A 0 1 * A 4 5 + A 0 4 * A 1 5 - A 0 5 * A 1 4) + (-A 0 1 * A 2
        3 + A 0 2 * A 1 3 - A 0 3 * A 1 2)))
      ring
  · simp only [Matrix.mul_apply, sum_four]
    apply Complex.ext
    · change
        ((-A 0 5 - A 1 4) * (-A 2 5 - A 3 4) - (A 0 4 - A 1 5) * (-A 2 4 + A 3 5)) + ((A 2 5 - A 3
        4) * (-A 0 5 + A 1 4) - (-A 2 4 - A 3 5) * (-A 0 4 - A 1 5)) + ((A 0 1 - A 2 3 + A 4 5) *
        (A 0 3 - A 1 2) - (0) * (A 0 2 + A 1 3)) + ((A 0 3 - A 1 2) * (-A 0 1 + A 2 3 + A 4 5) -
        (A 0 2 + A 1 3) * (0)) = (energy A * 0 - 0 * 0) + (2 * ((-A 1 2 * A 4 5 + A 1 4 * A 2 5 -
        A 1 5 * A 2 4) - (-A 0 3 * A 4 5 + A 0 4 * A 3 5 - A 0 5 * A 3 4)) - 0 * ((A 1 3 * A 4 5 -
        A 1 4 * A 3 5 + A 1 5 * A 3 4) + (A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4)))
      dsimp only [energy]
      ring
    · change
        ((-A 0 5 - A 1 4) * (-A 2 4 + A 3 5) + (A 0 4 - A 1 5) * (-A 2 5 - A 3 4)) + ((A 2 5 - A 3
        4) * (-A 0 4 - A 1 5) + (-A 2 4 - A 3 5) * (-A 0 5 + A 1 4)) + ((A 0 1 - A 2 3 + A 4 5) *
        (A 0 2 + A 1 3) + (0) * (A 0 3 - A 1 2)) + ((A 0 3 - A 1 2) * (0) + (A 0 2 + A 1 3) * (-A
        0 1 + A 2 3 + A 4 5)) = (energy A * 0 + 0 * 0) + (2 * ((A 1 3 * A 4 5 - A 1 4 * A 3 5 + A
        1 5 * A 3 4) + (A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4)) + 0 * ((-A 1 2 * A 4 5 + A
        1 4 * A 2 5 - A 1 5 * A 2 4) - (-A 0 3 * A 4 5 + A 0 4 * A 3 5 - A 0 5 * A 3 4)))
      ring

theorem spin_square_row3 (A : Matrix6) (j : Fin 4) :
    (spin A * spin A) 3 j =
      ((energy A : ℂ) • (1 : Matrix4) + (2 : ℂ) • spin (coPfaffian A)) 3 j := by
  fin_cases j
  · simp only [Matrix.mul_apply, sum_four]
    apply Complex.ext
    · change
        ((-A 2 5 - A 3 4) * (-A 0 1 - A 2 3 - A 4 5) - (A 2 4 - A 3 5) * (0)) + ((-A 0 5 + A 1 4)
        * (-A 0 3 - A 1 2) - (A 0 4 + A 1 5) * (A 0 2 - A 1 3)) + ((A 0 3 - A 1 2) * (-A 0 5 - A 1
        4) - (-A 0 2 - A 1 3) * (A 0 4 - A 1 5)) + ((-A 0 1 + A 2 3 + A 4 5) * (-A 2 5 - A 3 4) -
        (0) * (A 2 4 - A 3 5)) = (energy A * 0 - 0 * 0) + (2 * (-(-A 0 1 * A 3 4 + A 0 3 * A 1 4 -
        A 0 4 * A 1 3) - (-A 0 1 * A 2 5 + A 0 2 * A 1 5 - A 0 5 * A 1 2)) - 0 * ((A 0 1 * A 3 5 -
        A 0 3 * A 1 5 + A 0 5 * A 1 3) - (A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2)))
      dsimp only [energy]
      ring
    · change
        ((-A 2 5 - A 3 4) * (0) + (A 2 4 - A 3 5) * (-A 0 1 - A 2 3 - A 4 5)) + ((-A 0 5 + A 1 4)
        * (A 0 2 - A 1 3) + (A 0 4 + A 1 5) * (-A 0 3 - A 1 2)) + ((A 0 3 - A 1 2) * (A 0 4 - A 1
        5) + (-A 0 2 - A 1 3) * (-A 0 5 - A 1 4)) + ((-A 0 1 + A 2 3 + A 4 5) * (A 2 4 - A 3 5) +
        (0) * (-A 2 5 - A 3 4)) = (energy A * 0 + 0 * 0) + (2 * ((A 0 1 * A 3 5 - A 0 3 * A 1 5 +
        A 0 5 * A 1 3) - (A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2)) + 0 * (-(-A 0 1 * A 3 4
        + A 0 3 * A 1 4 - A 0 4 * A 1 3) - (-A 0 1 * A 2 5 + A 0 2 * A 1 5 - A 0 5 * A 1 2)))
      ring
  · simp only [Matrix.mul_apply, sum_four]
    apply Complex.ext
    · change
        ((-A 2 5 - A 3 4) * (-A 0 3 - A 1 2) - (A 2 4 - A 3 5) * (-A 0 2 + A 1 3)) + ((-A 0 5 + A
        1 4) * (A 0 1 + A 2 3 - A 4 5) - (A 0 4 + A 1 5) * (0)) + ((A 0 3 - A 1 2) * (A 2 5 - A 3
        4) - (-A 0 2 - A 1 3) * (-A 2 4 - A 3 5)) + ((-A 0 1 + A 2 3 + A 4 5) * (-A 0 5 + A 1 4) -
        (0) * (A 0 4 + A 1 5)) = (energy A * 0 - 0 * 0) + (2 * (-(-A 1 2 * A 3 4 + A 1 3 * A 2 4 -
        A 1 4 * A 2 3) + (-A 0 2 * A 3 5 + A 0 3 * A 2 5 - A 0 5 * A 2 3)) - 0 * ((A 1 2 * A 3 5 -
        A 1 3 * A 2 5 + A 1 5 * A 2 3) + (A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3)))
      dsimp only [energy]
      ring
    · change
        ((-A 2 5 - A 3 4) * (-A 0 2 + A 1 3) + (A 2 4 - A 3 5) * (-A 0 3 - A 1 2)) + ((-A 0 5 + A
        1 4) * (0) + (A 0 4 + A 1 5) * (A 0 1 + A 2 3 - A 4 5)) + ((A 0 3 - A 1 2) * (-A 2 4 - A 3
        5) + (-A 0 2 - A 1 3) * (A 2 5 - A 3 4)) + ((-A 0 1 + A 2 3 + A 4 5) * (A 0 4 + A 1 5) +
        (0) * (-A 0 5 + A 1 4)) = (energy A * 0 + 0 * 0) + (2 * ((A 1 2 * A 3 5 - A 1 3 * A 2 5 +
        A 1 5 * A 2 3) + (A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3)) + 0 * (-(-A 1 2 * A 3 4
        + A 1 3 * A 2 4 - A 1 4 * A 2 3) + (-A 0 2 * A 3 5 + A 0 3 * A 2 5 - A 0 5 * A 2 3)))
      ring
  · simp only [Matrix.mul_apply, sum_four]
    apply Complex.ext
    · change
        ((-A 2 5 - A 3 4) * (-A 0 5 - A 1 4) - (A 2 4 - A 3 5) * (-A 0 4 + A 1 5)) + ((-A 0 5 + A
        1 4) * (A 2 5 - A 3 4) - (A 0 4 + A 1 5) * (A 2 4 + A 3 5)) + ((A 0 3 - A 1 2) * (A 0 1 -
        A 2 3 + A 4 5) - (-A 0 2 - A 1 3) * (0)) + ((-A 0 1 + A 2 3 + A 4 5) * (A 0 3 - A 1 2) -
        (0) * (-A 0 2 - A 1 3)) = (energy A * 0 - 0 * 0) + (2 * ((-A 1 2 * A 4 5 + A 1 4 * A 2 5 -
        A 1 5 * A 2 4) - (-A 0 3 * A 4 5 + A 0 4 * A 3 5 - A 0 5 * A 3 4)) - 0 * (-(A 1 3 * A 4 5
        - A 1 4 * A 3 5 + A 1 5 * A 3 4) - (A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4)))
      dsimp only [energy]
      ring
    · change
        ((-A 2 5 - A 3 4) * (-A 0 4 + A 1 5) + (A 2 4 - A 3 5) * (-A 0 5 - A 1 4)) + ((-A 0 5 + A
        1 4) * (A 2 4 + A 3 5) + (A 0 4 + A 1 5) * (A 2 5 - A 3 4)) + ((A 0 3 - A 1 2) * (0) + (-A
        0 2 - A 1 3) * (A 0 1 - A 2 3 + A 4 5)) + ((-A 0 1 + A 2 3 + A 4 5) * (-A 0 2 - A 1 3) +
        (0) * (A 0 3 - A 1 2)) = (energy A * 0 + 0 * 0) + (2 * (-(A 1 3 * A 4 5 - A 1 4 * A 3 5 +
        A 1 5 * A 3 4) - (A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4)) + 0 * ((-A 1 2 * A 4 5 +
        A 1 4 * A 2 5 - A 1 5 * A 2 4) - (-A 0 3 * A 4 5 + A 0 4 * A 3 5 - A 0 5 * A 3 4)))
      ring
  · simp only [Matrix.mul_apply, sum_four]
    apply Complex.ext
    · change
        ((-A 2 5 - A 3 4) * (-A 2 5 - A 3 4) - (A 2 4 - A 3 5) * (-A 2 4 + A 3 5)) + ((-A 0 5 + A
        1 4) * (-A 0 5 + A 1 4) - (A 0 4 + A 1 5) * (-A 0 4 - A 1 5)) + ((A 0 3 - A 1 2) * (A 0 3
        - A 1 2) - (-A 0 2 - A 1 3) * (A 0 2 + A 1 3)) + ((-A 0 1 + A 2 3 + A 4 5) * (-A 0 1 + A 2
        3 + A 4 5) - (0) * (0)) = (energy A * 1 - 0 * 0) + (2 * (-(-A 2 3 * A 4 5 + A 2 4 * A 3 5
        - A 2 5 * A 3 4) + (-A 0 1 * A 4 5 + A 0 4 * A 1 5 - A 0 5 * A 1 4) + (-A 0 1 * A 2 3 + A
        0 2 * A 1 3 - A 0 3 * A 1 2)) - 0 * (0))
      dsimp only [energy]
      ring
    · change
        ((-A 2 5 - A 3 4) * (-A 2 4 + A 3 5) + (A 2 4 - A 3 5) * (-A 2 5 - A 3 4)) + ((-A 0 5 + A
        1 4) * (-A 0 4 - A 1 5) + (A 0 4 + A 1 5) * (-A 0 5 + A 1 4)) + ((A 0 3 - A 1 2) * (A 0 2
        + A 1 3) + (-A 0 2 - A 1 3) * (A 0 3 - A 1 2)) + ((-A 0 1 + A 2 3 + A 4 5) * (0) + (0) *
        (-A 0 1 + A 2 3 + A 4 5)) = (energy A * 0 + 0 * 1) + (2 * (0) + 0 * (-(-A 2 3 * A 4 5 + A
        2 4 * A 3 5 - A 2 5 * A 3 4) + (-A 0 1 * A 4 5 + A 0 4 * A 1 5 - A 0 5 * A 1 4) + (-A 0 1
        * A 2 3 + A 0 2 * A 1 3 - A 0 3 * A 1 2)))
      ring

theorem spin_square (A : Matrix6) :
    spin A * spin A = (energy A : ℂ) • (1 : Matrix4) + (2 : ℂ) • spin (coPfaffian A) := by
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact spin_square_row0 A j
  · exact spin_square_row1 A j
  · exact spin_square_row2 A j
  · exact spin_square_row3 A j

end NoExoticSixSphere.RankSixSkewMatrix
