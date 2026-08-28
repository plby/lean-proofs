import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Explicit skew-six Pfaffian algebra

The matrix formulas in this file are polynomial expressions in the actual
upper-triangular entries of a real six-by-six matrix. Every identity is proved
in Lean; symbolic exploration is not used as a trusted certificate.
-/

namespace NoExoticSixSphere.RankSixSkewMatrix

abbrev Matrix6 := Matrix (Fin 6) (Fin 6) ℝ

def skew (A : Matrix6) : Matrix6 :=
  !![0, A 0 1, A 0 2, A 0 3, A 0 4, A 0 5;
     -A 0 1, 0, A 1 2, A 1 3, A 1 4, A 1 5;
     -A 0 2, -A 1 2, 0, A 2 3, A 2 4, A 2 5;
     -A 0 3, -A 1 3, -A 2 3, 0, A 3 4, A 3 5;
     -A 0 4, -A 1 4, -A 2 4, -A 3 4, 0, A 4 5;
     -A 0 5, -A 1 5, -A 2 5, -A 3 5, -A 4 5, 0]

def pfaffian (A : Matrix6) : ℝ :=
  A 0 1 * A 2 3 * A 4 5 - A 0 1 * A 2 4 * A 3 5 + A 0 1 * A 2 5 * A 3 4 -
  A 0 2 * A 1 3 * A 4 5 + A 0 2 * A 1 4 * A 3 5 - A 0 2 * A 1 5 * A 3 4 +
  A 0 3 * A 1 2 * A 4 5 - A 0 3 * A 1 4 * A 2 5 + A 0 3 * A 1 5 * A 2 4 -
  A 0 4 * A 1 2 * A 3 5 + A 0 4 * A 1 3 * A 2 5 - A 0 4 * A 1 5 * A 2 3 +
  A 0 5 * A 1 2 * A 3 4 - A 0 5 * A 1 3 * A 2 4 + A 0 5 * A 1 4 * A 2 3

def coPfaffian (A : Matrix6) : Matrix6 := skew
  !![0, -A 2 3 * A 4 5 + A 2 4 * A 3 5 - A 2 5 * A 3 4,
        A 1 3 * A 4 5 - A 1 4 * A 3 5 + A 1 5 * A 3 4,
        -A 1 2 * A 4 5 + A 1 4 * A 2 5 - A 1 5 * A 2 4,
        A 1 2 * A 3 5 - A 1 3 * A 2 5 + A 1 5 * A 2 3,
        -A 1 2 * A 3 4 + A 1 3 * A 2 4 - A 1 4 * A 2 3;
     0, 0, -A 0 3 * A 4 5 + A 0 4 * A 3 5 - A 0 5 * A 3 4,
        A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4,
        -A 0 2 * A 3 5 + A 0 3 * A 2 5 - A 0 5 * A 2 3,
        A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3;
     0, 0, 0, -A 0 1 * A 4 5 + A 0 4 * A 1 5 - A 0 5 * A 1 4,
        A 0 1 * A 3 5 - A 0 3 * A 1 5 + A 0 5 * A 1 3,
        -A 0 1 * A 3 4 + A 0 3 * A 1 4 - A 0 4 * A 1 3;
     0, 0, 0, 0, -A 0 1 * A 2 5 + A 0 2 * A 1 5 - A 0 5 * A 1 2,
        A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2;
     0, 0, 0, 0, 0, -A 0 1 * A 2 3 + A 0 2 * A 1 3 - A 0 3 * A 1 2;
     0, 0, 0, 0, 0, 0]

def energy (A : Matrix6) : ℝ :=
  A 0 1 ^ 2 + A 0 2 ^ 2 + A 0 3 ^ 2 + A 0 4 ^ 2 + A 0 5 ^ 2 +
  A 1 2 ^ 2 + A 1 3 ^ 2 + A 1 4 ^ 2 + A 1 5 ^ 2 +
  A 2 3 ^ 2 + A 2 4 ^ 2 + A 2 5 ^ 2 + A 3 4 ^ 2 + A 3 5 ^ 2 + A 4 5 ^ 2

theorem skew_transpose (A : Matrix6) : (skew A).transpose = -(skew A) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skew]

theorem skew_eq (A : Matrix6) (hA : A.transpose = -A) : skew A = A := by
  have he (i j : Fin 6) : A j i = -A i j := congrArg (fun B : Matrix6 ↦ B i j) hA
  have hd (i : Fin 6) : A i i = 0 := by
    have h := he i i
    linarith
  ext i j
  fin_cases i <;> fin_cases j
  all_goals first | rfl | exact (hd _).symm | exact neg_eq_iff_eq_neg.mpr (he _ _)

theorem sum_six {R : Type*} [AddCommMonoid R] (f : Fin 6 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + 0))))) = _
  simp only [add_zero, add_assoc]

theorem mul_coPfaffian_row0 (A : Matrix6) (j : Fin 6) :
    (skew A * coPfaffian A) 0 j = (pfaffian A • (1 : Matrix6)) 0 j := by
  fin_cases j
  · simp only [Matrix.mul_apply, sum_six]
    change
      (0) * (0) +
      (A 0 1) * (-(-A 2 3 * A 4 5 + A 2 4 * A 3 5 - A 2 5 * A 3 4)) +
      (A 0 2) * (-(A 1 3 * A 4 5 - A 1 4 * A 3 5 + A 1 5 * A 3 4)) +
      (A 0 3) * (-(-A 1 2 * A 4 5 + A 1 4 * A 2 5 - A 1 5 * A 2 4)) +
      (A 0 4) * (-(A 1 2 * A 3 5 - A 1 3 * A 2 5 + A 1 5 * A 2 3)) +
      (A 0 5) * (-(-A 1 2 * A 3 4 + A 1 3 * A 2 4 - A 1 4 * A 2 3)) = pfaffian A * 1
    dsimp only [pfaffian]
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (0) * (-A 2 3 * A 4 5 + A 2 4 * A 3 5 - A 2 5 * A 3 4) +
      (A 0 1) * (0) +
      (A 0 2) * (-(-A 0 3 * A 4 5 + A 0 4 * A 3 5 - A 0 5 * A 3 4)) +
      (A 0 3) * (-(A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4)) +
      (A 0 4) * (-(-A 0 2 * A 3 5 + A 0 3 * A 2 5 - A 0 5 * A 2 3)) +
      (A 0 5) * (-(A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3)) = pfaffian A * 0
    dsimp only [pfaffian]
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (0) * (A 1 3 * A 4 5 - A 1 4 * A 3 5 + A 1 5 * A 3 4) +
      (A 0 1) * (-A 0 3 * A 4 5 + A 0 4 * A 3 5 - A 0 5 * A 3 4) +
      (A 0 2) * (0) +
      (A 0 3) * (-(-A 0 1 * A 4 5 + A 0 4 * A 1 5 - A 0 5 * A 1 4)) +
      (A 0 4) * (-(A 0 1 * A 3 5 - A 0 3 * A 1 5 + A 0 5 * A 1 3)) +
      (A 0 5) * (-(-A 0 1 * A 3 4 + A 0 3 * A 1 4 - A 0 4 * A 1 3)) = pfaffian A * 0
    dsimp only [pfaffian]
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (0) * (-A 1 2 * A 4 5 + A 1 4 * A 2 5 - A 1 5 * A 2 4) +
      (A 0 1) * (A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4) +
      (A 0 2) * (-A 0 1 * A 4 5 + A 0 4 * A 1 5 - A 0 5 * A 1 4) +
      (A 0 3) * (0) +
      (A 0 4) * (-(-A 0 1 * A 2 5 + A 0 2 * A 1 5 - A 0 5 * A 1 2)) +
      (A 0 5) * (-(A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2)) = pfaffian A * 0
    dsimp only [pfaffian]
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (0) * (A 1 2 * A 3 5 - A 1 3 * A 2 5 + A 1 5 * A 2 3) +
      (A 0 1) * (-A 0 2 * A 3 5 + A 0 3 * A 2 5 - A 0 5 * A 2 3) +
      (A 0 2) * (A 0 1 * A 3 5 - A 0 3 * A 1 5 + A 0 5 * A 1 3) +
      (A 0 3) * (-A 0 1 * A 2 5 + A 0 2 * A 1 5 - A 0 5 * A 1 2) +
      (A 0 4) * (0) +
      (A 0 5) * (-(-A 0 1 * A 2 3 + A 0 2 * A 1 3 - A 0 3 * A 1 2)) = pfaffian A * 0
    dsimp only [pfaffian]
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (0) * (-A 1 2 * A 3 4 + A 1 3 * A 2 4 - A 1 4 * A 2 3) +
      (A 0 1) * (A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3) +
      (A 0 2) * (-A 0 1 * A 3 4 + A 0 3 * A 1 4 - A 0 4 * A 1 3) +
      (A 0 3) * (A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2) +
      (A 0 4) * (-A 0 1 * A 2 3 + A 0 2 * A 1 3 - A 0 3 * A 1 2) +
      (A 0 5) * (0) = pfaffian A * 0
    dsimp only [pfaffian]
    ring

theorem mul_coPfaffian_row1 (A : Matrix6) (j : Fin 6) :
    (skew A * coPfaffian A) 1 j = (pfaffian A • (1 : Matrix6)) 1 j := by
  fin_cases j
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-A 0 1) * (0) +
      (0) * (-(-A 2 3 * A 4 5 + A 2 4 * A 3 5 - A 2 5 * A 3 4)) +
      (A 1 2) * (-(A 1 3 * A 4 5 - A 1 4 * A 3 5 + A 1 5 * A 3 4)) +
      (A 1 3) * (-(-A 1 2 * A 4 5 + A 1 4 * A 2 5 - A 1 5 * A 2 4)) +
      (A 1 4) * (-(A 1 2 * A 3 5 - A 1 3 * A 2 5 + A 1 5 * A 2 3)) +
      (A 1 5) * (-(-A 1 2 * A 3 4 + A 1 3 * A 2 4 - A 1 4 * A 2 3)) = pfaffian A * 0
    dsimp only [pfaffian]
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-A 0 1) * (-A 2 3 * A 4 5 + A 2 4 * A 3 5 - A 2 5 * A 3 4) +
      (0) * (0) +
      (A 1 2) * (-(-A 0 3 * A 4 5 + A 0 4 * A 3 5 - A 0 5 * A 3 4)) +
      (A 1 3) * (-(A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4)) +
      (A 1 4) * (-(-A 0 2 * A 3 5 + A 0 3 * A 2 5 - A 0 5 * A 2 3)) +
      (A 1 5) * (-(A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3)) = pfaffian A * 1
    dsimp only [pfaffian]
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-A 0 1) * (A 1 3 * A 4 5 - A 1 4 * A 3 5 + A 1 5 * A 3 4) +
      (0) * (-A 0 3 * A 4 5 + A 0 4 * A 3 5 - A 0 5 * A 3 4) +
      (A 1 2) * (0) +
      (A 1 3) * (-(-A 0 1 * A 4 5 + A 0 4 * A 1 5 - A 0 5 * A 1 4)) +
      (A 1 4) * (-(A 0 1 * A 3 5 - A 0 3 * A 1 5 + A 0 5 * A 1 3)) +
      (A 1 5) * (-(-A 0 1 * A 3 4 + A 0 3 * A 1 4 - A 0 4 * A 1 3)) = pfaffian A * 0
    dsimp only [pfaffian]
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-A 0 1) * (-A 1 2 * A 4 5 + A 1 4 * A 2 5 - A 1 5 * A 2 4) +
      (0) * (A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4) +
      (A 1 2) * (-A 0 1 * A 4 5 + A 0 4 * A 1 5 - A 0 5 * A 1 4) +
      (A 1 3) * (0) +
      (A 1 4) * (-(-A 0 1 * A 2 5 + A 0 2 * A 1 5 - A 0 5 * A 1 2)) +
      (A 1 5) * (-(A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2)) = pfaffian A * 0
    dsimp only [pfaffian]
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-A 0 1) * (A 1 2 * A 3 5 - A 1 3 * A 2 5 + A 1 5 * A 2 3) +
      (0) * (-A 0 2 * A 3 5 + A 0 3 * A 2 5 - A 0 5 * A 2 3) +
      (A 1 2) * (A 0 1 * A 3 5 - A 0 3 * A 1 5 + A 0 5 * A 1 3) +
      (A 1 3) * (-A 0 1 * A 2 5 + A 0 2 * A 1 5 - A 0 5 * A 1 2) +
      (A 1 4) * (0) +
      (A 1 5) * (-(-A 0 1 * A 2 3 + A 0 2 * A 1 3 - A 0 3 * A 1 2)) = pfaffian A * 0
    dsimp only [pfaffian]
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-A 0 1) * (-A 1 2 * A 3 4 + A 1 3 * A 2 4 - A 1 4 * A 2 3) +
      (0) * (A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3) +
      (A 1 2) * (-A 0 1 * A 3 4 + A 0 3 * A 1 4 - A 0 4 * A 1 3) +
      (A 1 3) * (A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2) +
      (A 1 4) * (-A 0 1 * A 2 3 + A 0 2 * A 1 3 - A 0 3 * A 1 2) +
      (A 1 5) * (0) = pfaffian A * 0
    dsimp only [pfaffian]
    ring

theorem mul_coPfaffian_row2 (A : Matrix6) (j : Fin 6) :
    (skew A * coPfaffian A) 2 j = (pfaffian A • (1 : Matrix6)) 2 j := by
  fin_cases j
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-A 0 2) * (0) +
      (-A 1 2) * (-(-A 2 3 * A 4 5 + A 2 4 * A 3 5 - A 2 5 * A 3 4)) +
      (0) * (-(A 1 3 * A 4 5 - A 1 4 * A 3 5 + A 1 5 * A 3 4)) +
      (A 2 3) * (-(-A 1 2 * A 4 5 + A 1 4 * A 2 5 - A 1 5 * A 2 4)) +
      (A 2 4) * (-(A 1 2 * A 3 5 - A 1 3 * A 2 5 + A 1 5 * A 2 3)) +
      (A 2 5) * (-(-A 1 2 * A 3 4 + A 1 3 * A 2 4 - A 1 4 * A 2 3)) = pfaffian A * 0
    dsimp only [pfaffian]
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-A 0 2) * (-A 2 3 * A 4 5 + A 2 4 * A 3 5 - A 2 5 * A 3 4) +
      (-A 1 2) * (0) +
      (0) * (-(-A 0 3 * A 4 5 + A 0 4 * A 3 5 - A 0 5 * A 3 4)) +
      (A 2 3) * (-(A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4)) +
      (A 2 4) * (-(-A 0 2 * A 3 5 + A 0 3 * A 2 5 - A 0 5 * A 2 3)) +
      (A 2 5) * (-(A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3)) = pfaffian A * 0
    dsimp only [pfaffian]
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-A 0 2) * (A 1 3 * A 4 5 - A 1 4 * A 3 5 + A 1 5 * A 3 4) +
      (-A 1 2) * (-A 0 3 * A 4 5 + A 0 4 * A 3 5 - A 0 5 * A 3 4) +
      (0) * (0) +
      (A 2 3) * (-(-A 0 1 * A 4 5 + A 0 4 * A 1 5 - A 0 5 * A 1 4)) +
      (A 2 4) * (-(A 0 1 * A 3 5 - A 0 3 * A 1 5 + A 0 5 * A 1 3)) +
      (A 2 5) * (-(-A 0 1 * A 3 4 + A 0 3 * A 1 4 - A 0 4 * A 1 3)) = pfaffian A * 1
    dsimp only [pfaffian]
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-A 0 2) * (-A 1 2 * A 4 5 + A 1 4 * A 2 5 - A 1 5 * A 2 4) +
      (-A 1 2) * (A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4) +
      (0) * (-A 0 1 * A 4 5 + A 0 4 * A 1 5 - A 0 5 * A 1 4) +
      (A 2 3) * (0) +
      (A 2 4) * (-(-A 0 1 * A 2 5 + A 0 2 * A 1 5 - A 0 5 * A 1 2)) +
      (A 2 5) * (-(A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2)) = pfaffian A * 0
    dsimp only [pfaffian]
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-A 0 2) * (A 1 2 * A 3 5 - A 1 3 * A 2 5 + A 1 5 * A 2 3) +
      (-A 1 2) * (-A 0 2 * A 3 5 + A 0 3 * A 2 5 - A 0 5 * A 2 3) +
      (0) * (A 0 1 * A 3 5 - A 0 3 * A 1 5 + A 0 5 * A 1 3) +
      (A 2 3) * (-A 0 1 * A 2 5 + A 0 2 * A 1 5 - A 0 5 * A 1 2) +
      (A 2 4) * (0) +
      (A 2 5) * (-(-A 0 1 * A 2 3 + A 0 2 * A 1 3 - A 0 3 * A 1 2)) = pfaffian A * 0
    dsimp only [pfaffian]
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-A 0 2) * (-A 1 2 * A 3 4 + A 1 3 * A 2 4 - A 1 4 * A 2 3) +
      (-A 1 2) * (A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3) +
      (0) * (-A 0 1 * A 3 4 + A 0 3 * A 1 4 - A 0 4 * A 1 3) +
      (A 2 3) * (A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2) +
      (A 2 4) * (-A 0 1 * A 2 3 + A 0 2 * A 1 3 - A 0 3 * A 1 2) +
      (A 2 5) * (0) = pfaffian A * 0
    dsimp only [pfaffian]
    ring

theorem mul_coPfaffian_row3 (A : Matrix6) (j : Fin 6) :
    (skew A * coPfaffian A) 3 j = (pfaffian A • (1 : Matrix6)) 3 j := by
  fin_cases j
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-A 0 3) * (0) +
      (-A 1 3) * (-(-A 2 3 * A 4 5 + A 2 4 * A 3 5 - A 2 5 * A 3 4)) +
      (-A 2 3) * (-(A 1 3 * A 4 5 - A 1 4 * A 3 5 + A 1 5 * A 3 4)) +
      (0) * (-(-A 1 2 * A 4 5 + A 1 4 * A 2 5 - A 1 5 * A 2 4)) +
      (A 3 4) * (-(A 1 2 * A 3 5 - A 1 3 * A 2 5 + A 1 5 * A 2 3)) +
      (A 3 5) * (-(-A 1 2 * A 3 4 + A 1 3 * A 2 4 - A 1 4 * A 2 3)) = pfaffian A * 0
    dsimp only [pfaffian]
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-A 0 3) * (-A 2 3 * A 4 5 + A 2 4 * A 3 5 - A 2 5 * A 3 4) +
      (-A 1 3) * (0) +
      (-A 2 3) * (-(-A 0 3 * A 4 5 + A 0 4 * A 3 5 - A 0 5 * A 3 4)) +
      (0) * (-(A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4)) +
      (A 3 4) * (-(-A 0 2 * A 3 5 + A 0 3 * A 2 5 - A 0 5 * A 2 3)) +
      (A 3 5) * (-(A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3)) = pfaffian A * 0
    dsimp only [pfaffian]
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-A 0 3) * (A 1 3 * A 4 5 - A 1 4 * A 3 5 + A 1 5 * A 3 4) +
      (-A 1 3) * (-A 0 3 * A 4 5 + A 0 4 * A 3 5 - A 0 5 * A 3 4) +
      (-A 2 3) * (0) +
      (0) * (-(-A 0 1 * A 4 5 + A 0 4 * A 1 5 - A 0 5 * A 1 4)) +
      (A 3 4) * (-(A 0 1 * A 3 5 - A 0 3 * A 1 5 + A 0 5 * A 1 3)) +
      (A 3 5) * (-(-A 0 1 * A 3 4 + A 0 3 * A 1 4 - A 0 4 * A 1 3)) = pfaffian A * 0
    dsimp only [pfaffian]
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-A 0 3) * (-A 1 2 * A 4 5 + A 1 4 * A 2 5 - A 1 5 * A 2 4) +
      (-A 1 3) * (A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4) +
      (-A 2 3) * (-A 0 1 * A 4 5 + A 0 4 * A 1 5 - A 0 5 * A 1 4) +
      (0) * (0) +
      (A 3 4) * (-(-A 0 1 * A 2 5 + A 0 2 * A 1 5 - A 0 5 * A 1 2)) +
      (A 3 5) * (-(A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2)) = pfaffian A * 1
    dsimp only [pfaffian]
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-A 0 3) * (A 1 2 * A 3 5 - A 1 3 * A 2 5 + A 1 5 * A 2 3) +
      (-A 1 3) * (-A 0 2 * A 3 5 + A 0 3 * A 2 5 - A 0 5 * A 2 3) +
      (-A 2 3) * (A 0 1 * A 3 5 - A 0 3 * A 1 5 + A 0 5 * A 1 3) +
      (0) * (-A 0 1 * A 2 5 + A 0 2 * A 1 5 - A 0 5 * A 1 2) +
      (A 3 4) * (0) +
      (A 3 5) * (-(-A 0 1 * A 2 3 + A 0 2 * A 1 3 - A 0 3 * A 1 2)) = pfaffian A * 0
    dsimp only [pfaffian]
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-A 0 3) * (-A 1 2 * A 3 4 + A 1 3 * A 2 4 - A 1 4 * A 2 3) +
      (-A 1 3) * (A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3) +
      (-A 2 3) * (-A 0 1 * A 3 4 + A 0 3 * A 1 4 - A 0 4 * A 1 3) +
      (0) * (A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2) +
      (A 3 4) * (-A 0 1 * A 2 3 + A 0 2 * A 1 3 - A 0 3 * A 1 2) +
      (A 3 5) * (0) = pfaffian A * 0
    dsimp only [pfaffian]
    ring

theorem mul_coPfaffian_row4 (A : Matrix6) (j : Fin 6) :
    (skew A * coPfaffian A) 4 j = (pfaffian A • (1 : Matrix6)) 4 j := by
  fin_cases j
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-A 0 4) * (0) +
      (-A 1 4) * (-(-A 2 3 * A 4 5 + A 2 4 * A 3 5 - A 2 5 * A 3 4)) +
      (-A 2 4) * (-(A 1 3 * A 4 5 - A 1 4 * A 3 5 + A 1 5 * A 3 4)) +
      (-A 3 4) * (-(-A 1 2 * A 4 5 + A 1 4 * A 2 5 - A 1 5 * A 2 4)) +
      (0) * (-(A 1 2 * A 3 5 - A 1 3 * A 2 5 + A 1 5 * A 2 3)) +
      (A 4 5) * (-(-A 1 2 * A 3 4 + A 1 3 * A 2 4 - A 1 4 * A 2 3)) = pfaffian A * 0
    dsimp only [pfaffian]
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-A 0 4) * (-A 2 3 * A 4 5 + A 2 4 * A 3 5 - A 2 5 * A 3 4) +
      (-A 1 4) * (0) +
      (-A 2 4) * (-(-A 0 3 * A 4 5 + A 0 4 * A 3 5 - A 0 5 * A 3 4)) +
      (-A 3 4) * (-(A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4)) +
      (0) * (-(-A 0 2 * A 3 5 + A 0 3 * A 2 5 - A 0 5 * A 2 3)) +
      (A 4 5) * (-(A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3)) = pfaffian A * 0
    dsimp only [pfaffian]
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-A 0 4) * (A 1 3 * A 4 5 - A 1 4 * A 3 5 + A 1 5 * A 3 4) +
      (-A 1 4) * (-A 0 3 * A 4 5 + A 0 4 * A 3 5 - A 0 5 * A 3 4) +
      (-A 2 4) * (0) +
      (-A 3 4) * (-(-A 0 1 * A 4 5 + A 0 4 * A 1 5 - A 0 5 * A 1 4)) +
      (0) * (-(A 0 1 * A 3 5 - A 0 3 * A 1 5 + A 0 5 * A 1 3)) +
      (A 4 5) * (-(-A 0 1 * A 3 4 + A 0 3 * A 1 4 - A 0 4 * A 1 3)) = pfaffian A * 0
    dsimp only [pfaffian]
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-A 0 4) * (-A 1 2 * A 4 5 + A 1 4 * A 2 5 - A 1 5 * A 2 4) +
      (-A 1 4) * (A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4) +
      (-A 2 4) * (-A 0 1 * A 4 5 + A 0 4 * A 1 5 - A 0 5 * A 1 4) +
      (-A 3 4) * (0) +
      (0) * (-(-A 0 1 * A 2 5 + A 0 2 * A 1 5 - A 0 5 * A 1 2)) +
      (A 4 5) * (-(A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2)) = pfaffian A * 0
    dsimp only [pfaffian]
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-A 0 4) * (A 1 2 * A 3 5 - A 1 3 * A 2 5 + A 1 5 * A 2 3) +
      (-A 1 4) * (-A 0 2 * A 3 5 + A 0 3 * A 2 5 - A 0 5 * A 2 3) +
      (-A 2 4) * (A 0 1 * A 3 5 - A 0 3 * A 1 5 + A 0 5 * A 1 3) +
      (-A 3 4) * (-A 0 1 * A 2 5 + A 0 2 * A 1 5 - A 0 5 * A 1 2) +
      (0) * (0) +
      (A 4 5) * (-(-A 0 1 * A 2 3 + A 0 2 * A 1 3 - A 0 3 * A 1 2)) = pfaffian A * 1
    dsimp only [pfaffian]
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-A 0 4) * (-A 1 2 * A 3 4 + A 1 3 * A 2 4 - A 1 4 * A 2 3) +
      (-A 1 4) * (A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3) +
      (-A 2 4) * (-A 0 1 * A 3 4 + A 0 3 * A 1 4 - A 0 4 * A 1 3) +
      (-A 3 4) * (A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2) +
      (0) * (-A 0 1 * A 2 3 + A 0 2 * A 1 3 - A 0 3 * A 1 2) +
      (A 4 5) * (0) = pfaffian A * 0
    dsimp only [pfaffian]
    ring

theorem mul_coPfaffian_row5 (A : Matrix6) (j : Fin 6) :
    (skew A * coPfaffian A) 5 j = (pfaffian A • (1 : Matrix6)) 5 j := by
  fin_cases j
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-A 0 5) * (0) +
      (-A 1 5) * (-(-A 2 3 * A 4 5 + A 2 4 * A 3 5 - A 2 5 * A 3 4)) +
      (-A 2 5) * (-(A 1 3 * A 4 5 - A 1 4 * A 3 5 + A 1 5 * A 3 4)) +
      (-A 3 5) * (-(-A 1 2 * A 4 5 + A 1 4 * A 2 5 - A 1 5 * A 2 4)) +
      (-A 4 5) * (-(A 1 2 * A 3 5 - A 1 3 * A 2 5 + A 1 5 * A 2 3)) +
      (0) * (-(-A 1 2 * A 3 4 + A 1 3 * A 2 4 - A 1 4 * A 2 3)) = pfaffian A * 0
    dsimp only [pfaffian]
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-A 0 5) * (-A 2 3 * A 4 5 + A 2 4 * A 3 5 - A 2 5 * A 3 4) +
      (-A 1 5) * (0) +
      (-A 2 5) * (-(-A 0 3 * A 4 5 + A 0 4 * A 3 5 - A 0 5 * A 3 4)) +
      (-A 3 5) * (-(A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4)) +
      (-A 4 5) * (-(-A 0 2 * A 3 5 + A 0 3 * A 2 5 - A 0 5 * A 2 3)) +
      (0) * (-(A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3)) = pfaffian A * 0
    dsimp only [pfaffian]
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-A 0 5) * (A 1 3 * A 4 5 - A 1 4 * A 3 5 + A 1 5 * A 3 4) +
      (-A 1 5) * (-A 0 3 * A 4 5 + A 0 4 * A 3 5 - A 0 5 * A 3 4) +
      (-A 2 5) * (0) +
      (-A 3 5) * (-(-A 0 1 * A 4 5 + A 0 4 * A 1 5 - A 0 5 * A 1 4)) +
      (-A 4 5) * (-(A 0 1 * A 3 5 - A 0 3 * A 1 5 + A 0 5 * A 1 3)) +
      (0) * (-(-A 0 1 * A 3 4 + A 0 3 * A 1 4 - A 0 4 * A 1 3)) = pfaffian A * 0
    dsimp only [pfaffian]
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-A 0 5) * (-A 1 2 * A 4 5 + A 1 4 * A 2 5 - A 1 5 * A 2 4) +
      (-A 1 5) * (A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4) +
      (-A 2 5) * (-A 0 1 * A 4 5 + A 0 4 * A 1 5 - A 0 5 * A 1 4) +
      (-A 3 5) * (0) +
      (-A 4 5) * (-(-A 0 1 * A 2 5 + A 0 2 * A 1 5 - A 0 5 * A 1 2)) +
      (0) * (-(A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2)) = pfaffian A * 0
    dsimp only [pfaffian]
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-A 0 5) * (A 1 2 * A 3 5 - A 1 3 * A 2 5 + A 1 5 * A 2 3) +
      (-A 1 5) * (-A 0 2 * A 3 5 + A 0 3 * A 2 5 - A 0 5 * A 2 3) +
      (-A 2 5) * (A 0 1 * A 3 5 - A 0 3 * A 1 5 + A 0 5 * A 1 3) +
      (-A 3 5) * (-A 0 1 * A 2 5 + A 0 2 * A 1 5 - A 0 5 * A 1 2) +
      (-A 4 5) * (0) +
      (0) * (-(-A 0 1 * A 2 3 + A 0 2 * A 1 3 - A 0 3 * A 1 2)) = pfaffian A * 0
    dsimp only [pfaffian]
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-A 0 5) * (-A 1 2 * A 3 4 + A 1 3 * A 2 4 - A 1 4 * A 2 3) +
      (-A 1 5) * (A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3) +
      (-A 2 5) * (-A 0 1 * A 3 4 + A 0 3 * A 1 4 - A 0 4 * A 1 3) +
      (-A 3 5) * (A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2) +
      (-A 4 5) * (-A 0 1 * A 2 3 + A 0 2 * A 1 3 - A 0 3 * A 1 2) +
      (0) * (0) = pfaffian A * 1
    dsimp only [pfaffian]
    ring

theorem mul_coPfaffian (A : Matrix6) :
    skew A * coPfaffian A = pfaffian A • (1 : Matrix6) := by
  ext i j
  fin_cases i
  · exact mul_coPfaffian_row0 A j
  · exact mul_coPfaffian_row1 A j
  · exact mul_coPfaffian_row2 A j
  · exact mul_coPfaffian_row3 A j
  · exact mul_coPfaffian_row4 A j
  · exact mul_coPfaffian_row5 A j

theorem coPfaffian_eq_of_square (A : Matrix6) (hA : A.transpose = -A)
    (hsq : A * A = -(1 : Matrix6)) : coPfaffian A = (-pfaffian A) • A := by
  have h := congrArg (fun B : Matrix6 ↦ A * B) (mul_coPfaffian A)
  rw [skew_eq A hA, ← Matrix.mul_assoc, hsq] at h
  simpa only [neg_mul, one_mul, Matrix.mul_smul, mul_one, neg_smul, neg_neg] using
    congrArg Neg.neg h

end NoExoticSixSphere.RankSixSkewMatrix
