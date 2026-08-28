import Wikipedia.NoExoticSixSphere.RankSixSpinMatrix

/-!
# A homogeneous quadratic complex-structure matrix from a spinor

The skew matrix below is defined for every vector of four complex numbers.
Its square is minus the fourth power of the spinor norm times identity.
All entries and polynomial identities are checked over the reals.
-/

namespace NoExoticSixSphere.RankSixSkewMatrix

def spinorNormSq (q : Fin 4 → ℂ) : ℝ :=
  (q 0).re ^ 2 + (q 0).im ^ 2 + (q 1).re ^ 2 + (q 1).im ^ 2 +
    (q 2).re ^ 2 + (q 2).im ^ 2 + (q 3).re ^ 2 + (q 3).im ^ 2

def spinorMatrix (q : Fin 4 → ℂ) : Matrix6 :=
  let a0 : ℝ := (q 0).re
  let b0 : ℝ := (q 0).im
  let a1 : ℝ := (q 1).re
  let b1 : ℝ := (q 1).im
  let a2 : ℝ := (q 2).re
  let b2 : ℝ := (q 2).im
  let a3 : ℝ := (q 3).re
  let b3 : ℝ := (q 3).im
  skew !![0,
      -a0 ^ 2 + a1 ^ 2 + a2 ^ 2 - a3 ^ 2 - b0 ^ 2 + b1 ^ 2 + b2 ^ 2 - b3 ^ 2,
      2 * a0 * b1 - 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2,
      -2 * a0 * a1 + 2 * a2 * a3 - 2 * b0 * b1 + 2 * b2 * b3,
      2 * a0 * b2 + 2 * a1 * b3 - 2 * a2 * b0 - 2 * a3 * b1,
      -2 * a0 * a2 - 2 * a1 * a3 - 2 * b0 * b2 - 2 * b1 * b3;
    0,
      0,
      -2 * a0 * a1 - 2 * a2 * a3 - 2 * b0 * b1 - 2 * b2 * b3,
      -2 * a0 * b1 + 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2,
      -2 * a0 * a2 + 2 * a1 * a3 - 2 * b0 * b2 + 2 * b1 * b3,
      -2 * a0 * b2 + 2 * a1 * b3 + 2 * a2 * b0 - 2 * a3 * b1;
    0,
      0,
      0,
      -a0 ^ 2 + a1 ^ 2 - a2 ^ 2 + a3 ^ 2 - b0 ^ 2 + b1 ^ 2 - b2 ^ 2 + b3 ^ 2,
      2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 - 2 * a3 * b0,
      -2 * a0 * a3 + 2 * a1 * a2 - 2 * b0 * b3 + 2 * b1 * b2;
    0,
      0,
      0,
      0,
      -2 * a0 * a3 - 2 * a1 * a2 - 2 * b0 * b3 - 2 * b1 * b2,
      -2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 + 2 * a3 * b0;
    0,
      0,
      0,
      0,
      0,
      -a0 ^ 2 - a1 ^ 2 + a2 ^ 2 + a3 ^ 2 - b0 ^ 2 - b1 ^ 2 + b2 ^ 2 + b3 ^ 2;
    0,
      0,
      0,
      0,
      0,
      0]

theorem spinorMatrix_transpose (q : Fin 4 → ℂ) :
    (spinorMatrix q).transpose = -spinorMatrix q :=
  skew_transpose _

theorem spinorMatrix_square_row0 (q : Fin 4 → ℂ) (j : Fin 6) :
    (spinorMatrix q * spinorMatrix q) 0 j =
      ((-(spinorNormSq q ^ 2)) • (1 : Matrix6)) 0 j := by
  let a0 : ℝ := (q 0).re
  let b0 : ℝ := (q 0).im
  let a1 : ℝ := (q 1).re
  let b1 : ℝ := (q 1).im
  let a2 : ℝ := (q 2).re
  let b2 : ℝ := (q 2).im
  let a3 : ℝ := (q 3).re
  let b3 : ℝ := (q 3).im
  fin_cases j
  · simp only [Matrix.mul_apply, sum_six]
    change
      (0) * (0) + (-a0 ^ 2 + a1 ^ 2 + a2 ^ 2 - a3 ^ 2 - b0 ^ 2 + b1 ^ 2 + b2 ^ 2 - b3 ^ 2) *
      (-(-a0 ^ 2 + a1 ^ 2 + a2 ^ 2 - a3 ^ 2 - b0 ^ 2 + b1 ^ 2 + b2 ^ 2 - b3 ^ 2)) + (2 * a0 * b1
      - 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2) * (-(2 * a0 * b1 - 2 * a1 * b0 - 2 * a2 * b3 +
      2 * a3 * b2)) + (-2 * a0 * a1 + 2 * a2 * a3 - 2 * b0 * b1 + 2 * b2 * b3) * (-(-2 * a0 * a1
      + 2 * a2 * a3 - 2 * b0 * b1 + 2 * b2 * b3)) + (2 * a0 * b2 + 2 * a1 * b3 - 2 * a2 * b0 - 2
      * a3 * b1) * (-(2 * a0 * b2 + 2 * a1 * b3 - 2 * a2 * b0 - 2 * a3 * b1)) + (-2 * a0 * a2 -
      2 * a1 * a3 - 2 * b0 * b2 - 2 * b1 * b3) * (-(-2 * a0 * a2 - 2 * a1 * a3 - 2 * b0 * b2 - 2
      * b1 * b3)) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) ^
      2) * 1
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (0) * (-a0 ^ 2 + a1 ^ 2 + a2 ^ 2 - a3 ^ 2 - b0 ^ 2 + b1 ^ 2 + b2 ^ 2 - b3 ^ 2) + (-a0 ^ 2
      + a1 ^ 2 + a2 ^ 2 - a3 ^ 2 - b0 ^ 2 + b1 ^ 2 + b2 ^ 2 - b3 ^ 2) * (0) + (2 * a0 * b1 - 2 *
      a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2) * (-(-2 * a0 * a1 - 2 * a2 * a3 - 2 * b0 * b1 - 2 *
      b2 * b3)) + (-2 * a0 * a1 + 2 * a2 * a3 - 2 * b0 * b1 + 2 * b2 * b3) * (-(-2 * a0 * b1 + 2
      * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2)) + (2 * a0 * b2 + 2 * a1 * b3 - 2 * a2 * b0 - 2 *
      a3 * b1) * (-(-2 * a0 * a2 + 2 * a1 * a3 - 2 * b0 * b2 + 2 * b1 * b3)) + (-2 * a0 * a2 - 2
      * a1 * a3 - 2 * b0 * b2 - 2 * b1 * b3) * (-(-2 * a0 * b2 + 2 * a1 * b3 + 2 * a2 * b0 - 2 *
      a3 * b1)) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) ^ 2)
      * 0
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (0) * (2 * a0 * b1 - 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2) + (-a0 ^ 2 + a1 ^ 2 + a2 ^ 2
      - a3 ^ 2 - b0 ^ 2 + b1 ^ 2 + b2 ^ 2 - b3 ^ 2) * (-2 * a0 * a1 - 2 * a2 * a3 - 2 * b0 * b1
      - 2 * b2 * b3) + (2 * a0 * b1 - 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2) * (0) + (-2 * a0
      * a1 + 2 * a2 * a3 - 2 * b0 * b1 + 2 * b2 * b3) * (-(-a0 ^ 2 + a1 ^ 2 - a2 ^ 2 + a3 ^ 2 -
      b0 ^ 2 + b1 ^ 2 - b2 ^ 2 + b3 ^ 2)) + (2 * a0 * b2 + 2 * a1 * b3 - 2 * a2 * b0 - 2 * a3 *
      b1) * (-(2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 - 2 * a3 * b0)) + (-2 * a0 * a2 - 2 * a1
      * a3 - 2 * b0 * b2 - 2 * b1 * b3) * (-(-2 * a0 * a3 + 2 * a1 * a2 - 2 * b0 * b3 + 2 * b1 *
      b2)) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) ^ 2) * 0
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (0) * (-2 * a0 * a1 + 2 * a2 * a3 - 2 * b0 * b1 + 2 * b2 * b3) + (-a0 ^ 2 + a1 ^ 2 + a2 ^
      2 - a3 ^ 2 - b0 ^ 2 + b1 ^ 2 + b2 ^ 2 - b3 ^ 2) * (-2 * a0 * b1 + 2 * a1 * b0 - 2 * a2 *
      b3 + 2 * a3 * b2) + (2 * a0 * b1 - 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2) * (-a0 ^ 2 +
      a1 ^ 2 - a2 ^ 2 + a3 ^ 2 - b0 ^ 2 + b1 ^ 2 - b2 ^ 2 + b3 ^ 2) + (-2 * a0 * a1 + 2 * a2 *
      a3 - 2 * b0 * b1 + 2 * b2 * b3) * (0) + (2 * a0 * b2 + 2 * a1 * b3 - 2 * a2 * b0 - 2 * a3
      * b1) * (-(-2 * a0 * a3 - 2 * a1 * a2 - 2 * b0 * b3 - 2 * b1 * b2)) + (-2 * a0 * a2 - 2 *
      a1 * a3 - 2 * b0 * b2 - 2 * b1 * b3) * (-(-2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 + 2 *
      a3 * b0)) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) ^ 2)
      * 0
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (0) * (2 * a0 * b2 + 2 * a1 * b3 - 2 * a2 * b0 - 2 * a3 * b1) + (-a0 ^ 2 + a1 ^ 2 + a2 ^ 2
      - a3 ^ 2 - b0 ^ 2 + b1 ^ 2 + b2 ^ 2 - b3 ^ 2) * (-2 * a0 * a2 + 2 * a1 * a3 - 2 * b0 * b2
      + 2 * b1 * b3) + (2 * a0 * b1 - 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2) * (2 * a0 * b3 -
      2 * a1 * b2 + 2 * a2 * b1 - 2 * a3 * b0) + (-2 * a0 * a1 + 2 * a2 * a3 - 2 * b0 * b1 + 2 *
      b2 * b3) * (-2 * a0 * a3 - 2 * a1 * a2 - 2 * b0 * b3 - 2 * b1 * b2) + (2 * a0 * b2 + 2 *
      a1 * b3 - 2 * a2 * b0 - 2 * a3 * b1) * (0) + (-2 * a0 * a2 - 2 * a1 * a3 - 2 * b0 * b2 - 2
      * b1 * b3) * (-(-a0 ^ 2 - a1 ^ 2 + a2 ^ 2 + a3 ^ 2 - b0 ^ 2 - b1 ^ 2 + b2 ^ 2 + b3 ^ 2)) =
      -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) ^ 2) * 0
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (0) * (-2 * a0 * a2 - 2 * a1 * a3 - 2 * b0 * b2 - 2 * b1 * b3) + (-a0 ^ 2 + a1 ^ 2 + a2 ^
      2 - a3 ^ 2 - b0 ^ 2 + b1 ^ 2 + b2 ^ 2 - b3 ^ 2) * (-2 * a0 * b2 + 2 * a1 * b3 + 2 * a2 *
      b0 - 2 * a3 * b1) + (2 * a0 * b1 - 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2) * (-2 * a0 *
      a3 + 2 * a1 * a2 - 2 * b0 * b3 + 2 * b1 * b2) + (-2 * a0 * a1 + 2 * a2 * a3 - 2 * b0 * b1
      + 2 * b2 * b3) * (-2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 + 2 * a3 * b0) + (2 * a0 * b2 +
      2 * a1 * b3 - 2 * a2 * b0 - 2 * a3 * b1) * (-a0 ^ 2 - a1 ^ 2 + a2 ^ 2 + a3 ^ 2 - b0 ^ 2 -
      b1 ^ 2 + b2 ^ 2 + b3 ^ 2) + (-2 * a0 * a2 - 2 * a1 * a3 - 2 * b0 * b2 - 2 * b1 * b3) * (0)
      = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) ^ 2) * 0
    ring

theorem spinorMatrix_square_row1 (q : Fin 4 → ℂ) (j : Fin 6) :
    (spinorMatrix q * spinorMatrix q) 1 j =
      ((-(spinorNormSq q ^ 2)) • (1 : Matrix6)) 1 j := by
  let a0 : ℝ := (q 0).re
  let b0 : ℝ := (q 0).im
  let a1 : ℝ := (q 1).re
  let b1 : ℝ := (q 1).im
  let a2 : ℝ := (q 2).re
  let b2 : ℝ := (q 2).im
  let a3 : ℝ := (q 3).re
  let b3 : ℝ := (q 3).im
  fin_cases j
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-(-a0 ^ 2 + a1 ^ 2 + a2 ^ 2 - a3 ^ 2 - b0 ^ 2 + b1 ^ 2 + b2 ^ 2 - b3 ^ 2)) * (0) + (0) *
      (-(-a0 ^ 2 + a1 ^ 2 + a2 ^ 2 - a3 ^ 2 - b0 ^ 2 + b1 ^ 2 + b2 ^ 2 - b3 ^ 2)) + (-2 * a0 *
      a1 - 2 * a2 * a3 - 2 * b0 * b1 - 2 * b2 * b3) * (-(2 * a0 * b1 - 2 * a1 * b0 - 2 * a2 * b3
      + 2 * a3 * b2)) + (-2 * a0 * b1 + 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2) * (-(-2 * a0 *
      a1 + 2 * a2 * a3 - 2 * b0 * b1 + 2 * b2 * b3)) + (-2 * a0 * a2 + 2 * a1 * a3 - 2 * b0 * b2
      + 2 * b1 * b3) * (-(2 * a0 * b2 + 2 * a1 * b3 - 2 * a2 * b0 - 2 * a3 * b1)) + (-2 * a0 *
      b2 + 2 * a1 * b3 + 2 * a2 * b0 - 2 * a3 * b1) * (-(-2 * a0 * a2 - 2 * a1 * a3 - 2 * b0 *
      b2 - 2 * b1 * b3)) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3
      ^ 2) ^ 2) * 0
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-(-a0 ^ 2 + a1 ^ 2 + a2 ^ 2 - a3 ^ 2 - b0 ^ 2 + b1 ^ 2 + b2 ^ 2 - b3 ^ 2)) * (-a0 ^ 2 +
      a1 ^ 2 + a2 ^ 2 - a3 ^ 2 - b0 ^ 2 + b1 ^ 2 + b2 ^ 2 - b3 ^ 2) + (0) * (0) + (-2 * a0 * a1
      - 2 * a2 * a3 - 2 * b0 * b1 - 2 * b2 * b3) * (-(-2 * a0 * a1 - 2 * a2 * a3 - 2 * b0 * b1 -
      2 * b2 * b3)) + (-2 * a0 * b1 + 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2) * (-(-2 * a0 * b1
      + 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2)) + (-2 * a0 * a2 + 2 * a1 * a3 - 2 * b0 * b2 +
      2 * b1 * b3) * (-(-2 * a0 * a2 + 2 * a1 * a3 - 2 * b0 * b2 + 2 * b1 * b3)) + (-2 * a0 * b2
      + 2 * a1 * b3 + 2 * a2 * b0 - 2 * a3 * b1) * (-(-2 * a0 * b2 + 2 * a1 * b3 + 2 * a2 * b0 -
      2 * a3 * b1)) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2)
      ^ 2) * 1
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-(-a0 ^ 2 + a1 ^ 2 + a2 ^ 2 - a3 ^ 2 - b0 ^ 2 + b1 ^ 2 + b2 ^ 2 - b3 ^ 2)) * (2 * a0 * b1
      - 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2) + (0) * (-2 * a0 * a1 - 2 * a2 * a3 - 2 * b0 *
      b1 - 2 * b2 * b3) + (-2 * a0 * a1 - 2 * a2 * a3 - 2 * b0 * b1 - 2 * b2 * b3) * (0) + (-2 *
      a0 * b1 + 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2) * (-(-a0 ^ 2 + a1 ^ 2 - a2 ^ 2 + a3 ^ 2
      - b0 ^ 2 + b1 ^ 2 - b2 ^ 2 + b3 ^ 2)) + (-2 * a0 * a2 + 2 * a1 * a3 - 2 * b0 * b2 + 2 * b1
      * b3) * (-(2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 - 2 * a3 * b0)) + (-2 * a0 * b2 + 2 *
      a1 * b3 + 2 * a2 * b0 - 2 * a3 * b1) * (-(-2 * a0 * a3 + 2 * a1 * a2 - 2 * b0 * b3 + 2 *
      b1 * b2)) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) ^ 2)
      * 0
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-(-a0 ^ 2 + a1 ^ 2 + a2 ^ 2 - a3 ^ 2 - b0 ^ 2 + b1 ^ 2 + b2 ^ 2 - b3 ^ 2)) * (-2 * a0 *
      a1 + 2 * a2 * a3 - 2 * b0 * b1 + 2 * b2 * b3) + (0) * (-2 * a0 * b1 + 2 * a1 * b0 - 2 * a2
      * b3 + 2 * a3 * b2) + (-2 * a0 * a1 - 2 * a2 * a3 - 2 * b0 * b1 - 2 * b2 * b3) * (-a0 ^ 2
      + a1 ^ 2 - a2 ^ 2 + a3 ^ 2 - b0 ^ 2 + b1 ^ 2 - b2 ^ 2 + b3 ^ 2) + (-2 * a0 * b1 + 2 * a1 *
      b0 - 2 * a2 * b3 + 2 * a3 * b2) * (0) + (-2 * a0 * a2 + 2 * a1 * a3 - 2 * b0 * b2 + 2 * b1
      * b3) * (-(-2 * a0 * a3 - 2 * a1 * a2 - 2 * b0 * b3 - 2 * b1 * b2)) + (-2 * a0 * b2 + 2 *
      a1 * b3 + 2 * a2 * b0 - 2 * a3 * b1) * (-(-2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 + 2 *
      a3 * b0)) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) ^ 2)
      * 0
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-(-a0 ^ 2 + a1 ^ 2 + a2 ^ 2 - a3 ^ 2 - b0 ^ 2 + b1 ^ 2 + b2 ^ 2 - b3 ^ 2)) * (2 * a0 * b2
      + 2 * a1 * b3 - 2 * a2 * b0 - 2 * a3 * b1) + (0) * (-2 * a0 * a2 + 2 * a1 * a3 - 2 * b0 *
      b2 + 2 * b1 * b3) + (-2 * a0 * a1 - 2 * a2 * a3 - 2 * b0 * b1 - 2 * b2 * b3) * (2 * a0 *
      b3 - 2 * a1 * b2 + 2 * a2 * b1 - 2 * a3 * b0) + (-2 * a0 * b1 + 2 * a1 * b0 - 2 * a2 * b3
      + 2 * a3 * b2) * (-2 * a0 * a3 - 2 * a1 * a2 - 2 * b0 * b3 - 2 * b1 * b2) + (-2 * a0 * a2
      + 2 * a1 * a3 - 2 * b0 * b2 + 2 * b1 * b3) * (0) + (-2 * a0 * b2 + 2 * a1 * b3 + 2 * a2 *
      b0 - 2 * a3 * b1) * (-(-a0 ^ 2 - a1 ^ 2 + a2 ^ 2 + a3 ^ 2 - b0 ^ 2 - b1 ^ 2 + b2 ^ 2 + b3
      ^ 2)) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) ^ 2) * 0
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-(-a0 ^ 2 + a1 ^ 2 + a2 ^ 2 - a3 ^ 2 - b0 ^ 2 + b1 ^ 2 + b2 ^ 2 - b3 ^ 2)) * (-2 * a0 *
      a2 - 2 * a1 * a3 - 2 * b0 * b2 - 2 * b1 * b3) + (0) * (-2 * a0 * b2 + 2 * a1 * b3 + 2 * a2
      * b0 - 2 * a3 * b1) + (-2 * a0 * a1 - 2 * a2 * a3 - 2 * b0 * b1 - 2 * b2 * b3) * (-2 * a0
      * a3 + 2 * a1 * a2 - 2 * b0 * b3 + 2 * b1 * b2) + (-2 * a0 * b1 + 2 * a1 * b0 - 2 * a2 *
      b3 + 2 * a3 * b2) * (-2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 + 2 * a3 * b0) + (-2 * a0 *
      a2 + 2 * a1 * a3 - 2 * b0 * b2 + 2 * b1 * b3) * (-a0 ^ 2 - a1 ^ 2 + a2 ^ 2 + a3 ^ 2 - b0 ^
      2 - b1 ^ 2 + b2 ^ 2 + b3 ^ 2) + (-2 * a0 * b2 + 2 * a1 * b3 + 2 * a2 * b0 - 2 * a3 * b1) *
      (0) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) ^ 2) * 0
    ring

theorem spinorMatrix_square_row2 (q : Fin 4 → ℂ) (j : Fin 6) :
    (spinorMatrix q * spinorMatrix q) 2 j =
      ((-(spinorNormSq q ^ 2)) • (1 : Matrix6)) 2 j := by
  let a0 : ℝ := (q 0).re
  let b0 : ℝ := (q 0).im
  let a1 : ℝ := (q 1).re
  let b1 : ℝ := (q 1).im
  let a2 : ℝ := (q 2).re
  let b2 : ℝ := (q 2).im
  let a3 : ℝ := (q 3).re
  let b3 : ℝ := (q 3).im
  fin_cases j
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-(2 * a0 * b1 - 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2)) * (0) + (-(-2 * a0 * a1 - 2 *
      a2 * a3 - 2 * b0 * b1 - 2 * b2 * b3)) * (-(-a0 ^ 2 + a1 ^ 2 + a2 ^ 2 - a3 ^ 2 - b0 ^ 2 +
      b1 ^ 2 + b2 ^ 2 - b3 ^ 2)) + (0) * (-(2 * a0 * b1 - 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 *
      b2)) + (-a0 ^ 2 + a1 ^ 2 - a2 ^ 2 + a3 ^ 2 - b0 ^ 2 + b1 ^ 2 - b2 ^ 2 + b3 ^ 2) * (-(-2 *
      a0 * a1 + 2 * a2 * a3 - 2 * b0 * b1 + 2 * b2 * b3)) + (2 * a0 * b3 - 2 * a1 * b2 + 2 * a2
      * b1 - 2 * a3 * b0) * (-(2 * a0 * b2 + 2 * a1 * b3 - 2 * a2 * b0 - 2 * a3 * b1)) + (-2 *
      a0 * a3 + 2 * a1 * a2 - 2 * b0 * b3 + 2 * b1 * b2) * (-(-2 * a0 * a2 - 2 * a1 * a3 - 2 *
      b0 * b2 - 2 * b1 * b3)) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2
      + b3 ^ 2) ^ 2) * 0
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-(2 * a0 * b1 - 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2)) * (-a0 ^ 2 + a1 ^ 2 + a2 ^ 2 -
      a3 ^ 2 - b0 ^ 2 + b1 ^ 2 + b2 ^ 2 - b3 ^ 2) + (-(-2 * a0 * a1 - 2 * a2 * a3 - 2 * b0 * b1
      - 2 * b2 * b3)) * (0) + (0) * (-(-2 * a0 * a1 - 2 * a2 * a3 - 2 * b0 * b1 - 2 * b2 * b3))
      + (-a0 ^ 2 + a1 ^ 2 - a2 ^ 2 + a3 ^ 2 - b0 ^ 2 + b1 ^ 2 - b2 ^ 2 + b3 ^ 2) * (-(-2 * a0 *
      b1 + 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2)) + (2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1
      - 2 * a3 * b0) * (-(-2 * a0 * a2 + 2 * a1 * a3 - 2 * b0 * b2 + 2 * b1 * b3)) + (-2 * a0 *
      a3 + 2 * a1 * a2 - 2 * b0 * b3 + 2 * b1 * b2) * (-(-2 * a0 * b2 + 2 * a1 * b3 + 2 * a2 *
      b0 - 2 * a3 * b1)) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3
      ^ 2) ^ 2) * 0
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-(2 * a0 * b1 - 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2)) * (2 * a0 * b1 - 2 * a1 * b0 -
      2 * a2 * b3 + 2 * a3 * b2) + (-(-2 * a0 * a1 - 2 * a2 * a3 - 2 * b0 * b1 - 2 * b2 * b3)) *
      (-2 * a0 * a1 - 2 * a2 * a3 - 2 * b0 * b1 - 2 * b2 * b3) + (0) * (0) + (-a0 ^ 2 + a1 ^ 2 -
      a2 ^ 2 + a3 ^ 2 - b0 ^ 2 + b1 ^ 2 - b2 ^ 2 + b3 ^ 2) * (-(-a0 ^ 2 + a1 ^ 2 - a2 ^ 2 + a3 ^
      2 - b0 ^ 2 + b1 ^ 2 - b2 ^ 2 + b3 ^ 2)) + (2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 - 2 *
      a3 * b0) * (-(2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 - 2 * a3 * b0)) + (-2 * a0 * a3 + 2
      * a1 * a2 - 2 * b0 * b3 + 2 * b1 * b2) * (-(-2 * a0 * a3 + 2 * a1 * a2 - 2 * b0 * b3 + 2 *
      b1 * b2)) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) ^ 2)
      * 1
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-(2 * a0 * b1 - 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2)) * (-2 * a0 * a1 + 2 * a2 * a3 -
      2 * b0 * b1 + 2 * b2 * b3) + (-(-2 * a0 * a1 - 2 * a2 * a3 - 2 * b0 * b1 - 2 * b2 * b3)) *
      (-2 * a0 * b1 + 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2) + (0) * (-a0 ^ 2 + a1 ^ 2 - a2 ^
      2 + a3 ^ 2 - b0 ^ 2 + b1 ^ 2 - b2 ^ 2 + b3 ^ 2) + (-a0 ^ 2 + a1 ^ 2 - a2 ^ 2 + a3 ^ 2 - b0
      ^ 2 + b1 ^ 2 - b2 ^ 2 + b3 ^ 2) * (0) + (2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 - 2 * a3
      * b0) * (-(-2 * a0 * a3 - 2 * a1 * a2 - 2 * b0 * b3 - 2 * b1 * b2)) + (-2 * a0 * a3 + 2 *
      a1 * a2 - 2 * b0 * b3 + 2 * b1 * b2) * (-(-2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 + 2 *
      a3 * b0)) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) ^ 2)
      * 0
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-(2 * a0 * b1 - 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2)) * (2 * a0 * b2 + 2 * a1 * b3 -
      2 * a2 * b0 - 2 * a3 * b1) + (-(-2 * a0 * a1 - 2 * a2 * a3 - 2 * b0 * b1 - 2 * b2 * b3)) *
      (-2 * a0 * a2 + 2 * a1 * a3 - 2 * b0 * b2 + 2 * b1 * b3) + (0) * (2 * a0 * b3 - 2 * a1 *
      b2 + 2 * a2 * b1 - 2 * a3 * b0) + (-a0 ^ 2 + a1 ^ 2 - a2 ^ 2 + a3 ^ 2 - b0 ^ 2 + b1 ^ 2 -
      b2 ^ 2 + b3 ^ 2) * (-2 * a0 * a3 - 2 * a1 * a2 - 2 * b0 * b3 - 2 * b1 * b2) + (2 * a0 * b3
      - 2 * a1 * b2 + 2 * a2 * b1 - 2 * a3 * b0) * (0) + (-2 * a0 * a3 + 2 * a1 * a2 - 2 * b0 *
      b3 + 2 * b1 * b2) * (-(-a0 ^ 2 - a1 ^ 2 + a2 ^ 2 + a3 ^ 2 - b0 ^ 2 - b1 ^ 2 + b2 ^ 2 + b3
      ^ 2)) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) ^ 2) * 0
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-(2 * a0 * b1 - 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2)) * (-2 * a0 * a2 - 2 * a1 * a3 -
      2 * b0 * b2 - 2 * b1 * b3) + (-(-2 * a0 * a1 - 2 * a2 * a3 - 2 * b0 * b1 - 2 * b2 * b3)) *
      (-2 * a0 * b2 + 2 * a1 * b3 + 2 * a2 * b0 - 2 * a3 * b1) + (0) * (-2 * a0 * a3 + 2 * a1 *
      a2 - 2 * b0 * b3 + 2 * b1 * b2) + (-a0 ^ 2 + a1 ^ 2 - a2 ^ 2 + a3 ^ 2 - b0 ^ 2 + b1 ^ 2 -
      b2 ^ 2 + b3 ^ 2) * (-2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 + 2 * a3 * b0) + (2 * a0 * b3
      - 2 * a1 * b2 + 2 * a2 * b1 - 2 * a3 * b0) * (-a0 ^ 2 - a1 ^ 2 + a2 ^ 2 + a3 ^ 2 - b0 ^ 2
      - b1 ^ 2 + b2 ^ 2 + b3 ^ 2) + (-2 * a0 * a3 + 2 * a1 * a2 - 2 * b0 * b3 + 2 * b1 * b2) *
      (0) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) ^ 2) * 0
    ring

theorem spinorMatrix_square_row3 (q : Fin 4 → ℂ) (j : Fin 6) :
    (spinorMatrix q * spinorMatrix q) 3 j =
      ((-(spinorNormSq q ^ 2)) • (1 : Matrix6)) 3 j := by
  let a0 : ℝ := (q 0).re
  let b0 : ℝ := (q 0).im
  let a1 : ℝ := (q 1).re
  let b1 : ℝ := (q 1).im
  let a2 : ℝ := (q 2).re
  let b2 : ℝ := (q 2).im
  let a3 : ℝ := (q 3).re
  let b3 : ℝ := (q 3).im
  fin_cases j
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-(-2 * a0 * a1 + 2 * a2 * a3 - 2 * b0 * b1 + 2 * b2 * b3)) * (0) + (-(-2 * a0 * b1 + 2 *
      a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2)) * (-(-a0 ^ 2 + a1 ^ 2 + a2 ^ 2 - a3 ^ 2 - b0 ^ 2 +
      b1 ^ 2 + b2 ^ 2 - b3 ^ 2)) + (-(-a0 ^ 2 + a1 ^ 2 - a2 ^ 2 + a3 ^ 2 - b0 ^ 2 + b1 ^ 2 - b2
      ^ 2 + b3 ^ 2)) * (-(2 * a0 * b1 - 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2)) + (0) * (-(-2
      * a0 * a1 + 2 * a2 * a3 - 2 * b0 * b1 + 2 * b2 * b3)) + (-2 * a0 * a3 - 2 * a1 * a2 - 2 *
      b0 * b3 - 2 * b1 * b2) * (-(2 * a0 * b2 + 2 * a1 * b3 - 2 * a2 * b0 - 2 * a3 * b1)) + (-2
      * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 + 2 * a3 * b0) * (-(-2 * a0 * a2 - 2 * a1 * a3 - 2 *
      b0 * b2 - 2 * b1 * b3)) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2
      + b3 ^ 2) ^ 2) * 0
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-(-2 * a0 * a1 + 2 * a2 * a3 - 2 * b0 * b1 + 2 * b2 * b3)) * (-a0 ^ 2 + a1 ^ 2 + a2 ^ 2 -
      a3 ^ 2 - b0 ^ 2 + b1 ^ 2 + b2 ^ 2 - b3 ^ 2) + (-(-2 * a0 * b1 + 2 * a1 * b0 - 2 * a2 * b3
      + 2 * a3 * b2)) * (0) + (-(-a0 ^ 2 + a1 ^ 2 - a2 ^ 2 + a3 ^ 2 - b0 ^ 2 + b1 ^ 2 - b2 ^ 2 +
      b3 ^ 2)) * (-(-2 * a0 * a1 - 2 * a2 * a3 - 2 * b0 * b1 - 2 * b2 * b3)) + (0) * (-(-2 * a0
      * b1 + 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2)) + (-2 * a0 * a3 - 2 * a1 * a2 - 2 * b0 *
      b3 - 2 * b1 * b2) * (-(-2 * a0 * a2 + 2 * a1 * a3 - 2 * b0 * b2 + 2 * b1 * b3)) + (-2 * a0
      * b3 - 2 * a1 * b2 + 2 * a2 * b1 + 2 * a3 * b0) * (-(-2 * a0 * b2 + 2 * a1 * b3 + 2 * a2 *
      b0 - 2 * a3 * b1)) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3
      ^ 2) ^ 2) * 0
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-(-2 * a0 * a1 + 2 * a2 * a3 - 2 * b0 * b1 + 2 * b2 * b3)) * (2 * a0 * b1 - 2 * a1 * b0 -
      2 * a2 * b3 + 2 * a3 * b2) + (-(-2 * a0 * b1 + 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2)) *
      (-2 * a0 * a1 - 2 * a2 * a3 - 2 * b0 * b1 - 2 * b2 * b3) + (-(-a0 ^ 2 + a1 ^ 2 - a2 ^ 2 +
      a3 ^ 2 - b0 ^ 2 + b1 ^ 2 - b2 ^ 2 + b3 ^ 2)) * (0) + (0) * (-(-a0 ^ 2 + a1 ^ 2 - a2 ^ 2 +
      a3 ^ 2 - b0 ^ 2 + b1 ^ 2 - b2 ^ 2 + b3 ^ 2)) + (-2 * a0 * a3 - 2 * a1 * a2 - 2 * b0 * b3 -
      2 * b1 * b2) * (-(2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 - 2 * a3 * b0)) + (-2 * a0 * b3
      - 2 * a1 * b2 + 2 * a2 * b1 + 2 * a3 * b0) * (-(-2 * a0 * a3 + 2 * a1 * a2 - 2 * b0 * b3 +
      2 * b1 * b2)) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2)
      ^ 2) * 0
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-(-2 * a0 * a1 + 2 * a2 * a3 - 2 * b0 * b1 + 2 * b2 * b3)) * (-2 * a0 * a1 + 2 * a2 * a3
      - 2 * b0 * b1 + 2 * b2 * b3) + (-(-2 * a0 * b1 + 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2))
      * (-2 * a0 * b1 + 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2) + (-(-a0 ^ 2 + a1 ^ 2 - a2 ^ 2
      + a3 ^ 2 - b0 ^ 2 + b1 ^ 2 - b2 ^ 2 + b3 ^ 2)) * (-a0 ^ 2 + a1 ^ 2 - a2 ^ 2 + a3 ^ 2 - b0
      ^ 2 + b1 ^ 2 - b2 ^ 2 + b3 ^ 2) + (0) * (0) + (-2 * a0 * a3 - 2 * a1 * a2 - 2 * b0 * b3 -
      2 * b1 * b2) * (-(-2 * a0 * a3 - 2 * a1 * a2 - 2 * b0 * b3 - 2 * b1 * b2)) + (-2 * a0 * b3
      - 2 * a1 * b2 + 2 * a2 * b1 + 2 * a3 * b0) * (-(-2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 +
      2 * a3 * b0)) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2)
      ^ 2) * 1
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-(-2 * a0 * a1 + 2 * a2 * a3 - 2 * b0 * b1 + 2 * b2 * b3)) * (2 * a0 * b2 + 2 * a1 * b3 -
      2 * a2 * b0 - 2 * a3 * b1) + (-(-2 * a0 * b1 + 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2)) *
      (-2 * a0 * a2 + 2 * a1 * a3 - 2 * b0 * b2 + 2 * b1 * b3) + (-(-a0 ^ 2 + a1 ^ 2 - a2 ^ 2 +
      a3 ^ 2 - b0 ^ 2 + b1 ^ 2 - b2 ^ 2 + b3 ^ 2)) * (2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 -
      2 * a3 * b0) + (0) * (-2 * a0 * a3 - 2 * a1 * a2 - 2 * b0 * b3 - 2 * b1 * b2) + (-2 * a0 *
      a3 - 2 * a1 * a2 - 2 * b0 * b3 - 2 * b1 * b2) * (0) + (-2 * a0 * b3 - 2 * a1 * b2 + 2 * a2
      * b1 + 2 * a3 * b0) * (-(-a0 ^ 2 - a1 ^ 2 + a2 ^ 2 + a3 ^ 2 - b0 ^ 2 - b1 ^ 2 + b2 ^ 2 +
      b3 ^ 2)) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) ^ 2)
      * 0
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-(-2 * a0 * a1 + 2 * a2 * a3 - 2 * b0 * b1 + 2 * b2 * b3)) * (-2 * a0 * a2 - 2 * a1 * a3
      - 2 * b0 * b2 - 2 * b1 * b3) + (-(-2 * a0 * b1 + 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2))
      * (-2 * a0 * b2 + 2 * a1 * b3 + 2 * a2 * b0 - 2 * a3 * b1) + (-(-a0 ^ 2 + a1 ^ 2 - a2 ^ 2
      + a3 ^ 2 - b0 ^ 2 + b1 ^ 2 - b2 ^ 2 + b3 ^ 2)) * (-2 * a0 * a3 + 2 * a1 * a2 - 2 * b0 * b3
      + 2 * b1 * b2) + (0) * (-2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 + 2 * a3 * b0) + (-2 * a0
      * a3 - 2 * a1 * a2 - 2 * b0 * b3 - 2 * b1 * b2) * (-a0 ^ 2 - a1 ^ 2 + a2 ^ 2 + a3 ^ 2 - b0
      ^ 2 - b1 ^ 2 + b2 ^ 2 + b3 ^ 2) + (-2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 + 2 * a3 * b0)
      * (0) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) ^ 2) * 0
    ring

theorem spinorMatrix_square_row4 (q : Fin 4 → ℂ) (j : Fin 6) :
    (spinorMatrix q * spinorMatrix q) 4 j =
      ((-(spinorNormSq q ^ 2)) • (1 : Matrix6)) 4 j := by
  let a0 : ℝ := (q 0).re
  let b0 : ℝ := (q 0).im
  let a1 : ℝ := (q 1).re
  let b1 : ℝ := (q 1).im
  let a2 : ℝ := (q 2).re
  let b2 : ℝ := (q 2).im
  let a3 : ℝ := (q 3).re
  let b3 : ℝ := (q 3).im
  fin_cases j
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-(2 * a0 * b2 + 2 * a1 * b3 - 2 * a2 * b0 - 2 * a3 * b1)) * (0) + (-(-2 * a0 * a2 + 2 *
      a1 * a3 - 2 * b0 * b2 + 2 * b1 * b3)) * (-(-a0 ^ 2 + a1 ^ 2 + a2 ^ 2 - a3 ^ 2 - b0 ^ 2 +
      b1 ^ 2 + b2 ^ 2 - b3 ^ 2)) + (-(2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 - 2 * a3 * b0)) *
      (-(2 * a0 * b1 - 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2)) + (-(-2 * a0 * a3 - 2 * a1 * a2
      - 2 * b0 * b3 - 2 * b1 * b2)) * (-(-2 * a0 * a1 + 2 * a2 * a3 - 2 * b0 * b1 + 2 * b2 *
      b3)) + (0) * (-(2 * a0 * b2 + 2 * a1 * b3 - 2 * a2 * b0 - 2 * a3 * b1)) + (-a0 ^ 2 - a1 ^
      2 + a2 ^ 2 + a3 ^ 2 - b0 ^ 2 - b1 ^ 2 + b2 ^ 2 + b3 ^ 2) * (-(-2 * a0 * a2 - 2 * a1 * a3 -
      2 * b0 * b2 - 2 * b1 * b3)) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3
      ^ 2 + b3 ^ 2) ^ 2) * 0
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-(2 * a0 * b2 + 2 * a1 * b3 - 2 * a2 * b0 - 2 * a3 * b1)) * (-a0 ^ 2 + a1 ^ 2 + a2 ^ 2 -
      a3 ^ 2 - b0 ^ 2 + b1 ^ 2 + b2 ^ 2 - b3 ^ 2) + (-(-2 * a0 * a2 + 2 * a1 * a3 - 2 * b0 * b2
      + 2 * b1 * b3)) * (0) + (-(2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 - 2 * a3 * b0)) * (-(-2
      * a0 * a1 - 2 * a2 * a3 - 2 * b0 * b1 - 2 * b2 * b3)) + (-(-2 * a0 * a3 - 2 * a1 * a2 - 2
      * b0 * b3 - 2 * b1 * b2)) * (-(-2 * a0 * b1 + 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2)) +
      (0) * (-(-2 * a0 * a2 + 2 * a1 * a3 - 2 * b0 * b2 + 2 * b1 * b3)) + (-a0 ^ 2 - a1 ^ 2 + a2
      ^ 2 + a3 ^ 2 - b0 ^ 2 - b1 ^ 2 + b2 ^ 2 + b3 ^ 2) * (-(-2 * a0 * b2 + 2 * a1 * b3 + 2 * a2
      * b0 - 2 * a3 * b1)) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 +
      b3 ^ 2) ^ 2) * 0
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-(2 * a0 * b2 + 2 * a1 * b3 - 2 * a2 * b0 - 2 * a3 * b1)) * (2 * a0 * b1 - 2 * a1 * b0 -
      2 * a2 * b3 + 2 * a3 * b2) + (-(-2 * a0 * a2 + 2 * a1 * a3 - 2 * b0 * b2 + 2 * b1 * b3)) *
      (-2 * a0 * a1 - 2 * a2 * a3 - 2 * b0 * b1 - 2 * b2 * b3) + (-(2 * a0 * b3 - 2 * a1 * b2 +
      2 * a2 * b1 - 2 * a3 * b0)) * (0) + (-(-2 * a0 * a3 - 2 * a1 * a2 - 2 * b0 * b3 - 2 * b1 *
      b2)) * (-(-a0 ^ 2 + a1 ^ 2 - a2 ^ 2 + a3 ^ 2 - b0 ^ 2 + b1 ^ 2 - b2 ^ 2 + b3 ^ 2)) + (0) *
      (-(2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 - 2 * a3 * b0)) + (-a0 ^ 2 - a1 ^ 2 + a2 ^ 2 +
      a3 ^ 2 - b0 ^ 2 - b1 ^ 2 + b2 ^ 2 + b3 ^ 2) * (-(-2 * a0 * a3 + 2 * a1 * a2 - 2 * b0 * b3
      + 2 * b1 * b2)) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^
      2) ^ 2) * 0
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-(2 * a0 * b2 + 2 * a1 * b3 - 2 * a2 * b0 - 2 * a3 * b1)) * (-2 * a0 * a1 + 2 * a2 * a3 -
      2 * b0 * b1 + 2 * b2 * b3) + (-(-2 * a0 * a2 + 2 * a1 * a3 - 2 * b0 * b2 + 2 * b1 * b3)) *
      (-2 * a0 * b1 + 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2) + (-(2 * a0 * b3 - 2 * a1 * b2 +
      2 * a2 * b1 - 2 * a3 * b0)) * (-a0 ^ 2 + a1 ^ 2 - a2 ^ 2 + a3 ^ 2 - b0 ^ 2 + b1 ^ 2 - b2 ^
      2 + b3 ^ 2) + (-(-2 * a0 * a3 - 2 * a1 * a2 - 2 * b0 * b3 - 2 * b1 * b2)) * (0) + (0) *
      (-(-2 * a0 * a3 - 2 * a1 * a2 - 2 * b0 * b3 - 2 * b1 * b2)) + (-a0 ^ 2 - a1 ^ 2 + a2 ^ 2 +
      a3 ^ 2 - b0 ^ 2 - b1 ^ 2 + b2 ^ 2 + b3 ^ 2) * (-(-2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1
      + 2 * a3 * b0)) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^
      2) ^ 2) * 0
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-(2 * a0 * b2 + 2 * a1 * b3 - 2 * a2 * b0 - 2 * a3 * b1)) * (2 * a0 * b2 + 2 * a1 * b3 -
      2 * a2 * b0 - 2 * a3 * b1) + (-(-2 * a0 * a2 + 2 * a1 * a3 - 2 * b0 * b2 + 2 * b1 * b3)) *
      (-2 * a0 * a2 + 2 * a1 * a3 - 2 * b0 * b2 + 2 * b1 * b3) + (-(2 * a0 * b3 - 2 * a1 * b2 +
      2 * a2 * b1 - 2 * a3 * b0)) * (2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 - 2 * a3 * b0) +
      (-(-2 * a0 * a3 - 2 * a1 * a2 - 2 * b0 * b3 - 2 * b1 * b2)) * (-2 * a0 * a3 - 2 * a1 * a2
      - 2 * b0 * b3 - 2 * b1 * b2) + (0) * (0) + (-a0 ^ 2 - a1 ^ 2 + a2 ^ 2 + a3 ^ 2 - b0 ^ 2 -
      b1 ^ 2 + b2 ^ 2 + b3 ^ 2) * (-(-a0 ^ 2 - a1 ^ 2 + a2 ^ 2 + a3 ^ 2 - b0 ^ 2 - b1 ^ 2 + b2 ^
      2 + b3 ^ 2)) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) ^
      2) * 1
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-(2 * a0 * b2 + 2 * a1 * b3 - 2 * a2 * b0 - 2 * a3 * b1)) * (-2 * a0 * a2 - 2 * a1 * a3 -
      2 * b0 * b2 - 2 * b1 * b3) + (-(-2 * a0 * a2 + 2 * a1 * a3 - 2 * b0 * b2 + 2 * b1 * b3)) *
      (-2 * a0 * b2 + 2 * a1 * b3 + 2 * a2 * b0 - 2 * a3 * b1) + (-(2 * a0 * b3 - 2 * a1 * b2 +
      2 * a2 * b1 - 2 * a3 * b0)) * (-2 * a0 * a3 + 2 * a1 * a2 - 2 * b0 * b3 + 2 * b1 * b2) +
      (-(-2 * a0 * a3 - 2 * a1 * a2 - 2 * b0 * b3 - 2 * b1 * b2)) * (-2 * a0 * b3 - 2 * a1 * b2
      + 2 * a2 * b1 + 2 * a3 * b0) + (0) * (-a0 ^ 2 - a1 ^ 2 + a2 ^ 2 + a3 ^ 2 - b0 ^ 2 - b1 ^ 2
      + b2 ^ 2 + b3 ^ 2) + (-a0 ^ 2 - a1 ^ 2 + a2 ^ 2 + a3 ^ 2 - b0 ^ 2 - b1 ^ 2 + b2 ^ 2 + b3 ^
      2) * (0) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) ^ 2)
      * 0
    ring

theorem spinorMatrix_square_row5 (q : Fin 4 → ℂ) (j : Fin 6) :
    (spinorMatrix q * spinorMatrix q) 5 j =
      ((-(spinorNormSq q ^ 2)) • (1 : Matrix6)) 5 j := by
  let a0 : ℝ := (q 0).re
  let b0 : ℝ := (q 0).im
  let a1 : ℝ := (q 1).re
  let b1 : ℝ := (q 1).im
  let a2 : ℝ := (q 2).re
  let b2 : ℝ := (q 2).im
  let a3 : ℝ := (q 3).re
  let b3 : ℝ := (q 3).im
  fin_cases j
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-(-2 * a0 * a2 - 2 * a1 * a3 - 2 * b0 * b2 - 2 * b1 * b3)) * (0) + (-(-2 * a0 * b2 + 2 *
      a1 * b3 + 2 * a2 * b0 - 2 * a3 * b1)) * (-(-a0 ^ 2 + a1 ^ 2 + a2 ^ 2 - a3 ^ 2 - b0 ^ 2 +
      b1 ^ 2 + b2 ^ 2 - b3 ^ 2)) + (-(-2 * a0 * a3 + 2 * a1 * a2 - 2 * b0 * b3 + 2 * b1 * b2)) *
      (-(2 * a0 * b1 - 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2)) + (-(-2 * a0 * b3 - 2 * a1 * b2
      + 2 * a2 * b1 + 2 * a3 * b0)) * (-(-2 * a0 * a1 + 2 * a2 * a3 - 2 * b0 * b1 + 2 * b2 *
      b3)) + (-(-a0 ^ 2 - a1 ^ 2 + a2 ^ 2 + a3 ^ 2 - b0 ^ 2 - b1 ^ 2 + b2 ^ 2 + b3 ^ 2)) * (-(2
      * a0 * b2 + 2 * a1 * b3 - 2 * a2 * b0 - 2 * a3 * b1)) + (0) * (-(-2 * a0 * a2 - 2 * a1 *
      a3 - 2 * b0 * b2 - 2 * b1 * b3)) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2
      + a3 ^ 2 + b3 ^ 2) ^ 2) * 0
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-(-2 * a0 * a2 - 2 * a1 * a3 - 2 * b0 * b2 - 2 * b1 * b3)) * (-a0 ^ 2 + a1 ^ 2 + a2 ^ 2 -
      a3 ^ 2 - b0 ^ 2 + b1 ^ 2 + b2 ^ 2 - b3 ^ 2) + (-(-2 * a0 * b2 + 2 * a1 * b3 + 2 * a2 * b0
      - 2 * a3 * b1)) * (0) + (-(-2 * a0 * a3 + 2 * a1 * a2 - 2 * b0 * b3 + 2 * b1 * b2)) *
      (-(-2 * a0 * a1 - 2 * a2 * a3 - 2 * b0 * b1 - 2 * b2 * b3)) + (-(-2 * a0 * b3 - 2 * a1 *
      b2 + 2 * a2 * b1 + 2 * a3 * b0)) * (-(-2 * a0 * b1 + 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 *
      b2)) + (-(-a0 ^ 2 - a1 ^ 2 + a2 ^ 2 + a3 ^ 2 - b0 ^ 2 - b1 ^ 2 + b2 ^ 2 + b3 ^ 2)) * (-(-2
      * a0 * a2 + 2 * a1 * a3 - 2 * b0 * b2 + 2 * b1 * b3)) + (0) * (-(-2 * a0 * b2 + 2 * a1 *
      b3 + 2 * a2 * b0 - 2 * a3 * b1)) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2
      + a3 ^ 2 + b3 ^ 2) ^ 2) * 0
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-(-2 * a0 * a2 - 2 * a1 * a3 - 2 * b0 * b2 - 2 * b1 * b3)) * (2 * a0 * b1 - 2 * a1 * b0 -
      2 * a2 * b3 + 2 * a3 * b2) + (-(-2 * a0 * b2 + 2 * a1 * b3 + 2 * a2 * b0 - 2 * a3 * b1)) *
      (-2 * a0 * a1 - 2 * a2 * a3 - 2 * b0 * b1 - 2 * b2 * b3) + (-(-2 * a0 * a3 + 2 * a1 * a2 -
      2 * b0 * b3 + 2 * b1 * b2)) * (0) + (-(-2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 + 2 * a3 *
      b0)) * (-(-a0 ^ 2 + a1 ^ 2 - a2 ^ 2 + a3 ^ 2 - b0 ^ 2 + b1 ^ 2 - b2 ^ 2 + b3 ^ 2)) +
      (-(-a0 ^ 2 - a1 ^ 2 + a2 ^ 2 + a3 ^ 2 - b0 ^ 2 - b1 ^ 2 + b2 ^ 2 + b3 ^ 2)) * (-(2 * a0 *
      b3 - 2 * a1 * b2 + 2 * a2 * b1 - 2 * a3 * b0)) + (0) * (-(-2 * a0 * a3 + 2 * a1 * a2 - 2 *
      b0 * b3 + 2 * b1 * b2)) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2
      + b3 ^ 2) ^ 2) * 0
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-(-2 * a0 * a2 - 2 * a1 * a3 - 2 * b0 * b2 - 2 * b1 * b3)) * (-2 * a0 * a1 + 2 * a2 * a3
      - 2 * b0 * b1 + 2 * b2 * b3) + (-(-2 * a0 * b2 + 2 * a1 * b3 + 2 * a2 * b0 - 2 * a3 * b1))
      * (-2 * a0 * b1 + 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2) + (-(-2 * a0 * a3 + 2 * a1 * a2
      - 2 * b0 * b3 + 2 * b1 * b2)) * (-a0 ^ 2 + a1 ^ 2 - a2 ^ 2 + a3 ^ 2 - b0 ^ 2 + b1 ^ 2 - b2
      ^ 2 + b3 ^ 2) + (-(-2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 + 2 * a3 * b0)) * (0) + (-(-a0
      ^ 2 - a1 ^ 2 + a2 ^ 2 + a3 ^ 2 - b0 ^ 2 - b1 ^ 2 + b2 ^ 2 + b3 ^ 2)) * (-(-2 * a0 * a3 - 2
      * a1 * a2 - 2 * b0 * b3 - 2 * b1 * b2)) + (0) * (-(-2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 *
      b1 + 2 * a3 * b0)) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3
      ^ 2) ^ 2) * 0
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-(-2 * a0 * a2 - 2 * a1 * a3 - 2 * b0 * b2 - 2 * b1 * b3)) * (2 * a0 * b2 + 2 * a1 * b3 -
      2 * a2 * b0 - 2 * a3 * b1) + (-(-2 * a0 * b2 + 2 * a1 * b3 + 2 * a2 * b0 - 2 * a3 * b1)) *
      (-2 * a0 * a2 + 2 * a1 * a3 - 2 * b0 * b2 + 2 * b1 * b3) + (-(-2 * a0 * a3 + 2 * a1 * a2 -
      2 * b0 * b3 + 2 * b1 * b2)) * (2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 - 2 * a3 * b0) +
      (-(-2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 + 2 * a3 * b0)) * (-2 * a0 * a3 - 2 * a1 * a2
      - 2 * b0 * b3 - 2 * b1 * b2) + (-(-a0 ^ 2 - a1 ^ 2 + a2 ^ 2 + a3 ^ 2 - b0 ^ 2 - b1 ^ 2 +
      b2 ^ 2 + b3 ^ 2)) * (0) + (0) * (-(-a0 ^ 2 - a1 ^ 2 + a2 ^ 2 + a3 ^ 2 - b0 ^ 2 - b1 ^ 2 +
      b2 ^ 2 + b3 ^ 2)) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^
      2) ^ 2) * 0
    ring
  · simp only [Matrix.mul_apply, sum_six]
    change
      (-(-2 * a0 * a2 - 2 * a1 * a3 - 2 * b0 * b2 - 2 * b1 * b3)) * (-2 * a0 * a2 - 2 * a1 * a3
      - 2 * b0 * b2 - 2 * b1 * b3) + (-(-2 * a0 * b2 + 2 * a1 * b3 + 2 * a2 * b0 - 2 * a3 * b1))
      * (-2 * a0 * b2 + 2 * a1 * b3 + 2 * a2 * b0 - 2 * a3 * b1) + (-(-2 * a0 * a3 + 2 * a1 * a2
      - 2 * b0 * b3 + 2 * b1 * b2)) * (-2 * a0 * a3 + 2 * a1 * a2 - 2 * b0 * b3 + 2 * b1 * b2) +
      (-(-2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 + 2 * a3 * b0)) * (-2 * a0 * b3 - 2 * a1 * b2
      + 2 * a2 * b1 + 2 * a3 * b0) + (-(-a0 ^ 2 - a1 ^ 2 + a2 ^ 2 + a3 ^ 2 - b0 ^ 2 - b1 ^ 2 +
      b2 ^ 2 + b3 ^ 2)) * (-a0 ^ 2 - a1 ^ 2 + a2 ^ 2 + a3 ^ 2 - b0 ^ 2 - b1 ^ 2 + b2 ^ 2 + b3 ^
      2) + (0) * (0) = -((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2)
      ^ 2) * 1
    ring

theorem spinorMatrix_square (q : Fin 4 → ℂ) :
    spinorMatrix q * spinorMatrix q = (-(spinorNormSq q ^ 2)) • (1 : Matrix6) := by
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact spinorMatrix_square_row0 q j
  · exact spinorMatrix_square_row1 q j
  · exact spinorMatrix_square_row2 q j
  · exact spinorMatrix_square_row3 q j
  · exact spinorMatrix_square_row4 q j
  · exact spinorMatrix_square_row5 q j

end NoExoticSixSphere.RankSixSkewMatrix
