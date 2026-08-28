import Wikipedia.NoExoticSixSphere.RankSixSpinorMatrix
import Wikipedia.NoExoticSixSphere.RankSixSpinInverse

/-!
# The spin matrix of a spinor

This identifies the homogeneous quadratic skew-six matrix with the
rank-one outer product of the spinor, after removing the scalar trace.
-/

namespace NoExoticSixSphere.RankSixSkewMatrix

def spinorOuter (q : Fin 4 → ℂ) : Matrix4 := fun i j ↦ q i * star (q j)

theorem spinorMatrix_spin_row0 (q : Fin 4 → ℂ) (j : Fin 4) :
    spin (spinorMatrix q) 0 j =
      ((4 : ℂ) • spinorOuter q - (spinorNormSq q : ℂ) • (1 : Matrix4)) 0 j := by
  let a0 : ℝ := (q 0).re
  let b0 : ℝ := (q 0).im
  let a1 : ℝ := (q 1).re
  let b1 : ℝ := (q 1).im
  let a2 : ℝ := (q 2).re
  let b2 : ℝ := (q 2).im
  let a3 : ℝ := (q 3).re
  let b3 : ℝ := (q 3).im
  fin_cases j
  · apply Complex.ext
    · change
        -(-a0 ^ 2 + a1 ^ 2 + a2 ^ 2 - a3 ^ 2 - b0 ^ 2 + b1 ^ 2 + b2 ^ 2 - b3 ^ 2) - (-a0 ^ 2 +
        a1 ^ 2 - a2 ^ 2 + a3 ^ 2 - b0 ^ 2 + b1 ^ 2 - b2 ^ 2 + b3 ^ 2) - (-a0 ^ 2 - a1 ^ 2 + a2 ^
        2 + a3 ^ 2 - b0 ^ 2 - b1 ^ 2 + b2 ^ 2 + b3 ^ 2) = (4 * (a0 * a0 - b0 * (-b0)) - 0 * (a0
        * (-b0) + b0 * a0)) - ((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 +
        b3 ^ 2) * 1 - 0 * 0)
      ring
    · change
        0 = (4 * (a0 * (-b0) + b0 * a0) + 0 * (a0 * a0 - b0 * (-b0))) - ((a0 ^ 2 + b0 ^ 2 + a1 ^
        2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) * 0 + 0 * 1)
      ring
  · apply Complex.ext
    · change
        -(-2 * a0 * a1 + 2 * a2 * a3 - 2 * b0 * b1 + 2 * b2 * b3) - (-2 * a0 * a1 - 2 * a2 * a3
        - 2 * b0 * b1 - 2 * b2 * b3) = (4 * (a0 * a1 - b0 * (-b1)) - 0 * (a0 * (-b1) + b0 * a1))
        - ((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) * 0 - 0 * 0)
      ring
    · change
        -(2 * a0 * b1 - 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2) + (-2 * a0 * b1 + 2 * a1 * b0 -
        2 * a2 * b3 + 2 * a3 * b2) = (4 * (a0 * (-b1) + b0 * a1) + 0 * (a0 * a1 - b0 * (-b1))) -
        ((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) * 0 + 0 * 0)
      ring
  · apply Complex.ext
    · change
        -(-2 * a0 * a2 - 2 * a1 * a3 - 2 * b0 * b2 - 2 * b1 * b3) - (-2 * a0 * a2 + 2 * a1 * a3
        - 2 * b0 * b2 + 2 * b1 * b3) = (4 * (a0 * a2 - b0 * (-b2)) - 0 * (a0 * (-b2) + b0 * a2))
        - ((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) * 0 - 0 * 0)
      ring
    · change
        -(2 * a0 * b2 + 2 * a1 * b3 - 2 * a2 * b0 - 2 * a3 * b1) + (-2 * a0 * b2 + 2 * a1 * b3 +
        2 * a2 * b0 - 2 * a3 * b1) = (4 * (a0 * (-b2) + b0 * a2) + 0 * (a0 * a2 - b0 * (-b2))) -
        ((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) * 0 + 0 * 0)
      ring
  · apply Complex.ext
    · change
        -(-2 * a0 * a3 + 2 * a1 * a2 - 2 * b0 * b3 + 2 * b1 * b2) - (-2 * a0 * a3 - 2 * a1 * a2
        - 2 * b0 * b3 - 2 * b1 * b2) = (4 * (a0 * a3 - b0 * (-b3)) - 0 * (a0 * (-b3) + b0 * a3))
        - ((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) * 0 - 0 * 0)
      ring
    · change
        -(2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 - 2 * a3 * b0) + (-2 * a0 * b3 - 2 * a1 * b2 +
        2 * a2 * b1 + 2 * a3 * b0) = (4 * (a0 * (-b3) + b0 * a3) + 0 * (a0 * a3 - b0 * (-b3))) -
        ((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) * 0 + 0 * 0)
      ring

theorem spinorMatrix_spin_row1 (q : Fin 4 → ℂ) (j : Fin 4) :
    spin (spinorMatrix q) 1 j =
      ((4 : ℂ) • spinorOuter q - (spinorNormSq q : ℂ) • (1 : Matrix4)) 1 j := by
  let a0 : ℝ := (q 0).re
  let b0 : ℝ := (q 0).im
  let a1 : ℝ := (q 1).re
  let b1 : ℝ := (q 1).im
  let a2 : ℝ := (q 2).re
  let b2 : ℝ := (q 2).im
  let a3 : ℝ := (q 3).re
  let b3 : ℝ := (q 3).im
  fin_cases j
  · apply Complex.ext
    · change
        -(-2 * a0 * a1 + 2 * a2 * a3 - 2 * b0 * b1 + 2 * b2 * b3) - (-2 * a0 * a1 - 2 * a2 * a3
        - 2 * b0 * b1 - 2 * b2 * b3) = (4 * (a1 * a0 - b1 * (-b0)) - 0 * (a1 * (-b0) + b1 * a0))
        - ((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) * 0 - 0 * 0)
      ring
    · change
        (2 * a0 * b1 - 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2) - (-2 * a0 * b1 + 2 * a1 * b0 -
        2 * a2 * b3 + 2 * a3 * b2) = (4 * (a1 * (-b0) + b1 * a0) + 0 * (a1 * a0 - b1 * (-b0))) -
        ((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) * 0 + 0 * 0)
      ring
  · apply Complex.ext
    · change
        (-a0 ^ 2 + a1 ^ 2 + a2 ^ 2 - a3 ^ 2 - b0 ^ 2 + b1 ^ 2 + b2 ^ 2 - b3 ^ 2) + (-a0 ^ 2 + a1
        ^ 2 - a2 ^ 2 + a3 ^ 2 - b0 ^ 2 + b1 ^ 2 - b2 ^ 2 + b3 ^ 2) - (-a0 ^ 2 - a1 ^ 2 + a2 ^ 2
        + a3 ^ 2 - b0 ^ 2 - b1 ^ 2 + b2 ^ 2 + b3 ^ 2) = (4 * (a1 * a1 - b1 * (-b1)) - 0 * (a1 *
        (-b1) + b1 * a1)) - ((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3
        ^ 2) * 1 - 0 * 0)
      ring
    · change
        0 = (4 * (a1 * (-b1) + b1 * a1) + 0 * (a1 * a1 - b1 * (-b1))) - ((a0 ^ 2 + b0 ^ 2 + a1 ^
        2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) * 0 + 0 * 1)
      ring
  · apply Complex.ext
    · change
        (-2 * a0 * a3 + 2 * a1 * a2 - 2 * b0 * b3 + 2 * b1 * b2) - (-2 * a0 * a3 - 2 * a1 * a2 -
        2 * b0 * b3 - 2 * b1 * b2) = (4 * (a1 * a2 - b1 * (-b2)) - 0 * (a1 * (-b2) + b1 * a2)) -
        ((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) * 0 - 0 * 0)
      ring
    · change
        (2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 - 2 * a3 * b0) + (-2 * a0 * b3 - 2 * a1 * b2 +
        2 * a2 * b1 + 2 * a3 * b0) = (4 * (a1 * (-b2) + b1 * a2) + 0 * (a1 * a2 - b1 * (-b2))) -
        ((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) * 0 + 0 * 0)
      ring
  · apply Complex.ext
    · change
        -(-2 * a0 * a2 - 2 * a1 * a3 - 2 * b0 * b2 - 2 * b1 * b3) + (-2 * a0 * a2 + 2 * a1 * a3
        - 2 * b0 * b2 + 2 * b1 * b3) = (4 * (a1 * a3 - b1 * (-b3)) - 0 * (a1 * (-b3) + b1 * a3))
        - ((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) * 0 - 0 * 0)
      ring
    · change
        -(2 * a0 * b2 + 2 * a1 * b3 - 2 * a2 * b0 - 2 * a3 * b1) - (-2 * a0 * b2 + 2 * a1 * b3 +
        2 * a2 * b0 - 2 * a3 * b1) = (4 * (a1 * (-b3) + b1 * a3) + 0 * (a1 * a3 - b1 * (-b3))) -
        ((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) * 0 + 0 * 0)
      ring

theorem spinorMatrix_spin_row2 (q : Fin 4 → ℂ) (j : Fin 4) :
    spin (spinorMatrix q) 2 j =
      ((4 : ℂ) • spinorOuter q - (spinorNormSq q : ℂ) • (1 : Matrix4)) 2 j := by
  let a0 : ℝ := (q 0).re
  let b0 : ℝ := (q 0).im
  let a1 : ℝ := (q 1).re
  let b1 : ℝ := (q 1).im
  let a2 : ℝ := (q 2).re
  let b2 : ℝ := (q 2).im
  let a3 : ℝ := (q 3).re
  let b3 : ℝ := (q 3).im
  fin_cases j
  · apply Complex.ext
    · change
        -(-2 * a0 * a2 - 2 * a1 * a3 - 2 * b0 * b2 - 2 * b1 * b3) - (-2 * a0 * a2 + 2 * a1 * a3
        - 2 * b0 * b2 + 2 * b1 * b3) = (4 * (a2 * a0 - b2 * (-b0)) - 0 * (a2 * (-b0) + b2 * a0))
        - ((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) * 0 - 0 * 0)
      ring
    · change
        (2 * a0 * b2 + 2 * a1 * b3 - 2 * a2 * b0 - 2 * a3 * b1) - (-2 * a0 * b2 + 2 * a1 * b3 +
        2 * a2 * b0 - 2 * a3 * b1) = (4 * (a2 * (-b0) + b2 * a0) + 0 * (a2 * a0 - b2 * (-b0))) -
        ((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) * 0 + 0 * 0)
      ring
  · apply Complex.ext
    · change
        (-2 * a0 * a3 + 2 * a1 * a2 - 2 * b0 * b3 + 2 * b1 * b2) - (-2 * a0 * a3 - 2 * a1 * a2 -
        2 * b0 * b3 - 2 * b1 * b2) = (4 * (a2 * a1 - b2 * (-b1)) - 0 * (a2 * (-b1) + b2 * a1)) -
        ((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) * 0 - 0 * 0)
      ring
    · change
        -(2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 - 2 * a3 * b0) - (-2 * a0 * b3 - 2 * a1 * b2 +
        2 * a2 * b1 + 2 * a3 * b0) = (4 * (a2 * (-b1) + b2 * a1) + 0 * (a2 * a1 - b2 * (-b1))) -
        ((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) * 0 + 0 * 0)
      ring
  · apply Complex.ext
    · change
        (-a0 ^ 2 + a1 ^ 2 + a2 ^ 2 - a3 ^ 2 - b0 ^ 2 + b1 ^ 2 + b2 ^ 2 - b3 ^ 2) - (-a0 ^ 2 + a1
        ^ 2 - a2 ^ 2 + a3 ^ 2 - b0 ^ 2 + b1 ^ 2 - b2 ^ 2 + b3 ^ 2) + (-a0 ^ 2 - a1 ^ 2 + a2 ^ 2
        + a3 ^ 2 - b0 ^ 2 - b1 ^ 2 + b2 ^ 2 + b3 ^ 2) = (4 * (a2 * a2 - b2 * (-b2)) - 0 * (a2 *
        (-b2) + b2 * a2)) - ((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3
        ^ 2) * 1 - 0 * 0)
      ring
    · change
        0 = (4 * (a2 * (-b2) + b2 * a2) + 0 * (a2 * a2 - b2 * (-b2))) - ((a0 ^ 2 + b0 ^ 2 + a1 ^
        2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) * 0 + 0 * 1)
      ring
  · apply Complex.ext
    · change
        (-2 * a0 * a1 + 2 * a2 * a3 - 2 * b0 * b1 + 2 * b2 * b3) - (-2 * a0 * a1 - 2 * a2 * a3 -
        2 * b0 * b1 - 2 * b2 * b3) = (4 * (a2 * a3 - b2 * (-b3)) - 0 * (a2 * (-b3) + b2 * a3)) -
        ((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) * 0 - 0 * 0)
      ring
    · change
        (2 * a0 * b1 - 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2) + (-2 * a0 * b1 + 2 * a1 * b0 -
        2 * a2 * b3 + 2 * a3 * b2) = (4 * (a2 * (-b3) + b2 * a3) + 0 * (a2 * a3 - b2 * (-b3))) -
        ((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) * 0 + 0 * 0)
      ring

theorem spinorMatrix_spin_row3 (q : Fin 4 → ℂ) (j : Fin 4) :
    spin (spinorMatrix q) 3 j =
      ((4 : ℂ) • spinorOuter q - (spinorNormSq q : ℂ) • (1 : Matrix4)) 3 j := by
  let a0 : ℝ := (q 0).re
  let b0 : ℝ := (q 0).im
  let a1 : ℝ := (q 1).re
  let b1 : ℝ := (q 1).im
  let a2 : ℝ := (q 2).re
  let b2 : ℝ := (q 2).im
  let a3 : ℝ := (q 3).re
  let b3 : ℝ := (q 3).im
  fin_cases j
  · apply Complex.ext
    · change
        -(-2 * a0 * a3 + 2 * a1 * a2 - 2 * b0 * b3 + 2 * b1 * b2) - (-2 * a0 * a3 - 2 * a1 * a2
        - 2 * b0 * b3 - 2 * b1 * b2) = (4 * (a3 * a0 - b3 * (-b0)) - 0 * (a3 * (-b0) + b3 * a0))
        - ((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) * 0 - 0 * 0)
      ring
    · change
        (2 * a0 * b3 - 2 * a1 * b2 + 2 * a2 * b1 - 2 * a3 * b0) - (-2 * a0 * b3 - 2 * a1 * b2 +
        2 * a2 * b1 + 2 * a3 * b0) = (4 * (a3 * (-b0) + b3 * a0) + 0 * (a3 * a0 - b3 * (-b0))) -
        ((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) * 0 + 0 * 0)
      ring
  · apply Complex.ext
    · change
        -(-2 * a0 * a2 - 2 * a1 * a3 - 2 * b0 * b2 - 2 * b1 * b3) + (-2 * a0 * a2 + 2 * a1 * a3
        - 2 * b0 * b2 + 2 * b1 * b3) = (4 * (a3 * a1 - b3 * (-b1)) - 0 * (a3 * (-b1) + b3 * a1))
        - ((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) * 0 - 0 * 0)
      ring
    · change
        (2 * a0 * b2 + 2 * a1 * b3 - 2 * a2 * b0 - 2 * a3 * b1) + (-2 * a0 * b2 + 2 * a1 * b3 +
        2 * a2 * b0 - 2 * a3 * b1) = (4 * (a3 * (-b1) + b3 * a1) + 0 * (a3 * a1 - b3 * (-b1))) -
        ((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) * 0 + 0 * 0)
      ring
  · apply Complex.ext
    · change
        (-2 * a0 * a1 + 2 * a2 * a3 - 2 * b0 * b1 + 2 * b2 * b3) - (-2 * a0 * a1 - 2 * a2 * a3 -
        2 * b0 * b1 - 2 * b2 * b3) = (4 * (a3 * a2 - b3 * (-b2)) - 0 * (a3 * (-b2) + b3 * a2)) -
        ((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) * 0 - 0 * 0)
      ring
    · change
        -(2 * a0 * b1 - 2 * a1 * b0 - 2 * a2 * b3 + 2 * a3 * b2) - (-2 * a0 * b1 + 2 * a1 * b0 -
        2 * a2 * b3 + 2 * a3 * b2) = (4 * (a3 * (-b2) + b3 * a2) + 0 * (a3 * a2 - b3 * (-b2))) -
        ((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) * 0 + 0 * 0)
      ring
  · apply Complex.ext
    · change
        -(-a0 ^ 2 + a1 ^ 2 + a2 ^ 2 - a3 ^ 2 - b0 ^ 2 + b1 ^ 2 + b2 ^ 2 - b3 ^ 2) + (-a0 ^ 2 +
        a1 ^ 2 - a2 ^ 2 + a3 ^ 2 - b0 ^ 2 + b1 ^ 2 - b2 ^ 2 + b3 ^ 2) + (-a0 ^ 2 - a1 ^ 2 + a2 ^
        2 + a3 ^ 2 - b0 ^ 2 - b1 ^ 2 + b2 ^ 2 + b3 ^ 2) = (4 * (a3 * a3 - b3 * (-b3)) - 0 * (a3
        * (-b3) + b3 * a3)) - ((a0 ^ 2 + b0 ^ 2 + a1 ^ 2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 +
        b3 ^ 2) * 1 - 0 * 0)
      ring
    · change
        0 = (4 * (a3 * (-b3) + b3 * a3) + 0 * (a3 * a3 - b3 * (-b3))) - ((a0 ^ 2 + b0 ^ 2 + a1 ^
        2 + b1 ^ 2 + a2 ^ 2 + b2 ^ 2 + a3 ^ 2 + b3 ^ 2) * 0 + 0 * 1)
      ring

theorem spinorMatrix_spin (q : Fin 4 → ℂ) :
    spin (spinorMatrix q) =
      (4 : ℂ) • spinorOuter q - (spinorNormSq q : ℂ) • (1 : Matrix4) := by
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact spinorMatrix_spin_row0 q j
  · exact spinorMatrix_spin_row1 q j
  · exact spinorMatrix_spin_row2 q j
  · exact spinorMatrix_spin_row3 q j

end NoExoticSixSphere.RankSixSkewMatrix
