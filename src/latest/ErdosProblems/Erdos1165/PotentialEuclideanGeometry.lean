/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.PotentialRadialMass
import ErdosProblems.Erdos1165.EndpointDiagonal

/-!
# Euclidean geometry for diagonal walk coordinates

The even-time Fourier factorization uses the half-diagonal coordinates
`(|x₁+x₂|/2, |x₁-x₂|/2)`.  This file records their exact relation
to the ordinary Euclidean radius, independently of any asymptotic estimate.
-/

open Real

namespace Erdos1165
namespace PotentialEuclideanGeometry

open EndpointDiagonal PotentialRadialMass

/-- Squared Euclidean radius, as a real number. -/
noncomputable def euclideanRadiusSq (x : Point) : ℝ :=
  (x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2

/-- Ordinary Euclidean radius of a lattice point. -/
noncomputable def euclideanRadius (x : Point) : ℝ :=
  Real.sqrt (euclideanRadiusSq x)

/-- Euclidean radius in the half-diagonal coordinate plane. -/
noncomputable def diagonalRadius (d e : ℕ) : ℝ :=
  Real.sqrt (radiusSq d e : ℝ)

theorem euclideanRadiusSq_nonneg (x : Point) : 0 ≤ euclideanRadiusSq x := by
  unfold euclideanRadiusSq
  positivity

theorem euclideanRadius_nonneg (x : Point) : 0 ≤ euclideanRadius x :=
  Real.sqrt_nonneg _

theorem euclideanRadius_sq (x : Point) :
    euclideanRadius x ^ 2 = euclideanRadiusSq x := by
  exact Real.sq_sqrt (euclideanRadiusSq_nonneg x)

theorem euclideanRadius_pos_iff (x : Point) : 0 < euclideanRadius x ↔ x ≠ 0 := by
  unfold euclideanRadius
  rw [Real.sqrt_pos]
  constructor
  · intro h hx
    subst x
    simp [euclideanRadiusSq] at h
  · intro hx
    unfold euclideanRadiusSq
    have : x.1 ≠ 0 ∨ x.2 ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (Prod.ext h.1 h.2)
    rcases this with h | h
    · nlinarith [sq_pos_of_ne_zero (by exact_mod_cast h : (x.1 : ℝ) ≠ 0)]
    · nlinarith [sq_pos_of_ne_zero (by exact_mod_cast h : (x.2 : ℝ) ≠ 0)]

theorem diagonalRadius_nonneg (d e : ℕ) : 0 ≤ diagonalRadius d e :=
  Real.sqrt_nonneg _

theorem diagonalRadius_sq (d e : ℕ) :
    diagonalRadius d e ^ 2 = (radiusSq d e : ℝ) := by
  apply Real.sq_sqrt
  unfold radiusSq
  positivity

/-- Exact Pythagorean relation between Cartesian and half-diagonal
coordinates. -/
theorem diagonal_sq_sum_eq_cartesian_half_of_even {x : Point}
    (hx : Even (x.1 + x.2)) :
    ((firstDiagonalOffset x : ℕ) : ℝ) ^ 2 +
        ((secondDiagonalOffset x : ℕ) : ℝ) ^ 2 =
      euclideanRadiusSq x / 2 := by
  obtain ⟨a, ha⟩ := hx
  let b : ℤ := x.1 - a
  have hb : x.1 - x.2 = b + b := by
    dsimp [b]
    omega
  have hfirst : firstDiagonalOffset x = a.natAbs := by
    rw [firstDiagonalOffset, ha, natAbs_add_self_div_two]
  have hsecond : secondDiagonalOffset x = b.natAbs := by
    rw [secondDiagonalOffset, hb, natAbs_add_self_div_two]
  have hx1 : x.1 = a + b := by
    dsimp [b]
    omega
  have hx2 : x.2 = a - b := by
    dsimp [b]
    omega
  have haabs : ((a.natAbs : ℕ) : ℝ) = |(a : ℝ)| := by
    have h := congrArg (fun z : ℤ ↦ (z : ℝ)) (Int.natCast_natAbs a)
    simpa using h
  have hbabs : ((b.natAbs : ℕ) : ℝ) = |(b : ℝ)| := by
    have h := congrArg (fun z : ℤ ↦ (z : ℝ)) (Int.natCast_natAbs b)
    simpa using h
  rw [hfirst, hsecond, haabs, hbabs]
  unfold euclideanRadiusSq
  rw [hx1, hx2]
  push_cast
  rw [sq_abs, sq_abs]
  ring

theorem radiusSq_diagonalOffsets_eq_cartesian_half_of_even {x : Point}
    (hx : Even (x.1 + x.2)) :
    (radiusSq (firstDiagonalOffset x) (secondDiagonalOffset x) : ℝ) =
      euclideanRadiusSq x / 2 := by
  simpa [radiusSq] using diagonal_sq_sum_eq_cartesian_half_of_even hx

/-- The Cartesian radius is `sqrt 2` times the half-diagonal radius. -/
theorem euclideanRadius_eq_sqrt_two_mul_diagonalRadius_of_even {x : Point}
    (hx : Even (x.1 + x.2)) :
    euclideanRadius x = Real.sqrt 2 *
      diagonalRadius (firstDiagonalOffset x) (secondDiagonalOffset x) := by
  have hsq := radiusSq_diagonalOffsets_eq_cartesian_half_of_even hx
  unfold euclideanRadius diagonalRadius
  rw [show euclideanRadiusSq x = 2 *
      (radiusSq (firstDiagonalOffset x) (secondDiagonalOffset x) : ℝ) by
        linarith]
  exact Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) _

/-- `sqrt 2` contributes half of `log 2`. -/
theorem log_sqrt_two : Real.log (Real.sqrt 2) = Real.log 2 / 2 := by
  rw [Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem log_euclideanRadius_eq_of_even {x : Point}
    (hx : Even (x.1 + x.2))
    (hdiag : 0 < diagonalRadius (firstDiagonalOffset x) (secondDiagonalOffset x)) :
    Real.log (euclideanRadius x) =
      Real.log (diagonalRadius (firstDiagonalOffset x) (secondDiagonalOffset x)) +
        Real.log 2 / 2 := by
  rw [euclideanRadius_eq_sqrt_two_mul_diagonalRadius_of_even hx,
    Real.log_mul (by positivity : Real.sqrt (2 : ℝ) ≠ 0) hdiag.ne', log_sqrt_two]
  ring

end PotentialEuclideanGeometry
end Erdos1165
