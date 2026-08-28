import Wikipedia.HopfProblem.ToricFan

/-!
# Integral characters separating the cusp charts

The A₂ triangles are cut out by the three pencils of integral lines
`x = n`, `y = n`, and `x + y = n`. Their strip indices give an explicit
integral character nonnegative on one cone and nonpositive on another.
It is strictly positive on every ray excluded from the chart overlap.
These are the separation data needed to prove Hausdorffness of the gluing.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.ToricSeparation

open ToricCharts ToricFan Triangle

def stripIndex (s : Triangle) : Fin 3 → ℤ :=
  ![s.a, s.b, s.a + s.b + if s.upper then 1 else 0]

def pencil (k : Fin 3) (x : Fin 3 → ℤ) : ℤ := ![x 0, x 1, x 0 + x 1] k

def sign (a b : ℤ) : ℤ := if a < b then -1 else if b < a then 1 else 0

def stripValue (a b x : ℤ) : ℤ := sign a b * (2 * x - a - b - 1)

theorem sign_swap (a b : ℤ) : sign b a = -sign a b := by
  unfold sign
  split_ifs <;> omega

theorem stripValue_nonneg {a b x : ℤ} (hx : a ≤ x ∧ x ≤ a + 1) :
    0 ≤ stripValue a b x := by
  unfold stripValue sign
  split_ifs <;> omega

theorem stripValue_zero_bounds {a b x : ℤ} (hx : a ≤ x ∧ x ≤ a + 1)
    (hzero : stripValue a b x = 0) : b ≤ x ∧ x ≤ b + 1 := by
  unfold stripValue sign at hzero
  split_ifs at hzero <;> omega

theorem ray_strip_bounds (s : Triangle) (j k : Fin 3) :
    stripIndex s k ≤ pencil k (fun i => s.rays i j) ∧
      pencil k (fun i => s.rays i j) ≤ stripIndex s k + 1 := by
  cases h : s.upper <;> fin_cases j <;> fin_cases k <;>
    simp [stripIndex, pencil, rays, h] <;> omega

theorem transition_nonneg_of_bounds (s t : Triangle) (j : Fin 3)
    (h : ∀ k, stripIndex t k ≤ pencil k (fun i => s.rays i j) ∧
      pencil k (fun i => s.rays i j) ≤ stripIndex t k + 1) :
    ∀ i, 0 ≤ transition s t i j := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  intro i
  cases ht : t.upper <;> fin_cases i <;>
    simp [transition, dual, ht, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    simp [stripIndex, pencil, ht] at h0 h1 h2 <;> omega

/-- The homogeneous integral character obtained by adding the three
strip-separating affine functions. -/
def character (s t : Triangle) : Fin 3 → ℤ :=
  let e : Fin 3 → ℤ := fun k => sign (stripIndex s k) (stripIndex t k)
  ![2 * (e 0 + e 2), 2 * (e 1 + e 2),
    -(e 0 * (stripIndex s 0 + stripIndex t 0 + 1) +
      e 1 * (stripIndex s 1 + stripIndex t 1 + 1) +
      e 2 * (stripIndex s 2 + stripIndex t 2 + 1))]

theorem character_swap (s t : Triangle) : character t s = -character s t := by
  have he (k : Fin 3) : sign (stripIndex t k) (stripIndex s k) =
      -sign (stripIndex s k) (stripIndex t k) := sign_swap _ _
  unfold character
  simp only [he]
  ext i
  fin_cases i <;> dsimp <;> ring

/-- Its exponents in the source chart are nonnegative integers. -/
def exponents (s t : Triangle) : Fin 3 → ℤ := character s t ᵥ* s.rays

theorem exponents_eq_sum (s t : Triangle) (j : Fin 3) :
    exponents s t j = ∑ k, stripValue (stripIndex s k) (stripIndex t k)
      (pencil k (fun i => s.rays i j)) := by
  simp [exponents, character, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
    stripValue, pencil]
  ring

theorem exponents_nonneg (s t : Triangle) (j : Fin 3) : 0 ≤ exponents s t j := by
  rw [exponents_eq_sum]
  exact Finset.sum_nonneg fun k _ => stripValue_nonneg (ray_strip_bounds s j k)

theorem transition_nonneg_of_exponent_zero (s t : Triangle) (j : Fin 3)
    (hzero : exponents s t j = 0) : ∀ i, 0 ≤ transition s t i j := by
  apply transition_nonneg_of_bounds s t j
  intro k
  apply stripValue_zero_bounds (ray_strip_bounds s j k)
  rw [exponents_eq_sum] at hzero
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun k _ => stripValue_nonneg (ray_strip_bounds s j k))).mp hzero k (Finset.mem_univ k)

theorem exponents_pos_of_transition_neg (s t : Triangle) (i j : Fin 3)
    (hneg : transition s t i j < 0) : 0 < exponents s t j := by
  have hn := exponents_nonneg s t j
  by_contra h
  have hz : exponents s t j = 0 := by omega
  exact (not_lt_of_ge (transition_nonneg_of_exponent_zero s t j hz i)) hneg

theorem exponents_transition (s t : Triangle) :
    exponents t s ᵥ* transition s t = -exponents s t := by
  rw [exponents, character_swap, Matrix.vecMul_vecMul, transition_covariance]
  simp [exponents, Matrix.neg_vecMul]

theorem exponents_cancel (s t : Triangle) (j : Fin 3) :
    exponents s t j + ∑ i, exponents t s i * transition s t i j = 0 := by
  have h := congrFun (exponents_transition s t) j
  change (∑ i, exponents t s i * transition s t i j) = -exponents s t j at h
  omega

end Wikipedia.HopfProblem.ToricSeparation
