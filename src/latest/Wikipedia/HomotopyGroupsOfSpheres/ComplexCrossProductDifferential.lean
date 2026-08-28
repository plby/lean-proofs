import Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductTrace
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # The actual derivative of the polynomial cross-product map

The formulas are valid for arbitrary differentiable ambient curves. They
therefore apply to curves on the unit sphere without a choice of chart.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

def matrixVariation (z v : Vector) : Matrix (Fin 3) (Fin 3) ℂ :=
  outer v z + outer z v + crossMatrix (fun r ↦ star (v r))

def symmetricMatrix (z : Vector) : Matrix (Fin 3) (Fin 3) ℂ :=
  matrix z * (matrix z).transpose

def symmetricVariation (z v : Vector) : Matrix (Fin 3) (Fin 3) ℂ :=
  matrixVariation z v * (matrix z).transpose + matrix z * (matrixVariation z v).transpose

def squareSumVariation (z v : Vector) : ℂ := ∑ r, 2 * z r * v r

theorem hasDerivAt_crossMatrix_entry (z : ℝ → Vector) (v : Vector) (x : ℝ)
    (hz : ∀ r, HasDerivAt (fun t ↦ z t r) (v r) x) (r s : Fin 3) :
    HasDerivAt (fun t ↦ crossMatrix (z t) r s) (crossMatrix v r s) x := by
  fin_cases r <;> fin_cases s
  all_goals first
    | exact hasDerivAt_const x 0
    | exact hz 0
    | exact hz 1
    | exact hz 2
    | exact (hz 0).neg
    | exact (hz 1).neg
    | exact (hz 2).neg

theorem hasDerivAt_matrix_entry (z : ℝ → Vector) (v : Vector) (x : ℝ)
    (hz : ∀ r, HasDerivAt (fun t ↦ z t r) (v r) x) (r s : Fin 3) :
    HasDerivAt (fun t ↦ matrix (z t) r s) (matrixVariation (z x) v r s) x := by
  have hc := hasDerivAt_crossMatrix_entry (fun t r ↦ star (z t r))
    (fun r ↦ star (v r)) x (fun r ↦ (hz r).star) r s
  change HasDerivAt
    (fun t ↦ z t r * z t s + crossMatrix (fun k ↦ star (z t k)) r s)
    (v r * z x s + z x r * v s + crossMatrix (fun k ↦ star (v k)) r s) x
  exact ((hz r).mul (hz s)).add hc

theorem hasDerivAt_matrix (z : ℝ → Vector) (v : Vector) (x : ℝ)
    (hz : ∀ r, HasDerivAt (fun t ↦ z t r) (v r) x) :
    HasDerivAt (fun t ↦ matrix (z t)) (matrixVariation (z x) v) x := by
  apply hasDerivAt_pi.mpr
  intro r
  exact hasDerivAt_pi.mpr (fun s ↦ hasDerivAt_matrix_entry z v x hz r s)

theorem hasDerivAt_symmetricMatrix_entry (z : ℝ → Vector) (v : Vector) (x : ℝ)
    (hz : ∀ r, HasDerivAt (fun t ↦ z t r) (v r) x) (r s : Fin 3) :
    HasDerivAt (fun t ↦ symmetricMatrix (z t) r s)
      (symmetricVariation (z x) v r s) x := by
  have he := HasDerivAt.fun_sum (u := Finset.univ) (fun k (_ : k ∈ Finset.univ) ↦
    (hasDerivAt_matrix_entry z v x hz r k).mul (hasDerivAt_matrix_entry z v x hz s k))
  have hd : symmetricVariation (z x) v r s =
      ∑ k, (matrixVariation (z x) v r k * matrix (z x) s k +
        matrix (z x) r k * matrixVariation (z x) v s k) := by
    simp [symmetricVariation, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_add_distrib]
  rw [hd]
  exact he

theorem hasDerivAt_symmetricMatrix (z : ℝ → Vector) (v : Vector) (x : ℝ)
    (hz : ∀ r, HasDerivAt (fun t ↦ z t r) (v r) x) :
    HasDerivAt (fun t ↦ symmetricMatrix (z t)) (symmetricVariation (z x) v) x := by
  apply hasDerivAt_pi.mpr
  intro r
  exact hasDerivAt_pi.mpr (fun s ↦ hasDerivAt_symmetricMatrix_entry z v x hz r s)

theorem hasDerivAt_squareSum (z : ℝ → Vector) (v : Vector) (x : ℝ)
    (hz : ∀ r, HasDerivAt (fun t ↦ z t r) (v r) x) :
    HasDerivAt (fun t ↦ squareSum (z t)) (squareSumVariation (z x) v) x := by
  have he := HasDerivAt.fun_sum (u := Finset.univ) (fun r (_ : r ∈ Finset.univ) ↦
    (hz r).mul (hz r))
  have hd : squareSumVariation (z x) v = ∑ r, (v r * z x r + z x r * v r) := by
    unfold squareSumVariation
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [hd]
  convert he using 1 <;> try rfl
  funext t
  simp only [squareSum, pow_two, Pi.mul_apply]

theorem symmetricVariation_trace (z v : Vector) :
    (symmetricVariation z v).trace =
      2 * squareSum z * squareSumVariation z v + 2 * star (squareSumVariation z v) := by
  simp [Matrix.trace, Matrix.diag, symmetricVariation, matrixVariation, matrix, outer,
    crossMatrix, squareSum, squareSumVariation, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.cons_val_two]
  ring

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
