import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryExponential
import Wikipedia.HomotopyGroupsOfSpheres.Circle

/-!
# Trace rigidity from determinant one along an exponential path

The determinant at a single time does not determine the trace of the
generator. The determinant along the entire interval does: uniqueness
of lifts to the real covering of the circle forces its argument to vanish.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.ImaginarySymmetricMatrices

theorem slope_eq_zero_of_circle_exp (a : ℝ)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, Circle.exp (t * a) = 1) : a = 0 := by
  have he : Circle.exp ∘ (fun t : I ↦ (t : ℝ) * a) =
      Circle.exp ∘ (fun _ : I ↦ (0 : ℝ)) := by
    funext t
    exact (h t t.property).trans Circle.exp_zero.symm
  have hl := Circle.isCoveringMap_exp.eq_of_comp_eq
    (continuous_subtype_val.mul_const a) continuous_const he (0 : I) (by simp)
  have h1 := congrFun hl (1 : I)
  change (1 : ℝ) * a = 0 at h1
  simpa only [one_mul] using h1

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem trace_eq_zero_of_det_exp_interval (A : Matrix N N ℝ) (hsym : A.transpose = A)
    (hdet : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (NormedSpace.exp (imaginary (t • A))).det = 1) : A.trace = 0 := by
  apply slope_eq_zero_of_circle_exp
  intro t ht
  apply Circle.ext
  rw [Circle.coe_exp]
  change Complex.exp (((t * A.trace : ℝ) : ℂ) * Complex.I) = 1
  have hs : (t • A).transpose = t • A := by rw [Matrix.transpose_smul, hsym]
  have hd := hdet t ht
  rw [det_exp_imaginary _ hs, Matrix.trace_smul] at hd
  simpa only [smul_eq_mul, Complex.ofReal_mul, mul_comm Complex.I] using hd

theorem trace_eq_zero_of_det_pi_exp_interval (A : Matrix N N ℝ) (hsym : A.transpose = A)
    (hdet : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (NormedSpace.exp (imaginary ((t * Real.pi) • A))).det = 1) : A.trace = 0 := by
  have hs : (Real.pi • A).transpose = Real.pi • A := by rw [Matrix.transpose_smul, hsym]
  have ht : (Real.pi • A).trace = 0 := by
    apply trace_eq_zero_of_det_exp_interval _ hs
    intro t ht
    simpa only [smul_smul] using hdet t ht
  rw [Matrix.trace_smul, smul_eq_mul] at ht
  exact (mul_eq_zero.mp ht).resolve_left Real.pi_ne_zero

end Wikipedia.HomotopyGroupsOfSpheres.ImaginarySymmetricMatrices
