import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricCurveTangency
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryLocalLogarithm

/-!
# The derivative of a constant-determinant symmetric unitary curve at identity

Its entries are purely imaginary, and their imaginary parts form the actual
real symmetric trace-zero model used by the logarithm chart.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices

open QuaternionicBottMatrix ImaginarySymmetricMatrices RealSymmetricMixing

theorem identity_curve_entry_re_zero (B : ℝ → Space (Fin 3))
    (D : Matrix (Fin 3) (Fin 3) ℂ) (x : ℝ)
    (hB : ∀ r s, HasDerivAt (fun t ↦ (B t).val.val r s) (D r s) x)
    (hBx : (B x).val.val = 1) (r s : Fin 3) : (D r s).re = 0 := by
  have he : star (D s r) + D r s = 0 := by
    simpa [hBx, Matrix.one_apply, mul_ite, ite_mul, Finset.sum_add_distrib] using
      unitary_curve_derivative B D x hB r s
  rw [symmetric_curve_derivative B D x hB s r] at he
  have hr := congrArg Complex.re he
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.zero_re] at hr
  linarith

theorem hasDerivAt_det_identity (B : ℝ → Space (Fin 3))
    (D : Matrix (Fin 3) (Fin 3) ℂ) (x : ℝ)
    (hB : ∀ r s, HasDerivAt (fun t ↦ (B t).val.val r s) (D r s) x)
    (hBx : (B x).val.val = 1) :
    HasDerivAt (fun t ↦ (B t).val.val.det) D.trace x := by
  have he := (((((hB 0 0).mul (hB 1 1)).mul (hB 2 2)).sub
    (((hB 0 0).mul (hB 1 2)).mul (hB 2 1))).sub
    (((hB 0 1).mul (hB 1 0)).mul (hB 2 2))).add
    (((hB 0 1).mul (hB 1 2)).mul (hB 2 0))
  have he' := (he.add (((hB 0 2).mul (hB 1 0)).mul (hB 2 1))).sub
    (((hB 0 2).mul (hB 1 1)).mul (hB 2 0))
  convert he' using 1 <;> try rfl
  · funext t
    simp only [Matrix.det_fin_three, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  · simp [Pi.mul_apply, hBx, Matrix.trace_fin_three]

theorem constant_identity_curve_trace_zero (B : ℝ → Space (Fin 3))
    (D : Matrix (Fin 3) (Fin 3) ℂ) (x : ℝ)
    (hB : ∀ r s, HasDerivAt (fun t ↦ (B t).val.val r s) (D r s) x)
    (hBx : (B x).val.val = 1) (c : ℂ) (hdet : ∀ t, (B t).val.val.det = c) :
    D.trace = 0 := by
  have he := hasDerivAt_det_identity B D x hB hBx
  have hf : (fun t ↦ (B t).val.val.det) = fun _ ↦ c := funext hdet
  rw [hf] at he
  exact he.unique (hasDerivAt_const x c)

theorem identity_curve_imaginaryPart_mem (B : ℝ → Space (Fin 3))
    (D : Matrix (Fin 3) (Fin 3) ℂ) (x : ℝ)
    (hB : ∀ r s, HasDerivAt (fun t ↦ (B t).val.val r s) (D r s) x)
    (hBx : (B x).val.val = 1) (c : ℂ) (hdet : ∀ t, (B t).val.val.det = c) :
    LocalLogarithm.imaginaryPart D ∈ symmetricTraceZero (Fin 3) := by
  constructor
  · ext r s
    exact congrArg Complex.im (symmetric_curve_derivative B D x hB s r)
  · have h := congrArg Complex.im (constant_identity_curve_trace_zero B D x hB hBx c hdet)
    simpa [LocalLogarithm.imaginaryPart, Matrix.trace_fin_three] using h

theorem identity_curve_imaginary_reconstruction (B : ℝ → Space (Fin 3))
    (D : Matrix (Fin 3) (Fin 3) ℂ) (x : ℝ)
    (hB : ∀ r s, HasDerivAt (fun t ↦ (B t).val.val r s) (D r s) x)
    (hBx : (B x).val.val = 1) : D = imaginary (LocalLogarithm.imaginaryPart D) := by
  ext r s
  apply Complex.ext
  · simpa [imaginary_apply, LocalLogarithm.imaginaryPart] using
      identity_curve_entry_re_zero B D x hB hBx r s
  · simp [imaginary_apply, LocalLogarithm.imaginaryPart]

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices
