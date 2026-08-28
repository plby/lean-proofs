import Wikipedia.HopfProblem.ConifoldStandardBoundaryAlgebra
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Matrix.Normed

/-!
# Ambient regularity of the standard conifold coordinate changes

These are real smoothness statements on the original matrix space, equipped
with its product norm.  They use the explicit entry formulas and do not
introduce or transport any manifold structure on a boundary level set.
-/

open scoped ComplexConjugate ContDiff Matrix.Norms.Elementwise

namespace Wikipedia.HopfProblem.ConifoldStandardBoundary

/-- The adjugate of the conjugate transpose is real smooth on matrix space. -/
theorem adjointAdjugate_contDiff {n : ℕ∞ω} : ContDiff ℝ n adjointAdjugate := by
  have hc (i j : Fin 2) :
      ContDiff ℝ n (fun M : MatrixSpace => conj (M i j)) :=
    Complex.conjCLE.contDiff.comp (contDiff_apply_apply ℝ ℂ i j)
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · simpa [adjointAdjugate_entries] using hc 1 1
  · simpa [adjointAdjugate_entries] using (hc 1 0).neg
  · simpa [adjointAdjugate_entries] using (hc 0 1).neg
  · simpa [adjointAdjugate_entries] using hc 0 0

theorem adjointAdjugate_continuous : Continuous adjointAdjugate :=
  (adjointAdjugate_contDiff (n := ∞)).continuous

/-- Each constant-coefficient deformation is real smooth on matrix space. -/
theorem deform_contDiff (a : ℝ) {n : ℕ∞ω} : ContDiff ℝ n (deform a) := by
  have ha : ContDiff ℝ n (fun _ : MatrixSpace => (a : ℂ)) := contDiff_const
  exact contDiff_id.add (ha.smul adjointAdjugate_contDiff)

theorem deform_continuous (a : ℝ) : Continuous (deform a) :=
  (deform_contDiff a (n := ∞)).continuous

/-- The squared Frobenius norm is a real smooth polynomial in the entries. -/
theorem frobeniusSq_contDiff {n : ℕ∞ω} : ContDiff ℝ n frobeniusSq := by
  have hn : ContDiff ℝ n (Complex.normSq : ℂ → ℝ) := by
    change ContDiff ℝ n (fun z : ℂ => z.re * z.re + z.im * z.im)
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  have he (i j : Fin 2) :
      ContDiff ℝ n (fun M : MatrixSpace => Complex.normSq (M i j)) :=
    hn.comp (contDiff_apply_apply ℝ ℂ i j)
  change ContDiff ℝ n (fun M : MatrixSpace => frobeniusSq M)
  simp only [frobeniusSq_entries]
  exact ((he 0 0).add (he 0 1)).add ((he 1 0).add (he 1 1))

theorem frobeniusSq_continuous : Continuous frobeniusSq :=
  (frobeniusSq_contDiff (n := ∞)).continuous

/-- The complex determinant is real smooth on the original matrix space. -/
theorem det_contDiff {n : ℕ∞ω} :
    ContDiff ℝ n (fun M : MatrixSpace => M.det) := by
  have he (i j : Fin 2) : ContDiff ℝ n (fun M : MatrixSpace => M i j) :=
    contDiff_apply_apply ℝ ℂ i j
  simpa only [Matrix.det_fin_two] using
    ((he 0 0).mul (he 1 1)).sub ((he 0 1).mul (he 1 0))

theorem det_continuous : Continuous (fun M : MatrixSpace => M.det) :=
  (det_contDiff (n := ∞)).continuous

end Wikipedia.HopfProblem.ConifoldStandardBoundary
