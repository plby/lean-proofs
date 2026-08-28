import Wikipedia.HopfProblem.ConifoldPolarRegularityCoordinates
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Ambient regularity of the explicit polar-coordinate formulas

All differentiability statements are over the reals, on the original matrix
space with its product norm and on the original Euclidean coordinate spaces.
They do not transport a smooth structure to a matrix group or a level set.
-/

open scoped ContDiff Matrix.Norms.Elementwise

namespace Wikipedia.HopfProblem.ConifoldPolar

open ConifoldStandardBoundary

private theorem hyperbolicScale_argument_pos (b : Base) : 0 < 1 + ‖b‖ ^ 2 := by
  nlinarith [sq_nonneg ‖b‖]

private theorem denominator_argument_pos (M : MatrixSpace) : 0 < frobeniusSq M + 2 := by
  have h : 0 ≤ frobeniusSq M := by
    exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (M i j)
  linarith

/-- The scalar factor is smooth even at the origin of Euclidean three-space. -/
theorem hyperbolicScale_contDiff {n : ℕ∞ω} : ContDiff ℝ n hyperbolicScale := by
  exact (contDiff_const.add (contDiff_id.norm_sq ℝ)).sqrt
    (fun b => (hyperbolicScale_argument_pos b).ne')

theorem hyperbolicScale_continuous : Continuous hyperbolicScale :=
  (hyperbolicScale_contDiff (n := ∞)).continuous

/-- The positive matrix factor varies real smoothly with all base coordinates. -/
theorem positiveMatrix_contDiff {n : ℕ∞ω} : ContDiff ℝ n positiveMatrix := by
  exact ((Complex.ofRealCLM.contDiff.comp hyperbolicScale_contDiff).smul
    (contDiff_const (c := (1 : MatrixSpace)))).add tracelessMatrix_contDiff

theorem positiveMatrix_continuous : Continuous positiveMatrix :=
  (positiveMatrix_contDiff (n := ∞)).continuous

/-- The explicit polar denominator has no singularity anywhere in matrix space. -/
theorem denominator_contDiff {n : ℕ∞ω} : ContDiff ℝ n denominator := by
  exact (frobeniusSq_contDiff.add contDiff_const).sqrt
    (fun M => (denominator_argument_pos M).ne')

theorem denominator_continuous : Continuous denominator :=
  (denominator_contDiff (n := ∞)).continuous

/-- The explicit unitary-factor formula is smooth on the whole ambient matrix space. -/
theorem unitaryPart_contDiff {n : ℕ∞ω} : ContDiff ℝ n unitaryPart := by
  have hd : ContDiff ℝ n (fun M : MatrixSpace => (denominator M : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp denominator_contDiff
  have hi : ContDiff ℝ n (fun M : MatrixSpace => (denominator M : ℂ)⁻¹) :=
    hd.inv fun M => Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (denominator_argument_pos M)).ne'
  exact hi.smul (deform_contDiff 1)

theorem unitaryPart_continuous : Continuous unitaryPart :=
  (unitaryPart_contDiff (n := ∞)).continuous

private theorem matrixMul_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞ω} {f g : E → MatrixSpace} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (fun x => f x * g x) := by
  have he_f (i j : Fin 2) : ContDiff ℝ n (fun x => f x i j) :=
    (contDiff_apply_apply ℝ ℂ i j).comp hf
  have he_g (i j : Fin 2) : ContDiff ℝ n (fun x => g x i j) :=
    (contDiff_apply_apply ℝ ℂ i j).comp hg
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simpa only [Matrix.mul_apply, Fin.sum_univ_two] using
    ((he_f i 0).mul (he_g 0 j)).add ((he_f i 1).mul (he_g 1 j))

private theorem conjTranspose_contDiff {n : ℕ∞ω} :
    ContDiff ℝ n (fun M : MatrixSpace => M.conjTranspose) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact Complex.conjCLE.contDiff.comp (contDiff_apply_apply ℝ ℂ j i)

/-- The explicit positive-factor formula is smooth on the whole ambient matrix space. -/
theorem positivePart_contDiff {n : ℕ∞ω} : ContDiff ℝ n positivePart := by
  exact matrixMul_contDiff contDiff_id (conjTranspose_contDiff.comp unitaryPart_contDiff)

theorem positivePart_continuous : Continuous positivePart :=
  (positivePart_contDiff (n := ∞)).continuous

/-- The inverse polar formula is jointly smooth on the two original Euclidean spaces. -/
theorem inverseMatrix_contDiff {n : ℕ∞ω} :
    ContDiff ℝ n (fun p : Base × Normal => inverseMatrix p.1 p.2) := by
  exact matrixMul_contDiff (positiveMatrix_contDiff.comp contDiff_fst)
    (unitaryMatrix_contDiff.comp contDiff_snd)

theorem inverseMatrix_continuous :
    Continuous (fun p : Base × Normal => inverseMatrix p.1 p.2) :=
  (inverseMatrix_contDiff (n := ∞)).continuous

end Wikipedia.HopfProblem.ConifoldPolar
