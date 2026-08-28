import Wikipedia.HopfProblem.CuspCircleNormalTrivializationEquiv
import Wikipedia.HopfProblem.ConifoldStandardBoundaryCircle
import Mathlib.Analysis.Matrix.Normed

/-!
# The literal two-chart small-resolution matrices

The lower and upper matrices use the original two normal coordinates.
Their cocycle, determinant, Frobenius radius, and column weights are exact
matrix identities. The target is the unchanged matrix space used by the
standard conifold-boundary construction.
-/

noncomputable section

open scoped ComplexConjugate ContDiff Matrix Matrix.Norms.Elementwise

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Conifold

open ConifoldStandardBoundary

/-- The original lower small-resolution matrix. -/
def lowerMatrix (a : ℂ) (p : ℂ × ℂ) : MatrixSpace :=
  !![p.1, p.2; a * p.1, a * p.2]

/-- The original upper small-resolution matrix. -/
def upperMatrix (b : ℂ) (p : ℂ × ℂ) : MatrixSpace :=
  !![b * p.1, b * p.2; p.1, p.2]

@[simp] theorem lowerMatrix_det (a : ℂ) (p : ℂ × ℂ) : (lowerMatrix a p).det = 0 := by
  simp [lowerMatrix, Matrix.det_fin_two]
  ring

@[simp] theorem upperMatrix_det (b : ℂ) (p : ℂ × ℂ) : (upperMatrix b p).det = 0 := by
  simp [upperMatrix, Matrix.det_fin_two]
  ring

@[simp] theorem lowerMatrix_zero (a : ℂ) : lowerMatrix a 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerMatrix]

@[simp] theorem upperMatrix_zero (b : ℂ) : upperMatrix b 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperMatrix]

theorem lowerMatrix_eq_zero_iff (a : ℂ) (p : ℂ × ℂ) : lowerMatrix a p = 0 ↔ p = 0 := by
  constructor
  · intro h
    apply Prod.ext
    · exact congrArg (fun M : MatrixSpace => M 0 0) h
    · exact congrArg (fun M : MatrixSpace => M 0 1) h
  · rintro rfl
    exact lowerMatrix_zero a

theorem upperMatrix_eq_zero_iff (b : ℂ) (p : ℂ × ℂ) : upperMatrix b p = 0 ↔ p = 0 := by
  constructor
  · intro h
    apply Prod.ext
    · exact congrArg (fun M : MatrixSpace => M 1 0) h
    · exact congrArg (fun M : MatrixSpace => M 1 1) h
  · rintro rfl
    exact upperMatrix_zero b

/-- The matrix cocycle is exactly the original toric transition. -/
theorem upperMatrix_transition (a : ℂ) (ha : a ≠ 0) (p : ℂ × ℂ) :
    upperMatrix a⁻¹ (a * p.1, a * p.2) = lowerMatrix a p := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperMatrix, lowerMatrix, ha]

/-- The explicit inverse normal frames have exactly the native transition. -/
theorem upperInverse_transition (a : ℂ) (ha : a ≠ 0) (v : ℂ × ℂ) :
    upperInverse a⁻¹ v = (a * (lowerInverse a v).1, a * (lowerInverse a v).2) := by
  apply (upperEquiv a⁻¹).injective
  change upperMap a⁻¹ (upperInverse a⁻¹ v) =
    upperMap a⁻¹ (a * (lowerInverse a v).1, a * (lowerInverse a v).2)
  rw [upperMap_upperInverse, upper_lower_compatibility a ha, lowerMap_lowerInverse]

/-- Hence the matrix in real-trivial normal coordinates is independent of chart. -/
theorem normalMatrix_transition (a : ℂ) (ha : a ≠ 0) (v : ℂ × ℂ) :
    upperMatrix a⁻¹ (upperInverse a⁻¹ v) = lowerMatrix a (lowerInverse a v) := by
  rw [upperInverse_transition a ha, upperMatrix_transition a ha]

theorem frobeniusSq_lowerMatrix (a : ℂ) (p : ℂ × ℂ) :
    frobeniusSq (lowerMatrix a p) =
      denominator a * (Complex.normSq p.1 + Complex.normSq p.2) := by
  simp [frobeniusSq_entries, lowerMatrix, Complex.normSq_mul, denominator]
  ring

theorem frobeniusSq_upperMatrix (b : ℂ) (p : ℂ × ℂ) :
    frobeniusSq (upperMatrix b p) =
      denominator b * (Complex.normSq p.1 + Complex.normSq p.2) := by
  simp [frobeniusSq_entries, upperMatrix, Complex.normSq_mul, denominator]
  ring

/-- Frobenius norm is literally the radius of the already constructed normal frame. -/
theorem frobeniusSq_lowerMatrix_lowerInverse (a : ℂ) (v : ℂ × ℂ) :
    frobeniusSq (lowerMatrix a (lowerInverse a v)) =
      Complex.normSq v.1 + Complex.normSq v.2 := by
  rw [frobeniusSq_lowerMatrix, ← lowerMap_normSq, lowerMap_lowerInverse]

theorem frobeniusSq_upperMatrix_upperInverse (b : ℂ) (v : ℂ × ℂ) :
    frobeniusSq (upperMatrix b (upperInverse b v)) =
      Complex.normSq v.1 + Complex.normSq v.2 := by
  rw [frobeniusSq_upperMatrix, ← upperMap_normSq, upperMap_upperInverse]

/-- The original two weights act on the actual two matrix columns. -/
theorem lowerMatrix_oppositeWeights (a u : ℂ) (p : ℂ × ℂ) :
    lowerMatrix a (u⁻¹ * p.1, u * p.2) = rightCircle u (lowerMatrix a p) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerMatrix, rightCircle_entries] <;> ring

theorem upperMatrix_oppositeWeights (b u : ℂ) (p : ℂ × ℂ) :
    upperMatrix b (u⁻¹ * p.1, u * p.2) = rightCircle u (upperMatrix b p) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperMatrix, rightCircle_entries] <;> ring

theorem lowerInverse_unit_smul (a u : ℂ) (hu : ‖u‖ = 1) (v : ℂ × ℂ) :
    lowerInverse a (u • v) =
      (u⁻¹ * (lowerInverse a v).1, u * (lowerInverse a v).2) := by
  apply (lowerEquiv a).injective
  change lowerMap a (lowerInverse a (u • v)) =
    lowerMap a (u⁻¹ * (lowerInverse a v).1, u * (lowerInverse a v).2)
  rw [lowerMap_lowerInverse, lowerMap_oppositeWeights_of_norm_eq_one a u hu,
    lowerMap_lowerInverse]

theorem upperInverse_unit_smul (b u : ℂ) (hu : ‖u‖ = 1) (v : ℂ × ℂ) :
    upperInverse b (u • v) =
      (u⁻¹ * (upperInverse b v).1, u * (upperInverse b v).2) := by
  apply (upperEquiv b).injective
  change upperMap b (upperInverse b (u • v)) =
    upperMap b (u⁻¹ * (upperInverse b v).1, u * (upperInverse b v).2)
  rw [upperMap_upperInverse, upperMap_oppositeWeights_of_norm_eq_one b u hu,
    upperMap_upperInverse]

theorem lowerNormalMatrix_unit_smul (a u : ℂ) (hu : ‖u‖ = 1) (v : ℂ × ℂ) :
    lowerMatrix a (lowerInverse a (u • v)) =
      rightCircle u (lowerMatrix a (lowerInverse a v)) := by
  rw [lowerInverse_unit_smul a u hu, lowerMatrix_oppositeWeights]

theorem upperNormalMatrix_unit_smul (b u : ℂ) (hu : ‖u‖ = 1) (v : ℂ × ℂ) :
    upperMatrix b (upperInverse b (u • v)) =
      rightCircle u (upperMatrix b (upperInverse b v)) := by
  rw [upperInverse_unit_smul b u hu, upperMatrix_oppositeWeights]

variable {n : ℕ∞ω}

/-- These are real-analytic maps of the literal base and normal coordinates. -/
theorem contDiff_lowerMatrix :
    ContDiff ℝ n (fun q : ℂ × (ℂ × ℂ) => lowerMatrix q.1 q.2) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact contDiff_fst.comp contDiff_snd
  · exact contDiff_snd.comp contDiff_snd
  · exact contDiff_fst.mul (contDiff_fst.comp contDiff_snd)
  · exact contDiff_fst.mul (contDiff_snd.comp contDiff_snd)

theorem contDiff_upperMatrix :
    ContDiff ℝ n (fun q : ℂ × (ℂ × ℂ) => upperMatrix q.1 q.2) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact contDiff_fst.mul (contDiff_fst.comp contDiff_snd)
  · exact contDiff_fst.mul (contDiff_snd.comp contDiff_snd)
  · exact contDiff_fst.comp contDiff_snd
  · exact contDiff_snd.comp contDiff_snd

theorem contDiff_lowerNormalMatrix :
    ContDiff ℝ n (fun q : ℂ × (ℂ × ℂ) => lowerMatrix q.1 (lowerInverse q.1 q.2)) :=
  contDiff_lowerMatrix.comp (contDiff_fst.prodMk contDiff_lowerInverse)

theorem contDiff_upperNormalMatrix :
    ContDiff ℝ n (fun q : ℂ × (ℂ × ℂ) => upperMatrix q.1 (upperInverse q.1 q.2)) :=
  contDiff_upperMatrix.comp (contDiff_fst.prodMk contDiff_upperInverse)

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Conifold
