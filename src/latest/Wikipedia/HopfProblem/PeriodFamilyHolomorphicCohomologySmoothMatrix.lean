import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Real smoothness of the genuine inverse matrix

The determinant and adjugate are finite polynomials in the matrix entries.
The defining adjugate formula for `Matrix.inv` therefore proves smoothness
where the actual determinant is nonzero. The statements use the original
matrix inverse and matrix-vector multiplication, on arbitrary parameter
subsets and without an assumed smooth-inversion operator.
-/

noncomputable section

open scoped BigOperators ContDiff Matrix Matrix.Norms.Elementwise

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Set E}

/-- The actual determinant of a real smooth matrix family is smooth. -/
theorem matrix_det_contDiffOn {A : E → Matrix ι ι ℝ}
    (hA : ContDiffOn ℝ ∞ A S) :
    ContDiffOn ℝ ∞ (fun x => (A x).det) S := by
  classical
  simp only [Matrix.det_apply']
  apply ContDiffOn.sum
  intro σ _
  apply contDiffOn_const.mul
  apply contDiffOn_prod
  intro i _
  exact contDiffOn_pi.mp (contDiffOn_pi.mp hA (σ i)) i

/-- Every entry of the original adjugate is a smooth determinant polynomial. -/
theorem matrix_adjugate_contDiffOn {A : E → Matrix ι ι ℝ}
    (hA : ContDiffOn ℝ ∞ A S) :
    ContDiffOn ℝ ∞ (fun x => (A x).adjugate) S := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  simp only [Matrix.adjugate_apply]
  apply matrix_det_contDiffOn
  apply contDiffOn_pi.mpr
  intro k
  apply contDiffOn_pi.mpr
  intro l
  by_cases h : k = j
  · simpa only [Matrix.updateRow_apply, if_pos h] using
      (contDiffOn_const :
        ContDiffOn ℝ ∞ (fun _ : E => (Pi.single i (1 : ℝ) : ι → ℝ) l) S)
  · simpa only [Matrix.updateRow_apply, if_neg h] using
      (contDiffOn_pi.mp (contDiffOn_pi.mp hA k) l)

/-- Genuine `Matrix.inv` is real smooth along every nonsingular smooth family. -/
theorem matrix_inv_contDiffOn {A : E → Matrix ι ι ℝ}
    (hA : ContDiffOn ℝ ∞ A S) (hdet : ∀ x ∈ S, (A x).det ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => (A x)⁻¹) S := by
  have hd := (matrix_det_contDiffOn hA).fun_inv hdet
  have ha := matrix_adjugate_contDiffOn hA
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv'] using hd.fun_smul ha

/-- The inverse function itself is smooth on the actual nonsingular locus. -/
theorem matrix_inv_contDiffOn_nonsingular :
    ContDiffOn ℝ ∞ (fun A : Matrix ι ι ℝ => A⁻¹) {A | A.det ≠ 0} :=
  matrix_inv_contDiffOn contDiffOn_id (fun _ h => h)

omit [DecidableEq ι] in
/-- Actual matrix-vector multiplication preserves jointly smooth dependence. -/
theorem matrix_mulVec_contDiffOn {A : E → Matrix ι ι ℝ} {v : E → ι → ℝ}
    (hA : ContDiffOn ℝ ∞ A S) (hv : ContDiffOn ℝ ∞ v S) :
    ContDiffOn ℝ ∞ (fun x => A x *ᵥ v x) S := by
  apply contDiffOn_pi.mpr
  intro i
  simp only [Matrix.mulVec, dotProduct]
  apply ContDiffOn.sum
  intro j _
  exact (contDiffOn_pi.mp (contDiffOn_pi.mp hA i) j).mul (contDiffOn_pi.mp hv j)

/-- Apply the genuine inverse to a smoothly varying vector on the same subset. -/
theorem matrix_inv_mulVec_contDiffOn {A : E → Matrix ι ι ℝ} {v : E → ι → ℝ}
    (hA : ContDiffOn ℝ ∞ A S) (hv : ContDiffOn ℝ ∞ v S)
    (hdet : ∀ x ∈ S, (A x).det ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => (A x)⁻¹ *ᵥ v x) S :=
  matrix_mulVec_contDiffOn (matrix_inv_contDiffOn hA hdet) hv

/-- Joint smoothness in the parameter and vector for the original inverse action. -/
theorem matrix_inv_mulVec_contDiffOn_prod {A : E → Matrix ι ι ℝ}
    (hA : ContDiffOn ℝ ∞ A S) (hdet : ∀ x ∈ S, (A x).det ≠ 0) :
    ContDiffOn ℝ ∞ (fun p : E × (ι → ℝ) => (A p.1)⁻¹ *ᵥ p.2)
      (S ×ˢ Set.univ) :=
  matrix_inv_mulVec_contDiffOn
    (hA.comp contDiffOn_fst (fun _ hp => hp.1)) contDiffOn_snd
    (fun p hp => hdet p.1 hp.1)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Smooth
