import Wikipedia.HopfProblem.Lattice
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The period domain and its generator formulas

This module uses the actual complex period matrices of Definition 3.3. Its
parameters are arbitrary complex numbers; it does not assume the existence
of the equivariant holomorphic period functions of Theorem 3.4.
-/

noncomputable section

namespace Wikipedia.HopfProblem

open scoped Matrix

/-- The three entries used to specify the periods. -/
@[ext] structure PeriodPoint where
  τ : ℂ
  μ : ℂ
  β : ℂ

namespace PeriodPoint

/-- The function `D` of Definition 3.1. -/
def discriminant (p : PeriodPoint) : ℝ := p.β.im - 6 * p.μ.im ^ 2 / p.τ.im

/-- The open period domain used in the paper. -/
def Admissible (p : PeriodPoint) : Prop := 0 < p.τ.im ∧ p.discriminant < 0

/-- The complex period matrix, with columns indexed by `(γ̂,û,ŵ,δ̂)`. -/
def matrix (p : PeriodPoint) : Matrix (Fin 2) (Fin 4) ℂ :=
  !![6 * p.μ, p.τ, 1, 0; p.β, p.μ, 0, 1]

/-- The same real-linear period map, in the coordinate order
`(Re ζ₁, Im ζ₁, Re ζ₂, Im ζ₂)` of Lemma 3.14. -/
def realMatrix (p : PeriodPoint) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![6 * p.μ.re, p.τ.re, 1, 0;
     6 * p.μ.im, p.τ.im, 0, 0;
     p.β.re, p.μ.re, 0, 1;
     p.β.im, p.μ.im, 0, 0]

/-- The order-three generator's transformation laws (Definition 3.1). -/
def step₁ (p : PeriodPoint) : PeriodPoint :=
  ⟨(p.τ - 1) / p.τ, (1 - p.μ) / p.τ, p.β + 2 - 6 * (1 - p.μ) ^ 2 / p.τ⟩

/-- The order-four generator's transformation laws (Definition 3.1). -/
def step₂ (p : PeriodPoint) : PeriodPoint :=
  ⟨-1 / p.τ, 1 + p.μ / p.τ, p.β - 3 - 6 * p.μ ^ 2 / p.τ⟩

/-- The cusp generator's transformation laws. -/
def step₀ (p : PeriodPoint) : PeriodPoint := ⟨p.τ - 1, p.μ, p.β + 1⟩

/-- The two complex matrices in Proposition 3.16. -/
def R₁ (p : PeriodPoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-1 / p.τ, 0; (1 - p.μ) / p.τ, 1]

def R₂ (p : PeriodPoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1 / p.τ, 0; -p.μ / p.τ, 1]

theorem τ_ne_zero (p : PeriodPoint) (h : 0 < p.τ.im) : p.τ ≠ 0 := by
  intro heq
  simp [heq] at h

theorem τ_sub_one_ne_zero (p : PeriodPoint) (h : 0 < p.τ.im) : p.τ - 1 ≠ 0 := by
  intro heq
  have heq' : p.τ = 1 := sub_eq_zero.mp heq
  simp [heq'] at h

/-- The determinant computation in Lemma 3.14, before dividing by `Im τ`. -/
theorem det_realMatrix (p : PeriodPoint) :
    p.realMatrix.det = p.τ.im * p.β.im - 6 * p.μ.im ^ 2 := by
  have hminor : p.realMatrix.submatrix (Fin.succAbove (0 : Fin 4))
      (Fin.succAbove (2 : Fin 4)) =
      !![6 * p.μ.im, p.τ.im, 0; p.β.re, p.μ.re, 1; p.β.im, p.μ.im, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_column _ 2, Fin.sum_univ_four, hminor]
  norm_num [realMatrix, Matrix.det_fin_three, Matrix.cons_val_two, Matrix.cons_val_three]
  ring

theorem det_realMatrix_eq_discriminant (p : PeriodPoint) (h : p.τ.im ≠ 0) :
    p.realMatrix.det = p.τ.im * p.discriminant := by
  rw [det_realMatrix]
  unfold discriminant
  field_simp

theorem det_realMatrix_neg (p : PeriodPoint) (h : p.Admissible) : p.realMatrix.det < 0 := by
  rw [det_realMatrix_eq_discriminant p (ne_of_gt h.1)]
  exact mul_neg_of_pos_of_neg h.1 h.2

theorem det_R₁ (p : PeriodPoint) : p.R₁.det = -1 / p.τ := by
  simp [R₁, Matrix.det_fin_two]

theorem det_R₂ (p : PeriodPoint) : p.R₂.det = 1 / p.τ := by
  simp [R₂, Matrix.det_fin_two]

/-- Proposition 3.16 for the first generator. -/
theorem step₁_matrix (p : PeriodPoint) (h : p.τ ≠ 0) :
    p.step₁.matrix = p.R₁ * p.matrix * (T₁.map (Int.castRingHom ℂ)).transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [step₁, matrix, R₁, T₁, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;> ring

/-- Proposition 3.16 for the second generator. -/
theorem step₂_matrix (p : PeriodPoint) (h : p.τ ≠ 0) :
    p.step₂.matrix = p.R₂ * p.matrix * (T₂.map (Int.castRingHom ℂ)).transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [step₂, matrix, R₂, T₂, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;> ring

/-- Proposition 3.16 at the cusp has trivial complex linear factor. -/
theorem step₀_matrix (p : PeriodPoint) :
    p.step₀.matrix = p.matrix * (T₀.map (Int.castRingHom ℂ)).transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [step₀, matrix, T₀, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals ring

theorem step₀_discriminant (p : PeriodPoint) : p.step₀.discriminant = p.discriminant := by
  simp [step₀, discriminant]

theorem step₂_discriminant (p : PeriodPoint) (h : p.τ.im ≠ 0) :
    p.step₂.discriminant = p.discriminant := by
  have hτ : p.τ ≠ 0 := by
    intro heq
    exact h (by simp [heq])
  have hn : Complex.normSq p.τ ≠ 0 := mt Complex.normSq_eq_zero.mp hτ
  simp [step₂, discriminant, Complex.div_im, Complex.mul_im, Complex.mul_re, pow_two]
  field_simp
  simp [Complex.normSq_apply]
  ring

theorem step₁_discriminant (p : PeriodPoint) (h : p.τ.im ≠ 0) :
    p.step₁.discriminant = p.discriminant := by
  have hτ : p.τ ≠ 0 := by
    intro heq
    exact h (by simp [heq])
  have hs := step₂_discriminant ⟨p.τ, 1 - p.μ, p.β⟩ h
  simpa [step₁, step₂, discriminant, sub_div, hτ, Complex.div_im, neg_div] using hs

theorem step₁_im (p : PeriodPoint) (h : p.τ ≠ 0) :
    p.step₁.τ.im = p.τ.im / Complex.normSq p.τ := by
  simp [step₁, sub_div, h, neg_div]

theorem step₂_im (p : PeriodPoint) :
    p.step₂.τ.im = p.τ.im / Complex.normSq p.τ := by
  simp [step₂, neg_div]

theorem step₁_admissible (p : PeriodPoint) (h : p.Admissible) : p.step₁.Admissible := by
  refine ⟨?_, ?_⟩
  · rw [step₁_im p (p.τ_ne_zero h.1)]
    exact div_pos h.1 (Complex.normSq_pos.mpr (p.τ_ne_zero h.1))
  · rw [step₁_discriminant p (ne_of_gt h.1)]
    exact h.2

theorem step₂_admissible (p : PeriodPoint) (h : p.Admissible) : p.step₂.Admissible := by
  refine ⟨?_, ?_⟩
  · rw [step₂_im]
    exact div_pos h.1 (Complex.normSq_pos.mpr (p.τ_ne_zero h.1))
  · rw [step₂_discriminant p (ne_of_gt h.1)]
    exact h.2

theorem step₀_admissible (p : PeriodPoint) (h : p.Admissible) : p.step₀.Admissible := by
  exact ⟨by simpa [step₀] using h.1, by simpa [step₀_discriminant] using h.2⟩

/-- The intermediate values in Proposition 3.11 and Proposition 3.13. -/
theorem step₁_sq (p : PeriodPoint) (h₀ : p.τ ≠ 0) (h₁ : p.τ - 1 ≠ 0) :
    p.step₁.step₁ =
      ⟨-1 / (p.τ - 1), (p.τ - 1 + p.μ) / (p.τ - 1),
        p.β - 2 - 6 * p.μ ^ 2 / (p.τ - 1)⟩ := by
  apply PeriodPoint.ext <;> simp [step₁] <;> field_simp <;> ring

theorem step₂_sq (p : PeriodPoint) (h : p.τ ≠ 0) :
    p.step₂.step₂ = ⟨p.τ, 1 - p.τ - p.μ, p.β - 6 + 6 * p.τ + 12 * p.μ⟩ := by
  apply PeriodPoint.ext <;> simp [step₂] <;> field_simp <;> ring

theorem step₁_cube (p : PeriodPoint) (h₀ : p.τ ≠ 0) (h₁ : p.τ - 1 ≠ 0) :
    p.step₁.step₁.step₁ = p := by
  rw [step₁_sq p h₀ h₁]
  apply PeriodPoint.ext <;> simp [step₁] <;> field_simp <;> ring

theorem step₂_fourth (p : PeriodPoint) (h : p.τ ≠ 0) :
    p.step₂.step₂.step₂.step₂ = p := by
  rw [step₂_sq (p.step₂.step₂), step₂_sq p h]
  · apply PeriodPoint.ext <;> simp
    all_goals ring
  · simpa [step₂] using h

/-- The inverse of the cusp transformation is the product of the two elliptic
transformations, in the order dictated by `g₀ = (g₁g₂)⁻¹`. -/
theorem step₁_step₂ (p : PeriodPoint) (h : p.τ ≠ 0) :
    p.step₂.step₁ = ⟨p.τ + 1, p.μ, p.β - 1⟩ := by
  apply PeriodPoint.ext <;> simp [step₁, step₂] <;> field_simp <;> ring

end PeriodPoint

end Wikipedia.HopfProblem
