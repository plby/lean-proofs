import ErdosProblems.Erdos1148.RelativeFlow
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Rotation frames and a uniform angular closeness estimate -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

noncomputable def rotationFrame (θ : ℝ) : SL(2, ℝ) :=
  ⟨!![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ], by
    simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_neg, sub_neg_eq_add]
    nlinarith [Real.sin_sq_add_cos_sq θ]⟩

lemma rotationFrame_add (θ φ : ℝ) : rotationFrame (θ + φ) = rotationFrame θ * rotationFrame φ := by
  apply Subtype.ext
  change (rotationFrame (θ + φ) : Matrix (Fin 2) (Fin 2) ℝ) =
    ((rotationFrame θ * rotationFrame φ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationFrame, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring

@[simp] lemma rotationFrame_zero : rotationFrame 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotationFrame]

lemma rotationFrame_inv (θ : ℝ) : (rotationFrame θ)⁻¹ = rotationFrame (-θ) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← rotationFrame_add, add_neg_cancel, rotationFrame_zero]

lemma rotationFrame_entryCloseOne (θ : ℝ) : EntryCloseOne |θ| (rotationFrame θ) := by
  have hs : |Real.sin θ| ≤ |θ| := by simpa using Real.abs_sin_sub_sin_le θ 0
  have hc : |Real.cos θ - 1| ≤ |θ| := by simpa using Real.abs_cos_sub_cos_le θ 0
  simpa only [EntryCloseOne, rotationFrame, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, abs_neg] using And.intro hc ⟨hs, hs, hc⟩

theorem rotationFrame_relative_close (θ φ : ℝ) :
    EntryCloseOne |φ - θ| ((rotationFrame θ)⁻¹ * rotationFrame φ) := by
  rw [rotationFrame_inv, ← rotationFrame_add, neg_add_eq_sub]
  exact rotationFrame_entryCloseOne _

theorem exists_rotationFrame_of_entries (g : SL(2, ℝ))
    (ha : g 0 0 = g 1 1) (hb : g 0 1 = -g 1 0) :
    ∃ θ ∈ Set.Icc (-Real.pi) Real.pi, rotationFrame θ = g := by
  let z : ℂ := ⟨g 0 0, g 1 0⟩
  have hdet := g.prop
  rw [Matrix.det_fin_two] at hdet
  have hnormSq : Complex.normSq z = 1 := by
    simp only [z, Complex.normSq_mk]
    rw [hb, ← ha] at hdet
    nlinarith
  have hnorm : ‖z‖ = 1 := by
    rw [Complex.normSq_eq_norm_sq] at hnormSq
    nlinarith [norm_nonneg z]
  have hz : z ≠ 0 := by intro h; rw [h, norm_zero] at hnorm; norm_num at hnorm
  refine ⟨z.arg, ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩, ?_⟩
  have hcos : Real.cos z.arg = g 0 0 := by rw [Complex.cos_arg hz, hnorm, div_one]
  have hsin : Real.sin z.arg = g 1 0 := by rw [Complex.sin_arg, hnorm, div_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotationFrame, hcos, hsin, ha, hb]

end Erdos1148.DukeArithmetic
