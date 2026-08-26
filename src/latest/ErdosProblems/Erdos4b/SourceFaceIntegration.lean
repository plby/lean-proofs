/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceTensorVariational

/-!
# Measurability and bounds for the Maynard face operator

These are ordinary finite-interval integrals, on the same coordinate
subtype as the source's pinned functionals.
-/

namespace Erdos4b

noncomputable section

open MeasureTheory BoundedGaps.Maynard
open scoped BigOperators

theorem measurable_maynardInsertJoint {K : ℕ} (h : Fin K) :
    Measurable (fun z : (maynardFaceIndex K h → ℝ) × ℝ ↦
      maynardInsertCoordinate h z.2 z.1) := by
  rw [measurable_pi_iff]
  intro i
  by_cases hi : i = h
  · simp only [maynardInsertCoordinate, dif_pos hi]
    exact measurable_snd
  · let j : maynardFaceIndex K h := ⟨i, hi⟩
    simpa [maynardInsertCoordinate, hi, j, Function.comp_def] using
      ((measurable_pi_apply j).comp measurable_fst)

theorem measurable_maynardFaceIntegral {K : ℕ} {F : (Fin K → ℝ) → ℝ}
    (hF : Measurable F) (h : Fin K) :
    Measurable (fun t : maynardFaceIndex K h → ℝ ↦
      ∫ x : ℝ in Set.Icc 0 1, F (maynardInsertCoordinate h x t)) :=
  ((hF.comp (measurable_maynardInsertJoint h)).stronglyMeasurable.integral_prod_right').measurable

theorem maynardFaceIntegral_norm_le_one {K : ℕ} {F : (Fin K → ℝ) → ℝ}
    (hF : ∀ t, ‖F t‖ ≤ 1) (h : Fin K) (t : maynardFaceIndex K h → ℝ) :
    ‖∫ x : ℝ in Set.Icc 0 1, F (maynardInsertCoordinate h x t)‖ ≤ 1 := by
  calc
    _ ≤ 1 * volume.real (Set.Icc (0 : ℝ) 1) :=
      norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top (fun x _ ↦ hF _)
    _ = 1 := by rw [Real.volume_real_Icc_of_le] <;> norm_num

theorem sum_maynardInsertCoordinate {K : ℕ} (h : Fin K) (x : ℝ)
    (t : maynardFaceIndex K h → ℝ) :
    (∑ i : Fin K, maynardInsertCoordinate h x t i) = x + ∑ i, t i := by
  classical
  rw [Fintype.sum_eq_add_sum_subtype_ne (maynardInsertCoordinate h x t) h,
    maynardInsertCoordinate_at]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact maynardInsertCoordinate_off h x t i.val i.property

end

end Erdos4b
