import ErdosProblems.Erdos1148.UpperHalfPlaneFundamentalMass
import ErdosProblems.Erdos1148.UpperHalfPlaneCircleNull
import Mathlib.MeasureTheory.Group.FundamentalDomain

/-! # A measurable domain for the integral action on real determinant-one matrices -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Measure Filter
open scoped MatrixGroups ENNReal Pointwise

def MatrixHalfSign (g : SL(2, ℝ)) : Prop :=
  0 < g 0 0 ∨ (g 0 0 = 0 ∧ 0 < g 0 1)

lemma matrixHalfSign_or_neg (g : SL(2, ℝ)) : MatrixHalfSign g ∨ MatrixHalfSign (-g) := by
  have hdet := g.property
  rw [Matrix.det_fin_two] at hdet
  by_cases h₀ : g 0 0 = 0
  · have h₁ : g 0 1 ≠ 0 := by intro h; simp [h₀, h] at hdet
    rcases lt_or_gt_of_ne h₁ with h | h
    · right
      exact Or.inr ⟨by simpa using h₀, by simpa using neg_pos.mpr h⟩
    · exact Or.inl (Or.inr ⟨h₀, h⟩)
  · rcases lt_or_gt_of_ne h₀ with h | h
    · exact Or.inr (Or.inl (by simpa using neg_pos.mpr h))
    · exact Or.inl (Or.inl h)

lemma matrixHalfSign_not_neg {g : SL(2, ℝ)} (hg : MatrixHalfSign g) :
    ¬ MatrixHalfSign (-g) := by
  intro hn
  simp only [MatrixHalfSign, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply] at hg hn
  rcases hg with hg | ⟨hg, hg'⟩ <;> rcases hn with hn | ⟨hn, hn'⟩ <;> linarith

def modularHaarDomain : Set SL(2, ℝ) :=
  {g | g • UpperHalfPlane.I ∈ ModularGroup.fdo ∧ MatrixHalfSign g}

theorem measurableSet_modularHaarDomain : MeasurableSet modularHaarDomain := by
  have h₀ : MeasurableSet {g : SL(2, ℝ) | 0 < g 0 0} :=
    (isOpen_lt continuous_const (by fun_prop)).measurableSet
  have h₁ : MeasurableSet {g : SL(2, ℝ) | g 0 0 = 0} :=
    (isClosed_eq (by fun_prop) continuous_const).measurableSet
  have h₂ : MeasurableSet {g : SL(2, ℝ) | 0 < g 0 1} :=
    (isOpen_lt continuous_const (by fun_prop)).measurableSet
  exact (ModularGroup.isOpen_fdo.measurableSet.preimage measurable_smul_I).inter
    (h₀.union (h₁.inter h₂))

lemma integral_frame_smul_I (γ : SL(2, ℤ)) (g : SL(2, ℝ)) :
    (γ • g) • UpperHalfPlane.I = γ • (g • UpperHalfPlane.I) := by
  rw [integralRealMatrix_smul, mul_smul]
  rw [MulAction.compHom_smul_def, MulAction.compHom_smul_def]
  congr 1

instance integralRealHaarInvariant : SMulInvariantMeasure SL(2, ℤ) SL(2, ℝ)
    (Measure.haar (G := SL(2, ℝ))) where
  measure_preimage_smul γ s hs := measure_preimage_mul _ (γ : SL(2, ℝ)) s

theorem modularHaarDomain_translate_unique {g : SL(2, ℝ)} {γ : SL(2, ℤ)}
    (hg : g ∈ modularHaarDomain) (hγg : γ • g ∈ modularHaarDomain) : γ = 1 := by
  have hfd : γ • (g • UpperHalfPlane.I) ∈ ModularGroup.fdo := by
    rw [← integral_frame_smul_I]
    exact hγg.1
  rcases ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fdo hg.1 hfd with h | h
  · exact h
  · subst γ
    have hn : -g ∈ modularHaarDomain := by
      simpa [integralRealMatrix_smul] using hγg
    exact (matrixHalfSign_not_neg hg.2 hn.2).elim

theorem modularHaarDomain_mass_finite :
    (Measure.haar (G := SL(2, ℝ))) modularHaarDomain < ∞ := by
  apply lt_of_le_of_lt (measure_mono ?_) specialLinear_haar_fd_preimage_finite
  intro g hg
  exact ⟨hg.1.1.le, hg.1.2.le⟩

end Erdos1148.DukeArithmetic
