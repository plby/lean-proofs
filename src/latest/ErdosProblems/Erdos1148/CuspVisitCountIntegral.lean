import ErdosProblems.Erdos1148.CuspVisitExceedance
import ErdosProblems.Erdos1148.ModularFlowHomeomorph
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Measurability and invariant expectation of the cusp visit count -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory

def modularCuspVisitSet (H : ℝ) (i : ℕ) : Set ModularOrbitSpace :=
  (modularRightTranslate (diagonalFlow (i : ℝ))) ⁻¹' modularCusp H

noncomputable def modularCuspVisitCount (H : ℝ) (n : ℕ) (x : ModularOrbitSpace) : ℝ :=
  ((modularCuspVisitTimes H n x).card : ℝ)

lemma measurableSet_modularCuspVisitSet (H : ℝ) (i : ℕ) :
    MeasurableSet (modularCuspVisitSet H i) :=
  (measurableSet_modularCusp H).preimage (continuous_modularRightTranslate _).measurable

lemma modularCuspVisitTimes_card (H : ℝ) (n : ℕ) (x : ModularOrbitSpace) :
    (modularCuspVisitTimes H n x).card = (modularCuspVisitPattern H n x).card :=
  Finset.card_image_of_injective _ Fin.val_injective

theorem modularCuspVisitCount_eq_sum_indicator (H : ℝ) (n : ℕ) (x : ModularOrbitSpace) :
    modularCuspVisitCount H n x = ∑ i : Fin n,
      (modularCuspVisitSet H i.val).indicator (fun _ : ModularOrbitSpace => (1 : ℝ)) x := by
  classical
  rw [modularCuspVisitCount, modularCuspVisitTimes_card]
  change ((Finset.univ.filter (fun i : Fin n =>
    modularRightTranslate (diagonalFlow (i.val : ℝ)) x ∈ modularCusp H)).card : ℝ) = _
  rw [Finset.natCast_card_filter]
  simp only [Set.indicator_apply, modularCuspVisitSet, Set.mem_preimage]

theorem modularCuspVisitCount_nonneg (H : ℝ) (n : ℕ) (x : ModularOrbitSpace) :
    0 ≤ modularCuspVisitCount H n x := Nat.cast_nonneg _

theorem modularCuspVisitCount_le (H : ℝ) (n : ℕ) (x : ModularOrbitSpace) :
    modularCuspVisitCount H n x ≤ (n : ℝ) := by
  have hcard : (modularCuspVisitTimes H n x).card ≤ n := by
    rw [modularCuspVisitTimes_card]
    exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  change ((modularCuspVisitTimes H n x).card : ℝ) ≤ (n : ℝ)
  exact_mod_cast hcard

theorem measurable_modularCuspVisitCount (H : ℝ) (n : ℕ) : Measurable (modularCuspVisitCount H n) := by
  have heq : modularCuspVisitCount H n = fun x => ∑ i : Fin n,
      (modularCuspVisitSet H i.val).indicator (fun _ : ModularOrbitSpace => (1 : ℝ)) x :=
    funext (modularCuspVisitCount_eq_sum_indicator H n)
  rw [heq]
  exact Finset.measurable_sum _ (fun i _ => measurable_const.indicator (measurableSet_modularCuspVisitSet H i.val))

theorem integrable_modularCuspVisitCount (μ : Measure ModularOrbitSpace) [IsFiniteMeasure μ]
    (H : ℝ) (n : ℕ) : Integrable (modularCuspVisitCount H n) μ := by
  have heq : modularCuspVisitCount H n = fun x => ∑ i : Fin n,
      (modularCuspVisitSet H i.val).indicator (fun _ : ModularOrbitSpace => (1 : ℝ)) x :=
    funext (modularCuspVisitCount_eq_sum_indicator H n)
  rw [heq]
  exact integrable_finsetSum _ (fun i _ => (integrable_const (1 : ℝ)).indicator
    (measurableSet_modularCuspVisitSet H i.val))

theorem integral_modularCuspVisitCount (μ : Measure ModularOrbitSpace) [IsFiniteMeasure μ]
    (hinv : ∀ t : ℝ, Measure.map (modularRightTranslate (diagonalFlow t)) μ = μ)
    (H : ℝ) (n : ℕ) :
    (∫ x, modularCuspVisitCount H n x ∂μ) = (n : ℝ) * μ.real (modularCusp H) := by
  have hi (i : Fin n) : Integrable
      ((modularCuspVisitSet H i.val).indicator (fun _ : ModularOrbitSpace => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_modularCuspVisitSet H i.val)
  calc
    _ = ∫ x, ∑ i : Fin n,
        (modularCuspVisitSet H i.val).indicator (fun _ : ModularOrbitSpace => (1 : ℝ)) x ∂μ := by
      congr 1
      funext x
      exact modularCuspVisitCount_eq_sum_indicator H n x
    _ = ∑ i : Fin n, ∫ x,
        (modularCuspVisitSet H i.val).indicator (fun _ : ModularOrbitSpace => (1 : ℝ)) x ∂μ :=
      integral_finsetSum _ (fun i _ => hi i)
    _ = ∑ i : Fin n, μ.real (modularCuspVisitSet H i.val) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [smul_eq_mul, mul_one] using
        integral_indicator_const (1 : ℝ) (measurableSet_modularCuspVisitSet H i.val)
    _ = ∑ _i : Fin n, μ.real (modularCusp H) := by
      apply Finset.sum_congr rfl
      intro i _
      exact modular_flow_measureReal_preimage μ hinv (i.val : ℝ) (modularCusp H)
    _ = _ := by simp

lemma measurableSet_modularCuspVisitExceedance (H : ℝ) (n : ℕ) (A : ℝ) :
    MeasurableSet (modularCuspVisitExceedance H n A) :=
  measurableSet_le measurable_const (measurable_modularCuspVisitCount H n)

end Erdos1148.DukeArithmetic
