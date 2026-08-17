import ErdosProblems.Erdos121.Construction

/-! # Total-mass estimates for the `K₅` construction -/

open Filter
open scoped BigOperators

namespace Erdos121

set_option autoImplicit false

noncomputable section

lemma card_k5Parameter (U : ℕ) :
    Fintype.card (K5Parameter U) = (U / 100000000 + 1) ^ 5 := by
  rw [Fintype.card_coe]
  simp [K5Parameter, k5ParameterBox, Fintype.card_piFinset,
    Finset.prod_const]

lemma sum_k5ControlledAssignment_weight (U : ℕ) :
    (∑ σ : K5ControlledAssignment U, smallAssignmentWeight σ.1) =
      smallControlledMass (smallCutoff U) (smallLogBudget U) := by
  rw [smallControlledMass]
  simpa using
    (Finset.sum_subtype_eq_sum_filter
      (s := (Finset.univ : Finset (SmallAssignment (smallCutoff U))))
      (fun σ => smallAssignmentWeight σ)
      (p := fun σ => smallAssignedLog σ ≤ smallLogBudget U))

lemma k5TotalMassFormula (U : ℕ) :
    (k5Weight U).mass (fun _ => True) =
      ∑ σ : K5ControlledAssignment U,
        smallAssignmentWeight σ.1 *
          ∑ t : K5Parameter U,
            ∏ e, dyadicPrimeMass (k5OutcomeBins U σ t e) := by
  classical
  rw [FiniteWeight.mass_true]
  change (∑ ω : K5Outcome U, k5OutcomeWeight ω) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Fintype.sum_sigma]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  change (∑ p : K5LargeChoice U σ t,
      smallAssignmentWeight σ.1 * ∏ e, ((p e : ℕ) : ℝ)⁻¹) = _
  rw [← Finset.mul_sum]
  rw [sum_k5LargeChoice_weight]

lemma k5LargeMassProduct_lower {U : ℕ} (hU : 1000000000 ≤ U)
    (hprime : ∀ b : ℕ, U / 100 ≤ b → b ≤ U →
      (1 : ℝ) / (200 * U) ≤ dyadicPrimeMass b)
    (σ : K5ControlledAssignment U) (t : K5Parameter U) :
    ((1 : ℝ) / (200 * U)) ^ 10 ≤
      ∏ e, dyadicPrimeMass (k5OutcomeBins U σ t e) := by
  rw [show ((1 : ℝ) / (200 * U)) ^ 10 =
      ∏ _e : Fin 10, ((1 : ℝ) / (200 * U)) by simp]
  apply Finset.prod_le_prod
  · intro e he
    positivity
  · intro e he
    have hb := k5Outcome_bin_bounds hU σ t e
    exact hprime _ hb.1 (hb.2.trans (Nat.div_le_self U 2))

/-- A fully explicit lower bound for the good mass. -/
theorem eventually_k5TotalMass_lower :
    ∀ᶠ U : ℕ in atTop,
      (smallEuler 10 (smallCutoff U) / 2) *
          ((U / 100000000 + 1 : ℕ) : ℝ) ^ 5 *
          ((1 : ℝ) / (200 * U)) ^ 10 ≤
        (k5Weight U).mass (fun _ => True) := by
  filter_upwards [eventually_smallControlledMass_ge_half,
    eventually_dyadicPrimeMass_bounds_on_scale,
    eventually_ge_atTop 1000000000] with U hsmall hprime hU
  rw [k5TotalMassFormula]
  let q : ℝ := ((1 : ℝ) / (200 * U)) ^ 10
  have hq : 0 ≤ q := by positivity
  calc
    (smallEuler 10 (smallCutoff U) / 2) *
          ((U / 100000000 + 1 : ℕ) : ℝ) ^ 5 * q ≤
        smallControlledMass (smallCutoff U) (smallLogBudget U) *
          ((U / 100000000 + 1 : ℕ) : ℝ) ^ 5 * q := by
      gcongr
    _ = (∑ σ : K5ControlledAssignment U, smallAssignmentWeight σ.1) *
          (Fintype.card (K5Parameter U) : ℝ) * q := by
      rw [sum_k5ControlledAssignment_weight, card_k5Parameter]
      norm_cast
    _ ≤ ∑ σ : K5ControlledAssignment U,
        smallAssignmentWeight σ.1 *
          ∑ t : K5Parameter U,
            ∏ e, dyadicPrimeMass (k5OutcomeBins U σ t e) := by
      rw [mul_assoc]
      rw [show (Fintype.card (K5Parameter U) : ℝ) * q =
          ∑ _t : K5Parameter U, q by simp]
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro σ hσ
      rw [Finset.mul_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro t ht
      exact mul_le_mul_of_nonneg_left
        (k5LargeMassProduct_lower hU (fun b hb hbu => (hprime b hb hbu).1) σ t)
        (smallAssignmentWeight_nonneg σ.1)

end

end Erdos121
