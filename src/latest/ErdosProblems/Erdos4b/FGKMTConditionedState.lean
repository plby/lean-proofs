/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTNormalizerMoments
import ErdosProblems.Erdos4b.FGKMTSourceBadPrimeCount

/-! # Conditioning the actual finite previous-state law on containment -/

namespace Erdos4b.FGKMT.FiniteEdgeFamily

noncomputable section

open scoped BigOperators

variable {α Ξ : Type*} [Fintype Ξ] [DecidableEq α]

def conditionedStateMass (ρ : Ξ → ℝ) (W : Ξ → Finset α) (e : Finset α) (s : Ξ) : ℝ :=
  (if e ⊆ W s then ρ s else 0) / containmentMass ρ W e

theorem containmentMass_pos_of_relative_error {ρ : Ξ → ℝ} {W : Ξ → Finset α}
    {P : α → ℝ} {e : Finset α} {η : ℝ}
    (hP : ∀ v ∈ e, 0 < P v) (hη : η < 1)
    (hcont : |containmentMass ρ W e - survivalProduct P e| ≤ η * survivalProduct P e) :
    0 < containmentMass ρ W e := by
  have hp := survivalProduct_pos hP
  have hlo := (abs_le.mp hcont).1
  nlinarith

theorem conditionedStateMass_nonneg {ρ : Ξ → ℝ} {W : Ξ → Finset α} {e : Finset α}
    (hρ : ∀ s, 0 ≤ ρ s) (hq : 0 < containmentMass ρ W e) (s : Ξ) :
    0 ≤ conditionedStateMass ρ W e s := by
  apply div_nonneg _ hq.le
  split_ifs
  · exact hρ s
  · exact le_rfl

theorem conditionedStateMass_sum_one {ρ : Ξ → ℝ} {W : Ξ → Finset α} {e : Finset α}
    (hq : 0 < containmentMass ρ W e) : (∑ s, conditionedStateMass ρ W e s) = 1 := by
  simp only [conditionedStateMass, ← Finset.sum_div]
  exact div_self hq.ne'

theorem conditionedState_containment (ρ : Ξ → ℝ) (W : Ξ → Finset α) (e A : Finset α) :
    containmentMass (conditionedStateMass ρ W e) W A =
      containmentMass ρ W (e ∪ A) / containmentMass ρ W e := by
  change (∑ s, if A ⊆ W s then
      (if e ⊆ W s then ρ s else 0) / containmentMass ρ W e else 0) =
    (∑ s, if e ∪ A ⊆ W s then ρ s else 0) / containmentMass ρ W e
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _hs
  by_cases he : e ⊆ W s <;> by_cases hA : A ⊆ W s <;>
    simp only [Finset.union_subset_iff, he, hA, and_self, and_false, false_and,
      if_true, if_false, zero_div]

theorem conditionedState_expectation (ρ Z : Ξ → ℝ) (W : Ξ → Finset α) (e : Finset α) :
    (∑ s, conditionedStateMass ρ W e s * Z s) =
      (∑ s, if e ⊆ W s then ρ s * Z s else 0) / containmentMass ρ W e := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _hs
  by_cases he : e ⊆ W s
  · simp only [conditionedStateMass, if_pos he]
    ring
  · simp only [conditionedStateMass, if_neg he, zero_div, zero_mul]

theorem conditionedState_expectation_le {ρ Z : Ξ → ℝ} {W : Ξ → Finset α} {e : Finset α}
    (hρ : ∀ s, 0 ≤ ρ s) (hZ : ∀ s, 0 ≤ Z s) (hq : 0 < containmentMass ρ W e) :
    (∑ s, conditionedStateMass ρ W e s * Z s) ≤
      (∑ s, ρ s * Z s) / containmentMass ρ W e := by
  rw [conditionedState_expectation]
  apply div_le_div_of_nonneg_right _ hq.le
  apply Finset.sum_le_sum
  intro s _hs
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (hρ s) (hZ s)

theorem conditionedState_tail_le {ρ Z : Ξ → ℝ} {W : Ξ → Finset α} {e : Finset α}
    (hρ : ∀ s, 0 ≤ ρ s) (hZ : ∀ s, 0 ≤ Z s) (hq : 0 < containmentMass ρ W e)
    {t : ℝ} (ht : 0 < t) :
    (∑ s, if t ≤ Z s then conditionedStateMass ρ W e s else 0) ≤
      (∑ s, ρ s * Z s) / (containmentMass ρ W e * t) := by
  have h := (finite_nonnegative_tail_le (conditionedStateMass ρ W e) Z
    (conditionedStateMass_nonneg hρ hq) hZ ht).trans
    (div_le_div_of_nonneg_right (conditionedState_expectation_le hρ hZ hq) ht.le)
  simpa only [div_div] using h

end

end Erdos4b.FGKMT.FiniteEdgeFamily
