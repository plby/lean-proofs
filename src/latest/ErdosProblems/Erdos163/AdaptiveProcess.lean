/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.ProductAverage
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite adaptive sequential averages

Lee's random-greedy algorithm chooses the next target vertex from the current
state (within a target part it chooses a vertex of maximum realized defect).
The fixed-list process is useful for several projections, but the main
embedding theorem needs this state-dependent version.
-/

open scoped BigOperators
open Finset

namespace Erdos163
namespace AdaptiveProcess

universe u v

variable {β : Type u} {σ : Type v} [DecidableEq β]

inductive StateRun (choices : σ → Finset β) (step : σ → β → σ) :
    ℕ → σ → σ → Prop
  | nil (state) : StateRun choices step 0 state state
  | cons {fuel : ℕ} {state final : σ} {z : β}
      (hz : z ∈ choices state)
      (hrest : StateRun choices step fuel (step state z) final) :
      StateRun choices step (fuel + 1) state final

noncomputable def average (choices : σ → Finset β) (step : σ → β → σ) :
    ℕ → σ → (σ → ℝ) → ℝ
  | 0, state, payoff => payoff state
  | fuel + 1, state, payoff =>
      𝔼 z ∈ choices state, average choices step fuel (step state z) payoff

@[simp] theorem average_zero (choices : σ → Finset β) (step : σ → β → σ)
    (state : σ) (payoff : σ → ℝ) :
    average choices step 0 state payoff = payoff state := rfl

@[simp] theorem average_succ (choices : σ → Finset β) (step : σ → β → σ)
    (fuel : ℕ) (state : σ) (payoff : σ → ℝ) :
    average choices step (fuel + 1) state payoff =
      𝔼 z ∈ choices state, average choices step fuel (step state z) payoff := rfl

theorem exists_stateRun_le_average (choices : σ → Finset β)
    (step : σ → β → σ) (hne : ∀ state, (choices state).Nonempty)
    (fuel : ℕ) (state : σ) (payoff : σ → ℝ) :
    ∃ final, StateRun choices step fuel state final ∧
      payoff final ≤ average choices step fuel state payoff := by
  induction fuel generalizing state with
  | zero => exact ⟨state, .nil state, le_rfl⟩
  | succ fuel ih =>
      obtain ⟨z, hz, hzavg⟩ := Finset.exists_le_of_expect_le (hne state)
        (le_rfl : (𝔼 z ∈ choices state,
          average choices step fuel (step state z) payoff) ≤ _)
      obtain ⟨final, hrun, hfinal⟩ := ih (step state z)
      exact ⟨final, .cons hz hrun, hfinal.trans hzavg⟩

theorem average_nonneg (choices : σ → Finset β) (step : σ → β → σ)
    (fuel : ℕ) (state : σ) {payoff : σ → ℝ}
    (h : ∀ final, StateRun choices step fuel state final → 0 ≤ payoff final) :
    0 ≤ average choices step fuel state payoff := by
  induction fuel generalizing state with
  | zero => exact h state (.nil state)
  | succ fuel ih =>
      unfold average Finset.expect
      apply mul_nonneg
      · positivity
      · exact Finset.sum_nonneg fun z hz => ih (step state z)
          (fun final hrun => h final (.cons hz hrun))

theorem average_mono (choices : σ → Finset β) (step : σ → β → σ)
    (fuel : ℕ) (state : σ) {payoff payoff' : σ → ℝ}
    (h : ∀ final, StateRun choices step fuel state final →
      payoff final ≤ payoff' final) :
    average choices step fuel state payoff ≤
      average choices step fuel state payoff' := by
  induction fuel generalizing state with
  | zero => exact h state (.nil state)
  | succ fuel ih =>
      apply Finset.expect_le_expect
      intro z hz
      exact ih (step state z) fun final hrun => h final (.cons hz hrun)

theorem average_congr (choices : σ → Finset β) (step : σ → β → σ)
    (fuel : ℕ) (state : σ) {payoff payoff' : σ → ℝ}
    (h : ∀ final, StateRun choices step fuel state final →
      payoff final = payoff' final) :
    average choices step fuel state payoff =
      average choices step fuel state payoff' := by
  apply le_antisymm
  · exact average_mono choices step fuel state fun final hrun => (h final hrun).le
  · exact average_mono choices step fuel state fun final hrun => (h final hrun).ge

theorem average_sum {κ : Type*} [DecidableEq κ]
    (choices : σ → Finset β) (step : σ → β → σ)
    (fuel : ℕ) (state : σ) (S : Finset κ) (payoff : κ → σ → ℝ) :
    average choices step fuel state (fun final => ∑ i ∈ S, payoff i final) =
      ∑ i ∈ S, average choices step fuel state (payoff i) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      simp only [average_succ]
      simp_rw [ih]
      rw [Finset.expect_sum_comm]

theorem average_const_mul (choices : σ → Finset β) (step : σ → β → σ)
    (fuel : ℕ) (state : σ) (c : ℝ) (payoff : σ → ℝ) :
    average choices step fuel state (fun final => c * payoff final) =
      c * average choices step fuel state payoff := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      simp only [average_succ]
      simp_rw [ih]
      simp only [Finset.expect_eq_sum_div_card, ← Finset.mul_sum]
      ring

noncomputable def weightedAverage (choices : σ → Finset β)
    (step : σ → β → σ) (weight : σ → ℝ) :
    ℕ → σ → (σ → ℝ) → ℝ
  | 0, state, payoff => payoff state
  | fuel + 1, state, payoff =>
      𝔼 z ∈ choices state,
        weight state * weightedAverage choices step weight fuel (step state z) payoff

@[simp] theorem weightedAverage_zero (choices : σ → Finset β)
    (step : σ → β → σ) (weight : σ → ℝ)
    (state : σ) (payoff : σ → ℝ) :
    weightedAverage choices step weight 0 state payoff = payoff state := rfl

@[simp] theorem weightedAverage_succ (choices : σ → Finset β)
    (step : σ → β → σ) (weight : σ → ℝ)
    (fuel : ℕ) (state : σ) (payoff : σ → ℝ) :
    weightedAverage choices step weight (fuel + 1) state payoff =
      𝔼 z ∈ choices state,
        weight state * weightedAverage choices step weight fuel (step state z) payoff := rfl

theorem weightedAverage_nonneg (choices : σ → Finset β)
    (step : σ → β → σ) (weight : σ → ℝ)
    (hweight : ∀ state, 0 ≤ weight state)
    (fuel : ℕ) (state : σ) {payoff : σ → ℝ}
    (hpayoff : ∀ final, 0 ≤ payoff final) :
    0 ≤ weightedAverage choices step weight fuel state payoff := by
  induction fuel generalizing state with
  | zero => exact hpayoff state
  | succ fuel ih =>
      unfold weightedAverage Finset.expect
      apply mul_nonneg
      · positivity
      · exact Finset.sum_nonneg fun z _ =>
          mul_nonneg (hweight state) (ih (step state z))

/-- Finite change of measure with a state-dependent schedule. -/
theorem average_le_weightedAverage
    (oldChoices newChoices : σ → Finset β) (step : σ → β → σ)
    (weight : σ → ℝ)
    (hold : ∀ state, (oldChoices state).Nonempty)
    (hnew : ∀ state, (newChoices state).Nonempty)
    (hsub : ∀ state, oldChoices state ⊆ newChoices state)
    (hratio : ∀ state,
      ((newChoices state).card : ℝ) / (oldChoices state).card ≤ weight state)
    (hweight : ∀ state, 0 ≤ weight state)
    (fuel : ℕ) (state : σ) (payoff : σ → ℝ)
    (hpayoff : ∀ final, 0 ≤ payoff final) :
    average oldChoices step fuel state payoff ≤
      weightedAverage newChoices step weight fuel state payoff := by
  induction fuel generalizing state with
  | zero => exact le_rfl
  | succ fuel ih =>
      rw [average_succ, weightedAverage_succ]
      let tail : β → ℝ := fun z =>
        weightedAverage newChoices step weight fuel (step state z) payoff
      calc
        (𝔼 z ∈ oldChoices state,
            average oldChoices step fuel (step state z) payoff) ≤
            𝔼 z ∈ oldChoices state, tail z := by
              apply Finset.expect_le_expect
              intro z hz
              exact ih (step state z)
        _ ≤ (((newChoices state).card : ℝ) / (oldChoices state).card) *
              (𝔼 z ∈ newChoices state, tail z) :=
          Process.expect_subset_le_card_ratio (hold state) (hsub state) tail
            (fun z _ => weightedAverage_nonneg newChoices step weight
              hweight fuel (step state z) hpayoff)
        _ ≤ weight state * (𝔼 z ∈ newChoices state, tail z) := by
          exact mul_le_mul_of_nonneg_right (hratio state)
            (Finset.expect_nonneg fun z _ =>
              weightedAverage_nonneg newChoices step weight hweight fuel
                (step state z) hpayoff)
        _ = 𝔼 z ∈ newChoices state, weight state * tail z := by
          simp only [Finset.expect_eq_sum_div_card]
          rw [← Finset.mul_sum]
          ring

theorem average_add (choices : σ → Finset β) (step : σ → β → σ)
    (fuel : ℕ) (state : σ) (payoff payoff' : σ → ℝ) :
    average choices step fuel state (fun final => payoff final + payoff' final) =
      average choices step fuel state payoff +
        average choices step fuel state payoff' := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      simp only [average_succ]
      simp_rw [ih]
      rw [Finset.expect_add_distrib]

theorem average_div (choices : σ → Finset β) (step : σ → β → σ)
    (fuel : ℕ) (state : σ) (payoff : σ → ℝ) (c : ℝ) :
    average choices step fuel state (fun final => payoff final / c) =
      average choices step fuel state payoff / c := by
  change average choices step fuel state (fun final => payoff final * c⁻¹) =
    average choices step fuel state payoff * c⁻¹
  simpa [mul_comm] using
    average_const_mul choices step fuel state c⁻¹ payoff

end AdaptiveProcess
end Erdos163
