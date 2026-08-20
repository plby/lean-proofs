/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.MomentPropagation

/-!
# Terminal neutralization and independent product moments

Once every forward neighbor of a target vertex is neutralized, the recorded
defect is a function of independent uniform coordinates.  This file proves
that statement directly for the finite sequential process.
-/

open Finset

namespace Erdos163
namespace RandomGreedy

universe u v w

variable {α : Type u} {β : Type v} {ι : Type w}
  [Fintype α] [DecidableEq α] [LinearOrder α]
  [Fintype β] [DecidableEq β] [DecidableEq ι]

structure ObservationState
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β)
    (remaining : List α) (state : State α β) : Prop where
  before : ∀ ⦃x a⦄, x ∈ remaining → a ∉ remaining → x < a
  formula : ∀ a, a ∉ remaining →
    state.observed a =
      FiniteDefect.defectPower G (threshold a)
        (fun y : forwardNeighbors H a => value default state y)
        (host (part a)) momentExponent

theorem observationState_initial
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β) :
    ObservationState G H host part threshold momentExponent default order
      (initialState : State α β) := by
  constructor
  · intro x a hx ha
    exact (ha (order_mem a)).elim
  · intro a ha
    exact (ha (order_mem a)).elim

theorem observationState_step
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β)
    {x : α} {xs : List α} {state : State α β} (z : β)
    (hpair : (x :: xs).Pairwise fun a b => b < a)
    (hstate : ObservationState G H host part threshold momentExponent default
      (x :: xs) state) :
    ObservationState G H host part threshold momentExponent default xs
      (step G H host part threshold momentExponent default x state z) := by
  have hbelow : ∀ y ∈ xs, y < x := (List.pairwise_cons.mp hpair).1
  constructor
  · intro y a hy ha
    by_cases hax : a = x
    · subst a
      exact hbelow y hy
    · exact hstate.before (by simp [hy]) (by simp [hax, ha])
  · intro a ha
    by_cases hax : a = x
    · subst a
      simp only [step, Function.update_self]
      congr 1
      funext y
      have hyx : x < (y : α) := (by
        simpa [forwardNeighbors] using y.property : H.Adj x y ∧ x < y).2
      exact (value_step_of_ne G H host part threshold momentExponent default state
        (ne_of_gt hyx) z).symm
    · have hold := hstate.formula a (by simp [hax, ha])
      rw [show (step G H host part threshold momentExponent default x state z).observed a =
          state.observed a by simp [step, hax]]
      rw [hold]
      congr 1
      funext y
      apply Eq.symm
      apply value_step_of_ne G H host part threshold momentExponent default state
      intro hyx
      have hxa : x < a := hstate.before (by simp) (by simp [hax, ha])
      have hax' : a < x := (by
        simpa [forwardNeighbors] using y.property : H.Adj a y ∧ a < y).2.trans_eq hyx
      exact (lt_asymm hxa hax').elim

theorem stateRun_observation_final (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β)
    {remaining : List α} {state final : State α β}
    (hrun : Process.StateRun
      (maskedChoices I G H host part default)
      (step G H host part threshold momentExponent default)
      remaining state final)
    (hpair : remaining.Pairwise fun a b => b < a)
    (hstate : ObservationState G H host part threshold momentExponent default
      remaining state) :
    ObservationState G H host part threshold momentExponent default [] final := by
  induction hrun with
  | nil state => simpa using hstate
  | @cons x xs state final z hz hrest ih =>
      exact ih (List.pairwise_cons.mp hpair).2
        (observationState_step G H host part threshold momentExponent default z
          hpair hstate)

theorem final_observed_formula (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β)
    {final : State α β}
    (hrun : Process.StateRun
      (maskedChoices I G H host part default)
      (step G H host part threshold momentExponent default)
      order (initialState : State α β) final) (x : α) :
    final.observed x =
      FiniteDefect.defectPower G (threshold x)
        (fun y : forwardNeighbors H x => value default final y)
        (host (part x)) momentExponent := by
  have hfinal := stateRun_observation_final I G H host part threshold momentExponent
    default hrun order_pairwise
      (observationState_initial G H host part threshold momentExponent default)
  exact hfinal.formula x (by simp)

theorem defectPower_sq (G : SimpleGraph β) [DecidableRel G.Adj]
    (θ D : ℕ) {κ : Type*} [Fintype κ] (q : κ → β) (T : Finset β) :
    (FiniteDefect.defectPower G θ q T (2 * D)) ^ 2 =
      FiniteDefect.defectPower G θ q T (4 * D) := by
  unfold FiniteDefect.defectPower
  by_cases hz : FiniteDefect.defect G θ q T = 0
  · simp [hz]
  · simp only [hz, if_false]
    rw [← pow_mul]
    congr 1
    omega

theorem final_observed_sq_formula (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (D : ℕ) (default : β)
    {final : State α β}
    (hrun : Process.StateRun
      (maskedChoices I G H host part default)
      (step G H host part threshold (2 * D) default)
      order (initialState : State α β) final) (x : α) :
    (final.observed x) ^ 2 =
      FiniteDefect.defectPower G (threshold x)
        (fun y : forwardNeighbors H x => value default final y)
        (host (part x)) (4 * D) := by
  rw [final_observed_formula I G H host part threshold (2 * D) default hrun x]
  exact defectPower_sq G (threshold x) D _ _

/-- A terminal neutral average is an independent-coordinate average. -/
theorem terminalNeutralAverage_eq_coordinateAverage (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (hhost : ∀ i, (host i).Nonempty)
    (part : α → ι) (threshold : α → ℕ)
    (D : ℕ) (default : β) (x : α)
    (hneutral : forwardNeighbors H x ⊆ I) :
    neutralAverage I G H host part threshold (2 * D) default
        (fun final => (final.observed x) ^ 2) =
      Process.coordinateAverage (fun y => host (part y)) order
        (fun _ => default)
        (fun f => FiniteDefect.defectPower G (threshold x)
          (fun y : forwardNeighbors H x => f y)
          (host (part x)) (4 * D)) := by
  let payoff : (α → β) → ℝ := fun f =>
    FiniteDefect.defectPower G (threshold x)
      (fun y : forwardNeighbors H x => f y) (host (part x)) (4 * D)
  have hpayoff : ∀ f g : α → β,
      (∀ y ∈ forwardNeighbors H x, f y = g y) → payoff f = payoff g := by
    intro f g hfg
    unfold payoff
    congr 1
    funext y
    exact hfg y y.property
  calc
    neutralAverage I G H host part threshold (2 * D) default
        (fun final => (final.observed x) ^ 2) =
      Process.stateAverage (maskedChoices I G H host part default)
        (step G H host part threshold (2 * D) default) order
        (initialState : State α β) (fun final => payoff (value default final)) := by
          apply Process.stateAverage_congr
          intro final hrun
          exact final_observed_sq_formula I G H host part threshold D default hrun x
    _ = Process.coordinateAverage (fun y => host (part y)) order
        (value default (initialState : State α β)) payoff := by
      apply Process.stateAverage_eq_fixedAverage
      · exact fun y state => maskedChoices_nonempty I G H host hhost part default y state
      · exact fun y => hhost (part y)
      · intro y state hy
        simp [maskedChoices, hneutral hy]
      · exact fun y state z =>
          value_step_self G H host part threshold (2 * D) default state y z
      · exact fun y state z a hay =>
          value_step_of_ne G H host part threshold (2 * D) default state hay z
      · exact hpayoff
    _ = Process.coordinateAverage (fun y => host (part y)) order
        (fun _ => default) payoff := by
      apply Process.fixedAverage_congr_on
      · intro y hy hyorder
        exact (hyorder (order_mem y)).elim
      · exact hpayoff
    _ = Process.coordinateAverage (fun y => host (part y)) order
        (fun _ => default)
        (fun f => FiniteDefect.defectPower G (threshold x)
          (fun y : forwardNeighbors H x => f y)
          (host (part x)) (4 * D)) := rfl

end RandomGreedy
end Erdos163
