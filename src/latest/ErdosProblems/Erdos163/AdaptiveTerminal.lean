/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.AdaptivePropagation

/-!
# Terminal moments for the adaptive schedule

An adaptive, history-dependent permutation of independent coordinates still
has the product distribution, provided the next coordinate is chosen before
its fresh value is sampled.  We prove that finite statement directly and use
it to identify Lee's neutralized terminal square moment with
`FiniteDefect.familyMoment`.
-/

open scoped BigOperators
open Finset

namespace Erdos163
namespace AdaptiveGreedy

universe u v w

variable {α : Type u} {β : Type v} {ι : Type w}
  [Fintype α] [DecidableEq α] [LinearOrder α]
  [Fintype β] [DecidableEq β]
  [DecidableEq ι] [LinearOrder ι]

theorem value_step_eq_update
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (default : β) (x : α)
    (state : State α β) (z : β) :
    RandomGreedy.value default
        (stepAt G H host part threshold momentExponent default x state z).core =
      Function.update (RandomGreedy.value default state.core) x z := by
  funext y
  by_cases hyx : y = x
  · subst y
    simp [stepAt]
  · have h := RandomGreedy.value_step_of_ne G H host part (threshold ∘ part)
      momentExponent default state.core hyx z
    simpa [stepAt, Function.update, hyx] using h

def relevantOrder (S remaining : Finset α) : List α :=
  RandomGreedy.order.filter fun x => x ∈ S ∧ x ∈ remaining

theorem relevantOrder_nodup (S remaining : Finset α) :
    (relevantOrder S remaining).Nodup :=
  RandomGreedy.order_nodup.filter _

/-- Projection of a state-dependent exposure process onto coordinates whose
transitions have been neutralized. -/
theorem adaptiveAverage_eq_coordinateAverage
    (I S : Finset α) (hSI : S ⊆ I)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (hhost : ∀ i, (host i).Nonempty)
    (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    {fuel : ℕ} (state : State α β) (hfuel : fuel = state.remaining.card)
    (payoff : (α → β) → ℝ)
    (hpayoff : ∀ f g, (∀ y ∈ S, f y = g y) → payoff f = payoff g) :
    AdaptiveProcess.average
        (maskedChoices I G H host part threshold defaultTarget default)
        (step G H host part threshold momentExponent defaultTarget default)
        fuel state (fun final => payoff (RandomGreedy.value default final.core)) =
      Process.coordinateAverage (fun y => host (part y))
        (relevantOrder S state.remaining)
        (RandomGreedy.value default state.core) payoff := by
  induction fuel generalizing state with
  | zero =>
      have hempty : state.remaining = ∅ := Finset.card_eq_zero.mp hfuel.symm
      simp [relevantOrder, hempty]
  | succ fuel ih =>
      have hcardpos : 0 < state.remaining.card := by omega
      have hne : state.remaining.Nonempty := Finset.card_pos.mp hcardpos
      let x := next G H host part threshold defaultTarget default state
      have hx : x ∈ state.remaining :=
        next_mem G H host part threshold defaultTarget default state hne
      let state' : β → State α β := fun z =>
        step G H host part threshold momentExponent defaultTarget default state z
      have hcard : ∀ z, fuel = (state' z).remaining.card := by
        intro z
        simp only [state', step, stepAt]
        rw [Finset.card_erase_of_mem hx]
        omega
      rw [AdaptiveProcess.average_succ]
      by_cases hxS : x ∈ S
      · have hxI : x ∈ I := hSI hxS
        have hchoices :
            maskedChoices I G H host part threshold defaultTarget default state =
              host (part x) := by simp [maskedChoices, x, hxI]
        have hxnot : x ∉ relevantOrder S (state.remaining.erase x) := by
          simp [relevantOrder]
        have hmem : ∀ y : α,
            y ∈ relevantOrder S state.remaining ↔
              y ∈ x :: relevantOrder S (state.remaining.erase x) := by
          intro y
          by_cases hyx : y = x
          · subst y
            have hxorder : x ∈ (RandomGreedy.order : List α) :=
              RandomGreedy.order_mem x
            simp [relevantOrder, hxorder, hxS, hx]
          · simp [relevantOrder, hyx]
        have hperm :
            Process.coordinateAverage (fun y => host (part y))
                (relevantOrder S state.remaining)
                (RandomGreedy.value default state.core) payoff =
              Process.coordinateAverage (fun y => host (part y))
                (x :: relevantOrder S (state.remaining.erase x))
                (RandomGreedy.value default state.core) payoff := by
          apply Process.coordinateAverage_eq_of_nodup_same_mem
          · exact relevantOrder_nodup S state.remaining
          · exact List.nodup_cons.mpr
              ⟨hxnot, relevantOrder_nodup S (state.remaining.erase x)⟩
          · exact hmem
        rw [hperm, Process.coordinateAverage_cons, hchoices]
        apply Finset.expect_congr rfl
        intro z hz
        rw [ih (state' z) (hcard z)]
        have hremaining : (state' z).remaining = state.remaining.erase x := rfl
        rw [hremaining]
        have hvalue : RandomGreedy.value default (state' z).core =
            Function.update (RandomGreedy.value default state.core) x z := by
          exact value_step_eq_update G H host part threshold momentExponent
            default x state z
        rw [hvalue]
      · have horder : relevantOrder S state.remaining =
            relevantOrder S (state.remaining.erase x) := by
          unfold relevantOrder
          apply List.filter_congr
          intro y hy
          by_cases hyS : y ∈ S
          · have hyx : y ≠ x := fun h => hxS (h ▸ hyS)
            simp [hyS, hyx]
          · simp [hyS]
        rw [horder]
        have hneChoices := maskedChoices_nonempty I G H host hhost part threshold
          defaultTarget default state
        calc
          (𝔼 z ∈ maskedChoices I G H host part threshold defaultTarget default state,
              AdaptiveProcess.average
                (maskedChoices I G H host part threshold defaultTarget default)
                (step G H host part threshold momentExponent defaultTarget default)
                fuel (state' z)
                (fun final => payoff (RandomGreedy.value default final.core))) =
              𝔼 z ∈ maskedChoices I G H host part threshold defaultTarget default state,
                Process.coordinateAverage (fun y => host (part y))
                  (relevantOrder S (state.remaining.erase x))
                  (RandomGreedy.value default (state' z).core) payoff := by
            apply Finset.expect_congr rfl
            intro z hz
            simpa [show (state' z).remaining = state.remaining.erase x from rfl] using
              ih (state' z) (hcard z)
          _ = 𝔼 _z ∈ maskedChoices I G H host part threshold defaultTarget default state,
                Process.coordinateAverage (fun y => host (part y))
                  (relevantOrder S (state.remaining.erase x))
                  (RandomGreedy.value default state.core) payoff := by
            apply Finset.expect_congr rfl
            intro z hz
            apply Process.fixedAverage_congr_on (fun y => host (part y)) S
            · intro y hyS hyorder
              have hyx : y ≠ x := fun h => hxS (h ▸ hyS)
              have hv := congrFun
                (value_step_eq_update G H host part threshold momentExponent
                  default x state z) y
              simpa [state', step, x, Function.update, hyx] using hv
            · exact hpayoff
          _ = Process.coordinateAverage (fun y => host (part y))
                (relevantOrder S (state.remaining.erase x))
                (RandomGreedy.value default state.core) payoff :=
            Finset.expect_const hneChoices _

/-! ## The recorded observation is a terminal function of higher values -/

structure ObservationState
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (default : β) (state : State α β) : Prop where
  formula : ∀ x, RandomGreedy.assigned state.core x →
    state.core.observed x =
      FiniteDefect.defectPower G (threshold (part x))
        (fun y : RandomGreedy.forwardNeighbors H x =>
          RandomGreedy.value default state.core y)
        (host (part x)) momentExponent

theorem observationState_initial
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (default : β) :
    ObservationState G H host part threshold momentExponent default
      (initialState : State α β) := by
  constructor
  intro x hx
  simp [RandomGreedy.assigned, initialState, RandomGreedy.initialState] at hx

theorem observationState_step
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    (horder : ∀ ⦃a b⦄, H.Adj a b → (a < b ↔ part a < part b))
    {state : State α β} (hne : state.remaining.Nonempty) (z : β)
    (hschedule : ScheduleState part state)
    (hstate : ObservationState G H host part threshold momentExponent default state) :
    ObservationState G H host part threshold momentExponent default
      (step G H host part threshold momentExponent defaultTarget default state z) := by
  let x := next G H host part threshold defaultTarget default state
  have hx : x ∈ state.remaining :=
    next_mem G H host part threshold defaultTarget default state hne
  constructor
  intro a ha
  by_cases hax : a = x
  · subst a
    change
      (RandomGreedy.step G H host part (threshold ∘ part) momentExponent
        default x state.core z).observed x =
      FiniteDefect.defectPower G (threshold (part x))
        (fun y : RandomGreedy.forwardNeighbors H x =>
          RandomGreedy.value default
            (RandomGreedy.step G H host part (threshold ∘ part) momentExponent
              default x state.core z) y)
        (host (part x)) momentExponent
    rw [show
      (RandomGreedy.step G H host part (threshold ∘ part) momentExponent
        default x state.core z).observed x =
        FiniteDefect.defectPower G (threshold (part x))
          (fun y : RandomGreedy.forwardNeighbors H x =>
            RandomGreedy.value default state.core y)
          (host (part x)) momentExponent by simp [RandomGreedy.step]]
    congr 1
    funext y
    have hyprop : H.Adj x (y : α) ∧ x < (y : α) := by
      simpa [RandomGreedy.forwardNeighbors] using y.property
    exact (RandomGreedy.value_step_of_ne G H host part (threshold ∘ part)
      momentExponent default state.core (H.ne_of_adj hyprop.1).symm z).symm
  · have haold : RandomGreedy.assigned state.core a :=
      (RandomGreedy.assigned_step_of_ne G H host part (threshold ∘ part)
        momentExponent default state.core hax z).mp ha
    rw [show (step G H host part threshold momentExponent defaultTarget default
        state z).core.observed a = state.core.observed a by
          simp [step, stepAt, RandomGreedy.step, x, hax]]
    rw [hstate.formula a haold]
    congr 1
    funext y
    symm
    apply RandomGreedy.value_step_of_ne G H host part (threshold ∘ part)
      momentExponent default state.core
    intro hyx
    have hyprop : H.Adj a (y : α) ∧ a < (y : α) := by
      simpa [RandomGreedy.forwardNeighbors] using y.property
    have haxAdj : H.Adj a x := by simpa [hyx] using hyprop.1
    have hpartlt : part a < part x := (horder haxAdj).1 (by
      simpa [hyx] using hyprop.2)
    have hpartle : part x ≤ part a := hschedule.parts_ordered hx haold
    exact (not_lt_of_ge hpartle) hpartlt

theorem stateRun_observation_final (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    (horder : ∀ ⦃a b⦄, H.Adj a b → (a < b ↔ part a < part b))
    {fuel : ℕ} {state final : State α β}
    (hrun : AdaptiveProcess.StateRun
      (maskedChoices I G H host part threshold defaultTarget default)
      (step G H host part threshold momentExponent defaultTarget default)
      fuel state final)
    (hschedule : ScheduleState part state)
    (hstate : ObservationState G H host part threshold momentExponent default state)
    (hfuel : fuel ≤ state.remaining.card) :
    ObservationState G H host part threshold momentExponent default final := by
  induction hrun with
  | nil state => exact hstate
  | @cons fuel state final z hz hrest ih =>
      have hcardpos : 0 < state.remaining.card := by omega
      have hne : state.remaining.Nonempty := Finset.card_pos.mp hcardpos
      have hx := next_mem G H host part threshold defaultTarget default state hne
      have hfuel' : fuel ≤
          (step G H host part threshold momentExponent defaultTarget default
            state z).remaining.card := by
        simp only [step, stepAt]
        rw [Finset.card_erase_of_mem hx]
        omega
      exact ih
        (scheduleState_step G H host part threshold momentExponent defaultTarget
          default hne z hschedule)
        (observationState_step G H host part threshold momentExponent defaultTarget
          default horder hne z hschedule hstate) hfuel'

theorem final_observed_formula (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    (horder : ∀ ⦃a b⦄, H.Adj a b → (a < b ↔ part a < part b))
    {final : State α β}
    (hrun : AdaptiveProcess.StateRun
      (maskedChoices I G H host part threshold defaultTarget default)
      (step G H host part threshold momentExponent defaultTarget default)
      (Fintype.card α) initialState final) (x : α) :
    final.core.observed x =
      FiniteDefect.defectPower G (threshold (part x))
        (fun y : RandomGreedy.forwardNeighbors H x =>
          RandomGreedy.value default final.core y)
        (host (part x)) momentExponent := by
  have hfuel : Fintype.card α ≤
      (initialState : State α β).remaining.card := by simp [initialState]
  have hobs := stateRun_observation_final I G H host part threshold momentExponent
    defaultTarget default horder hrun (scheduleState_initial part)
      (observationState_initial G H host part threshold momentExponent default) hfuel
  exact hobs.formula x
    (fullRun_assigned I G H host part threshold momentExponent defaultTarget
      default hrun x)

theorem terminalNeutralAverage_eq_familyMoment (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (hhost : ∀ i, (host i).Nonempty)
    (part : α → ι) (threshold : ι → ℕ)
    (D : ℕ) (defaultTarget : α) (default : β)
    (horder : ∀ ⦃a b⦄, H.Adj a b → (a < b ↔ part a < part b))
    (x : α) (hneutral : RandomGreedy.forwardNeighbors H x ⊆ I) :
    neutralAverage I G H host part threshold (2 * D) defaultTarget default
        (fun final => (final.core.observed x) ^ 2) =
      FiniteDefect.familyMoment G (threshold (part x)) (4 * D)
        (fun y : RandomGreedy.forwardNeighbors H x => host (part y))
        (host (part x)) := by
  let S := RandomGreedy.forwardNeighbors H x
  let A : α → Finset β := fun y => host (part y)
  let payoff : (α → β) → ℝ := fun f =>
    FiniteDefect.defectPower G (threshold (part x))
      (fun y : S => f y) (host (part x)) (4 * D)
  have hpayoff : ∀ f g : α → β,
      (∀ y ∈ S, f y = g y) → payoff f = payoff g := by
    intro f g hfg
    unfold payoff
    congr 1
    funext y
    exact hfg y y.property
  calc
    neutralAverage I G H host part threshold (2 * D) defaultTarget default
        (fun final => (final.core.observed x) ^ 2) =
      AdaptiveProcess.average
        (maskedChoices I G H host part threshold defaultTarget default)
        (step G H host part threshold (2 * D) defaultTarget default)
        (Fintype.card α) initialState
        (fun final => payoff (RandomGreedy.value default final.core)) := by
          unfold neutralAverage
          apply AdaptiveProcess.average_congr
          intro final hrun
          rw [final_observed_formula I G H host part threshold (2 * D)
            defaultTarget default horder hrun x]
          exact RandomGreedy.defectPower_sq G (threshold (part x)) D _ _
    _ = Process.coordinateAverage A
        (relevantOrder S (initialState : State α β).remaining)
        (RandomGreedy.value default (initialState : State α β).core) payoff := by
          exact adaptiveAverage_eq_coordinateAverage I S hneutral G H host hhost
            part threshold (2 * D) defaultTarget default (initialState : State α β)
            (by simp [initialState]) payoff hpayoff
    _ = Process.coordinateAverage A (RandomGreedy.order.filter (· ∈ S))
        (fun _ => default) payoff := by
          simp only [relevantOrder, initialState, Finset.mem_univ, and_true]
          apply Process.fixedAverage_congr_on A S
          · intro y hyS hyorder
            simp [RandomGreedy.value, RandomGreedy.initialState]
          · exact hpayoff
    _ = 𝔼 g ∈ FiniteDefect.familyTuples (fun y : S => A y),
          payoff (fun a => if ha : a ∈ S then g ⟨a, ha⟩ else default) := by
            apply Process.coordinateAverage_eq_familyAverage_on
            · exact RandomGreedy.order_nodup.filter _
            · intro a
              simp [RandomGreedy.order_mem]
    _ = FiniteDefect.familyMoment G (threshold (part x)) (4 * D)
        (fun y : S => host (part y)) (host (part x)) := by
          unfold FiniteDefect.familyMoment payoff A
          apply Finset.expect_congr rfl
          intro g hg
          congr 1
          funext y
          simp [y.property]

/-- Complete adaptive embedding theorem from literal host-part defect
moments. -/
theorem hasCopy_of_family_moments
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (defaultTarget : α) (default : β)
    (hhostNonempty : ∀ i, (host i).Nonempty)
    (hhostDisjoint : ∀ ⦃i j⦄, i ≠ j → Disjoint (host i) (host j))
    (hpart : ∀ ⦃a b⦄, H.Adj a b → part a ≠ part b)
    (horder : ∀ ⦃a b⦄, H.Adj a b → (a < b ↔ part a < part b))
    (hthreshold : ∀ i, 0 < threshold i)
    (hpartSize : ∀ x, 2 * (RandomGreedy.partVertices part x).card ≤
      threshold (part x))
    {γ : ℝ} (hγ : 1 ≤ γ)
    (hsize : ∀ x, ((host (part x)).card : ℝ) ≤ γ * threshold (part x))
    (D : ℕ) (hD : 0 < D)
    (hforward : ∀ x, (RandomGreedy.forwardNeighbors H x).card ≤ D)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hmoment : ∀ x,
      FiniteDefect.familyMoment G (threshold (part x)) (4 * D)
        (fun y : RandomGreedy.forwardNeighbors H x => host (part y))
        (host (part x)) ≤ μ)
    (htotal :
      ∑ x : α, (2 / (threshold (part x) : ℝ)) *
        (2 * RandomGreedy.branchCoefficient (2 * γ) D * μ) < 1) :
    HasCopy H G := by
  apply hasCopy_of_terminal_moments G H host part threshold defaultTarget default
    hhostNonempty hhostDisjoint hpart horder hthreshold hpartSize hγ hsize D
    hD hforward μ hμ
  · intro I x hneutral
    rw [terminalNeutralAverage_eq_familyMoment I G H host hhostNonempty part
      threshold D defaultTarget default horder x hneutral]
    exact hmoment x
  · exact htotal

end AdaptiveGreedy
end Erdos163
