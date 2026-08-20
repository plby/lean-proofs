/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.AdaptiveEmbedding

/-!
# Averaging Lee's terminal class criterion

This file converts a weighted bound for the expected recorded defects into a
single run satisfying the deterministic terminal-mass criterion.  Summing
with weight `2 / θ_i` is the step which retains Lee's decisive factor
`|W_i| / θ_i` rather than losing a factor equal to the whole target order.
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

noncomputable def average
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    (payoff : State α β → ℝ) : ℝ :=
  AdaptiveProcess.average
    (choices G H host part threshold defaultTarget default)
    (step G H host part threshold momentExponent defaultTarget default)
    (Fintype.card α) initialState payoff

theorem choices_nonempty
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (hhost : ∀ i, (host i).Nonempty)
    (part : α → ι) (threshold : ι → ℕ)
    (defaultTarget : α) (default : β) (state : State α β) :
    (choices G H host part threshold defaultTarget default state).Nonempty := by
  exact RandomGreedy.choices_nonempty G H host hhost part default state.core
    (next G H host part threshold defaultTarget default state)

theorem stateRun_remaining_card
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    (runChoices : State α β → Finset β)
    {fuel : ℕ} {state final : State α β}
    (hrun : AdaptiveProcess.StateRun
      runChoices
      (step G H host part threshold momentExponent defaultTarget default)
      fuel state final)
    (hfuel : fuel ≤ state.remaining.card) :
    final.remaining.card + fuel = state.remaining.card := by
  induction hrun with
  | nil state => simp
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
      have hcard :
          (step G H host part threshold momentExponent defaultTarget default
            state z).remaining.card + 1 = state.remaining.card := by
        simp only [step, stepAt]
        rw [Finset.card_erase_of_mem hx]
        omega
      calc
        final.remaining.card + (fuel + 1) =
            (final.remaining.card + fuel) + 1 := by omega
        _ = (step G H host part threshold momentExponent defaultTarget default
              state z).remaining.card + 1 := by rw [ih hfuel']
        _ = state.remaining.card := hcard

theorem stateRun_schedule_final
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    (runChoices : State α β → Finset β)
    {fuel : ℕ} {state final : State α β}
    (hrun : AdaptiveProcess.StateRun
      runChoices
      (step G H host part threshold momentExponent defaultTarget default)
      fuel state final)
    (hschedule : ScheduleState part state)
    (hfuel : fuel ≤ state.remaining.card) :
    ScheduleState part final := by
  induction hrun with
  | nil state => exact hschedule
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
          default hne z hschedule) hfuel'

/-! ## Recorded defects for an adaptive exposure order -/

structure RecordedDefects (momentExponent : ℕ) (state : State α β) : Prop where
  recorded : ∀ x, RandomGreedy.assigned state.core x →
    state.core.observed x =
      if state.core.defectSeen x = 0 then 0
      else state.core.defectSeen x ^ momentExponent
  defect_zero_or_one_le : ∀ x, RandomGreedy.assigned state.core x →
    state.core.defectSeen x = 0 ∨ 1 ≤ state.core.defectSeen x

theorem recordedDefects_initial (momentExponent : ℕ) :
    RecordedDefects momentExponent (initialState : State α β) := by
  constructor <;> intro x hx
  · simp [RandomGreedy.assigned, initialState, RandomGreedy.initialState] at hx
  · simp [RandomGreedy.assigned, initialState, RandomGreedy.initialState] at hx

theorem recordedDefects_stepAt
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (default : β) (x : α)
    {state : State α β} (z : β)
    (hstate : RecordedDefects momentExponent state) :
    RecordedDefects momentExponent
      (stepAt G H host part threshold momentExponent default x state z) := by
  constructor
  · intro y hy
    by_cases hyx : y = x
    · subst y
      simp [stepAt, RandomGreedy.step, FiniteDefect.defectPower]
    · have hyold : RandomGreedy.assigned state.core y :=
        (RandomGreedy.assigned_step_of_ne G H host part (threshold ∘ part)
          momentExponent default state.core hyx z).mp hy
      simpa [stepAt, RandomGreedy.step, hyx] using hstate.recorded y hyold
  · intro y hy
    by_cases hyx : y = x
    · subst y
      simp only [stepAt, RandomGreedy.step, Function.update_self]
      by_cases hz : FiniteDefect.defect G (threshold (part x))
          (fun y : RandomGreedy.forwardNeighbors H x =>
            RandomGreedy.value default state.core y) (host (part x)) = 0
      · exact Or.inl hz
      · exact Or.inr (FiniteDefect.one_le_defect_of_ne_zero G hz)
    · have hyold : RandomGreedy.assigned state.core y :=
        (RandomGreedy.assigned_step_of_ne G H host part (threshold ∘ part)
          momentExponent default state.core hyx z).mp hy
      simpa [stepAt, RandomGreedy.step, hyx] using
        hstate.defect_zero_or_one_le y hyold

theorem stateRun_recordedDefects_final
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    (runChoices : State α β → Finset β)
    {fuel : ℕ} {state final : State α β}
    (hrun : AdaptiveProcess.StateRun
      runChoices
      (step G H host part threshold momentExponent defaultTarget default)
      fuel state final)
    (hstate : RecordedDefects momentExponent state) :
    RecordedDefects momentExponent final := by
  induction hrun with
  | nil state => exact hstate
  | @cons fuel state final z hz hrest ih =>
      exact ih (recordedDefects_stepAt G H host part threshold momentExponent
        default (next G H host part threshold defaultTarget default state) z hstate)

theorem final_observed_nonneg
    (momentExponent : ℕ) {state : State α β}
    (hrecorded : RecordedDefects momentExponent state) {x : α}
    (hx : RandomGreedy.assigned state.core x) :
    0 ≤ state.core.observed x := by
  rw [hrecorded.recorded x hx]
  split_ifs with hz
  · exact le_rfl
  · exact pow_nonneg
      ((hrecorded.defect_zero_or_one_le x hx).resolve_left hz |>.trans' zero_le_one) _

theorem partDefectMass_eq_sum_observed_of_complete
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (default : β) (hexponent : 0 < momentExponent)
    {state : State α β} (hschedule : ScheduleState part state)
    (hempty : state.remaining = ∅)
    (hrecorded : RecordedDefects momentExponent state) (i : ι) :
    partDefectMass G H host part threshold default state i momentExponent =
      ∑ x ∈ Finset.univ.filter fun x => part x = i, state.core.observed x := by
  unfold partDefectMass
  apply Finset.sum_congr rfl
  intro x hx
  have hxassigned : RandomGreedy.assigned state.core x :=
    (hschedule.assigned_iff x).2 (by simp [hempty])
  simp only [realizedDefect, if_pos hxassigned]
  rw [hrecorded.recorded x hxassigned]
  by_cases hz : state.core.defectSeen x = 0
  · simp [hz, Nat.ne_of_gt hexponent]
  · simp [hz]

/-! ## Selection of a run -/

theorem hasCopy_of_weighted_average_observed_lt_one
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    (hhostNonempty : ∀ i, (host i).Nonempty)
    (hhostDisjoint : ∀ ⦃i j⦄, i ≠ j → Disjoint (host i) (host j))
    (hpart : ∀ ⦃a b⦄, H.Adj a b → part a ≠ part b)
    (horder : ∀ ⦃a b⦄, H.Adj a b → (a < b ↔ part a < part b))
    (hthreshold : ∀ i, 0 < threshold i)
    (hpartSize : ∀ x, 2 * (RandomGreedy.partVertices part x).card ≤
      threshold (part x))
    (hexponent : 0 < momentExponent)
    (htotal :
      ∑ x : α, (2 / (threshold (part x) : ℝ)) *
          average G H host part threshold momentExponent defaultTarget default
            (fun final => final.core.observed x) < 1) :
    HasCopy H G := by
  let payoff : State α β → ℝ := fun final =>
    ∑ x : α, (2 / (threshold (part x) : ℝ)) * final.core.observed x
  have havg : average G H host part threshold momentExponent defaultTarget
      default payoff =
      ∑ x : α, (2 / (threshold (part x) : ℝ)) *
        average G H host part threshold momentExponent defaultTarget default
          (fun final => final.core.observed x) := by
    unfold average payoff
    rw [AdaptiveProcess.average_sum]
    apply Finset.sum_congr rfl
    intro x hx
    exact AdaptiveProcess.average_const_mul _ _ _ _ _ _
  obtain ⟨final, hrun, hpayoff⟩ :=
    AdaptiveProcess.exists_stateRun_le_average
      (choices G H host part threshold defaultTarget default)
      (step G H host part threshold momentExponent defaultTarget default)
      (choices_nonempty G H host hhostNonempty part threshold defaultTarget default)
      (Fintype.card α) initialState payoff
  have hpayoff_lt : payoff final < 1 := by
    change payoff final ≤
      average G H host part threshold momentExponent defaultTarget default payoff
      at hpayoff
    have havg_lt :
        average G H host part threshold momentExponent defaultTarget default payoff < 1 := by
      rw [havg]
      exact htotal
    exact hpayoff.trans_lt havg_lt
  have hfuel : Fintype.card α ≤
      (initialState : State α β).remaining.card := by simp [initialState]
  have hcard := stateRun_remaining_card G H host part threshold momentExponent
    defaultTarget default
      (choices G H host part threshold defaultTarget default) hrun hfuel
  have hempty : final.remaining = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [initialState] using hcard
  have hschedule := stateRun_schedule_final G H host part threshold momentExponent
    defaultTarget default
      (choices G H host part threshold defaultTarget default) hrun
      (scheduleState_initial part) hfuel
  have hrecorded := stateRun_recordedDefects_final G H host part threshold
    momentExponent defaultTarget default
      (choices G H host part threshold defaultTarget default) hrun
      (recordedDefects_initial momentExponent)
  apply hasCopy_of_stateRun_and_terminal_masses G H host part threshold
    momentExponent defaultTarget default hhostDisjoint hpart horder hthreshold
    hpartSize hexponent hrun
  intro i
  have hmass := partDefectMass_eq_sum_observed_of_complete G H host part
    threshold momentExponent default hexponent hschedule hempty hrecorded i
  have hpartPayoff :
      (2 / (threshold i : ℝ)) *
          partDefectMass G H host part threshold default final i momentExponent ≤
        payoff final := by
    rw [hmass]
    rw [Finset.mul_sum]
    dsimp [payoff]
    calc
      (∑ x ∈ Finset.univ.filter fun x => part x = i,
          2 / (threshold i : ℝ) * final.core.observed x) =
        ∑ x ∈ Finset.univ.filter fun x => part x = i,
          2 / (threshold (part x) : ℝ) * final.core.observed x := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [(Finset.mem_filter.mp hx).2]
      _ ≤ ∑ x ∈ (Finset.univ : Finset α),
          2 / (threshold (part x) : ℝ) * final.core.observed x := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact Finset.filter_subset _ _
            · intro x hx hxi
              have hθ0 : (0 : ℝ) ≤ threshold (part x) := by positivity
              exact mul_nonneg (div_nonneg (by norm_num) hθ0)
                (final_observed_nonneg momentExponent hrecorded
                  ((hschedule.assigned_iff x).2 (by simp [hempty])))
  have hweighted_lt :
      (2 / (threshold i : ℝ)) *
          partDefectMass G H host part threshold default final i momentExponent < 1 :=
    hpartPayoff.trans_lt hpayoff_lt
  have hθ : (0 : ℝ) < threshold i := by exact_mod_cast hthreshold i
  have hmass0 : 0 ≤
      partDefectMass G H host part threshold default final i momentExponent := by
    rw [hmass]
    exact Finset.sum_nonneg fun x hx =>
      final_observed_nonneg momentExponent hrecorded
        ((hschedule.assigned_iff x).2 (by simp [hempty]))
  have hscaled :
      (2 / (threshold i : ℝ) *
          partDefectMass G H host part threshold default final i momentExponent) *
          threshold i < 1 * threshold i :=
    mul_lt_mul_of_pos_right hweighted_lt hθ
  have hcancel :
      (2 / (threshold i : ℝ) *
        partDefectMass G H host part threshold default final i momentExponent) *
          threshold i =
        2 * partDefectMass G H host part threshold default final i momentExponent := by
    field_simp
  rw [hcancel, one_mul] at hscaled
  nlinarith

end AdaptiveGreedy
end Erdos163
