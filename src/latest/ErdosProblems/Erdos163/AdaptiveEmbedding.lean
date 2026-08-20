/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.AdaptiveGreedy

/-!
# Deterministic correctness of Lee's adaptive schedule

This file iterates the local maximum-defect estimate.  A successful run uses
an unused common neighbor at every transition; after exactly `|V(H)|`
transitions its recorded map is an ordinary (not induced) graph embedding.
-/

open Finset

namespace Erdos163
namespace AdaptiveGreedy

universe u v w

variable {α : Type u} {β : Type v} {ι : Type w}
  [Fintype α] [DecidableEq α] [LinearOrder α]
  [Fintype β] [DecidableEq β]
  [DecidableEq ι] [LinearOrder ι]

inductive SuccessfulRun
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β) :
    ℕ → State α β → State α β → Prop
  | nil (state) : SuccessfulRun G H host part threshold momentExponent
      defaultTarget default 0 state state
  | cons {fuel : ℕ} {state final : State α β} {z : β}
      (hne : state.remaining.Nonempty)
      (hz : z ∈ RandomGreedy.unusedCandidates G H host part default state.core
        (next G H host part threshold defaultTarget default state))
      (hrest : SuccessfulRun G H host part threshold momentExponent
        defaultTarget default fuel
        (step G H host part threshold momentExponent defaultTarget default state z) final) :
      SuccessfulRun G H host part threshold momentExponent
        defaultTarget default (fuel + 1) state final

theorem SuccessfulRun.remaining_card
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    {fuel : ℕ} {state final : State α β}
    (hrun : SuccessfulRun G H host part threshold momentExponent
      defaultTarget default fuel state final) :
    final.remaining.card + fuel = state.remaining.card := by
  induction hrun with
  | nil state => simp
  | @cons fuel state final z hne hz hrest ih =>
      have hx := next_mem G H host part threshold defaultTarget default state hne
      have hcard :
          (step G H host part threshold momentExponent defaultTarget default
            state z).remaining.card + 1 = state.remaining.card := by
        simp only [step, stepAt]
        rw [Finset.card_erase_of_mem hx]
        exact Nat.sub_add_cancel (Finset.card_pos.mpr ⟨_, hx⟩)
      calc
        final.remaining.card + (fuel + 1) =
            (final.remaining.card + fuel) + 1 := by simp [Nat.add_assoc]
        _ = (step G H host part threshold momentExponent defaultTarget default
            state z).remaining.card + 1 := by rw [ih]
        _ = state.remaining.card := hcard

theorem SuccessfulRun.good_final
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    (hhost : ∀ ⦃i j⦄, i ≠ j → Disjoint (host i) (host j))
    (hpart : ∀ ⦃a b⦄, H.Adj a b → part a ≠ part b)
    (horder : ∀ ⦃a b⦄, H.Adj a b → (a < b ↔ part a < part b))
    {fuel : ℕ} {state final : State α β}
    (hrun : SuccessfulRun G H host part threshold momentExponent
      defaultTarget default fuel state final)
    (hgood : GoodState G H host part default state)
    (hordered : DefectsOrdered G H host part threshold default state) :
    GoodState G H host part default final ∧
      DefectsOrdered G H host part threshold default final := by
  induction hrun with
  | nil state => exact ⟨hgood, hordered⟩
  | @cons fuel state final z hne hz hrest ih =>
      exact ih
        (goodState_step G H host part threshold momentExponent defaultTarget default
          hhost hpart horder hne hgood hz)
        (defectsOrdered_step G H host part threshold momentExponent defaultTarget
          default hpart hne z hgood hordered)

theorem SuccessfulRun.hasCopy
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    (hhost : ∀ ⦃i j⦄, i ≠ j → Disjoint (host i) (host j))
    (hpart : ∀ ⦃a b⦄, H.Adj a b → part a ≠ part b)
    (horder : ∀ ⦃a b⦄, H.Adj a b → (a < b ↔ part a < part b))
    {final : State α β}
    (hrun : SuccessfulRun G H host part threshold momentExponent
      defaultTarget default (Fintype.card α) initialState final) :
    HasCopy H G := by
  have hcard := hrun.remaining_card G H host part threshold momentExponent
    defaultTarget default
  have hempty : final.remaining = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [initialState] using hcard
  have hfinal := hrun.good_final G H host part threshold momentExponent
    defaultTarget default hhost hpart horder
    (goodState_initial G H host part default)
    (defectsOrdered_initial G H host part threshold default)
  refine ⟨{
    toFun := RandomGreedy.value default final.core
    injective' := ?_
    map_adj' := ?_
  }⟩
  · intro x y hxy
    exact hfinal.1.injective
      ((hfinal.1.assigned_iff x).2 (by simp [hempty]))
      ((hfinal.1.assigned_iff y).2 (by simp [hempty])) hxy
  · intro x y hxy
    exact hfinal.1.map_adj
      ((hfinal.1.assigned_iff x).2 (by simp [hempty]))
      ((hfinal.1.assigned_iff y).2 (by simp [hempty])) hxy

/-- A literal run of the random rule for which Lee's class-moment condition
holds at every nonterminal state. -/
inductive MassControlledRun
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β) :
    ℕ → State α β → State α β → Prop
  | nil (state) : MassControlledRun G H host part threshold momentExponent
      defaultTarget default 0 state state
  | cons {fuel : ℕ} {state final : State α β} {z : β}
      (hne : state.remaining.Nonempty)
      (hmass : partDefectMass G H host part threshold default state
        (part (next G H host part threshold defaultTarget default state)) momentExponent ≤
          (threshold (part
            (next G H host part threshold defaultTarget default state)) : ℝ) / 2)
      (hz : z ∈ choices G H host part threshold defaultTarget default state)
      (hrest : MassControlledRun G H host part threshold momentExponent
        defaultTarget default fuel
        (step G H host part threshold momentExponent defaultTarget default state z) final) :
      MassControlledRun G H host part threshold momentExponent
        defaultTarget default (fuel + 1) state final

theorem MassControlledRun.toSuccessful
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    (hhost : ∀ ⦃i j⦄, i ≠ j → Disjoint (host i) (host j))
    (hpart : ∀ ⦃a b⦄, H.Adj a b → part a ≠ part b)
    (horder : ∀ ⦃a b⦄, H.Adj a b → (a < b ↔ part a < part b))
    (hthreshold : ∀ i, 0 < threshold i)
    (hpartSize : ∀ x, 2 * (RandomGreedy.partVertices part x).card ≤
      threshold (part x))
    (hexponent : 0 < momentExponent)
    {fuel : ℕ} {state final : State α β}
    (hrun : MassControlledRun G H host part threshold momentExponent
      defaultTarget default fuel state final)
    (hgood : GoodState G H host part default state)
    (hordered : DefectsOrdered G H host part threshold default state) :
    SuccessfulRun G H host part threshold momentExponent
      defaultTarget default fuel state final := by
  induction hrun with
  | nil state => exact .nil state
  | @cons fuel state final z hne hmass hz hrest ih =>
      have hchoices := choices_eq_unused_of_partDefectMass_le G H host part
        threshold momentExponent defaultTarget default hthreshold hpartSize hne
        hgood hordered hmass hexponent
      have hzunused : z ∈ RandomGreedy.unusedCandidates G H host part default
          state.core (next G H host part threshold defaultTarget default state) := by
        simpa [hchoices] using hz
      exact .cons hne hzunused
        (ih
          (goodState_step G H host part threshold momentExponent defaultTarget default
            hhost hpart horder hne hgood hzunused)
          (defectsOrdered_step G H host part threshold momentExponent defaultTarget
            default hpart hne z hgood hordered))

theorem MassControlledRun.hasCopy
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    (hhost : ∀ ⦃i j⦄, i ≠ j → Disjoint (host i) (host j))
    (hpart : ∀ ⦃a b⦄, H.Adj a b → part a ≠ part b)
    (horder : ∀ ⦃a b⦄, H.Adj a b → (a < b ↔ part a < part b))
    (hthreshold : ∀ i, 0 < threshold i)
    (hpartSize : ∀ x, 2 * (RandomGreedy.partVertices part x).card ≤
      threshold (part x))
    (hexponent : 0 < momentExponent)
    {final : State α β}
    (hrun : MassControlledRun G H host part threshold momentExponent
      defaultTarget default (Fintype.card α) initialState final) :
    HasCopy H G := by
  exact (hrun.toSuccessful G H host part threshold momentExponent defaultTarget
    default hhost hpart horder hthreshold hpartSize hexponent
    (goodState_initial G H host part default)
    (defectsOrdered_initial G H host part threshold default)).hasCopy
      G H host part threshold momentExponent defaultTarget default hhost hpart horder

/-! ## Relating a visited class moment to the terminal realization -/

/-- The scheduling facts which hold for every run, including histories which
use one of the two failure branches. -/
structure ScheduleState (part : α → ι) (state : State α β) : Prop where
  assigned_iff : ∀ x, RandomGreedy.assigned state.core x ↔ x ∉ state.remaining
  parts_ordered : ∀ ⦃x y⦄, x ∈ state.remaining →
    RandomGreedy.assigned state.core y → part x ≤ part y

theorem ScheduleState.of_good
    (G : SimpleGraph β) (H : SimpleGraph α) (host : ι → Finset β)
    (part : α → ι) (default : β) {state : State α β}
    (hgood : GoodState G H host part default state) : ScheduleState part state :=
  ⟨hgood.assigned_iff, hgood.parts_ordered⟩

theorem scheduleState_initial (part : α → ι) :
    ScheduleState part (initialState : State α β) := by
  constructor
  · intro x
    simp [RandomGreedy.assigned, initialState, RandomGreedy.initialState]
  · intro x y hx hy
    simp [RandomGreedy.assigned, initialState, RandomGreedy.initialState] at hy

theorem scheduleState_step
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    {state : State α β} (hne : state.remaining.Nonempty) (z : β)
    (hschedule : ScheduleState part state) :
    ScheduleState part
      (step G H host part threshold momentExponent defaultTarget default state z) := by
  let x := next G H host part threshold defaultTarget default state
  have hx := next_mem G H host part threshold defaultTarget default state hne
  constructor
  · intro y
    by_cases hyx : y = x
    · subst y
      change RandomGreedy.assigned
          (RandomGreedy.step G H host part (threshold ∘ part) momentExponent
            default x state.core z) x ↔ x ∉ state.remaining.erase x
      simp
    · change RandomGreedy.assigned
        (RandomGreedy.step G H host part (threshold ∘ part) momentExponent
          default x state.core z) y ↔ y ∉ state.remaining.erase x
      rw [RandomGreedy.assigned_step_of_ne G H host part (threshold ∘ part)
        momentExponent default state.core hyx z]
      rw [hschedule.assigned_iff]
      simp [hyx]
  · intro a b ha hb
    by_cases hbx : b = x
    · subst b
      exact part_le_part_next G H host part threshold defaultTarget default state hne
        (Finset.mem_erase.mp ha).2
    · exact hschedule.parts_ordered (Finset.mem_erase.mp ha).2
        ((RandomGreedy.assigned_step_of_ne G H host part (threshold ∘ part)
          momentExponent default state.core hbx z).mp hb)

theorem partDefectMass_stepAt_same_part
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent s : ℕ) (default : β)
    (hpart : ∀ ⦃a b⦄, H.Adj a b → part a ≠ part b)
    {state : State α β} {x : α} (hx : x ∈ state.remaining) (z : β)
    (hschedule : ScheduleState part state) :
    partDefectMass G H host part threshold default
        (stepAt G H host part threshold momentExponent default x state z) (part x) s =
      partDefectMass G H host part threshold default state (part x) s := by
  classical
  unfold partDefectMass
  apply Finset.sum_congr rfl
  intro y hy
  have hypart : part y = part x := (Finset.mem_filter.mp hy).2
  by_cases hyx : y = x
  · subst y
    have hxunassigned : ¬ RandomGreedy.assigned state.core x := by
      intro hassigned
      exact ((hschedule.assigned_iff x).mp hassigned) hx
    have hxassigned' : RandomGreedy.assigned
        (stepAt G H host part threshold momentExponent default x state z).core x := by
      exact RandomGreedy.assigned_step_self G H host part (threshold ∘ part)
        momentExponent default state.core x z
    simp only [realizedDefect, if_pos hxassigned', if_neg hxunassigned]
    simp [stepAt, RandomGreedy.step, currentDefect]
  · have hstable := currentDefect_stepAt_of_same_part G H host part threshold
      momentExponent default hpart state hypart z
    have hassigned_iff : RandomGreedy.assigned
          (stepAt G H host part threshold momentExponent default x state z).core y ↔
        RandomGreedy.assigned state.core y := by
      exact RandomGreedy.assigned_step_of_ne G H host part (threshold ∘ part)
        momentExponent default state.core hyx z
    by_cases hyassigned : RandomGreedy.assigned state.core y
    · have hyassigned' := hassigned_iff.mpr hyassigned
      simp only [realizedDefect, if_pos hyassigned', if_pos hyassigned]
      simp [stepAt, RandomGreedy.step, hyx]
    · have hyassigned' : ¬ RandomGreedy.assigned
          (stepAt G H host part threshold momentExponent default x state z).core y :=
        fun h => hyassigned (hassigned_iff.mp h)
      simp only [realizedDefect, if_neg hyassigned', if_neg hyassigned]
      exact congrArg (fun t : ℝ => t ^ s) hstable

theorem partDefectMass_stepAt_of_part_assigned
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent s : ℕ) (default : β)
    {state : State α β} {x : α} (i : ι) (z : β)
    (hx : x ∈ state.remaining)
    (hschedule : ScheduleState part state)
    (hall : ∀ y, part y = i → RandomGreedy.assigned state.core y) :
    partDefectMass G H host part threshold default
        (stepAt G H host part threshold momentExponent default x state z) i s =
      partDefectMass G H host part threshold default state i s := by
  classical
  unfold partDefectMass
  apply Finset.sum_congr rfl
  intro y hy
  have hypart : part y = i := (Finset.mem_filter.mp hy).2
  have hyassigned := hall y hypart
  have hyx : y ≠ x := by
    intro heq
    subst y
    exact ((hschedule.assigned_iff x).mp hyassigned) hx
  have hassigned_iff : RandomGreedy.assigned
        (stepAt G H host part threshold momentExponent default x state z).core y ↔
      RandomGreedy.assigned state.core y := by
    exact RandomGreedy.assigned_step_of_ne G H host part (threshold ∘ part)
      momentExponent default state.core hyx z
  have hyassigned' := hassigned_iff.mpr hyassigned
  simp only [realizedDefect, if_pos hyassigned', if_pos hyassigned]
  simp [stepAt, RandomGreedy.step, hyx]

/-- Once a target part becomes the greatest remaining part, its realized
defect mass no longer changes during the rest of a run.  While that part is
active this is `partDefectMass_stepAt_same_part`; after the schedule moves to
a smaller part, every vertex of the old part is already assigned. -/
theorem partDefectMass_final_eq_of_stateRun
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent s : ℕ) (defaultTarget : α) (default : β)
    (hpart : ∀ ⦃a b⦄, H.Adj a b → part a ≠ part b)
    {fuel : ℕ} {state final : State α β} {i : ι}
    (hrun : AdaptiveProcess.StateRun
      (choices G H host part threshold defaultTarget default)
      (step G H host part threshold momentExponent defaultTarget default)
      fuel state final)
    (hschedule : ScheduleState part state)
    (hparts : ∀ ⦃y⦄, y ∈ state.remaining → part y ≤ i)
    (hfuel : fuel ≤ state.remaining.card) :
    partDefectMass G H host part threshold default final i s =
      partDefectMass G H host part threshold default state i s := by
  induction hrun with
  | nil state => rfl
  | @cons fuel state final z hz hrest ih =>
      have hcardpos : 0 < state.remaining.card := by omega
      have hne : state.remaining.Nonempty := Finset.card_pos.mp hcardpos
      let x := next G H host part threshold defaultTarget default state
      have hx : x ∈ state.remaining :=
        next_mem G H host part threshold defaultTarget default state hne
      have hxi : part x ≤ i := hparts hx
      have hstepMass :
          partDefectMass G H host part threshold default
              (step G H host part threshold momentExponent defaultTarget default
                state z) i s =
            partDefectMass G H host part threshold default state i s := by
        by_cases hxiEq : part x = i
        · subst i
          simpa [step, x] using
            partDefectMass_stepAt_same_part G H host part threshold
              momentExponent s default hpart hx z hschedule
        · have hxilt : part x < i := lt_of_le_of_ne hxi hxiEq
          have hall : ∀ y, part y = i →
              RandomGreedy.assigned state.core y := by
            intro y hyi
            by_contra hyassigned
            have hyrem : y ∈ state.remaining := by
              by_contra hynot
              exact hyassigned ((hschedule.assigned_iff y).2 hynot)
            have hiyx : i ≤ part x := by
              simpa [hyi, x] using
                part_le_part_next G H host part threshold defaultTarget default
                  state hne hyrem
            exact (not_le_of_gt hxilt) hiyx
          simpa [step, x] using
            partDefectMass_stepAt_of_part_assigned G H host part threshold
              momentExponent s default i z hx hschedule hall
      have hschedule' : ScheduleState part
          (step G H host part threshold momentExponent defaultTarget default
            state z) :=
        scheduleState_step G H host part threshold momentExponent defaultTarget
          default hne z hschedule
      have hparts' : ∀ ⦃y⦄,
          y ∈ (step G H host part threshold momentExponent defaultTarget default
            state z).remaining → part y ≤ i := by
        intro y hy
        exact hparts (Finset.mem_erase.mp (by simpa [step, stepAt, x] using hy)).2
      have hfuel' : fuel ≤
          (step G H host part threshold momentExponent defaultTarget default
            state z).remaining.card := by
        simp only [step, stepAt]
        rw [Finset.card_erase_of_mem hx]
        omega
      exact (ih hschedule' hparts' hfuel').trans hstepMass

/-- A full random run whose terminal mass is small in every target part is a
mass-controlled run: the preceding trace lemma transports the terminal bound
back to the unique time at which each part is active. -/
theorem stateRun_to_massControlled
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    (hpart : ∀ ⦃a b⦄, H.Adj a b → part a ≠ part b)
    {fuel : ℕ} {state final : State α β}
    (hrun : AdaptiveProcess.StateRun
      (choices G H host part threshold defaultTarget default)
      (step G H host part threshold momentExponent defaultTarget default)
      fuel state final)
    (hschedule : ScheduleState part state)
    (hfuel : fuel ≤ state.remaining.card)
    (hfinal : ∀ i, partDefectMass G H host part threshold default final i
      momentExponent ≤ (threshold i : ℝ) / 2) :
    MassControlledRun G H host part threshold momentExponent defaultTarget
      default fuel state final := by
  induction hrun with
  | nil state => exact .nil state
  | @cons fuel state final z hz hrest ih =>
      have hcardpos : 0 < state.remaining.card := by omega
      have hne : state.remaining.Nonempty := Finset.card_pos.mp hcardpos
      let x := next G H host part threshold defaultTarget default state
      have hx : x ∈ state.remaining :=
        next_mem G H host part threshold defaultTarget default state hne
      have hparts : ∀ ⦃y⦄, y ∈ state.remaining → part y ≤ part x := by
        intro y hy
        simpa [x] using
          part_le_part_next G H host part threshold defaultTarget default state
            hne hy
      have htrace := partDefectMass_final_eq_of_stateRun G H host part threshold
        momentExponent momentExponent defaultTarget default hpart
        (.cons hz hrest) hschedule hparts hfuel
      have hmass : partDefectMass G H host part threshold default state
          (part x) momentExponent ≤ (threshold (part x) : ℝ) / 2 := by
        rw [← htrace]
        exact hfinal (part x)
      have hschedule' : ScheduleState part
          (step G H host part threshold momentExponent defaultTarget default
            state z) :=
        scheduleState_step G H host part threshold momentExponent defaultTarget
          default hne z hschedule
      have hfuel' : fuel ≤
          (step G H host part threshold momentExponent defaultTarget default
            state z).remaining.card := by
        simp only [step, stepAt]
        rw [Finset.card_erase_of_mem hx]
        omega
      exact .cons hne (by simpa [x] using hmass) hz
        (ih hschedule' hfuel' hfinal)

/-- Terminal form of Lee's deterministic embedding criterion. -/
theorem hasCopy_of_stateRun_and_terminal_masses
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    (hhost : ∀ ⦃i j⦄, i ≠ j → Disjoint (host i) (host j))
    (hpart : ∀ ⦃a b⦄, H.Adj a b → part a ≠ part b)
    (horder : ∀ ⦃a b⦄, H.Adj a b → (a < b ↔ part a < part b))
    (hthreshold : ∀ i, 0 < threshold i)
    (hpartSize : ∀ x, 2 * (RandomGreedy.partVertices part x).card ≤
      threshold (part x))
    (hexponent : 0 < momentExponent)
    {final : State α β}
    (hrun : AdaptiveProcess.StateRun
      (choices G H host part threshold defaultTarget default)
      (step G H host part threshold momentExponent defaultTarget default)
      (Fintype.card α) initialState final)
    (hfinal : ∀ i, partDefectMass G H host part threshold default final i
      momentExponent ≤ (threshold i : ℝ) / 2) :
    HasCopy H G := by
  have hcontrolled := stateRun_to_massControlled G H host part threshold
    momentExponent defaultTarget default hpart hrun
    (scheduleState_initial part) (by simp [initialState]) hfinal
  exact hcontrolled.hasCopy G H host part threshold momentExponent
    defaultTarget default hhost hpart horder hthreshold hpartSize hexponent

end AdaptiveGreedy
end Erdos163
