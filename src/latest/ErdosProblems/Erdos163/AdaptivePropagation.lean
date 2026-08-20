/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.AdaptiveNeutralization

/-!
# Defect-moment propagation for the adaptive schedule

The analytic product estimate is independent of the exposure order.  This
file supplies the adaptive analogues of the recorded-cost invariants and
lifts the same branching estimate through `AdaptiveProcess.average`.
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

structure CostBoundState (C : ℝ) (state : State α β) : Prop where
  cost_nonneg : ∀ x, RandomGreedy.assigned state.core x →
    0 ≤ state.core.costSeen x
  cost_le : ∀ x, RandomGreedy.assigned state.core x →
    state.core.costSeen x ≤ C * max 1 (state.core.defectSeen x)

theorem costBoundState_initial (C : ℝ) :
    CostBoundState C (initialState : State α β) := by
  constructor <;> intro x hx
  · simp [RandomGreedy.assigned, initialState, RandomGreedy.initialState] at hx
  · simp [RandomGreedy.assigned, initialState, RandomGreedy.initialState] at hx

theorem costBoundState_stepAt
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (default : β) {γ : ℝ} (hγ : 1 ≤ γ)
    (hsize : ∀ x, ((host (part x)).card : ℝ) ≤ γ * threshold (part x))
    (x : α) {state : State α β} (z : β)
    (hstate : CostBoundState (2 * γ) state) :
    CostBoundState (2 * γ)
      (stepAt G H host part threshold momentExponent default x state z) := by
  constructor
  · intro y hy
    by_cases hyx : y = x
    · subst y
      simpa [stepAt, RandomGreedy.step] using
        RandomGreedy.localCost_nonneg G H host part default state.core x
    · have hyold : RandomGreedy.assigned state.core y :=
        (RandomGreedy.assigned_step_of_ne G H host part (threshold ∘ part)
          momentExponent default state.core hyx z).mp hy
      simpa [stepAt, RandomGreedy.step, hyx] using hstate.cost_nonneg y hyold
  · intro y hy
    by_cases hyx : y = x
    · subst y
      simpa [stepAt, RandomGreedy.step] using
        RandomGreedy.localCost_le_defect G H host part (threshold ∘ part)
          default state.core x hγ (hsize x)
    · have hyold : RandomGreedy.assigned state.core y :=
        (RandomGreedy.assigned_step_of_ne G H host part (threshold ∘ part)
          momentExponent default state.core hyx z).mp hy
      simpa [stepAt, RandomGreedy.step, hyx] using hstate.cost_le y hyold

theorem stateRun_costBound_final (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    {γ : ℝ} (hγ : 1 ≤ γ)
    (hsize : ∀ x, ((host (part x)).card : ℝ) ≤ γ * threshold (part x))
    {fuel : ℕ} {state final : State α β}
    (hrun : AdaptiveProcess.StateRun
      (maskedChoices I G H host part threshold defaultTarget default)
      (step G H host part threshold momentExponent defaultTarget default)
      fuel state final)
    (hstate : CostBoundState (2 * γ) state) :
    CostBoundState (2 * γ) final := by
  induction hrun with
  | nil state => exact hstate
  | @cons fuel state final z hz hrest ih =>
      exact ih (costBoundState_stepAt G H host part threshold momentExponent
        default hγ hsize
        (next G H host part threshold defaultTarget default state) z hstate)

theorem fullRun_assigned (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    {final : State α β}
    (hrun : AdaptiveProcess.StateRun
      (maskedChoices I G H host part threshold defaultTarget default)
      (step G H host part threshold momentExponent defaultTarget default)
      (Fintype.card α) initialState final) :
    ∀ x, RandomGreedy.assigned final.core x := by
  have hfuel : Fintype.card α ≤
      (initialState : State α β).remaining.card := by simp [initialState]
  have hcard := stateRun_remaining_card G H host part threshold momentExponent
    defaultTarget default
      (maskedChoices I G H host part threshold defaultTarget default) hrun hfuel
  have hempty : final.remaining = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [initialState] using hcard
  have hschedule := stateRun_schedule_final G H host part threshold momentExponent
    defaultTarget default
      (maskedChoices I G H host part threshold defaultTarget default) hrun
      (scheduleState_initial part) hfuel
  intro x
  exact (hschedule.assigned_iff x).2 (by simp [hempty])

theorem final_cost_bounds (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    {γ : ℝ} (hγ : 1 ≤ γ)
    (hsize : ∀ x, ((host (part x)).card : ℝ) ≤ γ * threshold (part x))
    {final : State α β}
    (hrun : AdaptiveProcess.StateRun
      (maskedChoices I G H host part threshold defaultTarget default)
      (step G H host part threshold momentExponent defaultTarget default)
      (Fintype.card α) initialState final) :
    ∀ x, 0 ≤ final.core.costSeen x ∧
      final.core.costSeen x ≤ (2 * γ) * max 1 (final.core.defectSeen x) := by
  have hb := stateRun_costBound_final I G H host part threshold momentExponent
    defaultTarget default hγ hsize hrun (costBoundState_initial (2 * γ))
  have ha := fullRun_assigned I G H host part threshold momentExponent
    defaultTarget default hrun
  intro x
  exact ⟨hb.cost_nonneg x (ha x), hb.cost_le x (ha x)⟩

theorem costProduct_univ_le (I J : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    {γ : ℝ} (hγ : 1 ≤ γ)
    (hsize : ∀ x, ((host (part x)).card : ℝ) ≤ γ * threshold (part x))
    {final : State α β}
    (hrun : AdaptiveProcess.StateRun
      (maskedChoices I G H host part threshold defaultTarget default)
      (step G H host part threshold momentExponent defaultTarget default)
      (Fintype.card α) initialState final) :
    costProduct J Finset.univ final ≤
      (2 * γ) ^ J.card * ∏ x ∈ J, max 1 (final.core.defectSeen x) := by
  have hb := final_cost_bounds I G H host part threshold momentExponent
    defaultTarget default hγ hsize hrun
  have hfilter : J.filter (· ∈ (Finset.univ : Finset α)) = J := by simp
  unfold costProduct
  rw [hfilter]
  calc
    (∏ x ∈ J, final.core.costSeen x) ≤
        ∏ x ∈ J, ((2 * γ) * max 1 (final.core.defectSeen x)) := by
      apply Finset.prod_le_prod
      · intro x hx
        exact (hb x).1
      · intro x hx
        exact (hb x).2
    _ = (2 * γ) ^ J.card *
        ∏ x ∈ J, max 1 (final.core.defectSeen x) := by
      rw [Finset.prod_mul_distrib]
      simp

theorem final_recorded (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    {final : State α β}
    (hrun : AdaptiveProcess.StateRun
      (maskedChoices I G H host part threshold defaultTarget default)
      (step G H host part threshold momentExponent defaultTarget default)
      (Fintype.card α) initialState final) :
    RecordedDefects momentExponent final :=
  stateRun_recordedDefects_final G H host part threshold momentExponent
    defaultTarget default
      (maskedChoices I G H host part threshold defaultTarget default) hrun
      (recordedDefects_initial momentExponent)

theorem final_observed_zero_or_one_le (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    {final : State α β}
    (hrun : AdaptiveProcess.StateRun
      (maskedChoices I G H host part threshold defaultTarget default)
      (step G H host part threshold momentExponent defaultTarget default)
      (Fintype.card α) initialState final) (x : α) :
    final.core.observed x = 0 ∨ 1 ≤ final.core.observed x := by
  have hr := final_recorded I G H host part threshold momentExponent
    defaultTarget default hrun
  have ha := fullRun_assigned I G H host part threshold momentExponent
    defaultTarget default hrun x
  rw [hr.recorded x ha]
  by_cases hz : final.core.defectSeen x = 0
  · simp [hz]
  · rw [if_neg hz]
    right
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
      ((hr.defect_zero_or_one_le x ha).resolve_left hz) momentExponent

theorem final_observed_nonneg_run (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    {final : State α β}
    (hrun : AdaptiveProcess.StateRun
      (maskedChoices I G H host part threshold defaultTarget default)
      (step G H host part threshold momentExponent defaultTarget default)
      (Fintype.card α) initialState final) (x : α) :
    0 ≤ final.core.observed x := by
  exact final_observed_nonneg momentExponent
    (final_recorded I G H host part threshold momentExponent defaultTarget
      default hrun)
    (fullRun_assigned I G H host part threshold momentExponent defaultTarget
      default hrun x)

theorem final_defect_pow_le_observed (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    {final : State α β}
    (hrun : AdaptiveProcess.StateRun
      (maskedChoices I G H host part threshold defaultTarget default)
      (step G H host part threshold momentExponent defaultTarget default)
      (Fintype.card α) initialState final)
    {t : ℕ} (ht : 0 < t) (hts : t ≤ momentExponent) (x : α) :
    final.core.defectSeen x ^ t ≤ final.core.observed x := by
  have hr := final_recorded I G H host part threshold momentExponent
    defaultTarget default hrun
  have ha := fullRun_assigned I G H host part threshold momentExponent
    defaultTarget default hrun x
  rw [hr.recorded x ha]
  by_cases hz : final.core.defectSeen x = 0
  · simp [hz, Nat.ne_of_gt ht]
  · rw [if_neg hz]
    exact pow_le_pow_right₀
      ((hr.defect_zero_or_one_le x ha).resolve_left hz) hts

/-! ## One neutralization branch -/

theorem changeSet_union_forward (I : Finset α)
    (H : SimpleGraph α) [DecidableRel H.Adj] (x : α) :
    changeSet I (I ∪ RandomGreedy.forwardNeighbors H x) =
      RandomGreedy.forwardNeighbors H x \ I := by
  ext y
  simp only [changeSet, Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨hyI | hyF, hyNotI⟩
    · exact (hyNotI hyI).elim
    · exact ⟨hyF, hyNotI⟩
  · rintro ⟨hyF, hyNotI⟩
    exact ⟨Or.inr hyF, hyNotI⟩

theorem neutralAverage_observed_le_branch
    (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (hhost : ∀ i, (host i).Nonempty)
    (part : α → ι) (threshold : ι → ℕ)
    (defaultTarget : α) (default : β) {γ : ℝ} (hγ : 1 ≤ γ)
    (hsize : ∀ x, ((host (part x)).card : ℝ) ≤ γ * threshold (part x))
    (D : ℕ) (hforward : ∀ x, (RandomGreedy.forwardNeighbors H x).card ≤ D)
    (x : α)
    (hJ : (RandomGreedy.forwardNeighbors H x \ I).Nonempty) :
    neutralAverage I G H host part threshold (2 * D) defaultTarget default
        (fun final => final.core.observed x) ≤
      RandomGreedy.branchCoefficient (2 * γ)
          (RandomGreedy.forwardNeighbors H x \ I).card *
        neutralAverage (I ∪ RandomGreedy.forwardNeighbors H x) G H host part
          threshold (2 * D) defaultTarget default
          (fun final => (final.core.observed x) ^ 2) +
        (∑ y ∈ RandomGreedy.forwardNeighbors H x \ I,
          neutralAverage (I ∪ RandomGreedy.forwardNeighbors H x) G H host part
            threshold (2 * D) defaultTarget default
            (fun final => final.core.observed y)) /
          (2 * ((RandomGreedy.forwardNeighbors H x \ I).card : ℝ) ^ 2) := by
  let J := RandomGreedy.forwardNeighbors H x \ I
  let I' := I ∪ RandomGreedy.forwardNeighbors H x
  let C : ℝ := 2 * γ
  let A : ℝ := RandomGreedy.branchCoefficient C J.card
  have hII' : I ⊆ I' := Finset.subset_union_left
  have hchange : changeSet I I' = J := changeSet_union_forward I H x
  have hnonnegI :
      neutralAverage I G H host part threshold (2 * D) defaultTarget default
          (fun final => final.core.observed x) =
        neutralAverage I G H host part threshold (2 * D) defaultTarget default
          (fun final => max 0 (final.core.observed x)) := by
    unfold neutralAverage
    apply AdaptiveProcess.average_congr
    intro final hrun
    have hobs := final_observed_nonneg_run I G H host part threshold (2 * D)
      defaultTarget default hrun x
    exact (max_eq_right hobs).symm
  rw [hnonnegI]
  calc
    neutralAverage I G H host part threshold (2 * D) defaultTarget default
        (fun final => max 0 (final.core.observed x)) ≤
      neutralAverage I' G H host part threshold (2 * D) defaultTarget default
        (fun final => max 0 (final.core.observed x) *
          costProduct J Finset.univ final) := by
      simpa [hchange] using
        neutralAverage_le_costProduct hII' G H host hhost part threshold
          (2 * D) defaultTarget default
          (fun final => max 0 (final.core.observed x))
          (fun final => le_max_left _ _)
    _ ≤ neutralAverage I' G H host part threshold (2 * D) defaultTarget default
        (fun final =>
          A * (final.core.observed x) ^ 2 +
            (∑ y ∈ J, final.core.observed y) / (2 * (J.card : ℝ) ^ 2)) := by
      unfold neutralAverage
      apply AdaptiveProcess.average_mono
      intro final hrun
      have hobs0 := final_observed_nonneg_run I' G H host part threshold (2 * D)
        defaultTarget default hrun x
      have hcost := costProduct_univ_le I' J G H host part threshold (2 * D)
        defaultTarget default hγ hsize hrun
      have hmul :
          max 0 (final.core.observed x) * costProduct J Finset.univ final ≤
            C ^ J.card * final.core.observed x *
              ∏ y ∈ J, max 1 (final.core.defectSeen y) := by
        rw [max_eq_right hobs0]
        calc
          final.core.observed x * costProduct J Finset.univ final ≤
              final.core.observed x *
                ((2 * γ) ^ J.card *
                  ∏ y ∈ J, max 1 (final.core.defectSeen y)) :=
            mul_le_mul_of_nonneg_left hcost hobs0
          _ = C ^ J.card * final.core.observed x *
                ∏ y ∈ J, max 1 (final.core.defectSeen y) := by
            simp only [C]
            ring
      have hJcard : J.card ≤ D :=
        (Finset.card_le_card Finset.sdiff_subset).trans (hforward x)
      have htwoJ : 2 * J.card ≤ 2 * D := Nat.mul_le_mul_left 2 hJcard
      have hJpos : 0 < 2 * J.card := Nat.mul_pos (by norm_num) hJ.card_pos
      have hroot := RandomGreedy.root_mul_product_le_root_sq_add_children hJ
        (fun y => final.core.defectSeen y) (fun y => final.core.observed y) C
        (final.core.observed x)
        (final_observed_zero_or_one_le I' G H host part threshold (2 * D)
          defaultTarget default hrun x)
        (fun y hy => final_observed_nonneg_run I' G H host part threshold (2 * D)
          defaultTarget default hrun y)
        (fun y hy => final_defect_pow_le_observed I' G H host part threshold
          (2 * D) defaultTarget default hrun hJpos htwoJ y)
      exact hmul.trans (by simpa [A, C, RandomGreedy.branchCoefficient] using hroot)
    _ = A * neutralAverage I' G H host part threshold (2 * D) defaultTarget
          default (fun final => (final.core.observed x) ^ 2) +
        (∑ y ∈ J, neutralAverage I' G H host part threshold (2 * D)
          defaultTarget default (fun final => final.core.observed y)) /
          (2 * (J.card : ℝ) ^ 2) := by
      unfold neutralAverage
      rw [AdaptiveProcess.average_add]
      rw [AdaptiveProcess.average_const_mul]
      rw [AdaptiveProcess.average_div]
      rw [AdaptiveProcess.average_sum]
    _ = _ := rfl

/-! ## Propagation on the forward-neighbor DAG -/

theorem neutralAverage_observed_le_of_terminal
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (hhost : ∀ i, (host i).Nonempty)
    (part : α → ι) (threshold : ι → ℕ)
    (defaultTarget : α) (default : β) {γ : ℝ} (hγ : 1 ≤ γ)
    (hsize : ∀ x, ((host (part x)).card : ℝ) ≤ γ * threshold (part x))
    (D : ℕ) (hforward : ∀ x, (RandomGreedy.forwardNeighbors H x).card ≤ D)
    (μ A : ℝ) (hμ : 0 ≤ μ) (hA : 1 / 2 ≤ A)
    (hcoefficient : ∀ q : ℕ, q ≤ D →
      RandomGreedy.branchCoefficient (2 * γ) q ≤ A)
    (hterminal : ∀ (I : Finset α) (x : α),
      RandomGreedy.forwardNeighbors H x ⊆ I →
      neutralAverage I G H host part threshold (2 * D) defaultTarget default
        (fun final => (final.core.observed x) ^ 2) ≤ μ) :
    ∀ (I : Finset α) (x : α),
      neutralAverage I G H host part threshold (2 * D) defaultTarget default
        (fun final => final.core.observed x) ≤ 2 * A * μ := by
  let B : ℝ := 2 * A * μ
  have hA0 : 0 ≤ A := by linarith
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  let P : ℕ → Prop := fun k =>
    ∀ x : α, RandomGreedy.higherCount x = k → ∀ I : Finset α,
      neutralAverage I G H host part threshold (2 * D) defaultTarget default
        (fun final => final.core.observed x) ≤ B
  have hP : ∀ k, P k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro x hxrank I
      let J := RandomGreedy.forwardNeighbors H x \ I
      by_cases hJ : J.Nonempty
      · let I' := I ∪ RandomGreedy.forwardNeighbors H x
        have hstep := neutralAverage_observed_le_branch I G H host hhost part
          threshold defaultTarget default hγ hsize D hforward x hJ
        have hroot : neutralAverage I' G H host part threshold (2 * D)
            defaultTarget default (fun final => (final.core.observed x) ^ 2) ≤ μ := by
          apply hterminal
          exact Finset.subset_union_right
        have hroot0 : 0 ≤ neutralAverage I' G H host part threshold (2 * D)
            defaultTarget default (fun final => (final.core.observed x) ^ 2) := by
          unfold neutralAverage
          apply AdaptiveProcess.average_nonneg
          intro final hrun
          exact sq_nonneg _
        have hJcard : J.card ≤ D :=
          (Finset.card_le_card Finset.sdiff_subset).trans (hforward x)
        have hcoeff := hcoefficient J.card hJcard
        have hcoeff0 : 0 ≤ RandomGreedy.branchCoefficient (2 * γ) J.card := by
          unfold RandomGreedy.branchCoefficient
          positivity
        have hrootTerm :
            RandomGreedy.branchCoefficient (2 * γ) J.card *
                neutralAverage I' G H host part threshold (2 * D) defaultTarget
                  default (fun final => (final.core.observed x) ^ 2) ≤ A * μ :=
          mul_le_mul hcoeff hroot hroot0 hA0
        have hchildren :
            ∑ y ∈ J, neutralAverage I' G H host part threshold (2 * D)
                defaultTarget default (fun final => final.core.observed y) ≤
              (J.card : ℝ) * B := by
          calc
            _ ≤ ∑ _y ∈ J, B := by
              apply Finset.sum_le_sum
              intro y hy
              have hyForward : y ∈ RandomGreedy.forwardNeighbors H x :=
                (Finset.mem_sdiff.mp hy).1
              have hxy : x < y := (Finset.mem_filter.mp hyForward).2.2
              have hyrank : RandomGreedy.higherCount y < k := by
                rw [← hxrank]
                exact RandomGreedy.higherCount_lt_of_lt hxy
              exact ih (RandomGreedy.higherCount y) hyrank y rfl I'
            _ = (J.card : ℝ) * B := by simp
        have hdenom : 0 < (2 * (J.card : ℝ) ^ 2) := by
          have : (0 : ℝ) < J.card := by exact_mod_cast hJ.card_pos
          positivity
        have hquotient :
            (∑ y ∈ J, neutralAverage I' G H host part threshold (2 * D)
              defaultTarget default (fun final => final.core.observed y)) /
                (2 * (J.card : ℝ) ^ 2) ≤ B / 2 := by
          calc
            _ ≤ ((J.card : ℝ) * B) / (2 * (J.card : ℝ) ^ 2) :=
              div_le_div_of_nonneg_right hchildren hdenom.le
            _ = B / (2 * (J.card : ℝ)) := by
              have hcardne : (J.card : ℝ) ≠ 0 := by
                exact_mod_cast hJ.card_ne_zero
              field_simp
            _ ≤ B / 2 := by
              apply div_le_div_of_nonneg_left hB0 (by norm_num)
              have hqone : (1 : ℝ) ≤ J.card := by exact_mod_cast hJ.card_pos
              nlinarith
        calc
          neutralAverage I G H host part threshold (2 * D) defaultTarget default
              (fun final => final.core.observed x) ≤
              RandomGreedy.branchCoefficient (2 * γ) J.card *
                neutralAverage I' G H host part threshold (2 * D) defaultTarget
                  default (fun final => (final.core.observed x) ^ 2) +
                (∑ y ∈ J, neutralAverage I' G H host part threshold (2 * D)
                  defaultTarget default (fun final => final.core.observed y)) /
                    (2 * (J.card : ℝ) ^ 2) := by simpa [J, I'] using hstep
          _ ≤ A * μ + B / 2 := add_le_add hrootTerm hquotient
          _ = B := by simp [B]; ring
      · have hsubset : RandomGreedy.forwardNeighbors H x ⊆ I :=
          Finset.sdiff_eq_empty_iff_subset.mp
            (Finset.not_nonempty_iff_eq_empty.mp hJ)
        have hlinear : neutralAverage I G H host part threshold (2 * D)
            defaultTarget default (fun final => final.core.observed x) ≤
          neutralAverage I G H host part threshold (2 * D) defaultTarget default
            (fun final => (final.core.observed x) ^ 2) := by
          unfold neutralAverage
          apply AdaptiveProcess.average_mono
          intro final hrun
          rcases final_observed_zero_or_one_le I G H host part threshold (2 * D)
            defaultTarget default hrun x with hzero | hone
          · simp [hzero]
          · nlinarith [sq_nonneg (final.core.observed x)]
        calc
          neutralAverage I G H host part threshold (2 * D) defaultTarget default
              (fun final => final.core.observed x) ≤
            neutralAverage I G H host part threshold (2 * D) defaultTarget default
              (fun final => (final.core.observed x) ^ 2) := hlinear
          _ ≤ μ := hterminal I x hsubset
          _ ≤ B := by dsimp [B]; nlinarith
  intro I x
  exact hP (RandomGreedy.higherCount x) x rfl I

theorem average_observed_le_of_terminal
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (hhost : ∀ i, (host i).Nonempty)
    (part : α → ι) (threshold : ι → ℕ)
    (defaultTarget : α) (default : β) {γ : ℝ} (hγ : 1 ≤ γ)
    (hsize : ∀ x, ((host (part x)).card : ℝ) ≤ γ * threshold (part x))
    (D : ℕ) (hforward : ∀ x, (RandomGreedy.forwardNeighbors H x).card ≤ D)
    (μ A : ℝ) (hμ : 0 ≤ μ) (hA : 1 / 2 ≤ A)
    (hcoefficient : ∀ q : ℕ, q ≤ D →
      RandomGreedy.branchCoefficient (2 * γ) q ≤ A)
    (hterminal : ∀ (I : Finset α) (x : α),
      RandomGreedy.forwardNeighbors H x ⊆ I →
      neutralAverage I G H host part threshold (2 * D) defaultTarget default
        (fun final => (final.core.observed x) ^ 2) ≤ μ) (x : α) :
    average G H host part threshold (2 * D) defaultTarget default
        (fun final => final.core.observed x) ≤ 2 * A * μ := by
  have h := neutralAverage_observed_le_of_terminal G H host hhost part threshold
    defaultTarget default hγ hsize D hforward μ A hμ hA hcoefficient hterminal
      (∅ : Finset α) x
  have hempty : maskedChoices (∅ : Finset α) G H host part threshold
      defaultTarget default = choices G H host part threshold defaultTarget default := by
    funext state
    simp [maskedChoices]
  unfold neutralAverage at h
  unfold average
  rw [hempty] at h
  exact h

/-- Adaptive random-greedy theorem with the terminal square moments left as
the host-side input. -/
theorem hasCopy_of_terminal_moments
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
    (hterminal : ∀ (I : Finset α) (x : α),
      RandomGreedy.forwardNeighbors H x ⊆ I →
      neutralAverage I G H host part threshold (2 * D) defaultTarget default
        (fun final => (final.core.observed x) ^ 2) ≤ μ)
    (htotal :
      ∑ x : α, (2 / (threshold (part x) : ℝ)) *
        (2 * RandomGreedy.branchCoefficient (2 * γ) D * μ) < 1) :
    HasCopy H G := by
  let A := RandomGreedy.branchCoefficient (2 * γ) D
  have hC : (1 : ℝ) ≤ 2 * γ := by linarith
  have hA : (1 / 2 : ℝ) ≤ A := by
    dsimp [A, RandomGreedy.branchCoefficient]
    nlinarith [sq_nonneg ((D : ℝ) * (2 * γ) ^ D)]
  have hcoeff : ∀ q : ℕ, q ≤ D →
      RandomGreedy.branchCoefficient (2 * γ) q ≤ A := by
    intro q hq
    exact RandomGreedy.branchCoefficient_mono hC hq
  apply hasCopy_of_weighted_average_observed_lt_one G H host part threshold
    (2 * D) defaultTarget default hhostNonempty hhostDisjoint hpart horder
    hthreshold hpartSize (Nat.mul_pos (by norm_num) hD)
  calc
    ∑ x : α, (2 / (threshold (part x) : ℝ)) *
        average G H host part threshold (2 * D) defaultTarget default
          (fun final => final.core.observed x) ≤
      ∑ x : α, (2 / (threshold (part x) : ℝ)) * (2 * A * μ) := by
        apply Finset.sum_le_sum
        intro x hx
        apply mul_le_mul_of_nonneg_left
        · exact average_observed_le_of_terminal G H host hhostNonempty part
            threshold defaultTarget default hγ hsize D hforward μ A hμ hA hcoeff
              hterminal x
        · exact div_nonneg (by norm_num) (by positivity)
    _ < 1 := by simpa [A] using htotal

end AdaptiveGreedy
end Erdos163
