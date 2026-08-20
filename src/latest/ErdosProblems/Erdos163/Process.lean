/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.FiniteDefect

/-!
# Finite sequential averaging

The random-greedy argument is kept entirely finite.  `average` is the
expectation obtained by successively choosing a uniform element of a
nonempty, history-dependent finset.  The accompanying `Run` relation records
the deterministic executions represented by that average.
-/

open scoped BigOperators
open Finset

namespace Erdos163
namespace Process

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

/-! ## General state process -/

universe w

inductive StateRun {σ : Type w} (choices : α → σ → Finset β)
    (step : α → σ → β → σ) : List α → σ → σ → Prop
  | nil (state) : StateRun choices step [] state state
  | cons {x : α} {xs : List α} {state final : σ} {y : β}
      (hy : y ∈ choices x state)
      (hrest : StateRun choices step xs (step x state y) final) :
      StateRun choices step (x :: xs) state final

noncomputable def stateAverage {σ : Type w} (choices : α → σ → Finset β)
    (step : α → σ → β → σ) : List α → σ → (σ → ℝ) → ℝ
  | [], state, payoff => payoff state
  | x :: xs, state, payoff =>
      𝔼 y ∈ choices x state,
        stateAverage choices step xs (step x state y) payoff

@[simp] theorem stateAverage_nil {σ : Type w} (choices : α → σ → Finset β)
    (step : α → σ → β → σ) (state : σ) (payoff : σ → ℝ) :
    stateAverage choices step [] state payoff = payoff state := rfl

@[simp] theorem stateAverage_cons {σ : Type w} (choices : α → σ → Finset β)
    (step : α → σ → β → σ) (x : α) (xs : List α) (state : σ)
    (payoff : σ → ℝ) :
    stateAverage choices step (x :: xs) state payoff =
      𝔼 y ∈ choices x state,
        stateAverage choices step xs (step x state y) payoff := rfl

theorem exists_stateRun_le_average {σ : Type w} (choices : α → σ → Finset β)
    (step : α → σ → β → σ) (hne : ∀ x state, (choices x state).Nonempty)
    (order : List α) (state : σ) (payoff : σ → ℝ) :
    ∃ final, StateRun choices step order state final ∧
      payoff final ≤ stateAverage choices step order state payoff := by
  induction order generalizing state with
  | nil => exact ⟨state, .nil state, le_rfl⟩
  | cons x xs ih =>
      obtain ⟨y, hy, hyavg⟩ := Finset.exists_le_of_expect_le (hne x state)
        (le_rfl : (𝔼 y ∈ choices x state,
          stateAverage choices step xs (step x state y) payoff) ≤ _)
      obtain ⟨final, hrun, hfinal⟩ := ih (step x state y)
      exact ⟨final, .cons hy hrun, hfinal.trans hyavg⟩

theorem stateAverage_nonneg {σ : Type w} (choices : α → σ → Finset β)
    (step : α → σ → β → σ) (order : List α) (state : σ)
    {payoff : σ → ℝ}
    (h : ∀ final, StateRun choices step order state final → 0 ≤ payoff final) :
    0 ≤ stateAverage choices step order state payoff := by
  induction order generalizing state with
  | nil => exact h state (.nil state)
  | cons x xs ih =>
      unfold stateAverage Finset.expect
      apply mul_nonneg
      · positivity
      · exact Finset.sum_nonneg fun y hy => ih (step x state y)
          (fun final hrun => h final (.cons hy hrun))

theorem stateAverage_mono {σ : Type w} (choices : α → σ → Finset β)
    (step : α → σ → β → σ) (order : List α) (state : σ)
    {payoff payoff' : σ → ℝ}
    (h : ∀ final, StateRun choices step order state final →
      payoff final ≤ payoff' final) :
    stateAverage choices step order state payoff ≤
      stateAverage choices step order state payoff' := by
  induction order generalizing state with
  | nil => exact h state (.nil state)
  | cons x xs ih =>
      apply Finset.expect_le_expect
      intro y hy
      exact ih (step x state y) fun final hrun => h final (.cons hy hrun)

theorem stateAverage_congr {σ : Type w} (choices : α → σ → Finset β)
    (step : α → σ → β → σ) (order : List α) (state : σ)
    {payoff payoff' : σ → ℝ}
    (h : ∀ final, StateRun choices step order state final →
      payoff final = payoff' final) :
    stateAverage choices step order state payoff =
      stateAverage choices step order state payoff' := by
  apply le_antisymm
  · exact stateAverage_mono choices step order state fun final hrun =>
      (h final hrun).le
  · exact stateAverage_mono choices step order state fun final hrun =>
      (h final hrun).ge

theorem stateAverage_sum {σ : Type w} {κ : Type*} [DecidableEq κ]
    (choices : α → σ → Finset β) (step : α → σ → β → σ)
    (order : List α) (state : σ) (S : Finset κ) (payoff : κ → σ → ℝ) :
    stateAverage choices step order state (fun final => ∑ i ∈ S, payoff i final) =
      ∑ i ∈ S, stateAverage choices step order state (payoff i) := by
  induction order generalizing state with
  | nil => rfl
  | cons x xs ih =>
      simp only [stateAverage_cons]
      simp_rw [ih]
      rw [Finset.expect_sum_comm]

theorem stateAverage_const_mul {σ : Type w}
    (choices : α → σ → Finset β) (step : α → σ → β → σ)
    (order : List α) (state : σ) (c : ℝ) (payoff : σ → ℝ) :
    stateAverage choices step order state (fun final => c * payoff final) =
      c * stateAverage choices step order state payoff := by
  induction order generalizing state with
  | nil => rfl
  | cons x xs ih =>
      simp only [stateAverage_cons]
      simp_rw [ih]
      simp only [Finset.expect_eq_sum_div_card, ← Finset.mul_sum]
      ring

/-- A sequential average with a nonnegative history-dependent factor inserted
at every transition.  This is the finite Radon--Nikodym expression used in
the neutralization argument. -/
noncomputable def weightedStateAverage {σ : Type w}
    (choices : α → σ → Finset β) (step : α → σ → β → σ)
    (weight : α → σ → ℝ) : List α → σ → (σ → ℝ) → ℝ
  | [], state, payoff => payoff state
  | x :: xs, state, payoff =>
      𝔼 y ∈ choices x state,
        weight x state *
          weightedStateAverage choices step weight xs (step x state y) payoff

@[simp] theorem weightedStateAverage_nil {σ : Type w}
    (choices : α → σ → Finset β) (step : α → σ → β → σ)
    (weight : α → σ → ℝ) (state : σ) (payoff : σ → ℝ) :
    weightedStateAverage choices step weight [] state payoff = payoff state := rfl

@[simp] theorem weightedStateAverage_cons {σ : Type w}
    (choices : α → σ → Finset β) (step : α → σ → β → σ)
    (weight : α → σ → ℝ) (x : α) (xs : List α) (state : σ)
    (payoff : σ → ℝ) :
    weightedStateAverage choices step weight (x :: xs) state payoff =
      𝔼 y ∈ choices x state,
        weight x state *
          weightedStateAverage choices step weight xs (step x state y) payoff := rfl

theorem weightedStateAverage_nonneg {σ : Type w}
    (choices : α → σ → Finset β) (step : α → σ → β → σ)
    (weight : α → σ → ℝ) (hweight : ∀ x state, 0 ≤ weight x state)
    (order : List α) (state : σ) {payoff : σ → ℝ}
    (hpayoff : ∀ final, 0 ≤ payoff final) :
    0 ≤ weightedStateAverage choices step weight order state payoff := by
  induction order generalizing state with
  | nil => exact hpayoff state
  | cons x xs ih =>
      unfold weightedStateAverage Finset.expect
      apply mul_nonneg
      · positivity
      · exact Finset.sum_nonneg fun y _ =>
          mul_nonneg (hweight x state) (ih (step x state y))

/-- Change of measure from a uniform nonempty subset to a larger uniform
finset. -/
theorem expect_subset_le_card_ratio {γ : Type*} [DecidableEq γ]
    {S T : Finset γ} (hS : S.Nonempty) (hsub : S ⊆ T)
    (f : γ → ℝ) (hf : ∀ x ∈ T, 0 ≤ f x) :
    (𝔼 x ∈ S, f x) ≤
      ((T.card : ℝ) / S.card) * (𝔼 x ∈ T, f x) := by
  rw [Finset.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card]
  have hsum : ∑ x ∈ S, f x ≤ ∑ x ∈ T, f x :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x hxT hxS => hf x hxT)
  have hScard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hTcard : (0 : ℝ) < T.card := by
    exact_mod_cast (hS.card_pos.trans_le (Finset.card_le_card hsub))
  calc
    (∑ x ∈ S, f x) / (S.card : ℝ) ≤
        (∑ x ∈ T, f x) / (S.card : ℝ) :=
      div_le_div_of_nonneg_right hsum hScard.le
    _ = ((T.card : ℝ) / S.card) *
        ((∑ x ∈ T, f x) / (T.card : ℝ)) := by
      field_simp

/-- Finite change of measure for a sequential process.  At every history the
old choice set is contained in the new one, and `weight` bounds the ratio of
their cardinalities. -/
theorem stateAverage_le_weightedStateAverage {σ : Type w}
    (oldChoices newChoices : α → σ → Finset β)
    (step : α → σ → β → σ) (weight : α → σ → ℝ)
    (hold : ∀ x state, (oldChoices x state).Nonempty)
    (hnew : ∀ x state, (newChoices x state).Nonempty)
    (hsub : ∀ x state, oldChoices x state ⊆ newChoices x state)
    (hratio : ∀ x state,
      ((newChoices x state).card : ℝ) / (oldChoices x state).card ≤ weight x state)
    (hweight : ∀ x state, 0 ≤ weight x state)
    (order : List α) (state : σ) (payoff : σ → ℝ)
    (hpayoff : ∀ final, 0 ≤ payoff final) :
    stateAverage oldChoices step order state payoff ≤
      weightedStateAverage newChoices step weight order state payoff := by
  induction order generalizing state with
  | nil => exact le_rfl
  | cons x xs ih =>
      rw [stateAverage_cons, weightedStateAverage_cons]
      let tail : β → ℝ := fun y =>
        weightedStateAverage newChoices step weight xs (step x state y) payoff
      calc
        (𝔼 y ∈ oldChoices x state,
            stateAverage oldChoices step xs (step x state y) payoff) ≤
            𝔼 y ∈ oldChoices x state, tail y := by
              apply Finset.expect_le_expect
              intro y _
              exact ih (step x state y)
        _ ≤ (((newChoices x state).card : ℝ) /
              (oldChoices x state).card) *
              (𝔼 y ∈ newChoices x state, tail y) :=
          expect_subset_le_card_ratio (hold x state) (hsub x state) tail
            (fun y _ => weightedStateAverage_nonneg newChoices step weight
              hweight xs (step x state y) hpayoff)
        _ ≤ weight x state * (𝔼 y ∈ newChoices x state, tail y) := by
          exact mul_le_mul_of_nonneg_right (hratio x state)
            (Finset.expect_nonneg fun y _ =>
              weightedStateAverage_nonneg newChoices step weight hweight xs
                (step x state y) hpayoff)
        _ = 𝔼 y ∈ newChoices x state, weight x state * tail y := by
          simp only [Finset.expect_eq_sum_div_card]
          rw [← Finset.mul_sum]
          ring

theorem stateAverage_add {σ : Type w}
    (choices : α → σ → Finset β) (step : α → σ → β → σ)
    (order : List α) (state : σ) (payoff payoff' : σ → ℝ) :
    stateAverage choices step order state (fun final => payoff final + payoff' final) =
      stateAverage choices step order state payoff +
        stateAverage choices step order state payoff' := by
  induction order generalizing state with
  | nil => rfl
  | cons x xs ih =>
      simp only [stateAverage_cons]
      simp_rw [ih]
      rw [Finset.expect_add_distrib]

theorem stateAverage_div {σ : Type w}
    (choices : α → σ → Finset β) (step : α → σ → β → σ)
    (order : List α) (state : σ) (payoff : σ → ℝ) (c : ℝ) :
    stateAverage choices step order state (fun final => payoff final / c) =
      stateAverage choices step order state payoff / c := by
  simpa [div_eq_inv_mul] using
    stateAverage_const_mul choices step order state c⁻¹ payoff

/-! ## Projection to independent coordinates -/

noncomputable def coordinateAverage (A : α → Finset β) :
    List α → (α → β) → ((α → β) → ℝ) → ℝ :=
  stateAverage (fun x _ => A x) (fun x f z => Function.update f x z)

@[simp] theorem coordinateAverage_nil (A : α → Finset β)
    (f : α → β) (payoff : (α → β) → ℝ) :
    coordinateAverage A [] f payoff = payoff f := rfl

@[simp] theorem coordinateAverage_cons (A : α → Finset β)
    (x : α) (xs : List α) (f : α → β) (payoff : (α → β) → ℝ) :
    coordinateAverage A (x :: xs) f payoff =
      𝔼 z ∈ A x, coordinateAverage A xs (Function.update f x z) payoff := rfl

theorem fixedAverage_congr_on (A : α → Finset β) (S : Finset α)
    (order : List α) (f g : α → β) (payoff : (α → β) → ℝ)
    (hfg : ∀ y ∈ S, y ∉ order → f y = g y)
    (hpayoff : ∀ f g, (∀ y ∈ S, f y = g y) → payoff f = payoff g) :
    coordinateAverage A order f payoff =
      coordinateAverage A order g payoff := by
  induction order generalizing f g with
  | nil =>
      apply hpayoff
      intro y hy
      exact hfg y hy (by simp)
  | cons x xs ih =>
      rw [coordinateAverage_cons, coordinateAverage_cons]
      apply Finset.expect_congr rfl
      intro z hz
      apply ih
      · intro y hy hyxs
        by_cases hyx : y = x
        · subst y
          simp
        · simpa [Function.update, hyx] using
            hfg y hy (by simp [hyx, hyxs])

theorem stateAverage_eq_fixedAverage {σ : Type w}
    (choices : α → σ → Finset β) (step : α → σ → β → σ)
    (get : σ → α → β) (A : α → Finset β) (S : Finset α)
    (hne : ∀ x state, (choices x state).Nonempty)
    (hA : ∀ x, (A x).Nonempty)
    (hchoices : ∀ x state, x ∈ S → choices x state = A x)
    (hself : ∀ x state z, get (step x state z) x = z)
    (hother : ∀ x state z y, y ≠ x → get (step x state z) y = get state y)
    (payoff : (α → β) → ℝ)
    (hpayoff : ∀ f g, (∀ y ∈ S, f y = g y) → payoff f = payoff g)
    (order : List α) (state : σ) :
    stateAverage choices step order state (fun final => payoff (get final)) =
      coordinateAverage A order (get state) payoff := by
  induction order generalizing state with
  | nil => rfl
  | cons x xs ih =>
      rw [stateAverage_cons, coordinateAverage_cons]
      by_cases hxS : x ∈ S
      · rw [hchoices x state hxS]
        apply Finset.expect_congr rfl
        intro z hz
        rw [ih]
        apply fixedAverage_congr_on A S xs
          (get (step x state z)) (Function.update (get state) x z) payoff
        · intro y hy hyxs
          by_cases hyx : y = x
          · subst y
            simp [hself]
          · simp [hother _ _ _ _ hyx, Function.update, hyx]
        · exact hpayoff
      · let K := coordinateAverage A xs (get state) payoff
        calc
          (𝔼 z ∈ choices x state,
              stateAverage choices step xs (step x state z)
                (fun final => payoff (get final))) =
              𝔼 _z ∈ choices x state, K := by
                apply Finset.expect_congr rfl
                intro z hz
                rw [ih]
                apply fixedAverage_congr_on A S xs
                  (get (step x state z)) (get state) payoff
                · intro y hy hyxs
                  have hyx : y ≠ x := by
                    intro hyx
                    subst y
                    exact hxS hy
                  exact hother x state z y hyx
                · exact hpayoff
          _ = K := Finset.expect_const (hne x state) K
          _ = 𝔼 _z ∈ A x, K := (Finset.expect_const (hA x) K).symm
          _ = 𝔼 z ∈ A x,
              coordinateAverage A xs (Function.update (get state) x z) payoff := by
                apply Finset.expect_congr rfl
                intro z hz
                symm
                apply fixedAverage_congr_on A S xs
                  (Function.update (get state) x z) (get state) payoff
                · intro y hy hyxs
                  have hyx : y ≠ x := by
                    intro hyx
                    subst y
                    exact hxS hy
                  simp [Function.update, hyx]
                · exact hpayoff

/-- A completed execution of a list of history-dependent choices. -/
inductive Run (choices : α → (α → β) → Finset β) :
    List α → (α → β) → (α → β) → Prop
  | nil (f) : Run choices [] f f
  | cons {x : α} {xs : List α} {f g : α → β} {y : β}
      (hy : y ∈ choices x f)
      (hrest : Run choices xs (Function.update f x y) g) :
      Run choices (x :: xs) f g

/-- Nested uniform average of a payoff over a finite sequential process. -/
noncomputable def average (choices : α → (α → β) → Finset β) :
    List α → (α → β) → ((α → β) → ℝ) → ℝ
  | [], f, payoff => payoff f
  | x :: xs, f, payoff =>
      𝔼 y ∈ choices x f,
        average choices xs (Function.update f x y) payoff

@[simp] theorem average_nil (choices : α → (α → β) → Finset β)
    (f : α → β) (payoff : (α → β) → ℝ) :
    average choices [] f payoff = payoff f := rfl

@[simp] theorem average_cons (choices : α → (α → β) → Finset β)
    (x : α) (xs : List α) (f : α → β) (payoff : (α → β) → ℝ) :
    average choices (x :: xs) f payoff =
      𝔼 y ∈ choices x f,
        average choices xs (Function.update f x y) payoff := rfl

theorem average_congr (choices : α → (α → β) → Finset β)
    (order : List α) (f : α → β) {payoff payoff' : (α → β) → ℝ}
    (h : ∀ g, Run choices order f g → payoff g = payoff' g) :
    average choices order f payoff = average choices order f payoff' := by
  induction order generalizing f with
  | nil => exact h f (.nil f)
  | cons x xs ih =>
      apply Finset.expect_congr rfl
      intro y hy
      apply ih
      intro g hg
      exact h g (.cons hy hg)

theorem average_mono (choices : α → (α → β) → Finset β)
    (order : List α) (f : α → β) {payoff payoff' : (α → β) → ℝ}
    (h : ∀ g, Run choices order f g → payoff g ≤ payoff' g) :
    average choices order f payoff ≤ average choices order f payoff' := by
  induction order generalizing f with
  | nil => exact h f (.nil f)
  | cons x xs ih =>
      apply Finset.expect_le_expect
      intro y hy
      apply ih
      intro g hg
      exact h g (.cons hy hg)

theorem average_nonneg (choices : α → (α → β) → Finset β)
    (order : List α) (f : α → β) {payoff : (α → β) → ℝ}
    (h : ∀ g, Run choices order f g → 0 ≤ payoff g) :
    0 ≤ average choices order f payoff := by
  induction order generalizing f with
  | nil => exact h f (.nil f)
  | cons x xs ih =>
      unfold average Finset.expect
      apply mul_nonneg
      · positivity
      · exact Finset.sum_nonneg fun y hy => ih (Function.update f x y)
          (fun g hg => h g (.cons hy hg))

theorem average_const (choices : α → (α → β) → Finset β)
    (hne : ∀ x f, (choices x f).Nonempty)
    (order : List α) (f : α → β) (c : ℝ) :
    average choices order f (fun _ => c) = c := by
  induction order generalizing f with
  | nil => rfl
  | cons x xs ih =>
      simp only [average_cons]
      have hpoint : ∀ y ∈ choices x f,
          average choices xs (Function.update f x y) (fun _ => c) = c :=
        fun y hy => ih (Function.update f x y)
      rw [Finset.expect_congr rfl hpoint]
      exact Finset.expect_const (hne x f) c

/-- Some deterministic execution has payoff no larger than the sequential
average. -/
theorem exists_run_le_average (choices : α → (α → β) → Finset β)
    (hne : ∀ x f, (choices x f).Nonempty)
    (order : List α) (f : α → β) (payoff : (α → β) → ℝ) :
    ∃ g, Run choices order f g ∧
      payoff g ≤ average choices order f payoff := by
  induction order generalizing f with
  | nil => exact ⟨f, .nil f, le_rfl⟩
  | cons x xs ih =>
      obtain ⟨y, hy, hyavg⟩ := Finset.exists_le_of_expect_le (hne x f)
        (le_rfl : (𝔼 y ∈ choices x f,
          average choices xs (Function.update f x y) payoff) ≤ _)
      obtain ⟨g, hrun, hg⟩ := ih (Function.update f x y)
      exact ⟨g, .cons hy hrun, hg.trans hyavg⟩

/-- Some deterministic execution has payoff no smaller than the sequential
average. -/
theorem exists_average_le_run (choices : α → (α → β) → Finset β)
    (hne : ∀ x f, (choices x f).Nonempty)
    (order : List α) (f : α → β) (payoff : (α → β) → ℝ) :
    ∃ g, Run choices order f g ∧
      average choices order f payoff ≤ payoff g := by
  induction order generalizing f with
  | nil => exact ⟨f, .nil f, le_rfl⟩
  | cons x xs ih =>
      obtain ⟨y, hy, hyavg⟩ := Finset.exists_le_of_le_expect (hne x f)
        (le_rfl : _ ≤ 𝔼 y ∈ choices x f,
          average choices xs (Function.update f x y) payoff)
      obtain ⟨g, hrun, hg⟩ := ih (Function.update f x y)
      exact ⟨g, .cons hy hrun, hyavg.trans hg⟩

end Process
end Erdos163
