/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteProbability

/-!
# Joint finite laws from a Markov kernel

`FiniteLaw.bind` forgets the input state.  Master-iteration updates need the
joint pair consisting of the old state and a conditionally sampled cover.
This file supplies that elementary construction and its probability
calculus.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

namespace FiniteLaw

variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

/-- Sample `ω` from `L`, then sample `ξ` from `K ω`, retaining both. -/
def jointBind [DecidableEq Ω] [DecidableEq Ξ]
    (L : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ) : FiniteLaw (Ω × Ξ) :=
  L.bind fun ω ↦ (K ω).map fun ξ ↦ (ω, ξ)

/-- The mass of a pair in a joint bind is the product of the old-state mass
and the corresponding conditional mass. -/
@[simp]
theorem jointBind_mass [DecidableEq Ω] [DecidableEq Ξ]
    (L : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ) (ω : Ω) (ξ : Ξ) :
    (L.jointBind K).mass (ω, ξ) = L.mass ω * (K ω).mass ξ := by
  classical
  unfold jointBind FiniteLaw.bind FiniteLaw.map
  change (∑ x : Ω, L.mass x *
      ∑ y : Ξ, if (x, y) = (ω, ξ) then (K x).mass y else 0) = _
  rw [Finset.sum_eq_single ω]
  · simp
  · intro x _ hx
    simp [hx]
  · simp

/-- A joint outcome has positive mass exactly when both the sampled old state
and the conditional outcome have positive mass. -/
theorem jointBind_mass_pos_iff [DecidableEq Ω] [DecidableEq Ξ]
    (L : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ) (ω : Ω) (ξ : Ξ) :
    0 < (L.jointBind K).mass (ω, ξ) ↔
      0 < L.mass ω ∧ 0 < (K ω).mass ξ := by
  rw [jointBind_mass]
  constructor
  · intro h
    rcases mul_pos_iff.mp h with hpos | hneg
    · exact hpos
    · exact ((not_lt_of_ge (zero_le : 0 ≤ L.mass ω)) hneg.1).elim
  · rintro ⟨hL, hK⟩
    exact mul_pos hL hK

/-- Law of total probability for a joint bind. -/
theorem probability_jointBind [DecidableEq Ω] [DecidableEq Ξ]
    (L : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ) (P : Ω × Ξ → Prop) :
    (L.jointBind K).probability P =
      ∑ ω, L.mass ω * (K ω).probability (fun ξ ↦ P (ω, ξ)) := by
  rw [jointBind, probability_bind]
  apply sum_congr rfl
  intro ω _hω
  rw [probability_map]

/-- The first marginal of a joint bind is the original law. -/
theorem probability_jointBind_fst [DecidableEq Ω] [DecidableEq Ξ]
    (L : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ) (P : Ω → Prop) :
    (L.jointBind K).probability (fun z ↦ P z.1) = L.probability P := by
  classical
  rw [probability_jointBind]
  unfold probability
  apply sum_congr rfl
  intro ω _hω
  by_cases hP : P ω
  · simp [hP, (K ω).sum_mass]
  · simp [hP]

/-- Adjoining a further conditional sample does not change an event that
depends only on the first conditional sample.  A uniform bound needed only
on positive-mass outer states therefore passes through both joint binds. -/
theorem jointBind_jointBind_probability_snd_fst_le_on_support
    {Z : Type*} [Fintype Z] [DecidableEq Z]
    [DecidableEq Ω] [DecidableEq Ξ]
    (L : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ)
    (H : Ω → Ξ → FiniteLaw Z) (P : Ω → Ξ → Prop)
    (b : ℝ≥0)
    (hP : ∀ ω, 0 < L.mass ω → (K ω).probability (P ω) ≤ b) :
    (L.jointBind (fun ω ↦ (K ω).jointBind (H ω))).probability
        (fun z ↦ P z.1 z.2.1) ≤ b := by
  classical
  rw [probability_jointBind]
  calc
    ∑ ω, L.mass ω *
          ((K ω).jointBind (H ω)).probability
            (fun z ↦ P ω z.1) ≤
        ∑ ω, L.mass ω * b := by
      apply sum_le_sum
      intro ω _hω
      by_cases hmass : 0 < L.mass ω
      · gcongr
        rw [probability_jointBind_fst]
        exact hP ω hmass
      · have hzero : L.mass ω = 0 :=
          le_antisymm (not_lt.mp hmass) zero_le
        simp [hzero]
    _ = b := by
      rw [← Finset.sum_mul, L.sum_mass, one_mul]

/-- Support of the old law and support of every conditional kernel combine
to support the corresponding predicate on pairs. -/
theorem SupportedOn.jointBind [DecidableEq Ω] [DecidableEq Ξ]
    {L : FiniteLaw Ω} {K : Ω → FiniteLaw Ξ}
    {P : Ω → Prop} {Q : Ω → Ξ → Prop}
    (hL : L.SupportedOn P)
    (hK : ∀ ω, P ω → (K ω).SupportedOn (Q ω)) :
    (L.jointBind K).SupportedOn (fun z ↦ P z.1 ∧ Q z.1 z.2) := by
  change (L.bind (fun ω ↦ (K ω).map fun ξ ↦ (ω, ξ))).SupportedOn
    (fun z ↦ P z.1 ∧ Q z.1 z.2)
  apply FiniteLaw.SupportedOn.bind (P := P)
    (Q := fun z : Ω × Ξ ↦ P z.1 ∧ Q z.1 z.2) hL
    (fun ω ↦ (K ω).map fun ξ ↦ (ω, ξ))
  intro ω hP
  apply FiniteLaw.SupportedOn.map
    (Q := fun z : Ω × Ξ ↦ P z.1 ∧ Q z.1 z.2)
    (hK ω hP) (fun ξ ↦ (ω, ξ))
  intro ξ hQ
  exact ⟨hP, hQ⟩

/-- A uniform conditional event bound multiplies the probability of an old
state event. -/
theorem jointBind_probability_and_le [DecidableEq Ω] [DecidableEq Ξ]
    (L : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ)
    (P : Ω → Prop) (Q : Ω → Ξ → Prop) (b : ℝ≥0)
    (hQ : ∀ ω, P ω → (K ω).probability (Q ω) ≤ b) :
    (L.jointBind K).probability (fun z ↦ P z.1 ∧ Q z.1 z.2) ≤
      b * L.probability P := by
  classical
  rw [probability_jointBind]
  calc
    ∑ ω, L.mass ω * (K ω).probability
        (fun ξ ↦ P ω ∧ Q ω ξ) ≤
        ∑ ω, L.mass ω * (if P ω then b else 0) := by
      apply sum_le_sum
      intro ω _hω
      by_cases hPω : P ω
      · simp only [hPω, true_and, if_true]
        gcongr
        exact hQ ω hPω
      · have hfalse : (fun ξ ↦ P ω ∧ Q ω ξ) =
            (fun _ : Ξ ↦ False) := by
          funext ξ
          simp [hPω]
        rw [hfalse, probability_false]
        simp [hPω]
    _ = b * L.probability P := by
      unfold probability
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro ω _hω
      by_cases hPω : P ω <;> simp [hPω, mul_comm]

/-- Variant where the conditional bound may depend on the old state but is
pointwise dominated on the event of interest. -/
theorem jointBind_probability_and_le_of_pointwise
    [DecidableEq Ω] [DecidableEq Ξ]
    (L : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ)
    (P : Ω → Prop) (Q : Ω → Ξ → Prop) (b : Ω → ℝ≥0) (B : ℝ≥0)
    (hQ : ∀ ω, P ω → (K ω).probability (Q ω) ≤ b ω)
    (hb : ∀ ω, P ω → b ω ≤ B) :
    (L.jointBind K).probability (fun z ↦ P z.1 ∧ Q z.1 z.2) ≤
      B * L.probability P := by
  apply L.jointBind_probability_and_le K P Q B
  intro ω hP
  exact (hQ ω hP).trans (hb ω hP)

/-- Support-sensitive form of `jointBind_probability_and_le`.  Conditional
bounds are needed only at old states of positive mass; zero-mass fibers make
no contribution to the law of total probability. -/
theorem jointBind_probability_and_le_on_support
    [DecidableEq Ω] [DecidableEq Ξ]
    (L : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ)
    (P : Ω → Prop) (Q : Ω → Ξ → Prop) (b : ℝ≥0)
    (hQ : ∀ ω, 0 < L.mass ω → P ω →
      (K ω).probability (Q ω) ≤ b) :
    (L.jointBind K).probability (fun z ↦ P z.1 ∧ Q z.1 z.2) ≤
      b * L.probability P := by
  classical
  rw [probability_jointBind]
  calc
    ∑ ω, L.mass ω * (K ω).probability
        (fun ξ ↦ P ω ∧ Q ω ξ) ≤
        ∑ ω, L.mass ω * (if P ω then b else 0) := by
      apply sum_le_sum
      intro ω _hω
      by_cases hmass : 0 < L.mass ω
      · by_cases hPω : P ω
        · simp only [hPω, true_and, if_true]
          gcongr
          exact hQ ω hmass hPω
        · have hfalse : (fun ξ ↦ P ω ∧ Q ω ξ) =
              (fun _ : Ξ ↦ False) := by
            funext ξ
            simp [hPω]
          rw [hfalse, probability_false]
          simp [hPω]
      · have hzero : L.mass ω = 0 :=
          le_antisymm (not_lt.mp hmass) zero_le
        simp [hzero]
    _ = b * L.probability P := by
      unfold probability
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro ω _hω
      by_cases hPω : P ω <;> simp [hPω, mul_comm]

end FiniteLaw

end

end Erdos207
