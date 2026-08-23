/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerInduction

/-!
# The inner finite induction in van der Poorten--Loxton Lemma 4

At a fixed outer level `N`, source Lemma 4 repeats the same integral
Hermite extrapolation step `3 * (rank + 1)` times.  The invariant after `t`
steps is vanishing on the exact rectangle

`lemmaFourRadius N t × lemmaFourBudget N t`.

This file isolates that finite induction from the analytic proof of a single
step.  It also records the exact derivative-budget bookkeeping used in a
step: the new base multi-index budget plus the available jet-order loss is
the old budget.  In particular, the concrete interpolation argument can use
these theorems without reproving any recursion or natural-number arithmetic.
-/

noncomputable section

namespace Erdos240.BakerLemma4InnerInduction

open Erdos240
open Erdos240.BakerInduction

variable {ι : Type*} [Fintype ι]

/-- The exact fixed-outer-level invariant after `t` integral extrapolation
steps in source Lemma 4. -/
def InnerInvariant (P : VDPLParameters ι)
    (G : ℂ → VDPLMultiIndex P.rank → ℂ) (N t : ℕ) : Prop :=
  VanishesOn G 1 (P.lemmaFourRadius N t) (P.lemmaFourBudget N t)

/-- The number of inner extrapolation steps in source Lemma 4. -/
def terminalStage (P : VDPLParameters ι) : ℕ :=
  3 * (P.rank + 1)

/-- An assumption-transparent interface for the analytic one-step argument.
The bound on `t` prevents the callback from being asked to prove a step past
the source endpoint. -/
def InnerStepCallback (P : VDPLParameters ι)
    (G : ℂ → VDPLMultiIndex P.rank → ℂ) (N : ℕ) : Prop :=
  ∀ t, t < terminalStage P →
    InnerInvariant P G N t → InnerInvariant P G N (t + 1)

/-- The level seed is definitionally the stage-zero inner invariant. -/
theorem innerInvariant_zero_iff
    (P : VDPLParameters ι) (G : ℂ → VDPLMultiIndex P.rank → ℂ) (N : ℕ) :
    InnerInvariant P G N 0 ↔ IntegralSeedAtLevel P G N := by
  simp [InnerInvariant, IntegralSeedAtLevel]

/-- The terminal inner invariant is definitionally the full output retained
for Lemma 5. -/
theorem innerInvariant_terminal_iff
    (P : VDPLParameters ι) (G : ℂ → VDPLMultiIndex P.rank → ℂ) (N : ℕ) :
    InnerInvariant P G N (terminalStage P) ↔
      IntegralExtrapolatedAtLevel P G N := by
  rfl

/-- Iterate an analytic one-step callback to every stage not past the source
endpoint. -/
theorem innerInvariant_of_le_terminal
    (P : VDPLParameters ι) (G : ℂ → VDPLMultiIndex P.rank → ℂ) (N : ℕ)
    (hzero : InnerInvariant P G N 0)
    (hstep : InnerStepCallback P G N) :
    ∀ t, t ≤ terminalStage P → InnerInvariant P G N t := by
  intro t
  induction t with
  | zero =>
      intro _ht
      exact hzero
  | succ t ih =>
      intro ht
      exact hstep t (Nat.lt_of_succ_le ht)
        (ih (Nat.le_of_succ_le ht))

/-- Source Lemma 4's finite inner induction: a seed and the concrete
one-step interpolation callback produce the exact extrapolated rectangle. -/
theorem integralExtrapolatedAtLevel_of_innerStep
    (P : VDPLParameters ι) (G : ℂ → VDPLMultiIndex P.rank → ℂ) (N : ℕ)
    (hstep : InnerStepCallback P G N) :
    IntegralSeedAtLevel P G N → IntegralExtrapolatedAtLevel P G N := by
  intro hseed
  rw [← innerInvariant_terminal_iff P G N]
  exact innerInvariant_of_le_terminal P G N
    ((innerInvariant_zero_iff P G N).2 hseed) hstep _ le_rfl

/-- The exact Lemma 4 derivative budget never increases at an inner step.
The first step is the exceptional halving step; every later step uses the
source factor `1 - epsilon`. -/
theorem lemmaFourBudget_succ_le
    (P : VDPLParameters ι) (N t : ℕ) :
    P.lemmaFourBudget N (t + 1) ≤ P.lemmaFourBudget N t := by
  cases t with
  | zero =>
      simp only [Nat.zero_add, P.lemmaFourBudget_zero,
        P.lemmaFourBudget_one]
      have hfloor :
          ((⌊(P.Slevel N : ℝ) / 2⌋₊ : ℕ) : ℝ) ≤
            (P.Slevel N : ℝ) / 2 :=
        Nat.floor_le (by positivity)
      have hhalf : (P.Slevel N : ℝ) / 2 ≤ P.Slevel N := by
        have hnonneg : (0 : ℝ) ≤ P.Slevel N := by positivity
        linarith
      exact_mod_cast hfloor.trans hhalf
  | succ t =>
      have htpos : 1 ≤ t + 1 := by omega
      have hepslt : P.epsilon < 1 := by
        rw [P.epsilon_eq]
        have hrank : (0 : ℝ) < P.rank + 1 := by positivity
        apply (div_lt_one (by positivity : (0 : ℝ) < 6 * (P.rank + 1))).2
        nlinarith
      have harg :
          0 ≤ (1 - P.epsilon) *
            (P.lemmaFourBudget N (t + 1) : ℝ) := by
        positivity
      have hfloor :
          ((⌊(1 - P.epsilon) *
              (P.lemmaFourBudget N (t + 1) : ℝ)⌋₊ : ℕ) : ℝ) ≤
            (1 - P.epsilon) *
              (P.lemmaFourBudget N (t + 1) : ℝ) :=
        Nat.floor_le harg
      have hmul :
          (1 - P.epsilon) *
              (P.lemmaFourBudget N (t + 1) : ℝ) ≤
            P.lemmaFourBudget N (t + 1) := by
        have hbudget :
            (0 : ℝ) ≤ P.lemmaFourBudget N (t + 1) := by positivity
        nlinarith [P.epsilon_pos]
      rw [show t + 1 + 1 = t + 2 by omega,
        P.lemmaFourBudget_succ_succ,
        P.lemmaFourEpsilon_eq_epsilon htpos]
      exact_mod_cast hfloor.trans hmul

/-- Exact natural-number form of the base-budget/jet-budget decomposition. -/
theorem add_budgetLoss_eq {Bnext Bcur : ℕ} (h : Bnext ≤ Bcur) :
    Bnext + (Bcur - Bnext) = Bcur := by
  omega

/-- Inequality form of `add_budgetLoss_eq`, convenient for total-weight
estimates. -/
theorem add_budgetLoss_le {Bnext Bcur : ℕ} (h : Bnext ≤ Bcur) :
    Bnext + (Bcur - Bnext) ≤ Bcur := by
  exact (add_budgetLoss_eq h).le

/-- At every actual Lemma 4 step, the next base multi-index budget plus the
available jet-order loss is exactly the current budget. -/
theorem lemmaFourBudget_succ_add_loss_eq
    (P : VDPLParameters ι) (N t : ℕ) :
    P.lemmaFourBudget N (t + 1) +
        (P.lemmaFourBudget N t - P.lemmaFourBudget N (t + 1)) =
      P.lemmaFourBudget N t := by
  exact add_budgetLoss_eq (lemmaFourBudget_succ_le P N t)

/-- The requested inequality form of the source multiplicity bookkeeping. -/
theorem lemmaFourBudget_succ_add_loss_le
    (P : VDPLParameters ι) (N t : ℕ) :
    P.lemmaFourBudget N (t + 1) +
        (P.lemmaFourBudget N t - P.lemmaFourBudget N (t + 1)) ≤
      P.lemmaFourBudget N t := by
  exact (lemmaFourBudget_succ_add_loss_eq P N t).le

/-- A base multi-index of next-stage weight and a jet order within the lost
budget have combined multiplicity at most the current-stage budget. -/
theorem weight_add_jet_le_currentBudget
    (P : VDPLParameters ι) (N t : ℕ)
    (m : VDPLMultiIndex P.rank) (jetOrder : ℕ)
    (hm : VDPLMultiIndex.weight m ≤ P.lemmaFourBudget N (t + 1))
    (hjet : jetOrder ≤
      P.lemmaFourBudget N t - P.lemmaFourBudget N (t + 1)) :
    VDPLMultiIndex.weight m + jetOrder ≤ P.lemmaFourBudget N t := by
  exact (Nat.add_le_add hm hjet).trans
    (lemmaFourBudget_succ_add_loss_le P N t)

end Erdos240.BakerLemma4InnerInduction

#print axioms Erdos240.BakerLemma4InnerInduction.integralExtrapolatedAtLevel_of_innerStep
#print axioms Erdos240.BakerLemma4InnerInduction.lemmaFourBudget_succ_add_loss_eq
#print axioms Erdos240.BakerLemma4InnerInduction.weight_add_jet_le_currentBudget
