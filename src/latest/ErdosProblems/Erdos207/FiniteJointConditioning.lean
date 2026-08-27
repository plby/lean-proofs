/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteJointBind
import ErdosProblems.Erdos207.FiniteConditioning

/-!
# Conditioning a joint finite law on uniformly likely fibers

The reserve event used in one cover-down step depends on the old state.
These elementary lemmas turn a uniform conditional failure estimate for the
new sample into positivity and a quantitative lower bound for the good event
in the joint law.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

namespace FiniteLaw

variable {Omega Xi : Type*} [Fintype Omega] [DecidableEq Omega]
  [Fintype Xi] [DecidableEq Xi]

/-- A uniform bound on failure in every conditional fiber is also a bound
on failure in the joint law. -/
theorem jointBind_probability_not_le
    (L : FiniteLaw Omega) (K : Omega → FiniteLaw Xi)
    (Good : Omega → Xi → Prop) (epsilon : ℝ≥0)
    (hbad : ∀ omega, (K omega).probability (fun xi ↦ ¬ Good omega xi) ≤ epsilon) :
    (L.jointBind K).probability (fun z ↦ ¬ Good z.1 z.2) ≤ epsilon := by
  have h := L.jointBind_probability_and_le K (fun _ ↦ True)
    (fun omega xi ↦ ¬ Good omega xi) epsilon
    (fun omega _htrue ↦ hbad omega)
  simpa only [true_and, probability_true, mul_one] using h

/-- A failure bound is needed only on base points having positive mass. -/
theorem jointBind_probability_not_le_on_support
    (L : FiniteLaw Omega) (K : Omega → FiniteLaw Xi)
    (Good : Omega → Xi → Prop) (epsilon : ℝ≥0)
    (hbad : ∀ omega, 0 < L.mass omega →
      (K omega).probability (fun xi ↦ ¬ Good omega xi) ≤ epsilon) :
    (L.jointBind K).probability (fun z ↦ ¬ Good z.1 z.2) ≤ epsilon := by
  have h := L.jointBind_probability_and_le_on_support K (fun _ ↦ True)
    (fun omega xi ↦ ¬ Good omega xi) epsilon
    (fun omega hmass _htrue ↦ hbad omega hmass)
  simpa only [true_and, probability_true, mul_one] using h

/-- The joint good event has probability at least `1 - epsilon`. -/
theorem one_sub_le_jointBind_probability
    (L : FiniteLaw Omega) (K : Omega → FiniteLaw Xi)
    (Good : Omega → Xi → Prop) (epsilon : ℝ≥0)
    (hbad : ∀ omega, (K omega).probability (fun xi ↦ ¬ Good omega xi) ≤ epsilon) :
    1 - epsilon ≤ (L.jointBind K).probability (fun z ↦ Good z.1 z.2) := by
  let J := L.jointBind K
  have hnot : J.probability (fun z ↦ ¬ Good z.1 z.2) ≤ epsilon :=
    L.jointBind_probability_not_le K Good epsilon hbad
  rw [J.probability_not] at hnot
  exact tsub_le_iff_tsub_le.mp hnot

/-- The support-sensitive fiber bound gives the same lower bound for the
joint good event. -/
theorem one_sub_le_jointBind_probability_on_support
    (L : FiniteLaw Omega) (K : Omega → FiniteLaw Xi)
    (Good : Omega → Xi → Prop) (epsilon : ℝ≥0)
    (hbad : ∀ omega, 0 < L.mass omega →
      (K omega).probability (fun xi ↦ ¬ Good omega xi) ≤ epsilon) :
    1 - epsilon ≤ (L.jointBind K).probability (fun z ↦ Good z.1 z.2) := by
  let J := L.jointBind K
  have hnot : J.probability (fun z ↦ ¬ Good z.1 z.2) ≤ epsilon :=
    L.jointBind_probability_not_le_on_support K Good epsilon hbad
  rw [J.probability_not] at hnot
  exact tsub_le_iff_tsub_le.mp hnot

/-- If the uniform conditional failure bound is below one, the joint good
event has positive probability. -/
theorem jointBind_probability_pos_of_not_le
    (L : FiniteLaw Omega) (K : Omega → FiniteLaw Xi)
    (Good : Omega → Xi → Prop) (epsilon : ℝ≥0)
    (hbad : ∀ omega, (K omega).probability (fun xi ↦ ¬ Good omega xi) ≤ epsilon)
    (hepsilon : epsilon < 1) :
    0 < (L.jointBind K).probability (fun z ↦ Good z.1 z.2) := by
  have hlower := L.one_sub_le_jointBind_probability K Good epsilon hbad
  exact (tsub_pos_iff_lt.mpr hepsilon).trans_le hlower

/-- Conditioning the joint law on its dependent good event is supported on
that event. -/
theorem conditionJointBind_supported
    (L : FiniteLaw Omega) (K : Omega → FiniteLaw Xi)
    (Good : Omega → Xi → Prop)
    (hpos : 0 < (L.jointBind K).probability (fun z ↦ Good z.1 z.2)) :
    ((L.jointBind K).conditionOn (fun z ↦ Good z.1 z.2) hpos).SupportedOn
      (fun z ↦ Good z.1 z.2) :=
  conditionOn_supported _ _ hpos

end FiniteLaw

end

end Erdos207
