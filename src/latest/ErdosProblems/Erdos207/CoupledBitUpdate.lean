/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IndependentMonotoneCoupling
import ErdosProblems.Erdos207.FiniteLawKernelCalculus
import Mathlib.Data.Fintype.Powerset

/-! # Coupling an arbitrary batch update to independent proposals -/

namespace Erdos207.FiniteLaw

open Finset
open scoped NNReal

noncomputable section

def coupledBitUpdate
    {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (p q : I → ℝ≥0) (hpq : ∀ i, p i ≤ q i) (hq : ∀ i, q i ≤ 1)
    (update : (I → Bool) → S) : FiniteLaw (Finset I × S) :=
  map (fun x ↦ (selectedByBits (fun i ↦ (x i).1), update (fun i ↦ (x i).2)))
    (independentMonotoneBits p q hpq hq)

theorem coupledBitUpdate_proposal
    {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (p q : I → ℝ≥0) (hpq : ∀ i, p i ≤ q i) (hq : ∀ i, q i ≤ 1)
    (update : (I → Bool) → S) :
    map Prod.fst (coupledBitUpdate p q hpq hq update) =
      map selectedByBits (independentBits q hq) := by
  unfold coupledBitUpdate
  rw [map_comp, ← independentMonotoneBits_proposal p q hpq hq, map_comp]
  rfl

theorem coupledBitUpdate_actual
    {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (p q : I → ℝ≥0) (hpq : ∀ i, p i ≤ q i) (hq : ∀ i, q i ≤ 1)
    (update : (I → Bool) → S) :
    map Prod.snd (coupledBitUpdate p q hpq hq update) =
      map update (independentBits p (fun i ↦ (hpq i).trans (hq i))) := by
  unfold coupledBitUpdate
  rw [map_comp, ← independentMonotoneBits_actual p q hpq hq, map_comp]
  rfl

theorem coupledBitUpdate_supported
    {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (p q : I → ℝ≥0) (hpq : ∀ i, p i ≤ q i) (hq : ∀ i, q i ≤ 1)
    (update : (I → Bool) → S) (accepted : S → Finset I) (old : Finset I)
    (hupdate : ∀ x, accepted (update x) ⊆ old ∪ selectedByBits x) :
    (coupledBitUpdate p q hpq hq update).SupportedOn
      (fun z ↦ accepted z.2 ⊆ old ∪ z.1) := by
  unfold coupledBitUpdate
  apply SupportedOn.map (Q := fun z ↦ accepted z.2 ⊆ old ∪ z.1)
    (independentMonotoneBits_supported p q hpq hq)
    (fun x ↦ (selectedByBits (fun i ↦ (x i).1), update (fun i ↦ (x i).2)))
  intro x hx
  exact (hupdate _).trans (union_subset_union Subset.rfl hx)

end

end Erdos207.FiniteLaw
