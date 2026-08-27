/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IndependentBitsRestriction
import ErdosProblems.Erdos207.CoupledBitUpdate

/-! # A fixed ambient proposal universe around variable auxiliary coordinates -/

namespace Erdos207.FiniteLaw

open Finset
open scoped NNReal

noncomputable section

def coupledEmbeddedBitUpdate
    {J I S : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    [Fintype S] [DecidableEq S]
    (e : J ↪ I) (p : J → ℝ≥0) (q : I → ℝ≥0)
    (hpq : ∀ j, p j ≤ q (e j)) (hq : ∀ i, q i ≤ 1)
    (update : (J → Bool) → S) : FiniteLaw (Finset I × S) :=
  coupledBitUpdate (extendBitProbability e p) q (extendBitProbability_le e p q hpq) hq
    (fun x ↦ update (fun j ↦ x (e j)))

theorem coupledEmbeddedBitUpdate_proposal
    {J I S : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    [Fintype S] [DecidableEq S]
    (e : J ↪ I) (p : J → ℝ≥0) (q : I → ℝ≥0)
    (hpq : ∀ j, p j ≤ q (e j)) (hq : ∀ i, q i ≤ 1)
    (update : (J → Bool) → S) :
    map Prod.fst (coupledEmbeddedBitUpdate e p q hpq hq update) =
      map selectedByBits (independentBits q hq) :=
  coupledBitUpdate_proposal _ _ _ _ _

theorem coupledEmbeddedBitUpdate_actual
    {J I S : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    [Fintype S] [DecidableEq S]
    (e : J ↪ I) (p : J → ℝ≥0) (q : I → ℝ≥0)
    (hpq : ∀ j, p j ≤ q (e j)) (hq : ∀ i, q i ≤ 1)
    (update : (J → Bool) → S) :
    map Prod.snd (coupledEmbeddedBitUpdate e p q hpq hq update) =
      map update (independentBits p (fun j ↦ (hpq j).trans (hq (e j)))) := by
  unfold coupledEmbeddedBitUpdate
  rw [coupledBitUpdate_actual]
  rw [← independentBits_restrict_extension e p _
    (fun i ↦ (extendBitProbability_le e p q hpq i).trans (hq i)), map_comp]
  rfl

theorem selectedByBits_restrict_map_subset
    {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (e : J ↪ I) (x : I → Bool) :
    (selectedByBits (fun j ↦ x (e j))).map e ⊆ selectedByBits x := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := mem_map.mp hi
  have hj' : x (e j) = true := by simpa only [mem_selectedByBits_iff] using hj
  exact mem_selectedByBits_iff.mpr hj'

theorem coupledEmbeddedBitUpdate_supported
    {J I S : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    [Fintype S] [DecidableEq S]
    (e : J ↪ I) (p : J → ℝ≥0) (q : I → ℝ≥0)
    (hpq : ∀ j, p j ≤ q (e j)) (hq : ∀ i, q i ≤ 1)
    (update : (J → Bool) → S) (accepted : S → Finset J) (old : Finset J)
    (hupdate : ∀ x, accepted (update x) ⊆ old ∪ selectedByBits x) :
    (coupledEmbeddedBitUpdate e p q hpq hq update).SupportedOn
      (fun z ↦ (accepted z.2).map e ⊆ old.map e ∪ z.1) := by
  apply coupledBitUpdate_supported _ _ _ _ _ (fun s ↦ (accepted s).map e) (old.map e)
  intro x
  have hmap : (accepted (update (fun j ↦ x (e j)))).map e ⊆
      (old ∪ selectedByBits (fun j ↦ x (e j))).map e :=
    map_subset_map.mpr (hupdate (fun j ↦ x (e j)))
  rw [map_union] at hmap
  exact hmap.trans (union_subset_union Subset.rfl (selectedByBits_restrict_map_subset e x))

end

end Erdos207.FiniteLaw
