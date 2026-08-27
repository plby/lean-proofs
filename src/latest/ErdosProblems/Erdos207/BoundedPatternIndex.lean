/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialRootTypicality
import ErdosProblems.Erdos207.FiniteSpanCounting

/-! # A polynomial index set containing every bounded-support graph pattern -/

namespace Erdos207

open Finset

noncomputable section

abbrev BoundedGraphPattern (V : Type*) [Fintype V] [DecidableEq V] (h : ℕ) :=
  {Q : SimpleGraph V // (graphSupportFinset Q).card ≤ h}

abbrev WorkingGraphPattern {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (h : ℕ) := {Q : BoundedGraphPattern V h // Q.1 ≤ G}

noncomputable instance workingGraphPatternFintype
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (h : ℕ) :
    Fintype (WorkingGraphPattern G h) := Fintype.ofFinite _

theorem graphEdges_injective
    {V : Type*} [Fintype V] [DecidableEq V] :
    Function.Injective (graphEdges (V := V)) := by
  intro Q R h
  ext a b
  have he : s(a, b) ∈ graphEdges Q ↔ s(a, b) ∈ graphEdges R := by rw [h]
  simpa only [mem_graphEdges_iff, SimpleGraph.mem_edgeSet] using he

def boundedGraphPatternCode
    {V : Type*} [Fintype V] [DecidableEq V] (h : ℕ) (Q : BoundedGraphPattern V h) :
    subsetsUpToCard (univ : Finset (Sym2 V)) (h ^ 2) :=
  ⟨graphEdges Q.1, mem_subsetsUpToCard_iff.mpr ⟨subset_univ _,
    (card_graphEdges_le_graphSupportFinset_sq Q.1).trans (Nat.pow_le_pow_left Q.2 2)⟩⟩

theorem boundedGraphPatternCode_injective
    {V : Type*} [Fintype V] [DecidableEq V] (h : ℕ) :
    Function.Injective (boundedGraphPatternCode (V := V) h) := by
  intro Q R hQR
  apply Subtype.ext
  exact graphEdges_injective (congrArg Subtype.val hQR)

theorem card_sym2_le_square
    (V : Type*) [Fintype V] : Fintype.card (Sym2 V) ≤ Fintype.card V ^ 2 := by
  have hinj : Function.Injective (fun e : Sym2 V ↦ e.out) := by
    intro e f hef
    have h := congrArg (fun p : V × V ↦ s(p.1, p.2)) hef
    simpa only [Sym2.mk, e.out_eq, f.out_eq] using h
  simpa only [Fintype.card_prod, pow_two] using Fintype.card_le_of_injective _ hinj

theorem card_boundedGraphPattern_le_polynomial
    (V : Type*) [Fintype V] [DecidableEq V] (h : ℕ) :
    Fintype.card (BoundedGraphPattern V h) ≤
      (h ^ 2 + 1) * (Fintype.card V + 1) ^ (2 * h ^ 2) := by
  calc
    _ ≤ Fintype.card (subsetsUpToCard (univ : Finset (Sym2 V)) (h ^ 2)) :=
      Fintype.card_le_of_injective (boundedGraphPatternCode h) (boundedGraphPatternCode_injective h)
    _ = (subsetsUpToCard (univ : Finset (Sym2 V)) (h ^ 2)).card := Fintype.card_coe _
    _ ≤ (h ^ 2 + 1) * (Fintype.card (Sym2 V) + 1) ^ (h ^ 2) := by
      simpa only [card_univ] using card_subsetsUpToCard_le (univ : Finset (Sym2 V)) (h ^ 2)
    _ ≤ (h ^ 2 + 1) * ((Fintype.card V + 1) ^ 2) ^ (h ^ 2) := by
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      have hc := card_sym2_le_square V
      nlinarith only [hc, Nat.zero_le (Fintype.card V)]
    _ = _ := by rw [pow_mul]

theorem card_workingGraphPattern_le_polynomial
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (h : ℕ) :
    Fintype.card (WorkingGraphPattern G h) ≤
      (h ^ 2 + 1) * (Fintype.card V + 1) ^ (2 * h ^ 2) := by
  exact (Fintype.card_le_of_injective (fun Q : WorkingGraphPattern G h ↦ Q.1)
    Subtype.val_injective).trans (card_boundedGraphPattern_le_polynomial V h)

end

end Erdos207
