/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveEdgeSampling
import ErdosProblems.Erdos207.IndependentBernoulliBudgetTail

/-! # Exponential upper tails for reserve spokes on any fixed vertex set -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def reserveSpokeEdges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U X : Finset V) (w : V) : Finset (Sym2 V) :=
  (X.image (fun v ↦ s(v, w))) ∩ crossingEdges G U

theorem reserveSpoke_image_selected
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U X : Finset V) (w : V) (omega : Sym2 V → Bool) :
    (X.filter (fun v ↦ s(v, w) ∈ reserveEdges G U omega)).image (fun v ↦ s(v, w)) =
      (reserveSpokeEdges G U X w).filter (fun e ↦ omega e = true) := by
  ext e
  simp only [mem_image, mem_filter, mem_reserveEdges_iff, reserveSpokeEdges, mem_inter]
  constructor
  · rintro ⟨v, ⟨hv, he, hbit⟩, rfl⟩
    exact ⟨⟨⟨v, hv, rfl⟩, he⟩, hbit⟩
  · rintro ⟨⟨⟨v, hv, rfl⟩, he⟩, hbit⟩
    exact ⟨v, ⟨hv, he, hbit⟩, rfl⟩

theorem reserveSpoke_selected_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U X : Finset V) (w : V) (omega : Sym2 V → Bool) :
    (X.filter (fun v ↦ s(v, w) ∈ reserveEdges G U omega)).card =
      ((reserveSpokeEdges G U X w).filter (fun e ↦ omega e = true)).card := by
  have hinj : Function.Injective (fun v : V ↦ s(v, w)) := fun _ _ h ↦ Sym2.congr_left.mp h
  have h := congrArg Finset.card (reserveSpoke_image_selected G U X w omega)
  simpa only [card_image_of_injective _ hinj] using h

theorem reserveSpoke_mean_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U X : Finset V) (w : V) (r : ℝ≥0) :
    (∑ e ∈ reserveSpokeEdges G U X w, (reserveEdgeProbability G U r e : ℝ)) ≤
      (r : ℝ) * X.card := by
  have hinj : Function.Injective (fun v : V ↦ s(v, w)) := fun _ _ h ↦ Sym2.congr_left.mp h
  have hcard : (reserveSpokeEdges G U X w).card ≤ X.card := by
    calc
      _ ≤ (X.image (fun v ↦ s(v, w))).card := card_le_card inter_subset_left
      _ = X.card := card_image_of_injective _ hinj
  have hcardR : ((reserveSpokeEdges G U X w).card : ℝ) ≤ X.card := by exact_mod_cast hcard
  calc
    _ = ∑ _e ∈ reserveSpokeEdges G U X w, (r : ℝ) := by
      apply sum_congr rfl
      intro e he
      simp only [reserveEdgeProbability, if_pos (mem_inter.mp he).2]
    _ = (r : ℝ) * (reserveSpokeEdges G U X w).card := by
      simp only [sum_const, nsmul_eq_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcardR r.coe_nonneg

theorem reserveEdgeLaw_probability_spoke_count_ge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U X : Finset V) (w : V) (r : ℝ≥0) (hr : r ≤ 1) :
    ((reserveEdgeLaw G U r hr).probability (fun omega ↦
      2 * (r : ℝ) * X.card ≤ (X.filter (fun v ↦ s(v, w) ∈ reserveEdges G U omega)).card) : ℝ) ≤
      Real.exp (-(r : ℝ) * X.card / 4) := by
  have h := FiniteLaw.independentBits_probability_count_ge_twice_budget
    (reserveEdgeProbability G U r) (reserveEdgeProbability_le_one G U hr)
    (reserveSpokeEdges G U X w) ((r : ℝ) * X.card) (reserveSpoke_mean_le G U X w r)
  simpa only [reserveEdgeLaw, reserveSpoke_selected_card, mul_assoc, neg_mul] using h

end

end Erdos207
