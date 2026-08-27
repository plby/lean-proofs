/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SampledLinkGoodCover
import ErdosProblems.Erdos207.SourceLinkForbiddenOrders

/-! # Fixed pinned-edge unions for varying prior data and varying links -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem FiniteLaw.not_sampledLinkForbiddenGood_le
    {Ω O V : Type*} [Fintype Ω] [DecidableEq V]
    (L : FiniteLaw Ω) (K : Ω → O → BipartiteLink V) (F : ForbiddenFamilyOn V)
    (I D Q : Ω → TripleSystemOn V) (cap : ℕ) (pins : Finset (Sym2 V)) (error : Sym2 V → ℝ≥0)
    (hpins : ∀ x, (∀ o (a : ↥(K x o).left), s((K x o).center,(K x o).leftEmbedding a) ∈ pins) ∧
      (∀ o (b : ↥(K x o).right), s((K x o).center,(K x o).rightEmbedding b) ∈ pins))
    (htail : ∀ e ∈ pins, L.probability (fun x ↦ cap < (sourceLinkForbiddenSamples F (I x) (D x) (Q x) e).card) ≤ error e) :
    L.probability (fun x ↦ ¬ IsSampledLinkForbiddenGood (K x) F (I x) (D x) (Q x) cap) ≤
      ∑ e ∈ pins, error e := by
  calc
    _ ≤ L.probability (fun x ↦ ∃ e ∈ pins, cap < (sourceLinkForbiddenSamples F (I x) (D x) (Q x) e).card) := by
      apply L.probability_mono
      intro x hx
      by_contra hnone
      push Not at hnone
      apply hx
      intro o
      exact ⟨fun a ↦ hnone _ ((hpins x).1 o a), fun b ↦ hnone _ ((hpins x).2 o b)⟩
    _ ≤ ∑ e ∈ pins, L.probability (fun x ↦ cap < (sourceLinkForbiddenSamples F (I x) (D x) (Q x) e).card) :=
      L.probability_exists_le pins _
    _ ≤ _ := sum_le_sum htail

theorem FiniteLaw.not_sampledLinkForbiddenOrdersGood_le
    {Ω O V J : Type*} [Fintype Ω] [DecidableEq V] [DecidableEq J]
    (L : FiniteLaw Ω) (K : Ω → O → BipartiteLink V) (orders : Finset J) (F : J → ForbiddenFamilyOn V)
    (I D Q : Ω → TripleSystemOn V) (cap : J → ℕ) (pins : Finset (Sym2 V)) (error : J → Sym2 V → ℝ≥0)
    (hpins : ∀ x, (∀ o (a : ↥(K x o).left), s((K x o).center,(K x o).leftEmbedding a) ∈ pins) ∧
      (∀ o (b : ↥(K x o).right), s((K x o).center,(K x o).rightEmbedding b) ∈ pins))
    (htail : ∀ j ∈ orders, ∀ e ∈ pins,
      L.probability (fun x ↦ cap j < (sourceLinkForbiddenSamples (F j) (I x) (D x) (Q x) e).card) ≤ error j e) :
    L.probability (fun x ↦ ¬ IsSampledLinkForbiddenGood (K x) (orders.biUnion F) (I x) (D x) (Q x)
      (∑ j ∈ orders, cap j)) ≤ ∑ e ∈ pins, ∑ j ∈ orders, error j e := by
  apply L.not_sampledLinkForbiddenGood_le K (orders.biUnion F) I D Q (∑ j ∈ orders, cap j)
    pins (fun e ↦ ∑ j ∈ orders, error j e) hpins
  intro e he
  exact L.sourceLinkForbiddenOrders_probability_le orders F I D Q e cap (fun j ↦ error j e)
    (fun j hj ↦ htail j hj e he)

end

end Erdos207
