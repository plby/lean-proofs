/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceQuasiObstructionCount

/-! # Forbidden-order unions retain the proper residual-spoke obstruction -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem sourceQuasiObstructedVertices_biUnion_subset
    {J V : Type*} [DecidableEq J] [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (orders : Finset J) (F : J → ForbiddenFamilyOn V)
    (e : Sym2 V) (S B : Finset V) (G : SimpleGraph V) (I D : TripleSystemOn V) :
    sourceQuasiObstructedVertices W (orders.biUnion F) e S B G I D ⊆
      orders.biUnion (fun j ↦ sourceQuasiObstructedVertices W (F j) e S B G I D) := by
  intro u hu
  have hh := mem_filter.mp hu
  obtain ⟨T, hT, he, hlevel, hcomplete, hnot⟩ := hh.2.2.2.2
  obtain ⟨E, hE, hTE, hcover⟩ := hcomplete
  obtain ⟨j, hj, hEj⟩ := mem_biUnion.mp hE
  apply mem_biUnion.mpr
  refine ⟨j, hj, mem_filter.mpr ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1,
    T, hT, he, hlevel, ⟨E, hEj, hTE, hcover⟩, ?_⟩⟩
  rintro ⟨E', hE', hTE', hcover'⟩
  exact hnot ⟨E', mem_biUnion.mpr ⟨j, hj, hE'⟩, hTE', hcover'⟩

theorem sourceQuasiObstructedVertices_biUnion_card_le
    {J V : Type*} [DecidableEq J] [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (orders : Finset J) (F : J → ForbiddenFamilyOn V)
    (e : Sym2 V) (S B : Finset V) (G : SimpleGraph V) (I D : TripleSystemOn V) :
    (sourceQuasiObstructedVertices W (orders.biUnion F) e S B G I D).card ≤
      ∑ j ∈ orders, (sourceQuasiObstructedVertices W (F j) e S B G I D).card :=
  (card_le_card (sourceQuasiObstructedVertices_biUnion_subset W orders F e S B G I D)).trans card_biUnion_le

theorem FiniteLaw.sourceQuasiForbiddenOrders_probability_le
    {Ω J V : Type*} [Fintype Ω] [DecidableEq J] [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Ω) (W : Vortex V ell) (orders : Finset J) (F : J → ForbiddenFamilyOn V)
    (e : Sym2 V) (S B : Finset V) (G : SimpleGraph V) (I D : Ω → TripleSystemOn V)
    (cutoff error : J → ℝ≥0)
    (hbound : ∀ j ∈ orders, L.probability (fun ω ↦ cutoff j <
      (sourceQuasiObstructedVertices W (F j) e S B G (I ω) (D ω)).card) ≤ error j) :
    L.probability (fun ω ↦ (∑ j ∈ orders, cutoff j) <
      (sourceQuasiObstructedVertices W (orders.biUnion F) e S B G (I ω) (D ω)).card) ≤
        ∑ j ∈ orders, error j := by
  apply le_trans _ ((L.probability_exists_le orders _).trans (sum_le_sum hbound))
  apply L.probability_mono
  intro ω hbad
  by_contra hn
  have hupper : ∀ j ∈ orders,
      ((sourceQuasiObstructedVertices W (F j) e S B G (I ω) (D ω)).card : ℝ≥0) ≤ cutoff j := by
    intro j hj
    exact le_of_not_gt (fun h ↦ hn ⟨j, hj, h⟩)
  have hcount : ((sourceQuasiObstructedVertices W (orders.biUnion F) e S B G (I ω) (D ω)).card : ℝ≥0) ≤
      ∑ j ∈ orders, ((sourceQuasiObstructedVertices W (F j) e S B G (I ω) (D ω)).card : ℝ≥0) := by
    exact_mod_cast sourceQuasiObstructedVertices_biUnion_card_le W orders F e S B G (I ω) (D ω)
  exact (not_lt_of_ge (hcount.trans (sum_le_sum hupper))) hbad

end

end Erdos207
