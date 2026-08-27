/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLeftObstructionCount
import ErdosProblems.Erdos207.SourceQuasiForbiddenOrders

/-! # Finite forbidden-order unions for the reserved-spoke left obstruction -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem sourceLeftObstructedVertices_biUnion_subset
    {J V : Type*} [DecidableEq J] [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (orders : Finset J) (F : J → ForbiddenFamilyOn V)
    (e : Sym2 V) (S : Finset V) (G : SimpleGraph V) (I D : TripleSystemOn V)
    (reserve : Finset (Sym2 V)) :
    sourceLeftObstructedVertices W (orders.biUnion F) e S G I D reserve ⊆
      orders.biUnion (fun j ↦ sourceLeftObstructedVertices W (F j) e S G I D reserve) := by
  intro u hu
  have hh := mem_filter.mp hu
  obtain ⟨j, hj, huj⟩ := mem_biUnion.mp
    (sourceQuasiObstructedVertices_biUnion_subset W orders F e S e.toFinset G I D hh.1)
  exact mem_biUnion.mpr ⟨j, hj, mem_filter.mpr ⟨huj, hh.2⟩⟩

theorem sourceLeftObstructedVertices_biUnion_card_le
    {J V : Type*} [DecidableEq J] [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (orders : Finset J) (F : J → ForbiddenFamilyOn V)
    (e : Sym2 V) (S : Finset V) (G : SimpleGraph V) (I D : TripleSystemOn V)
    (reserve : Finset (Sym2 V)) :
    (sourceLeftObstructedVertices W (orders.biUnion F) e S G I D reserve).card ≤
      ∑ j ∈ orders, (sourceLeftObstructedVertices W (F j) e S G I D reserve).card :=
  (card_le_card (sourceLeftObstructedVertices_biUnion_subset W orders F e S G I D reserve)).trans
    card_biUnion_le

theorem FiniteLaw.sourceLeftForbiddenOrders_probability_le
    {Ω J V : Type*} [Fintype Ω] [DecidableEq J] [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Ω) (W : Vortex V ell) (orders : Finset J) (F : J → ForbiddenFamilyOn V)
    (e : Sym2 V) (S : Finset V) (G : SimpleGraph V) (I D : Ω → TripleSystemOn V)
    (reserve : Ω → Finset (Sym2 V)) (cutoff error : J → ℝ≥0)
    (hbound : ∀ j ∈ orders, L.probability (fun ω ↦ cutoff j <
      (sourceLeftObstructedVertices W (F j) e S G (I ω) (D ω) (reserve ω)).card) ≤ error j) :
    L.probability (fun ω ↦ (∑ j ∈ orders, cutoff j) <
      (sourceLeftObstructedVertices W (orders.biUnion F) e S G (I ω) (D ω) (reserve ω)).card) ≤
        ∑ j ∈ orders, error j := by
  apply le_trans _ ((L.probability_exists_le orders _).trans (sum_le_sum hbound))
  apply L.probability_mono
  intro ω hbad
  by_contra hn
  have hupper : ∀ j ∈ orders,
      ((sourceLeftObstructedVertices W (F j) e S G (I ω) (D ω) (reserve ω)).card : ℝ≥0) ≤ cutoff j := by
    intro j hj
    exact le_of_not_gt (fun h ↦ hn ⟨j, hj, h⟩)
  have hcount : ((sourceLeftObstructedVertices W (orders.biUnion F) e S G (I ω) (D ω) (reserve ω)).card : ℝ≥0) ≤
      ∑ j ∈ orders, ((sourceLeftObstructedVertices W (F j) e S G (I ω) (D ω) (reserve ω)).card : ℝ≥0) := by
    exact_mod_cast sourceLeftObstructedVertices_biUnion_card_le W orders F e S G (I ω) (D ω) (reserve ω)
  exact (not_lt_of_ge (hcount.trans (sum_le_sum hupper))) hbad

end

end Erdos207
