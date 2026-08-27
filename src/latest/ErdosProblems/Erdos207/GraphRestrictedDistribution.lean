/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PersistentPairDistributionObstruction

/-! # Distribution estimates for prescribed edges in the initial working graph

The ambient graph restriction excludes both diagonals and deterministically
reserved absorber edges. No factor inverse to the target density is needed.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def IsInitialGraphProductBound
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (selected : Ω → TripleSystemOn V) (G : SimpleGraph V)
    (p C b : ℝ≥0) : Prop :=
  ∀ (Q : TripleSystemOn V) (E : Finset (Sym2 V)), E ⊆ graphEdges G →
    L.probability (fun ω ↦ Q ⊆ selected ω ∧
      ∀ e ∈ E, e ∉ (coveredGraph (selected ω)).edgeSet) ≤
      C ^ (Q.card + E.card) * (p ^ E.card * (Fintype.card V : ℝ≥0)⁻¹ ^ Q.card + b)

def IsGraphStronglyWellDistributed
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Ω) (W : Vortex V ell) (k : Fin (ell + 1)) (G : SimpleGraph V)
    (initial later : Ω → TripleSystemOn V) (p C b : ℝ≥0) : Prop :=
  ∀ (Ifix Dfix : TripleSystemOn V) (Efix : Finset (Sym2 V)),
    Disjoint Ifix Dfix → Efix ⊆ graphEdges G →
    L.probability (StrongDistributionEvent initial later Ifix Dfix Efix) ≤
      C ^ (Ifix.card + Dfix.card + Efix.card) *
        (p ^ Efix.card * (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card * laterTriangleScale W k p Dfix + b)

theorem offdiagPart_eq_of_subset_graphEdges
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {E : Finset (Sym2 V)}
    (hE : E ⊆ graphEdges G) : offdiagPart E = E := by
  apply Subset.antisymm (offdiagPart_subset E)
  intro e he
  exact mem_offdiagPart_iff.mpr ⟨he, G.not_isDiag_of_mem_edgeSet (mem_graphEdges_iff.mp (hE he))⟩

theorem initialGraphProductScale_of_survival_point
    {V : Type*} [Fintype V] [DecidableEq V]
    (survival point p C b : ℝ≥0) (hsurvival : survival ≤ C * p)
    (hpoint : point ≤ C * (Fintype.card V : ℝ≥0)⁻¹) (hC : 1 ≤ C)
    (Q : TripleSystemOn V) (E : Finset (Sym2 V)) :
    survival ^ E.card * point ^ Q.card + b ≤
      C ^ (Q.card + E.card) * (p ^ E.card * (Fintype.card V : ℝ≥0)⁻¹ ^ Q.card + b) := by
  have hmain : survival ^ E.card * point ^ Q.card ≤
      C ^ (Q.card + E.card) * (p ^ E.card * (Fintype.card V : ℝ≥0)⁻¹ ^ Q.card) := by
    calc
      _ ≤ (C * p) ^ E.card * (C * (Fintype.card V : ℝ≥0)⁻¹) ^ Q.card := by gcongr
      _ = _ := by rw [mul_pow, mul_pow, pow_add]; ring
  have herror : b ≤ C ^ (Q.card + E.card) * b := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_pow₀ hC : 1 ≤ C ^ (Q.card + E.card)) zero_le
  calc
    _ ≤ C ^ (Q.card + E.card) * (p ^ E.card * (Fintype.card V : ℝ≥0)⁻¹ ^ Q.card) +
        C ^ (Q.card + E.card) * b := add_le_add hmain herror
    _ = _ := by ring

theorem initialGraphProductBound_of_compatible_patterns
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (selected : Ω → TripleSystemOn V) (G : SimpleGraph V)
    (ambient : TripleSystemOn V) (survival point p C b : ℝ≥0)
    (hstruct : L.SupportedOn fun ω ↦ IsPackingOn (selected ω) ∧ selected ω ⊆ ambient)
    (hcompatible : ∀ (Q : TripleSystemOn V) (E : Finset (Sym2 V)),
      IsPackingOn Q → Q ⊆ ambient → Disjoint (Q.biUnion tripleEdgeFinset) E → E ⊆ graphEdges G →
      L.probability (fun ω ↦ Q ⊆ selected ω ∧
        ∀ e ∈ E, e ∉ (coveredGraph (selected ω)).edgeSet) ≤
        survival ^ E.card * point ^ Q.card + b)
    (hsurvival : survival ≤ C * p) (hpoint : point ≤ C * (Fintype.card V : ℝ≥0)⁻¹)
    (hC : 1 ≤ C) : IsInitialGraphProductBound L selected G p C b := by
  classical
  intro Q E hE
  by_cases hgood : IsPackingOn Q ∧ Q ⊆ ambient ∧ Disjoint (Q.biUnion tripleEdgeFinset) E
  · exact (hcompatible Q E hgood.1 hgood.2.1 hgood.2.2 hE).trans
      (initialGraphProductScale_of_survival_point survival point p C b hsurvival hpoint hC Q E)
  · have hzero : L.probability (fun ω ↦ Q ⊆ selected ω ∧
        ∀ e ∈ E, e ∉ (coveredGraph (selected ω)).edgeSet) ≤ L.probability (fun _ ↦ False) := by
      apply L.probability_mono_of_supported hstruct
      intro ω hω hevent
      apply hgood
      refine ⟨hω.1.mono hevent.1, hevent.1.trans hω.2, disjoint_left.mpr ?_⟩
      intro e heQ heE
      obtain ⟨T, hT, heT⟩ := mem_biUnion.mp heQ
      apply hevent.2 e heE
      rw [coveredGraph_edgeSet_eq_biUnion]
      exact mem_biUnion.mpr ⟨T, hevent.1 hT, heT⟩
    rw [L.probability_false] at hzero
    exact hzero.trans zero_le

theorem IsInitialGraphProductBound.toGraphStronglyWellDistributed
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {selected : Ω → TripleSystemOn V} {G : SimpleGraph V} {p C b : ℝ≥0}
    (h : IsInitialGraphProductBound L selected G p C b) (W : Vortex V ell) (k : Fin (ell + 1)) :
    IsGraphStronglyWellDistributed L W k G selected (fun _ ↦ ∅) p C b := by
  classical
  intro Ifix Dfix Efix _hdisjoint hE
  by_cases hD : Dfix = ∅
  · subst Dfix
    have hevent : StrongDistributionEvent selected (fun _ ↦ ∅) Ifix ∅ Efix =
        (fun ω ↦ Ifix ⊆ selected ω ∧ ∀ e ∈ Efix, e ∉ (coveredGraph (selected ω)).edgeSet) := by
      funext ω
      simp [StrongDistributionEvent]
    rw [hevent]
    simpa only [card_empty, add_zero,
      laterTriangleScale_empty, mul_one] using h Ifix Efix hE
  · have hzero : L.probability (StrongDistributionEvent selected (fun _ ↦ ∅) Ifix Dfix Efix) ≤
        L.probability (fun _ ↦ False) := by
      apply L.probability_mono
      intro ω hevent
      exact hD (subset_empty.mp hevent.2.1)
    rw [L.probability_false] at hzero
    exact hzero.trans zero_le

end

end Erdos207
