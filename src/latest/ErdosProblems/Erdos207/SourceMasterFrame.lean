/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ResidualMasterCompression
import ErdosProblems.Erdos207.IntermediateLinkSourceGeometry

/-! # Deterministic old-state data survives every prepared-law reindexing -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

structure SourceMasterFrame
    {Omega V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell+1)) (F : ForbiddenFamilyOn V)
    (Gamma : SimpleGraph V) (ambient : TripleSystemOn V)
    (G : Omega → SimpleGraph V) (A I D : Omega → TripleSystemOn V) (p eta xi : ℝ≥0) (h : ℕ) : Prop where
  stage : ∀ omega, IsMasterStagePointwiseGood W k F (G omega) (A omega) (I omega) (D omega) p eta xi h
  even : ∀ omega v, Even ((neighborsIn (G omega) univ v).card)
  available : ∀ omega, A omega ⊆ ambient
  selected : ∀ omega, I omega ∪ D omega ⊆ ambient
  cover : ∀ omega, CoversOriginalGraph Gamma (G omega) (I omega) (D omega)
  graph_le : ∀ omega, G omega ≤ Gamma
  support : ∀ omega, GraphSupportedOn (G omega) (W.U k : Set V)

theorem SourceMasterFrame.comp
    {Omega Xi V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell+1)} {F : ForbiddenFamilyOn V}
    {Gamma : SimpleGraph V} {ambient : TripleSystemOn V}
    {G : Omega → SimpleGraph V} {A I D : Omega → TripleSystemOn V} {p eta xi : ℝ≥0} {h : ℕ}
    (frame : SourceMasterFrame W k F Gamma ambient G A I D p eta xi h) (f : Xi → Omega) :
    SourceMasterFrame W k F Gamma ambient (G ∘ f) (A ∘ f) (I ∘ f) (D ∘ f) p eta xi h :=
  ⟨fun x ↦ frame.stage (f x), fun x ↦ frame.even (f x), fun x ↦ frame.available (f x),
    fun x ↦ frame.selected (f x), fun x ↦ frame.cover (f x), fun x ↦ frame.graph_le (f x),
    fun x ↦ frame.support (f x)⟩

theorem IsResidualCompressedMasterLaw.sourceFrame
    {Xi V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw (MasterStateOn V)} {W : Vortex V ell} {k : Fin (ell+1)}
    {F : ForbiddenFamilyOn V} {Gamma : SimpleGraph V} {ambient : TripleSystemOn V}
    {p eta xi C beta : ℝ≥0} {h : ℕ}
    (hlaw : IsResidualCompressedMasterLaw law W k F Gamma ambient p eta xi C beta h)
    (hpointwise : law.SupportedOn (masterPointwiseGoodEvent W k F MasterStateOn.graph MasterStateOn.available
      MasterStateOn.initial MasterStateOn.later p eta xi h))
    (f : Xi → MasterStateOn V) (hf : ∀ x, 0 < law.mass (f x)) :
    SourceMasterFrame W k F Gamma ambient (MasterStateOn.graph ∘ f) (MasterStateOn.available ∘ f)
      (MasterStateOn.initial ∘ f) (MasterStateOn.later ∘ f) p eta xi h :=
  ⟨fun x ↦ hpointwise (f x) (hf x), fun x ↦ hlaw.1.1 (f x) (hf x),
    fun x ↦ hlaw.2.1 (f x) (hf x), fun x ↦ hlaw.2.2.1 (f x) (hf x),
    fun x ↦ hlaw.2.2.2.1 (f x) (hf x), fun x ↦ hlaw.2.2.2.2.1 (f x) (hf x),
    fun x ↦ hlaw.2.2.2.2.2 (f x) (hf x)⟩

theorem SourceMasterFrame.available_geometry
    {Omega V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell+1)} {F : ForbiddenFamilyOn V}
    {Gamma : SimpleGraph V} {ambient : TripleSystemOn V}
    {G : Omega → SimpleGraph V} {A I D : Omega → TripleSystemOn V} {p eta xi : ℝ≥0} {h : ℕ}
    (frame : SourceMasterFrame W k F Gamma ambient G A I D p eta xi h) (omega : Omega) :
    (∀ T ∈ A omega, (W.prefix k).level T = Fin.last k.val) ∧
      ∀ T ∈ A omega, ∀ e ∈ tripleEdgeFinset T,
        e ∈ graphEdges Gamma ∧ e ∉ (coveredGraph (I omega ∪ D omega)).edgeSet := by
  have htri := (frame.stage omega).2.2.2.2.2.1
  have hleave := (frame.stage omega).2.2.2.2.1
  constructor
  · intro T hT
    exact W.prefix_level_eq_last_of_subset k T (htri.triple_vertices_subset (frame.support omega) hT)
  · intro T hT e he
    induction e using Sym2.ind with
    | h u v =>
      have hG : (G omega).Adj u v := mem_graphEdges_iff.mp (htri.triple_edges_subset hT he)
      exact ⟨mem_graphEdges_iff.mpr (frame.graph_le omega hG), (leaveGraph_adj.mp (hleave hG)).2⟩

theorem SourceMasterFrame.available_disjoint
    {Omega V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell+1)} {F : ForbiddenFamilyOn V}
    {Gamma : SimpleGraph V} {ambient : TripleSystemOn V}
    {G : Omega → SimpleGraph V} {A I D : Omega → TripleSystemOn V} {p eta xi : ℝ≥0} {h : ℕ}
    (frame : SourceMasterFrame W k F Gamma ambient G A I D p eta xi h) (omega : Omega) :
    Disjoint (A omega) (I omega ∪ D omega) := by
  apply disjoint_left.mpr
  intro T hT hOld
  obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.mp (show 1 < T.1.card by rw [T.property]; omega)
  have hG := (frame.stage omega).2.2.2.2.2.1 T hT u hu v hv huv
  exact (leaveGraph_adj.mp ((frame.stage omega).2.2.2.2.1 hG)).2
    (coveredGraph_adj.mpr ⟨T, hOld, hu, hv, huv⟩)

end

end Erdos207
