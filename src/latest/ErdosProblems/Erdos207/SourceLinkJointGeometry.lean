/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLinkReservoirGeometry

/-! # Named geometric certificates for the joint marked-link application -/

namespace Erdos207

open Finset
open scoped Classical

noncomputable section

structure RawLinkSourceGeometry
    {O V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell+1)) (Gamma : SimpleGraph V) (U : Finset V)
    (initial later historical available : TripleSystemOn V) (reserve : Finset (Sym2 V))
    (center : O ↪ V) (links : O → BipartiteLink V) (orders : Finset ℕ) (F : ℕ → ForbiddenFamilyOn V) : Prop where
  center_eq : ∀ o, (links o).center = center o
  center_outside : ∀ o, center o ∉ U
  left_inner : ∀ o, (links o).left ⊆ U
  right_inner : ∀ o, (links o).right ⊆ U
  reserve_spokes : ∀ o, (links o).SpokesIn reserve
  graph_spokes : ∀ o, (links o).SpokesIn (graphEdges Gamma)
  triangles : ConsistsOfTriangles Gamma available
  terminal_available : ∀ T ∈ available, T.1 ⊆ W.U k
  initially_safe : ∀ j ∈ orders, ∀ T ∈ available, ¬ CompletesForbidden (F j) (initial ∪ historical) T
  later_terminal : ∀ T ∈ later \ historical, (W.prefix k).level T = Fin.last k.val

theorem RawLinkSourceGeometry.pinned_edges
    {O V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell+1)} {Gamma : SimpleGraph V} {U : Finset V}
    {initial later historical available : TripleSystemOn V} {reserve : Finset (Sym2 V)}
    {center : O ↪ V} {links : O → BipartiteLink V} {orders : Finset ℕ} {F : ℕ → ForbiddenFamilyOn V}
    (hg : RawLinkSourceGeometry W k Gamma U initial later historical available reserve center links orders F) :
    (∀ o (x : ↥(links o).left), s((links o).center,(links o).leftEmbedding x) ∈ crossingEdges Gamma U) ∧
    (∀ o (x : ↥(links o).right), s((links o).center,(links o).rightEmbedding x) ∈ crossingEdges Gamma U) := by
  constructor
  · intro o x
    apply mem_crossingEdges_iff.mpr
    refine ⟨mem_graphEdges_iff.mp ((hg.graph_spokes o).1 x.1 x.2), ?_⟩
    exact isCrossingEdge_mk_iff.mpr (Or.inr ⟨hg.left_inner o x.2,
      by simpa only [hg.center_eq o] using hg.center_outside o⟩)
  · intro o x
    apply mem_crossingEdges_iff.mpr
    refine ⟨mem_graphEdges_iff.mp ((hg.graph_spokes o).2 x.1 x.2), ?_⟩
    exact isCrossingEdge_mk_iff.mpr (Or.inr ⟨hg.right_inner o x.2,
      by simpa only [hg.center_eq o] using hg.center_outside o⟩)

theorem RawLinkSourceGeometry.reservoir_source_geometry
    {O V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell+1)} {Gamma : SimpleGraph V} {U : Finset V}
    {initial later historical available : TripleSystemOn V} {reserve : Finset (Sym2 V)}
    {center : O ↪ V} {links : O → BipartiteLink V} {orders : Finset ℕ} {F : ℕ → ForbiddenFamilyOn V}
    (hg : RawLinkSourceGeometry W k Gamma U initial later historical available reserve center links orders F)
    {result : TripleSystemOn V × TripleSystemOn V}
    (hs : IsSampledLinkJointOutcome (orders.biUnion F) available (initial ∪ later) links result)
    {j : ℕ} (hj : j ∈ orders) :
    result.1 ⊆ sourceLinkAmbientCandidates (W.U k) U ∧
      (∀ T ∈ result.1, ¬ CompletesForbidden (F j) (initial ∪ historical) T) ∧
      (∀ T ∈ later \ historical, (W.prefix k).level T = Fin.last k.val) ∧
      result.1.biUnion tripleEdgeFinset ⊆ sourceLinkRetainedEdges Gamma U initial later reserve := by
  refine ⟨?_, fun T hT ↦ hg.initially_safe j hj T (hs.reservoir_available hT), hg.later_terminal,
    hs.reservoir_retainedEdges hg.triangles hg.center_eq hg.center_outside hg.left_inner hg.right_inner hg.reserve_spokes⟩
  intro T hT
  exact mem_sourceLinkAmbientCandidates_iff.mpr ⟨hg.terminal_available T (hs.reservoir_available hT),
    hs.reservoir_family.card_inner_vertices hg.center_eq hg.center_outside hg.left_inner hg.right_inner T hT⟩

theorem rawLinkSource_joint_geometry
    {Ω O V : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {kernel : Ω → FiniteLaw (TripleSystemOn V × TripleSystemOn V)}
    {W : Vortex V ell} {k : Fin (ell+1)} {Gamma : SimpleGraph V} {U : Finset V}
    {initial later historical available : Ω → TripleSystemOn V} {reserve : Ω → Finset (Sym2 V)}
    {center : Ω → O ↪ V} {links : Ω → O → BipartiteLink V} {orders : Finset ℕ} {F : ℕ → ForbiddenFamilyOn V}
    (hgeometry : L.SupportedOn fun omega ↦ RawLinkSourceGeometry W k Gamma U (initial omega) (later omega)
      (historical omega) (available omega) (reserve omega) (center omega) (links omega) orders F)
    (hstruct : ∀ omega, 0 < L.mass omega → (kernel omega).SupportedOn
      (IsSampledLinkJointOutcome (orders.biUnion F) (available omega) (initial omega ∪ later omega) (links omega)))
    {j : ℕ} (hj : j ∈ orders) :
    (L.jointBind kernel).SupportedOn fun result ↦ result.2.1 ⊆ sourceLinkAmbientCandidates (W.U k) U ∧
      (∀ T ∈ result.2.1, ¬ CompletesForbidden (F j) (initial result.1 ∪ historical result.1) T) ∧
      (∀ T ∈ later result.1 \ historical result.1, (W.prefix k).level T = Fin.last k.val) ∧
      result.2.1.biUnion tripleEdgeFinset ⊆
        sourceLinkRetainedEdges Gamma U (initial result.1) (later result.1) (reserve result.1) := by
  intro result hmass
  have hm := (L.jointBind_mass_pos_iff kernel result.1 result.2).mp hmass
  exact (hgeometry result.1 hm.1).reservoir_source_geometry (hstruct result.1 hm.1 result.2 hm.2) hj

theorem rawLinkSource_joint_pins
    {Ω O V : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} (kernel : Ω → FiniteLaw (TripleSystemOn V × TripleSystemOn V))
    {W : Vortex V ell} {k : Fin (ell+1)} {Gamma : SimpleGraph V} {U : Finset V}
    {initial later historical available : Ω → TripleSystemOn V} {reserve : Ω → Finset (Sym2 V)}
    {center : Ω → O ↪ V} {links : Ω → O → BipartiteLink V} {orders : Finset ℕ} {F : ℕ → ForbiddenFamilyOn V}
    (hgeometry : L.SupportedOn fun omega ↦ RawLinkSourceGeometry W k Gamma U (initial omega) (later omega)
      (historical omega) (available omega) (reserve omega) (center omega) (links omega) orders F) :
    (L.jointBind kernel).SupportedOn fun result ↦
      (∀ o (x : ↥(links result.1 o).left), s((links result.1 o).center,(links result.1 o).leftEmbedding x) ∈ crossingEdges Gamma U) ∧
      (∀ o (x : ↥(links result.1 o).right), s((links result.1 o).center,(links result.1 o).rightEmbedding x) ∈ crossingEdges Gamma U) := by
  intro result hmass
  exact (hgeometry result.1 ((L.jointBind_mass_pos_iff kernel result.1 result.2).mp hmass).1).pinned_edges

end

end Erdos207
