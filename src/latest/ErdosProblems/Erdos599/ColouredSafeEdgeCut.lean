/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeFinitePortSplice
import ErdosProblems.Erdos599.RoofQuotient

/-!
# Cutting one represented edge without losing vertices

Apply the existing finite-port splice to two trivial port paths. The
result retains both pieces of the old owner and every other old member.
The cut tail becomes a full terminal and no new edge is inserted.
-/

noncomputable section

namespace Erdos599.DWeb.IsWarp

open Set _root_.Erdos599.DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {D : DWeb V} {W : Set D.DPath} {s t : V}

theorem exists_edgeCut (hW : D.IsWarp W) (hedge : (s, t) ∈ familyEdges W) (hne : s ≠ t) :
    ∃ U : Set D.DPath, D.IsWarp U ∧ familyEdges U = familyEdges W \ {(s, t)} ∧
      D.vertexSet U = D.vertexSet W ∧ D.initialSet W ⊆ D.initialSet U ∧
      D.terminalFrontier U = D.terminalFrontier W ∪ {s} ∧
      ∀ r : Ray D.graph, Sum.inr r ∈ U →
        ∃ r0 : Ray D.graph, Sum.inr r0 ∈ W ∧
          ∃ lost : Set (V × V), lost.Finite ∧ r0.edgeSet \ lost ⊆ r.edgeSet := by
  let K := D.trivialPath '' ({s, t} : Set V)
  have hK : D.IsWarp K := D.isWarp_trivialPaths _
  have hKfinite : D.HasFiniteCharacter K := by
    rintro p ⟨x, _hx, rfl⟩
    exact ⟨FinitePath.trivial D.graph x, rfl⟩
  have hKV : D.vertexSet K = {s, t} := D.vertexSet_trivialPaths _
  have hKT : D.terminalFrontier K = {s, t} := D.terminalFrontier_trivialPaths _
  have hKE : familyEdges K = ∅ := by
    apply Set.Subset.antisymm ?_ (Set.empty_subset _)
    intro e he
    simp only [familyEdges, Set.mem_iUnion] at he
    obtain ⟨p, ⟨x, _hx, rfl⟩, hep⟩ := he
    simp [DWeb.trivialPath, Path.trivial, FinitePath.edgeSet,
      FinitePath.trivial, Walk.edgeSet] at hep
  obtain ⟨U, hU, hUE, hUV, hUI, hUT, _hpE, _hpT, htrace⟩ :=
    ColouredSafeFinitePortSplice.exists_finitePortSplice_exact hW hK hKfinite hedge hne
      (FinitePath.trivial D.graph s) ⟨s, by simp, rfl⟩ rfl
      (by rw [hKV, hKT]; exact id)
      (by rw [hKV]; exact Set.inter_subset_left)
  have hports : ({s, t} : Set V) ⊆ D.vertexSet W := by
    rw [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact familyEdges_subset_vertexSet_prod W hedge
  refine ⟨U, hU, ?_, ?_, ?_, ?_, htrace⟩
  · simpa only [hKE, Set.union_empty] using hUE
  · rw [hUV, hKV, Set.union_eq_self_of_subset_right hports]
  · rw [hUI]
    exact Set.subset_union_left.trans Set.subset_union_left
  · rw [hUT, hKT]
    have hdiff : ({s, t} \ {t} : Set V) = {s} := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
      aesop
    rw [hdiff]

#print axioms exists_edgeCut

end Erdos599.DWeb.IsWarp
