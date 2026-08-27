/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveWedgeLegality

/-!
# Deterministic greedy cover of an indexed edge list

This is the finite induction underlying KSSS Section 10.2.  Edges are exposed
in an arbitrary order.  An already covered edge is skipped; otherwise a
strict reserve-candidate surplus over the current edge and forbidden blockers
supplies one legal triangle.  The induction preserves packinghood and
forbidden avoidance through `GreedyReachable`.
-/

namespace Erdos207

open Finset

noncomputable section

lemma coveredGraph_mono
    {V : Type*} [DecidableEq V] {P Q : TripleSystemOn V}
    (hPQ : P ⊆ Q) : coveredGraph P ≤ coveredGraph Q := by
  intro u v huv
  obtain ⟨T, hTP, huT, hvT, huvne⟩ := coveredGraph_adj.mp huv
  exact coveredGraph_adj.mpr ⟨T, hPQ hTP, huT, hvT, huvne⟩

/-- Greedily cover every edge in a list, provided the current blocker count
is always strictly smaller than its fixed reserve-supported candidate set. -/
theorem exists_greedyReachable_cover_edgeList
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (A P₀ : TripleSystemOn V)
    (G : SimpleGraph V) (U : Finset V) (ω : Sym2 V → Bool)
    (edges : List (Sym2 V)) (S : Sym2 V → Finset V)
    (hpacking₀ : IsPackingOn P₀) (havoid₀ : AvoidsForbidden P₀ F)
    (hne : ∀ e, e ∈ edges → e.out.1 ≠ e.out.2)
    (hu : ∀ e, e ∈ edges → e.out.1 ∉ U)
    (hv : ∀ e, e ∈ edges → e.out.2 ∉ U)
    (hSU : ∀ e, e ∈ edges → S e ⊆ U)
    (hA : ∀ e, ∀ he : e ∈ edges, ∀ w, ∀ hw : w ∈ S e,
      let w' : ThirdVertex e.out.1 e.out.2 :=
        ⟨w, fun h ↦ hu e he (h ▸ hSU e he hw),
          fun h ↦ hv e he (h ▸ hSU e he hw)⟩
      thirdVertexTriple (hne e he) w' ∈ A)
    (hsurplus : ∀ (Q : TripleSystemOn V) (e : Sym2 V),
      ∀ hreach : GreedyReachable F P₀ Q, Q ⊆ P₀ ∪ A →
      (Q \ P₀).card ≤ edges.length →
      ∀ he : e ∈ edges,
      (leaveGraph Q).Adj e.out.1 e.out.2 →
      (edgeBlockedThirdVertices A Q (hne e he) ∪
        forbiddenBlockedThirdVertices F A Q (hne e he)).card <
        (activeReserveWedgeVertices G U (S e)
          e.out.1 e.out.2 ω).card) :
    ∃ Q : TripleSystemOn V,
      GreedyReachable F P₀ Q ∧ Q ⊆ P₀ ∪ A ∧
      (Q \ P₀).card ≤ edges.length ∧
      ∀ e ∈ edges, (coveredGraph Q).Adj e.out.1 e.out.2 := by
  classical
  suffices haux : ∀ (todo : List (Sym2 V)),
      (∀ e, e ∈ todo → e ∈ edges) →
      ∀ Q : TripleSystemOn V,
        GreedyReachable F P₀ Q → Q ⊆ P₀ ∪ A →
        (Q \ P₀).card + todo.length ≤ edges.length →
        ∃ Q' : TripleSystemOn V,
          GreedyReachable F P₀ Q' ∧ Q ⊆ Q' ∧ Q' ⊆ P₀ ∪ A ∧
          (Q' \ Q).card ≤ todo.length ∧
          ∀ e ∈ todo, (coveredGraph Q').Adj e.out.1 e.out.2 by
    obtain ⟨Q, hreach, _hP₀Q, hQA, hcard, hcover⟩ :=
      haux edges (fun _e he ↦ he) P₀ GreedyReachable.refl
        (subset_union_left) (by simp)
    exact ⟨Q, hreach, hQA, hcard, hcover⟩
  intro todo htodo
  induction todo with
  | nil =>
      intro Q hreach hQA _hinv
      exact ⟨Q, hreach, Subset.rfl, hQA, by simp, by simp⟩
  | cons e tail ih =>
      intro Q hreach hQA hinv
      have heEdges : e ∈ edges := htodo e (by simp)
      have htailSub : ∀ f, f ∈ tail → f ∈ edges := by
        intro f hf
        exact htodo f (by simp [hf])
      by_cases heCovered : (coveredGraph Q).Adj e.out.1 e.out.2
      · have hinvTail : (Q \ P₀).card + tail.length ≤ edges.length := by
          simp only [List.length_cons] at hinv
          omega
        obtain ⟨Q', hreach', hQQ', hQ'A, hcard, htail⟩ :=
          ih htailSub Q hreach hQA hinvTail
        refine ⟨Q', hreach', hQQ', hQ'A, ?_, ?_⟩
        · simp only [List.length_cons]
          omega
        intro f hf
        simp only [List.mem_cons] at hf
        rcases hf with rfl | hf
        · exact coveredGraph_mono hQQ' heCovered
        · exact htail f hf
      · have heLeave : (leaveGraph Q).Adj e.out.1 e.out.2 := by
          apply leaveGraph_adj.mpr
          refine ⟨hne e heEdges, ?_⟩
          rintro ⟨T, hTQ, hleft, hright, hne'⟩
          exact heCovered
            (coveredGraph_adj.mpr ⟨T, hTQ, hleft, hright, hne'⟩)
        have hpackingQ : IsPackingOn Q := hreach.isPacking hpacking₀
        have hAvoidQ : AvoidsForbidden Q F := hreach.avoidsForbidden havoid₀
        have hAe : ∀ w, ∀ hw : w ∈ S e,
            let w' : ThirdVertex e.out.1 e.out.2 :=
              ⟨w, fun h ↦ hu e heEdges (h ▸ hSU e heEdges hw),
                fun h ↦ hv e heEdges (h ▸ hSU e heEdges hw)⟩
            thirdVertexTriple heLeave.ne w' ∈ A := by
          intro w hw
          have hbase := hA e heEdges w hw
          exact hbase
        have hglobal : (Q \ P₀).card ≤ edges.length := by
          omega
        obtain ⟨w, _hwActive, hTA, hlegal⟩ :=
          exists_legal_activeReserveWedge_of_blocked_lt
            hpackingQ hAvoidQ heLeave (hu e heEdges) (hv e heEdges)
            (hSU e heEdges) ω hAe
              (hsurplus Q e hreach hQA hglobal heEdges heLeave)
        let T := thirdVertexTriple heLeave.ne w
        let Q₁ := insert T Q
        have hreach₁ : GreedyReachable F P₀ Q₁ :=
          GreedyReachable.step hreach hlegal
        have hQQ₁ : Q ⊆ Q₁ := subset_insert T Q
        have hQ₁A : Q₁ ⊆ P₀ ∪ A := by
          intro R hR
          rw [mem_insert] at hR
          rcases hR with rfl | hRQ
          · exact mem_union_right P₀ hTA
          · exact hQA hRQ
        have hnewCard : (Q₁ \ P₀).card ≤ (Q \ P₀).card + 1 := by
          have hP₀Q : P₀ ⊆ Q := hreach.initial_subset
          have hP₀Q₁ : P₀ ⊆ Q₁ := hP₀Q.trans hQQ₁
          rw [card_sdiff_of_subset hP₀Q₁,
            card_sdiff_of_subset hP₀Q]
          have hcardQ₁ : Q₁.card ≤ Q.card + 1 := by
            simpa [Q₁] using card_insert_le T Q
          omega
        have hinv₁ : (Q₁ \ P₀).card + tail.length ≤ edges.length := by
          simp only [List.length_cons] at hinv
          omega
        have heCovered₁ : (coveredGraph Q₁).Adj e.out.1 e.out.2 := by
          exact coveredGraph_adj.mpr ⟨T, mem_insert_self T Q,
            left_mem_thirdVertexTriple _ _, right_mem_thirdVertexTriple _ _,
            heLeave.ne⟩
        obtain ⟨Q', hreach', hQ₁Q', hQ'A, hcardTail, htail⟩ :=
          ih htailSub Q₁ hreach₁ hQ₁A hinv₁
        refine ⟨Q', hreach', hQQ₁.trans hQ₁Q', hQ'A, ?_, ?_⟩
        · rw [card_sdiff_of_subset (hQQ₁.trans hQ₁Q')]
          rw [card_sdiff_of_subset hQ₁Q'] at hcardTail
          have hcardQ₁ : Q₁.card ≤ Q.card + 1 := by
            simpa [Q₁] using card_insert_le T Q
          simp only [List.length_cons]
          omega
        intro f hf
        simp only [List.mem_cons] at hf
        rcases hf with rfl | hf
        · exact coveredGraph_mono hQ₁Q' heCovered₁
        · exact htail f hf

end

end Erdos207
