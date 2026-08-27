/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceProfileFiberCount
import ErdosProblems.Erdos207.SourceVortexWellSpread

/-! # Source WS2 for genuine configurations with equal remainders -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem genuine_profiledDistinctPair_vertex_bounds
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    (W : Vortex V ell) {F : ForbiddenFamilyOn V} (T T' : TripleOn V)
    (t : VortexProfile ell) (hconfig : ∀ E ∈ F, IsErdosConfigOn j E) (hj : 5 ≤ j)
    {p : TripleSystemOn V × TripleSystemOn V}
    (hp : p ∈ W.profiledDistinctEqualRemainderPairs F T T' t) :
    verticesOn ({T, T'} : TripleSystemOn V) ⊆ verticesOn p.1 ∧
      (verticesOn p.1).card = j ∧
      (verticesOn p.1 \ verticesOn ({T, T'} : TripleSystemOn V)).card ≤ j - 4 ∧
      ∀ k ≤ ell,
        finPrefixSum (W.vertexProfile (verticesOn p.1 \ verticesOn ({T, T'} : TripleSystemOn V))) k ≤
          finPrefixSum t k := by
  have hp0 := (mem_filter.mp hp).1
  obtain ⟨hE, hE', hne, hT, hT', hrem, hprof⟩ :=
    (W.mem_profiledDistinctEqualRemainderPairs_iff F T T' t p).mp hp
  have hspan := genuine_distinctEqualRemainderPairs_span_eq hconfig hj hp0
  have hroot : verticesOn ({T, T'} : TripleSystemOn V) ⊆ verticesOn p.1 := by
    intro x hx
    obtain ⟨S, hS, hxS⟩ := mem_biUnion.mp hx
    rcases mem_insert.mp hS with hST | hS
    · subst S
      exact mem_biUnion.mpr ⟨T, hT, hxS⟩
    · have hS' : S = T' := mem_singleton.mp hS
      subst S
      rw [hspan]
      exact mem_biUnion.mpr ⟨T', hT', hxS⟩
  have hcard : (verticesOn p.1).card = j := IsErdosConfig.vertices_card_eq (hconfig _ hE) hj
  have hfour := four_le_vertices_pair_of_ne (distinctEqualRemainderPairs_roots_ne hp0)
  have hextra : (verticesOn p.1 \ verticesOn ({T, T'} : TripleSystemOn V)).card ≤ j - 4 := by
    rw [card_sdiff_of_subset hroot, hcard]
    omega
  refine ⟨hroot, hcard, hextra, ?_⟩
  intro k hk
  let A := W.verticesBefore (verticesOn p.1 \ verticesOn ({T, T'} : TripleSystemOn V)) k
  have hAextra : A ⊆ verticesOn p.1 \ verticesOn ({T, T'} : TripleSystemOn V) := filter_subset _ _
  have hAcard : A.card ≤ j - 2 := (card_le_card hAextra).trans (hextra.trans (by omega))
  have htouch := IsErdosConfig.card_le_trianglesTouching (hconfig _ hE) hj A
    (hAextra.trans sdiff_subset) hAcard
  have hbefore := W.trianglesTouching_verticesBefore_subset (k := k) p.1 {T, T'}
  have hcross : T' ∉ p.1 := (distinctEqualRemainderPairs_cross_not_mem hp0).1
  have hdiff : p.1 \ {T, T'} = p.1.erase T := by
    simp only [sdiff_insert, sdiff_singleton_eq_erase, erase_eq_of_notMem hcross]
  rw [W.finPrefixSum_vertexProfile, ← hprof, W.finPrefixSum_outerProfile _ hk]
  change A.card ≤ _
  exact htouch.trans ((card_le_card hbefore).trans_eq (by rw [hdiff]))

theorem card_genuine_profiledDistinctPairs_source_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    (W : Vortex V ell) {F : ForbiddenFamilyOn V} (T T' : TripleOn V)
    (t : VortexProfile ell) (hconfig : ∀ E ∈ F, IsErdosConfigOn j E)
    (hj : 5 ≤ j) (hterminal : 0 < W.terminalSize) :
    ((W.profiledDistinctEqualRemainderPairs F T T' t).card : ℝ≥0) ≤
      (exactBankVortexCoefficient j ell : ℝ≥0) * W.sourceProfileScale (j - 4) t := by
  let P := W.profiledDistinctEqualRemainderPairs F T T' t
  let root := verticesOn ({T, T'} : TripleSystemOn V)
  let extra := fun p : TripleSystemOn V × TripleSystemOn V ↦ verticesOn p.1 \ root
  have hgeom := fun p (hp : p ∈ P) ↦ genuine_profiledDistinctPair_vertex_bounds W T T' t hconfig hj hp
  have hfiber : ∀ A : Finset V, (P.filter fun p ↦ extra p = A).card ≤ 2 ^ (j ^ 3) := by
    intro A
    let G := P.filter fun p ↦ extra p = A
    by_cases hG : G.Nonempty
    · obtain ⟨p0, hp0⟩ := hG
      have hm0 := mem_filter.mp hp0
      have hg0 := hgeom p0 hm0.1
      have hspan : (root ∪ A).card = j := by
        rw [← hm0.2]
        change (root ∪ (verticesOn p0.1 \ root)).card = j
        rw [union_sdiff_of_subset hg0.1]
        exact hg0.2.1
      have hcount : G.card ≤ (tripleSystemsSupportedOn (root ∪ A)).card := by
        apply card_le_card_of_injOn (fun p ↦ p.1)
        · intro p hp
          have hm := mem_filter.mp hp
          have hg := hgeom p hm.1
          apply mem_tripleSystemsSupportedOn_iff.mpr
          have heq : root ∪ A = verticesOn p.1 := by
            rw [← hm.2]
            exact union_sdiff_of_subset hg.1
          exact heq.symm.subset
        · intro p hp p' hp' heq
          exact distinctEqualRemainderPairs_fst_injOn F T T'
            (mem_filter.mp (mem_filter.mp hp).1).1
            (mem_filter.mp (mem_filter.mp hp').1).1 heq
      exact hcount.trans ((card_tripleSystemsSupportedOn_le _).trans_eq (by rw [hspan]))
    · change G.card ≤ _
      rw [not_nonempty_iff_eq_empty.mp hG, card_empty]
      exact zero_le
  have hsize : ∀ p ∈ P, (extra p).card ≤ j := by
    intro p hp
    exact (hgeom p hp).2.2.1.trans (by omega)
  have hb : ∀ p ∈ P, (extra p).card ≤ j - 4 ∧
      ∀ k ≤ ell, finPrefixSum (W.vertexProfile (extra p)) k ≤ finPrefixSum t k := by
    intro p hp
    exact (hgeom p hp).2.2
  have h := card_mul_terminal_pow_le_of_vertex_encoding W P extra t hterminal hfiber hsize hb
  rw [W.le_mul_sourceProfileScale_iff _ _ _ _ hterminal]
  exact_mod_cast h

end

end Erdos207
