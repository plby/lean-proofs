/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos182.Foundations
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Hall

/-!
# Regular factors of finite bipartite graphs

This file proves the factor lemma used in the lower-bound argument for
Erdős Problem 182: if a finite bipartite graph is `q`-regular, then it has
a spanning `r`-regular subgraph for every `r ≤ q`.

The proof is the standard one.  An incidence double count verifies Hall's
condition for every positive regular graph.  In the bipartite case Hall gives
a perfect matching; deleting it lowers every degree by one.  Induction then
extracts the required factor.
-/

open scoped Classical

namespace Erdos182

open SimpleGraph

/-- Instance-independent regularity, used internally to keep the induction
independent of the particular `Fintype` structures on neighbor sets. -/
private def IsRegularNcard {V : Type*} (G : SimpleGraph V) (q : ℕ) : Prop :=
  ∀ v, (G.neighborSet v).ncard = q

private theorem isRegularNcard_of_isRegularOfDegree {V : Type*} [Fintype V]
    {G : SimpleGraph V} {q : ℕ} (hG : G.IsRegularOfDegree q) : IsRegularNcard G q := by
  intro v
  rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
  exact hG v

private theorem isRegularOfDegree_of_isRegularNcard {V : Type*} [Fintype V]
    {G : SimpleGraph V} {q : ℕ} (hG : IsRegularNcard G q) : G.IsRegularOfDegree q := by
  intro v
  rw [← SimpleGraph.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard]
  exact hG v

/-- A positive finite regular graph satisfies the cardinal form of Hall's
condition.  Count incidences between `s` and its union of neighbor sets: the
left side is `q * |s|`, while each vertex on the right is counted at most
`q` times. -/
private theorem hall_ncard_of_pos_regular {V : Type*} [Fintype V]
    (G : SimpleGraph V) {q : ℕ} (hq : 0 < q) (hreg : IsRegularNcard G q) (s : Set V) :
    s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard := by
  classical
  let sf := s.toFinset
  let nf := sf.biUnion (fun v ↦ G.neighborFinset v)
  have hdouble := Finset.sum_card_eq_sum_biUnion_card (fun v ↦ G.neighborFinset v) sf
  have hleft : ∑ v ∈ sf, (G.neighborFinset v).card = sf.card * q := by
    apply Finset.sum_const_nat
    intro v _
    simpa [SimpleGraph.neighborFinset_def, Set.ncard_eq_toFinset_card'] using hreg v
  have hright :
      ∑ w ∈ nf, ({v | v ∈ sf ∧ w ∈ G.neighborFinset v} : Finset V).card ≤
        nf.card * q := by
    exact Finset.sum_le_card_nsmul nf
      (fun w ↦ ({v | v ∈ sf ∧ w ∈ G.neighborFinset v} : Finset V).card) q fun w _ ↦ by
        rw [← hreg w, Set.ncard_eq_toFinset_card']
        apply Finset.card_le_card
        intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
        have hadj : G.Adj v w := by
          simpa [SimpleGraph.mem_neighborFinset] using hv.2
        simpa [SimpleGraph.mem_neighborFinset] using hadj.symm
  have hmul : sf.card * q ≤ nf.card * q := hleft.symm.trans_le (hdouble.trans_le hright)
  have hcard : sf.card ≤ nf.card := Nat.le_of_mul_le_mul_right hmul hq
  have hnf : nf = (⋃ x ∈ s, G.neighborSet x).toFinset := by
    ext w
    simp [sf, nf, SimpleGraph.neighborFinset_def]
  rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
  rw [← hnf]
  simpa only [sf] using hcard

/-- Every finite positive regular bipartite graph has a perfect matching. -/
theorem exists_isPerfectMatching_of_pos_regular {V : Type*} [Fintype V]
    (G : SimpleGraph V) {q : ℕ} (hq : 0 < q) (hreg : G.IsRegularOfDegree q)
    (hbip : G.IsBipartite) : ∃ M : G.Subgraph, M.IsPerfectMatching := by
  classical
  obtain ⟨s, t, hst⟩ := hbip.exists_isBipartiteWith
  exact G.exists_isPerfectMatching_of_forall_ncard_le hst
    (hall_ncard_of_pos_regular G hq (isRegularNcard_of_isRegularOfDegree hreg))

private theorem isBipartite_mono {V : Type*} {G H : SimpleGraph V}
    (hG : G.IsBipartite) (hle : H ≤ G) : H.IsBipartite := by
  obtain ⟨s, t, hst⟩ := hG.exists_isBipartiteWith
  apply (show H.IsBipartiteWith s t from ?_).isBipartite
  refine ⟨hst.disjoint, ?_⟩
  intro v w hadj
  exact hst.mem_of_adj (hle hadj)

private theorem regularNcard_sdiff_perfectMatching {V : Type*} [Fintype V]
    (G : SimpleGraph V) {q : ℕ} (hreg : IsRegularNcard G (q + 1))
    {M : G.Subgraph} (hM : M.IsPerfectMatching) :
    IsRegularNcard (G \ M.spanningCoe) q := by
  classical
  have hMreg : IsRegularNcard M.spanningCoe 1 := by
    intro v
    rw [Set.ncard_eq_one, Set.singleton_iff_unique_mem]
    simpa [SimpleGraph.mem_neighborSet, SimpleGraph.Subgraph.spanningCoe_adj] using
      (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM v)
  intro v
  rw [SimpleGraph.neighborSet_sdiff,
    Set.ncard_sdiff (SimpleGraph.neighborSet_mono M.spanningCoe_le v)]
  simp [hreg v, hMreg v]

private theorem exists_regularNcard_spanning_subgraph_of_bipartite
    {V : Type*} [Fintype V] (G : SimpleGraph V) {q r : ℕ} (hbip : G.IsBipartite)
    (hreg : IsRegularNcard G q) (hr : r ≤ q) :
    ∃ H : SimpleGraph V, H ≤ G ∧ IsRegularNcard H r := by
  classical
  induction q generalizing G r with
  | zero =>
      have hr0 : r = 0 := Nat.eq_zero_of_le_zero hr
      subst r
      refine ⟨⊥, bot_le, ?_⟩
      intro v
      simp
  | succ q ih =>
      by_cases hrq : r = q + 1
      · subst r
        exact ⟨G, le_rfl, by simpa using hreg⟩
      · have hr' : r ≤ q := Nat.le_of_lt_succ (lt_of_le_of_ne hr hrq)
        have hregDegree : G.IsRegularOfDegree (q + 1) :=
          isRegularOfDegree_of_isRegularNcard hreg
        obtain ⟨M, hM⟩ :=
          exists_isPerfectMatching_of_pos_regular G (Nat.succ_pos q) hregDegree hbip
        let G' := G \ M.spanningCoe
        have hG'reg : IsRegularNcard G' q := by
          exact regularNcard_sdiff_perfectMatching G hreg hM
        have hG'bip : G'.IsBipartite :=
          isBipartite_mono hbip fun _ _ h ↦ h.1
        obtain ⟨H, hHle, hHreg⟩ := ih G' hG'bip hG'reg hr'
        have hG'le : G' ≤ G := fun _ _ h ↦ h.1
        exact ⟨H, hHle.trans hG'le, hHreg⟩

/-- The simple-graph form of the bipartite factor theorem. -/
theorem exists_regular_spanning_subgraph_of_bipartite {V : Type*} [Fintype V]
    (G : SimpleGraph V) {q r : ℕ} (hbip : G.IsBipartite)
    (hreg : G.IsRegularOfDegree q) (hr : r ≤ q) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.IsRegularOfDegree r := by
  obtain ⟨H, hHle, hHreg⟩ :=
    exists_regularNcard_spanning_subgraph_of_bipartite G hbip
      (isRegularNcard_of_isRegularOfDegree hreg) hr
  exact ⟨H, hHle, isRegularOfDegree_of_isRegularNcard hHreg⟩

/-- The subgraph form of the bipartite factor theorem.  The returned subgraph
contains every ambient vertex. -/
theorem exists_spanning_regular_subgraph_of_bipartite {V : Type*} [Fintype V]
    (G : SimpleGraph V) {q r : ℕ} (hbip : G.IsBipartite)
    (hreg : G.IsRegularOfDegree q) (hr : r ≤ q) :
    ∃ H : G.Subgraph, H.IsSpanning ∧ H.spanningCoe.IsRegularOfDegree r := by
  obtain ⟨H, hHle, hHreg⟩ :=
    exists_regular_spanning_subgraph_of_bipartite G hbip hreg hr
  exact ⟨G.toSubgraph H hHle, SimpleGraph.toSubgraph.isSpanning (G := G) H hHle, hHreg⟩

/-- A nonempty finite bipartite `q`-regular graph contains a nonempty
`r`-regular subgraph for every `r ≤ q`, in the literal support semantics of
`ContainsRegularSubgraph`. -/
theorem containsRegularSubgraph_of_bipartite_regular {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) {q r : ℕ} (hbip : G.IsBipartite)
    (hreg : G.IsRegularOfDegree q) (hr : r ≤ q) :
    ContainsRegularSubgraph G r := by
  obtain ⟨H, hHspan, hHreg⟩ :=
    exists_spanning_regular_subgraph_of_bipartite G hbip hreg hr
  refine ⟨H, ?_, ?_⟩
  · exact ⟨Classical.choice inferInstance, hHspan _⟩
  · intro v
    rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree,
      SimpleGraph.Subgraph.coe_degree, ← SimpleGraph.Subgraph.degree_spanningCoe]
    exact hHreg v

/-- In a finite bipartite graph, the presence of a nonempty `q`-regular
subgraph with `3 ≤ q` forces the presence of a nonempty `3`-regular
subgraph.  The factor is first found inside the given regular subgraph and is
then mapped back through the canonical inclusion into the ambient graph. -/
theorem containsRegularSubgraph_three_of_bipartite
    {V : Type*} [Fintype V] (G : SimpleGraph V) {q : ℕ}
    (hbip : G.IsBipartite) (hq : 3 ≤ q)
    (hG : ContainsRegularSubgraph G q) : ContainsRegularSubgraph G 3 := by
  classical
  obtain ⟨K, hKne, hKreg⟩ := hG
  let : Nonempty K.verts := Set.nonempty_coe_sort.mpr hKne
  obtain ⟨J, hJne, hJreg⟩ :=
    containsRegularSubgraph_of_bipartite_regular K.coe (hbip.subgraph K) (by
      intro v
      rw [← SimpleGraph.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard]
      exact hKreg v) hq
  let f : SimpleGraph.Copy K.coe G := ⟨K.hom, K.hom_injective⟩
  let L : G.Subgraph := J.map f.toHom
  let e : J.coe ≃g L.coe := f.isoSubgraphMap J
  refine ⟨L, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := hJne
    exact ⟨f v, Set.mem_image_of_mem f hv⟩
  · intro v
    obtain ⟨x, hx, hxv⟩ := v.2
    let xJ : J.verts := ⟨x, hx⟩
    have hev : e xJ = v := by
      apply Subtype.ext
      exact hxv
    rw [← hev]
    rw [← Set.ncard_congr' (e.mapNeighborSet xJ)]
    exact hJreg xJ

end Erdos182
