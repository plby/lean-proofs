/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos76.AlmostComplete
import ErdosProblems.Erdos570.BondyChvatal
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Sparse-complement Hamilton cycles for the almost-complete induction

This file supplies the graph-theoretic input called Corollary 2.5 in
Gruslys--Letzter.  It is separated from the fractional-packing construction:
a graph on at least three vertices with at most `|V| - 3 + a` missing edges
has a cyclic ordering in which at most `a` consecutive pairs are missing.

The proof adds the minimum required number of missing edges and applies the
standard (distinct-vertex) form of Ore's theorem.  The Bondy--Chvatal
development vendored for Erdős Problem 570 provides the closure machinery.
-/

open Finset

namespace Erdos76

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

attribute [local instance] Classical.propDecidable

private lemma missingEdgeCount_eq_compl_edgeSet_ncard_ham
    (G : SimpleGraph A) :
    missingEdgeCount G = Gᶜ.edgeSet.ncard := by
  let hs : Gᶜ.edgeSet.Finite := Set.toFinite _
  unfold missingEdgeCount
  rw [Set.ncard_eq_toFinset_card _ hs]
  congr 1
  ext e
  simp [SimpleGraph.mem_edgeFinset]

private theorem top_isHamiltonian_of_three_le_card
    (hA : 3 ≤ Fintype.card A) :
    (⊤ : SimpleGraph A).IsHamiltonian := by
  obtain ⟨r, hr⟩ : ∃ r, Fintype.card A = r + 3 :=
    ⟨Fintype.card A - 3, by omega⟩
  let e : Fin (r + 3) ≃ A := by
    simpa [hr] using (Fintype.equivFin A).symm
  let f : SimpleGraph.cycleGraph (r + 3) →g (⊤ : SimpleGraph A) :=
    ⟨fun x ↦ e x, fun {x y} hxy ↦ by
      simp only [SimpleGraph.top_adj, ne_eq]
      exact e.injective.ne hxy.ne⟩
  let p := (SimpleGraph.cycleGraph.cycle r).map f
  intro _
  refine ⟨f 0, p, ?_⟩
  rw [SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq]
  refine ⟨?_, ?_⟩
  · exact SimpleGraph.cycleGraph.isCycle_cycle.map e.injective
  · simp [p, hr]

/-- The usual form of Ore's theorem, whose degree-sum hypothesis is imposed
only on *distinct* nonadjacent vertices. -/
private theorem ore_theorem_distinct (G : SimpleGraph A)
    (hA : 3 ≤ Fintype.card A)
    (hdeg : ∀ {u v : A}, u ≠ v → ¬G.Adj u v →
      Fintype.card A ≤ G.degree u + G.degree v) :
    G.IsHamiltonian := by
  suffices G.closure = (⊤ : SimpleGraph A) from
    SimpleGraph.from_closure_iff.mp
      (this ▸ top_isHamiltonian_of_three_le_card hA)
  rw [eq_top_iff]
  intro u v huv
  simp only [SimpleGraph.top_adj, ne_eq] at huv
  by_cases hadj : G.Adj u v
  · exact SimpleGraph.self_le_closure G hadj
  · apply SimpleGraph.closure_spec G huv
    calc
      Fintype.card A ≤ G.degree u + G.degree v := hdeg huv hadj
      _ ≤ G.closure.degree u + G.closure.degree v :=
        add_le_add
          (G.degree_le_of_le (v := u) (SimpleGraph.self_le_closure G))
          (G.degree_le_of_le (v := v) (SimpleGraph.self_le_closure G))

/-- A graph with at most `|V| - 3` missing edges is Hamiltonian.  This is
the special sparse-complement consequence of Ore used in Corollary 2.5. -/
theorem isHamiltonian_of_missingEdgeCount_le_card_sub_three
    (G : SimpleGraph A) (hA : 3 ≤ Fintype.card A)
    (hmissing : missingEdgeCount G ≤ Fintype.card A - 3) :
    G.IsHamiltonian := by
  apply ore_theorem_distinct G hA
  intro u v huv hnonadj
  have hcompAdj : Gᶜ.Adj u v :=
    (SimpleGraph.compl_adj G u v).2 ⟨huv, hnonadj⟩
  let Iu : Finset (Sym2 A) := Gᶜ.incidenceFinset u
  let Iv : Finset (Sym2 A) := Gᶜ.incidenceFinset v
  have hinter : Iu ∩ Iv = {s(u, v)} := by
    ext e
    simpa only [Iu, Iv, Finset.mem_inter,
      SimpleGraph.mem_incidenceFinset, Finset.mem_singleton,
      Set.mem_inter_iff, Set.mem_singleton_iff] using
      Set.ext_iff.mp
        (Gᶜ.incidenceSet_inter_incidenceSet_of_adj hcompAdj) e
  have hunion : Iu ∪ Iv ⊆ Gᶜ.edgeFinset :=
    Finset.union_subset
      (Gᶜ.incidenceFinset_subset (v := u))
      (Gᶜ.incidenceFinset_subset (v := v))
  have hunionCard : (Iu ∪ Iv).card ≤ Gᶜ.edgeFinset.card :=
    Finset.card_le_card hunion
  have hcardFormula := Finset.card_union_add_card_inter Iu Iv
  rw [hinter, Finset.card_singleton] at hcardFormula
  have hIu : Iu.card = Gᶜ.degree u := by simp [Iu]
  have hIv : Iv.card = Gᶜ.degree v := by simp [Iv]
  have hcompSum : G.degree u + Gᶜ.degree u = Fintype.card A - 1 := by
    have hdlt := G.degree_lt_card_verts u
    have h := G.degree_compl (v := u)
    omega
  have hcompSum' : G.degree v + Gᶜ.degree v = Fintype.card A - 1 := by
    have hdlt := G.degree_lt_card_verts v
    have h := G.degree_compl (v := v)
    omega
  unfold missingEdgeCount at hmissing
  omega

/-- Corollary 2.5 in the precise edge-finset form needed by D5.  The returned
finset is the edge set of a spanning simple cycle: it has one edge per vertex,
at most `a` of its edges are absent from `G`, and exactly two of its edges are
incident with every vertex. -/
theorem exists_approximateHamiltonianCycle_edges
    (G : SimpleGraph A) (a : ℕ) (hA : 3 ≤ Fintype.card A)
    (hmissing : missingEdgeCount G ≤ Fintype.card A - 3 + a) :
    ∃ C : Finset (Sym2 A),
      C.card = Fintype.card A ∧
      (C.filter fun e ↦ e ∉ G.edgeSet).card ≤ a ∧
      ∀ v : A, (C.filter fun e ↦ v ∈ e).card = 2 := by
  classical
  let r : ℕ := missingEdgeCount G - (Fintype.card A - 3)
  have hrMissing : r ≤ Gᶜ.edgeFinset.card := by
    simp only [r, missingEdgeCount]
    omega
  obtain ⟨B, hBG, hBcard⟩ := Finset.exists_subset_card_eq hrMissing
  have hra : r ≤ a := by
    dsimp only [r]
    omega
  let K : SimpleGraph A :=
    G ⊔ SimpleGraph.fromEdgeSet (↑B : Set (Sym2 A))
  have hKcompl : Kᶜ = Gᶜ.deleteEdges (↑B : Set (Sym2 A)) := by
    ext x y
    simp only [K, SimpleGraph.compl_adj, SimpleGraph.sup_adj,
      SimpleGraph.fromEdgeSet_adj, SimpleGraph.deleteEdges_adj,
      Finset.mem_coe, not_or, not_and_or, not_not]
    tauto
  have hKmissing : missingEdgeCount K ≤ Fintype.card A - 3 := by
    have hBset : (↑B : Set (Sym2 A)) ⊆ Gᶜ.edgeSet := by
      intro e he
      exact SimpleGraph.mem_edgeFinset.mp (hBG (by simpa using he))
    rw [missingEdgeCount_eq_compl_edgeSet_ncard_ham]
    have hKedgeSet : Kᶜ.edgeSet = Gᶜ.edgeSet \ (↑B : Set (Sym2 A)) := by
      rw [hKcompl, SimpleGraph.edgeSet_deleteEdges]
    rw [hKedgeSet, Set.ncard_sdiff' hBset,
      Set.ncard_coe_finset, ← missingEdgeCount_eq_compl_edgeSet_ncard_ham,
      hBcard]
    dsimp only [r]
    omega
  have hKham : K.IsHamiltonian :=
    isHamiltonian_of_missingEdgeCount_le_card_sub_three K hA hKmissing
  obtain ⟨z, p, hp⟩ := hKham (by omega : Fintype.card A ≠ 1)
  let C : Finset (Sym2 A) := p.edges.toFinset
  refine ⟨C, ?_, ?_, ?_⟩
  · dsimp only [C]
    rw [List.toFinset_card_of_nodup hp.isCycle.isTrail.edges_nodup,
      SimpleGraph.Walk.length_edges]
    exact hp.length_eq
  · calc
      (C.filter fun e ↦ e ∉ G.edgeSet).card ≤ B.card := by
        apply Finset.card_le_card
        intro e he
        have heC : e ∈ C := (Finset.mem_filter.mp he).1
        have heG : e ∉ G.edgeSet := (Finset.mem_filter.mp he).2
        have hep : e ∈ p.edges := by
          simpa only [C, List.mem_toFinset] using heC
        have heK : e ∈ K.edgeSet := p.edges_subset_edgeSet hep
        change e ∈ (G ⊔ SimpleGraph.fromEdgeSet
          (↑B : Set (Sym2 A))).edgeSet at heK
        rw [SimpleGraph.edgeSet_sup, Set.mem_union] at heK
        have heAdd : e ∈ (SimpleGraph.fromEdgeSet
            (↑B : Set (Sym2 A))).edgeSet := heK.resolve_left heG
        rw [SimpleGraph.edgeSet_fromEdgeSet] at heAdd
        exact heAdd.1
      _ = r := hBcard
      _ ≤ a := hra
  · intro v
    let J : SimpleGraph A := p.toSubgraph.spanningCoe
    have hCJ : C = J.edgeFinset := by
      ext e
      change e ∈ p.edges.toFinset ↔ e ∈ J.edgeFinset
      rw [List.mem_toFinset]
      rw [SimpleGraph.mem_edgeFinset]
      change e ∈ p.edges ↔ e ∈ p.toSubgraph.edgeSet
      exact p.mem_edges_toSubgraph.symm
    rw [hCJ, ← J.incidenceFinset_eq_filter]
    rw [J.card_incidenceFinset_eq_degree]
    rw [← J.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard]
    change (p.toSubgraph.neighborSet v).ncard = 2
    exact hp.isCycle.ncard_neighborSet_toSubgraph_eq_two (hp.mem_support v)

end

end Erdos76
