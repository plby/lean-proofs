/-
Copyright (c) 2026 Brian Rabern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Rabern and Opus 5
-/

import ErdosProblems.Erdos1091.BrooksOddCycle
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import ErdosProblems.Erdos1091.BrooksVertexLemmas
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.Hall.Finite

/-!
# Brooks' theorem

This file develops Rabern's inductive proof of Brooks' theorem (maximal independent set deletion
and clique / odd-cycle surgery with path-extension colouring).

## The statement being proved

Following Rabern, the theorem is stated in the form

> if `χ(G) = Δ(G) + 1` then either `G` contains `K_{Δ(G)+1}`, or `Δ(G) = 2` and `G` contains an
> odd cycle.

## References

* L. Rabern, *Yet another proof of Brooks' theorem*, Discrete Math. **346** (2023), 113261.
  https://doi.org/10.1016/j.disc.2022.113261
  (primary source for the inductive argument formalized here)
* D. W. Cranston and L. Rabern, *Brooks' theorem and beyond*, J. Graph Theory **80** (2015),
  no. 3, 199–225. https://doi.org/10.1002/jgt.21847 · arXiv:1403.0479
  (survey; a referee of this paper asked that the short proof be made public)
* R. L. Brooks, *On colouring the nodes of a network*, Proc. Cambridge Philos. Soc. **37** (1941),
  194–197.

## Status

The inductive argument is complete: STEPs 1–11, low-degree deletion, the independent-set branch,
clique surgery (including the odd-cycle triangle `C_3`), longer-odd-cycle surgery (`C_5`, `C_7`, …)
via `Colorable.of_rabern_path_extension`, and the main theorem `brooks` are fully proved.
-/

set_option linter.style.longFile 2100

section

universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {n : ℕ}

/-! ### Auxiliary notions -/

/-- `K⁻ₙ₊₂`: the complete graph on `Fin (n + 2)` with the single edge `{0, 1}` removed.

So `K⁻_{k+1}` is `cliqueMinusEdge (k - 1)` for `k ≥ 3`. -/
def cliqueMinusEdge (n : ℕ) : SimpleGraph (Fin (n + 2)) :=
  (⊤ : SimpleGraph (Fin (n + 2))).deleteEdges {s(0, 1)}

lemma cliqueMinusEdge_le_top (n : ℕ) :
    cliqueMinusEdge n ≤ (⊤ : SimpleGraph (Fin (n + 2))) :=
  deleteEdges_le _

theorem cliqueFree_of_cliqueMinusEdge_free {k : ℕ}
    (h : ¬ cliqueMinusEdge k ⊑ G) : G.CliqueFree (k + 2) := by
  intro s hs
  exact h <| (IsContained.of_le (cliqueMinusEdge_le_top k)).trans <|
    not_cliqueFree_iff_top_isContained (k + 2) |>.1 fun hcf => hcf s hs

/-- An equivalence with `σ 0 = a` and `σ 1 = b`, assuming `a ≠ b`. -/
def finPlaceTwo {n : ℕ} (a b : Fin (n + 2)) (_hne : a ≠ b) : Fin (n + 2) ≃ Fin (n + 2) :=
  (Equiv.swap 0 a).trans (Equiv.swap (Equiv.swap 0 a 1) b)

lemma finPlaceTwo_zero {n : ℕ} (a b : Fin (n + 2)) (hne : a ≠ b) :
    finPlaceTwo a b hne 0 = a := by
  simp only [finPlaceTwo, Equiv.trans_apply, Equiv.swap_apply_left, Equiv.swap_apply_def]
  split_ifs <;> simp_all

lemma finPlaceTwo_one {n : ℕ} (a b : Fin (n + 2)) (hne : a ≠ b) :
    finPlaceTwo a b hne 1 = b := by
  simp [finPlaceTwo, Equiv.swap_apply_left]

/-! ### Ingredient lemmas -/

/-- STEP 1: the case `Δ(G) ≤ 2`. -/
theorem colorable_maxDegree_of_maxDegree_le_two [Fintype V] [DecidableRel G.Adj]
    (_h2 : G.maxDegree ≤ 2) (hcf : G.CliqueFree (G.maxDegree + 1))
    (hodd : G.maxDegree = 2 → ¬G.HasOddCycle) :
    G.Colorable G.maxDegree := by
  match hΔ : G.maxDegree with
  | 0 =>
    rw [hΔ] at hcf
    refine colorable_zero_iff.2 ?_
    by_contra hne
    rw [not_isEmpty_iff] at hne
    obtain ⟨v⟩ := hne
    exact hcf {v} ⟨by simp [isClique_iff], by simp⟩
  | 1 =>
    rw [hΔ, cliqueFree_two] at hcf
    exact colorable_one_iff.2 hcf
  | 2 =>
    exact colorable_two_iff_not_hasOddCycle.2 (hodd hΔ)
  | k + 3 =>
    lia

/-- STEP 3a: every finite graph has a maximal independent set. -/
theorem exists_maximal_isIndepSet (G : SimpleGraph V) [Finite V] :
    ∃ I : Set V, Maximal G.IsIndepSet I := by
  obtain ⟨s, hs⟩ := G.maximumIndepSet_exists
  exact ⟨↑s, hs.isMaximalIndepSet s⟩

/-- STEP 3b: a maximal independent set is dominating. -/
theorem Maximal.exists_adj_of_notMem {I : Set V} (hI : Maximal G.IsIndepSet I) {v : V}
    (hv : v ∉ I) : ∃ w ∈ I, G.Adj v w := by
  by_contra hcon
  push Not at hcon
  have hindep : G.IsIndepSet (insert v I) := by
    intro x hx y hy hxy
    simp only [Set.mem_insert_iff] at hx hy
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · exact absurd rfl hxy
      · exact hcon y hy
    · rcases hy with rfl | hy
      · exact fun hadj => hcon x hx hadj.symm
      · exact hI.1 hx hy hxy
  exact hv (hI.2 hindep (Set.subset_insert v I) (Set.mem_insert v I))

/-- STEP 3c: deleting a maximal independent set drops the maximum degree. -/
theorem maxDegree_induce_compl_lt_of_maximal [Fintype V] [DecidableRel G.Adj]
    {I : Set V} [DecidablePred (· ∈ I)] [Nonempty ↥(Iᶜ : Set V)]
    (hI : Maximal G.IsIndepSet I) :
    (G.induce (Iᶜ : Set V)).maxDegree < G.maxDegree := by
  classical
  obtain ⟨⟨v0, hv0⟩⟩ := ‹Nonempty ↥(Iᶜ : Set V)›
  obtain ⟨w0, _, hw0⟩ := Maximal.exists_adj_of_notMem hI (v := v0)
    (Set.notMem_of_mem_compl hv0)
  have hdeg0 : 0 < G.degree v0 := by
    rw [← card_neighborFinset_eq_degree, Finset.card_pos]
    exact ⟨w0, (G.mem_neighborFinset v0 w0).2 hw0⟩
  have hpos : 0 < G.maxDegree := lt_of_lt_of_le hdeg0 (G.degree_le_maxDegree v0)
  refine (maxDegree_le_of_forall_degree_le (G.induce (Iᶜ : Set V)) (G.maxDegree - 1)
    fun v => ?_).trans_lt (Nat.sub_lt hpos Nat.zero_lt_one)
  obtain ⟨w, hwI, hwadj⟩ := Maximal.exists_adj_of_notMem hI (v := ↑v)
    (Set.notMem_of_mem_compl v.property)
  have hsubset :
      ((G.induce (Iᶜ : Set V)).neighborFinset v).map (.subtype (· ∈ (Iᶜ : Set V))) ⊆
        (G.neighborFinset ↑v).erase w := by
    intro x hx
    rcases Finset.mem_map.1 hx with ⟨a, ha, rfl⟩
    have ha' : G.Adj ↑v ↑a := by simpa [mem_neighborFinset, comap_adj] using ha
    have hne : ↑a ≠ w := fun h =>
      Set.notMem_of_mem_compl (h ▸ a.property : w ∈ Iᶜ) hwI
    exact Finset.mem_erase.2 ⟨hne, (G.mem_neighborFinset _ _).2 ha'⟩
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_map, card_neighborFinset_eq_degree] at hcard
  have herase :
      ((G.neighborFinset ↑v).erase w).card + 1 = G.degree ↑v := by
    rw [Finset.card_erase_add_one ((G.mem_neighborFinset _ _).2 hwadj),
      card_neighborFinset_eq_degree]
  have := G.degree_le_maxDegree (↑v)
  omega

/-- STEP 4: deleting an independent set costs at most one color. -/
theorem Colorable.of_induce_compl_isIndepSet {I : Set V} (hI : G.IsIndepSet I)
    (h : (G.induce (Iᶜ : Set V)).Colorable n) :
    G.Colorable (n + 1) := by
  obtain ⟨C⟩ := h
  classical
  let color : V → Fin (n + 1) := fun v =>
    if hv : v ∈ I then Fin.last n
    else Fin.castSucc (C ⟨v, Set.mem_compl hv⟩)
  refine ⟨Coloring.mk color fun {x y} hxy => ?_⟩
  dsimp [color]
  by_cases hx : x ∈ I <;> by_cases hy : y ∈ I
  · exact absurd hxy (hI hx hy hxy.ne)
  · simp [hx, hy, Fin.ne_of_gt (Fin.castSucc_lt_last _)]
  · simp [hx, hy, Fin.ne_of_lt (Fin.castSucc_lt_last _)]
  · have hxy' : (G.induce (Iᶜ : Set V)).Adj ⟨x, Set.mem_compl hx⟩ ⟨y, Set.mem_compl hy⟩ := hxy
    simp only [hx, hy, ↓reduceDIte]
    exact Fin.castSucc_inj.ne.mpr (C.valid hxy')

/-- STEP 5: if no vertex has degree below `Δ`, the graph is `Δ`-regular. -/
theorem isRegularOfDegree_maxDegree_of_forall_le [Fintype V] [DecidableRel G.Adj]
    (h : ∀ v, G.maxDegree ≤ G.degree v) :
    G.IsRegularOfDegree G.maxDegree :=
  fun v => le_antisymm (G.degree_le_maxDegree v) (h v)

/-- STEP 6: in a `k`-regular `G` with `1 ≤ k`, a vertex of a `(k-1)`-regular induced subgraph
`Q ⊆ Iᶜ` has exactly one neighbor in `I`. -/
theorem existsUnique_adj_mem_of_isRegular [Fintype V] [DecidableRel G.Adj] {k : ℕ}
    (hk : 1 ≤ k) (hG : G.IsRegularOfDegree k) {I Q : Set V} (hI : Maximal G.IsIndepSet I)
    (hQI : Q ⊆ Iᶜ) [DecidablePred (· ∈ Q)] [DecidablePred (· ∈ I)]
    (hQ : (G.induce Q).IsRegularOfDegree (k - 1)) (v : V) (hv : v ∈ Q) :
    ∃! w, w ∈ I ∧ G.Adj v w := by
  classical
  have hdegQ : (G.induce Q).degree ⟨v, hv⟩ = k - 1 := hQ _
  have hinter : (G.neighborFinset v ∩ Q.toFinset).card = k - 1 := by
    have hmap := congrArg Finset.card (G.map_neighborFinset_induce (s := Q) ⟨v, hv⟩)
    simpa [card_neighborFinset_eq_degree, hdegQ] using hmap.symm
  have hsum :
      (G.neighborFinset v ∩ Q.toFinset).card + (G.neighborFinset v \ Q.toFinset).card =
        G.degree v := by
    rw [← card_neighborFinset_eq_degree, add_comm, Finset.card_sdiff_add_card_inter]
  have hout : (G.neighborFinset v \ Q.toFinset).card = 1 := by
    have hdeg := hG v
    omega
  obtain ⟨w, hw⟩ := Finset.card_eq_one.1 hout
  have hwmem : w ∈ G.neighborFinset v \ Q.toFinset := by simp [hw]
  have hwAdj : G.Adj v w := (G.mem_neighborFinset _ _).1 (Finset.mem_sdiff.1 hwmem).1
  have hwI : w ∈ I := by
    obtain ⟨w', hw'I, hw'Adj⟩ := Maximal.exists_adj_of_notMem hI (v := v)
      (Set.notMem_of_mem_compl (hQI hv))
    have hw'out : w' ∈ G.neighborFinset v \ Q.toFinset := by
      refine Finset.mem_sdiff.2 ⟨(G.mem_neighborFinset _ _).2 hw'Adj, ?_⟩
      simp only [Set.mem_toFinset]
      exact fun hq => absurd hw'I (Set.notMem_of_mem_compl (hQI hq))
    have : w' = w := by rw [hw] at hw'out; simpa using hw'out
    rwa [← this]
  refine ⟨w, ⟨hwI, hwAdj⟩, ?_⟩
  intro w' ⟨hw'I, hw'Adj⟩
  have hw'out : w' ∈ G.neighborFinset v \ Q.toFinset := by
    refine Finset.mem_sdiff.2 ⟨(G.mem_neighborFinset _ _).2 hw'Adj, ?_⟩
    simp only [Set.mem_toFinset]
    exact fun hq => absurd hw'I (Set.notMem_of_mem_compl (hQI hq))
  rw [hw] at hw'out
  simpa using hw'out

/-- STEP 7: on a connected graph, a non-constant labelling has an edge with distinct labels. -/
theorem Connected.exists_adj_ne_of_ne {β : Type*} (hG : G.Connected) (f : V → β) {a b : V}
    (hab : f a ≠ f b) :
    ∃ u v, G.Adj u v ∧ f u ≠ f v := by
  obtain ⟨p⟩ := hG a b
  induction p with
  | nil => exact (hab rfl).elim
  | @cons u v w h q ih =>
    by_cases hf : f u = f v
    · exact ih (hf ▸ hab)
    · exact ⟨u, v, h, hf⟩

/-- STEP 8a: a complete graph has a Hamiltonian path between any two distinct vertices. -/
theorem exists_isHamiltonian_walk_top [Fintype V] [DecidableEq V] {y z : V} (hyz : y ≠ z) :
    ∃ p : (⊤ : SimpleGraph V).Walk y z, p.IsHamiltonian := by
  classical
  have key : ∀ (s : Finset V) (a b : V), a ≠ b → a ∉ s → b ∉ s →
      ∃ p : (⊤ : SimpleGraph V).Walk a b,
        p.IsPath ∧ p.support.toFinset = insert a (insert b s) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro a b hab _ _
      refine ⟨Walk.cons ((top_adj a b).2 hab) Walk.nil, ?_, ?_⟩
      · exact (Walk.cons_isPath_iff _ _).2 ⟨Walk.IsPath.nil, by simp [hab]⟩
      · simp
    | insert x s hx ih =>
      intro a b hab ha hb
      have hxa : x ≠ a := fun h => ha (h ▸ Finset.mem_insert_self _ _)
      have hxb : x ≠ b := fun h => hb (h ▸ Finset.mem_insert_self _ _)
      have has : a ∉ s := fun h => ha (Finset.mem_insert_of_mem h)
      have hbs : b ∉ s := fun h => hb (Finset.mem_insert_of_mem h)
      obtain ⟨p, hp, hsup⟩ := ih x b hxb (by simp [hx]) hbs
      have hadj : (⊤ : SimpleGraph V).Adj a x := (top_adj a x).2 hxa.symm
      refine ⟨Walk.cons hadj p, (Walk.cons_isPath_iff _ _).2 ⟨hp, ?_⟩, ?_⟩
      · intro hmem
        have : a ∈ p.support.toFinset := List.mem_toFinset.2 hmem
        rw [hsup] at this
        simp only [Finset.mem_insert] at this
        rcases this with rfl | h
        · exact hxa rfl
        · rcases h with rfl | hin
          · exact hab rfl
          · exact has hin
      · simp only [Walk.support_cons, List.toFinset_cons, hsup]
        ext; simp; tauto
  obtain ⟨p, hp, hsup⟩ := key ((Finset.univ.erase y).erase z) y z hyz (by simp) (by simp)
  refine ⟨p, hp.isHamiltonian_of_mem fun w => List.mem_toFinset.1 ?_⟩
  rw [hsup]
  simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_univ]
  tauto

theorem exists_isHamiltonian_walk_of_isCycle_snd [DecidableEq V] {y : V} {c : G.Walk y y}
    (hc : c.IsCycle) (hspan : ∀ t, t ∈ c.support) :
    ∃ p : G.Walk y c.snd, p.IsHamiltonian := by
  have hnil : ¬c.Nil := hc.not_nil
  have hadj := c.adj_snd hnil
  have hsupp : c.support = y :: c.tail.support := by
    conv_lhs => rw [← c.cons_tail_eq hnil]
    simp [Walk.support_cons]
  have hc' : (Walk.cons hadj c.tail).IsCycle := by rwa [c.cons_tail_eq hnil]
  obtain ⟨hp, _⟩ := (Walk.cons_isCycle_iff c.tail hadj).1 hc'
  refine ⟨c.tail.reverse, Walk.IsPath.isHamiltonian_of_mem
    ((Walk.isPath_reverse_iff _).2 hp) fun t => ?_⟩
  have ht := hspan t
  rw [hsupp, List.mem_cons] at ht
  simp only [Walk.support_reverse, List.mem_reverse]
  exact ht.elim (fun h => h ▸ c.tail.end_mem_support) id

/-- STEP 8b: a spanning cycle yields a Hamiltonian path between the endpoints of any cycle edge. -/
theorem exists_isHamiltonian_walk_of_isCycle [DecidableEq V] {y : V} {c : G.Walk y y}
    (hc : c.IsCycle) (hspan : ∀ t, t ∈ c.support) {z : V}
    (hz_edge : s(y, z) ∈ c.edges) :
    ∃ p : G.Walk y z, p.IsHamiltonian := by
  have hnil : ¬c.Nil := hc.not_nil
  have hadj := c.adj_snd hnil
  have hedges : c.edges = s(y, c.snd) :: c.tail.edges := by
    conv_lhs => rw [← c.cons_tail_eq hnil]
    simp [Walk.edges_cons]
  by_cases hz : z = c.snd
  · exact hz ▸ exists_isHamiltonian_walk_of_isCycle_snd hc hspan
  · have hmem : s(y, z) ∈ c.tail.edges := by
      rw [hedges, List.mem_cons] at hz_edge
      exact hz_edge.resolve_left fun hEq => by
        cases Sym2.eq_iff.mp hEq with
        | inl h => exact hz h.2
        | inr h => exact hadj.ne h.1
    have hc' : (Walk.cons hadj c.tail).IsCycle := by rwa [c.cons_tail_eq hnil]
    have hp : c.tail.IsPath := ((Walk.cons_isCycle_iff c.tail hadj).1 hc').1
    have hzpen : z = c.penultimate := by
      have h := hp.eq_penultimate_of_mem_edges hmem
      cases c with
      | nil => exact (hnil Walk.nil_nil).elim
      | cons hadj' p =>
        have hc'' : (Walk.cons hadj' p).IsCycle := hc
        have hpnnil : ¬p.Nil := Walk.not_nil_of_isCycle_cons hc''
        have h' : z = p.penultimate := by simpa using h
        exact h'.trans (Walk.penultimate_cons_of_not_nil hadj' p hpnnil).symm
    have hzR : z = c.reverse.snd := hzpen.trans (Walk.snd_reverse c).symm
    have hspanR : ∀ t, t ∈ c.reverse.support := fun t => by simp [hspan t]
    exact hzR ▸ exists_isHamiltonian_walk_of_isCycle_snd hc.reverse hspanR

/-- STEP 9: adding one edge raises the maximum degree by at most one. -/
theorem degree_sup_edge_le [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (u w v : V) :
    (G ⊔ edge u w).degree v ≤ G.degree v + 1 := by
  classical
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree, neighborFinset_sup]
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add_left ?_ _)
  refine Finset.card_le_one.2 fun a ha b hb => ?_
  have ha' : (edge u w).Adj v a := (mem_neighborFinset _ _ _).1 ha
  have hb' : (edge u w).Adj v b := (mem_neighborFinset _ _ _).1 hb
  simp only [edge_adj] at ha' hb'
  aesop

theorem maxDegree_sup_edge_le [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (u w : V) :
    (G ⊔ edge u w).maxDegree ≤ G.maxDegree + 1 := by
  classical
  exact maxDegree_le_of_forall_degree_le _ _ fun v =>
    (degree_sup_edge_le (G := G) u w v).trans (Nat.succ_le_succ (G.degree_le_maxDegree v))

/-- STEP 10: if `G` has no `K⁻_{k+2}`, then adding one edge cannot create a `K_{k+2}`. -/
theorem cliqueFree_sup_edge_of_cliqueMinusEdge_free {k : ℕ} (u w : V)
    (h : ¬ cliqueMinusEdge k ⊑ G) :
    (G ⊔ edge u w).CliqueFree (k + 2) := by
  classical
  have hcf : G.CliqueFree (k + 2) := cliqueFree_of_cliqueMinusEdge_free h
  by_cases hne : u = w
  · subst hne; simpa [sup_edge_self] using hcf
  by_cases hadj : G.Adj u w
  · simpa [sup_edge_of_adj G hadj] using hcf
  intro s hs
  have hu : u ∈ s := hcf.mem_of_sup_edge_isNClique hs
  have hw : w ∈ s := by
    have hs' : (G ⊔ edge w u).IsNClique (k + 2) s := by rwa [edge_comm]
    exact hcf.mem_of_sup_edge_isNClique hs'
  let e : Fin (k + 2) ≃ ↥s := (Finset.equivFinOfCardEq (s := s) hs.card_eq).symm
  let a : Fin (k + 2) := e.symm ⟨u, hu⟩
  let b : Fin (k + 2) := e.symm ⟨w, hw⟩
  have hab : a ≠ b := fun hEq => hne (by
    have := congrArg (fun i => (e i : V)) hEq
    simpa [a, b] using this)
  let σ := finPlaceTwo a b hab
  have hσ0 : σ 0 = a := finPlaceTwo_zero a b hab
  have hσ1 : σ 1 = b := finPlaceTwo_one a b hab
  let f : Fin (k + 2) → V := fun i => ↑(e (σ i))
  have hinj : Function.Injective f := by
    intro x y hxy
    exact σ.injective (e.injective (Subtype.ext hxy))
  have hf0 : f 0 = u := by simp [f, hσ0, a]
  have hf1 : f 1 = w := by simp [f, hσ1, b]
  have hhom : ∀ {x y : Fin (k + 2)}, (cliqueMinusEdge k).Adj x y → G.Adj (f x) (f y) := by
    intro x y hxy
    have hxy' : x ≠ y ∧ s(x, y) ≠ s(0, 1) := by
      simpa [cliqueMinusEdge, deleteEdges_adj, top_adj] using hxy
    have hadjSup : (G ⊔ edge u w).Adj (f x) (f y) := by
      refine hs.isClique (e (σ x)).property (e (σ y)).property ?_
      exact fun hEq => hxy'.1 (hinj hEq)
    rw [sup_adj, edge_adj] at hadjSup
    rcases hadjSup with hG | ⟨hpair, _⟩
    · exact hG
    · have : s(f x, f y) = s(u, w) := by
        rcases hpair with ⟨hxu, hyw⟩ | ⟨hxw, hyu⟩
        · simp [hxu, hyw]
        · rw [hxw, hyu, Sym2.eq_swap]
      have hmap : Sym2.map f s(x, y) = Sym2.map f s(0, 1) := by
        simpa [Sym2.map_mk, hf0, hf1] using this
      have hinj2 : Function.Injective (Sym2.map f) := Sym2.map.injective hinj
      exact absurd (hinj2 hmap) hxy'.2
  exact absurd ⟨Hom.toCopy ⟨f, fun {_ _} => hhom⟩ hinj⟩ h

private theorem neighborFinset_inter_subset_inter_union
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (v : V) (s t : Finset V) :
    G.neighborFinset v ∩ s ⊆ G.neighborFinset v ∩ (s ∪ t) := by
  intro x hx
  exact Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hx).1,
    Finset.mem_union_left _ (Finset.mem_inter.1 hx).2⟩

/-- STEP 11: extend a coloring greedily along a path. -/
theorem Colorable.of_induce_union_support [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {s : Finset V} {y z : V} (p : G.Walk y z) (hp : p.IsPath)
    (hcol : (G.induce (↑s : Set V)).Colorable n)
    (hfree : ∀ v ∈ p.support, (G.neighborFinset v ∩ (s ∪ p.support.toFinset)).card < n) :
    (G.induce (↑(s ∪ p.support.toFinset) : Set V)).Colorable n := by
  classical
  induction p generalizing s with
  | @nil u =>
    have hsets : s ∪ (Walk.nil : G.Walk u u).support.toFinset = insert u s := by
      ext x; simp [Walk.support_nil]
    have hgoal : (G.induce (↑(insert u s) : Set V)).Colorable n := by
      by_cases hu : u ∈ s
      · have : insert u s = s := Finset.insert_eq_of_mem hu
        rwa [this]
      · refine Colorable.of_induce_insert hcol ?_
        have hfu : (G.neighborFinset u ∩ (s ∪ {u})).card < n := by
          simpa [Walk.support_nil] using hfree u (by simp [Walk.support_nil])
        exact lt_of_le_of_lt
          (Finset.card_le_card (neighborFinset_inter_subset_inter_union u s {u})) hfu
    exact hsets ▸ hgoal
  | @cons u v w h q ih =>
    have hpq : q.IsPath := ((Walk.cons_isPath_iff h q).1 hp).1
    have hcol_u : (G.induce (↑(insert u s) : Set V)).Colorable n := by
      by_cases hu : u ∈ s
      · have : insert u s = s := Finset.insert_eq_of_mem hu
        rwa [this]
      · refine Colorable.of_induce_insert hcol ?_
        have hfu := hfree u (by simp [Walk.support_cons])
        exact lt_of_le_of_lt
          (Finset.card_le_card
            (neighborFinset_inter_subset_inter_union u s (Walk.cons h q).support.toFinset)) hfu
    have hfree_q : ∀ x ∈ q.support,
        (G.neighborFinset x ∩ (insert u s ∪ q.support.toFinset)).card < n := by
      intro x hx
      have hx' : x ∈ (Walk.cons h q).support := by simp [Walk.support_cons, hx]
      have := hfree x hx'
      refine lt_of_le_of_lt (Finset.card_le_card ?_) this
      intro y hy
      have hy1 := (Finset.mem_inter.1 hy).1
      have hy2 := (Finset.mem_inter.1 hy).2
      refine Finset.mem_inter.2 ⟨hy1, ?_⟩
      simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, Walk.support_cons,
        List.mem_cons] at hy2 ⊢
      tauto
    have hsets : s ∪ (Walk.cons h q).support.toFinset = insert u s ∪ q.support.toFinset := by
      ext x
      simp only [Walk.support_cons, List.toFinset_cons, Finset.mem_union, Finset.mem_insert,
        List.mem_toFinset]
      tauto
    exact hsets ▸ ih (s := insert u s) hpq hcol_u hfree_q

/-- Same as `of_induce_insert_color`, but returns the colouring and records that old colours on
`s` are preserved and the new vertex gets colour `a`. Assumes `v ∉ s`. -/
theorem exists_coloring_induce_insert_color [DecidableEq V] {s : Finset V} {v : V} {a : Fin n}
    (hv : v ∉ s)
    (C : (G.induce (↑s : Set V)).Coloring (Fin n))
    (ha : ∀ (w : V) (hw : w ∈ s), G.Adj v w → C ⟨w, hw⟩ ≠ a) :
    ∃ C' : (G.induce (↑(insert v s) : Set V)).Coloring (Fin n),
      C' ⟨v, Finset.mem_insert_self v s⟩ = a ∧
        ∀ (u : V) (hu : u ∈ s),
          C' ⟨u, Finset.mem_insert_of_mem hu⟩ = C ⟨u, hu⟩ := by
  classical
  let f : V → Fin n := fun u => if hu : u ∈ s then C ⟨u, hu⟩ else a
  have hf : ∀ (u : V) (hu : u ∈ s), f u = C ⟨u, hu⟩ := fun _ hu => dif_pos hu
  have hfree : ∀ w, G.Adj v w → w ∈ s → f w ≠ a := fun w hw hws hc =>
    ha w hws hw (hf w hws ▸ hc)
  let C' : (G.induce (↑(insert v s) : Set V)).Coloring (Fin n) :=
    Coloring.mk (fun u => if u.1 = v then a else f u.1) <| by
      rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
      have hadj : G.Adj x y := hxy
      rcases eq_or_ne x v with hxv | hxv
      · rcases eq_or_ne y v with hyv | hyv
        · exact absurd (hxv.trans hyv.symm) hadj.ne
        · rw [if_pos hxv, if_neg hyv]
          exact (hfree y (hxv ▸ hadj) (hy.resolve_left hyv)).symm
      · rcases eq_or_ne y v with hyv | hyv
        · rw [if_neg hxv, if_pos hyv]
          exact hfree x (hyv ▸ hadj.symm) (hx.resolve_left hxv)
        · rw [if_neg hxv, if_neg hyv, hf x (hx.resolve_left hxv), hf y (hy.resolve_left hyv)]
          exact C.valid hadj
  refine ⟨C', ?_, fun u hu => ?_⟩
  · change (if (v : V) = v then a else f v) = a
    simp
  · have hne : u ≠ v := fun h => hv (h ▸ hu)
    change (if (u : V) = v then a else f u) = C ⟨u, hu⟩
    rw [if_neg hne, hf u hu]

/-- Greedy step with a prescribed free colour (needed when two neighbours share a colour). -/
theorem Colorable.of_induce_insert_color [DecidableEq V] {s : Finset V} {v : V} {a : Fin n}
    (C : (G.induce (↑s : Set V)).Coloring (Fin n))
    (ha : ∀ (w : V) (hw : w ∈ s), G.Adj v w → C ⟨w, hw⟩ ≠ a) :
    (G.induce (↑(insert v s) : Set V)).Colorable n := by
  classical
  by_cases hv : v ∈ s
  · rw [Finset.insert_eq_of_mem hv]
    exact ⟨C⟩
  · obtain ⟨C', _, _⟩ := exists_coloring_induce_insert_color hv C ha
    exact ⟨C'⟩

/-- Same as `of_induce_insert`, returning the colouring with old colours preserved. Assumes `v ∉ s`. -/
theorem exists_coloring_induce_insert [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {s : Finset V} {v : V} [NeZero n]
    (hv : v ∉ s)
    (C : (G.induce (↑s : Set V)).Coloring (Fin n))
    (hlt : (G.neighborFinset v ∩ s).card < n) :
    ∃ C' : (G.induce (↑(insert v s) : Set V)).Coloring (Fin n),
      ∀ (u : V) (hu : u ∈ s),
        C' ⟨u, Finset.mem_insert_of_mem hu⟩ = C ⟨u, hu⟩ := by
  classical
  let f : V → Fin n := fun u => if hu : u ∈ s then C ⟨u, hu⟩ else 0
  obtain ⟨a, ha⟩ : ∃ a, a ∉ (G.neighborFinset v ∩ s).image f := by
    have hcard : ((G.neighborFinset v ∩ s).image f).card < n :=
      lt_of_le_of_lt Finset.card_image_le hlt
    obtain ⟨a, ha⟩ : (((G.neighborFinset v ∩ s).image f)ᶜ).Nonempty := by
      rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]; lia
    exact ⟨a, Finset.mem_compl.1 ha⟩
  have hfree : ∀ (w : V) (hw : w ∈ s), G.Adj v w → C ⟨w, hw⟩ ≠ a := fun w hw hadj hEq => by
    have hf : f w = C ⟨w, hw⟩ := dif_pos hw
    have him : f w ∈ (G.neighborFinset v ∩ s).image f :=
      Finset.mem_image_of_mem f (Finset.mem_inter.2 ⟨(mem_neighborFinset _ _ _).2 hadj, hw⟩)
    exact ha (by rwa [hf, hEq] at him)
  obtain ⟨C', _, hpres⟩ := exists_coloring_induce_insert_color hv C hfree
  exact ⟨C', hpres⟩

/-- Greedy step when the already-coloured neighbours use fewer than `n` colours. -/
theorem Colorable.of_induce_insert_image [Fintype V] [DecidableRel G.Adj]
    [DecidableEq V] {s : Finset V} {v : V} [NeZero n]
    (C : (G.induce (↑s : Set V)).Coloring (Fin n))
    (hlt : (((G.neighborFinset v ∩ s).image fun w =>
        if hw : w ∈ s then (C ⟨w, hw⟩ : Fin n) else 0) : Finset (Fin n)).card < n) :
    (G.induce (↑(insert v s) : Set V)).Colorable n := by
  classical
  let f : V → Fin n := fun w => if hw : w ∈ s then C ⟨w, hw⟩ else 0
  obtain ⟨a, ha⟩ : ∃ a : Fin n, a ∉ (G.neighborFinset v ∩ s).image f := by
    have hcard : ((G.neighborFinset v ∩ s).image f).card < n := by simpa [f] using hlt
    obtain ⟨a, ha⟩ : (((G.neighborFinset v ∩ s).image f)ᶜ).Nonempty := by
      rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]; lia
    exact ⟨a, Finset.mem_compl.1 ha⟩
  exact Colorable.of_induce_insert_color (C := C) (a := a) fun w hw hadj hEq => by
    have hf : f w = C ⟨w, hw⟩ := dif_pos hw
    have : f w ∈ (G.neighborFinset v ∩ s).image f :=
      Finset.mem_image_of_mem f (Finset.mem_inter.2 ⟨(mem_neighborFinset _ _ _).2 hadj, hw⟩)
    exact ha (by rwa [hf, hEq] at this)

/-! ### The `K⁻` extension (STEP 2) -/

section CliqueMinusEdgeColorable
open Classical

lemma neighborFinset_cliqueMinusEdge_zero (n : ℕ) :
    (cliqueMinusEdge n).neighborFinset (0 : Fin (n + 2)) = (Finset.univ.erase 0).erase 1 := by
  apply Finset.ext
  intro i
  constructor
  · intro hi
    have hadj : (cliqueMinusEdge n).Adj 0 i := (mem_neighborFinset _ _ _).1 hi
    have h := deleteEdges_adj.1 hadj
    have hine : i ≠ 0 := h.1.ne'
    have hine01 : s((0 : Fin (n + 2)), i) ≠ s(0, 1) := by
      simpa [Set.mem_singleton_iff] using h.2
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_erase.2 ⟨hine, Finset.mem_univ _⟩⟩
    intro h1; exact hine01 (h1 ▸ rfl)
  · intro hi
    have hi1 : i ≠ 1 := (Finset.mem_erase.1 hi).1
    have hi0 : i ≠ 0 := (Finset.mem_erase.1 (Finset.mem_erase.1 hi).2).1
    apply (mem_neighborFinset _ _ _).2
    refine deleteEdges_adj.2 ⟨(top_adj 0 i).2 hi0.symm, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hEq
    rcases Sym2.eq_iff.mp hEq with ⟨_, rfl⟩ | ⟨h01, _⟩
    · exact hi1 rfl
    · exact Fin.zero_ne_one h01

lemma degree_cliqueMinusEdge_zero (n : ℕ) :
    (cliqueMinusEdge n).degree (0 : Fin (n + 2)) = n := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_cliqueMinusEdge_zero,
    Finset.card_erase_of_mem (by simp [Fin.zero_ne_one.symm]),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  omega

lemma neighborFinset_cliqueMinusEdge_one (n : ℕ) :
    (cliqueMinusEdge n).neighborFinset (1 : Fin (n + 2)) = (Finset.univ.erase 0).erase 1 := by
  apply Finset.ext
  intro i
  constructor
  · intro hi
    have hadj : (cliqueMinusEdge n).Adj 1 i := (mem_neighborFinset _ _ _).1 hi
    have h := deleteEdges_adj.1 hadj
    have hine : i ≠ 1 := h.1.ne'
    have hine01 : s((1 : Fin (n + 2)), i) ≠ s(0, 1) := by
      simpa [Set.mem_singleton_iff] using h.2
    refine Finset.mem_erase.2 ⟨hine, Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩⟩
    intro h0; subst h0; exact hine01 (by rw [Sym2.eq_swap])
  · intro hi
    have hi1 : i ≠ 1 := (Finset.mem_erase.1 hi).1
    have hi0 : i ≠ 0 := (Finset.mem_erase.1 (Finset.mem_erase.1 hi).2).1
    apply (mem_neighborFinset _ _ _).2
    refine deleteEdges_adj.2 ⟨(top_adj 1 i).2 hi1.symm, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hEq
    rcases Sym2.eq_iff.mp hEq with ⟨h10, _⟩ | ⟨_, hi0'⟩
    · exact Fin.zero_ne_one h10.symm
    · exact hi0 hi0'

lemma degree_cliqueMinusEdge_one (n : ℕ) :
    (cliqueMinusEdge n).degree (1 : Fin (n + 2)) = n := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_cliqueMinusEdge_one,
    Finset.card_erase_of_mem (by simp [Fin.zero_ne_one.symm]),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  omega

lemma degree_cliqueMinusEdge_of_ne_zero_one {n : ℕ} {i : Fin (n + 2)}
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) :
    (cliqueMinusEdge n).degree i = n + 1 := by
  rw [← card_neighborFinset_eq_degree]
  have hset : (cliqueMinusEdge n).neighborFinset i = Finset.univ.erase i := by
    apply Finset.ext
    intro j
    constructor
    · intro hj
      exact Finset.mem_erase.2 ⟨((mem_neighborFinset _ _ _).1 hj).ne', Finset.mem_univ _⟩
    · intro hj
      have hji : j ≠ i := (Finset.mem_erase.1 hj).1
      apply (mem_neighborFinset _ _ _).2
      refine deleteEdges_adj.2 ⟨(top_adj i j).2 hji.symm, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro hEq
      rcases Sym2.eq_iff.mp hEq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hi0 rfl
      · exact hi1 rfl
  rw [hset, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  omega

lemma map_neighborFinset_cliqueMinusEdge_subset
    {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj] {n : ℕ}
    (φ : Copy (cliqueMinusEdge n) G) (a : Fin (n + 2)) :
    ((cliqueMinusEdge n).neighborFinset a).map φ.toEmbedding ⊆
      G.neighborFinset (φ a) ∩ (Set.range φ).toFinset := by
  intro x hx
  rcases Finset.mem_map.1 hx with ⟨i, hi, rfl⟩
  refine Finset.mem_inter.2 ⟨?_, ?_⟩
  · exact (mem_neighborFinset _ _ _).2 (φ.toHom.map_adj ((mem_neighborFinset _ _ _).1 hi))
  · exact Set.mem_toFinset.2 ⟨i, rfl⟩

lemma card_neighborFinset_sdiff_range_cliqueMinusEdge_le
    {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    {n : ℕ} (hΔ : G.maxDegree ≤ n + 1) (φ : Copy (cliqueMinusEdge n) G)
    (a : Fin (n + 2)) (hdegH : (cliqueMinusEdge n).degree a = n) :
    (G.neighborFinset (φ a) \ (Set.range φ).toFinset).card ≤ 1 := by
  have hge : n ≤ (G.neighborFinset (φ a) ∩ (Set.range φ).toFinset).card := by
    have := Finset.card_le_card (map_neighborFinset_cliqueMinusEdge_subset φ a)
    rwa [Finset.card_map, card_neighborFinset_eq_degree, hdegH] at this
  have hsum :
      (G.neighborFinset (φ a) ∩ (Set.range φ).toFinset).card +
        (G.neighborFinset (φ a) \ (Set.range φ).toFinset).card =
        G.degree (φ a) := by
    rw [← card_neighborFinset_eq_degree, add_comm, Finset.card_sdiff_add_card_inter]
  have hdegG := (G.degree_le_maxDegree (φ a)).trans hΔ
  omega

lemma neighborFinset_subset_range_of_degree_cliqueMinusEdge
    {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    {n : ℕ} (hΔ : G.maxDegree ≤ n + 1) (φ : Copy (cliqueMinusEdge n) G)
    {i : Fin (n + 2)} (hdegH : (cliqueMinusEdge n).degree i = n + 1) :
    G.neighborFinset (φ i) ⊆ (Set.range φ).toFinset := by
  intro w hw
  by_contra hwn
  have hge : n + 1 ≤ (G.neighborFinset (φ i) ∩ (Set.range φ).toFinset).card := by
    have := Finset.card_le_card (map_neighborFinset_cliqueMinusEdge_subset φ i)
    rwa [Finset.card_map, card_neighborFinset_eq_degree, hdegH] at this
  have hsum :
      (G.neighborFinset (φ i) ∩ (Set.range φ).toFinset).card +
        (G.neighborFinset (φ i) \ (Set.range φ).toFinset).card =
        G.degree (φ i) := by
    rw [← card_neighborFinset_eq_degree, add_comm, Finset.card_sdiff_add_card_inter]
  have hdegG := (G.degree_le_maxDegree (φ i)).trans hΔ
  have hpos : (G.neighborFinset (φ i) \ (Set.range φ).toFinset).card ≥ 1 :=
    Finset.one_le_card.2 ⟨w, Finset.mem_sdiff.2 ⟨hw, hwn⟩⟩
  omega

private lemma not_adj_ends_of_cliqueMinusEdge_copy
    {V : Type u} {G : SimpleGraph V} {n : ℕ} (hcf : G.CliqueFree (n + 1))
    (hn : 1 ≤ n) (φ : Copy (cliqueMinusEdge (n - 1)) G) :
    ¬ G.Adj (φ 0) (φ 1) := by
  intro hadj
  have hsz : n - 1 + 2 = n + 1 := by omega
  have htop : (⊤ : SimpleGraph (Fin (n - 1 + 2))) ⊑ G := by
    refine ⟨Hom.toCopy ⟨φ, fun {a b} hab => ?_⟩ φ.injective⟩
    by_cases hab01 : s(a, b) = s((0 : Fin (n - 1 + 2)), 1)
    · have hφ : s(φ a, φ b) = s(φ 0, φ 1) := by
        rcases Sym2.eq_iff.mp hab01 with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · simp [ha, hb]
        · simp [ha, hb, Sym2.eq_swap]
      rcases Sym2.eq_iff.mp hφ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h1 ▸ h2 ▸ hadj
      · exact h1 ▸ h2 ▸ hadj.symm
    · exact φ.toHom.map_adj <| by
        simp only [cliqueMinusEdge, deleteEdges_adj, top_adj, Set.mem_singleton_iff]
        exact ⟨hab.ne, hab01⟩
  exact (not_cliqueFree_iff_top_isContained (n + 1)).2 (by rwa [← hsz]) hcf

/-- If `G` contains a copy of `K⁻_{n+1}` and the complement of its image is `n`-colourable, then
`G` is `n`-colourable (Rabern STEP 2). -/
theorem Colorable.of_cliqueMinusEdge_copy {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj]
    {n : ℕ} (hn : 3 ≤ n) (hΔ : G.maxDegree ≤ n) (hcf : G.CliqueFree (n + 1))
    (φ : Copy (cliqueMinusEdge (n - 1)) G)
    (hcol : (G.induce ((Set.range φ)ᶜ : Set V)).Colorable n) :
    G.Colorable n := by
  have : NeZero n := ⟨by lia⟩
  obtain ⟨C⟩ := hcol
  let S : Set V := Set.range φ
  let x : V := φ 0
  let y : V := φ 1
  have hnotAdj : ¬ G.Adj x y := not_adj_ends_of_cliqueMinusEdge_copy hcf (by lia) φ
  have hx_out : (G.neighborFinset x \ S.toFinset).card ≤ 1 := by
    simpa [x, S] using card_neighborFinset_sdiff_range_cliqueMinusEdge_le
      (n := n - 1) (by omega) φ 0 (degree_cliqueMinusEdge_zero _)
  have hy_out : (G.neighborFinset y \ S.toFinset).card ≤ 1 := by
    simpa [y, S] using card_neighborFinset_sdiff_range_cliqueMinusEdge_le
      (n := n - 1) (by omega) φ 1 (degree_cliqueMinusEdge_one _)
  let fOut : V → Fin n := fun v => if hv : v ∈ Sᶜ then C ⟨v, hv⟩ else 0
  let Nx : Finset V := G.neighborFinset x \ S.toFinset
  let Ny : Finset V := G.neighborFinset y \ S.toFinset
  have hNx : Nx.card ≤ 1 := hx_out
  have hNy : Ny.card ≤ 1 := hy_out
  obtain ⟨α, hα⟩ : ∃ α : Fin n, α ∉ (Nx ∪ Ny).image fOut := by
    have hcard : ((Nx ∪ Ny).image fOut).card ≤ 2 :=
      (Finset.card_image_le).trans ((Finset.card_union_le _ _).trans (by omega))
    obtain ⟨α, hα⟩ : (((Nx ∪ Ny).image fOut)ᶜ).Nonempty := by
      rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
      omega
    exact ⟨α, Finset.mem_compl.1 hα⟩
  have hαx : ∀ v ∈ Nx, fOut v ≠ α := fun v hv hEq =>
    hα (hEq ▸ Finset.mem_image_of_mem fOut (Finset.mem_union_left _ hv))
  have hαy : ∀ v ∈ Ny, fOut v ≠ α := fun v hv hEq =>
    hα (hEq ▸ Finset.mem_image_of_mem fOut (Finset.mem_union_right _ hv))
  let ψ : Fin (n - 1 + 2) ≃ ↥S := Equiv.ofInjective (↑φ) φ.injective
  let rest : Finset (Fin (n - 1 + 2)) := (Finset.univ.erase 0).erase 1
  have hrest_card : rest.card = n - 1 := by
    simp [rest, Finset.card_erase_of_mem, Finset.mem_univ, Fin.zero_ne_one.symm,
      Finset.card_univ, Fintype.card_fin]
  let colors : Finset (Fin n) := Finset.univ.erase α
  have hcolors_card : colors.card = n - 1 := by
    simp [colors, Finset.card_erase_of_mem, Finset.mem_univ, Fintype.card_fin]
  let e : ↥rest ≃ ↥colors := Finset.equivOfCardEq (hrest_card.trans hcolors_card.symm)
  let colorH : Fin (n - 1 + 2) → Fin n := fun i =>
    if h : i ∈ rest then (e ⟨i, h⟩).1 else α
  have colorH_end {i : Fin (n - 1 + 2)} (hi : i ∉ rest) : colorH i = α := by
    simp [colorH, hi]
  have colorH_rest {i : Fin (n - 1 + 2)} (hi : i ∈ rest) : colorH i = (e ⟨i, hi⟩).1 := by
    simp [colorH, hi]
  have mem_rest_iff {i : Fin (n - 1 + 2)} : i ∈ rest ↔ i ≠ 0 ∧ i ≠ 1 := by
    simp [rest, Finset.mem_erase, Finset.mem_univ, and_comm]
  have φ_symm (v : V) (hv : v ∈ S) : φ (ψ.symm ⟨v, hv⟩) = v :=
    congrArg Subtype.val (ψ.apply_symm_apply ⟨v, hv⟩)
  let color : V → Fin n := fun v =>
    if hv : v ∈ S then colorH (ψ.symm ⟨v, hv⟩) else C ⟨v, hv⟩
  refine ⟨Coloring.mk color ?_⟩
  intro u v huv
  dsimp [color]
  by_cases huS : u ∈ S <;> by_cases hvS : v ∈ S
  · -- both in the copy
    simp only [huS, hvS, ↓reduceDIte]
    set i := ψ.symm ⟨u, huS⟩
    set j := ψ.symm ⟨v, hvS⟩
    have hui : φ i = u := φ_symm u huS
    have hvj : φ j = v := φ_symm v hvS
    have hij : i ≠ j := fun hEq => huv.ne (by rw [← hui, ← hvj, hEq])
    by_cases hi : i ∈ rest <;> by_cases hj : j ∈ rest
    · rw [colorH_rest hi, colorH_rest hj]
      exact Subtype.coe_injective.ne (e.injective.ne (Subtype.ext_iff.not.mpr hij))
    · rw [colorH_rest hi, colorH_end hj]
      exact Finset.ne_of_mem_erase (e ⟨i, hi⟩).property
    · rw [colorH_end hi, colorH_rest hj]
      exact (Finset.ne_of_mem_erase (e ⟨j, hj⟩).property).symm
    · -- both ends: must be `{0,1}`, which are non-adjacent
      have hi01 : i = 0 ∨ i = 1 := by
        have := (mem_rest_iff (i := i)).not.1 hi
        push Not at this; tauto
      have hj01 : j = 0 ∨ j = 1 := by
        have := (mem_rest_iff (i := j)).not.1 hj
        push Not at this; tauto
      have : ¬ G.Adj (φ i) (φ j) := by
        rcases hi01 with hi0 | hi0 <;> rcases hj01 with hj0 | hj0
        · exact absurd (hi0.trans hj0.symm) hij
        · simpa [x, y, hui, hvj, hi0, hj0] using hnotAdj
        · simpa [x, y, hui, hvj, hi0, hj0, adj_comm] using hnotAdj
        · exact absurd (hi0.trans hj0.symm) hij
      exact absurd (by simpa [hui, hvj] using huv) this
  · -- `u` in copy, `v` outside
    simp only [huS, hvS, ↓reduceDIte]
    set i := ψ.symm ⟨u, huS⟩
    have hui : φ i = u := φ_symm u huS
    by_cases hi : i ∈ rest
    · -- rest vertices have no outside neighbours
      have hi01 : i ≠ 0 ∧ i ≠ 1 := (mem_rest_iff (i := i)).1 hi
      have hdeg : (cliqueMinusEdge (n - 1)).degree i = (n - 1) + 1 :=
        degree_cliqueMinusEdge_of_ne_zero_one (n := n - 1) hi01.1 hi01.2
      have hN : G.neighborFinset (φ i) ⊆ S.toFinset := by
        simpa [S] using neighborFinset_subset_range_of_degree_cliqueMinusEdge
          (n := n - 1) (by omega) φ hdeg
      exact absurd (Set.mem_toFinset.1 (hN (by simpa [hui] using (mem_neighborFinset _ _ _).2 huv)))
        (mt Set.mem_toFinset.2 (by simpa [Set.mem_toFinset] using hvS))
    · rw [colorH_end hi]
      have hi01 : i = 0 ∨ i = 1 := by
        have := (mem_rest_iff (i := i)).not.1 hi
        push Not at this; tauto
      have huxy : u = x ∨ u = y :=
        hi01.imp (fun h => hui.symm.trans (congrArg φ h)) (fun h => hui.symm.trans (congrArg φ h))
      have hfOut : fOut v = C ⟨v, hvS⟩ := dif_pos hvS
      rcases huxy with rfl | rfl
      · exact (hfOut ▸ hαx v (Finset.mem_sdiff.2 ⟨(mem_neighborFinset _ _ _).2 huv,
          fun h => hvS (Set.mem_toFinset.1 h)⟩)).symm
      · exact (hfOut ▸ hαy v (Finset.mem_sdiff.2 ⟨(mem_neighborFinset _ _ _).2 huv,
          fun h => hvS (Set.mem_toFinset.1 h)⟩)).symm
  · -- `u` outside, `v` in copy (symmetric)
    simp only [huS, hvS, ↓reduceDIte]
    set j := ψ.symm ⟨v, hvS⟩
    have hvj : φ j = v := φ_symm v hvS
    by_cases hj : j ∈ rest
    · have hj01 : j ≠ 0 ∧ j ≠ 1 := (mem_rest_iff (i := j)).1 hj
      have hdeg : (cliqueMinusEdge (n - 1)).degree j = (n - 1) + 1 :=
        degree_cliqueMinusEdge_of_ne_zero_one (n := n - 1) hj01.1 hj01.2
      have hN : G.neighborFinset (φ j) ⊆ S.toFinset := by
        simpa [S] using neighborFinset_subset_range_of_degree_cliqueMinusEdge
          (n := n - 1) (by omega) φ hdeg
      exact absurd (Set.mem_toFinset.1 (hN (by simpa [hvj] using (mem_neighborFinset _ _ _).2 huv.symm)))
        (mt Set.mem_toFinset.2 (by simpa [Set.mem_toFinset] using huS))
    · rw [colorH_end hj]
      have hj01 : j = 0 ∨ j = 1 := by
        have := (mem_rest_iff (i := j)).not.1 hj
        push Not at this; tauto
      have hvxy : v = x ∨ v = y :=
        hj01.imp (fun h => hvj.symm.trans (congrArg φ h)) (fun h => hvj.symm.trans (congrArg φ h))
      have hfOut : fOut u = C ⟨u, huS⟩ := dif_pos huS
      rcases hvxy with rfl | rfl
      · exact hfOut ▸ hαx u (Finset.mem_sdiff.2 ⟨(mem_neighborFinset _ _ _).2 huv.symm,
          fun h => huS (Set.mem_toFinset.1 h)⟩)
      · exact hfOut ▸ hαy u (Finset.mem_sdiff.2 ⟨(mem_neighborFinset _ _ _).2 huv.symm,
          fun h => huS (Set.mem_toFinset.1 h)⟩)
  · -- both outside
    simp only [huS, hvS, ↓reduceDIte]
    exact C.valid huv

end CliqueMinusEdgeColorable

/-! ### The induction -/

/-! ### Surgery helpers -/

/-- Image of a `K_Δ` copy in `G.induce Iᶜ`. -/
theorem exists_clique_set_of_copy {Δ : ℕ} {I : Set V}
    (ψ : Copy (⊤ : SimpleGraph (Fin Δ)) (G.induce (Iᶜ : Set V))) :
    ∃ Q : Set V, Q ⊆ (Iᶜ : Set V) ∧ Q.ncard = Δ ∧ G.IsClique Q := by
  let ι : Fin Δ → V := fun i => (ψ i : V)
  have hinj : Function.Injective ι := fun _ _ h => ψ.injective (Subtype.ext h)
  refine ⟨Set.range ι, fun _ ⟨i, hi⟩ => hi ▸ (ψ i).property, ?_, ?_⟩
  · rw [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
  · intro a ha b hb hne
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    exact ψ.toHom.map_adj ((top_adj i j).2 fun h => hne (congrArg ι h))

/-- If a `Δ`-set `Q` is a clique of neighbours of `w`, then `Q ∪ {w}` is a `(Δ+1)`-clique. -/
theorem isNClique_union_singleton_of_neighbors [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {Δ : ℕ} {Q : Finset V} {w : V}
    (hQcard : Q.card = Δ)
    (hQclique : G.IsClique (Q : Set V))
    (hwQ : w ∉ Q)
    (hN : G.neighborFinset w = Q) :
    G.IsNClique (Δ + 1) (Q ∪ {w}) := by
  refine ⟨?clique, ?card⟩
  case card =>
    rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.2 hwQ),
      Finset.card_singleton, hQcard]
  case clique =>
    intro a ha b hb hne
    have ha' : a ∈ Q ∨ a = w := by
      have := Finset.mem_union.1 (show a ∈ Q ∪ {w} from ha)
      exact this.imp_right Finset.mem_singleton.1
    have hb' : b ∈ Q ∨ b = w := by
      have := Finset.mem_union.1 (show b ∈ Q ∪ {w} from hb)
      exact this.imp_right Finset.mem_singleton.1
    match ha', hb' with
    | Or.inl haQ, Or.inl hbQ =>
      exact hQclique (show a ∈ (Q : Set V) from haQ) (show b ∈ (Q : Set V) from hbQ) hne
    | Or.inl haQ, Or.inr hbw =>
      have : a ∈ G.neighborFinset w := by rw [hN]; exact haQ
      exact hbw ▸ ((mem_neighborFinset _ _ _).1 this).symm
    | Or.inr haw, Or.inl hbQ =>
      have : b ∈ G.neighborFinset w := by rw [hN]; exact hbQ
      exact haw ▸ (mem_neighborFinset _ _ _).1 this
    | Or.inr haw, Or.inr hbw =>
      exact (hne (haw.trans hbw.symm)).elim

/-- Neighbour set of `w` equals `Q` when `Q ⊆ N(w)` and both have cardinality `Δ`. -/
theorem neighborFinset_eq_of_subset_of_card [Fintype V] [DecidableRel G.Adj]
    {Q : Finset V} {w : V} {Δ : ℕ}
    (hsub : Q ⊆ G.neighborFinset w)
    (hQcard : Q.card = Δ)
    (hdeg : G.degree w = Δ) :
    G.neighborFinset w = Q :=
  (Finset.eq_of_subset_of_card_le hsub
    (by rw [card_neighborFinset_eq_degree, hdeg, hQcard])).symm

/-- From the inductive hypothesis on graphs of size `≤ k`, every such graph is `n`-colorable
when `3 ≤ n`, `Δ ≤ n`, and there is no `K_{n+1}`. -/
private theorem colorable_of_card_le_of_maxDegree_le
    {k n : ℕ}
    (ih : ∀ {V : Type u} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      Fintype.card V ≤ k → G.CliqueFree (G.maxDegree + 1) →
        (G.maxDegree = 2 → ¬G.HasOddCycle) → G.Colorable G.maxDegree)
    {V : Type u} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (hcard : Fintype.card V ≤ k) (hn : 3 ≤ n) (hΔ : G.maxDegree ≤ n)
    (hcf : G.CliqueFree (n + 1)) : G.Colorable n := by
  by_cases hc : G.Colorable G.maxDegree
  · exact Colorable.mono hΔ hc
  · by_cases hcf' : G.CliqueFree (G.maxDegree + 1)
    · by_cases hodd : G.maxDegree = 2 → ¬G.HasOddCycle
      · exact absurd (ih G hcard hcf' hodd) hc
      · -- `Δ = 2` and an odd cycle: greedy gives a 3-colouring.
        exact Colorable.mono (by lia) G.colorable_maxDegree_succ
    · -- Has a `K_{Δ+1}`. If `Δ = n` this contradicts `hcf`; otherwise greedy
      -- gives a `(Δ+1)`-colouring with `Δ+1 ≤ n`.
      by_cases hEq : G.maxDegree = n
      · rw [hEq] at hcf'
        exact absurd hcf hcf'
      · exact Colorable.mono (by lia) G.colorable_maxDegree_succ

/-- A complete graph on `n` vertices admits an `n`-colouring avoiding one forbidden colour
per vertex, provided the forbidden colours are not all equal. -/
theorem exists_coloring_avoiding_of_isClique [Fintype V] [DecidableEq V]
    {n : ℕ} {s : Finset V} (_hs : G.IsClique (s : Set V)) (hcard : s.card = n)
    (f : V → Fin n) (hne : ∃ a ∈ s, ∃ b ∈ s, f a ≠ f b) :
    ∃ c : V → Fin n, (∀ a ∈ s, ∀ b ∈ s, a ≠ b → c a ≠ c b) ∧ ∀ a ∈ s, c a ≠ f a := by
  classical
  have hnpos : 0 < n := by
    obtain ⟨a, ha, b, hb, hab⟩ := hne
    have hab_ne : a ≠ b := fun h => hab (h ▸ rfl)
    have hle : ({a, b} : Finset V).card ≤ n := by
      rw [← hcard]
      exact Finset.card_le_card (Finset.insert_subset ha (Finset.singleton_subset_iff.2 hb))
    have h2 : ({a, b} : Finset V).card = 2 := by simp [Finset.card_insert_of_notMem, hab_ne]
    omega
  let ι := ↥s
  have hιcard : Fintype.card ι = n := by simp [ι, ← hcard]
  let t : ι → Finset (Fin n) := fun x => Finset.univ.erase (f x.1)
  have hcompl_mem (u : Finset ι) (c : Fin n) :
      c ∈ (u.biUnion t)ᶜ ↔ ∀ x ∈ u, f x.1 = c := by
    constructor
    · intro hc x hx
      have : c ∉ t x := fun htx =>
        (Finset.mem_compl.1 hc) (Finset.mem_biUnion.2 ⟨x, hx, htx⟩)
      exact (by simpa [t, Finset.mem_erase] using this : c = f x.1).symm
    · intro hc
      refine Finset.mem_compl.2 ?_
      intro hbi
      rcases Finset.mem_biUnion.1 hbi with ⟨x, hx, htx⟩
      have : c ≠ f x.1 := by simpa [t, Finset.mem_erase] using htx
      exact this (hc x hx).symm
  have hhall : ∀ (u : Finset ι), u.card ≤ (u.biUnion t).card := by
    intro u
    have hcard_b : (u.biUnion t).card = n - (u.biUnion t)ᶜ.card := by
      have := Finset.card_add_card_compl (u.biUnion t)
      simp only [Fintype.card_fin] at this
      omega
    by_cases he : u = ∅
    · subst he; simp
    · by_cases hcst : ∃ c : Fin n, ∀ x ∈ u, f x.1 = c
      · obtain ⟨c, hc⟩ := hcst
        have hcompl_eq : (u.biUnion t)ᶜ = {c} := by
          ext d
          rw [hcompl_mem, Finset.mem_singleton]
          constructor
          · intro hd
            obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty he
            exact (hd x hx).symm.trans (hc x hx)
          · intro hd x hx; exact hd ▸ hc x hx
        have hu_le : u.card ≤ n - 1 := by
          have hle_univ : u.card ≤ n := by simpa [hιcard] using Finset.card_le_univ u
          by_contra hgt
          have hu_eq : u.card = n := by omega
          have hu_univ : u = Finset.univ :=
            Finset.eq_univ_of_card u (by simp [hu_eq, hιcard])
          obtain ⟨a, ha, b, hb, hab⟩ := hne
          have : f a = f b := by
            have ha' : (⟨a, ha⟩ : ι) ∈ u := by simp [hu_univ]
            have hb' : (⟨b, hb⟩ : ι) ∈ u := by simp [hu_univ]
            exact (hc _ ha').trans (hc _ hb').symm
          exact hab this
        rw [hcard_b, hcompl_eq, Finset.card_singleton]
        omega
      · push Not at hcst
        have hcompl_empty : (u.biUnion t)ᶜ = ∅ := by
          ext c
          simp only [Finset.notMem_empty, hcompl_mem, iff_false]
          intro hc
          obtain ⟨x, hx, hne⟩ := hcst c
          exact hne (hc x hx)
        rw [hcard_b, hcompl_empty, Finset.card_empty, tsub_zero]
        simpa [hιcard] using Finset.card_le_univ u
  obtain ⟨g, hg_inj, hg_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' t).1 hhall
  refine ⟨fun v => if hv : v ∈ s then g ⟨v, hv⟩ else ⟨0, hnpos⟩, ?_, ?_⟩
  · intro a ha b hb hne'
    simp only [ha, hb, ↓reduceDIte]
    exact fun h => hne' (Subtype.ext_iff.1 (hg_inj h))
  · intro a ha
    simp only [ha, ↓reduceDIte]
    have := hg_mem ⟨a, ha⟩
    simpa [t, Finset.mem_erase] using this

/-- The unique neighbour of `v ∈ Q` outside `Q` is its star in `I`. -/
theorem eq_star_of_adj_mem_compl [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {Δ : ℕ} {I Q : Set V} [DecidablePred (· ∈ Q)]
    (hreg : G.IsRegularOfDegree Δ) (hk : 1 ≤ Δ)
    (hQI : Q ⊆ Iᶜ)
    (hQreg : (G.induce Q).IsRegularOfDegree (Δ - 1))
    {v : V} (hv : v ∈ Q) {w : V} (hw : w ∈ (Qᶜ : Set V)) (hadj : G.Adj v w)
    {ystar : V} (hystar : ystar ∈ I ∧ G.Adj v ystar) :
    w = ystar := by
  have hinter : (G.neighborFinset v ∩ Q.toFinset).card = Δ - 1 := by
    have hdegQ : (G.induce Q).degree ⟨v, hv⟩ = Δ - 1 := hQreg _
    have hmap := congrArg Finset.card (G.map_neighborFinset_induce (s := Q) ⟨v, hv⟩)
    simpa [card_neighborFinset_eq_degree, hdegQ] using hmap.symm
  have hsum :
      (G.neighborFinset v ∩ Q.toFinset).card + (G.neighborFinset v \ Q.toFinset).card =
        G.degree v := by
    rw [← card_neighborFinset_eq_degree, add_comm, Finset.card_sdiff_add_card_inter]
  have hout : (G.neighborFinset v \ Q.toFinset).card = 1 := by
    have hdeg := hreg v
    have h : (Δ - 1) + (G.neighborFinset v \ Q.toFinset).card = Δ := by
      rw [← hinter, ← hdeg]; exact hsum
    omega
  obtain ⟨w0, hw0⟩ := Finset.card_eq_one.1 hout
  have hwout : w ∈ G.neighborFinset v \ Q.toFinset :=
    Finset.mem_sdiff.2 ⟨(mem_neighborFinset _ _ _).2 hadj, by
      simp only [Set.mem_toFinset]; exact hw⟩
  have hstar_out : ystar ∈ G.neighborFinset v \ Q.toFinset := by
    refine Finset.mem_sdiff.2 ⟨(mem_neighborFinset _ _ _).2 hystar.2, ?_⟩
    simp only [Set.mem_toFinset]
    exact fun hQ => absurd hystar.1 (Set.notMem_of_mem_compl (hQI hQ))
  have hw_eq : w = w0 := by rw [hw0] at hwout; simpa using hwout
  have hs_eq : ystar = w0 := by rw [hw0] at hstar_out; simpa using hstar_out
  exact hw_eq.trans hs_eq.symm

/-- If every vertex of a `Δ`-clique `Q ⊆ Iᶜ` stars at the same `w ∈ I`, we get a `K_{Δ+1}`. -/
theorem isNClique_of_const_star [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {Δ : ℕ} {I : Set V} {Q : Finset V} {w : V}
    (hQcard : Q.card = Δ) (hQclique : G.IsClique (Q : Set V))
    (hQI : ↑Q ⊆ (Iᶜ : Set V)) (hwI : w ∈ I)
    (hadj : ∀ v ∈ Q, G.Adj v w) (hreg : G.degree w = Δ) :
    G.IsNClique (Δ + 1) (Q ∪ {w}) := by
  have hwQ : w ∉ Q := fun h => absurd hwI (Set.notMem_of_mem_compl (hQI h))
  have hsub : Q ⊆ G.neighborFinset w := fun v hv =>
    (mem_neighborFinset _ _ _).2 (hadj v hv).symm
  exact isNClique_union_singleton_of_neighbors hQcard hQclique hwQ
    (neighborFinset_eq_of_subset_of_card hsub hQcard hreg)

/-- Combine a colouring of `Qᶜ` with a Hall colouring of the clique `Q` that avoids star colours. -/
theorem Colorable.of_clique_block_with_stars [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {n : ℕ} {Q : Set V} [DecidablePred (· ∈ Q)] {I : Set V}
    (hQclique : G.IsClique Q) (hQcard : Q.ncard = n)
    (hQI : Q ⊆ (Iᶜ : Set V))
    (C : (G.induce (Qᶜ : Set V)).Coloring (Fin n))
    (star : V → V)
    (hstar : ∀ v ∈ Q, star v ∈ I ∧ G.Adj v (star v))
    (honly : ∀ v ∈ Q, ∀ w, w ∈ (Qᶜ : Set V) → G.Adj v w → w = star v)
    {a b : V} (ha : a ∈ Q) (hb : b ∈ Q)
    (hneC : C ⟨star a, fun h => absurd (hstar a ha).1 (Set.notMem_of_mem_compl (hQI h))⟩ ≠
            C ⟨star b, fun h => absurd (hstar b hb).1 (Set.notMem_of_mem_compl (hQI h))⟩) :
    G.Colorable n := by
  classical
  let Qf : Finset V := Q.toFinset
  have hQf_coe : (Qf : Set V) = Q := Set.coe_toFinset _
  have hQf_card : Qf.card = n := by rw [← Set.ncard_eq_toFinset_card' Q, hQcard]
  have hstar_Qc (v : V) (hv : v ∈ Q) : star v ∈ (Qᶜ : Set V) := fun h =>
    absurd (hstar v hv).1 (Set.notMem_of_mem_compl (hQI h))
  have hnpos : 0 < n := by
    have hab_ne : a ≠ b := fun heq => by
      subst heq
      exact hneC rfl
    have h2 : ({a, b} : Finset V).card = 2 := by
      simp [Finset.card_insert_of_notMem, hab_ne]
    have hle : ({a, b} : Finset V).card ≤ n := by
      rw [← hQf_card]
      exact Finset.card_le_card
        (Finset.insert_subset (by simpa [← Set.mem_toFinset] using ha)
          (Finset.singleton_subset_iff.2 (by simpa [← Set.mem_toFinset] using hb)))
    omega
  let f : V → Fin n := fun v =>
    if hv : v ∈ Q then C ⟨star v, hstar_Qc v hv⟩ else ⟨0, hnpos⟩
  have hne_f : ∃ x ∈ Qf, ∃ y ∈ Qf, f x ≠ f y :=
    ⟨a, by simpa [← Set.mem_toFinset] using ha, b, by simpa [← Set.mem_toFinset] using hb,
      by simpa [f, ha, hb] using hneC⟩
  obtain ⟨cQ, hcQ_proper, hcQ_avoid⟩ :=
    exists_coloring_avoiding_of_isClique (by simpa [hQf_coe] using hQclique) hQf_card f hne_f
  let color : V → Fin n := fun v => if hv : v ∈ Q then cQ v else C ⟨v, Set.mem_compl hv⟩
  refine ⟨Coloring.mk color fun {x y} hxy => ?_⟩
  dsimp [color]
  by_cases hxQ : x ∈ Q <;> by_cases hyQ : y ∈ Q
  · have hxQf : x ∈ Qf := by simpa [← Set.mem_toFinset] using hxQ
    have hyQf : y ∈ Qf := by simpa [← Set.mem_toFinset] using hyQ
    simpa [hxQ, hyQ] using hcQ_proper x hxQf y hyQf hxy.ne
  · have hyQc : y ∈ (Qᶜ : Set V) := Set.mem_compl hyQ
    have hy_eq : y = star x := honly x hxQ y hyQc hxy
    have hxQf : x ∈ Qf := by simpa [← Set.mem_toFinset] using hxQ
    have havoid := hcQ_avoid x hxQf
    simp only [f, hxQ, ↓reduceDIte] at havoid
    rw [hy_eq]
    simp only [hxQ, show star x ∉ Q from hy_eq ▸ hyQ, ↓reduceDIte]
    exact havoid
  · have hxQc : x ∈ (Qᶜ : Set V) := Set.mem_compl hxQ
    have hx_eq : x = star y := honly y hyQ x hxQc hxy.symm
    have hyQf : y ∈ Qf := by simpa [← Set.mem_toFinset] using hyQ
    have havoid := hcQ_avoid y hyQf
    simp only [f, hyQ, ↓reduceDIte] at havoid
    rw [hx_eq]
    simp only [hyQ, show star y ∉ Q from hx_eq ▸ hxQ, ↓reduceDIte]
    exact havoid.symm
  · have hxQc : x ∈ (Qᶜ : Set V) := Set.mem_compl hxQ
    have hyQc : y ∈ (Qᶜ : Set V) := Set.mem_compl hyQ
    have hxy' : (G.induce (Qᶜ : Set V)).Adj ⟨x, hxQc⟩ ⟨y, hyQc⟩ := hxy
    simp only [hxQ, hyQ, ↓reduceDIte]
    exact C.valid hxy'

/-- `G* = (G.induce Qᶜ) ⊔ edge ystar zstar` is `Δ`-colourable by the inductive hypothesis. -/
private theorem colorable_surgery_graph
    {V : Type u} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    {Δ : ℕ} (hΔ3 : 3 ≤ Δ) (hH : ¬ cliqueMinusEdge (Δ - 1) ⊑ G)
    (hreg' : G.IsRegularOfDegree Δ)
    {Q : Set V} [DecidablePred (· ∈ Q)]
    {k : ℕ} (hcardQc : Fintype.card ↥(Qᶜ : Set V) ≤ k)
    (ih : ∀ {V : Type u} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      Fintype.card V ≤ k → G.CliqueFree (G.maxDegree + 1) →
        (G.maxDegree = 2 → ¬G.HasOddCycle) → G.Colorable G.maxDegree)
    {ystar zstar : V}
    (hystar_Qc : ystar ∈ (Qᶜ : Set V)) (hzstar_Qc : zstar ∈ (Qᶜ : Set V))
    (_hne : ystar ≠ zstar)
    {y z : V} (hyQ : y ∈ Q) (hzQ : z ∈ Q)
    (hyAdj : G.Adj y ystar) (hzAdj : G.Adj z zstar) :
    (G.induce (Qᶜ : Set V) ⊔
      edge (⟨ystar, hystar_Qc⟩ : ↥(Qᶜ : Set V)) ⟨zstar, hzstar_Qc⟩).Colorable Δ := by
  classical
  set yS : ↥(Qᶜ : Set V) := ⟨ystar, hystar_Qc⟩
  set zS : ↥(Qᶜ : Set V) := ⟨zstar, hzstar_Qc⟩
  set Gstar := G.induce (Qᶜ : Set V) ⊔ edge yS zS
  have hΔstar : Gstar.maxDegree ≤ Δ := by
    refine maxDegree_le_of_forall_degree_le _ _ fun v => ?_
    have hdeg_le : (G.induce (Qᶜ : Set V)).degree v ≤ Δ := by
      have hsub :
          ((G.induce (Qᶜ : Set V)).neighborFinset v).map
            (Function.Embedding.subtype (· ∈ (Qᶜ : Set V))) ⊆ G.neighborFinset ↑v := by
        intro x hx
        rcases Finset.mem_map.1 hx with ⟨a, ha, rfl⟩
        exact (mem_neighborFinset _ _ _).2 ((mem_neighborFinset (G.induce (Qᶜ : Set V)) _ _).1 ha)
      have hle := Finset.card_le_card hsub
      rw [Finset.card_map, card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at hle
      exact hle.trans_eq (hreg' _)
    by_cases hv : (v : V) = ystar ∨ (v : V) = zstar
    · have hdrop : (G.induce (Qᶜ : Set V)).degree v ≤ Δ - 1 := by
        have hmem : ∃ x ∈ Q, G.Adj ↑v x := by
          rcases hv with h | h
          · exact ⟨y, hyQ, by simpa [h] using hyAdj.symm⟩
          · exact ⟨z, hzQ, by simpa [h] using hzAdj.symm⟩
        obtain ⟨x, hxQ, hxAdj⟩ := hmem
        have hxN : x ∈ G.neighborFinset ↑v := (mem_neighborFinset _ _ _).2 hxAdj
        have hsub :
            ((G.induce (Qᶜ : Set V)).neighborFinset v).map
              (Function.Embedding.subtype (· ∈ (Qᶜ : Set V))) ⊆
                (G.neighborFinset ↑v).erase x := by
          intro a ha
          rcases Finset.mem_map.1 ha with ⟨b, hb, rfl⟩
          have hb' : G.Adj ↑v ↑b := (mem_neighborFinset (G.induce (Qᶜ : Set V)) _ _).1 hb
          have hne_xb : (b : V) ≠ x := fun heq =>
            (Set.notMem_compl_iff.mpr hxQ) (heq ▸ b.property)
          exact Finset.mem_erase.2 ⟨hne_xb, (mem_neighborFinset _ _ _).2 hb'⟩
        have hle := Finset.card_le_card hsub
        rw [Finset.card_map, card_neighborFinset_eq_degree,
          Finset.card_erase_of_mem hxN, card_neighborFinset_eq_degree, hreg'] at hle
        exact hle
      exact (degree_sup_edge_le (G := G.induce (Qᶜ : Set V)) yS zS v).trans (by omega)
    · have hEq : Gstar.degree v = (G.induce (Qᶜ : Set V)).degree v := by
        rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
        congr 1
        ext w
        simp only [mem_neighborFinset, Gstar, sup_adj, edge_adj]
        constructor
        · intro h
          exact h.resolve_right (by
            intro hpair
            rcases hpair.1 with ⟨h1, _⟩ | ⟨h1, _⟩
            · exact hv (Or.inl (Subtype.ext_iff.mp h1))
            · exact hv (Or.inr (Subtype.ext_iff.mp h1)))
        · exact Or.inl
      exact hEq ▸ hdeg_le
  have hcfstar : Gstar.CliqueFree (Δ + 1) := by
    have hH' : ¬ cliqueMinusEdge (Δ - 1) ⊑ G.induce (Qᶜ : Set V) := fun h =>
      hH (h.trans (Copy.induce G (Qᶜ : Set V)).isContained)
    have := cliqueFree_sup_edge_of_cliqueMinusEdge_free (G := G.induce (Qᶜ : Set V))
      (k := Δ - 1) yS zS hH'
    convert this using 1; omega
  exact colorable_of_card_le_of_maxDegree_le (fun G => ih G) Gstar hcardQc hΔ3 hΔstar hcfstar

/-- An induced clique of size `n` is `(n-1)`-regular. -/
theorem isRegularOfDegree_induce_of_isClique [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {Q : Set V} [DecidablePred (· ∈ Q)] {n : ℕ}
    (hQclique : G.IsClique Q) (hQcard : Fintype.card ↥Q = n) :
    (G.induce Q).IsRegularOfDegree (n - 1) := by
  intro v
  rw [← card_neighborFinset_eq_degree]
  have hset : (G.induce Q).neighborFinset v = Finset.univ.erase v := by
    ext x
    constructor
    · intro hx
      exact Finset.mem_erase.2 ⟨((mem_neighborFinset _ _ _).1 hx).ne', Finset.mem_univ _⟩
    · intro hx
      have hne : (x : V) ≠ (v : V) :=
        Subtype.coe_injective.ne (Finset.mem_erase.1 hx).1
      exact (mem_neighborFinset _ _ _).2 (hQclique v.property x.property hne.symm)
  rw [hset, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hQcard]

/-- An induced clique on a nonempty set is connected. -/
theorem connected_induce_of_isClique [DecidableEq V]
    {Q : Set V} [Nonempty ↥Q] (hQclique : G.IsClique Q) :
    (G.induce Q).Connected := by
  refine (connected_iff _).2 ⟨fun a b => ?_, ‹Nonempty ↥Q›⟩
  by_cases h : a = b
  · subst h; exact ⟨Walk.nil⟩
  · exact ⟨Walk.cons (hQclique a.property b.property (Subtype.coe_injective.ne h)) Walk.nil⟩

/-- The vertex set of a cycle has cardinality equal to its length. -/
theorem Walk.IsCycle.support_toFinset_card [DecidableEq V] {v : V} {c : G.Walk v v}
    (hc : c.IsCycle) : c.support.toFinset.card = c.length := by
  have hnodup : c.support.tail.Nodup := hc.support_nodup
  have hne : c.support ≠ [] := c.support_ne_nil
  have hlen : c.support.tail.length = c.length := by
    have hsup := Walk.length_support c
    match hlist : c.support with
    | [] => exact (hne hlist).elim
    | _ :: t =>
      simp only [hlist, List.tail_cons, List.length_cons] at hsup ⊢
      omega
  have heq : c.support.toFinset = c.support.tail.toFinset := by
    ext x
    simp only [List.mem_toFinset]
    constructor
    · intro hx
      have hx' : x = c.support.head hne ∨ x ∈ c.support.tail :=
        List.mem_cons.1 ((List.cons_head_tail hne).symm ▸ hx)
      rcases hx' with rfl | hx'
      · -- `head = start = end ∈ tail`
        have hhead : c.support.head hne = v := by
          match c with
          | .nil => simp
          | .cons _ _ => simp [Walk.support_cons]
        rw [hhead]
        exact c.end_mem_tail_support hc.not_nil
      · exact hx'
    · exact List.mem_of_mem_tail
  rw [heq, List.toFinset_card_of_nodup hnodup, hlen]

/-- Combine a colouring of `Qᶜ` with a path-extension across a spanning `y,z`-path in `Q`,
following Rabern: colour `y` with the colour of `z*`, then greedily along the path
(internal vertices have an uncoloured neighbour; `z` sees `y` and `z*` the same colour). -/
theorem Colorable.of_rabern_path_extension [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] {Q : Finset V} {y z : V}
    (p : G.Walk y z) (hp : p.IsPath)
    (hspan : p.support.toFinset = Q)
    (C : (G.induce ((↑Q : Set V)ᶜ)).Coloring (Fin n))
    (star : V → V)
    (hstarQc : ∀ v ∈ Q, star v ∈ ((↑Q : Set V)ᶜ))
    (hstarAdj : ∀ v ∈ Q, G.Adj v (star v))
    (honly : ∀ v ∈ Q, ∀ w ∈ ((↑Q : Set V)ᶜ), G.Adj v w → w = star v)
    (hyzAdj : G.Adj y z)
    (hne : C ⟨star y, by
        have : y ∈ Q := by rw [← hspan]; exact List.mem_toFinset.2 p.start_mem_support
        exact hstarQc y this⟩ ≠
      C ⟨star z, by
        have : z ∈ Q := by rw [← hspan]; exact List.mem_toFinset.2 p.end_mem_support
        exact hstarQc z this⟩)
    (hdeg : ∀ v ∈ Q, (G.neighborFinset v).card ≤ n) :
    G.Colorable n := by
  classical
  have hyQ : y ∈ Q := by rw [← hspan]; exact List.mem_toFinset.2 p.start_mem_support
  have hzQ : z ∈ Q := by rw [← hspan]; exact List.mem_toFinset.2 p.end_mem_support
  set a : Fin n := C ⟨star z, hstarQc z hzQ⟩
  have hy_not : y ∉ (Qᶜ : Finset V) := Finset.notMem_compl.2 hyQ
  -- Build the colouring of `insert y Qᶜ` directly from `C`.
  set sY : Finset V := insert y (Qᶜ : Finset V)
  let colorY : ↥(↑sY : Set V) → Fin n := fun u =>
    if h : u.1 = y then a
    else C ⟨u.1, by
      have hu : u.1 ∈ sY := by simpa [sY] using u.property
      have hu' : u.1 ∈ (Qᶜ : Finset V) := (Finset.mem_insert.1 (by simpa [sY] using hu)).resolve_left h
      simpa using hu'⟩
  have hCy_valid : ∀ {x y' : ↥(↑sY : Set V)},
      (G.induce (↑sY : Set V)).Adj x y' → colorY x ≠ colorY y' := by
    intro x y' hxy
    have hadj : G.Adj x.1 y'.1 := hxy
    dsimp [colorY]
    by_cases hx : x.1 = y <;> by_cases hy' : y'.1 = y
    · exact absurd (hx.trans hy'.symm) hadj.ne
    · simp only [hx, hy', ↓reduceDIte]
      have hyQc : y'.1 ∈ ((↑Q : Set V)ᶜ) := by
        have : y'.1 ∈ (Qᶜ : Finset V) :=
          (Finset.mem_insert.1 (by simpa [sY] using y'.property)).resolve_left hy'
        simpa using this
      have : y'.1 = star y := honly y hyQ y'.1 hyQc (hx ▸ hadj)
      simpa [this, a] using Ne.symm hne
    · simp only [hx, hy', ↓reduceDIte]
      have hxQc : x.1 ∈ ((↑Q : Set V)ᶜ) := by
        have : x.1 ∈ (Qᶜ : Finset V) :=
          (Finset.mem_insert.1 (by simpa [sY] using x.property)).resolve_left hx
        simpa using this
      have : x.1 = star y := honly y hyQ x.1 hxQc (hy' ▸ hadj.symm)
      simpa [this, a] using hne
    · simp only [hx, hy', ↓reduceDIte]
      exact C.valid hadj
  let Cy : (G.induce (↑sY : Set V)).Coloring (Fin n) :=
    Coloring.mk colorY hCy_valid
  have hCy_y : Cy ⟨y, by simp [sY]⟩ = a := by
    change colorY _ = a; simp [colorY]
  have hzstar_Qc : star z ∈ (Qᶜ : Finset V) := by simpa using hstarQc z hzQ
  have hzstar_mem : star z ∈ sY := by simp [sY, hzstar_Qc]
  have hCy_zstar : Cy ⟨star z, hzstar_mem⟩ = a := by
    change colorY _ = a
    have hne_zy : (star z : V) ≠ y := fun h => hy_not (h ▸ hzstar_Qc)
    simp [colorY, hne_zy]
    rfl
  -- Length induction keeps the path endpoint `z` fixed (Walk induction would generalize it).
  -- Here `q` is the *uncoloured* suffix of the spanning path: colour its vertices in order,
  -- using a free colour at internal vertices and the `y`/`star z` collision at `z`.
  have along :
      ∀ (k : ℕ) {u : V} (q : G.Walk u z), q.length = k → q.IsPath →
        ∀ (s : Finset V) (Cs : (G.induce (↑s : Set V)).Coloring (Fin n))
          (hyS : y ∈ s) (hzS : star z ∈ s),
          Cs ⟨y, hyS⟩ = a → Cs ⟨star z, hzS⟩ = a →
          (∀ x ∈ q.support, x ∈ Q) →
          (∀ x ∈ q.support, x ∉ s) →
          (G.induce (↑(s ∪ q.support.toFinset) : Set V)).Colorable n := by
    intro k
    induction k with
    | zero =>
      intro u q hk hq s Cs hyS hzS hyC hzC hQin hfresh
      have hnil : q.Nil := Walk.length_eq_zero_iff.1 hk
      have huz : u = z := hnil.eq
      have hu_not : u ∉ s := hfresh u (by
        rw [(Walk.nil_iff_support_eq (p := q)).1 hnil]; simp)
      let f : V → Fin n := fun t => if ht : t ∈ s then Cs ⟨t, ht⟩ else 0
      have himg : ((G.neighborFinset u ∩ s).image f).card < n := by
        have hyN : y ∈ G.neighborFinset u ∩ s :=
          Finset.mem_inter.2 ⟨(mem_neighborFinset _ _ _).2 (huz ▸ hyzAdj.symm), hyS⟩
        have hsN : star z ∈ G.neighborFinset u ∩ s :=
          Finset.mem_inter.2 ⟨(mem_neighborFinset _ _ _).2
            (huz ▸ hstarAdj z hzQ), hzS⟩
        have hyne : y ≠ star z := fun h =>
          (Set.notMem_of_mem_compl (hstarQc z hzQ)) (h ▸ hyQ)
        have hfy : f y = a := by simp [f, hyS, hyC]
        have hfs : f (star z) = a := by simp [f, hzS, hzC]
        have hcoll : f y = f (star z) := hfy.trans hfs.symm
        by_cases hlt : (G.neighborFinset u ∩ s).card < n
        · exact Finset.card_image_le.trans_lt hlt
        · have hcardNs : (G.neighborFinset u ∩ s).card = n := by
            have : (G.neighborFinset u ∩ s).card ≤ n :=
              (Finset.card_le_card Finset.inter_subset_left).trans
                (huz ▸ hdeg z hzQ)
            omega
          have hnotInj : ¬ Set.InjOn f ↑(G.neighborFinset u ∩ s) := fun hInj =>
            hyne (hInj hyN hsN hcoll)
          refine Nat.lt_of_le_of_ne
            (Finset.card_image_le.trans (le_of_eq hcardNs)) fun heq => hnotInj ?_
          exact Finset.card_image_iff.1 (heq.trans hcardNs.symm)
      have hcolz := Colorable.of_induce_insert_image (C := Cs) (v := u)
        (by simpa [f] using himg)
      have hsets : s ∪ q.support.toFinset = insert u s := by
        rw [(Walk.nil_iff_support_eq (p := q)).1 hnil]
        change s ∪ {u} = insert u s
        rw [Finset.union_comm, ← Finset.insert_eq]
      exact hsets ▸ hcolz
    | succ k ih =>
      intro u q hk hq s Cs hyS hzS hyC hzC hQin hfresh
      have hnnil : ¬ q.Nil := by
        rw [Walk.not_nil_iff_lt_length]; omega
      obtain ⟨v, hadj, q', rfl⟩ := Walk.not_nil_iff.1 hnnil
      have hq' : q'.IsPath := ((Walk.cons_isPath_iff hadj q').1 hq).1
      have hu_not_q' : u ∉ q'.support := ((Walk.cons_isPath_iff hadj q').1 hq).2
      have huQ : u ∈ Q := hQin u (by simp [Walk.support_cons])
      have hu_not : u ∉ s := hfresh u (by simp [Walk.support_cons])
      have hlen' : q'.length = k := by simp [Walk.length_cons] at hk; omega
      -- Colour `u`; the next path vertex `v` is still uncoloured.
      have hv_fresh : v ∉ s := hfresh v (by simp [Walk.support_cons])
      have hlt : (G.neighborFinset u ∩ s).card < n := by
        have hvN : v ∈ G.neighborFinset u := (mem_neighborFinset _ _ _).2 hadj
        have hsub : G.neighborFinset u ∩ s ⊆ (G.neighborFinset u).erase v := by
          intro t ht
          exact Finset.mem_erase.2 ⟨fun he => hv_fresh (he ▸ (Finset.mem_inter.1 ht).2),
            (Finset.mem_inter.1 ht).1⟩
        have hle := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hvN] at hle
        have := hdeg u huQ
        omega
      obtain ⟨Cs', hpres⟩ := exists_coloring_induce_insert hu_not Cs hlt
      have hyS' : y ∈ insert u s := Finset.mem_insert_of_mem hyS
      have hzS' : star z ∈ insert u s := Finset.mem_insert_of_mem hzS
      have hyC' : Cs' ⟨y, hyS'⟩ = a := (hpres y hyS).trans hyC
      have hzC' : Cs' ⟨star z, hzS'⟩ = a := (hpres (star z) hzS).trans hzC
      have hsets : s ∪ (Walk.cons hadj q').support.toFinset =
          insert u s ∪ q'.support.toFinset := by
        rw [Walk.support_cons, List.toFinset_cons, Finset.union_insert, Finset.insert_union]
      rw [hsets]
      exact ih q' hlen' hq' (insert u s) Cs' hyS' hzS' hyC' hzC'
        (fun x hx => hQin x (by simp [Walk.support_cons, hx]))
        (fun x hx => by
          simp only [Finset.mem_insert, not_or]
          exact ⟨fun h => hu_not_q' (h ▸ hx),
            hfresh x (by simp [Walk.support_cons, hx])⟩)
  cases p with
  | nil => exact (hyzAdj.ne rfl).elim
  | cons hadj q =>
    -- `p` starts at already-coloured `y`; colour the suffix `q`.
    have hq : q.IsPath := ((Walk.cons_isPath_iff hadj q).1 hp).1
    have hy_not_q : y ∉ q.support := ((Walk.cons_isPath_iff hadj q).1 hp).2
    have hfinal := along q.length q rfl hq sY Cy (by simp [sY]) hzstar_mem hCy_y hCy_zstar
      (fun v hv => by
        have : v ∈ (Walk.cons hadj q).support.toFinset := by
          simp only [Walk.support_cons, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset] at hv ⊢; exact Or.inr hv
        simpa [← hspan] using this)
      (fun v hv => by
        simp only [sY, Finset.mem_insert, not_or]
        exact ⟨fun hvy => hy_not_q (hvy ▸ hv), by
          have hvQ : v ∈ Q := by
            have : v ∈ (Walk.cons hadj q).support.toFinset := by
              simp only [Walk.support_cons, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset] at hv ⊢; exact Or.inr hv
            simpa [← hspan] using this
          exact Finset.notMem_compl.2 hvQ⟩)
    have hsets : sY ∪ q.support.toFinset = Finset.univ := by
      ext x
      constructor
      · intro; exact Finset.mem_univ _
      · intro _
        by_cases hxQ : x ∈ Q
        · -- `x` lies on the spanning path `y :: q.support`.
          have hxsup : x ∈ (Walk.cons hadj q).support.toFinset := by
            rwa [hspan]
          refine Finset.mem_union.2 ?_
          have hxmem : x = y ∨ x ∈ q.support.toFinset := by
            simpa [Walk.support_cons, List.toFinset_cons, Finset.mem_insert] using hxsup
          rcases hxmem with rfl | hxmem
          · exact Or.inl (Finset.mem_insert_self _ _)
          · exact Or.inr hxmem
        · exact Finset.mem_union.2 (Or.inl (Finset.mem_insert_of_mem (Finset.mem_compl.2 hxQ)))
    rw [hsets, Finset.coe_univ] at hfinal
    exact (colorable_congr G.induceUnivIso).1 hfinal

/-- Clique-block assembly of Rabern surgery. -/
private theorem brooksSurgery_clique
    {V : Type u} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    {Δ : ℕ} (hΔ3 : 3 ≤ Δ) (hcf : G.CliqueFree (Δ + 1))
    (hH : ¬ cliqueMinusEdge (Δ - 1) ⊑ G) (hreg' : G.IsRegularOfDegree Δ)
    {I : Set V} (hI : Maximal G.IsIndepSet I) [DecidablePred (· ∈ I)]
    {k : ℕ} (hcardV : Fintype.card V ≤ k + 1)
    (ih : ∀ {V : Type u} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      Fintype.card V ≤ k → G.CliqueFree (G.maxDegree + 1) →
        (G.maxDegree = 2 → ¬G.HasOddCycle) → G.Colorable G.maxDegree)
    (Q : Set V) [DecidablePred (· ∈ Q)]
    (hQI : Q ⊆ (Iᶜ : Set V)) (hQcard : Q.ncard = Δ) (hQclique : G.IsClique Q) :
    G.Colorable Δ := by
  classical
  let Qf : Finset V := Q.toFinset
  have hQf_coe : (Qf : Set V) = Q := Set.coe_toFinset _
  have hQf_card : Qf.card = Δ := by
    rw [← Set.ncard_eq_toFinset_card' Q, hQcard]
  have hQcard_f : Fintype.card ↥Q = Δ := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hQcard]
  have hQreg : (G.induce Q).IsRegularOfDegree (Δ - 1) :=
    isRegularOfDegree_induce_of_isClique hQclique hQcard_f
  have hQne : Nonempty ↥Q :=
    Set.Nonempty.to_subtype ((Set.ncard_pos).1 (by omega : 0 < Q.ncard))
  have hQconn : (G.induce Q).Connected := connected_induce_of_isClique (Q := Q) hQclique
  have hstarU : ∀ v ∈ Q, ∃! w, w ∈ I ∧ G.Adj v w := fun v hv =>
    existsUnique_adj_mem_of_isRegular (by omega) hreg' hI hQI hQreg v hv
  let star : V → V := fun v =>
    if hv : v ∈ Q then Classical.choose (hstarU v hv).exists else v
  have hstar : ∀ v ∈ Q, star v ∈ I ∧ G.Adj v (star v) := by
    intro v hv
    simpa [star, hv] using Classical.choose_spec (hstarU v hv).exists
  have hstar_ne : ∃ y ∈ Q, ∃ z ∈ Q, star y ≠ star z := by
    by_contra h
    push Not at h
    obtain ⟨y0⟩ := hQne
    have hwI : star ↑y0 ∈ I := (hstar y0 y0.property).1
    have hadj : ∀ v ∈ Qf, G.Adj v (star ↑y0) := fun v hv => by
      have hvQ : v ∈ Q := by simpa [← hQf_coe] using hv
      exact (h v hvQ ↑y0 y0.property) ▸ (hstar v hvQ).2
    have : G.IsNClique (Δ + 1) (Qf ∪ {star ↑y0}) :=
      isNClique_of_const_star hQf_card (by simpa [hQf_coe] using hQclique)
        (by simpa [hQf_coe] using hQI) hwI hadj (hreg' _)
    exact hcf _ this
  obtain ⟨y0, hy0, z0, hz0, hne0⟩ := hstar_ne
  obtain ⟨y, z, hyzAdj, hstars_ne⟩ :=
    Connected.exists_adj_ne_of_ne hQconn (fun v : ↥Q => star ↑v)
      (show star ↑(⟨y0, hy0⟩ : ↥Q) ≠ star ↑(⟨z0, hz0⟩ : ↥Q) from hne0)
  set ystar := star ↑y
  set zstar := star ↑z
  have hyAdj : G.Adj ↑y ystar := (hstar _ y.property).2
  have hzAdj : G.Adj ↑z zstar := (hstar _ z.property).2
  have hystar_Qc : ystar ∈ (Qᶜ : Set V) := fun h =>
    absurd (hstar _ y.property).1 (Set.notMem_of_mem_compl (hQI h))
  have hzstar_Qc : zstar ∈ (Qᶜ : Set V) := fun h =>
    absurd (hstar _ z.property).1 (Set.notMem_of_mem_compl (hQI h))
  have hcardQc : Fintype.card ↥(Qᶜ : Set V) ≤ k := by
    have := Fintype.card_compl_set Q
    omega
  obtain ⟨Cstar⟩ := colorable_surgery_graph (G := G) hΔ3 hH hreg' hcardQc ih
    hystar_Qc hzstar_Qc hstars_ne y.property z.property hyAdj hzAdj
  let C : (G.induce (Qᶜ : Set V)).Coloring (Fin Δ) :=
    Cstar.comp (.ofLE le_sup_left)
  have hneC :
      C ⟨ystar, hystar_Qc⟩ ≠ C ⟨zstar, hzstar_Qc⟩ := by
    have hadj :
        (G.induce (Qᶜ : Set V) ⊔
          edge (⟨ystar, hystar_Qc⟩ : ↥(Qᶜ : Set V)) ⟨zstar, hzstar_Qc⟩).Adj
          ⟨ystar, hystar_Qc⟩ ⟨zstar, hzstar_Qc⟩ := by
      refine Or.inr ?_
      rw [edge_adj]
      exact ⟨Or.inl ⟨rfl, rfl⟩, fun h => hstars_ne (congrArg Subtype.val h)⟩
    simpa [C] using Cstar.valid hadj
  exact Colorable.of_clique_block_with_stars hQclique hQcard hQI C star hstar
    (fun v hv w hw hadj =>
      eq_star_of_adj_mem_compl hreg' (by omega) hQI hQreg hv hw hadj (hstar v hv))
    y.property z.property (by simpa [ystar, zstar] using hneC)

/-- Longer odd-cycle assembly of Rabern surgery (`C₅`, `C₇`, …). -/
private theorem brooksSurgery_longOddCycle
    {V : Type u} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    {Δ : ℕ} (hΔeq : Δ = 3) (hΔ3 : 3 ≤ Δ) (_hcf : G.CliqueFree (Δ + 1))
    (hH : ¬ cliqueMinusEdge (Δ - 1) ⊑ G) (hreg' : G.IsRegularOfDegree Δ)
    {I : Set V} (hI : Maximal G.IsIndepSet I) [DecidablePred (· ∈ I)]
    {k : ℕ} (hcardV : Fintype.card V ≤ k + 1)
    (ih : ∀ {V : Type u} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      Fintype.card V ≤ k → G.CliqueFree (G.maxDegree + 1) →
        (G.maxDegree = 2 → ¬G.HasOddCycle) → G.Colorable G.maxDegree)
    (hΔ2 : (G.induce (Iᶜ : Set V)).maxDegree = 2)
    {v0 : ↥(Iᶜ : Set V)} {c : (G.induce (Iᶜ : Set V)).Walk v0 v0}
    (hc : c.IsCycle) (hlen : Odd c.length) (htri : c.length ≠ 3) :
    G.Colorable Δ := by
  classical
  have hlen_ge : 5 ≤ c.length := by
    have h3le := hc.three_le_length
    rcases hlen with ⟨t, ht⟩
    omega
  let φ : G.induce (Iᶜ : Set V) →g G := (Embedding.induce (G := G) (Iᶜ : Set V)).toHom
  let cG : G.Walk (φ v0) (φ v0) := c.map φ
  have hcG : cG.IsCycle :=
    (Walk.isCycle_map_iff_of_injective (G := G.induce (Iᶜ : Set V)) (G' := G)
      Subtype.val_injective).2 hc
  let Qf : Finset V := cG.support.toFinset
  let Q : Set V := ↑Qf
  have : DecidablePred (· ∈ Q) := Classical.decPred _
  have hQI : Q ⊆ (Iᶜ : Set V) := by
    intro x hx
    have hx' : x ∈ cG.support := List.mem_toFinset.1 (by simpa [Q, Qf] using hx)
    have hx'' : x ∈ c.support.map φ := by simpa [cG, Walk.support_map] using hx'
    rcases List.mem_map.1 hx'' with ⟨y, _, rfl⟩
    exact y.property
  have hQcard_len : Q.ncard = c.length := by
    rw [Set.ncard_coe_finset]
    change cG.support.toFinset.card = c.length
    rw [hcG.support_toFinset_card]
    simp [cG, Walk.length_map]
  have hQne : Nonempty ↥Q :=
    Set.Nonempty.to_subtype ((Set.ncard_pos).1 (by omega : 0 < Q.ncard))
  have mem_support_of_mem_Q {x : V} (hx : x ∈ Q) : x ∈ cG.support :=
    List.mem_toFinset.1 (by simpa [Q, Qf] using hx)
  have mem_Q_of_mem_support {x : V} (hx : x ∈ cG.support) : x ∈ Q := by
    simpa [Q, Qf] using List.mem_toFinset.2 hx
  -- 2-regularity under maxDegree 2.
  have hQreg : (G.induce Q).IsRegularOfDegree (Δ - 1) := by
    rw [show Δ - 1 = 2 by omega]
    intro v
    refine le_antisymm ?_ ?_
    · have hvI : (v : V) ∈ (Iᶜ : Set V) := hQI v.property
      let vI : ↥(Iᶜ : Set V) := ⟨↑v, hvI⟩
      have hsub :
          ((G.induce Q).neighborFinset v).map (Function.Embedding.subtype (· ∈ Q)) ⊆
            ((G.induce (Iᶜ : Set V)).neighborFinset vI).map
              (Function.Embedding.subtype (· ∈ (Iᶜ : Set V))) := by
        intro x hx
        rcases Finset.mem_map.1 hx with ⟨a, ha, rfl⟩
        have hadj : G.Adj ↑v ↑a := (mem_neighborFinset (G.induce Q) _ _).1 ha
        refine Finset.mem_map.2 ⟨⟨↑a, hQI a.property⟩, ?_, rfl⟩
        exact (mem_neighborFinset (G.induce (Iᶜ : Set V)) _ _).2 hadj
      have hle := Finset.card_le_card hsub
      rw [Finset.card_map, Finset.card_map, card_neighborFinset_eq_degree,
        card_neighborFinset_eq_degree] at hle
      exact hle.trans ((G.induce (Iᶜ : Set V)).degree_le_maxDegree vI |>.trans_eq hΔ2)
    · have hvsupp : (v : V) ∈ cG.support := mem_support_of_mem_Q v.property
      have hn : (cG.toSubgraph.neighborSet ↑v).ncard = 2 :=
        hcG.ncard_neighborSet_toSubgraph_eq_two hvsupp
      let N := (cG.toSubgraph.neighborSet ↑v).toFinset
      have hNcard : N.card = 2 := by simpa [N, ← Set.ncard_eq_toFinset_card'] using hn
      have hsub : N ⊆ ((G.induce Q).neighborFinset v).map
          (Function.Embedding.subtype (· ∈ Q)) := by
        intro w hw
        have hadj : cG.toSubgraph.Adj ↑v w := by simpa [N, Set.mem_toFinset] using hw
        have hwsupp : w ∈ cG.support :=
          cG.mem_verts_toSubgraph.1 (cG.toSubgraph.edge_vert hadj.symm)
        refine Finset.mem_map.2 ⟨⟨w, mem_Q_of_mem_support hwsupp⟩, ?_, rfl⟩
        exact (mem_neighborFinset (G.induce Q) _ _).2 (cG.toSubgraph.adj_sub hadj)
      have hle := Finset.card_le_card hsub
      rwa [hNcard, Finset.card_map, card_neighborFinset_eq_degree] at hle
  have hQconn : (G.induce Q).Connected := by
    refine (connected_iff _).2 ⟨?_, hQne⟩
    intro a b
    have ha : ↑a ∈ cG.support := mem_support_of_mem_Q a.property
    have hb : ↑b ∈ cG.support := mem_support_of_mem_Q b.property
    let cRot := cG.rotate ↑a ha
    have hb' : ↑b ∈ cRot.support := (Walk.mem_support_rotate_iff _ _ _).2 hb
    let pG := cRot.takeUntil ↑b hb'
    have hpsupp : ∀ x ∈ pG.support, x ∈ Q := fun x hx =>
      mem_Q_of_mem_support ((Walk.mem_support_rotate_iff _ _ _).1
        (Walk.support_takeUntil_subset_support cRot hb' hx))
    exact ⟨pG.induce Q hpsupp⟩
  have hΔ1 : 1 ≤ Δ := by simp [hΔeq]
  have hstarU : ∀ v ∈ Q, ∃! w, w ∈ I ∧ G.Adj v w := fun v hv =>
    existsUnique_adj_mem_of_isRegular hΔ1 hreg' hI hQI (by convert hQreg) v hv
  let star : V → V := fun v =>
    if hv : v ∈ Q then Classical.choose (hstarU v hv).exists else v
  have hstar : ∀ v ∈ Q, star v ∈ I ∧ G.Adj v (star v) := by
    intro v hv
    simpa [star, hv] using Classical.choose_spec (hstarU v hv).exists
  have hstar_ne : ∃ y ∈ Q, ∃ z ∈ Q, star y ≠ star z := by
    by_contra h
    push Not at h
    obtain ⟨y0⟩ := hQne
    have hadjAll : ∀ v ∈ Qf, G.Adj v (star ↑y0) := fun v hv => by
      have hvQ : v ∈ Q := by simpa [Q] using hv
      exact (h v hvQ ↑y0 y0.property) ▸ (hstar v hvQ).2
    have hcard_le : Qf.card ≤ G.degree (star ↑y0) := by
      have hsub : Qf ⊆ G.neighborFinset (star ↑y0) := fun v hv =>
        (mem_neighborFinset _ _ _).2 (hadjAll v hv).symm
      exact (Finset.card_le_card hsub).trans_eq (by rw [card_neighborFinset_eq_degree])
    have : Q.ncard ≤ Δ := by
      simpa [Set.ncard_coe_finset, Q, hreg' (star ↑y0)] using hcard_le
    omega
  obtain ⟨y0, hy0, z0, hz0, hne0⟩ := hstar_ne
  obtain ⟨y, z, hyzAdjQ, hstars_ne⟩ :=
    Connected.exists_adj_ne_of_ne hQconn (fun v : ↥Q => star ↑v)
      (show star ↑(⟨y0, hy0⟩ : ↥Q) ≠ star ↑(⟨z0, hz0⟩ : ↥Q) from hne0)
  set ystar := star ↑y
  set zstar := star ↑z
  have hyAdj : G.Adj ↑y ystar := (hstar _ y.property).2
  have hzAdj : G.Adj ↑z zstar := (hstar _ z.property).2
  have hystar_Qc : ystar ∈ (Qᶜ : Set V) := fun h =>
    absurd (hstar _ y.property).1 (Set.notMem_of_mem_compl (hQI h))
  have hzstar_Qc : zstar ∈ (Qᶜ : Set V) := fun h =>
    absurd (hstar _ z.property).1 (Set.notMem_of_mem_compl (hQI h))
  have hcardQc : Fintype.card ↥(Qᶜ : Set V) ≤ k := by
    have hsplit := Fintype.card_compl_set Q
    have hQcardF : Fintype.card ↥Q = Q.ncard := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    have : 1 ≤ Fintype.card ↥Q := by rw [hQcardF]; omega
    omega
  obtain ⟨Cstar⟩ := colorable_surgery_graph (G := G) hΔ3 hH hreg' hcardQc ih
    hystar_Qc hzstar_Qc hstars_ne y.property z.property hyAdj hzAdj
  let C : (G.induce (Qᶜ : Set V)).Coloring (Fin Δ) :=
    Cstar.comp (.ofLE le_sup_left)
  have hneC :
      C ⟨ystar, hystar_Qc⟩ ≠ C ⟨zstar, hzstar_Qc⟩ := by
    have hadj :
        (G.induce (Qᶜ : Set V) ⊔
          edge (⟨ystar, hystar_Qc⟩ : ↥(Qᶜ : Set V)) ⟨zstar, hzstar_Qc⟩).Adj
          ⟨ystar, hystar_Qc⟩ ⟨zstar, hzstar_Qc⟩ := by
      refine Or.inr ?_
      rw [edge_adj]
      exact ⟨Or.inl ⟨rfl, rfl⟩, fun h => hstars_ne (congrArg Subtype.val h)⟩
    simpa [C] using Cstar.valid hadj
  -- Spanning cycle in `induce Q` based at `y`.
  have hy_supp : ↑y ∈ cG.support := mem_support_of_mem_Q y.property
  let cGy : G.Walk ↑y ↑y := cG.rotate ↑y hy_supp
  have hcGy : cGy.IsCycle := hcG.rotate hy_supp
  have hsuppGy : ∀ x ∈ cGy.support, x ∈ Q := fun x hx =>
    mem_Q_of_mem_support ((Walk.mem_support_rotate_iff _ _ _).1 hx)
  let cQ : (G.induce Q).Walk y y := cGy.induce Q hsuppGy
  have hcQ : cQ.IsCycle := by
    have hmap : cQ.map (Embedding.induce (G := G) Q).toHom = cGy := by
      simpa [cQ] using Walk.map_induce cGy hsuppGy
    exact (Walk.isCycle_map_iff_of_injective (G := G.induce Q) (G' := G)
      Subtype.val_injective).1 (hmap.symm ▸ hcGy)
  have hspanQ : ∀ t : ↥Q, t ∈ cQ.support := by
    intro t
    have ht : ↑t ∈ cGy.support :=
      (Walk.mem_support_rotate_iff _ _ _).2 (mem_support_of_mem_Q t.property)
    simpa [cQ, Walk.support_induce, List.mem_attachWith] using ht
  have hyzAdjG : G.Adj ↑y ↑z := hyzAdjQ
  -- Cycle subgraph neighbours at `y` coincide with `induce Q` neighbours.
  have hadj_cycleG : cGy.toSubgraph.Adj ↑y ↑z := by
    have hnY : (cGy.toSubgraph.neighborSet ↑y).ncard = 2 :=
      hcGy.ncard_neighborSet_toSubgraph_eq_two cGy.start_mem_support
    have himage :
        cGy.toSubgraph.neighborSet ↑y ⊆
          Subtype.val '' ((G.induce Q).neighborSet y) := by
      intro w hw
      have hadj : cGy.toSubgraph.Adj ↑y w := hw
      have hwsupp : w ∈ cGy.support :=
        cGy.mem_verts_toSubgraph.1 (cGy.toSubgraph.edge_vert hadj.symm)
      refine ⟨⟨w, hsuppGy w hwsupp⟩, ?_, rfl⟩
      exact (mem_neighborSet (G.induce Q) _ _).2 (cGy.toSubgraph.adj_sub hadj)
    have hcard_image :
        (Subtype.val '' ((G.induce Q).neighborSet y)).ncard = 2 := by
      have hdeg : (G.induce Q).degree y = 2 := by
        simpa [show Δ - 1 = 2 by omega] using hQreg y
      rw [Set.ncard_image_of_injective _ Subtype.val_injective]
      have : ((G.induce Q).neighborSet y).ncard = (G.induce Q).degree y := by
        rw [Set.ncard_eq_toFinset_card', ← card_neighborFinset_eq_degree]
        rfl
      rw [this, hdeg]
    have heq : cGy.toSubgraph.neighborSet ↑y =
        Subtype.val '' ((G.induce Q).neighborSet y) :=
      Set.eq_of_subset_of_ncard_le himage (by rw [hcard_image, hnY]) (Set.toFinite _)
    exact (heq ▸ ⟨z, (mem_neighborSet _ _ _).2 hyzAdjQ, rfl⟩ :
      ↑z ∈ cGy.toSubgraph.neighborSet ↑y)
  have hadj_cycleQ : cQ.toSubgraph.Adj y z := by
    have hmap : cQ.map (Embedding.induce (G := G) Q).toHom = cGy := by
      simpa [cQ] using Walk.map_induce cGy hsuppGy
    have heq : cGy.toSubgraph =
        cQ.toSubgraph.map (Embedding.induce (G := G) Q).toHom := by
      rw [← hmap]
      exact Walk.toSubgraph_map (Embedding.induce (G := G) Q).toHom cQ
    have h := hadj_cycleG
    rw [heq, Subgraph.map_adj] at h
    obtain ⟨y', z', hadj, hy', hz'⟩ := h
    obtain rfl := Subtype.ext hy'
    obtain rfl := Subtype.ext hz'
    exact hadj
  obtain ⟨cQ', hcQ', hsnd, hverts⟩ := hcQ.exists_isCycle_snd_verts_eq hadj_cycleQ
  have hspanQ' : ∀ t : ↥Q, t ∈ cQ'.support := fun t => by
    rw [← Walk.mem_verts_toSubgraph, hverts, Walk.mem_verts_toSubgraph]
    exact hspanQ t
  obtain ⟨pQ0, hpQ0⟩ :=
    exists_isHamiltonian_walk_of_isCycle_snd (c := cQ') hcQ' hspanQ'
  let pQ : (G.induce Q).Walk y z := by
    rw [← hsnd]; exact pQ0
  have hpQ : pQ.IsHamiltonian := by
    subst hsnd; exact hpQ0
  let p : G.Walk ↑y ↑z := pQ.map (Embedding.induce (G := G) Q).toHom
  have hp : p.IsPath :=
    (Walk.isPath_map_iff_of_injective Subtype.val_injective).2 hpQ.isPath
  have hspan : p.support.toFinset = Qf := by
    ext x
    constructor
    · intro hx
      have hxsup : x ∈ (pQ.map (Embedding.induce (G := G) Q).toHom).support := by
        simpa [p] using List.mem_toFinset.1 hx
      rw [Walk.support_map] at hxsup
      rcases List.mem_map.1 hxsup with ⟨x', _, rfl⟩
      simpa [Q, Qf] using x'.property
    · intro hx
      have hxQ : x ∈ Q := by simpa [Q] using hx
      have hxmem : (⟨x, hxQ⟩ : ↥Q) ∈ pQ.support := hpQ.mem_support _
      refine List.mem_toFinset.2 ?_
      change x ∈ (pQ.map (Embedding.induce (G := G) Q).toHom).support
      rw [Walk.support_map]
      exact List.mem_map.2 ⟨⟨x, hxQ⟩, hxmem, rfl⟩
  have : NeZero Δ := ⟨by omega⟩
  have hstarQc : ∀ v ∈ Qf, star v ∈ ((↑Qf : Set V)ᶜ) := fun v hv => by
    have hvQ : v ∈ Q := by simpa [Q] using hv
    exact fun h => absurd (hstar v hvQ).1 (Set.notMem_of_mem_compl (hQI h))
  have hstarAdj' : ∀ v ∈ Qf, G.Adj v (star v) := fun v hv =>
    (hstar v (by simpa [Q] using hv)).2
  have honly : ∀ v ∈ Qf, ∀ w ∈ ((↑Qf : Set V)ᶜ), G.Adj v w → w = star v :=
    fun v hv w hw hadj =>
      eq_star_of_adj_mem_compl hreg' hΔ1 hQI (by convert hQreg)
        (by simpa [Q] using hv) (by simpa [Q] using hw) hadj
        (hstar v (by simpa [Q] using hv))
  have hdeg : ∀ v ∈ Qf, (G.neighborFinset v).card ≤ Δ := fun v _ => by
    rw [card_neighborFinset_eq_degree, hreg' v]
  let C' : (G.induce ((↑Qf : Set V)ᶜ)).Coloring (Fin Δ) := by convert C
  have hne' :
      C' ⟨star ↑y, hstarQc ↑y (by simpa [Q, Qf] using y.property)⟩ ≠
        C' ⟨star ↑z, hstarQc ↑z (by simpa [Q, Qf] using z.property)⟩ := by
    change C ⟨ystar, hystar_Qc⟩ ≠ C ⟨zstar, hzstar_Qc⟩
    exact hneC
  exact Colorable.of_rabern_path_extension (n := Δ) (Q := Qf) p hp hspan C' star
    hstarQc hstarAdj' honly hyzAdjG hne' hdeg

/-- Core of Rabern's surgery: given a maximal independent set whose deletion yields a Brooks
counterexample containing `K_Δ` or an odd cycle, colour `G` with `Δ` colours. -/
private theorem brooksSurgery
    {V : Type u} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    {Δ : ℕ} (hΔdef : Δ = G.maxDegree) (hΔ3 : 3 ≤ Δ)
    (hcf : G.CliqueFree (Δ + 1)) (hH : ¬ cliqueMinusEdge (Δ - 1) ⊑ G)
    (hreg' : G.IsRegularOfDegree Δ)
    {I : Set V} (hI : Maximal G.IsIndepSet I)
    [DecidablePred (· ∈ I)] [Nonempty ↥(Iᶜ : Set V)]
    (hΔ'eq : (G.induce (Iᶜ : Set V)).maxDegree = Δ - 1)
    {k : ℕ} (hcardV : Fintype.card V ≤ k + 1)
    (_hcard' : Fintype.card ↥(Iᶜ : Set V) ≤ k)
    (hQcase : ¬ (G.induce (Iᶜ : Set V)).CliqueFree Δ ∨
      ((G.induce (Iᶜ : Set V)).maxDegree = 2 ∧ (G.induce (Iᶜ : Set V)).HasOddCycle))
    (ih : ∀ {V : Type u} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      Fintype.card V ≤ k → G.CliqueFree (G.maxDegree + 1) →
        (G.maxDegree = 2 → ¬G.HasOddCycle) → G.Colorable G.maxDegree) :
    G.Colorable Δ := by
  classical
  rcases hQcase with hNotCF | ⟨hΔ2, hoddQ⟩
  · obtain ⟨ψ⟩ := (not_cliqueFree_iff_top_isContained Δ).1 hNotCF
    obtain ⟨Q, hQI, hQcard, hQclique⟩ := exists_clique_set_of_copy (I := I) ψ
    exact brooksSurgery_clique (G := G) hΔ3 hcf hH hreg' hI hcardV ih Q hQI hQcard hQclique
  · -- Odd-cycle case: necessarily `Δ = 3`.
    have hΔeq : Δ = 3 := by omega
    obtain ⟨v0, c, hc, hlen⟩ := hoddQ
    by_cases htri : c.length = 3
    · -- Triangle in `G'`: lift to a `K_3` in `G` and use the clique block.
      obtain ⟨s, hs⟩ :=
        (is3Clique_iff_exists_cycle_length_three
          (G := G.induce (Iᶜ : Set V))).2 ⟨v0, c, hc, htri⟩
      let Q : Set V := ↑(Finset.map ⟨Subtype.val, Subtype.val_injective⟩ s)
      have : DecidablePred (· ∈ Q) := Classical.decPred _
      have hQI : Q ⊆ (Iᶜ : Set V) := by
        intro x hx
        have hx' : x ∈ Finset.map ⟨Subtype.val, Subtype.val_injective⟩ s := by
          simpa [Q] using hx
        rcases Finset.mem_map.1 hx' with ⟨⟨_, hxI⟩, _, rfl⟩
        exact hxI
      have hQcard : Q.ncard = Δ := by
        rw [Set.ncard_coe_finset, Finset.card_map, hs.card_eq, hΔeq]
      have hQclique : G.IsClique Q := by
        intro a ha b hb hne
        have ha' : a ∈ Finset.map ⟨Subtype.val, Subtype.val_injective⟩ s := by
          simpa [Q] using ha
        have hb' : b ∈ Finset.map ⟨Subtype.val, Subtype.val_injective⟩ s := by
          simpa [Q] using hb
        rcases Finset.mem_map.1 ha' with ⟨a', haS, rfl⟩
        rcases Finset.mem_map.1 hb' with ⟨b', hbS, rfl⟩
        have hne' : a' ≠ b' := fun h => hne (congrArg Subtype.val h)
        exact hs.isClique haS hbS hne'
      exact brooksSurgery_clique (G := G) hΔ3 hcf hH hreg' hI hcardV ih Q hQI hQcard hQclique
    · -- Longer odd cycle: Rabern path endgame.
      exact brooksSurgery_longOddCycle (G := G) hΔeq hΔ3 hcf hH hreg' hI hcardV ih hΔ2 hc hlen htri



private theorem brooksAux :
    ∀ (m : ℕ) {V : Type u} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      Fintype.card V ≤ m → G.CliqueFree (G.maxDegree + 1) →
      (G.maxDegree = 2 → ¬G.HasOddCycle) → G.Colorable G.maxDegree := by
  intro m
  induction m with
  | zero =>
    intro V G _ _ hcard _ _
    have : IsEmpty V := Fintype.card_eq_zero_iff.1 (by lia)
    exact .of_isEmpty _
  | succ k ih =>
    intro V G _ _ hcard hcf hodd
    classical
    rcases le_or_gt G.maxDegree 2 with h2 | h3
    · exact colorable_maxDegree_of_maxDegree_le_two h2 hcf hodd
    have hΔ3 : 3 ≤ G.maxDegree := h3
    set Δ := G.maxDegree with hΔdef
    rcases em (cliqueMinusEdge (Δ - 1) ⊑ G) with hH | hH
    · -- STEP 2: colouring when `G` contains `K⁻_{Δ+1}`.
      obtain ⟨φ⟩ := hH
      let S : Set V := Set.range φ
      have hcard' : Fintype.card ↥(Sᶜ : Set V) ≤ k := by
        have := Fintype.card_compl_set S
        have hS : Fintype.card ↥S = Δ + 1 := by
          dsimp [S]
          rw [Set.card_range_of_injective (f := (φ : Fin (Δ - 1 + 2) → V)) φ.injective,
            Fintype.card_fin]
          omega
        omega
      have hΔ' : (G.induce (Sᶜ : Set V)).maxDegree ≤ Δ := by
        simpa [Δ] using Copy.maxDegree_mono (Embedding.induce (Sᶜ : Set V)).toCopy
      have hcf' : (G.induce (Sᶜ : Set V)).CliqueFree (Δ + 1) := by
        intro t ht
        exact hcf _ ((isNClique_induce_iff _ t _).1 ht)
      have hcol' : (G.induce (Sᶜ : Set V)).Colorable Δ :=
        colorable_of_card_le_of_maxDegree_le (fun G => ih G) (G.induce (Sᶜ : Set V))
          hcard' hΔ3 hΔ' hcf'
      simpa [Δ] using
        Colorable.of_cliqueMinusEdge_copy (G := G) hΔ3 (le_of_eq hΔdef.symm) hcf φ hcol'
    rcases em (∃ v, G.degree v < Δ) with ⟨v, hv⟩ | hreg
    · have hcard' : Fintype.card ↥({v}ᶜ : Set V) ≤ k := by
        have := Fintype.card_compl_set ({v} : Set V)
        simp only [Set.card_singleton] at this
        omega
      have hΔ' : (G.induce ({v}ᶜ : Set V)).maxDegree ≤ Δ := by
        simpa [Δ] using Copy.maxDegree_mono (Embedding.induce ({v}ᶜ : Set V)).toCopy
      have hcf' : (G.induce ({v}ᶜ : Set V)).CliqueFree (Δ + 1) := by
        intro t ht
        exact hcf _ ((isNClique_induce_iff _ t _).1 ht)
      have hcol' : (G.induce ({v}ᶜ : Set V)).Colorable Δ :=
        colorable_of_card_le_of_maxDegree_le (fun G => ih G) (G.induce ({v}ᶜ))
          hcard' hΔ3 hΔ' hcf'
      simpa [Δ] using Colorable.of_induce_compl_singleton hcol' hv
    push Not at hreg
    have hreg' : G.IsRegularOfDegree Δ :=
      isRegularOfDegree_maxDegree_of_forall_le (by simpa [Δ] using hreg)
    obtain ⟨I, hI⟩ := exists_maximal_isIndepSet G
    -- Surgery endgame (Rabern).
    have hVne : Nonempty V := by
      by_contra hEmpty
      rw [not_nonempty_iff] at hEmpty
      have h0 : G.maxDegree = 0 := by simp [maxDegree]
      omega
    have hI_nonempty : I.Nonempty := by
      by_contra hIempty
      rw [Set.not_nonempty_iff_eq_empty] at hIempty
      rw [hIempty] at hI
      obtain ⟨v⟩ := hVne
      have hindep : G.IsIndepSet ({v} : Set V) := by
        simp [IsIndepSet, Set.pairwise_singleton]
      exact absurd (hI.2 hindep (Set.empty_subset _) (Set.mem_singleton v)) (by simp)
    have hIc_nonempty : (Iᶜ : Set V).Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
      obtain ⟨v⟩ := hVne
      have hdeg0 : G.degree v = 0 := by
        rw [← card_neighborFinset_eq_degree]
        apply Finset.card_eq_zero.2
        ext w
        simp only [Finset.notMem_empty, mem_neighborFinset, iff_false]
        intro hadj
        exact hI.1 (by rw [h]; trivial) (by rw [h]; trivial) hadj.ne hadj
      have hdegΔ : G.degree v = Δ := hreg' v
      omega
    let G' : SimpleGraph ↥(Iᶜ : Set V) := G.induce (Iᶜ : Set V)
    have : Nonempty ↥(Iᶜ : Set V) := hIc_nonempty.to_subtype
    have hΔ'lt : G'.maxDegree < Δ := by
      simpa [G', Δ] using maxDegree_induce_compl_lt_of_maximal (G := G) hI
    by_cases hEasy : G'.Colorable (Δ - 1)
    · have hcol := Colorable.of_induce_compl_isIndepSet hI.1 hEasy
      have : Δ - 1 + 1 = Δ := by omega
      exact this ▸ hcol
    · have hΔ'eq : G'.maxDegree = Δ - 1 := by
        have hle : G'.maxDegree ≤ Δ - 1 := Nat.le_sub_one_of_lt hΔ'lt
        refine le_antisymm hle ?_
        by_contra hlt
        push Not at hlt
        exact hEasy (Colorable.mono (by omega) G'.colorable_maxDegree_succ)
      have hcard' : Fintype.card ↥(Iᶜ : Set V) ≤ k := by
        have hsplit := Fintype.card_compl_set I
        have hIpos : 0 < Fintype.card ↥I := by
          rw [Fintype.card_pos_iff]; exact hI_nonempty.to_subtype
        omega
      have hnot : ¬ G'.Colorable G'.maxDegree := by simpa [hΔ'eq] using hEasy
      have hQcase :
          (¬ G'.CliqueFree Δ) ∨ (G'.maxDegree = 2 ∧ G'.HasOddCycle) := by
        by_cases hcf' : G'.CliqueFree (G'.maxDegree + 1)
        · by_cases hodd' : G'.maxDegree = 2 → ¬ G'.HasOddCycle
          · exact absurd (ih G' hcard' hcf' hodd') hnot
          · push Not at hodd'
            exact Or.inr hodd'
        · left
          have : G'.maxDegree + 1 = Δ := by omega
          simpa [this] using hcf'
      exact brooksSurgery (G := G) hΔdef hΔ3 hcf hH hreg' hI hΔ'eq hcard hcard' hQcase
        (fun {V} G => @ih V G)

/-- **Brooks' theorem** (Rabern's form). -/
theorem brooks (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (h : ¬ G.Colorable G.maxDegree) :
    ¬ G.CliqueFree (G.maxDegree + 1) ∨ (G.maxDegree = 2 ∧ G.HasOddCycle) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hcf, hodd⟩ := hcon
  exact h (brooksAux _ G le_rfl hcf fun h2 => (hodd h2).elim)

end SimpleGraph
