import ErdosProblems.Erdos570.BondyChvatal

/-!
# Deterministic Hamiltonicity tools for Erdős Problem 622

This file contains endpoint-sensitive Hamiltonicity lemmas used in the
Draganić--Keevash--Müyesser argument.  In particular, it records the elementary
cycle-splicing operation separately from the degree estimates that produce the
two splice edges.
-/

open Finset

namespace Erdos622

namespace Hamiltonicity

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Closing the endpoints of a Hamilton path by one edge gives a Hamilton
cycle, provided the graph has at least three vertices. -/
theorem isHamiltonianCycle_cons_of_isHamiltonian
    {a b : V} {p : G.Walk a b} (hp : p.IsHamiltonian)
    (hV : 3 ≤ Fintype.card V) (hba : G.Adj b a) :
    (p.cons hba).IsHamiltonianCycle := by
  have hedge : s(b, a) ∉ p.edges := by
    intro hedge
    have hlength : p.length = 1 := by
      apply hp.isPath.length_eq_one_of_mem_edges
      simpa only [Sym2.eq_swap] using hedge
    rw [hp.length_eq] at hlength
    omega
  refine ⟨(SimpleGraph.Walk.cons_isCycle_iff p hba).mpr ⟨hp.isPath, hedge⟩, ?_⟩
  intro v
  rw [SimpleGraph.Walk.support_tail_of_not_nil _ (by simp),
    SimpleGraph.Walk.support_cons, List.tail_cons]
  exact hp v

/-- Splice two vertices outside `s` onto the two ends of the path obtained by
cutting a Hamilton cycle of `G[s]` at its base vertex.

The hypothesis involving `q.snd` says that the first edge after the cut joins
to `a`; the other splice edge joins the base vertex to `b`. -/
theorem isHamiltonian_splice_induced_cycle
    {s : Set V} {x : s} {a b : V}
    (q : (G.induce s).Walk x x) (hq : q.IsHamiltonianCycle)
    (ha : a ∉ s) (hb : b ∉ s) (hab : a ≠ b)
    (hcover : ∀ v : V, v ∈ s ∨ v = a ∨ v = b)
    (haq : G.Adj a q.snd.1) (hqb : G.Adj x.1 b) :
    ∃ p : G.Walk a b, p.IsHamiltonian := by
  let e : (G.induce s) →g G := (SimpleGraph.Embedding.induce s).toHom
  let r : G.Walk q.snd.1 x.1 := q.tail.map e
  let p : G.Walk a b := (r.cons haq).concat hqb
  refine ⟨p, ?_⟩
  have hrPath : r.IsPath := by
    exact hq.isHamiltonian_tail.isPath.map
      (SimpleGraph.Embedding.induce (G := G) s).injective
  have ha_not_mem : a ∉ r.support := by
    intro ha_mem
    change a ∈ (q.tail.map e).support at ha_mem
    rw [SimpleGraph.Walk.support_map] at ha_mem
    obtain ⟨z, -, hz⟩ := List.mem_map.mp ha_mem
    exact ha (hz ▸ z.2)
  have hb_not_mem : b ∉ (r.cons haq).support := by
    intro hb_mem
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hb_mem
    rcases hb_mem with hba | hb_mem
    · exact hab hba.symm
    · change b ∈ (q.tail.map e).support at hb_mem
      rw [SimpleGraph.Walk.support_map] at hb_mem
      obtain ⟨z, -, hz⟩ := List.mem_map.mp hb_mem
      exact hb (hz ▸ z.2)
  have hpPath : p.IsPath := by
    exact (hrPath.cons ha_not_mem).concat hb_not_mem hqb
  apply hpPath.isHamiltonian_of_mem
  intro v
  rcases hcover v with hv | rfl | rfl
  · have hvq : (⟨v, hv⟩ : s) ∈ q.tail.support :=
      hq.isHamiltonian_tail.mem_support ⟨v, hv⟩
    have hvr : v ∈ r.support := by
      change v ∈ (q.tail.map e).support
      rw [SimpleGraph.Walk.support_map]
      exact List.mem_map.mpr ⟨⟨v, hv⟩, hvq, rfl⟩
    exact SimpleGraph.Walk.support_subset_support_concat _ _
      (List.mem_cons_of_mem _ hvr)
  · exact p.start_mem_support
  · exact p.end_mem_support

/-- Two subsets of a finite ambient type whose cardinalities sum to more than
the order of the type intersect. -/
private theorem exists_mem_inter_of_card_lt_add {W : Type*} [Fintype W]
    [DecidableEq W] {A B : Finset W}
    (hcard : Fintype.card W < A.card + B.card) :
    ∃ x, x ∈ A ∧ x ∈ B := by
  by_contra h
  push Not at h
  have hdisj : Disjoint A B := Finset.disjoint_left.mpr h
  have hunion : A ∪ B ⊆ (Finset.univ : Finset W) := Finset.subset_univ _
  have hle := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_univ] at hle
  omega

/-- A cardinal form of the cycle-splicing argument.  If the two endpoint
neighbourhoods inside `s` have total size larger than `|s|`, then a Hamilton
cycle of `G[s]` can be cut and spliced into a Hamilton `a`--`b` path in `G`.

This formulation is convenient in applications: all degree bookkeeping is
isolated in the single strict cardinal inequality. -/
theorem exists_isHamiltonianPath_of_induced_cycle_of_card_lt_add
    {s : Set V} [Fintype s] {x : s} {a b : V}
    (q : (G.induce s).Walk x x) (hq : q.IsHamiltonianCycle)
    (ha : a ∉ s) (hb : b ∉ s) (hab : a ≠ b)
    (hcover : ∀ v : V, v ∈ s ∨ v = a ∨ v = b)
    (hcard : Fintype.card s <
      ((Finset.univ : Finset s).filter fun z ↦ G.Adj a z.1).card +
        ((Finset.univ : Finset s).filter fun z ↦ G.Adj z.1 b).card) :
    ∃ p : G.Walk a b, p.IsHamiltonian := by
  let A : Finset s := (Finset.univ : Finset s).filter fun z ↦ G.Adj a z.1
  let B : Finset s := (Finset.univ : Finset s).filter fun z ↦ G.Adj z.1 b
  let nextB : Finset s := B.image hq.next
  have hnext_card : nextB.card = B.card := by
    exact Finset.card_image_of_injective _ hq.next_inj
  have hinter : ∃ y, y ∈ A ∧ y ∈ nextB := by
    apply exists_mem_inter_of_card_lt_add
    simpa only [A, B, nextB, hnext_card] using hcard
  obtain ⟨y, hyA, hyNext⟩ := hinter
  obtain ⟨z, hzB, hzNext⟩ := Finset.mem_image.mp hyNext
  have hzSupport : z ∈ q.support := hq.mem_support z
  let r := q.rotate z hzSupport
  have hr : r.IsHamiltonianCycle := hq.rotate hzSupport
  have hr_snd : r.snd = y := by
    have hlen : 0 < r.length :=
      SimpleGraph.Walk.not_nil_iff_lt_length.mp hr.isCycle.not_nil
    have hnext : r.getVert 1 = hr.next z :=
      hr.getVert_succ_eq_next z (i := 0) hlen (by simp [r])
    have hrot : hr.next z = hq.next z := by
      exact SimpleGraph.Walk.IsHamiltonianCycle.rotate_next z hq hzSupport z
    exact hnext.trans (hrot.trans hzNext)
  apply isHamiltonian_splice_induced_cycle r hr ha hb hab hcover
  · rw [hr_snd]
    simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using hyA
  · simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using hzB

private def pairComplement (a b : V) : Finset V :=
  ((Finset.univ : Finset V).erase a).erase b

private theorem card_pairComplement {a b : V} (hab : a ≠ b) :
    (pairComplement a b).card = Fintype.card V - 2 := by
  rw [pairComplement, Finset.card_erase_of_mem (by simpa [hab] using hab.symm),
    Finset.card_erase_of_mem (by simp)]
  rw [Finset.card_univ]
  omega

private theorem pairComplement_cover {a b v : V} :
    v ∈ (pairComplement a b : Set V) ∨ v = a ∨ v = b := by
  simp only [pairComplement, Finset.coe_erase, Finset.coe_univ, Set.mem_sdiff,
    Set.mem_univ, Set.mem_singleton_iff, true_and]
  tauto

private theorem pairComplement_not_mem_left {a b : V} :
    a ∉ (pairComplement a b : Set V) := by
  simp [pairComplement]

private theorem pairComplement_not_mem_right {a b : V} :
    b ∉ (pairComplement a b : Set V) := by
  simp [pairComplement]

/-- Deleting two vertices removes at most two neighbours of every surviving
vertex.  The inequality is phrased with truncated subtraction, so it is valid
without a separate lower bound on the original degree. -/
theorem degree_sub_two_le_degree_induce_pairComplement {a b : V}
    (z : (pairComplement a b : Set V)) :
    G.degree z.1 - 2 ≤ (G.induce (pairComplement a b : Set V)).degree z := by
  let T : Finset V := ((G.neighborFinset z.1).erase a).erase b
  have hmap :
      ((G.induce (pairComplement a b : Set V)).neighborFinset z).map
          (Function.Embedding.subtype fun v ↦ v ∈ (pairComplement a b : Set V)) = T := by
    ext v
    constructor
    · intro hv
      obtain ⟨w, hw, hwv⟩ := Finset.mem_map.mp hv
      subst v
      have hadj : G.Adj z.1 w.1 :=
        SimpleGraph.induce_adj.mp
          ((G.induce (pairComplement a b : Set V)).mem_neighborFinset z w |>.mp hw)
      have hwmem : w.1 ≠ a ∧ w.1 ≠ b := by
        simpa [pairComplement] using w.2
      simp only [T, Finset.mem_erase, SimpleGraph.mem_neighborFinset]
      exact ⟨hwmem.2, hwmem.1, hadj⟩
    · intro hv
      simp only [T, Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hv
      let w : (pairComplement a b : Set V) := ⟨v, by
        simp [pairComplement, hv.1, hv.2.1]⟩
      apply Finset.mem_map.mpr
      refine ⟨w, ?_, rfl⟩
      exact (G.induce (pairComplement a b : Set V)).mem_neighborFinset z w |>.mpr
        (SimpleGraph.induce_adj.mpr hv.2.2)
  have hdeg : (G.induce (pairComplement a b : Set V)).degree z = T.card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← Finset.card_map, hmap]
  have ha := Finset.pred_card_le_card_erase (s := G.neighborFinset z.1) (a := a)
  have hb := Finset.pred_card_le_card_erase
    (s := (G.neighborFinset z.1).erase a) (a := b)
  rw [SimpleGraph.card_neighborFinset_eq_degree] at ha
  change ((G.neighborFinset z.1).erase a).card - 1 ≤ T.card at hb
  omega

private theorem map_endpoint_neighbors_left {a b : V} :
    (((Finset.univ : Finset (pairComplement a b : Set V)).filter
        fun z ↦ G.Adj a z.1).map
      (Function.Embedding.subtype fun v ↦ v ∈ (pairComplement a b : Set V))) =
      (G.neighborFinset a).erase b := by
  ext v
  constructor
  · intro hv
    obtain ⟨z, hz, hzv⟩ := Finset.mem_map.mp hv
    subst v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    simp only [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
    have hzmem : z.1 ≠ a ∧ z.1 ≠ b := by
      simpa [pairComplement] using z.2
    exact ⟨hzmem.2, hz⟩
  · intro hv
    simp only [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hv
    have hza : v ≠ a := hv.2.ne.symm
    let z : (pairComplement a b : Set V) := ⟨v, by
      simp [pairComplement, hv.1, hza]⟩
    apply Finset.mem_map.mpr
    exact ⟨z, by simp [z, hv.2], rfl⟩

private theorem map_endpoint_neighbors_right {a b : V} :
    (((Finset.univ : Finset (pairComplement a b : Set V)).filter
        fun z ↦ G.Adj z.1 b).map
      (Function.Embedding.subtype fun v ↦ v ∈ (pairComplement a b : Set V))) =
      (G.neighborFinset b).erase a := by
  ext v
  constructor
  · intro hv
    obtain ⟨z, hz, hzv⟩ := Finset.mem_map.mp hv
    subst v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    simp only [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
    have hzmem : z.1 ≠ a ∧ z.1 ≠ b := by
      simpa [pairComplement] using z.2
    exact ⟨hzmem.1, hz.symm⟩
  · intro hv
    simp only [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hv
    have hzb : v ≠ b := hv.2.ne.symm
    let z : (pairComplement a b : Set V) := ⟨v, by
      simp [pairComplement, hv.1, hzb]⟩
    apply Finset.mem_map.mpr
    exact ⟨z, by simp [z, hv.2.symm], rfl⟩

/-- The elementary dense-graph Hamilton-connectivity lemma used in the DKM
proof.  The degree hypothesis is the exact natural-number rendering of
`δ(G) ≥ |V(G)| / 2 + 1`, with the division interpreted over the reals.

The lower bound `5 ≤ |V|` is harmless in the asymptotic application and lets
the proof apply Dirac's theorem after deleting the prescribed endpoints. -/
theorem hamilton_connected_of_five_le_card
    (hV : 5 ≤ Fintype.card V)
    (hdeg : ∀ v : V, Fintype.card V + 2 ≤ 2 * G.degree v) :
    ∀ ⦃a b : V⦄, a ≠ b → ∃ p : G.Walk a b, p.IsHamiltonian := by
  intro a b hab
  let s : Set V := (pairComplement a b : Set V)
  have hs_card : Fintype.card s = Fintype.card V - 2 := by
    simpa [s] using card_pairComplement hab
  have hs_three : 3 ≤ Fintype.card s := by omega
  have hs_degree : ∀ z : s, Fintype.card s ≤
      2 * (G.induce s).degree z := by
    intro z
    have hz := degree_sub_two_le_degree_induce_pairComplement (G := G) z
    have hzdeg := hdeg z.1
    change G.degree z.1 - 2 ≤ (G.induce s).degree z at hz
    omega
  have hHam : (G.induce s).IsHamiltonian :=
    SimpleGraph.dirac_theorem hs_three hs_degree
  have : Nontrivial s := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card s)
  obtain ⟨q, hq⟩ := hHam.exists_isHamiltonianCycle x
  have hleft : G.degree a - 1 ≤
      ((Finset.univ : Finset s).filter fun z ↦ G.Adj a z.1).card := by
    change G.degree a - 1 ≤
      ((Finset.univ : Finset (pairComplement a b : Set V)).filter
        fun z ↦ G.Adj a z.1).card
    have hpred := Finset.pred_card_le_card_erase (s := G.neighborFinset a) (a := b)
    rw [SimpleGraph.card_neighborFinset_eq_degree] at hpred
    have hmap := map_endpoint_neighbors_left (G := G) (a := a) (b := b)
    have hcardMap := congrArg Finset.card hmap
    rw [Finset.card_map] at hcardMap
    exact hcardMap.symm ▸ hpred
  have hright : G.degree b - 1 ≤
      ((Finset.univ : Finset s).filter fun z ↦ G.Adj z.1 b).card := by
    change G.degree b - 1 ≤
      ((Finset.univ : Finset (pairComplement a b : Set V)).filter
        fun z ↦ G.Adj z.1 b).card
    have hpred := Finset.pred_card_le_card_erase (s := G.neighborFinset b) (a := a)
    rw [SimpleGraph.card_neighborFinset_eq_degree] at hpred
    have hmap := map_endpoint_neighbors_right (G := G) (a := a) (b := b)
    have hcardMap := congrArg Finset.card hmap
    rw [Finset.card_map] at hcardMap
    exact hcardMap.symm ▸ hpred
  apply exists_isHamiltonianPath_of_induced_cycle_of_card_lt_add q hq
  · exact pairComplement_not_mem_left
  · exact pairComplement_not_mem_right
  · exact hab
  · exact fun v ↦ pairComplement_cover
  · have ha := hdeg a
    have hb := hdeg b
    have ha_two : 2 ≤ G.degree a := by omega
    have hb_two : 2 ≤ G.degree b := by omega
    omega

end Hamiltonicity

end Erdos622
