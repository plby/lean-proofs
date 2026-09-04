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
import ErdosProblems.Erdos622.LongestCycle
import ErdosProblems.Erdos58.Structural.SpliceConstruction

/-!
# The finite Chvatal--Erdos theorem

This file proves the strict form of the Chvatal--Erdos Hamiltonicity theorem
used in the bi-dense case of Erdos Problem 622.  Connectivity is expressed by
the deletion predicate `LongestCycle.VertexConnectedAtLeast`; the independence
hypothesis is expressed directly for finite vertex sets.

The proof uses a longest cycle.  For a component outside it, deleting the
vertices of the cycle which see that component disconnects the graph, so there
are at least `k` such attachment vertices.  The successors of the attachments
in a fixed orientation of the longest cycle form an independent set: an edge
between two successors, together with a path through the outside component,
splices to a strictly longer cycle.  This contradicts the strict independence
bound.
-/

open Finset Set
open scoped SimpleGraph

namespace Erdos622
namespace ChvatalErdos

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## Elementary cardinal and cycle facts -/

/-- The deletion formulation of `k`-connectivity forces `k` not to exceed
the order of the finite graph. -/
lemma card_connectivity_le {k : ℕ}
    (hconn : LongestCycle.VertexConnectedAtLeast G k) :
    k ≤ Fintype.card V := by
  by_contra h
  have hunivlt : (Finset.univ : Finset V).card < k := by
    rw [Finset.card_univ]
    omega
  have hempty := hconn (Finset.univ : Finset V) hunivlt
  obtain ⟨v⟩ := hempty.nonempty
  exact v.2 (Finset.mem_univ v.1)

/-- Deletion-connectivity at level `k` gives the usual minimum-degree bound
`k - 1`.  This convention also handles complete graphs, for which deleting
all but one vertex still leaves a connected graph. -/
lemma connectivity_sub_one_le_degree {k : ℕ}
    (hconn : LongestCycle.VertexConnectedAtLeast G k) (v : V) :
    k - 1 ≤ G.degree v := by
  by_contra hdeg
  have hkcard := card_connectivity_le (G := G) hconn
  let C : Finset V := G.neighborFinset v
  have hCcard : C.card = G.degree v := G.card_neighborFinset_eq_degree v
  have hClt : C.card < k := by omega
  have hsmall : (insert v C).card < Fintype.card V := by
    have hvC : v ∉ C := by simp [C]
    rw [Finset.card_insert_of_notMem hvC, hCcard]
    omega
  obtain ⟨w, hwuniv, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  have hwv : w ≠ v := by
    intro hwv
    subst w
    exact hw (Finset.mem_insert_self _ _)
  have hwC : w ∉ C := fun hwC ↦ hw (Finset.mem_insert_of_mem hwC)
  let v' : {x : V // x ∉ C} := ⟨v, by simp [C]⟩
  let w' : {x : V // x ∉ C} := ⟨w, hwC⟩
  obtain ⟨p, hp⟩ := (hconn C hClt).exists_isPath v' w'
  have hpnon : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne (by
    intro heq
    exact hwv (congrArg Subtype.val heq).symm)
  have hadj := p.adj_snd hpnon
  have hadjG : G.Adj v p.snd.1 := SimpleGraph.induce_adj.mp hadj
  exact p.snd.2 ((G.mem_neighborFinset v p.snd.1).mpr hadjG)

/-- The length of a simple cycle in a finite graph is at most the order of
the graph. -/
lemma isCycle_length_le_card {v : V} {c : G.Walk v v} (hc : c.IsCycle) :
    c.length ≤ Fintype.card V := by
  have hnodup : c.support.tail.Nodup := hc.support_nodup
  have hsub : c.support.tail.toFinset ⊆ (Finset.univ : Finset V) :=
    Finset.subset_univ _
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnodup, Finset.card_univ] at hcard
  have hlen : c.support.tail.length = c.length := by
    rw [List.length_tail, c.length_support]
    omega
  simpa [hlen] using hcard

/-- The finite set of lengths of genuine cycles in `G`. -/
def cycleLengths (G : SimpleGraph V) : Finset ℕ :=
  (Finset.range (Fintype.card V + 1)).filter fun m ↦
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = m

lemma mem_cycleLengths_iff {m : ℕ} :
    m ∈ cycleLengths G ↔
      ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = m := by
  constructor
  · intro hm
    exact (Finset.mem_filter.mp hm).2
  · rintro ⟨v, c, hc, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (isCycle_length_le_card hc)),
      ⟨v, c, hc, rfl⟩⟩

/-- The standard endpoint argument: a longest path whose terminal endpoint
has degree `d ≥ 2` contains a cycle of length at least `d + 1`. -/
lemma exists_cycle_degree_add_one_le_of_isLongestPath
    {a b : V} {p : G.Walk a b} (hp : Erdos622.LongestCycle.IsLongestPath p)
    (hdeg : 2 ≤ G.degree b) :
    ∃ (z : V) (c : G.Walk z z), c.IsCycle ∧ G.degree b + 1 ≤ c.length := by
  let I : Finset ℕ := (Finset.range p.length).filter fun i ↦ G.Adj b (p.getVert i)
  have hplen : 2 ≤ p.length := hdeg.trans hp.degree_end_le_length
  have hI : I.Nonempty := by
    refine ⟨p.length - 1, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
    exact p.adj_penultimate (by
      rw [SimpleGraph.Walk.not_nil_iff_lt_length]
      omega) |>.symm
  let j : ℕ := I.min' hI
  have hjI : j ∈ I := Finset.min'_mem I hI
  have hjlt : j < p.length := (Finset.mem_filter.mp hjI).1 |> Finset.mem_range.mp
  have hbj : G.Adj b (p.getVert j) := (Finset.mem_filter.mp hjI).2
  let r : G.Walk (p.getVert j) b := p.drop j
  have hrpath : r.IsPath := hp.1.drop j
  have hneighbor : G.neighborFinset b ⊆ r.support.toFinset.erase b := by
    intro x hx
    have hbx : G.Adj b x := (G.mem_neighborFinset b x).mp hx
    have hxP : x ∈ p.support := hp.end_neighbor_mem_support hbx
    obtain ⟨i, hi, hile⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hxP
    have hilt : i < p.length := by
      rcases hile.lt_or_eq with hilt | rfl
      · exact hilt
      · rw [p.getVert_length] at hi
        exact (hbx.ne hi).elim
    have hiI : i ∈ I := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr hilt, hi.symm ▸ hbx⟩
    have hji : j ≤ i := Finset.min'_le I i hiI
    have hxR : x ∈ r.support := by
      have hm : (r.getVert (i - j)) = x := by
        change (p.drop j).getVert (i - j) = x
        rw [SimpleGraph.Walk.drop_getVert, Nat.add_sub_of_le hji, hi]
      exact hm ▸ r.getVert_mem_support (i - j)
    exact Finset.mem_erase.mpr ⟨hbx.ne.symm, List.mem_toFinset.mpr hxR⟩
  have hdegree_le : G.degree b ≤ r.length := by
    rw [← G.card_neighborFinset_eq_degree]
    calc
      (G.neighborFinset b).card ≤ (r.support.toFinset.erase b).card :=
        Finset.card_le_card hneighbor
      _ = r.length := by
        rw [Finset.card_erase_of_mem (List.mem_toFinset.mpr r.end_mem_support)]
        rw [List.toFinset_card_of_nodup hrpath.support_nodup, r.length_support]
        omega
  have hrlen : 2 ≤ r.length := hdeg.trans hdegree_le
  have hedge : s(p.getVert j, b) ∉ r.reverse.edges := by
    intro hedge
    have hedge' : s(p.getVert j, b) ∈ r.edges := by
      simpa [SimpleGraph.Walk.edges_reverse] using hedge
    have hone := hrpath.length_eq_one_of_mem_edges hedge'
    omega
  let c : G.Walk (p.getVert j) (p.getVert j) := r.reverse.cons hbj.symm
  have hc : c.IsCycle := by
    exact (SimpleGraph.Walk.cons_isCycle_iff r.reverse hbj.symm).mpr
      ⟨hrpath.reverse, hedge⟩
  refine ⟨p.getVert j, c, hc, ?_⟩
  simp only [c, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_reverse]
  omega

/-- Under deletion-connectivity at least `k`, a finite graph has a genuine
cycle of length at least `k` as soon as `k ≥ 3`. -/
lemma exists_cycle_connectivity_le_length {k : ℕ} (hk : 3 ≤ k)
    (hconn : LongestCycle.VertexConnectedAtLeast G k) :
    ∃ (z : V) (c : G.Walk z z), c.IsCycle ∧ k ≤ c.length := by
  have hcard : 0 < Fintype.card V :=
    lt_of_lt_of_le (by omega : 0 < k) (card_connectivity_le (G := G) hconn)
  let : Nonempty V := Fintype.card_pos_iff.mp hcard
  obtain ⟨a, b, p, hp⟩ := Erdos622.LongestCycle.exists_isLongestPath (G := G)
  have hbdeg : 2 ≤ G.degree b := by
    have := connectivity_sub_one_le_degree (G := G) hconn b
    omega
  obtain ⟨z, c, hc, hlen⟩ :=
    exists_cycle_degree_add_one_le_of_isLongestPath hp hbdeg
  refine ⟨z, c, hc, ?_⟩
  have := connectivity_sub_one_le_degree (G := G) hconn b
  omega

/-- Choose a genuine cycle of maximum length.  Its length is at least the
connectivity parameter. -/
lemma exists_longest_cycle {k : ℕ} (hk : 3 ≤ k)
    (hconn : LongestCycle.VertexConnectedAtLeast G k) :
    ∃ (z : V) (c : G.Walk z z),
      c.IsCycle ∧ k ≤ c.length ∧
        ∀ (z' : V) (c' : G.Walk z' z'), c'.IsCycle → c'.length ≤ c.length := by
  obtain ⟨z₀, c₀, hc₀, hklen⟩ :=
    exists_cycle_connectivity_le_length (G := G) hk hconn
  have hnonempty : (cycleLengths G).Nonempty := by
    refine ⟨c₀.length, ?_⟩
    exact mem_cycleLengths_iff.mpr ⟨z₀, c₀, hc₀, rfl⟩
  obtain ⟨m, hm, hmax⟩ :=
    Finset.exists_max_image (cycleLengths G) id hnonempty
  obtain ⟨z, c, hc, hcm⟩ := mem_cycleLengths_iff.mp hm
  subst m
  refine ⟨z, c, hc, ?_, ?_⟩
  · have hc₀mem := mem_cycleLengths_iff.mpr ⟨z₀, c₀, hc₀, rfl⟩
    have := hmax c₀.length hc₀mem
    simpa using hklen.trans this
  · intro z' c' hc'
    have hc'mem := mem_cycleLengths_iff.mpr ⟨z', c', hc', rfl⟩
    simpa using hmax c'.length hc'mem

/-! ## A maximum cycle and an exterior component -/

/-- The finite carrier of a genuine cycle has cardinality equal to its
length (the base vertex is the sole repetition in the closed support). -/
lemma cycleCarrier_card {z : V} {c : G.Walk z z} (hc : c.IsCycle) :
    c.support.toFinset.card = c.length := by
  have hz : z ∈ c.support.tail := c.end_mem_tail_support hc.not_nil
  rw [← c.cons_tail_support, List.toFinset_cons, Finset.insert_eq_of_mem
    (List.mem_toFinset.mpr hz), List.toFinset_card_of_nodup hc.support_nodup]
  rw [List.length_tail, c.length_support]
  omega

/-- Lift a cycle to the induced graph on its carrier.  There it is a
Hamiltonian cycle. -/
lemma induced_cycle_isHamiltonianCycle {z : V} {c : G.Walk z z}
    (hc : c.IsCycle) :
    let C := c.support.toFinset
    let hC : ∀ x ∈ c.support, x ∈ (C : Set V) := fun x hx ↦
      List.mem_toFinset.mpr hx
    (c.induce (C : Set V) hC).IsHamiltonianCycle := by
  dsimp only
  let C := c.support.toFinset
  let hC : ∀ x ∈ c.support, x ∈ (C : Set V) := fun x hx ↦
    List.mem_toFinset.mpr hx
  let q := c.induce (C : Set V) hC
  have hmap : q.map
      (SimpleGraph.Embedding.induce (G := G) (C : Set V)).toHom = c := by
    change (c.induce (C : Set V) hC).map
      (SimpleGraph.Embedding.induce (G := G) (C : Set V)).toHom = c
    exact SimpleGraph.Walk.map_induce c hC
  have hqcycle : q.IsCycle := by
    apply (SimpleGraph.Walk.isCycle_map_iff_of_injective
      (p := q)
      (f := (SimpleGraph.Embedding.induce (G := G) (C : Set V)).toHom)
      (SimpleGraph.Embedding.induce (G := G) (C : Set V)).injective).mp
    rw [hmap]
    exact hc
  rw [SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq]
  refine ⟨hqcycle, ?_⟩
  have hcardC : Fintype.card (C : Set V) = c.length := by
    exact (Fintype.card_coe C).trans (cycleCarrier_card hc)
  change q.length = Fintype.card (C : Set V)
  rw [hcardC]
  have hlength := congrArg SimpleGraph.Walk.length hmap
  rw [SimpleGraph.Walk.length_map] at hlength
  exact hlength

/-- The graph induced outside a finite carrier. -/
abbrev outsideGraph (G : SimpleGraph V) (C : Finset V) :
    SimpleGraph {v : V // v ∉ C} :=
  G.induce {v : V | v ∉ C}

/-- Cycle vertices having a neighbor in a fixed exterior component. -/
def attachments (G : SimpleGraph V) (C : Finset V)
    (K : (outsideGraph G C).ConnectedComponent) : Finset C :=
  Finset.univ.filter fun u ↦ ∃ y : K, G.Adj u.1 y.1.1

lemma mem_attachments_iff {C : Finset V}
    {K : (outsideGraph G C).ConnectedComponent} {u : C} :
    u ∈ attachments G C K ↔ ∃ y : K, G.Adj u.1 y.1.1 := by
  simp [attachments]

/-- The attachment set of an exterior component of a cycle of length at
least `k` has at least `k` vertices.  This is the only separator argument in
the proof and follows directly from `VertexConnectedAtLeast`. -/
lemma card_attachments_ge {k : ℕ} (hconn : LongestCycle.VertexConnectedAtLeast G k)
    {z : V} {c : G.Walk z z} (hc : c.IsCycle) (hklen : k ≤ c.length)
    (x : {v : V // v ∉ c.support.toFinset}) :
    k ≤ (attachments G c.support.toFinset
      ((outsideGraph G c.support.toFinset).connectedComponentMk x)).card := by
  let C : Finset V := c.support.toFinset
  let H : SimpleGraph {v : V // v ∉ C} := outsideGraph G C
  let K : H.ConnectedComponent := H.connectedComponentMk x
  let A : Finset C := attachments G C K
  change k ≤ A.card
  by_contra hAcard
  have hAlt : A.card < k := by omega
  let eC : C ↪ V := Function.Embedding.subtype _
  let D : Finset V := A.map eC
  have hDcard : D.card = A.card := by simp [D]
  have hDlt : D.card < k := by omega
  have hCcard : k ≤ C.card := by
    change k ≤ c.support.toFinset.card
    simpa [cycleCarrier_card hc] using hklen
  have hAC : A.card < C.card := lt_of_lt_of_le hAlt hCcard
  have hAC' : A.card < (Finset.univ : Finset C).card := by
    simpa using hAC
  obtain ⟨u, _huC, huA⟩ := Finset.exists_mem_notMem_of_card_lt_card hAC'
  have huD : (u : V) ∉ D := by
    intro hu
    obtain ⟨a, haA, hae⟩ := Finset.mem_map.mp hu
    have hau : a = u := Subtype.ext hae
    exact huA (hau ▸ haA)
  have hxD : (x : V) ∉ D := by
    intro hxmem
    obtain ⟨a, -, hae⟩ := Finset.mem_map.mp hxmem
    exact x.2 (hae ▸ a.2)
  let xD : {v : V // v ∉ D} := ⟨x, hxD⟩
  let uD : {v : V // v ∉ D} := ⟨u, huD⟩
  obtain ⟨p, hp⟩ := (hconn D hDlt).exists_isPath xD uD
  let embD : LongestCycle.deleteVertices G D →g G :=
    (SimpleGraph.Embedding.induce {v : V | v ∉ D}).toHom
  let q : G.Walk (x : V) (u : V) := p.map embD
  let KS : Set V := {v | ∃ hv : v ∉ C, (⟨v, hv⟩ : {w : V // w ∉ C}) ∈ K}
  have hxKS : (x : V) ∈ KS := by
    refine ⟨x.2, ?_⟩
    simpa [K, H] using
      (SimpleGraph.ConnectedComponent.connectedComponentMk_mem
        (G := H) (v := x))
  have huKS : (u : V) ∉ KS := by
    rintro ⟨hu, -⟩
    exact hu u.2
  obtain ⟨d, hdq, hdKS, hdnotKS⟩ := q.exists_boundary_dart KS hxKS huKS
  obtain ⟨hdfC, hdfK⟩ := hdKS
  have hdsC : d.snd ∈ C := by
    by_contra hdsC
    have hadjH : H.Adj ⟨d.fst, hdfC⟩ ⟨d.snd, hdsC⟩ :=
      SimpleGraph.induce_adj.mpr d.adj
    have hmem : (⟨d.snd, hdsC⟩ : {w : V // w ∉ C}) ∈ K :=
      K.mem_supp_of_adj_mem_supp hdfK hadjH
    exact hdnotKS ⟨hdsC, hmem⟩
  let dsC : C := ⟨d.snd, hdsC⟩
  have hdsA : dsC ∈ A := by
    apply mem_attachments_iff.mpr
    refine ⟨⟨⟨d.fst, hdfC⟩, hdfK⟩, ?_⟩
    exact d.adj.symm
  have hdsD : d.snd ∈ D := by
    apply Finset.mem_map.mpr
    exact ⟨dsC, hdsA, rfl⟩
  have hdsq : d.snd ∈ q.support :=
    q.dart_snd_mem_support_of_mem_darts hdq
  change d.snd ∈ (p.map embD).support at hdsq
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hdsq
  obtain ⟨w, hw, hwval⟩ := hdsq
  change (w : V) = d.snd at hwval
  exact w.2 (hwval.symm ▸ hdsD)

/-! ## Paths through an exterior component -/

/-- Two distinct attachment vertices can be joined by a simple path whose
internal vertices lie outside the cycle carrier. -/
lemma exists_path_through_component {C : Finset V}
    (K : (outsideGraph G C).ConnectedComponent) {u v : C}
    (hu : u ∈ attachments G C K) (hv : v ∈ attachments G C K)
    (huv : u ≠ v) :
    ∃ r : G.Walk (u : V) (v : V),
      r.IsPath ∧ 2 ≤ r.length ∧
        ∀ w ∈ r.support, w = u ∨ w = v ∨ w ∉ C := by
  obtain ⟨yu, huyu⟩ := mem_attachments_iff.mp hu
  obtain ⟨yv, hvv⟩ := mem_attachments_iff.mp hv
  obtain ⟨p, hp⟩ := K.connected_toSimpleGraph.exists_isPath yu yv
  let pH : (outsideGraph G C).Walk yu.1 yv.1 :=
    p.map K.toSimpleGraph_hom
  have hpH : pH.IsPath := hp.map (by
    intro a b hab
    exact Subtype.ext hab)
  let eOut : outsideGraph G C →g G :=
    (SimpleGraph.Embedding.induce {w : V | w ∉ C}).toHom
  let pG : G.Walk yu.1.1 yv.1.1 := pH.map eOut
  have hpG : pG.IsPath := hpH.map
    (SimpleGraph.Embedding.induce (G := G) {w : V | w ∉ C}).injective
  have hpGoutside : ∀ w ∈ pG.support, w ∉ C := by
    intro w hw hC
    change w ∈ (pH.map eOut).support at hw
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hw
    obtain ⟨t, -, htw⟩ := hw
    change (t : V) = w at htw
    exact t.2 (htw ▸ hC)
  let r : G.Walk (u : V) (v : V) := (pG.cons huyu).concat hvv.symm
  have huNot : (u : V) ∉ pG.support := by
    intro huP
    exact hpGoutside u huP u.2
  have hvNot : (v : V) ∉ (pG.cons huyu).support := by
    intro hvP
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hvP
    rcases hvP with hvu | hvP
    · exact huv (Subtype.ext hvu.symm)
    · exact hpGoutside v hvP v.2
  have hr : r.IsPath := (hpG.cons huNot).concat hvNot hvv.symm
  refine ⟨r, hr, ?_, ?_⟩
  · simp [r]
  · intro w hw
    simp only [r, SimpleGraph.Walk.support_concat,
      SimpleGraph.Walk.support_cons, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hw
    rcases hw with ((rfl | hw) | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (hpGoutside w hw))
    · exact Or.inr (Or.inl rfl)

/-! ## The two cycle-extension moves -/

/-- An exterior path cannot join a cycle vertex to its oriented successor
on a longest cycle: replacing that one cycle edge gives a longer cycle. -/
lemma next_ne_of_exterior_path_of_longest
    {C : Finset V} {zC : C}
    (q : (G.induce (C : Set V)).Walk zC zC)
    (hq : q.IsHamiltonianCycle)
    {u v : C} (huv : u ≠ v)
    (r : G.Walk (u : V) (v : V)) (hr : r.IsPath)
    (hrlen : 2 ≤ r.length)
    (hrsupport : ∀ w ∈ r.support, w = u ∨ w = v ∨ w ∉ C)
    (hmax : ∀ (z : V) (c : G.Walk z z), c.IsCycle → c.length ≤ q.length) :
    hq.next u ≠ v := by
  intro hnextEq
  have huq : u ∈ q.support := hq.mem_support u
  let qU : (G.induce (C : Set V)).Walk u u := q.rotate u huq
  have hqU : qU.IsHamiltonianCycle := hq.rotate huq
  have hqUpos : 0 < qU.length :=
    SimpleGraph.Walk.not_nil_iff_lt_length.mp hqU.isCycle.not_nil
  have hsnd : qU.snd = hq.next u := by
    have hnext : qU.getVert 1 = hqU.next u :=
      hqU.getVert_succ_eq_next u (i := 0) hqUpos (by simp [qU])
    have hrot : hqU.next u = hq.next u := by
      exact SimpleGraph.Walk.IsHamiltonianCycle.rotate_next u hq huq u
    exact hnext.trans hrot
  let eC : (G.induce (C : Set V)) →g G :=
    (SimpleGraph.Embedding.induce (C : Set V)).toHom
  let p₀ : G.Walk qU.snd.1 u.1 := qU.tail.map eC
  have hp₀ : p₀.IsPath := hqU.isHamiltonian_tail.isPath.map
    (SimpleGraph.Embedding.induce (G := G) (C : Set V)).injective
  let p : G.Walk (v : V) (u : V) := p₀.copy
    (by simpa [hsnd, hnextEq]) rfl
  have hp : p.IsPath := by simpa [p] using hp₀
  have hpC : ∀ w ∈ p.support, w ∈ C := by
    intro w hw
    have hw : w ∈ p₀.support := by
      simpa only [p, SimpleGraph.Walk.support_copy] using hw
    change w ∈ (qU.tail.map eC).support at hw
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hw
    obtain ⟨t, -, htw⟩ := hw
    change (t : V) = w at htw
    exact htw ▸ t.2
  have hdisj : r.support.tail.Disjoint p.support.tail := by
    rw [List.disjoint_left]
    intro w hwr hwp
    have hwr' : w ∈ r.support := List.tail_subset _ hwr
    have hwp' : w ∈ p.support := List.tail_subset _ hwp
    rcases hrsupport w hwr' with hwu | hwv | hwC
    · subst w
      have hn := hr.support_nodup
      rw [← r.cons_tail_support, List.nodup_cons] at hn
      exact hn.1 hwr
    · subst w
      have hn := hp.support_nodup
      rw [← p.cons_tail_support, List.nodup_cons] at hn
      exact hn.1 hwp
    · exact hwC (hpC w hwp')
  have hcycle : (r.append p).IsCycle :=
    hr.isCycle_append hp hdisj (Or.inl (by omega))
  have hlong := hmax u.1 (r.append p) hcycle
  have hplen : p.length = q.length - 1 := by
    calc
      p.length = p₀.length := by simp only [p, SimpleGraph.Walk.length_copy]
      _ = qU.tail.length := by
        change (qU.tail.map eC).length = qU.tail.length
        exact SimpleGraph.Walk.length_map eC qU.tail
      _ = qU.length - 1 := SimpleGraph.Walk.length_tail qU
      _ = q.length - 1 := by simp [qU]
  simp only [SimpleGraph.Walk.length_append] at hlong
  omega

/-- On the Hamilton path obtained by deleting the first edge of an oriented
Hamilton cycle, the edge leaving any nonterminal vertex is its oriented
successor edge. -/
private lemma isCycle_dart_eq_of_fst_eq
    {W : Type*} {H : SimpleGraph W} {a : W} {p : H.Walk a a}
    (hp : p.IsCycle) {d e : H.Dart} (hd : d ∈ p.darts) (he : e ∈ p.darts)
    (hfst : d.fst = e.fst) : d = e := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
  have hget : p.getVert i = p.getVert j := by
    simpa [p.darts_getElem_eq_getVert i hi,
      p.darts_getElem_eq_getVert j hj] using hfst
  have hi' : i ≤ p.length - 1 := by
    have : i < p.length := by simpa using hi
    omega
  have hj' : j ≤ p.length - 1 := by
    have : j < p.length := by simpa using hj
    omega
  have hij := hp.getVert_injOn' hi' hj' hget
  subst j
  rfl

lemma snd_dropUntil_tail_eq_next
    {C : Finset V} {zC v : C}
    (q : (G.induce (C : Set V)).Walk zC zC)
    (hq : q.IsHamiltonianCycle) (hzv : zC ≠ v)
    (hv : v ∈ q.tail.support) :
    (q.tail.dropUntil v hv).snd = hq.next v := by
  let s := q.tail.dropUntil v hv
  have hsnot : ¬ s.Nil := SimpleGraph.Walk.not_nil_of_ne hzv.symm
  let d := s.firstDart hsnot
  have hdS : d ∈ s.darts := s.firstDart_mem_darts hsnot
  have hdTail : d ∈ q.tail.darts :=
    q.tail.darts_dropUntil_subset_darts hv hdS
  have hdQ : d ∈ q.darts := by
    rw [SimpleGraph.Walk.darts_tail] at hdTail
    exact List.tail_subset _ hdTail
  obtain ⟨e, heQ, heFst, heSnd⟩ := hq.self_next_in_darts v
  have hde : d = e := isCycle_dart_eq_of_fst_eq hq.isCycle hdQ heQ (by
    simpa [d, s] using heFst.symm)
  have hsnd := congrArg (fun t : (G.induce (C : Set V)).Dart ↦ t.snd) hde
  simpa [d, s, heSnd] using hsnd

/-- The successors of two distinct attachment vertices cannot be adjacent on
a longest cycle.  The alleged successor edge, the exterior path, and the two
complementary oriented cycle arcs splice to a strictly longer cycle. -/
lemma not_adj_next_of_exterior_path_of_longest
    {C : Finset V} {zC : C}
    (q : (G.induce (C : Set V)).Walk zC zC)
    (hq : q.IsHamiltonianCycle)
    {u v : C} (huv : u ≠ v)
    (r : G.Walk (u : V) (v : V)) (hr : r.IsPath)
    (hrlen : 2 ≤ r.length)
    (hrsupport : ∀ w ∈ r.support, w = u ∨ w = v ∨ w ∉ C)
    (hmax : ∀ (z : V) (c : G.Walk z z), c.IsCycle → c.length ≤ q.length) :
    ¬ G.Adj (hq.next u).1 (hq.next v).1 := by
  intro hadj
  have hnu : hq.next u ≠ v :=
    next_ne_of_exterior_path_of_longest q hq huv r hr hrlen hrsupport hmax
  have hrsupportRev : ∀ w ∈ r.reverse.support,
      w = v ∨ w = u ∨ w ∉ C := by
    intro w hw
    have hw' : w ∈ r.support := by simpa using hw
    rcases hrsupport w hw' with hwu | hwv | hwC
    · exact Or.inr (Or.inl hwu)
    · exact Or.inl hwv
    · exact Or.inr (Or.inr hwC)
  have hnv : hq.next v ≠ u :=
    next_ne_of_exterior_path_of_longest q hq huv.symm r.reverse hr.reverse
      (by simpa using hrlen) hrsupportRev hmax
  have huq : u ∈ q.support := hq.mem_support u
  let qU : (G.induce (C : Set V)).Walk u u := q.rotate u huq
  have hqU : qU.IsHamiltonianCycle := hq.rotate huq
  have hqUpos : 0 < qU.length :=
    SimpleGraph.Walk.not_nil_iff_lt_length.mp hqU.isCycle.not_nil
  have hsndU : qU.snd = hq.next u := by
    have hnext : qU.getVert 1 = hqU.next u :=
      hqU.getVert_succ_eq_next u (i := 0) hqUpos (by simp [qU])
    have hrot : hqU.next u = hq.next u :=
      SimpleGraph.Walk.IsHamiltonianCycle.rotate_next u hq huq u
    exact hnext.trans hrot
  let P := qU.tail
  have hP : P.IsPath := hqU.isHamiltonian_tail.isPath
  have hvP : v ∈ P.support := hqU.isHamiltonian_tail.mem_support v
  let c₀ := P.takeUntil v hvP
  let s₀ := P.dropUntil v hvP
  let d₀ := s₀.tail
  have hs₀not : ¬ s₀.Nil := SimpleGraph.Walk.not_nil_of_ne huv.symm
  have hsndV : s₀.snd = hq.next v := by
    have hsnd : s₀.snd = hqU.next v := by
      exact snd_dropUntil_tail_eq_next qU hqU huv hvP
    exact hsnd.trans
      (SimpleGraph.Walk.IsHamiltonianCycle.rotate_next u hq huq v)
  have hc₀ : c₀.IsPath := hP.takeUntil hvP
  have hs₀ : s₀.IsPath := hP.dropUntil hvP
  have hd₀ : d₀.IsPath := hs₀.tail
  have hcd₀ : c₀.support.Disjoint d₀.support := by
    change c₀.support.Disjoint s₀.tail.support
    apply SimpleGraph.Walk.IsPath.disjoint_support_of_append
    · simpa [c₀, s₀] using hP
    · exact hs₀not
  let eC : (G.induce (C : Set V)) →g G :=
    (SimpleGraph.Embedding.induce (C : Set V)).toHom
  let cMap := c₀.map eC
  let dMap := d₀.map eC
  have hsndUG : eC qU.snd = (hq.next u).1 := by
    change (qU.snd : V) = (hq.next u : C)
    exact congrArg Subtype.val hsndU
  have hsndVG : eC s₀.snd = (hq.next v).1 := by
    change (s₀.snd : V) = (hq.next v : C)
    exact congrArg Subtype.val hsndV
  have hvG : eC v = v.1 := rfl
  have huG : eC u = u.1 := rfl
  let cG : G.Walk (hq.next u).1 v.1 := cMap.copy hsndUG hvG
  let dG : G.Walk (hq.next v).1 u.1 := dMap.copy hsndVG huG
  have heCinj : Function.Injective eC := by
    exact (SimpleGraph.Embedding.induce (G := G) (C : Set V)).injective
  have hcG : cG.IsPath := by
    change (cMap.copy hsndUG hvG).IsPath
    rw [SimpleGraph.Walk.isPath_copy]
    exact hc₀.map heCinj
  have hdG : dG.IsPath := by
    change (dMap.copy hsndVG huG).IsPath
    rw [SimpleGraph.Walk.isPath_copy]
    exact hd₀.map heCinj
  have hcGC : ∀ w ∈ cG.support, w ∈ C := by
    intro w hw
    change w ∈ (cMap.copy hsndUG hvG).support at hw
    rw [SimpleGraph.Walk.support_copy] at hw
    change w ∈ (c₀.map eC).support at hw
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hw
    obtain ⟨t, -, rfl⟩ := hw
    exact t.2
  have hdGC : ∀ w ∈ dG.support, w ∈ C := by
    intro w hw
    change w ∈ (dMap.copy hsndVG huG).support at hw
    rw [SimpleGraph.Walk.support_copy] at hw
    change w ∈ (d₀.map eC).support at hw
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hw
    obtain ⟨t, -, rfl⟩ := hw
    exact t.2
  have hcdG : cG.support.Disjoint dG.support := by
    change (cMap.copy hsndUG hvG).support.Disjoint
      (dMap.copy hsndVG huG).support
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_copy]
    change (c₀.map eC).support.Disjoint (d₀.map eC).support
    rw [SimpleGraph.Walk.support_map, SimpleGraph.Walk.support_map]
    exact hcd₀.map heCinj
  let A : Set V := {w | w ∈ cG.support}
  let B : Set V := {w | w ∈ dG.support}
  have hAB : Disjoint A B := by
    rw [Set.disjoint_left]
    exact fun _ hx hy ↦ hcdG hx hy
  have hnextU_not_r : (hq.next u).1 ∉ r.support := by
    intro hw
    rcases hrsupport _ hw with hwu | hwv | hwC
    · exact hq.next_ne (Subtype.ext hwu)
    · exact hnu (Subtype.ext hwv)
    · exact hwC (hq.next u).2
  have hnextV_not_r : (hq.next v).1 ∉ r.support := by
    intro hw
    rcases hrsupport _ hw with hwu | hwv | hwC
    · exact hnv (Subtype.ext hwu)
    · exact hq.next_ne (Subtype.ext hwv)
    · exact hwC (hq.next v).2
  have hlinkDisj : hadj.toWalk.support.Disjoint r.reverse.support := by
    rw [List.disjoint_left]
    intro w hwE hwR
    have hwR' : w ∈ r.support := by simpa using hwR
    simp only [hadj.support_toWalk, List.mem_cons, List.not_mem_nil,
      or_false] at hwE
    rcases hwE with rfl | rfl
    · exact hnextU_not_r hwR'
    · exact hnextV_not_r hwR'
  have hrInteriorOutside : ∀ w ∈ r.reverse.support.tail.dropLast, w ∉ C := by
    intro w hw
    have hwTail : w ∈ r.reverse.support.tail :=
      List.dropLast_subset _ hw
    have hwSupportRev : w ∈ r.reverse.support :=
      List.tail_subset _ hwTail
    have hwSupport : w ∈ r.support := by simpa using hwSupportRev
    have hwneV : w ≠ (v : V) := by
      have hn := hr.reverse.support_nodup
      rw [← r.reverse.cons_tail_support, List.nodup_cons] at hn
      intro hwv
      exact hn.1 (hwv ▸ hwTail)
    have htailne : r.reverse.support.tail ≠ [] := by
      apply List.ne_nil_of_length_pos
      rw [List.length_tail, r.reverse.length_support,
        SimpleGraph.Walk.length_reverse]
      omega
    have hwDrop : w ∈ r.reverse.support.dropLast := by
      rw [← r.reverse.cons_tail_support,
        List.dropLast_cons_of_ne_nil htailne]
      exact List.mem_cons_of_mem _ hw
    have hwneU : w ≠ (u : V) := by
      have hn := hr.reverse.support_nodup.rel_dropLast_getLast hwDrop
      simpa using hn
    rcases hrsupport w hwSupport with hwu | hwv | hwC
    · exact (hwneU hwu).elim
    · exact (hwneV hwv).elim
    · exact hwC
  let L : Erdos58.TwoLinkage G A B := {
    a₁ := (hq.next u).1
    a₂ := v.1
    b₁ := (hq.next v).1
    b₂ := u.1
    p := hadj.toWalk
    q := r.reverse
    p_isPath := hadj.isPath_toWalk
    q_isPath := hr.reverse
    a₁_mem := by exact cG.start_mem_support
    a₂_mem := by exact cG.end_mem_support
    b₁_mem := by exact dG.start_mem_support
    b₂_mem := by exact dG.end_mem_support
    disjoint_support := hlinkDisj
    p_interior := by simp [hadj.support_toWalk]
    q_interior := by
      intro w hw hwAB
      have hwOut := hrInteriorOutside w hw
      rcases hwAB with hwA | hwB
      · exact hwOut (hcGC w hwA)
      · exact hwOut (hdGC w hwB) }
  let newCycle := Erdos58.SpliceData.close L.p dG L.q cG
  have hnewCycle : newCycle.IsCycle := by
    exact Erdos58.Structural.linkage_close_isCycle L hAB cG dG hcG hdG
      (fun _ hx ↦ hx) (fun _ hx ↦ hx)
  have hsplit : c₀.length + s₀.length = P.length := by
    have hEq : c₀.append s₀ = P := P.take_spec hvP
    calc
      c₀.length + s₀.length = (c₀.append s₀).length := by simp
      _ = P.length := congrArg SimpleGraph.Walk.length hEq
  have hs₀pos : 0 < s₀.length :=
    SimpleGraph.Walk.not_nil_iff_lt_length.mp hs₀not
  have hd₀len : d₀.length = s₀.length - 1 :=
    SimpleGraph.Walk.length_tail s₀
  have hPlen : P.length = q.length - 1 := by
    calc
      P.length = qU.length - 1 := SimpleGraph.Walk.length_tail qU
      _ = q.length - 1 := by simp [qU]
  have harcs : cG.length + dG.length = q.length - 2 := by
    have hcmap : cG.length = c₀.length := by
      change (cMap.copy hsndUG hvG).length = c₀.length
      rw [SimpleGraph.Walk.length_copy]
      change (c₀.map eC).length = c₀.length
      exact SimpleGraph.Walk.length_map eC c₀
    have hdmap : dG.length = d₀.length := by
      change (dMap.copy hsndVG huG).length = d₀.length
      rw [SimpleGraph.Walk.length_copy]
      change (d₀.map eC).length = d₀.length
      exact SimpleGraph.Walk.length_map eC d₀
    rw [hcmap, hdmap, hd₀len]
    omega
  have hlong := hmax (hq.next u).1 newCycle hnewCycle
  have hnewLen : newCycle.length = 1 + dG.length + r.length + cG.length := by
    simp [newCycle, L]
  rw [hnewLen] at hlong
  omega

/-! ## Chvatal--Erdos Hamiltonicity -/

/-- **Finite Chvatal--Erdos theorem (strict independence form).**

If a finite graph on at least three vertices is `k`-vertex-connected, in the
deletion sense of `LongestCycle.VertexConnectedAtLeast`, and every finite
independent set has cardinality strictly less than `k`, then the graph is
Hamiltonian. -/
theorem isHamiltonian_of_vertexConnectedAtLeast_of_independence_lt
    {k : ℕ}
    (hcard : 3 ≤ Fintype.card V)
    (hk : 2 ≤ k)
    (hconn : LongestCycle.VertexConnectedAtLeast G k)
    (hindep : ∀ A : Finset V, G.IsIndepSet (A : Set V) → A.card < k) :
    G.IsHamiltonian := by
  by_cases hk2 : k = 2
  · have htop : G = ⊤ := by
      rw [eq_top_iff]
      intro u v huv
      simp only [SimpleGraph.top_adj, ne_eq] at huv
      by_contra huvAdj
      let A : Finset V := {u, v}
      have hAcard : A.card = 2 := by simp [A, huv]
      have hAind : G.IsIndepSet (A : Set V) := by
        intro x hx y hy hxy
        simp only [A, Finset.coe_insert, Finset.coe_singleton,
          Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact (hxy rfl).elim
        · exact huvAdj
        · exact fun h ↦ huvAdj h.symm
        · exact (hxy rfl).elim
      have := hindep A hAind
      rw [hAcard, hk2] at this
      omega
    rw [htop]
    apply SimpleGraph.dirac_theorem hcard
    intro u
    simp
    omega
  · have hk3 : 3 ≤ k := by omega
    obtain ⟨z, c, hc, hklen, hmax⟩ :=
      exists_longest_cycle (G := G) hk3 hconn
    by_cases hspan : c.length = Fintype.card V
    · intro _
      refine ⟨z, c, ?_⟩
      exact SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr
        ⟨hc, hspan⟩
    · have hclt : c.length < Fintype.card V := by
        exact (isCycle_length_le_card hc).lt_of_ne hspan
      let C : Finset V := c.support.toFinset
      have hCcard : C.card = c.length := cycleCarrier_card hc
      have hClt : C.card < Fintype.card V := by omega
      obtain ⟨x, -, hxC⟩ := Finset.exists_mem_notMem_of_card_lt_card hClt
      let xOut : {w : V // w ∉ C} := ⟨x, hxC⟩
      let K : (outsideGraph G C).ConnectedComponent :=
        (outsideGraph G C).connectedComponentMk xOut
      let A : Finset C := attachments G C K
      have hAcard : k ≤ A.card := by
        exact card_attachments_ge hconn hc hklen xOut
      let zC : C := ⟨z, List.mem_toFinset.mpr c.start_mem_support⟩
      let hC : ∀ w ∈ c.support, w ∈ (C : Set V) := fun w hw ↦
        List.mem_toFinset.mpr hw
      let q : (G.induce (C : Set V)).Walk zC zC :=
        c.induce (C : Set V) hC
      have hq : q.IsHamiltonianCycle := induced_cycle_isHamiltonianCycle hc
      have hqLen : q.length = c.length := by
        calc
          q.length = Fintype.card C := hq.length_eq
          _ = C.card := Fintype.card_coe C
          _ = c.length := hCcard
      have hmaxq : ∀ (z' : V) (c' : G.Walk z' z'),
          c'.IsCycle → c'.length ≤ q.length := by
        intro z' c' hc'
        rw [hqLen]
        exact hmax z' c' hc'
      let S₀ : Finset C := A.image hq.next
      let eC : C ↪ V := Function.Embedding.subtype _
      let S : Finset V := S₀.map eC
      have hScard : S.card = A.card := by
        calc
          S.card = S₀.card := Finset.card_map eC
          _ = A.card := Finset.card_image_of_injective A hq.next_inj
      have hSindep : G.IsIndepSet (S : Set V) := by
        intro a ha b hb hab
        have haS : a ∈ S := by simpa using ha
        have hbS : b ∈ S := by simpa using hb
        obtain ⟨a₀, ha₀S, rfl⟩ := Finset.mem_map.mp haS
        obtain ⟨b₀, hb₀S, rfl⟩ := Finset.mem_map.mp hbS
        obtain ⟨u, huA, huNext⟩ := Finset.mem_image.mp ha₀S
        obtain ⟨v, hvA, hvNext⟩ := Finset.mem_image.mp hb₀S
        subst a₀
        subst b₀
        have huv : u ≠ v := by
          intro huv
          subst v
          exact hab rfl
        obtain ⟨r, hr, hrlen, hrsupport⟩ :=
          exists_path_through_component K huA hvA huv
        exact not_adj_next_of_exterior_path_of_longest q hq huv r hr hrlen
          hrsupport hmaxq
      have hSlt := hindep S hSindep
      rw [hScard] at hSlt
      omega

end

end ChvatalErdos
end Erdos622
