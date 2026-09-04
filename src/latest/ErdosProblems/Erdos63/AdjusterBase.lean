/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos63.Adjusters
import ErdosProblems.Erdos63.AvoidanceDeep
import ErdosProblems.Erdos63.SubdivisionExtremal
import ErdosProblems.Erdos63.Lemma311
import ErdosProblems.Erdos63.PathCycles
import ErdosProblems.Erdos63.ExpanderExtraction
import ErdosProblems.Erdos63.Claim46Growth

/-!
# The simple-adjuster constructions

This file contains the graph-theoretic base of the adjuster construction in
Liu--Montgomery, Lemmas 4.2 and 4.3.  In particular, it isolates the exact
``two arcs differing by two'' consequence of an even cycle.  The remaining
statements combine that fact with the concrete simultaneous-expansion and
avoiding-connection lemmas developed in the preceding files.
-/

open Finset Set SimpleGraph
open scoped SimpleGraph

namespace Erdos63

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

variable {V : Type u}
variable {G : SimpleGraph V}

/-! ## The two almost-antipodal arcs of an even cycle -/

/-- Splitting an even cycle one edge short of an antipodal vertex produces
two simple paths whose lengths differ by exactly two.  Both paths are
supported on the original cycle.

This is the precise cycle operation used at the start of
Liu--Montgomery Lemma 4.2. -/
theorem exists_cycle_arcs_diff_two {c : V} (C : G.Walk c c)
    (hC : C.IsCycle) {half : ℕ} (hlen : C.length = 2 * half) :
    ∃ y : V, ∃ short long : G.Walk c y,
      short.IsPath ∧ long.IsPath ∧
      short.length = half - 1 ∧ long.length = half + 1 ∧
      (∀ z ∈ short.support, z ∈ C.support) ∧
      (∀ z ∈ long.support, z ∈ C.support) := by
  have hhalf : 2 ≤ half := by
    have hthree := hC.three_le_length
    omega
  let j : ℕ := half - 1
  let y : V := C.getVert j
  let short : G.Walk c y := C.take j
  let back : G.Walk y c := C.drop j
  let long : G.Walk c y := back.reverse
  have hjpos : 0 < j := by
    dsimp [j]
    omega
  have hjlt : j < C.length := by
    dsimp [j]
    omega
  have hshortPath : short.IsPath := by
    exact hC.isPath_take hjlt
  have hbackPath : back.IsPath := by
    exact hC.isPath_drop hjpos
  have hshortLen : short.length = half - 1 := by
    calc
      short.length = j ⊓ C.length := by simp [short]
      _ = j := Nat.min_eq_left (Nat.le_of_lt hjlt)
      _ = half - 1 := rfl
  have hlongLen : long.length = half + 1 := by
    simp [long, back, j, hlen]
    omega
  refine ⟨y, short, long, hshortPath, hbackPath.reverse,
    hshortLen, hlongLen, ?_, ?_⟩
  · intro z hz
    dsimp [short] at hz
    rw [Walk.support_take] at hz
    exact List.mem_of_mem_take hz
  · intro z hz
    have hzback : z ∈ back.support := by
      simpa [long, Walk.support_reverse] using hz
    dsimp [back] at hzback
    rw [Walk.drop_support_eq_support_drop_min] at hzback
    exact List.mem_of_mem_drop hzback

/-- Bipartiteness supplies the evenness hypothesis needed by
`exists_cycle_arcs_diff_two`. -/
theorem Bipartition.exists_cycle_arcs_diff_two [Fintype V]
    (B : Bipartition G) {c : V} (C : G.Walk c c) (hC : C.IsCycle) :
    ∃ half : ℕ, ∃ y : V, ∃ short long : G.Walk c y,
      C.length = 2 * half ∧
      short.IsPath ∧ long.IsPath ∧
      short.length = half - 1 ∧ long.length = half + 1 ∧
      (∀ z ∈ short.support, z ∈ C.support) ∧
      (∀ z ∈ long.support, z ∈ C.support) := by
  have heven : Even C.length :=
    (B.even_length_iff_sameSide C).2 (B.sameSide_refl c)
  obtain ⟨half, hhalf⟩ := heven
  have hlen : C.length = 2 * half := by omega
  obtain ⟨y, short, long, hshort, hlong, hshortLen, hlongLen,
    hshortSupport, hlongSupport⟩ :=
      Erdos63.exists_cycle_arcs_diff_two C hC hlen
  exact ⟨half, y, short, long, hlen, hshort, hlong, hshortLen,
    hlongLen, hshortSupport, hlongSupport⟩

/-- Every graph containing a cycle contains one of minimum length, and the
minimum cycle is no longer than the supplied witness. -/
theorem exists_shortestCycle_of_cycle {c₀ : V} (C₀ : G.Walk c₀ c₀)
    (hC₀ : C₀.IsCycle) :
    ∃ c : V, ∃ C : G.Walk c c,
      IsShortestCycle C ∧ C.length ≤ C₀.length := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∃ c : V, ∃ C : G.Walk c c, C.IsCycle ∧ C.length = n
  have hP : ∃ n, P n := ⟨C₀.length, c₀, C₀, hC₀, rfl⟩
  obtain ⟨c, C, hC, hlength⟩ := Nat.find_spec hP
  refine ⟨c, C, ⟨hC, ?_⟩, ?_⟩
  · intro x Q hQ
    have hmin : Nat.find hP ≤ Q.length :=
      Nat.find_min' hP ⟨x, Q, hQ, rfl⟩
    omega
  · have hmin : Nat.find hP ≤ C₀.length :=
      Nat.find_min' hP ⟨c₀, C₀, hC₀, rfl⟩
    omega

/-- A finite graph of minimum degree at least two contains a shortest cycle.
This elementary existence lemma is kept below the adjuster import boundary so
Claim 4.4 can combine it with the logarithmic Moore bound from Lemma 3.11. -/
theorem exists_shortestCycle_of_minDegree_two_local [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdegree : ∀ v : V, 2 ≤ G.degree v) :
    ∃ c : V, ∃ C : G.Walk c c, IsShortestCycle C := by
  classical
  have hnotAcyclic : ¬ G.IsAcyclic := by
    intro hacyclic
    obtain ⟨T, hGT, -, hT⟩ :=
      (SimpleGraph.connected_top (V := V)).exists_isTree_le_of_le_of_isAcyclic
        (G := ⊤) (H := G) le_top hacyclic
    have hsum : (∑ _ : V, 2) ≤ ∑ v : V, G.degree v := by
      apply Finset.sum_le_sum
      intro v _
      exact hdegree v
    have hedgeLower : Fintype.card V ≤ G.edgeFinset.card := by
      have htwice : 2 * Fintype.card V ≤ 2 * G.edgeFinset.card := by
        calc
          2 * Fintype.card V = ∑ _ : V, 2 := by simp [Nat.mul_comm]
          _ ≤ ∑ v : V, G.degree v := hsum
          _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
      omega
    have hedgeMono : G.edgeFinset.card ≤ T.edgeFinset.card :=
      Finset.card_mono (SimpleGraph.edgeFinset_mono hGT)
    have htreeEdges : T.edgeFinset.card + 1 = Fintype.card V :=
      hT.card_edgeFinset
    omega
  have hcycle : ∃ c : V, ∃ C : G.Walk c c, C.IsCycle := by
    by_contra hnone
    apply hnotAcyclic
    intro c C hC
    exact hnone ⟨c, C, hC⟩
  obtain ⟨c₀, C₀, hC₀⟩ := hcycle
  obtain ⟨c, C, hC, -⟩ := exists_shortestCycle_of_cycle C₀ hC₀
  exact ⟨c, C, hC⟩

/-- A shortest cycle has no chord.  The proof uses the two arcs after rotating
the cycle at one endpoint: a chord would have to be at least as long as each
arc, contradicting the three-edge lower bound for a cycle. -/
theorem IsShortestCycle.isChordless {c : V} {C : G.Walk c c}
    (hC : IsShortestCycle C) : C.IsChordless := by
  rw [Walk.isChordless_iff_forall_mem_edges]
  intro u v hu hv huv
  by_contra hedge
  let R : G.Walk u u := C.rotate u hu
  have hvR : v ∈ R.support := by simpa [R] using hv
  let p : G.Walk u v := R.takeUntil v hvR
  let q : G.Walk u v := (R.dropUntil v hvR).reverse
  let e : G.Walk u v := huv.toWalk
  have hR : R.IsCycle := hC.1.rotate hu
  have hp : p.IsPath := hR.isPath_takeUntil hvR
  have htake : ¬ (R.takeUntil v hvR).Nil := by
    rw [Walk.nil_takeUntil]
    exact G.ne_of_adj huv
  have hcyc : ((R.takeUntil v hvR).append (R.dropUntil v hvR)).IsCycle := by
    simpa using hR
  have hdrop : (R.dropUntil v hvR).IsPath :=
    hcyc.isPath_of_append_right htake
  have hq : q.IsPath := hdrop.reverse
  have he : e.IsPath := huv.isPath_toWalk
  have hedgeR : s(u, v) ∉ R.edges := by
    change s(u, v) ∉ (C.rotate u hu).edges
    rw [(C.rotate_edges u hu).mem_iff]
    exact hedge
  have hep : e ≠ p := by
    intro hep
    apply hedgeR
    apply R.edges_takeUntil_subset_edges hvR
    have : s(u, v) ∈ e.edges := by simp [e, huv.edges_toWalk]
    simpa [hep] using this
  have heq : e ≠ q := by
    intro heq
    apply hedgeR
    apply R.edges_dropUntil_subset_edges hvR
    have heEdge : s(u, v) ∈ e.edges := by simp [e, huv.edges_toWalk]
    have hqEdge : s(u, v) ∈ q.edges := by simpa [heq] using heEdge
    simpa [q, Walk.edges_reverse] using hqEdge
  have hsplit : C.length = p.length + q.length := by
    calc
      C.length = R.length := by simp [R]
      _ = (R.takeUntil v hvR).length + (R.dropUntil v hvR).length := by
        rw [← Walk.length_append, R.take_spec]
      _ = p.length + q.length := by simp [p, q]
  have hpOne : p.length ≤ 1 := by
    have h := hC.insideArc_length_le_shortcut p q e hq he heq hsplit
    simpa [e] using h
  have hqOne : q.length ≤ 1 := by
    have hsplit' : C.length = q.length + p.length := by omega
    have h := hC.insideArc_length_le_shortcut q p e hp he hep hsplit'
    simpa [e] using h
  have := hC.1.three_le_length
  omega

/-- Source Case I root selection.  If at most one vertex has been reserved,
minimum degree five and chordlessness leave two further distinct vertices
outside a shortest cycle. -/
theorem exists_two_vertices_outside_shortestCycle_and_reserved
    [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {c : V} (C : G.Walk c c) (hC : IsShortestCycle C)
    (reserved : Finset V) (hreserved : reserved.card ≤ 1)
    (hdegree : ∀ v : V, 5 ≤ G.degree v) :
    ∃ x₁ x₂ : V, x₁ ≠ x₂ ∧
      x₁ ∉ C.support ∧ x₂ ∉ C.support ∧
      x₁ ∉ reserved ∧ x₂ ∉ reserved := by
  let originalDecEq : DecidableEq V := inferInstance
  classical
  let : DecidableEq V := originalDecEq
  let available : Finset V :=
    (Finset.univ : Finset V) \ (C.support.toFinset ∪ reserved)
  have havailable : 1 < available.card := by
    by_contra hsmall
    have havailableCard : available.card ≤ 1 := by omega
    have hchordless := hC.isChordless
    have hinternal :
        (G.neighborFinset c ∩ C.support.toFinset).card ≤ 2 := by
      have hsub :
          (↑(G.neighborFinset c ∩ C.support.toFinset) : Set V) ⊆
            C.toSubgraph.neighborSet c := by
        intro w hw
        have hw' := Finset.mem_inter.1 hw
        have hadj : G.Adj c w := (G.mem_neighborFinset c w).1 hw'.1
        have hcC : c ∈ C.support := C.start_mem_support
        have hwC : w ∈ C.support := by simpa using hw'.2
        have hedgeC : s(c, w) ∈ C.edges :=
          hchordless.mem_edges hcC hwC hadj
        exact (SimpleGraph.Subgraph.mem_neighborSet C.toSubgraph c w).2
          (Walk.adj_toSubgraph_iff_mem_edges.2 hedgeC)
      have hncard :
          (↑(G.neighborFinset c ∩ C.support.toFinset) : Set V).ncard ≤
            (C.toSubgraph.neighborSet c).ncard :=
        Set.ncard_le_ncard hsub
      calc
        (G.neighborFinset c ∩ C.support.toFinset).card
            ≤ (C.toSubgraph.neighborSet c).ncard := by
              simpa only [Set.ncard_coe_finset] using hncard
        _ = 2 := hC.1.ncard_neighborSet_toSubgraph_eq_two C.start_mem_support
    have hexternalSubset : G.neighborFinset c \ C.support.toFinset ⊆
        available ∪ reserved := by
      intro w hw
      obtain ⟨hwN, hwC⟩ := Finset.mem_sdiff.1 hw
      by_cases hwR : w ∈ reserved
      · exact Finset.mem_union_right _ hwR
      · apply Finset.mem_union_left
        exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, by
          simp only [Finset.mem_union]
          exact fun h ↦ h.elim hwC hwR⟩
    have hexternal : (G.neighborFinset c \ C.support.toFinset).card ≤ 2 := by
      calc
        (G.neighborFinset c \ C.support.toFinset).card
            ≤ (available ∪ reserved).card := Finset.card_le_card hexternalSubset
        _ ≤ available.card + reserved.card := Finset.card_union_le _ _
        _ ≤ 2 := by omega
    have hpartition := Finset.card_sdiff_add_card_inter
      (G.neighborFinset c) C.support.toFinset
    have hdegreeCard : G.degree c =
        (G.neighborFinset c \ C.support.toFinset).card +
          (G.neighborFinset c ∩ C.support.toFinset).card := by
      simpa [G.card_neighborFinset_eq_degree] using hpartition.symm
    have := hdegree c
    omega
  obtain ⟨x₁, hx₁, x₂, hx₂, hx₁x₂⟩ := Finset.one_lt_card.1 havailable
  have hx₁out := (Finset.mem_sdiff.1 hx₁).2
  have hx₂out := (Finset.mem_sdiff.1 hx₂).2
  refine ⟨x₁, x₂, hx₁x₂, ?_, ?_, ?_, ?_⟩
  · intro hx
    exact hx₁out (Finset.mem_union_left _ (by simpa using hx))
  · intro hx
    exact hx₂out (Finset.mem_union_left _ (by simpa using hx))
  · intro hx
    exact hx₁out (Finset.mem_union_right _ hx)
  · intro hx
    exact hx₂out (Finset.mem_union_right _ hx)

/-- A cycle whose length is strictly below the minimum degree leaves at least
two vertices outside its support.  This supplies the two prescribed roots in
Case I of Claim 4.4 after the shortest-cycle bound is compared with the
extracted expander's minimum degree. -/
theorem exists_two_vertices_outside_cycle_of_length_lt_minDegree
    [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {c : V} (C : G.Walk c c) (hC : C.IsCycle)
    (hdegree : ∀ v : V, C.length + 1 ≤ G.degree v) :
    ∃ x₁ x₂ : V, x₁ ≠ x₂ ∧ x₁ ∉ C.support ∧ x₂ ∉ C.support := by
  let originalDecEq : DecidableEq V := inferInstance
  classical
  let : DecidableEq V := originalDecEq
  let v : V := Classical.choice inferInstance
  have hN : C.length + 1 < Fintype.card V :=
    (hdegree v).trans_lt (G.degree_lt_card_verts v)
  have hsupport : C.support.toFinset.card = C.length :=
    cycle_support_toFinset_card_eq_length C hC
  have hcomplement : 1 <
      ((Finset.univ : Finset V) \ C.support.toFinset).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      hsupport]
    omega
  obtain ⟨x₁, hx₁, x₂, hx₂, hx₁x₂⟩ := Finset.one_lt_card.1 hcomplement
  refine ⟨x₁, x₂, hx₁x₂, ?_, ?_⟩
  · exact fun hx ↦ (Finset.mem_sdiff.1 hx₁).2 (by simpa using hx)
  · exact fun hx ↦ (Finset.mem_sdiff.1 hx₂).2 (by simpa using hx)

/-- Reserving at most one vertex in addition to a short cycle still leaves
two distinct roots, provided the minimum degree has two further units of
slack.  This is the root-selection step in Case I of Claim 4.4: the reserved
set is the (possible) unique high-degree vertex of the extracted expander
outside its shortest cycle. -/
theorem exists_two_vertices_outside_cycle_and_singleton_of_length_lt_minDegree
    [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {c : V} (C : G.Walk c c) (hC : C.IsCycle) (reserved : Finset V)
    (hreserved : reserved.card ≤ 1)
    (hdegree : ∀ v : V, C.length + 2 ≤ G.degree v) :
    ∃ x₁ x₂ : V, x₁ ≠ x₂ ∧
      x₁ ∉ C.support ∧ x₂ ∉ C.support ∧
      x₁ ∉ reserved ∧ x₂ ∉ reserved := by
  let originalDecEq : DecidableEq V := inferInstance
  classical
  let : DecidableEq V := originalDecEq
  let v : V := Classical.choice inferInstance
  have hN : C.length + 2 < Fintype.card V :=
    (hdegree v).trans_lt (G.degree_lt_card_verts v)
  have hsupport : C.support.toFinset.card = C.length :=
    cycle_support_toFinset_card_eq_length C hC
  let blocked : Finset V := C.support.toFinset ∪ reserved
  have hblocked : blocked.card ≤ C.length + 1 := by
    calc
      blocked.card ≤ C.support.toFinset.card + reserved.card :=
        Finset.card_union_le _ _
      _ ≤ C.length + 1 := by omega
  have hcomplement : 1 < ((Finset.univ : Finset V) \ blocked).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    omega
  obtain ⟨x₁, hx₁, x₂, hx₂, hx₁x₂⟩ := Finset.one_lt_card.1 hcomplement
  have hx₁blocked := (Finset.mem_sdiff.1 hx₁).2
  have hx₂blocked := (Finset.mem_sdiff.1 hx₂).2
  refine ⟨x₁, x₂, hx₁x₂, ?_, ?_, ?_, ?_⟩
  · intro hx₁C
    exact hx₁blocked (Finset.mem_union_left _ (by simpa using hx₁C))
  · intro hx₂C
    exact hx₂blocked (Finset.mem_union_left _ (by simpa using hx₂C))
  · intro hx₁R
    exact hx₁blocked (Finset.mem_union_right _ hx₁R)
  · intro hx₂R
    exact hx₂blocked (Finset.mem_union_right _ hx₂R)

/-- A path between two distinct neighbors of `v`, internally avoiding `v`,
closes through `v` to a cycle two edges longer. -/
theorem exists_cycle_of_neighbor_path_avoiding
    {v a b : V} (hva : G.Adj v a) (hvb : G.Adj v b) (hab : a ≠ b)
    (p : G.Walk a b) (hp : p.IsPath)
    (hpv : p.Avoids ({v} : Set V) ({a, b} : Set V)) :
    ∃ C : G.Walk b b, C.IsCycle ∧ C.length = p.length + 2 := by
  have hvaNe : v ≠ a := G.ne_of_adj hva
  have hvbNe : v ≠ b := G.ne_of_adj hvb
  have hvNotSupport : v ∉ p.support := by
    intro hvp
    have hvab := hpv v hvp (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hvab
    exact hvab.elim hvaNe hvbNe
  let q : G.Walk v b := Walk.cons hva p
  have hq : q.IsPath := by
    simp [q, Walk.cons_isPath_iff, hp, hvNotSupport, hvaNe]
  have hpPos : 0 < p.length := by
    by_contra hzero
    have hpzero : p.length = 0 := by omega
    exact hab (p.eq_of_length_eq_zero hpzero)
  have hqLong : 1 < q.length := by
    simp [q]
    omega
  let C : G.Walk b b := Walk.cons hvb.symm q
  refine ⟨C, ?_, ?_⟩
  · exact hq.isCycle_cons_of_adj hqLong hvb.symm
  · simp [C, q]

/-- Split off two disjoint subsets of the same prescribed size. -/
theorem exists_two_disjoint_subsets_card_eq
    (S : Finset V) {s : ℕ} (hcard : 2 * s ≤ S.card) :
    ∃ A B : Finset V,
      A ⊆ S ∧ B ⊆ S ∧ Disjoint A B ∧ A.card = s ∧ B.card = s := by
  classical
  have hsS : s ≤ S.card := by omega
  obtain ⟨A, hAS, hAcard⟩ := Finset.exists_subset_card_eq hsS
  have hsRemaining : s ≤ (S \ A).card := by
    rw [Finset.card_sdiff_of_subset hAS, hAcard]
    omega
  obtain ⟨B, hBRemaining, hBcard⟩ :=
    Finset.exists_subset_card_eq hsRemaining
  refine ⟨A, B, hAS, hBRemaining.trans Finset.sdiff_subset, ?_, hAcard, hBcard⟩
  rw [Finset.disjoint_left]
  intro v hvA hvB
  exact (Finset.mem_sdiff.1 (hBRemaining hvB)).2 hvA

/-- Two equal disjoint blocks of neighbors of a high-degree vertex. -/
theorem exists_two_disjoint_neighbor_sets [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) {s : ℕ}
    (hdegree : 2 * s ≤ G.degree v) :
    ∃ A B : Finset V,
      A ⊆ G.neighborFinset v ∧ B ⊆ G.neighborFinset v ∧
        Disjoint A B ∧ A.card = s ∧ B.card = s := by
  apply exists_two_disjoint_subsets_card_eq (G.neighborFinset v)
  rw [G.card_neighborFinset_eq_degree]
  exact hdegree

/-- A concrete short-cycle constructor from the expander inequality.  It
splits the neighborhood of one vertex into two equal blocks, joins the blocks
while avoiding that vertex, and closes the resulting path through it. -/
theorem exists_short_cycle_through_vertex_of_lmExpander_growth [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (epsilon kappa : ℝ) (hexp : IsLMExpander G epsilon kappa)
    (v : V) (s q radius : ℕ)
    (hdegree : 2 * s ≤ G.degree v)
    (hlower : kappa / 2 ≤ (s : ℝ))
    (hrate : ∀ t : ℕ, s ≤ t → t ≤ Fintype.card V / 2 →
      (((1 + q : ℕ) : ℝ) ≤
        expansionEpsilon epsilon kappa t * (t : ℝ)))
    (hsteps : Fintype.card V / 2 + 1 ≤ s + radius * q) :
    ∃ c : V, ∃ C : G.Walk c c,
      C.IsCycle ∧ C.length ≤ 2 * radius + 2 := by
  classical
  obtain ⟨A, B, hA, hB, hAB, hAcard, hBcard⟩ :=
    exists_two_disjoint_neighbor_sets G v hdegree
  obtain ⟨a, ha, b, hb, p, hp, hplen⟩ :=
    exists_avoiding_path_between_of_lmExpander_growth
      G epsilon kappa hexp {v} A B q radius
      (by simpa [hAcard] using hlower)
      (by simpa [hBcard] using hlower)
      (fun t ht htN ↦ by
        simpa using hrate t (by simpa [hAcard] using ht) htN)
      (fun t ht htN ↦ by
        simpa using hrate t (by simpa [hBcard] using ht) htN)
      (by simpa [hAcard] using hsteps)
      (by simpa [hBcard] using hsteps)
  have hva : G.Adj v a := (G.mem_neighborFinset v a).1 (hA ha)
  have hvb : G.Adj v b := (G.mem_neighborFinset v b).1 (hB hb)
  have hab : a ≠ b := by
    intro h
    subst b
    exact (Finset.disjoint_left.1 hAB ha hb).elim
  obtain ⟨C, hC, hClength⟩ :=
    exists_cycle_of_neighbor_path_avoiding hva hvb hab p hp.1 (by
      change p.Avoids ({v} : Set V) ({a, b} : Set V)
      simpa using hp.2)
  exact ⟨b, C, hC, by omega⟩

/-- Shortest-cycle form of the preceding concrete construction. -/
theorem exists_shortest_cycle_of_lmExpander_growth [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (epsilon kappa : ℝ) (hexp : IsLMExpander G epsilon kappa)
    (v : V) (s q radius : ℕ)
    (hdegree : 2 * s ≤ G.degree v)
    (hlower : kappa / 2 ≤ (s : ℝ))
    (hrate : ∀ t : ℕ, s ≤ t → t ≤ Fintype.card V / 2 →
      (((1 + q : ℕ) : ℝ) ≤
        expansionEpsilon epsilon kappa t * (t : ℝ)))
    (hsteps : Fintype.card V / 2 + 1 ≤ s + radius * q) :
    ∃ c : V, ∃ C : G.Walk c c,
      IsShortestCycle C ∧ C.length ≤ 2 * radius + 2 := by
  obtain ⟨c₀, C₀, hC₀, hC₀length⟩ :=
    exists_short_cycle_through_vertex_of_lmExpander_growth
      G epsilon kappa hexp v s q radius hdegree hlower hrate hsteps
  obtain ⟨c, C, hC, hClength⟩ := exists_shortestCycle_of_cycle C₀ hC₀
  exact ⟨c, C, hC, hClength.trans hC₀length⟩

/-! ## Connecting the roots of two concrete expansions -/

private theorem Walk.avoids_empty_of_supported_disjoint {x y : V}
    {p : G.Walk x y} {S W : Finset V}
    (hsupport : ∀ z ∈ p.support, z ∈ S) (hSW : Disjoint S W) :
    p.Avoids (W : Set V) ∅ := by
  intro z hz hzW
  exact (Finset.disjoint_left.1 hSW (hsupport z hz) hzW).elim

private theorem Walk.avoids_empty_of_endpoints_outside {a b : V}
    {p : G.Walk a b} {W : Finset V}
    (hp : p.Avoids (W : Set V) ({a, b} : Set V))
    (ha : a ∉ W) (hb : b ∉ W) : p.Avoids (W : Set V) ∅ := by
  intro z hz hzW
  have hzab := hp z hz hzW
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzab
  rcases hzab with rfl | rfl
  · exact (ha hzW).elim
  · exact (hb hzW).elim

/-- A walk avoiding a set altogether has support disjoint from every walk
supported in that set. -/
theorem Walk.support_disjoint_of_avoids_empty {a b c d : V}
    {p : G.Walk a b} {q : G.Walk c d} {X : Set V}
    (hp : p.Avoids X ∅) (hq : ∀ z ∈ q.support, z ∈ X) :
    p.support.Disjoint q.support := by
  rw [List.disjoint_left]
  intro z hzp hzq
  exact (hp z hzp (hq z hzq)).elim

/-- Symmetric form of `support_disjoint_of_avoids_empty`. -/
theorem Walk.support_disjoint_of_supported_avoids_empty {a b c d : V}
    {p : G.Walk a b} {q : G.Walk c d} {X : Set V}
    (hp : ∀ z ∈ p.support, z ∈ X) (hq : q.Avoids X ∅) :
    p.support.Disjoint q.support :=
  (Walk.support_disjoint_of_avoids_empty hq hp).symm

/-- A graph-free multiplicative growth curve for the two connectors in Lemma
4.2.  It is the scalar content of `BallGrowthSchedule`, with the ambient order
made an explicit natural number so eventual parameter proofs do not quantify
over a graph. -/
structure LM42GrowthSchedule (N start workspace radius : ℕ)
    (epsilon kappa : ℝ) where
  size : ℕ → ℕ
  initial : size 0 ≤ start
  lower : ∀ i ≤ radius, kappa / 2 ≤ (size i : ℝ)
  target : N / 2 + 1 ≤ size radius
  step : ∀ i < radius, ∀ s : ℕ,
    size i ≤ s → s ≤ N / 2 →
      ((((workspace + (size (i + 1) - s) : ℕ) : ℝ)) ≤
        expansionEpsilon epsilon kappa s * (s : ℝ))

/-- Interpret a graph-free Lemma 4.2 curve at a finite graph of the certified
order. -/
def LM42GrowthSchedule.toBallGrowthSchedule [Fintype V]
    (G : SimpleGraph V) {N start workspace radius : ℕ}
    {epsilon kappa : ℝ}
    (S : LM42GrowthSchedule N start workspace radius epsilon kappa)
    (hN : Fintype.card V = N) :
    BallGrowthSchedule G epsilon kappa start workspace radius where
  size := S.size
  initial := S.initial
  lower := S.lower
  target := by simpa only [hN] using S.target
  step := by
    intro i hi s hs hsN
    apply S.step i hi s hs
    simpa only [hN] using hsN

/-- The direct Lemma 3.4 connector, extended through two vertex expansions
to their roots.  The conclusion is still derived solely from the concrete
Liu--Montgomery expander inequality. -/
theorem exists_expansion_root_connector_of_lmExpander_growth [Fintype V]
    {x y : V} {D₁ D₂ m₁ m₂ : ℕ}
    (E : VertexExpansion G x D₁ m₁)
    (F : VertexExpansion G y D₂ m₂)
    (W : Finset V) (hEW : Disjoint E.verts W) (hFW : Disjoint F.verts W)
    (epsilon k : ℝ) (hexp : IsLMExpander G epsilon k)
    (q radius : ℕ)
    (hElower : k / 2 ≤ (E.verts.card : ℝ))
    (hFlower : k / 2 ≤ (F.verts.card : ℝ))
    (hErate : ∀ s : ℕ, E.verts.card ≤ s → s ≤ Fintype.card V / 2 →
      (((W.card + q : ℕ) : ℝ) ≤
        expansionEpsilon epsilon k s * (s : ℝ)))
    (hFrate : ∀ s : ℕ, F.verts.card ≤ s → s ≤ Fintype.card V / 2 →
      (((W.card + q : ℕ) : ℝ) ≤
        expansionEpsilon epsilon k s * (s : ℝ)))
    (hEsteps : Fintype.card V / 2 + 1 ≤ E.verts.card + radius * q)
    (hFsteps : Fintype.card V / 2 + 1 ≤ F.verts.card + radius * q) :
    ∃ P : G.Walk x y,
      P.IsPath ∧ P.Avoids (W : Set V) ∅ ∧
        P.length ≤ m₁ + 2 * radius + m₂ := by
  classical
  obtain ⟨a, ha, b, hb, p, hp, hplen⟩ :=
    exists_avoiding_path_between_of_lmExpander_growth
      G epsilon k hexp W E.verts F.verts q radius
      hElower hFlower hErate hFrate hEsteps hFsteps
  obtain ⟨px, hpx, hpxlen, hpxsupport⟩ := E.exists_path ha
  obtain ⟨py, hpy, hpylen, hpysupport⟩ := F.exists_path hb
  have haW : a ∉ W := fun ha' ↦
    Finset.disjoint_left.1 hEW ha ha'
  have hbW : b ∉ W := fun hb' ↦
    Finset.disjoint_left.1 hFW hb hb'
  have hpxavoid : px.Avoids (W : Set V) ∅ :=
    Walk.avoids_empty_of_supported_disjoint hpxsupport hEW
  have hpyavoid : py.Avoids (W : Set V) ∅ :=
    Walk.avoids_empty_of_supported_disjoint hpysupport hFW
  have hpavoid : p.Avoids (W : Set V) ∅ :=
    Walk.avoids_empty_of_endpoints_outside hp.2 haW hbW
  let w : G.Walk x y := (px.append p).append py.reverse
  have hwavoid : w.Avoids (W : Set V) ∅ := by
    intro z hz hzW
    change z ∈ ((px.append p).append py.reverse).support at hz
    rw [Walk.mem_support_append_iff, Walk.mem_support_append_iff] at hz
    rcases hz with (hz | hz) | hz
    · exact hpxavoid z hz hzW
    · exact hpavoid z hz hzW
    · exact hpyavoid.reverse z hz hzW
  refine ⟨w.bypass, w.bypass_isPath,
    hwavoid.of_support_subset w.support_bypass_subset_support, ?_⟩
  calc
    w.bypass.length ≤ w.length := w.length_bypass_le_length
    _ = px.length + p.length + py.length := by
      simp [w, Walk.length_append]
    _ ≤ m₁ + 2 * radius + m₂ := by omega

/-- Multiplicative-growth version of the preceding root connector.  Each
endpoint may either already meet the schedule's starting size or use the
minimum-degree bootstrap branch of Lemma 3.4. -/
theorem exists_expansion_root_connector_of_LM42GrowthSchedule [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y : V} {D₁ D₂ m₁ m₂ start workspace radius : ℕ}
    (E : VertexExpansion G x D₁ m₁)
    (F : VertexExpansion G y D₂ m₂)
    (W : Finset V) (hEW : Disjoint E.verts W) (hFW : Disjoint F.verts W)
    (epsilon kappa : ℝ) (hexp : IsLMExpander G epsilon kappa)
    (degreeScale : ℕ) (hdegree : ∀ v : V, degreeScale ≤ G.degree v)
    (hW : W.card ≤ workspace)
    (hEseed : start ≤ E.verts.card ∨ start + workspace ≤ degreeScale)
    (hFseed : start ≤ F.verts.card ∨ start + workspace ≤ degreeScale)
    (growth : LM42GrowthSchedule (Fintype.card V) start workspace radius
      epsilon kappa) :
    ∃ P : G.Walk x y,
      P.IsPath ∧ P.Avoids (W : Set V) ∅ ∧
        P.length ≤ m₁ + 2 * (radius + 1) + m₂ := by
  let originalDecAdj : DecidableRel G.Adj := inferInstance
  classical
  let : DecidableRel G.Adj := originalDecAdj
  obtain ⟨a, ha, b, hb, p, hp, hpavoid, hplen⟩ :=
    exists_short_set_connector_ge G epsilon kappa hexp degreeScale
      hdegree W E.verts F.verts start workspace radius
      hW ⟨x, E.root_mem⟩ ⟨y, F.root_mem⟩ hEseed hFseed
      hEW hFW (growth.toBallGrowthSchedule G rfl)
  obtain ⟨px, hpx, hpxlen, hpxsupport⟩ := E.exists_path ha
  obtain ⟨py, hpy, hpylen, hpysupport⟩ := F.exists_path hb
  have hpxavoid : px.Avoids (W : Set V) ∅ :=
    Walk.avoids_empty_of_supported_disjoint hpxsupport hEW
  have hpyavoid : py.Avoids (W : Set V) ∅ :=
    Walk.avoids_empty_of_supported_disjoint hpysupport hFW
  let w : G.Walk x y := (px.append p).append py.reverse
  have hwavoid : w.Avoids (W : Set V) ∅ := by
    intro z hz hzW
    change z ∈ ((px.append p).append py.reverse).support at hz
    rw [Walk.mem_support_append_iff, Walk.mem_support_append_iff] at hz
    rcases hz with (hz | hz) | hz
    · exact hpxavoid z hz hzW
    · exact hpavoid z hz hzW
    · exact hpyavoid.reverse z hz hzW
  refine ⟨w.bypass, w.bypass_isPath,
    hwavoid.of_support_subset w.support_bypass_subset_support, ?_⟩
  calc
    w.bypass.length ≤ w.length := w.length_bypass_le_length
    _ = px.length + p.length + py.length := by simp [w, Walk.length_append]
    _ ≤ m₁ + 2 * (radius + 1) + m₂ := by omega

/-! ## Enlarging an existing expansion by an avoiding set-ball -/

/-- Enlarge a rooted expansion by taking an avoiding ball around its entire
vertex set.  A path from the old root to a new vertex is obtained by first
moving inside the old expansion to the seed of the witnessing avoiding path,
then appending that path and erasing loops. -/
noncomputable def VertexExpansion.ofBallAvoidingFrom [Fintype V]
    {x : V} {D oldRadius : ℕ}
    (E : VertexExpansion G x D oldRadius) (forbidden : Set V) (radius : ℕ) :
    VertexExpansion G x
      (ballAvoidingFrom G forbidden E.verts radius).card
      (oldRadius + radius) where
  vertices := ballAvoidingFrom G forbidden E.verts radius
  root_mem := subset_ballAvoidingFrom G forbidden E.verts radius E.root_mem
  card_vertices := rfl
  path_to := by
    intro y hy
    obtain ⟨a, ha, q, hq, hqLength⟩ :=
      (mem_ballAvoidingFrom G forbidden E.verts radius y).1 hy
    obtain ⟨p, hp, hpLength, hpSupport⟩ := E.exists_path ha
    let w : G.Walk x y := p.append q
    refine ⟨w.bypass, w.bypass_isPath, ?_, ?_⟩
    · calc
        w.bypass.length ≤ w.length := w.length_bypass_le_length
        _ = p.length + q.length := by simp [w]
        _ ≤ oldRadius + radius := Nat.add_le_add hpLength hqLength
    · intro z hz
      have hzw : z ∈ w.support := w.support_bypass_subset_support hz
      change z ∈ (p.append q).support at hzw
      rw [Walk.mem_support_append_iff] at hzw
      rcases hzw with hzp | hzq
      · exact subset_ballAvoidingFrom G forbidden E.verts radius
          (hpSupport z hzp)
      · exact support_subset_ballAvoidingFrom ha hq hqLength z hzq

@[simp] theorem VertexExpansion.verts_ofBallAvoidingFrom [Fintype V]
    {x : V} {D oldRadius : ℕ}
    (E : VertexExpansion G x D oldRadius) (forbidden : Set V) (radius : ℕ) :
    (E.ofBallAvoidingFrom forbidden radius).verts =
      ballAvoidingFrom G forbidden E.verts radius := rfl

/-- If the initial expansion misses the deleted set, then the whole avoiding
ball around it misses that set. -/
theorem VertexExpansion.disjoint_ofBallAvoidingFrom [Fintype V]
    {x : V} {D oldRadius : ℕ}
    (E : VertexExpansion G x D oldRadius) (forbidden : Finset V) (radius : ℕ)
    (hE : Disjoint E.verts forbidden) :
    Disjoint (E.ofBallAvoidingFrom (forbidden : Set V) radius).verts forbidden := by
  let originalDecEq : DecidableEq V := inferInstance
  classical
  let : DecidableEq V := originalDecEq
  rw [Finset.disjoint_left]
  intro y hyBall hyForbidden
  exact ballAvoidingFrom_avoids_forbidden G (forbidden : Set V) E.verts radius
    (fun a ha haForbidden ↦
      (Finset.disjoint_left.1 hE ha haForbidden).elim)
    y (by simpa using hyBall) hyForbidden

/-- A set-ball misses its forbidden finset when every seed misses it. -/
theorem disjoint_ballAvoidingFrom_forbidden [Fintype V]
    (G : SimpleGraph V) (A W : Finset V) (radius : ℕ)
    (hAW : Disjoint A W) :
    Disjoint (ballAvoidingFrom G (W : Set V) A radius) W := by
  rw [Finset.disjoint_left]
  intro y hyBall hyW
  exact ballAvoidingFrom_avoids_forbidden G (W : Set V) A radius
    (fun a ha haW ↦ (Finset.disjoint_left.1 hAW ha haW).elim)
    y hyBall hyW

/-- Grow both ends of an adjuster inside two specified avoiding balls and
shrink them to the same prescribed order.  All geometric separation is stated
directly for the two balls, so the result can be applied verbatim after the
correlated Lemma 3.7 in Claims 4.5 and 4.6. -/
theorem Adjuster.exists_replaceEnds_of_avoidingBalls [Fintype V]
    {D₀ oldRadius k target radius : ℕ}
    (A : Adjuster G D₀ oldRadius k)
    (leftForbidden rightForbidden : Set V)
    (htarget : 0 < target)
    (hleftCard : target ≤
      (ballAvoidingFrom G leftForbidden A.leftEnd.verts radius).card)
    (hrightCard : target ≤
      (ballAvoidingFrom G rightForbidden A.rightEnd.verts radius).card)
    (hcoreLeft : Disjoint A.core
      (ballAvoidingFrom G leftForbidden A.leftEnd.verts radius))
    (hcoreRight : Disjoint A.core
      (ballAvoidingFrom G rightForbidden A.rightEnd.verts radius))
    (hballs : Disjoint
      (ballAvoidingFrom G leftForbidden A.leftEnd.verts radius)
      (ballAvoidingFrom G rightForbidden A.rightEnd.verts radius)) :
    ∃ A' : Adjuster G target (oldRadius + radius) k,
      A'.leftEnd.verts ⊆
          ballAvoidingFrom G leftForbidden A.leftEnd.verts radius ∧
        A'.rightEnd.verts ⊆
          ballAvoidingFrom G rightForbidden A.rightEnd.verts radius ∧
        A'.core = A.core := by
  let originalDecEq : DecidableEq V := inferInstance
  classical
  let : DecidableEq V := originalDecEq
  let leftFull := A.leftEnd.ofBallAvoidingFrom leftForbidden radius
  let rightFull := A.rightEnd.ofBallAvoidingFrom rightForbidden radius
  obtain ⟨left, hleft⟩ := leftFull.proposition3_10 htarget (by
    simpa [leftFull] using hleftCard)
  obtain ⟨right, hright⟩ := rightFull.proposition3_10 htarget (by
    simpa [rightFull] using hrightCard)
  have hleftBall : left.verts ⊆
      ballAvoidingFrom G leftForbidden A.leftEnd.verts radius := by
    simpa [leftFull] using hleft
  have hrightBall : right.verts ⊆
      ballAvoidingFrom G rightForbidden A.rightEnd.verts radius := by
    simpa [rightFull] using hright
  let A' : Adjuster G target (oldRadius + radius) k :=
    A.replaceEnds left right
      (hcoreLeft.mono_right hleftBall)
      (hcoreRight.mono_right hrightBall)
      (hballs.mono hleftBall hrightBall)
      (Nat.le_add_right oldRadius radius)
  exact ⟨A', hleftBall, hrightBall, rfl⟩

/-- Shrink both end expansions of an adjuster to a common positive order.

This operation leaves the core and all adjustable routes unchanged.  It is
the final bookkeeping step in the corrected proof of Lemma 4.7: the join is
performed with end order enlarged by a logarithmic factor so that the whole
ambient forbidden set is affordable, and the two surviving ends are then
shrunk back to the order in the statement. -/
theorem Adjuster.exists_shrinkEnds
    {largeOrder target radius k : ℕ}
    (A : Adjuster G largeOrder radius k)
    (htarget : 0 < target) (hle : target ≤ largeOrder) :
    ∃ A' : Adjuster G target radius k,
      A'.core = A.core ∧ A'.leftRoot = A.leftRoot ∧
        A'.rightRoot = A.rightRoot ∧ A'.verts ⊆ A.verts := by
  let originalDecEq : DecidableEq V := inferInstance
  classical
  let : DecidableEq V := originalDecEq
  obtain ⟨left, hleft⟩ := A.leftEnd.proposition3_10 htarget hle
  obtain ⟨right, hright⟩ := A.rightEnd.proposition3_10 htarget hle
  let A' : Adjuster G target radius k :=
    A.replaceEnds left right
      (A.core_disjoint_left.mono_right hleft)
      (A.core_disjoint_right.mono_right hright)
      (A.ends_disjoint.mono hleft hright)
      le_rfl
  refine ⟨A', rfl, rfl, rfl, ?_⟩
  intro v hv
  change v ∈ left.verts ∪ right.verts ∪ A.core at hv
  change v ∈ A.leftEnd.verts ∪ A.rightEnd.verts ∪ A.core
  simp only [Finset.mem_union] at hv ⊢
  rcases hv with (hvLeft | hvRight) | hvCore
  · exact Or.inl (Or.inl (hleft hvLeft))
  · exact Or.inl (Or.inr (hright hvRight))
  · exact Or.inr hvCore

/-- Promote avoidance by all non-root vertices of an expansion to full
disjointness when the root itself also lies outside the forbidden set. -/
theorem VertexExpansion.disjoint_of_trim_disjoint
    {x : V} {D radius : ℕ} (E : VertexExpansion G x D radius)
    (W : Finset V) (htrim : Disjoint (E.verts \ {x}) W) (hxW : x ∉ W) :
    Disjoint E.verts W := by
  rw [Finset.disjoint_left]
  intro z hzE hzW
  by_cases hzx : z = x
  · exact hxW (hzx ▸ hzW)
  · exact (Finset.disjoint_left.1 htrim (by simpa using ⟨hzE, hzx⟩) hzW).elim

/-- Replace both ends by fresh radius-one stars.  This is the concrete
high-degree alternative in Claim 4.4: no abstract end-supply premise is used;
the stars are obtained from the actual degrees of the two roots. -/
theorem Adjuster.exists_replaceEnds_byStars [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {D₀ oldRadius k target newRadius budget : ℕ}
    (A : Adjuster G D₀ oldRadius k) (U : Finset V)
    (hAU : Disjoint U A.verts) (htarget : 0 < target)
    (hbudget : U.card + A.core.card + target + 1 ≤ budget)
    (hleftDegree : target + budget ≤ G.degree A.leftRoot)
    (hrightDegree : target + budget ≤ G.degree A.rightRoot)
    (honeRadius : 1 ≤ newRadius) (holdRadius : oldRadius ≤ newRadius) :
    ∃ A' : Adjuster G target newRadius k,
      A'.core = A.core ∧ Disjoint U A'.verts := by
  let originalDecEq : DecidableEq V := inferInstance
  classical
  let : DecidableEq V := originalDecEq
  have hleftU : A.leftRoot ∉ U := by
    intro h
    exact (Finset.disjoint_left.1 hAU h A.leftRoot_mem_verts).elim
  have hrightU : A.rightRoot ∉ U := by
    intro h
    exact (Finset.disjoint_left.1 hAU h A.rightRoot_mem_verts).elim
  have hleftCore : A.leftRoot ∉ A.core := by
    intro h
    exact (Finset.disjoint_left.1 A.core_disjoint_left h
      A.leftEnd.root_mem).elim
  have hrightCore : A.rightRoot ∉ A.core := by
    intro h
    exact (Finset.disjoint_left.1 A.core_disjoint_right h
      A.rightEnd.root_mem).elim
  have hroots : A.leftRoot ≠ A.rightRoot := by
    intro h
    exact (Finset.disjoint_left.1 A.ends_disjoint A.leftEnd.root_mem
      (h.symm ▸ A.rightEnd.root_mem)).elim
  let firstForbidden : Finset V := U ∪ A.core ∪ {A.rightRoot}
  have hfirstCard : firstForbidden.card ≤ budget := by
    have h₁ := Finset.card_union_le U A.core
    have h₂ := Finset.card_union_le (U ∪ A.core) ({A.rightRoot} : Finset V)
    dsimp [firstForbidden]
    simp only [Finset.card_singleton] at h₂
    omega
  obtain ⟨leftOne, hleftTrim⟩ := exists_starExpansion_avoiding
    G A.leftRoot firstForbidden target htarget
      (by exact (Nat.add_le_add_left hfirstCard target).trans hleftDegree)
  have hleftRootFirst : A.leftRoot ∉ firstForbidden := by
    simp [firstForbidden, hleftU, hleftCore, hroots]
  have hleftFull : Disjoint leftOne.verts firstForbidden := by
    rw [Finset.disjoint_left]
    intro z hzLeft hzForbidden
    by_cases hzx : z = A.leftRoot
    · exact hleftRootFirst (hzx ▸ hzForbidden)
    · exact (Finset.disjoint_left.1 hleftTrim (by
        rw [Finset.mem_sdiff, Finset.mem_singleton]
        exact ⟨hzLeft, hzx⟩) hzForbidden).elim
  let secondForbidden : Finset V := U ∪ A.core ∪ leftOne.verts
  have hsecondCard : secondForbidden.card ≤ budget := by
    have h₁ := Finset.card_union_le U A.core
    have h₂ := Finset.card_union_le (U ∪ A.core) leftOne.verts
    have hleftCard := leftOne.card_verts
    dsimp [secondForbidden]
    omega
  obtain ⟨rightOne, hrightTrim⟩ := exists_starExpansion_avoiding
    G A.rightRoot secondForbidden target htarget
      (by exact (Nat.add_le_add_left hsecondCard target).trans hrightDegree)
  have hrightNotLeft : A.rightRoot ∉ leftOne.verts := by
    intro h
    exact (Finset.disjoint_left.1 hleftFull h (by simp [firstForbidden])).elim
  have hrightRootSecond : A.rightRoot ∉ secondForbidden := by
    simp [secondForbidden, hrightU, hrightCore, hrightNotLeft]
  have hrightFull : Disjoint rightOne.verts secondForbidden := by
    rw [Finset.disjoint_left]
    intro z hzRight hzForbidden
    by_cases hzx : z = A.rightRoot
    · exact hrightRootSecond (hzx ▸ hzForbidden)
    · exact (Finset.disjoint_left.1 hrightTrim (by
        rw [Finset.mem_sdiff, Finset.mem_singleton]
        exact ⟨hzRight, hzx⟩) hzForbidden).elim
  let left : VertexExpansion G A.leftRoot target newRadius :=
    leftOne.radiusMono honeRadius
  let right : VertexExpansion G A.rightRoot target newRadius :=
    rightOne.radiusMono honeRadius
  have hcoreLeft : Disjoint A.core left.verts := by
    apply (hleftFull.mono_right ?_).symm
    intro z hz
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hz)
  have hcoreRight : Disjoint A.core right.verts := by
    apply (hrightFull.mono_right ?_).symm
    intro z hz
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hz)
  have hends : Disjoint left.verts right.verts := by
    apply (hrightFull.mono_right ?_).symm
    intro z hz
    exact Finset.mem_union_right _ hz
  let A' : Adjuster G target newRadius k :=
    A.replaceEnds left right hcoreLeft hcoreRight hends holdRadius
  refine ⟨A', rfl, ?_⟩
  rw [Finset.disjoint_left]
  intro z hzU hzA'
  change z ∈ left.verts ∪ right.verts ∪ A.core at hzA'
  simp only [Finset.mem_union] at hzA'
  rcases hzA' with (hzLeft | hzRight) | hzCore
  · exact (Finset.disjoint_left.1 hleftFull hzLeft (by
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hzU))).elim
  · exact (Finset.disjoint_left.1 hrightFull hzRight (by
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hzU))).elim
  · exact (Finset.disjoint_left.1 hAU hzU (A.core_subset_verts hzCore)).elim

/-- Attach a fresh star at the far endpoint of a path to one existing
expansion.  This is the end-construction used after the shortest connection
to the high-degree set in Claim 4.5. -/
theorem VertexExpansion.exists_attach_path_star [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {root a t : V} {D₀ oldRadius pathRadius target totalRadius : ℕ}
    (E : VertexExpansion G root D₀ oldRadius) (ha : a ∈ E.verts)
    (p : G.Walk a t) (hp : p.IsPath) (hpLength : p.length ≤ pathRadius)
    (forbidden : Finset V) (htarget : 0 < target)
    (htDegree : target + forbidden.card ≤ G.degree t)
    (hRadius : oldRadius + pathRadius + 1 ≤ totalRadius) :
    ∃ F : VertexExpansion G root target totalRadius,
      F.verts ⊆ E.verts ∪ p.support.toFinset ∪
        insert t ((Finset.univ : Finset V) \ forbidden) := by
  let originalDecEq : DecidableEq V := inferInstance
  classical
  let : DecidableEq V := originalDecEq
  obtain ⟨star, hstarTrim⟩ :=
    exists_starExpansion_avoiding G t forbidden target htarget htDegree
  obtain ⟨q, hq, hqLength, hqSupport⟩ := E.exists_path ha
  let w : G.Walk root t := q.append p
  have hwLength : w.bypass.length ≤ oldRadius + pathRadius := by
    calc
      w.bypass.length ≤ w.length := w.length_bypass_le_length
      _ = q.length + p.length := by simp [w]
      _ ≤ oldRadius + pathRadius := Nat.add_le_add hqLength hpLength
  obtain ⟨F, hF⟩ := exists_attached_vertexExpansion
    w.bypass w.bypass_isPath hwLength star hRadius
  refine ⟨F, ?_⟩
  intro z hzF
  have hz := Finset.mem_union.1 (hF hzF)
  rcases hz with hzW | hzStar
  · have hzw : z ∈ w.support :=
      w.support_bypass_subset_support (by simpa using hzW)
    change z ∈ (q.append p).support at hzw
    rw [Walk.mem_support_append_iff] at hzw
    rcases hzw with hzQ | hzP
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (hqSupport z hzQ))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simpa using hzP))
  · apply Finset.mem_union_right
    by_cases hzt : z = t
    · simp [hzt]
    · have hzTrim : z ∈ star.verts \ {t} := by
        rw [Finset.mem_sdiff, Finset.mem_singleton]
        exact ⟨hzStar, hzt⟩
      have hzNotForbidden : z ∉ forbidden := fun hzForbidden ↦
        (Finset.disjoint_left.1 hstarTrim hzTrim hzForbidden).elim
      simp [hzt, hzNotForbidden]

/-- Disjointness corollary of `exists_attach_path_star`. -/
theorem VertexExpansion.exists_attach_path_star_disjoint [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {root a t : V} {D₀ oldRadius pathRadius target totalRadius : ℕ}
    (E : VertexExpansion G root D₀ oldRadius) (ha : a ∈ E.verts)
    (p : G.Walk a t) (hp : p.IsPath) (hpLength : p.length ≤ pathRadius)
    (forbidden : Finset V) (hE : Disjoint E.verts forbidden)
    (hpAvoid : p.Avoids (forbidden : Set V) ∅)
    (htarget : 0 < target)
    (htDegree : target + forbidden.card ≤ G.degree t)
    (hRadius : oldRadius + pathRadius + 1 ≤ totalRadius) :
    ∃ F : VertexExpansion G root target totalRadius,
      Disjoint F.verts forbidden := by
  obtain ⟨F, hF⟩ := E.exists_attach_path_star G ha p hp hpLength
    forbidden htarget htDegree hRadius
  refine ⟨F, ?_⟩
  rw [Finset.disjoint_left]
  intro z hzF hzForbidden
  have hz := hF hzF
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_sdiff,
    Finset.mem_univ, true_and, List.mem_toFinset] at hz
  rcases hz with (hzE | hzP) | hzt | hzOutside
  · exact (Finset.disjoint_left.1 hE hzE hzForbidden).elim
  · exact hpAvoid z hzP hzForbidden
  · subst z
    exact hpAvoid t p.end_mem_support hzForbidden
  · exact hzOutside hzForbidden

/-- Attach a path from an existing end to an arbitrary vertex of a second
bounded expansion.  Re-rooting the latter pays twice its radius.  This is the
end-construction used with the small-diameter set from Lemma 3.12 in Claim
4.6. -/
theorem VertexExpansion.exists_attach_path_expansion
    {root a z center : V}
    {D₀ oldRadius pathRadius D₁ farRadius totalRadius : ℕ}
    (E : VertexExpansion G root D₀ oldRadius) (ha : a ∈ E.verts)
    (p : G.Walk a z) (hp : p.IsPath) (hpLength : p.length ≤ pathRadius)
    (Z : VertexExpansion G center D₁ farRadius) (hz : z ∈ Z.verts)
    (hRadius : oldRadius + pathRadius + 2 * farRadius ≤ totalRadius) :
    ∃ F : VertexExpansion G root D₁ totalRadius,
      F.verts ⊆ E.verts ∪ p.support.toFinset ∪ Z.verts := by
  let originalDecEq : DecidableEq V := inferInstance
  classical
  let : DecidableEq V := originalDecEq
  obtain ⟨q, hq, hqLength, hqSupport⟩ := E.exists_path ha
  let w : G.Walk root z := q.append p
  have hwLength : w.bypass.length ≤ oldRadius + pathRadius := by
    calc
      w.bypass.length ≤ w.length := w.length_bypass_le_length
      _ = q.length + p.length := by simp [w]
      _ ≤ oldRadius + pathRadius := Nat.add_le_add hqLength hpLength
  let Z' := Z.reroot hz
  obtain ⟨F, hF⟩ := exists_attached_vertexExpansion
    w.bypass w.bypass_isPath hwLength Z' hRadius
  refine ⟨F, ?_⟩
  intro v hvF
  have hv := Finset.mem_union.1 (hF hvF)
  rcases hv with hvW | hvZ
  · have hvw : v ∈ w.support :=
      w.support_bypass_subset_support (by simpa using hvW)
    change v ∈ (q.append p).support at hvw
    rw [Walk.mem_support_append_iff] at hvw
    rcases hvw with hvQ | hvP
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (hqSupport v hvQ))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simpa using hvP))
  · exact Finset.mem_union_right _ (by simpa [Z'] using hvZ)

/-- Disjointness corollary of `exists_attach_path_expansion`. -/
theorem VertexExpansion.exists_attach_path_expansion_disjoint
    {root a z center : V}
    {D₀ oldRadius pathRadius D₁ farRadius totalRadius : ℕ}
    (E : VertexExpansion G root D₀ oldRadius) (ha : a ∈ E.verts)
    (p : G.Walk a z) (hp : p.IsPath) (hpLength : p.length ≤ pathRadius)
    (Z : VertexExpansion G center D₁ farRadius) (hz : z ∈ Z.verts)
    (forbidden : Finset V) (hE : Disjoint E.verts forbidden)
    (hpAvoid : p.Avoids (forbidden : Set V) ∅)
    (hZ : Disjoint Z.verts forbidden)
    (hRadius : oldRadius + pathRadius + 2 * farRadius ≤ totalRadius) :
    ∃ F : VertexExpansion G root D₁ totalRadius,
      Disjoint F.verts forbidden := by
  obtain ⟨F, hF⟩ := E.exists_attach_path_expansion ha p hp hpLength Z hz hRadius
  refine ⟨F, ?_⟩
  rw [Finset.disjoint_left]
  intro v hvF hvForbidden
  have hv := hF hvF
  simp only [Finset.mem_union, List.mem_toFinset] at hv
  rcases hv with (hvE | hvP) | hvZ
  · exact (Finset.disjoint_left.1 hE hvE hvForbidden).elim
  · exact hpAvoid v hvP hvForbidden
  · exact (Finset.disjoint_left.1 hZ hvZ hvForbidden).elim

/-- Attach a fresh star after two explicitly chosen consecutive paths.

This version is used in Claim 4.5.  The first path is the selected internal
arm `Qᵢ`; spelling it out ensures that the opposite avoiding ball can delete
that arm without charging the whole old end. -/
theorem exists_expansion_of_two_paths_star_disjoint [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {root a t : V} {armRadius pathRadius target totalRadius : ℕ}
    (q : G.Walk root a) (p : G.Walk a t)
    (hqLength : q.length ≤ armRadius) (hpLength : p.length ≤ pathRadius)
    (forbidden : Finset V)
    (hqAvoid : q.Avoids (forbidden : Set V) ∅)
    (hpAvoid : p.Avoids (forbidden : Set V) ∅)
    (htarget : 0 < target)
    (htDegree : target + forbidden.card ≤ G.degree t)
    (hRadius : armRadius + pathRadius + 1 ≤ totalRadius) :
    ∃ E : VertexExpansion G root target totalRadius,
      Disjoint E.verts forbidden := by
  let originalDecEq : DecidableEq V := inferInstance
  classical
  let : DecidableEq V := originalDecEq
  obtain ⟨star, hstarTrim⟩ :=
    exists_starExpansion_avoiding G t forbidden target htarget htDegree
  let w : G.Walk root t := q.append p
  have hwLength : w.bypass.length ≤ armRadius + pathRadius := by
    calc
      w.bypass.length ≤ w.length := w.length_bypass_le_length
      _ = q.length + p.length := by simp [w]
      _ ≤ armRadius + pathRadius := Nat.add_le_add hqLength hpLength
  obtain ⟨E, hE⟩ := exists_attached_vertexExpansion
    w.bypass w.bypass_isPath hwLength star hRadius
  refine ⟨E, ?_⟩
  rw [Finset.disjoint_left]
  intro z hzE hzForbidden
  rcases Finset.mem_union.1 (hE hzE) with hzW | hzStar
  · have hzw : z ∈ w.support :=
      w.support_bypass_subset_support (by simpa using hzW)
    change z ∈ (q.append p).support at hzw
    rw [Walk.mem_support_append_iff] at hzw
    exact hzw.elim
      (fun hzq ↦ hqAvoid z hzq hzForbidden)
      (fun hzp ↦ hpAvoid z hzp hzForbidden)
  · by_cases hzt : z = t
    · subst z
      exact hpAvoid t p.end_mem_support hzForbidden
    · exact (Finset.disjoint_left.1 hstarTrim (by
        rw [Finset.mem_sdiff, Finset.mem_singleton]
        exact ⟨hzStar, hzt⟩) hzForbidden).elim

/-- Claim 4.6 analogue of `exists_expansion_of_two_paths_star_disjoint`,
attaching a rerooted auxiliary expansion instead of a star. -/
theorem exists_expansion_of_two_paths_expansion_disjoint
    {root a z center : V}
    {armRadius pathRadius target farRadius totalRadius : ℕ}
    (q : G.Walk root a) (p : G.Walk a z)
    (hqLength : q.length ≤ armRadius) (hpLength : p.length ≤ pathRadius)
    (Z : VertexExpansion G center target farRadius) (hz : z ∈ Z.verts)
    (forbidden : Finset V)
    (hqAvoid : q.Avoids (forbidden : Set V) ∅)
    (hpAvoid : p.Avoids (forbidden : Set V) ∅)
    (hZ : Disjoint Z.verts forbidden)
    (hRadius : armRadius + pathRadius + 2 * farRadius ≤ totalRadius) :
    ∃ E : VertexExpansion G root target totalRadius,
      Disjoint E.verts forbidden := by
  let originalDecEq : DecidableEq V := inferInstance
  classical
  let : DecidableEq V := originalDecEq
  let w : G.Walk root z := q.append p
  have hwLength : w.bypass.length ≤ armRadius + pathRadius := by
    calc
      w.bypass.length ≤ w.length := w.length_bypass_le_length
      _ = q.length + p.length := by simp [w]
      _ ≤ armRadius + pathRadius := Nat.add_le_add hqLength hpLength
  let Z' := Z.reroot hz
  obtain ⟨E, hE⟩ := exists_attached_vertexExpansion
    w.bypass w.bypass_isPath hwLength Z' hRadius
  refine ⟨E, ?_⟩
  rw [Finset.disjoint_left]
  intro v hvE hvForbidden
  rcases Finset.mem_union.1 (hE hvE) with hvW | hvZ
  · have hvw : v ∈ w.support :=
      w.support_bypass_subset_support (by simpa using hvW)
    change v ∈ (q.append p).support at hvw
    rw [Walk.mem_support_append_iff] at hvw
    exact hvw.elim
      (fun hvq ↦ hqAvoid v hvq hvForbidden)
      (fun hvp ↦ hpAvoid v hvp hvForbidden)
  · exact (Finset.disjoint_left.1 hZ (by simpa [Z'] using hvZ) hvForbidden).elim

/-- Replace both ends by stars reached through two explicit two-piece arms.

The right end is built first while deleting the entire left arm.  The left
end is then built while deleting the completed right expansion.  This is the
deterministic contradiction at the heart of Claim 4.5: two distinct nearby
high-degree vertices would create the forbidden robust simple adjuster. -/
theorem Adjuster.exists_replaceEnds_byTwoPathStars [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {D₀ oldRadius k target armRadius pathRadius totalRadius : ℕ}
    (A : Adjuster G D₀ oldRadius k) (U : Finset V)
    (hAU : Disjoint U A.verts)
    {a t b y : V}
    (qLeft : G.Walk A.leftRoot a) (pLeft : G.Walk a t)
    (qRight : G.Walk A.rightRoot b) (pRight : G.Walk b y)
    (hqLeftLength : qLeft.length ≤ armRadius)
    (hpLeftLength : pLeft.length ≤ pathRadius)
    (hqRightLength : qRight.length ≤ armRadius)
    (hpRightLength : pRight.length ≤ pathRadius)
    (hleftAvoid : qLeft.Avoids ((U ∪ A.core : Finset V) : Set V) ∅ ∧
      pLeft.Avoids ((U ∪ A.core : Finset V) : Set V) ∅)
    (hrightAvoid : qRight.Avoids
        ((U ∪ A.core ∪ qLeft.support.toFinset ∪ pLeft.support.toFinset :
          Finset V) : Set V) ∅ ∧
      pRight.Avoids
        ((U ∪ A.core ∪ qLeft.support.toFinset ∪ pLeft.support.toFinset :
          Finset V) : Set V) ∅)
    (htarget : 0 < target)
    (hyDegree : target +
        (U ∪ A.core ∪ qLeft.support.toFinset ∪
          pLeft.support.toFinset).card ≤ G.degree y)
    (htDegree : target +
        (U.card + A.core.card + target) ≤ G.degree t)
    (hRadius : armRadius + pathRadius + 1 ≤ totalRadius)
    (holdRadius : oldRadius ≤ totalRadius) :
    ∃ A' : Adjuster G target totalRadius k,
      A'.core = A.core ∧ Disjoint U A'.verts := by
  let originalDecEq : DecidableEq V := inferInstance
  classical
  let : DecidableEq V := originalDecEq
  let rightForbidden : Finset V :=
    U ∪ A.core ∪ qLeft.support.toFinset ∪ pLeft.support.toFinset
  obtain ⟨right, hright⟩ := exists_expansion_of_two_paths_star_disjoint
    G qRight pRight hqRightLength hpRightLength rightForbidden
      hrightAvoid.1 hrightAvoid.2 htarget (by simpa [rightForbidden] using hyDegree)
      hRadius
  let leftForbidden : Finset V := U ∪ A.core ∪ right.verts
  have hleftForbiddenCard : leftForbidden.card ≤
      U.card + A.core.card + target := by
    have h₁ := Finset.card_union_le U A.core
    have h₂ := Finset.card_union_le (U ∪ A.core) right.verts
    rw [right.card_verts] at h₂
    dsimp [leftForbidden]
    omega
  have hleftAvoid' :
      qLeft.Avoids (leftForbidden : Set V) ∅ ∧
        pLeft.Avoids (leftForbidden : Set V) ∅ := by
    constructor
    · intro z hz hzForbidden
      change z ∈ U ∪ A.core ∪ right.verts at hzForbidden
      simp only [Finset.mem_union] at hzForbidden
      rcases hzForbidden with (hzU | hzCore) | hzRight
      · exact hleftAvoid.1 z hz (by
          change z ∈ U ∪ A.core
          exact Finset.mem_union_left _ hzU)
      · exact hleftAvoid.1 z hz (by
          change z ∈ U ∪ A.core
          exact Finset.mem_union_right _ hzCore)
      · apply (Finset.disjoint_left.1 hright hzRight)
        change z ∈ rightForbidden
        simp [rightForbidden, hz]
    · intro z hz hzForbidden
      change z ∈ U ∪ A.core ∪ right.verts at hzForbidden
      simp only [Finset.mem_union] at hzForbidden
      rcases hzForbidden with (hzU | hzCore) | hzRight
      · exact hleftAvoid.2 z hz (by
          change z ∈ U ∪ A.core
          exact Finset.mem_union_left _ hzU)
      · exact hleftAvoid.2 z hz (by
          change z ∈ U ∪ A.core
          exact Finset.mem_union_right _ hzCore)
      · apply (Finset.disjoint_left.1 hright hzRight)
        change z ∈ rightForbidden
        simp [rightForbidden, hz]
  obtain ⟨left, hleft⟩ := exists_expansion_of_two_paths_star_disjoint
    G qLeft pLeft hqLeftLength hpLeftLength leftForbidden
      hleftAvoid'.1 hleftAvoid'.2 htarget
      (by exact (Nat.add_le_add_left hleftForbiddenCard target).trans htDegree)
      hRadius
  have hcoreLeft : Disjoint A.core left.verts := by
    apply (hleft.mono_right ?_).symm
    intro z hzCore
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hzCore)
  have hcoreRight : Disjoint A.core right.verts := by
    apply (hright.mono_right ?_).symm
    intro z hzCore
    change z ∈ rightForbidden
    simp [rightForbidden, hzCore]
  have hends : Disjoint left.verts right.verts := by
    apply hleft.mono_right
    intro z hzRight
    exact Finset.mem_union_right _ hzRight
  let A' : Adjuster G target totalRadius k :=
    A.replaceEnds left right hcoreLeft hcoreRight hends holdRadius
  refine ⟨A', rfl, ?_⟩
  rw [Finset.disjoint_left]
  intro z hzU hzA'
  change z ∈ left.verts ∪ right.verts ∪ A.core at hzA'
  simp only [Finset.mem_union] at hzA'
  rcases hzA' with (hzLeft | hzRight) | hzCore
  · exact (Finset.disjoint_left.1 hleft hzLeft (by
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hzU))).elim
  · exact (Finset.disjoint_left.1 hright hzRight (by
      change z ∈ rightForbidden
      simp [rightForbidden, hzU])).elim
  · exact (Finset.disjoint_left.1 hAU hzU (A.core_subset_verts hzCore)).elim

/-! ### The two endpoint replacements in Claims 4.5 and 4.6 -/

/-- Replace the right end by a prescribed subexpansion of an avoiding ball,
and replace the left end by a path leading to a fresh high-degree star.

The finite set `leftForbidden` is allowed to contain the whole right ball and
the old core.  Thus the conclusion records exactly the separation needed to
reuse the old adjuster core.  No expansion-supply premise occurs: both new
ends are constructed by the preceding concrete lemmas. -/
theorem Adjuster.exists_replaceRightBall_leftPathStar [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {D₀ oldRadius k target ballRadius pathRadius totalRadius : ℕ}
    (A : Adjuster G D₀ oldRadius k)
    {a t : V} (ha : a ∈ A.leftEnd.verts)
    (p : G.Walk a t) (hp : p.IsPath) (hpLength : p.length ≤ pathRadius)
    (rightForbidden : Set V)
    (hrightCard : target ≤
      (ballAvoidingFrom G rightForbidden A.rightEnd.verts ballRadius).card)
    (leftForbidden : Finset V)
    (hleftOld : Disjoint A.leftEnd.verts leftForbidden)
    (hpAvoid : p.Avoids (leftForbidden : Set V) ∅)
    (hcoreLeftForbidden : A.core ⊆ leftForbidden)
    (hrightBallLeftForbidden :
      ballAvoidingFrom G rightForbidden A.rightEnd.verts ballRadius ⊆
        leftForbidden)
    (hcoreRightBall : Disjoint A.core
      (ballAvoidingFrom G rightForbidden A.rightEnd.verts ballRadius))
    (htarget : 0 < target)
    (htDegree : target + leftForbidden.card ≤ G.degree t)
    (hleftRadius : oldRadius + pathRadius + 1 ≤ totalRadius)
    (hrightRadius : oldRadius + ballRadius ≤ totalRadius) :
    ∃ A' : Adjuster G target totalRadius k,
      Disjoint A'.leftEnd.verts leftForbidden ∧
        A'.rightEnd.verts ⊆
          ballAvoidingFrom G rightForbidden A.rightEnd.verts ballRadius ∧
        A'.core = A.core := by
  let originalDecEq : DecidableEq V := inferInstance
  classical
  let : DecidableEq V := originalDecEq
  obtain ⟨left, hleftForbidden⟩ :=
    A.leftEnd.exists_attach_path_star_disjoint G ha p hp hpLength
      leftForbidden hleftOld hpAvoid htarget htDegree hleftRadius
  let rightFull := A.rightEnd.ofBallAvoidingFrom rightForbidden ballRadius
  obtain ⟨rightSmall, hrightSmall⟩ :=
    rightFull.proposition3_10 htarget (by
      simpa [rightFull] using hrightCard)
  let right : VertexExpansion G A.rightRoot target totalRadius :=
    rightSmall.radiusMono hrightRadius
  have hrightBall : right.verts ⊆
      ballAvoidingFrom G rightForbidden A.rightEnd.verts ballRadius := by
    simpa [right, rightFull] using hrightSmall
  have hcoreLeft : Disjoint A.core left.verts := by
    exact (hleftForbidden.mono_right hcoreLeftForbidden).symm
  have hcoreRight : Disjoint A.core right.verts := by
    exact hcoreRightBall.mono_right hrightBall
  have hends : Disjoint left.verts right.verts := by
    exact hleftForbidden.mono_right
      (hrightBall.trans hrightBallLeftForbidden)
  let A' : Adjuster G target totalRadius k :=
    A.replaceEnds left right hcoreLeft hcoreRight hends (by omega)
  exact ⟨A', hleftForbidden, hrightBall, rfl⟩

/-- Replace the right end by a prescribed subexpansion of an avoiding ball,
and replace the left end by a path attached to a concrete auxiliary
expansion.  This is the deterministic final step of Claim 4.6 after Lemmas
3.7 and 3.12 have supplied the two large sets. -/
theorem Adjuster.exists_replaceRightBall_leftPathExpansion [Fintype V]
    {D₀ oldRadius k target ballRadius pathRadius farRadius totalRadius : ℕ}
    (A : Adjuster G D₀ oldRadius k)
    {a z center : V} (ha : a ∈ A.leftEnd.verts)
    (p : G.Walk a z) (hp : p.IsPath) (hpLength : p.length ≤ pathRadius)
    (Z : VertexExpansion G center target farRadius) (hz : z ∈ Z.verts)
    (rightForbidden : Set V)
    (hrightCard : target ≤
      (ballAvoidingFrom G rightForbidden A.rightEnd.verts ballRadius).card)
    (leftForbidden : Finset V)
    (hleftOld : Disjoint A.leftEnd.verts leftForbidden)
    (hpAvoid : p.Avoids (leftForbidden : Set V) ∅)
    (hZ : Disjoint Z.verts leftForbidden)
    (hcoreLeftForbidden : A.core ⊆ leftForbidden)
    (hrightBallLeftForbidden :
      ballAvoidingFrom G rightForbidden A.rightEnd.verts ballRadius ⊆
        leftForbidden)
    (hcoreRightBall : Disjoint A.core
      (ballAvoidingFrom G rightForbidden A.rightEnd.verts ballRadius))
    (htarget : 0 < target)
    (hleftRadius : oldRadius + pathRadius + 2 * farRadius ≤ totalRadius)
    (hrightRadius : oldRadius + ballRadius ≤ totalRadius) :
    ∃ A' : Adjuster G target totalRadius k,
      Disjoint A'.leftEnd.verts leftForbidden ∧
        A'.rightEnd.verts ⊆
          ballAvoidingFrom G rightForbidden A.rightEnd.verts ballRadius ∧
        A'.core = A.core := by
  let originalDecEq : DecidableEq V := inferInstance
  classical
  let : DecidableEq V := originalDecEq
  obtain ⟨left, hleftForbidden⟩ :=
    A.leftEnd.exists_attach_path_expansion_disjoint ha p hp hpLength Z hz
      leftForbidden hleftOld hpAvoid hZ hleftRadius
  let rightFull := A.rightEnd.ofBallAvoidingFrom rightForbidden ballRadius
  obtain ⟨rightSmall, hrightSmall⟩ :=
    rightFull.proposition3_10 htarget (by
      simpa [rightFull] using hrightCard)
  let right : VertexExpansion G A.rightRoot target totalRadius :=
    rightSmall.radiusMono hrightRadius
  have hrightBall : right.verts ⊆
      ballAvoidingFrom G rightForbidden A.rightEnd.verts ballRadius := by
    simpa [right, rightFull] using hrightSmall
  have hcoreLeft : Disjoint A.core left.verts := by
    exact (hleftForbidden.mono_right hcoreLeftForbidden).symm
  have hcoreRight : Disjoint A.core right.verts := by
    exact hcoreRightBall.mono_right hrightBall
  have hends : Disjoint left.verts right.verts := by
    exact hleftForbidden.mono_right
      (hrightBall.trans hrightBallLeftForbidden)
  let A' : Adjuster G target totalRadius k :=
    A.replaceEnds left right hcoreLeft hcoreRight hends (by omega)
  exact ⟨A', hleftForbidden, hrightBall, rfl⟩

/-! ### Returning an adjuster from an extracted induced subgraph -/

/-- Map an adjuster in an induced subgraph back to the ambient vertex type
and then enlarge the edge relation along a specified graph inclusion.  This
is the transport used in Claim 4.4 after Corollary 2.5 extracts an induced
expander inside a bipartite subgraph of the original graph. -/
noncomputable def Adjuster.ofInduceOfLE
    {H : SimpleGraph V} {S : Set V} {D radius k : ℕ}
    (A : Adjuster (H.induce S) D radius k) (hHG : H ≤ G) :
    Adjuster G D radius k :=
  (A.mapEmbedding (SimpleGraph.Embedding.induce S)).monoGraph hHG

@[simp] theorem Adjuster.ofInduceOfLE_leftRoot
    {H : SimpleGraph V} {S : Set V} {D radius k : ℕ}
    (A : Adjuster (H.induce S) D radius k) (hHG : H ≤ G) :
    (A.ofInduceOfLE hHG).leftRoot = A.leftRoot.1 := rfl

@[simp] theorem Adjuster.ofInduceOfLE_rightRoot
    {H : SimpleGraph V} {S : Set V} {D radius k : ℕ}
    (A : Adjuster (H.induce S) D radius k) (hHG : H ≤ G) :
    (A.ofInduceOfLE hHG).rightRoot = A.rightRoot.1 := rfl

@[simp] theorem Adjuster.ofInduceOfLE_core
    {H : SimpleGraph V} {S : Set V} {D radius k : ℕ}
    (A : Adjuster (H.induce S) D radius k) (hHG : H ≤ G) :
    (A.ofInduceOfLE hHG).core =
      A.core.map (Function.Embedding.subtype S) := rfl

@[simp] theorem Adjuster.ofInduceOfLE_verts
    {H : SimpleGraph V} {S : Set V} {D radius k : ℕ}
    (A : Adjuster (H.induce S) D radius k) (hHG : H ≤ G) :
    (A.ofInduceOfLE hHG).verts =
      A.verts.map (Function.Embedding.subtype S) := by
  classical
  rw [Adjuster.ofInduceOfLE, Adjuster.monoGraph_verts,
    Adjuster.mapEmbedding_verts]
  apply Finset.ext
  intro v
  simp only [Finset.mem_map]
  constructor <;> rintro ⟨a, ha, rfl⟩ <;> exact ⟨a, ha, rfl⟩

/-- Two-level version of `ofInduceOfLE`: an adjuster is first returned from
an extracted induced expander to an ambient induced graph, and then embedded
back into the original graph.  This is the exact transport shape produced by
Corollary 2.5 in Claim 4.4. -/
noncomputable def Adjuster.ofNestedInduceOfLE
    {S : Set V} {H : SimpleGraph S} {T : Set S} {D radius k : ℕ}
    (A : Adjuster (H.induce T) D radius k) (hHG : H ≤ G.induce S) :
    Adjuster G D radius k :=
  ((A.mapEmbedding (SimpleGraph.Embedding.induce T)).monoGraph hHG).mapEmbedding
    (SimpleGraph.Embedding.induce S)

@[simp] theorem Adjuster.ofNestedInduceOfLE_leftRoot
    {S : Set V} {H : SimpleGraph S} {T : Set S} {D radius k : ℕ}
    (A : Adjuster (H.induce T) D radius k) (hHG : H ≤ G.induce S) :
    (A.ofNestedInduceOfLE hHG).leftRoot = A.leftRoot.1.1 := by
  simp [Adjuster.ofNestedInduceOfLE]

@[simp] theorem Adjuster.ofNestedInduceOfLE_rightRoot
    {S : Set V} {H : SimpleGraph S} {T : Set S} {D radius k : ℕ}
    (A : Adjuster (H.induce T) D radius k) (hHG : H ≤ G.induce S) :
    (A.ofNestedInduceOfLE hHG).rightRoot = A.rightRoot.1.1 := by
  simp [Adjuster.ofNestedInduceOfLE]

/-- Every transported vertex remains in the outer induced carrier. -/
theorem Adjuster.ofNestedInduceOfLE_verts_mem
    {S : Set V} {H : SimpleGraph S} {T : Set S} {D radius k : ℕ}
    (A : Adjuster (H.induce T) D radius k) (hHG : H ≤ G.induce S)
    {v : V} (hv : v ∈ (A.ofNestedInduceOfLE hHG).verts) : v ∈ S := by
  classical
  rw [Adjuster.ofNestedInduceOfLE, Adjuster.mapEmbedding_verts] at hv
  obtain ⟨w, hw, rfl⟩ := Finset.mem_map.1 hv
  exact w.2

/-! ## The subdivision-free high-contact bound -/

/-- Vertices outside `W` which have at least `d` neighbors in `W`.

This is the set called `U₀` in the proof of Lemma 4.3 (with `d` replaced
there by `d / 2`). -/
noncomputable def manyNeighborsInto [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (W : Finset V) (d : ℕ) : Finset V := by
  exact ((Finset.univ : Finset V) \ W).filter fun v ↦
    d ≤ (W.filter fun w ↦ G.Adj v w).card

@[simp] theorem mem_manyNeighborsInto [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (W : Finset V) (d : ℕ) (v : V) :
    v ∈ manyNeighborsInto G W d ↔
      v ∉ W ∧ d ≤ (W.filter fun w ↦ G.Adj v w).card := by
  simp only [manyNeighborsInto, Finset.mem_filter, Finset.mem_sdiff,
    Finset.mem_univ, true_and]

/-- Proposition 3.16 in the exact form needed for the exceptional set in
Lemma 4.3.  If more than `|W|²` vertices outside `W` each sent `d` edges
into `W`, the skewed-subdivision lemma would construct a subdivision of
`K_d`. -/
theorem card_manyNeighborsInto_le_sq_of_no_oneSubdivisionClique [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) (d : ℕ)
    (hfree : ¬ oneSubdivisionClique d ⊑ G) :
    (manyNeighborsInto G W d).card ≤ W.card ^ 2 := by
  classical
  by_contra hcard
  have hlarge : W.card ^ 2 ≤ (manyNeighborsInto G W d).card := by omega
  have hnonempty : (manyNeighborsInto G W d).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty] at hcard
    simp at hcard
  have hdisjoint : Disjoint (manyNeighborsInto G W d) W := by
    rw [Finset.disjoint_left]
    intro v hv hvW
    exact ((mem_manyNeighborsInto G W d v).1 hv).1 hvW
  obtain ⟨v, hv, hvfew⟩ :=
    exists_few_neighbors_of_no_oneSubdivisionClique
      G (manyNeighborsInto G W d) W d hdisjoint hnonempty hlarge hfree
  exact (Nat.not_lt_of_ge ((mem_manyNeighborsInto G W d v).1 hv).2) hvfew

/-- The numerical `100 D²` form used after `|W| ≤ 10D`. -/
theorem card_manyNeighborsInto_le_hundred_mul_sq [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) (d D : ℕ)
    (hfree : ¬ oneSubdivisionClique d ⊑ G) (hW : W.card ≤ 10 * D) :
    (manyNeighborsInto G W d).card ≤ 100 * D ^ 2 := by
  calc
    (manyNeighborsInto G W d).card ≤ W.card ^ 2 :=
      card_manyNeighborsInto_le_sq_of_no_oneSubdivisionClique G W d hfree
    _ ≤ (10 * D) ^ 2 := Nat.pow_le_pow_left hW 2
    _ = 100 * D ^ 2 := by ring

/-! ## The initial density left after deleting `U` -/

/-- A degree lower bound outside a small exceptional set gives an average
degree lower bound.  The cardinal inequality is deliberately separated from
the graph argument; in Lemma 4.3 it is one of the eventual elementary
estimates. -/
theorem avgDegreeAtLeast_of_degree_outside [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (exceptional : Finset V) (minimum average : ℕ)
    (hdegree : ∀ v ∉ exceptional, minimum ≤ G.degree v)
    (hcount : average * Fintype.card V ≤
      (Fintype.card V - exceptional.card) * minimum) :
    AvgDegreeAtLeast G average := by
  rw [AvgDegreeAtLeast]
  calc
    average * Fintype.card V
        ≤ (Fintype.card V - exceptional.card) * minimum := hcount
    _ = ((Finset.univ : Finset V) \ exceptional).card * minimum := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ exceptional),
        Finset.card_univ]
    _ = ∑ v ∈ (Finset.univ : Finset V) \ exceptional, minimum := by simp
    _ ≤ ∑ v ∈ (Finset.univ : Finset V) \ exceptional, G.degree v := by
      apply Finset.sum_le_sum
      intro v hv
      exact hdegree v (Finset.mem_sdiff.1 hv).2
    _ ≤ ∑ v ∈ (Finset.univ : Finset V), G.degree v :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        (fun _ _ _ ↦ Nat.zero_le _)
    _ = ∑ v : V, G.degree v := by simp

/-- If at most `lost` neighbors of `v` lie in a deleted set, then the graph
induced by its complement retains degree at least `d - lost` at `v`. -/
theorem induce_compl_degree_lower [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (deleted : Finset V) (d lost : ℕ) (v : V) (hv : v ∉ deleted)
    (hdegree : d ≤ G.degree v)
    (hlost : (deleted.filter fun w ↦ G.Adj v w).card ≤ lost) :
    d - lost ≤
      (G.induce ((↑((Finset.univ : Finset V) \ deleted)) : Set V)).degree
        ⟨v, by simp [hv]⟩ := by
  let originalDecEq : DecidableEq V := inferInstance
  classical
  let : DecidableEq V := originalDecEq
  let S : Finset V := (Finset.univ : Finset V) \ deleted
  let kept : Finset V := S.filter fun w ↦ G.Adj v w
  let removed : Finset V := deleted.filter fun w ↦ G.Adj v w
  have hdisjoint : Disjoint kept removed := by
    rw [Finset.disjoint_left]
    intro w hwKept hwRemoved
    have hwS : w ∈ S := (Finset.mem_filter.1 hwKept).1
    have hwDeleted : w ∈ deleted := (Finset.mem_filter.1 hwRemoved).1
    exact (Finset.mem_sdiff.1 hwS).2 hwDeleted
  have hunion : kept ∪ removed = G.neighborFinset v := by
    ext w
    simp only [kept, removed, S, Finset.mem_union, Finset.mem_filter,
      Finset.mem_sdiff, Finset.mem_univ, true_and, G.mem_neighborFinset]
    tauto
  have hcards : kept.card + removed.card = G.degree v := by
    rw [← Finset.card_union_of_disjoint hdisjoint, hunion,
      G.card_neighborFinset_eq_degree]
  have hkept : d - lost ≤ kept.card := by
    calc
      d - lost ≤ G.degree v - lost := Nat.sub_le_sub_right hdegree lost
      _ ≤ G.degree v - removed.card := Nat.sub_le_sub_left hlost _
      _ = kept.card := by omega
  calc
    d - lost ≤ kept.card := hkept
    _ = (G.induce ((↑S : Set V))).degree ⟨v, by simp [S, hv]⟩ := by
      rw [← card_neighborFinset_eq_degree]
      let e : (↑S : Set V) ↪ V := Function.Embedding.subtype _
      have heq :
          ((G.induce (↑S : Set V)).neighborFinset
              ⟨v, by simp [S, hv]⟩).map e = kept := by
        ext w
        simp [e, kept, and_comm]
      rw [← heq, Finset.card_map]

/-- The source edge-count argument before Claim 4.4, stated directly as an
average-degree estimate in `G - U`.  All vertices except
`manyNeighborsInto G U contact` retain degree at least `d-contact`; the
explicit counting premise pays for the exceptional vertices. -/
theorem avgDegreeAtLeast_induce_compl_of_manyNeighborsInto [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (d contact average : ℕ)
    (hmin : ∀ v : V, d ≤ G.degree v)
    (hcount : average * (Fintype.card V - U.card) ≤
      ((Fintype.card V - U.card) -
          (manyNeighborsInto G U contact).card) * (d - contact)) :
    AvgDegreeAtLeast
      (G.induce ((↑((Finset.univ : Finset V) \ U)) : Set V)) average := by
  classical
  let S : Finset V := (Finset.univ : Finset V) \ U
  let H : SimpleGraph (↑S : Set V) := G.induce (↑S : Set V)
  let exceptional : Finset (↑S : Set V) :=
    (Finset.univ : Finset (↑S : Set V)).filter fun v ↦
      v.1 ∈ manyNeighborsInto G U contact
  have hexceptionalCard : exceptional.card ≤
      (manyNeighborsInto G U contact).card := by
    let e : (↑S : Set V) ↪ V := Function.Embedding.subtype _
    have hmap : exceptional.map e ⊆ manyNeighborsInto G U contact := by
      intro v hv
      rw [Finset.mem_map] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      exact (Finset.mem_filter.1 hw).2
    simpa [e] using Finset.card_le_card hmap
  have hcardS : Fintype.card (↑S : Set V) = Fintype.card V - U.card := by
    change Fintype.card (↑S) = Fintype.card V - U.card
    dsimp [S]
    rw [Fintype.card_coe,
      Finset.card_sdiff_of_subset (Finset.subset_univ U), Finset.card_univ]
  have hcountH : average * Fintype.card (↑S : Set V) ≤
      (Fintype.card (↑S : Set V) - exceptional.card) * (d - contact) := by
    rw [hcardS]
    exact hcount.trans (Nat.mul_le_mul_right (d - contact)
      (Nat.sub_le_sub_left hexceptionalCard (Fintype.card V - U.card)))
  apply avgDegreeAtLeast_of_degree_outside H exceptional (d - contact) average
  · intro v hvExceptional
    have hvU : v.1 ∉ U := by
      simpa [S] using v.2
    have hvNotMany : v.1 ∉ manyNeighborsInto G U contact := by
      intro hvMany
      apply hvExceptional
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hvMany⟩
    have hlost : (U.filter fun w ↦ G.Adj v.1 w).card ≤ contact := by
      have hnotLower : ¬ contact ≤
          (U.filter fun w ↦ G.Adj v.1 w).card := by
        intro hlower
        exact hvNotMany ((mem_manyNeighborsInto G U contact v.1).2 ⟨hvU, hlower⟩)
      omega
    simpa [H, S] using induce_compl_degree_lower G U d contact v.1 hvU
      (hmin v.1) hlost
  · exact hcountH

/-- Deleting a finite vertex set removes at most the sum of the ambient
degrees of its vertices.  We state the result using `ksInducedEdges`, whose
ambient edge count avoids any subtype-transport bookkeeping. -/
theorem card_edgeFinset_le_induced_compl_add_sum_degrees [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) :
    G.edgeFinset.card ≤
      ksInducedEdges G ((Finset.univ : Finset V) \ W) +
        ∑ v ∈ W, G.degree v := by
  classical
  let S : Finset V := (Finset.univ : Finset V) \ W
  let kept := G.edgeFinset.filter fun e ↦ e.toFinset ⊆ S
  let removed := G.edgeFinset.filter fun e ↦ ¬ e.toFinset ⊆ S
  have hremoved : removed ⊆ W.biUnion fun v ↦ G.incidenceFinset v := by
    intro e he
    obtain ⟨heEdge, heNot⟩ := Finset.mem_filter.1 he
    obtain ⟨v, hvEdge, hvS⟩ := Finset.not_subset.mp heNot
    have hvW : v ∈ W := by
      simpa [S] using hvS
    rw [Finset.mem_biUnion]
    refine ⟨v, hvW, ?_⟩
    rw [G.mem_incidenceFinset]
    exact ⟨SimpleGraph.mem_edgeFinset.mp heEdge, by simpa using hvEdge⟩
  have hremovedCard : removed.card ≤ ∑ v ∈ W, G.degree v := by
    calc
      removed.card ≤ (W.biUnion fun v ↦ G.incidenceFinset v).card :=
        Finset.card_le_card hremoved
      _ ≤ ∑ v ∈ W, (G.incidenceFinset v).card :=
        Finset.card_biUnion_le
      _ = ∑ v ∈ W, G.degree v := by
        apply Finset.sum_congr rfl
        intro v hv
        exact G.card_incidenceFinset_eq_degree v
  have hpartition : kept.card + removed.card = G.edgeFinset.card := by
    simpa [kept, removed] using
      (Finset.card_filter_add_card_filter_not
        (s := G.edgeFinset) (p := fun e ↦ e.toFinset ⊆ S))
  have hkept : kept.card = ksInducedEdges G S := by
    unfold ksInducedEdges
    congr 1
  dsimp [S] at hkept
  omega

/-- Nested deletion form of the preceding incidence bound.  Starting from the
edges left after deleting `U`, deleting the additional vertices in `W` loses
at most the sum of the ambient degrees over `W \ U`. -/
theorem ksInducedEdges_compl_le_compl_union_add_sum_degrees [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V) :
    ksInducedEdges G ((Finset.univ : Finset V) \ U) ≤
      ksInducedEdges G ((Finset.univ : Finset V) \ (U ∪ W)) +
        ∑ v ∈ W \ U, G.degree v := by
  let originalDecAdj : DecidableRel G.Adj := inferInstance
  classical
  let : DecidableRel G.Adj := originalDecAdj
  let S₀ : Finset V := (Finset.univ : Finset V) \ U
  let S₁ : Finset V := (Finset.univ : Finset V) \ (U ∪ W)
  let E₀ := G.edgeFinset.filter fun e ↦ e.toFinset ⊆ S₀
  let E₁ := G.edgeFinset.filter fun e ↦ e.toFinset ⊆ S₁
  let removed := E₀.filter fun e ↦ ¬ e.toFinset ⊆ S₁
  have hS₁S₀ : S₁ ⊆ S₀ := by
    intro v hv
    simp only [S₁, S₀, Finset.mem_sdiff, Finset.mem_univ, true_and] at hv ⊢
    exact fun hvU ↦ hv (Finset.mem_union_left W hvU)
  have hfiltered : E₀.filter (fun e ↦ e.toFinset ⊆ S₁) = E₁ := by
    ext e
    simp only [E₀, E₁, Finset.mem_filter]
    constructor
    · rintro ⟨⟨he, heS₀⟩, heS₁⟩
      exact ⟨he, heS₁⟩
    · rintro ⟨he, heS₁⟩
      exact ⟨⟨he, heS₁.trans hS₁S₀⟩, heS₁⟩
  have hremoved : removed ⊆ (W \ U).biUnion fun v ↦ G.incidenceFinset v := by
    intro e he
    obtain ⟨heE₀, heNot⟩ := Finset.mem_filter.1 he
    obtain ⟨heEdge, heS₀⟩ := Finset.mem_filter.1 heE₀
    obtain ⟨v, hvEdge, hvS₁⟩ := Finset.not_subset.mp heNot
    have hvS₀ := heS₀ hvEdge
    have hvNotU : v ∉ U := by simpa [S₀] using hvS₀
    have hvUW : v ∈ U ∪ W := by
      by_cases hvU : v ∈ U
      · exact Finset.mem_union_left W hvU
      · exact Finset.mem_union_right U (by
          simpa [S₁, hvU] using hvS₁)
    have hvW : v ∈ W := (Finset.mem_union.1 hvUW).resolve_left hvNotU
    rw [Finset.mem_biUnion]
    refine ⟨v, Finset.mem_sdiff.2 ⟨hvW, hvNotU⟩, ?_⟩
    rw [G.mem_incidenceFinset]
    exact ⟨SimpleGraph.mem_edgeFinset.mp heEdge, by simpa using hvEdge⟩
  have hremovedCard : removed.card ≤ ∑ v ∈ W \ U, G.degree v := by
    calc
      removed.card ≤ ((W \ U).biUnion fun v ↦ G.incidenceFinset v).card :=
        Finset.card_le_card hremoved
      _ ≤ ∑ v ∈ W \ U, (G.incidenceFinset v).card :=
        Finset.card_biUnion_le
      _ = ∑ v ∈ W \ U, G.degree v := by
        apply Finset.sum_congr rfl
        intro v hv
        exact G.card_incidenceFinset_eq_degree v
  have hpartition : E₁.card + removed.card = E₀.card := by
    rw [← hfiltered]
    simpa [removed] using
      (Finset.card_filter_add_card_filter_not
        (s := E₀) (p := fun e ↦ e.toFinset ⊆ S₁))
  have hE₀ : E₀.card = ksInducedEdges G S₀ := by
    unfold ksInducedEdges
    congr 1
  have hE₁ : E₁.card = ksInducedEdges G S₁ := by
    unfold ksInducedEdges
    congr 1
  dsimp [S₀, S₁] at hE₀ hE₁
  omega

/-- Average-degree consequence of nested deletion.  This is the exact edge
bookkeeping used in Claim 4.4: first delete `U`, then a bounded-degree ball
`W`, while charging only `W \ U` in the second step. -/
theorem avgDegreeAtLeast_induce_compl_union_of_deleted_degree_bound [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W : Finset V) (initial target Delta : ℕ)
    (haverage : AvgDegreeAtLeast
      (G.induce ((↑((Finset.univ : Finset V) \ U)) : Set V)) initial)
    (hdegree : ∀ v ∈ W \ U, G.degree v ≤ Delta)
    (hnumeric : target * (Fintype.card V - (U ∪ W).card) +
        2 * ((W \ U).card * Delta) ≤
          initial * (Fintype.card V - U.card)) :
    AvgDegreeAtLeast
      (G.induce ((↑((Finset.univ : Finset V) \ (U ∪ W))) : Set V)) target := by
  classical
  have hdegreeSum : ∑ v ∈ W \ U, G.degree v ≤ (W \ U).card * Delta := by
    calc
      ∑ v ∈ W \ U, G.degree v ≤ ∑ _v ∈ W \ U, Delta := by
        apply Finset.sum_le_sum
        intro v hv
        exact hdegree v hv
      _ = (W \ U).card * Delta := by simp
  have hedge := ksInducedEdges_compl_le_compl_union_add_sum_degrees G U W
  have hedge' : ksInducedEdges G ((Finset.univ : Finset V) \ U) ≤
      ksInducedEdges G ((Finset.univ : Finset V) \ (U ∪ W)) +
        (W \ U).card * Delta :=
    hedge.trans (Nat.add_le_add_left hdegreeSum _)
  have hcardU : Fintype.card
      (↑((Finset.univ : Finset V) \ U) : Set V) =
        Fintype.card V - U.card := by
    change Fintype.card (↑((Finset.univ : Finset V) \ U)) =
      Fintype.card V - U.card
    rw [Fintype.card_coe,
      Finset.card_sdiff_of_subset (Finset.subset_univ U), Finset.card_univ]
  have hcardUW : Fintype.card
      (↑((Finset.univ : Finset V) \ (U ∪ W)) : Set V) =
        Fintype.card V - (U ∪ W).card := by
    change Fintype.card (↑((Finset.univ : Finset V) \ (U ∪ W))) =
      Fintype.card V - (U ∪ W).card
    rw [Fintype.card_coe,
      Finset.card_sdiff_of_subset (Finset.subset_univ (U ∪ W)),
      Finset.card_univ]
  rw [AvgDegreeAtLeast,
    (G.induce ((↑((Finset.univ : Finset V) \ U)) : Set V)).sum_degrees_eq_twice_card_edges,
    ← ksInducedEdges_eq_card_edgeFinset_induce,
    hcardU] at haverage
  rw [AvgDegreeAtLeast,
    (G.induce ((↑((Finset.univ : Finset V) \ (U ∪ W))) : Set V)).sum_degrees_eq_twice_card_edges,
    ← ksInducedEdges_eq_card_edgeFinset_induce,
    hcardUW]
  omega

/-- If every deleted vertex has degree at most `Delta`, the preceding edge
bound and one explicit arithmetic inequality preserve a requested average
degree in the induced complement. -/
theorem avgDegreeAtLeast_induce_compl_of_deleted_degree_bound [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (initial target Delta : ℕ)
    (haverage : AvgDegreeAtLeast G initial)
    (hdegree : ∀ v ∈ W, G.degree v ≤ Delta)
    (hnumeric : target * (Fintype.card V - W.card) +
        2 * (W.card * Delta) ≤ initial * Fintype.card V) :
    AvgDegreeAtLeast
      (G.induce ((↑((Finset.univ : Finset V) \ W)) : Set V)) target := by
  classical
  have hdegreeSum : ∑ v ∈ W, G.degree v ≤ W.card * Delta := by
    calc
      ∑ v ∈ W, G.degree v ≤ ∑ _v ∈ W, Delta := by
        apply Finset.sum_le_sum
        intro v hv
        exact hdegree v hv
      _ = W.card * Delta := by simp
  have hedge := card_edgeFinset_le_induced_compl_add_sum_degrees G W
  have hedge' : G.edgeFinset.card ≤
      ksInducedEdges G ((Finset.univ : Finset V) \ W) + W.card * Delta :=
    hedge.trans (Nat.add_le_add_left hdegreeSum _)
  have hcardW : Fintype.card
      (↑((Finset.univ : Finset V) \ W) : Set V) =
        Fintype.card V - W.card := by
    change Fintype.card (↑((Finset.univ : Finset V) \ W)) =
      Fintype.card V - W.card
    rw [Fintype.card_coe,
      Finset.card_sdiff_of_subset (Finset.subset_univ W), Finset.card_univ]
  rw [AvgDegreeAtLeast, G.sum_degrees_eq_twice_card_edges] at haverage
  rw [AvgDegreeAtLeast]
  rw [hcardW,
    (G.induce ((↑((Finset.univ : Finset V) \ W)) : Set V)).sum_degrees_eq_twice_card_edges,
    ← ksInducedEdges_eq_card_edgeFinset_induce]
  omega

/-- Apply the concrete bipartite Komlós--Szemerédi extraction theorem inside
the complement of a deleted set.  Properness of the deletion supplies the
`Nonempty` instance on the subtype, so this wrapper has exactly the carrier
shape used in Claim 4.4. -/
theorem exists_bipartite_lmExpander_in_induced_compl [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V)
    (d : ℕ) (hd : 0 < d) (kappa : ℝ) (hkappa : 0 < kappa)
    (hproper : W.card < Fintype.card V)
    (havg : AvgDegreeAtLeast
      (G.induce ((↑((Finset.univ : Finset V) \ W)) : Set V)) (8 * d)) :
    ∃ (H : SimpleGraph
        ((↑((Finset.univ : Finset V) \ W)) : Set V))
      (hHAdj : DecidableRel H.Adj),
      letI : DecidableRel H.Adj := hHAdj
      ∃ (S : Finset ((↑((Finset.univ : Finset V) \ W)) : Set V)),
      H ≤ G.induce ((↑((Finset.univ : Finset V) \ W)) : Set V) ∧
      H.IsBipartite ∧ S.Nonempty ∧
      IsLMExpander (H.induce (↑S : Set _)) (1 / 1024) kappa ∧
      (2 * d : ℝ) ≤ ksInducedAverageDegree H S ∧
      ∀ v,
        (d : ℝ) ≤ (H.induce (↑S : Set _)).degree v := by
  let originalDecAdj : DecidableRel G.Adj := inferInstance
  classical
  let : DecidableRel G.Adj := originalDecAdj
  let T : Finset V := (Finset.univ : Finset V) \ W
  have hTcard : 0 < T.card := by
    dsimp [T]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ W), Finset.card_univ]
    omega
  obtain ⟨v, hvT⟩ := Finset.card_pos.1 hTcard
  let : Nonempty (↑T : Set V) := ⟨⟨v, hvT⟩⟩
  obtain ⟨H, S, hHG, hBip, hS, hExp, hAvg, hMin⟩ :=
    exists_bipartite_liu_montgomery_expander
      (G.induce (↑T : Set V)) hd hkappa (by simpa [T] using havg)
  let hHAdj : DecidableRel H.Adj := Classical.decRel _
  refine ⟨H, hHAdj, S, ?_, hBip, hS, ?_, ?_, ?_⟩
  · simpa [T] using hHG
  · simpa [T, hHAdj] using hExp
  · simpa [T, hHAdj] using hAvg
  · intro w
    simpa [T, hHAdj] using hMin w

/-! ## The high-degree deletion and its bounded balls -/

/-- Vertices whose ambient degree is at least `Delta`. -/
noncomputable def highDegreeVertices [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (Delta : ℕ) : Finset V := by
  exact (Finset.univ : Finset V).filter fun v ↦ Delta ≤ G.degree v

@[simp] theorem mem_highDegreeVertices [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (Delta : ℕ) (v : V) :
    v ∈ highDegreeVertices G Delta ↔ Delta ≤ G.degree v := by
  simp [highDegreeVertices]

theorem degree_le_of_not_mem_highDegreeVertices [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Delta : ℕ) {v : V}
    (hv : v ∉ highDegreeVertices G Delta) : G.degree v ≤ Delta := by
  rw [mem_highDegreeVertices] at hv
  omega

/-- The standard Moore bound specialized to deletion of all vertices of
degree at least `Delta`. -/
theorem card_ballAvoidingFrom_highDegreeVertices_le [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (Delta radius : ℕ)
    (hA : Disjoint A (highDegreeVertices G Delta)) :
    (ballAvoidingFrom G (highDegreeVertices G Delta : Set V) A radius).card ≤
      A.card * (Delta + 1) ^ radius := by
  exact card_ballAvoidingFrom_le_of_degree_bound G A
    (highDegreeVertices G Delta) Delta radius hA
      (fun v hv ↦ degree_le_of_not_mem_highDegreeVertices G Delta hv)

/-- Every vertex reached while avoiding the high-degree set has ambient
degree at most the threshold.  This is the edge-loss input when Claim 4.4
deletes the bounded ball `W'`. -/
theorem degree_le_on_ballAvoidingFrom_highDegreeVertices [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (Delta radius : ℕ)
    (hA : Disjoint A (highDegreeVertices G Delta)) :
    ∀ v ∈ ballAvoidingFrom G (highDegreeVertices G Delta : Set V) A radius,
      G.degree v ≤ Delta := by
  intro v hv
  apply degree_le_of_not_mem_highDegreeVertices G Delta
  intro hvHigh
  exact ballAvoidingFrom_avoids_forbidden G
    (highDegreeVertices G Delta : Set V) A radius
    (fun a ha haHigh ↦
      (Finset.disjoint_left.1 hA ha (by simpa using haHigh)).elim)
    v hv (by simpa using hvHigh)

/-- Global average-degree form of `induce_compl_degree_lower`. -/
theorem avgDegreeAtLeast_induce_compl_of_neighbor_loss [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (deleted : Finset V) (d lost : ℕ)
    (hdegree : ∀ v ∉ deleted, d ≤ G.degree v)
    (hlost : ∀ v ∉ deleted,
      (deleted.filter fun w ↦ G.Adj v w).card ≤ lost) :
    AvgDegreeAtLeast
      (G.induce ((↑((Finset.univ : Finset V) \ deleted)) : Set V))
      (d - lost) := by
  apply avgDegreeAtLeast_of_forall_degree
  intro v
  exact induce_compl_degree_lower G deleted d lost v.1
    (by simpa using v.2) (hdegree v.1 (by simpa using v.2))
    (hlost v.1 (by simpa using v.2))

/-- The density engine in Claim 4.4.

First delete `U`.  Proposition 3.16 bounds the vertices that send at least
`d / 2` edges into `U` by `100 D²`, so the first displayed numerical
inequality leaves average degree `initial`.  Next delete an avoiding ball
grown from `A` while avoiding every vertex of ambient degree at least
`Delta`.  Every vertex in that ball has degree at most `Delta`, and the
second displayed inequality pays for the resulting edge loss.

The hypotheses following the graph assumptions are literal natural-number
inequalities.  In the eventual Lemma 4.3 wrapper they are discharged by the
polylogarithmic scale estimates; no expander or adjuster availability is
assumed here. -/
theorem avgDegreeAtLeast_after_exceptional_and_lowDegreeBall
    [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U A : Finset V) (d D Delta radius initial target : ℕ)
    (hmin : ∀ v : V, d ≤ G.degree v)
    (hfree : ¬ oneSubdivisionClique (d / 2) ⊑ G)
    (hUcard : U.card ≤ 10 * D)
    (hAhigh : Disjoint A (highDegreeVertices G Delta))
    (hinitial : initial * (Fintype.card V - U.card) ≤
      ((Fintype.card V - U.card) - 100 * D ^ 2) * (d - d / 2))
    (hdelete : target *
          (Fintype.card V -
            (U ∪ ballAvoidingFrom G (highDegreeVertices G Delta : Set V)
              A radius).card) +
        2 * (((ballAvoidingFrom G
          (highDegreeVertices G Delta : Set V) A radius) \ U).card * Delta) ≤
          initial * (Fintype.card V - U.card)) :
    AvgDegreeAtLeast
      (G.induce
        ((↑((Finset.univ : Finset V) \ (U ∪
          ballAvoidingFrom G (highDegreeVertices G Delta : Set V) A radius))) :
            Set V))
      target := by
  let ball : Finset V :=
    ballAvoidingFrom G (highDegreeVertices G Delta : Set V) A radius
  have hexceptional : (manyNeighborsInto G U (d / 2)).card ≤ 100 * D ^ 2 :=
    card_manyNeighborsInto_le_hundred_mul_sq G U (d / 2) D hfree hUcard
  have hremaining :
      (Fintype.card V - U.card) - 100 * D ^ 2 ≤
        (Fintype.card V - U.card) -
          (manyNeighborsInto G U (d / 2)).card :=
    Nat.sub_le_sub_left hexceptional _
  have hinitialActual : initial * (Fintype.card V - U.card) ≤
      ((Fintype.card V - U.card) -
          (manyNeighborsInto G U (d / 2)).card) * (d - d / 2) :=
    hinitial.trans (Nat.mul_le_mul_right (d - d / 2) hremaining)
  have havgU : AvgDegreeAtLeast
      (G.induce ((↑((Finset.univ : Finset V) \ U)) : Set V)) initial :=
    avgDegreeAtLeast_induce_compl_of_manyNeighborsInto
      G U d (d / 2) initial hmin hinitialActual
  have hballDegree : ∀ v ∈ ball \ U, G.degree v ≤ Delta := by
    intro v hv
    exact degree_le_on_ballAvoidingFrom_highDegreeVertices G A Delta radius
      hAhigh v (Finset.mem_sdiff.1 hv).1
  apply avgDegreeAtLeast_induce_compl_union_of_deleted_degree_bound
    G U ball initial target Delta havgU hballDegree
  simpa [ball] using hdelete

/-! ## Splicing the two cycle arcs -/

/-- The vertices used by two root-to-cycle connectors and by the cycle,
apart from the two adjuster roots. -/
noncomputable def cycleSpliceCore {x y c z : V}
    (P : G.Walk x c) (Q : G.Walk y z) (C : G.Walk c c) : Finset V := by
  classical
  exact (P.support.toFinset ∪ C.support.toFinset ∪ Q.support.toFinset) \ {x, y}

/-- A universal size bound for the splice core. -/
theorem cycleSpliceCore_card_le {x y c z : V}
    (P : G.Walk x c) (Q : G.Walk y z) (C : G.Walk c c) :
    (cycleSpliceCore P Q C).card ≤ P.length + C.length + Q.length + 3 := by
  classical
  have hsdiff : (cycleSpliceCore P Q C).card ≤
      (P.support.toFinset ∪ C.support.toFinset ∪ Q.support.toFinset).card := by
    exact Finset.card_le_card Finset.sdiff_subset
  have hunion₁ := Finset.card_union_le P.support.toFinset C.support.toFinset
  have hunion₂ := Finset.card_union_le
    (P.support.toFinset ∪ C.support.toFinset) Q.support.toFinset
  have hPcard : P.support.toFinset.card ≤ P.length + 1 := by
    simpa [P.length_support] using List.toFinset_card_le P.support
  have hCcard : C.support.toFinset.card ≤ C.length + 1 := by
    simpa [C.length_support] using List.toFinset_card_le C.support
  have hQcard : Q.support.toFinset.card ≤ Q.length + 1 := by
    simpa [Q.length_support] using List.toFinset_card_le Q.support
  calc
    (cycleSpliceCore P Q C).card ≤
        (P.support.toFinset ∪ C.support.toFinset ∪ Q.support.toFinset).card :=
      hsdiff
    _ ≤ (P.support.toFinset ∪ C.support.toFinset).card +
        Q.support.toFinset.card := hunion₂
    _ ≤ (P.support.toFinset.card + C.support.toFinset.card) +
        Q.support.toFinset.card := Nat.add_le_add_right hunion₁ _
    _ ≤ (P.length + 1 + (C.length + 1)) + (Q.length + 1) :=
      Nat.add_le_add (Nat.add_le_add hPcard hCcard) hQcard
    _ = P.length + C.length + Q.length + 3 := by omega

/-- The numerical estimate used in Lemma 4.2: two connectors of length at
most `3m` and a cycle of length at most `2m` leave room inside the prescribed
`10m` core budget. -/
theorem cycleSpliceCore_card_le_ten_mul {x y c z : V} {m : ℕ}
    (P : G.Walk x c) (Q : G.Walk y z) (C : G.Walk c c)
    (hm : 2 ≤ m) (hP : P.length ≤ 3 * m) (hQ : Q.length ≤ 3 * m)
    (hC : C.length ≤ 2 * m) :
    (cycleSpliceCore P Q C).card ≤ 10 * m := by
  exact (cycleSpliceCore_card_le P Q C).trans (by omega)

/-! ## A finite greedy maximal-family lemma -/

/-- A finite-key greedy construction of a maximal conflict-free family.

The candidate type itself need not carry a finiteness instance.  This is
important for adjusters, which contain proof-valued path certificates.  It is
enough that each candidate has a key in a finite type and candidates with the
same key conflict.  Scanning the keys then constructs a finite family which
conflicts with every candidate. -/
theorem exists_finite_maximal_conflictFree_family_local
    {Candidate Key : Type*} [Fintype Key]
    (key : Candidate → Key) (Conflict : Candidate → Candidate → Prop)
    (hsame : ∀ a b, key a = key b → Conflict a b)
    (hsymm : ∀ a b, Conflict a b → Conflict b a) :
    ∃ S : Finset Candidate,
      ((S : Set Candidate).Pairwise fun a b ↦ ¬ Conflict a b) ∧
        ∀ a : Candidate, ∃ b ∈ S, Conflict a b := by
  classical
  have aux : ∀ keys : Finset Key, ∃ S : Finset Candidate,
      ((S : Set Candidate).Pairwise fun a b ↦ ¬ Conflict a b) ∧
      (∀ a : Candidate, key a ∈ keys → ∃ b ∈ S, Conflict a b) := by
    intro keys
    induction keys using Finset.induction with
    | empty =>
        refine ⟨∅, ?_, ?_⟩
        · simp
        · intro a ha
          simp at ha
    | @insert k keys hk ih =>
        obtain ⟨S, hSpair, hSmax⟩ := ih
        by_cases hnew : ∃ a : Candidate,
            key a = k ∧ ∀ b ∈ S, ¬ Conflict a b
        · obtain ⟨a, hakey, haconflict⟩ := hnew
          refine ⟨insert a S, ?_, ?_⟩
          · intro x hx y hy hxy
            simp only [Finset.coe_insert, Set.mem_insert_iff] at hx hy
            rcases hx with rfl | hx <;> rcases hy with rfl | hy
            · exact (hxy rfl).elim
            · exact haconflict y hy
            · intro hxa
              exact haconflict x hx (hsymm x _ hxa)
            · exact hSpair hx hy hxy
          · intro x hxkey
            rw [Finset.mem_insert] at hxkey
            rcases hxkey with hxk | hxkeys
            · refine ⟨a, Finset.mem_insert_self a S, ?_⟩
              exact hsame x a (hxk.trans hakey.symm)
            · obtain ⟨b, hbS, hxb⟩ := hSmax x hxkeys
              exact ⟨b, Finset.mem_insert_of_mem hbS, hxb⟩
        · refine ⟨S, hSpair, ?_⟩
          intro a hakeys
          rw [Finset.mem_insert] at hakeys
          rcases hakeys with hak | hakeys
          · have hnotall : ¬ ∀ b ∈ S, ¬ Conflict a b := by
              intro hall
              exact hnew ⟨a, hak, hall⟩
            push_neg at hnotall
            obtain ⟨b, hbS, hab⟩ := hnotall
            exact ⟨b, hbS, hab⟩
          · exact hSmax a hakeys
  obtain ⟨S, hpair, hmax⟩ := aux (Finset.univ : Finset Key)
  exact ⟨S, hpair, fun a ↦ hmax a (Finset.mem_univ _)⟩

/-- Remove a controlled exceptional subfamily and retain any prescribed
number of good members.  This is the finite counting step used after Claims
4.5 and 4.6; all asymptotic estimates enter only through `hcard`. -/
theorem exists_subset_sdiff_card_eq_of_add_card_le
    {Candidate : Type*} [DecidableEq Candidate]
    (S bad : Finset Candidate) (target : ℕ) (hbad : bad ⊆ S)
    (hcard : target + bad.card ≤ S.card) :
    ∃ T : Finset Candidate, T ⊆ S \ bad ∧ T.card = target := by
  have htarget : target ≤ (S \ bad).card := by
    rw [Finset.card_sdiff_of_subset hbad]
    omega
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq htarget
  exact ⟨T, hT, hTcard⟩

/-- The `4R`, discard fewer than `R`, retain `2R` specialization used between
Claims 4.5 and 4.6. -/
theorem exists_two_mul_subfamily_after_discard_lt
    {Candidate : Type*} [DecidableEq Candidate]
    (S bad : Finset Candidate) (R : ℕ) (hbad : bad ⊆ S)
    (hS : 4 * R ≤ S.card) (hbadCard : bad.card < R) :
    ∃ T : Finset Candidate, T ⊆ S \ bad ∧ T.card = 2 * R := by
  apply exists_subset_sdiff_card_eq_of_add_card_le S bad (2 * R) hbad
  omega

/-! ## The maximal family used in Lemma 4.3 -/

/-- There is a short path from `S` to `T` avoiding `X` altogether. -/
def HasShortAvoidingConnection (G : SimpleGraph V) (X : Finset V)
    (S T : Finset V) (radius : ℕ) : Prop :=
  ∃ x ∈ S, ∃ y ∈ T, ∃ p : G.Walk x y,
    p.IsPath ∧ p.Avoids (X : Set V) ∅ ∧ p.length ≤ radius

/-- A common vertex outside the deleted set gives a length-zero connection.
This turns the pairwise no-short-connection invariant of the maximal family
into literal disjointness of its end sets. -/
theorem hasShortAvoidingConnection_of_common_vertex
    {X S T : Finset V} {radius : ℕ} {z : V}
    (hzS : z ∈ S) (hzT : z ∈ T) (hzX : z ∉ X) :
    HasShortAvoidingConnection G X S T radius := by
  refine ⟨z, hzS, z, hzT, Walk.nil, Walk.IsPath.nil, ?_, by simp⟩
  intro w hw hwX
  have hwz : w = z := by simpa using hw
  exact hzX (hwz ▸ hwX)

theorem HasShortAvoidingConnection.symm {X S T : Finset V} {radius : ℕ}
    (h : HasShortAvoidingConnection G X S T radius) :
    HasShortAvoidingConnection G X T S radius := by
  obtain ⟨x, hx, y, hy, p, hp, havoid, hlen⟩ := h
  exact ⟨y, hy, x, hx, p.reverse, hp.reverse, havoid.reverse, by simpa using hlen⟩

/-- Relabel the two ends of an adjuster so that a prescribed short connection
starts in its left end.  Swapping preserves the core and the full vertex set,
which lets Claims 4.5 and 4.6 orient their shortest paths without changing any
avoidance hypothesis. -/
theorem Adjuster.exists_orientation_with_shortConnection_from_leftEnd
    {D radius k connectionRadius : ℕ}
    (A : Adjuster G D radius k) (deleted target : Finset V)
    (h : HasShortAvoidingConnection G deleted
      (A.leftEnd.verts ∪ A.rightEnd.verts) target connectionRadius) :
    ∃ A' : Adjuster G D radius k,
      A'.core = A.core ∧ A'.verts = A.verts ∧
        HasShortAvoidingConnection G deleted A'.leftEnd.verts target
          connectionRadius := by
  classical
  obtain ⟨x, hx, y, hy, p, hp, havoid, hlen⟩ := h
  rw [Finset.mem_union] at hx
  rcases hx with hxLeft | hxRight
  · exact ⟨A, rfl, rfl, x, hxLeft, y, hy, p, hp, havoid, hlen⟩
  · refine ⟨A.swap, by simp, by simp, x, ?_, y, hy, p, hp, havoid, hlen⟩
    exact hxRight

/-- If no short path from `A` reaches `Y` while avoiding `X`, then adding
`Y` to the deleted set does not change the radius-`radius` ball from `A`.
This is the formal deletion identity used in Claims 4.5 and 4.6 to pass from
balls in `G-U-Bᵢ-Cᵢ` to the corresponding balls in `G-L-U-Bᵢ-Cᵢ`. -/
theorem ballAvoidingFrom_union_eq_of_no_shortAvoidingConnection [Fintype V]
    (G : SimpleGraph V) (X Y A : Finset V) (radius : ℕ)
    (hAX : Disjoint A X)
    (hfar : ¬ HasShortAvoidingConnection G X A Y radius) :
    ballAvoidingFrom G ((X : Set V) ∪ (Y : Set V)) A radius =
      ballAvoidingFrom G (X : Set V) A radius := by
  classical
  apply ballAvoidingFrom_union_eq_of_disjoint
  intro y hyBall hyY
  apply hfar
  obtain ⟨a, ha, p, hp, hplen⟩ :=
    (mem_ballAvoidingFrom G (X : Set V) A radius y).1 hyBall
  have hpEmpty : p.Avoids (X : Set V) ∅ := by
    intro z hz hzX
    have hza : z = a := by simpa using hp.2 z hz hzX
    subst z
    exact (Finset.disjoint_left.1 hAX ha hzX).elim
  exact ⟨a, ha, y, hyY, p, hp.1, hpEmpty, hplen⟩

/-- Pointwise form of the exceptional-set definition: outside both `W` and
`manyNeighborsInto G W d`, a vertex has fewer than `d` neighbors in `W`. -/
theorem card_neighborsInto_lt_of_not_mem_manyNeighborsInto [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (d : ℕ) {v : V}
    (hvW : v ∉ W) (hvExceptional : v ∉ manyNeighborsInto G W d) :
    (W.filter fun w ↦ G.Adj v w).card < d := by
  have hnotLower : ¬ d ≤ (W.filter fun w ↦ G.Adj v w).card := by
    intro hlower
    exact hvExceptional ((mem_manyNeighborsInto G W d v).2 ⟨hvW, hlower⟩)
  omega

/-- Uniform degree-into-`W` bound on a set which avoids both `W` and the
exceptional high-contact set.  This discharges condition C4 in each of the
three correlated Lemma 3.7 applications in Lemma 4.3. -/
theorem neighborsInto_le_of_disjoint_manyNeighborsInto [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (W S : Finset V) (d : ℕ)
    (hSW : Disjoint S W)
    (hSExceptional : Disjoint S (manyNeighborsInto G W d)) :
    ∀ v ∈ S, (W.filter fun w ↦ G.Adj v w).card ≤ d := by
  intro v hvS
  exact (card_neighborsInto_lt_of_not_mem_manyNeighborsInto G W d
    (fun hvW ↦ (Finset.disjoint_left.1 hSW hvS hvW).elim)
    (fun hvExceptional ↦
      (Finset.disjoint_left.1 hSExceptional hvS hvExceptional).elim)).le

/-- Choose a minimum-length avoiding path between two finite sets from a
given short connection.  Its global minimality is exactly the input needed
by `hasLimitedContactAfterDeletion_of_shortest_path`. -/
theorem exists_shortest_of_hasShortAvoidingConnection
    {X S T : Finset V} {radius : ℕ}
    (h : HasShortAvoidingConnection G X S T radius) :
    ∃ x ∈ S, ∃ y ∈ T, ∃ p : G.Walk x y,
      p.IsPath ∧ p.Avoids (X : Set V) ∅ ∧ p.length ≤ radius ∧
      ∀ x' ∈ S, ∀ y' ∈ T, ∀ q : G.Walk x' y',
        q.IsPath → q.Avoids (X : Set V) ∅ → p.length ≤ q.length := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∃ x ∈ S, ∃ y ∈ T, ∃ p : G.Walk x y,
      p.IsPath ∧ p.Avoids (X : Set V) ∅ ∧ p.length = n
  have hP : ∃ n, P n := by
    obtain ⟨x, hx, y, hy, p, hp, havoid, hlen⟩ := h
    exact ⟨p.length, x, hx, y, hy, p, hp, havoid, rfl⟩
  obtain ⟨x, hx, y, hy, p, hp, havoid, hpLength⟩ := Nat.find_spec hP
  refine ⟨x, hx, y, hy, p, hp, havoid, ?_, ?_⟩
  · obtain ⟨x₀, hx₀, y₀, hy₀, p₀, hp₀, havoid₀, hlen₀⟩ := h
    have hmin : Nat.find hP ≤ p₀.length :=
      Nat.find_min' hP ⟨x₀, hx₀, y₀, hy₀, p₀, hp₀, havoid₀, rfl⟩
    omega
  · intro x' hx' y' hy' q hq hqavoid
    have hmin : Nat.find hP ≤ q.length :=
      Nat.find_min' hP ⟨x', hx', y', hy', q, hq, hqavoid, rfl⟩
    omega

/-- A short connection from a set disjoint from the deleted set can be
chosen shortest, and its support then has the exact limited-contact property
used by Lemma 3.7. -/
theorem exists_shortestConnection_with_limitedContact [Fintype V]
    {deleted A T : Finset V} {radius : ℕ}
    (hAdeleted : Disjoint A deleted)
    (h : HasShortAvoidingConnection G deleted A T radius) :
    ∃ a ∈ A, ∃ t ∈ T, ∃ p : G.Walk a t,
      p.IsPath ∧ p.Avoids (deleted : Set V) ∅ ∧
        p.length ≤ radius ∧
        HasLimitedContactAfterDeletion G A deleted p.support.toFinset 2 := by
  obtain ⟨a, ha, t, ht, p, hp, hpdeleted, hplen, hshortest⟩ :=
    exists_shortest_of_hasShortAvoidingConnection h
  exact ⟨a, ha, t, ht, p, hp, hpdeleted, hplen,
    hasLimitedContactAfterDeletion_of_shortest_path
      G A T deleted ha ht p hp hpdeleted hAdeleted hshortest⟩

/-- Opposite-end form of the shortest-path limited-contact lemma.  The fixed
path need not start in `A`; it is enough that no path from `A` to `T` is
shorter.  In Claims 4.5 and 4.6 the fixed path starts in the left end, while
`A` is the right end that Lemma 3.7 grows. -/
theorem hasLimitedContactAfterDeletion_of_opposite_shortest_path
    [Fintype V] (G : SimpleGraph V) (A T deleted : Finset V)
    {s t : V} (ht : t ∈ T) (p : G.Walk s t)
    (hp : p.IsPath) (hpdeleted : p.Avoids (deleted : Set V) ∅)
    (hAdeleted : Disjoint A deleted)
    (hshortest : ∀ a' ∈ A, ∀ t' ∈ T, ∀ q : G.Walk a' t',
      q.IsPath → q.Avoids (deleted : Set V) ∅ → p.length ≤ q.length) :
    HasLimitedContactAfterDeletion G A deleted p.support.toFinset 2 := by
  classical
  intro r
  let C : Finset V := p.support.toFinset
  let current := ballAvoidingFrom G ((deleted : Set V) ∪ (C : Set V)) A r
  have hcontactSubset :
      blockedExternalNeighborhood G (C : Set V) current ⊆
        (p.support.take (r + 2)).toFinset := by
    intro y hy
    obtain ⟨hyN, hyC⟩ :=
      (mem_blockedExternalNeighborhood G (C : Set V) current y).1 hy
    have hyp : y ∈ p.support := by
      simpa [C] using hyC
    obtain ⟨_, x, hxcurrent, hxy⟩ :=
      (mem_externalNeighborhood G current y).1 hyN
    obtain ⟨a', ha'A, q, hq, hqlen⟩ :=
      (mem_ballAvoidingFrom G
        ((deleted : Set V) ∪ (C : Set V)) A r x).1 hxcurrent
    have hqdeleted : q.Avoids (deleted : Set V) ∅ := by
      intro z hzq hzdeleted
      have hza' := hq.2 z hzq (Or.inl hzdeleted)
      have hzeq : z = a' := by simpa using hza'
      subst z
      exact (Finset.disjoint_left.1 hAdeleted ha'A hzdeleted).elim
    let edge : G.Walk x y := Walk.cons hxy Walk.nil
    have hedgedeleted : edge.Avoids (deleted : Set V) ∅ := by
      intro z hzedge hzdeleted
      have hzedge' : z = x ∨ z = y := by
        simpa [edge] using hzedge
      rcases hzedge' with hzx | hzy
      · subst z
        exact (hqdeleted _ q.end_mem_support hzdeleted).elim
      · subst z
        exact (hpdeleted _ hyp hzdeleted).elim
    have hdropdeleted :
        (p.dropUntil y hyp).Avoids (deleted : Set V) ∅ :=
      hpdeleted.of_support_subset (p.support_dropUntil_subset_support hyp)
    let w : G.Walk a' t :=
      (q.append edge).append (p.dropUntil y hyp)
    have hwdeleted : w.Avoids (deleted : Set V) ∅ := by
      intro z hzw hzdeleted
      change z ∈ ((q.append edge).append (p.dropUntil y hyp)).support at hzw
      rw [Walk.mem_support_append_iff, Walk.mem_support_append_iff] at hzw
      rcases hzw with (hzq | hzedge) | hzdrop
      · exact hqdeleted z hzq hzdeleted
      · exact hedgedeleted z hzedge hzdeleted
      · exact hdropdeleted z hzdrop hzdeleted
    have htake : (p.takeUntil y hyp).length ≤ r + 1 := by
      by_contra hnot
      have htakeLong : r + 1 < (p.takeUntil y hyp).length :=
        Nat.lt_of_not_ge hnot
      have hsplit : (p.takeUntil y hyp).length +
          (p.dropUntil y hyp).length = p.length := by
        calc
          (p.takeUntil y hyp).length + (p.dropUntil y hyp).length =
              ((p.takeUntil y hyp).append (p.dropUntil y hyp)).length := by
                rw [Walk.length_append]
          _ = p.length := congrArg Walk.length (p.take_spec hyp)
      have hwlength : w.length < p.length := by
        dsimp [w, edge]
        simp only [Walk.length_append, Walk.length_cons, Walk.length_nil]
        omega
      have hshort := hshortest a' ha'A t ht w.bypass w.bypass_isPath
        (hwdeleted.of_support_subset w.support_bypass_subset_support)
      exact (Nat.not_lt_of_ge (hshort.trans w.length_bypass_le_length)) hwlength
    rw [List.mem_toFinset]
    apply (List.mem_take_iff_idxOf_lt hyp).2
    rw [← p.length_takeUntil hyp]
    omega
  have hcard := Finset.card_le_card hcontactSubset
  have htoFinset := List.toFinset_card_le (p.support.take (r + 2))
  have htakeLength : (p.support.take (r + 2)).length ≤ r + 2 := by
    simp
  dsimp [current, C] at hcard
  omega

/-- Choose and orient a globally shortest connection from the union of an
adjuster's ends.  The end not containing the initial vertex then has
two-limited contact with the chosen path. -/
theorem Adjuster.exists_oriented_shortestConnection_with_opposite_limitedContact
    [Fintype V] {D radius k connectionRadius : ℕ}
    (A : Adjuster G D radius k) (deleted target : Finset V)
    (hEndsDeleted : Disjoint (A.leftEnd.verts ∪ A.rightEnd.verts) deleted)
    (h : HasShortAvoidingConnection G deleted
      (A.leftEnd.verts ∪ A.rightEnd.verts) target connectionRadius) :
    ∃ (A' : Adjuster G D radius k) (a t : V) (p : G.Walk a t),
      A'.core = A.core ∧ A'.verts = A.verts ∧
      A'.leftEnd.verts ∪ A'.rightEnd.verts =
        A.leftEnd.verts ∪ A.rightEnd.verts ∧
      a ∈ A'.leftEnd.verts ∧ t ∈ target ∧
      p.IsPath ∧ p.Avoids (deleted : Set V) ∅ ∧
      p.length ≤ connectionRadius ∧
      (∀ a' ∈ A'.leftEnd.verts ∪ A'.rightEnd.verts,
        ∀ t' ∈ target, ∀ q : G.Walk a' t',
          q.IsPath → q.Avoids (deleted : Set V) ∅ → p.length ≤ q.length) ∧
      (∀ a' ∈ A'.rightEnd.verts, ∀ t' ∈ target, ∀ q : G.Walk a' t',
        q.IsPath → q.Avoids (deleted : Set V) ∅ → p.length ≤ q.length) ∧
      HasLimitedContactAfterDeletion G A'.rightEnd.verts deleted
        p.support.toFinset 2 := by
  classical
  obtain ⟨a, ha, t, ht, p, hp, hpdeleted, hplen, hshortest⟩ :=
    exists_shortest_of_hasShortAvoidingConnection h
  rw [Finset.mem_union] at ha
  rcases ha with haLeft | haRight
  · have hrightDeleted : Disjoint A.rightEnd.verts deleted :=
      hEndsDeleted.mono_left Finset.subset_union_right
    have hrightShortest : ∀ a' ∈ A.rightEnd.verts,
        ∀ t' ∈ target, ∀ q : G.Walk a' t',
          q.IsPath → q.Avoids (deleted : Set V) ∅ → p.length ≤ q.length := by
      intro a' ha' t' ht' q hq hqdeleted
      exact hshortest a' (Finset.mem_union_right _ ha') t' ht' q hq hqdeleted
    refine ⟨A, a, t, p, rfl, rfl, rfl, haLeft, ht, hp, hpdeleted, hplen,
      hshortest, hrightShortest, ?_⟩
    exact hasLimitedContactAfterDeletion_of_opposite_shortest_path
      G A.rightEnd.verts target deleted ht p hp hpdeleted hrightDeleted
        hrightShortest
  · have hleftDeleted : Disjoint A.leftEnd.verts deleted :=
      hEndsDeleted.mono_left Finset.subset_union_left
    have hleftShortest : ∀ a' ∈ A.leftEnd.verts,
        ∀ t' ∈ target, ∀ q : G.Walk a' t',
          q.IsPath → q.Avoids (deleted : Set V) ∅ → p.length ≤ q.length := by
      intro a' ha' t' ht' q hq hqdeleted
      exact hshortest a' (Finset.mem_union_left _ ha') t' ht' q hq hqdeleted
    refine ⟨A.swap, a, t, p, by simp, by simp, by
      simp [Adjuster.swap, Finset.union_comm], haRight, ht, hp, hpdeleted,
      hplen, ?_, ?_, ?_⟩
    · simpa [Adjuster.swap, Finset.union_comm] using hshortest
    · simpa [Adjuster.swap] using hleftShortest
    exact hasLimitedContactAfterDeletion_of_opposite_shortest_path
      G A.leftEnd.verts target deleted ht p hp hpdeleted hleftDeleted hleftShortest

/-- Proof-carrying data chosen from an oriented shortest connection.  This
packages exactly the candidate-indexed functions used as the `Aᵢ,Bᵢ,Cᵢ`
inputs of correlated Lemma 3.7 in Claims 4.5 and 4.6. -/
structure OrientedShortestConnectionData
    [Fintype V] (G : SimpleGraph V) {D adjusterRadius k connectionRadius : ℕ}
    (A : Adjuster G D adjusterRadius k) (deleted target : Finset V) where
  adjusted : Adjuster G D adjusterRadius k
  start : V
  finish : V
  path : G.Walk start finish
  core_eq : adjusted.core = A.core
  verts_eq : adjusted.verts = A.verts
  ends_eq : adjusted.leftEnd.verts ∪ adjusted.rightEnd.verts =
    A.leftEnd.verts ∪ A.rightEnd.verts
  start_mem : start ∈ adjusted.leftEnd.verts
  finish_mem : finish ∈ target
  isPath : path.IsPath
  avoids : path.Avoids (deleted : Set V) ∅
  length_le : path.length ≤ connectionRadius
  ends_shortest :
    ∀ a' ∈ adjusted.leftEnd.verts ∪ adjusted.rightEnd.verts,
      ∀ t' ∈ target, ∀ q : G.Walk a' t',
        q.IsPath → q.Avoids (deleted : Set V) ∅ → path.length ≤ q.length
  opposite_shortest :
    ∀ a' ∈ adjusted.rightEnd.verts, ∀ t' ∈ target,
      ∀ q : G.Walk a' t', q.IsPath → q.Avoids (deleted : Set V) ∅ →
        path.length ≤ q.length
  opposite_limitedContact :
    HasLimitedContactAfterDeletion G adjusted.rightEnd.verts deleted
      path.support.toFinset 2

/-- The proved shortest-path theorem supplies the preceding data.  Keeping
the result in `Nonempty` permits elimination of the existential proof wholly
inside `Prop`. -/
theorem Adjuster.nonempty_orientedShortestConnectionData
    [Fintype V] {D adjusterRadius k connectionRadius : ℕ}
    (A : Adjuster G D adjusterRadius k) (deleted target : Finset V)
    (hEndsDeleted : Disjoint (A.leftEnd.verts ∪ A.rightEnd.verts) deleted)
    (h : HasShortAvoidingConnection G deleted
      (A.leftEnd.verts ∪ A.rightEnd.verts) target connectionRadius) :
    Nonempty (OrientedShortestConnectionData (connectionRadius := connectionRadius)
      G A deleted target) := by
  classical
  obtain ⟨A', a, t, p, hcore, hverts, hends, ha, ht, hp, havoid, hlen,
    hendsShortest, hshortest, hcontact⟩ :=
    A.exists_oriented_shortestConnection_with_opposite_limitedContact
      deleted target hEndsDeleted h
  exact ⟨
    { adjusted := A'
      start := a
      finish := t
      path := p
      core_eq := hcore
      verts_eq := hverts
      ends_eq := hends
      start_mem := ha
      finish_mem := ht
      isPath := hp
      avoids := havoid
      length_le := hlen
      ends_shortest := hendsShortest
      opposite_shortest := hshortest
      opposite_limitedContact := hcontact }⟩

/-- Choose the concrete oriented shortest-connection data. -/
noncomputable def Adjuster.orientedShortestConnectionData
    [Fintype V] {D adjusterRadius k connectionRadius : ℕ}
    (A : Adjuster G D adjusterRadius k) (deleted target : Finset V)
    (hEndsDeleted : Disjoint (A.leftEnd.verts ∪ A.rightEnd.verts) deleted)
    (h : HasShortAvoidingConnection G deleted
      (A.leftEnd.verts ∪ A.rightEnd.verts) target connectionRadius) :
    OrientedShortestConnectionData (connectionRadius := connectionRadius)
      G A deleted target :=
  Classical.choice
    (A.nonempty_orientedShortestConnectionData deleted target hEndsDeleted h)

/-- The globally shortest connection meets the end opposite its initial
vertex nowhere.  If it met that end, dropping the strict initial segment
would give a shorter admissible connection from that end to the target. -/
theorem OrientedShortestConnectionData.opposite_disjoint_path
    [Fintype V] {D adjusterRadius k connectionRadius : ℕ}
    {A : Adjuster G D adjusterRadius k} {deleted target : Finset V}
    (P : OrientedShortestConnectionData
      (connectionRadius := connectionRadius) G A deleted target) :
    Disjoint P.adjusted.rightEnd.verts P.path.support.toFinset := by
  classical
  rw [Finset.disjoint_left]
  intro z hzEnd hzPath
  have hzSupport : z ∈ P.path.support := List.mem_toFinset.1 hzPath
  have hzStart : z ≠ P.start := by
    intro h
    subst z
    exact (Finset.disjoint_left.1 P.adjusted.ends_disjoint
      P.start_mem hzEnd).elim
  let q : G.Walk z P.finish := P.path.dropUntil z hzSupport
  have hqPath : q.IsPath := by
    apply Walk.IsPath.mk'
    exact (P.path.support_dropUntil_suffix_support hzSupport).nodup
      P.isPath.support_nodup
  have hqAvoid : q.Avoids (deleted : Set V) ∅ :=
    P.avoids.of_support_subset
      (P.path.support_dropUntil_subset_support hzSupport)
  have hshort := P.opposite_shortest z hzEnd P.finish P.finish_mem q
    hqPath hqAvoid
  have hstrict : q.length < P.path.length :=
    P.path.length_dropUntil_lt_length hzSupport hzStart
  omega

/-- Minimality also shows that the chosen path meets its selected (left)
end only at its initial vertex. -/
theorem OrientedShortestConnectionData.eq_start_of_mem_leftEnd_path
    [Fintype V] {D adjusterRadius k connectionRadius : ℕ}
    {A : Adjuster G D adjusterRadius k} {deleted target : Finset V}
    (P : OrientedShortestConnectionData
      (connectionRadius := connectionRadius) G A deleted target)
    {z : V} (hzEnd : z ∈ P.adjusted.leftEnd.verts)
    (hzPath : z ∈ P.path.support) : z = P.start := by
  by_contra hzStart
  let q : G.Walk z P.finish := P.path.dropUntil z hzPath
  have hqPath : q.IsPath := by
    apply Walk.IsPath.mk'
    exact (P.path.support_dropUntil_suffix_support hzPath).nodup
      P.isPath.support_nodup
  have hqAvoid : q.Avoids (deleted : Set V) ∅ :=
    P.avoids.of_support_subset
      (P.path.support_dropUntil_subset_support hzPath)
  have hshort := P.ends_shortest z (Finset.mem_union_left _ hzEnd)
    P.finish P.finish_mem q hqPath hqAvoid
  have hstrict : q.length < P.path.length :=
    P.path.length_dropUntil_lt_length hzPath hzStart
  omega

/-- A small simple adjuster with the varying radius and end size used in the
maximal collection of the proof of Lemma 4.3. -/
structure SmallSimpleAdjusterCandidate (G : SimpleGraph V)
    (minRadius maxRadius : ℕ) where
  radius : ℕ
  min_le : minRadius ≤ radius
  le_max : radius ≤ maxRadius
  adjuster : Adjuster G (radius ^ 2) radius 1

/-- The genuinely independent numerical part of Lemma 4.2 after the source
matrix of six expansions has been constructed by Lemma 3.11.  This is kept at
the root `Erdos63` namespace because both the Claim 4.4 scale and the public
Lemma 4.2 theorem consume it. -/
structure LM42ConnectorScale (N d D m cycleLength : ℕ)
    (epsilon kappa : ℝ) where
  squareWorkspace : ℕ
  cubeWorkspace : ℕ
  squareStart : ℕ
  cubeStart : ℕ
  squareRadius : ℕ
  cubeRadius : ℕ
  two_le_m : 2 ≤ m
  D_pos : 0 < D
  connector_workspace_large :
    cycleLength + 2 + 2 * D + 2 * (m ^ 2 * D) ≤ cubeWorkspace
  connector_workspace_path :
    cycleLength + 2 + (3 * m + 1) + 2 * D ≤ squareWorkspace
  squareSeed : squareStart ≤ m ^ 2 * D ∨ squareStart + squareWorkspace ≤ d - 1
  cubeSeed : cubeStart ≤ m ^ 3 * D ∨ cubeStart + cubeWorkspace ≤ d - 1
  squareGrowth : LM42GrowthSchedule N squareStart squareWorkspace
    squareRadius epsilon kappa
  cubeGrowth : LM42GrowthSchedule N cubeStart cubeWorkspace
    cubeRadius epsilon kappa
  square_path_radius : 2 * (squareRadius + 1) ≤ m
  cube_path_radius : 2 * (cubeRadius + 1) ≤ m
  cycle_length : cycleLength ≤ 2 * m

namespace SmallSimpleAdjusterCandidate

variable {minRadius maxRadius : ℕ}

/-- The union of the two ends, excluding the core. -/
noncomputable def ends
    (A : SmallSimpleAdjusterCandidate G minRadius maxRadius) : Finset V :=
  A.adjuster.leftEnd.verts ∪ A.adjuster.rightEnd.verts

@[simp] theorem card_ends
    (A : SmallSimpleAdjusterCandidate G minRadius maxRadius) :
    A.ends.card = 2 * A.radius ^ 2 := by
  classical
  rw [ends, Finset.card_union_of_disjoint A.adjuster.ends_disjoint,
    A.adjuster.leftEnd.card_verts, A.adjuster.rightEnd.card_verts]
  omega

theorem card_adjuster_verts_le
    (A : SmallSimpleAdjusterCandidate G minRadius maxRadius) :
    A.adjuster.verts.card ≤ 2 * A.radius ^ 2 + 10 * A.radius := by
  simpa using A.adjuster.card_verts_le

theorem card_adjuster_verts_le_maxRadius
    (A : SmallSimpleAdjusterCandidate G minRadius maxRadius) :
    A.adjuster.verts.card ≤ 2 * maxRadius ^ 2 + 10 * maxRadius := by
  have hsq : A.radius ^ 2 ≤ maxRadius ^ 2 :=
    Nat.pow_le_pow_left A.le_max 2
  exact A.card_adjuster_verts_le.trans
    (Nat.add_le_add (Nat.mul_le_mul_left 2 hsq)
      (Nat.mul_le_mul_left 10 A.le_max))

/-- The union of all adjuster carriers in a finite candidate family has the
source-paper bound obtained by summing the uniform per-candidate estimate.
No disjointness assumption is needed for this upper bound. -/
theorem card_biUnion_adjuster_verts_le_maxRadius
    (S : Finset (SmallSimpleAdjusterCandidate G minRadius maxRadius)) :
    (S.biUnion fun A ↦ A.adjuster.verts).card ≤
      S.card * (2 * maxRadius ^ 2 + 10 * maxRadius) := by
  let originalDecEq : DecidableEq V := inferInstance
  classical
  let : DecidableEq V := originalDecEq
  calc
    (S.biUnion fun A ↦ A.adjuster.verts).card ≤
        ∑ A ∈ S, A.adjuster.verts.card := Finset.card_biUnion_le
    _ ≤ ∑ _A ∈ S, (2 * maxRadius ^ 2 + 10 * maxRadius) := by
      apply Finset.sum_le_sum
      intro A hA
      exact A.card_adjuster_verts_le_maxRadius
    _ = S.card * (2 * maxRadius ^ 2 + 10 * maxRadius) := by simp

/-- Adding a fixed protected set to all carriers in a finite candidate family
costs at most the sum of its cardinality and the preceding family bound. -/
theorem card_union_biUnion_adjuster_verts_le_maxRadius
    (U : Finset V)
    (S : Finset (SmallSimpleAdjusterCandidate G minRadius maxRadius)) :
    (U ∪ S.biUnion fun A ↦ A.adjuster.verts).card ≤
      U.card + S.card * (2 * maxRadius ^ 2 + 10 * maxRadius) := by
  let originalDecEq : DecidableEq V := inferInstance
  classical
  let : DecidableEq V := originalDecEq
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (card_biUnion_adjuster_verts_le_maxRadius S) U.card)

/-- Subtype-family version used directly for the maximal eligible collection
`A₀`, whose membership proof is intentionally erased from the count. -/
theorem card_biUnion_subtype_adjuster_verts_le_maxRadius
    {P : SmallSimpleAdjusterCandidate G minRadius maxRadius → Prop}
    (S : Finset {A // P A}) :
    (S.biUnion fun A ↦ A.1.adjuster.verts).card ≤
      S.card * (2 * maxRadius ^ 2 + 10 * maxRadius) := by
  let originalDecEq : DecidableEq V := inferInstance
  classical
  let : DecidableEq V := originalDecEq
  calc
    (S.biUnion fun A ↦ A.1.adjuster.verts).card ≤
        ∑ A ∈ S, A.1.adjuster.verts.card := Finset.card_biUnion_le
    _ ≤ ∑ _A ∈ S, (2 * maxRadius ^ 2 + 10 * maxRadius) := by
      apply Finset.sum_le_sum
      intro A hA
      exact A.1.card_adjuster_verts_le_maxRadius
    _ = S.card * (2 * maxRadius ^ 2 + 10 * maxRadius) := by simp

@[simp] theorem leftRoot_mem_ends
    (A : SmallSimpleAdjusterCandidate G minRadius maxRadius) :
    A.adjuster.leftRoot ∈ A.ends := by
  classical
  simp [ends, A.adjuster.leftEnd.root_mem]

@[simp] theorem rightRoot_mem_ends
    (A : SmallSimpleAdjusterCandidate G minRadius maxRadius) :
    A.adjuster.rightRoot ∈ A.ends := by
  classical
  simp [ends, A.adjuster.rightEnd.root_mem]

/-- Eligibility for the family `A₀` in the paper: the whole adjuster avoids
the ambient deletion, both ends avoid the high-degree set, and the ends are
far from the protected low-degree vertices. -/
def Eligible (A : SmallSimpleAdjusterCandidate G minRadius maxRadius)
    (deleted highDegree protectedSet : Finset V) (separation : ℕ) : Prop :=
  Disjoint deleted A.adjuster.verts ∧
  Disjoint A.ends highDegree ∧
  ¬ HasShortAvoidingConnection G highDegree A.ends
      (protectedSet \ highDegree) separation

/-- Candidate-dependent reachability used in Claims 4.5 and 4.6.  The
ambient deleted set is augmented by the candidate's own core, exactly as in
the source proof, so that a replacement end remains disjoint from the two
adjustable routes already stored in the core. -/
def ReachesAvoidingOwnCore
    (A : SmallSimpleAdjusterCandidate G minRadius maxRadius)
    (deleted target : Finset V) (radius : ℕ) : Prop :=
  HasShortAvoidingConnection G (deleted ∪ A.adjuster.core)
    A.ends target radius

/-- The exceptional candidates that have a short connection to `target`. -/
noncomputable def reachingSubfamily
    (S : Finset (SmallSimpleAdjusterCandidate G minRadius maxRadius))
    (deleted target : Finset V) (radius : ℕ) :
    Finset (SmallSimpleAdjusterCandidate G minRadius maxRadius) := by
  classical
  exact S.filter fun A ↦ A.ReachesAvoidingOwnCore deleted target radius

@[simp] theorem mem_reachingSubfamily
    (S : Finset (SmallSimpleAdjusterCandidate G minRadius maxRadius))
    (deleted target : Finset V) (radius : ℕ)
    (A : SmallSimpleAdjusterCandidate G minRadius maxRadius) :
    A ∈ reachingSubfamily S deleted target radius ↔
      A ∈ S ∧ A.ReachesAvoidingOwnCore deleted target radius := by
  classical
  simp [reachingSubfamily]

/-- The two ends of an eligible candidate avoid the ambient deletion
together with their own core. -/
theorem ends_disjoint_deleted_union_core
    (A : SmallSimpleAdjusterCandidate G minRadius maxRadius)
    {deleted highDegree protectedSet : Finset V} {separation : ℕ}
    (hA : A.Eligible deleted highDegree protectedSet separation) :
    Disjoint A.ends (deleted ∪ A.adjuster.core) := by
  rw [Finset.disjoint_left]
  intro v hvEnds hvDeleted
  rw [Finset.mem_union] at hvDeleted
  rcases hvDeleted with hvDeleted | hvCore
  · have hvVerts : v ∈ A.adjuster.verts := by
      rcases Finset.mem_union.1 hvEnds with hvLeft | hvRight
      · exact A.adjuster.leftEnd_verts_subset hvLeft
      · exact A.adjuster.rightEnd_verts_subset hvRight
    exact (Finset.disjoint_left.1 hA.1 hvDeleted hvVerts).elim
  · rcases Finset.mem_union.1 hvEnds with hvLeft | hvRight
    · exact (Finset.disjoint_left.1 A.adjuster.core_disjoint_left
        hvCore hvLeft).elim
    · exact (Finset.disjoint_left.1 A.adjuster.core_disjoint_right
        hvCore hvRight).elim

/-- Filter a proof-carrying eligible family by candidate-dependent short
reachability.  Keeping the proof subtype is convenient for the correlated
Lemma 3.7 index type. -/
noncomputable def reachingEligibleSubfamily
    {deleted highDegree protectedSet : Finset V} {separation : ℕ}
    (S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation})
    (target : Finset V) (radius : ℕ) :
    Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation} := by
  classical
  exact S.filter fun A ↦
    A.1.ReachesAvoidingOwnCore deleted target radius

@[simp] theorem mem_reachingEligibleSubfamily
    {deleted highDegree protectedSet : Finset V} {separation : ℕ}
    (S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation})
    (target : Finset V) (radius : ℕ)
    (A : {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
      A.Eligible deleted highDegree protectedSet separation}) :
    A ∈ reachingEligibleSubfamily S target radius ↔
      A ∈ S ∧ A.1.ReachesAvoidingOwnCore deleted target radius := by
  classical
  simp [reachingEligibleSubfamily]

/-- Canonically choose the oriented shortest connection attached to one
member of a reaching eligible subfamily. -/
noncomputable def reachingCandidateConnectionData
    [Fintype V]
    {deleted highDegree protectedSet target : Finset V}
    {separation connectionRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (i : {A // A ∈ reachingEligibleSubfamily S target connectionRadius}) :
    OrientedShortestConnectionData
      (connectionRadius := connectionRadius) G i.1.1.adjuster
      (deleted ∪ i.1.1.adjuster.core) target := by
  classical
  apply i.1.1.adjuster.orientedShortestConnectionData
  · simpa [SmallSimpleAdjusterCandidate.ends] using
      i.1.1.ends_disjoint_deleted_union_core i.1.2
  · have hreach :=
      (mem_reachingEligibleSubfamily S target connectionRadius i.1).1 i.2 |>.2
    simpa [ReachesAvoidingOwnCore, SmallSimpleAdjusterCandidate.ends] using hreach

/-- The opposite end selected by `reachingCandidateConnectionData` is one of
the original candidate's two ends. -/
theorem reachingCandidateConnectionData_rightEnd_subset
    [Fintype V]
    {deleted highDegree protectedSet target : Finset V}
    {separation connectionRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (i : {A // A ∈ reachingEligibleSubfamily S target connectionRadius}) :
    (reachingCandidateConnectionData i).adjusted.rightEnd.verts ⊆ i.1.1.ends := by
  intro v hv
  have hvEnds : v ∈
      (reachingCandidateConnectionData i).adjusted.leftEnd.verts ∪
        (reachingCandidateConnectionData i).adjusted.rightEnd.verts :=
    Finset.mem_union_right _ hv
  rw [(reachingCandidateConnectionData i).ends_eq] at hvEnds
  exact hvEnds

/-- The internal arm `Qᵢ` from the selected end root to the initial vertex
of the globally shortest connection. -/
noncomputable def reachingCandidateRootPath
    [Fintype V]
    {deleted highDegree protectedSet target : Finset V}
    {separation connectionRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (i : {A // A ∈ reachingEligibleSubfamily S target connectionRadius}) :
    G.Walk (reachingCandidateConnectionData i).adjusted.leftRoot
      (reachingCandidateConnectionData i).start :=
  Classical.choose
    ((reachingCandidateConnectionData i).adjusted.leftEnd.exists_path
      (reachingCandidateConnectionData i).start_mem)

theorem reachingCandidateRootPath_isPath
    [Fintype V]
    {deleted highDegree protectedSet target : Finset V}
    {separation connectionRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (i : {A // A ∈ reachingEligibleSubfamily S target connectionRadius}) :
    (reachingCandidateRootPath i).IsPath :=
  (Classical.choose_spec
    ((reachingCandidateConnectionData i).adjusted.leftEnd.exists_path
      (reachingCandidateConnectionData i).start_mem)).1

theorem reachingCandidateRootPath_length_le
    [Fintype V]
    {deleted highDegree protectedSet target : Finset V}
    {separation connectionRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (i : {A // A ∈ reachingEligibleSubfamily S target connectionRadius}) :
    (reachingCandidateRootPath i).length ≤ i.1.1.radius := by
  exact (Classical.choose_spec
    ((reachingCandidateConnectionData i).adjusted.leftEnd.exists_path
      (reachingCandidateConnectionData i).start_mem)).2.1

theorem reachingCandidateRootPath_support_subset
    [Fintype V]
    {deleted highDegree protectedSet target : Finset V}
    {separation connectionRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (i : {A // A ∈ reachingEligibleSubfamily S target connectionRadius}) :
    ∀ z ∈ (reachingCandidateRootPath i).support,
      z ∈ (reachingCandidateConnectionData i).adjusted.leftEnd.verts := by
  exact (Classical.choose_spec
    ((reachingCandidateConnectionData i).adjusted.leftEnd.exists_path
      (reachingCandidateConnectionData i).start_mem)).2.2

/-! ### The literal candidate-indexed inputs to Lemma 3.7 -/

/-- The end opposite the chosen shortest connection.  This is `Aᵢ` in both
Claims 4.5 and 4.6. -/
noncomputable def reachingCandidateSeed
    [Fintype V]
    {deleted highDegree protectedSet target : Finset V}
    {separation connectionRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (i : {A // A ∈ reachingEligibleSubfamily S target connectionRadius}) :
    Finset V :=
  (reachingCandidateConnectionData i).adjusted.rightEnd.verts

/-- The unchanged candidate core.  This is the first part of `Bᵢ`; keeping
the chosen path itself in `Cᵢ` is the logically equivalent unsplit version
of the source proof. -/
noncomputable def reachingCandidateCore
    [Fintype V]
    {deleted highDegree protectedSet target : Finset V}
    {separation connectionRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (i : {A // A ∈ reachingEligibleSubfamily S target connectionRadius}) :
    Finset V :=
  (reachingCandidateConnectionData i).adjusted.core

/-- The literal `Bᵢ` used by Claims 4.5 and 4.6: the adjuster core together
with the internal arm, but with its terminal/connection vertex removed.  The
removal makes the selected shortest connection avoid `U ∪ Bᵢ` outright. -/
noncomputable def reachingCandidateBarrier
    [Fintype V]
    {deleted highDegree protectedSet target : Finset V}
    {separation connectionRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (i : {A // A ∈ reachingEligibleSubfamily S target connectionRadius}) :
    Finset V :=
  reachingCandidateCore i ∪
    (reachingCandidateRootPath i).support.toFinset.erase
      (reachingCandidateConnectionData i).start

/-- The support of the chosen shortest connection.  This is `Cᵢ`. -/
noncomputable def reachingCandidatePath
    [Fintype V]
    {deleted highDegree protectedSet target : Finset V}
    {separation connectionRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (i : {A // A ∈ reachingEligibleSubfamily S target connectionRadius}) :
    Finset V :=
  (reachingCandidateConnectionData i).path.support.toFinset

theorem reachingCandidateSeed_subset_ends
    [Fintype V]
    {deleted highDegree protectedSet target : Finset V}
    {separation connectionRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (i : {A // A ∈ reachingEligibleSubfamily S target connectionRadius}) :
    reachingCandidateSeed i ⊆ i.1.1.ends :=
  reachingCandidateConnectionData_rightEnd_subset i

/-- Global shortestness gives exactly C3 of Lemma 3.7 for the literal
candidate-indexed sets. -/
theorem reachingCandidate_limitedContact
    [Fintype V]
    {deleted highDegree protectedSet target : Finset V}
    {separation connectionRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (i : {A // A ∈ reachingEligibleSubfamily S target connectionRadius}) :
    HasLimitedContactAfterDeletion G (reachingCandidateSeed i)
      (deleted ∪ reachingCandidateCore i) (reachingCandidatePath i) 2 := by
  change HasLimitedContactAfterDeletion G
    (reachingCandidateConnectionData i).adjusted.rightEnd.verts
    (deleted ∪ (reachingCandidateConnectionData i).adjusted.core)
    (reachingCandidateConnectionData i).path.support.toFinset 2
  rw [(reachingCandidateConnectionData i).core_eq]
  exact (reachingCandidateConnectionData i).opposite_limitedContact

/-- The selected shortest connection avoids the source-faithful barrier.
The only possible intersection with its internal arm is the common initial
vertex, and that vertex was erased from the barrier. -/
theorem reachingCandidatePath_avoids_deleted_union_barrier
    [Fintype V]
    {deleted highDegree protectedSet target : Finset V}
    {separation connectionRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (i : {A // A ∈ reachingEligibleSubfamily S target connectionRadius}) :
    (reachingCandidateConnectionData i).path.Avoids
      ((deleted ∪ reachingCandidateBarrier i : Finset V) : Set V) ∅ := by
  intro z hzPath hzDeleted
  rw [Finset.coe_union, Set.mem_union] at hzDeleted
  rcases hzDeleted with hzDeleted | hzBarrier
  · exact (reachingCandidateConnectionData i).avoids z hzPath (by
      exact Finset.mem_union_left _ hzDeleted)
  · change z ∈ reachingCandidateBarrier i at hzBarrier
    rw [reachingCandidateBarrier, Finset.mem_union] at hzBarrier
    rcases hzBarrier with hzCore | hzRootPath
    · apply (reachingCandidateConnectionData i).avoids z hzPath
      exact Finset.mem_union_right _ (by
        simpa [reachingCandidateCore,
          (reachingCandidateConnectionData i).core_eq] using hzCore)
    · rw [Finset.mem_erase, List.mem_toFinset] at hzRootPath
      have hzLeft := reachingCandidateRootPath_support_subset i z hzRootPath.2
      have hzeq :=
        (reachingCandidateConnectionData i).eq_start_of_mem_leftEnd_path
          hzLeft hzPath
      exact hzRootPath.1 hzeq

/-- The opposite seed avoids the common deletion together with `Bᵢ`. -/
theorem reachingCandidateSeed_disjoint_deleted_union_barrier
    [Fintype V]
    {deleted highDegree protectedSet target : Finset V}
    {separation connectionRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (i : {A // A ∈ reachingEligibleSubfamily S target connectionRadius}) :
    Disjoint (reachingCandidateSeed i)
      (deleted ∪ reachingCandidateBarrier i) := by
  rw [Finset.disjoint_left]
  intro z hzSeed hzDeleted
  rw [Finset.mem_union] at hzDeleted
  rcases hzDeleted with hzDeleted | hzBarrier
  · have hzVerts : z ∈ i.1.1.adjuster.verts := by
      rw [← (reachingCandidateConnectionData i).verts_eq]
      exact (reachingCandidateConnectionData i).adjusted.rightEnd_verts_subset
        hzSeed
    exact (Finset.disjoint_left.1 i.1.2.1 hzDeleted hzVerts).elim
  · rw [reachingCandidateBarrier, Finset.mem_union] at hzBarrier
    rcases hzBarrier with hzCore | hzRootPath
    · exact (Finset.disjoint_left.1
        (reachingCandidateConnectionData i).adjusted.core_disjoint_right
        (by simpa [reachingCandidateCore] using hzCore) hzSeed).elim
    · have hzLeft :
          z ∈ (reachingCandidateConnectionData i).adjusted.leftEnd.verts :=
        reachingCandidateRootPath_support_subset i z
          (List.mem_toFinset.1 (Finset.mem_erase.1 hzRootPath).2)
      exact (Finset.disjoint_left.1
        (reachingCandidateConnectionData i).adjusted.ends_disjoint
        hzLeft hzSeed).elim

/-- C3 in its exact source form, with `Bᵢ` containing the internal arm. -/
theorem reachingCandidate_limitedContact_barrier
    [Fintype V]
    {deleted highDegree protectedSet target : Finset V}
    {separation connectionRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (i : {A // A ∈ reachingEligibleSubfamily S target connectionRadius}) :
    HasLimitedContactAfterDeletion G (reachingCandidateSeed i)
      (deleted ∪ reachingCandidateBarrier i) (reachingCandidatePath i) 2 := by
  let P := reachingCandidateConnectionData i
  apply hasLimitedContactAfterDeletion_of_opposite_shortest_path
    G (reachingCandidateSeed i) target (deleted ∪ reachingCandidateBarrier i)
      (s := P.start) (t := P.finish) P.finish_mem P.path P.isPath
  · exact reachingCandidatePath_avoids_deleted_union_barrier i
  · exact reachingCandidateSeed_disjoint_deleted_union_barrier i
  · intro a ha t ht q hq hqAvoid
    apply P.opposite_shortest a ha t ht q hq
    intro z hzq hzOld
    apply hqAvoid z hzq
    rw [Finset.coe_union, Set.mem_union]
    rw [Finset.coe_union, Set.mem_union] at hzOld
    rcases hzOld with hzDeleted | hzCore
    · exact Or.inl hzDeleted
    · have hzCore' : z ∈ P.adjusted.core := by
        rw [P.core_eq]
        exact hzCore
      have hzBarrier : z ∈ reachingCandidateBarrier i := by
        exact Finset.mem_union_left _ (by
          change z ∈ reachingCandidateCore i
          exact hzCore')
      exact Or.inr hzBarrier

@[simp] theorem card_reachingCandidateSeed
    [Fintype V]
    {deleted highDegree protectedSet target : Finset V}
    {separation connectionRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (i : {A // A ∈ reachingEligibleSubfamily S target connectionRadius}) :
    (reachingCandidateSeed i).card = i.1.1.radius ^ 2 := by
  exact (reachingCandidateConnectionData i).adjusted.rightEnd.card_verts

theorem card_reachingCandidateCore_le
    [Fintype V]
    {deleted highDegree protectedSet target : Finset V}
    {separation connectionRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (i : {A // A ∈ reachingEligibleSubfamily S target connectionRadius}) :
    (reachingCandidateCore i).card ≤ 10 * i.1.1.radius := by
  change (reachingCandidateConnectionData i).adjusted.core.card ≤
    10 * i.1.1.radius
  simpa only [Nat.mul_one] using
    (reachingCandidateConnectionData i).adjusted.core_card_le

theorem card_reachingCandidateBarrier_le
    [Fintype V]
    {deleted highDegree protectedSet target : Finset V}
    {separation connectionRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (i : {A // A ∈ reachingEligibleSubfamily S target connectionRadius}) :
    (reachingCandidateBarrier i).card ≤ 11 * i.1.1.radius + 1 := by
  have hcore := card_reachingCandidateCore_le i
  have hrootSupport := List.toFinset_card_le
    (reachingCandidateRootPath i).support
  have hrootLength := reachingCandidateRootPath_length_le i
  have hunion := Finset.card_union_le (reachingCandidateCore i)
    ((reachingCandidateRootPath i).support.toFinset.erase
      (reachingCandidateConnectionData i).start)
  have herase : ((reachingCandidateRootPath i).support.toFinset.erase
      (reachingCandidateConnectionData i).start).card ≤
        (reachingCandidateRootPath i).support.toFinset.card :=
    Finset.card_le_card (Finset.erase_subset _ _)
  have hsupportLength :
      (reachingCandidateRootPath i).support.length =
        (reachingCandidateRootPath i).length + 1 :=
    (reachingCandidateRootPath i).length_support
  dsimp [reachingCandidateBarrier]
  omega

theorem card_reachingCandidatePath_le
    [Fintype V]
    {deleted highDegree protectedSet target : Finset V}
    {separation connectionRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (i : {A // A ∈ reachingEligibleSubfamily S target connectionRadius}) :
    (reachingCandidatePath i).card ≤ connectionRadius + 1 := by
  change (reachingCandidateConnectionData i).path.support.toFinset.card ≤
    connectionRadius + 1
  calc
    (reachingCandidateConnectionData i).path.support.toFinset.card ≤
        (reachingCandidateConnectionData i).path.support.length := by
      exact List.toFinset_card_le _
    _ = (reachingCandidateConnectionData i).path.length + 1 := by
      rw [(reachingCandidateConnectionData i).path.length_support]
    _ ≤ connectionRadius + 1 :=
      Nat.add_le_add_right (reachingCandidateConnectionData i).length_le 1

/-- Claim 4.5's geometric contradiction.

Once a shortest connection has reached one high-degree vertex, the opposite
end cannot reach a *different* high-degree vertex through the literal
`U,Bᵢ,Cᵢ` deletion.  Otherwise the two internal arms and the two connections
feed two fresh stars, producing the forbidden target adjuster.  Every
hypothesis after `hnoTarget` is a natural-number budget. -/
theorem no_second_highDegree_connection_of_no_targetAdjuster
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {deleted highDegree protectedSet targetSet : Finset V}
    {separation connectionRadius minRadius maxRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (i : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
    (targetOrder totalRadius Delta deletedCap : ℕ)
    (hTargetSet : targetSet ⊆ highDegree \ deleted)
    (hHighDegree : ∀ v ∈ highDegree, Delta ≤ G.degree v)
    (hnoTarget : ¬ ∃ A : Adjuster G targetOrder totalRadius 1,
      Disjoint deleted A.verts)
    (hTargetPos : 0 < targetOrder)
    (hDeletedCard : deleted.card ≤ deletedCap)
    (hRightBudget : targetOrder +
      (deletedCap + 10 * maxRadius + (maxRadius + 1) +
        (connectionRadius + 1)) ≤ Delta)
    (hLeftBudget : targetOrder +
      (deletedCap + 10 * maxRadius + targetOrder) ≤ Delta)
    (hRadius : maxRadius + connectionRadius + 1 ≤ totalRadius) :
    ¬ HasShortAvoidingConnection G
      (deleted ∪ reachingCandidateBarrier i ∪ reachingCandidatePath i)
      (reachingCandidateSeed i)
      (highDegree \ (deleted ∪ {(reachingCandidateConnectionData i).finish}))
      connectionRadius := by
  intro hsecond
  let P := reachingCandidateConnectionData i
  obtain ⟨b, hbSeed, y, hyHigh, pRight, hpRight, hpRightAvoid,
    hpRightLength⟩ := hsecond
  obtain ⟨qRight, hqRight, hqRightLength, hqRightSupport⟩ :=
    P.adjusted.rightEnd.exists_path hbSeed
  have hAdjustedDeleted : Disjoint deleted P.adjusted.verts := by
    rw [P.verts_eq]
    exact i.1.2.1
  have hqLeftAvoid : (reachingCandidateRootPath i).Avoids
      ((deleted ∪ P.adjusted.core : Finset V) : Set V) ∅ := by
    intro z hz hzForbidden
    change z ∈ deleted ∪ P.adjusted.core at hzForbidden
    rw [Finset.mem_union] at hzForbidden
    have hzLeft := reachingCandidateRootPath_support_subset i z hz
    rcases hzForbidden with hzDeleted | hzCore
    · exact (Finset.disjoint_left.1 hAdjustedDeleted hzDeleted
        (P.adjusted.leftEnd_verts_subset hzLeft)).elim
    · exact (Finset.disjoint_left.1 P.adjusted.core_disjoint_left
        hzCore hzLeft).elim
  have hpLeftAvoid : P.path.Avoids
      ((deleted ∪ P.adjusted.core : Finset V) : Set V) ∅ := by
    simpa [P.core_eq] using P.avoids
  let firstForbidden : Finset V :=
    deleted ∪ P.adjusted.core ∪
      (reachingCandidateRootPath i).support.toFinset ∪ P.path.support.toFinset
  have hqRightAvoid : qRight.Avoids (firstForbidden : Set V) ∅ := by
    intro z hz hzForbidden
    change z ∈ deleted ∪ P.adjusted.core ∪
      (reachingCandidateRootPath i).support.toFinset ∪
        P.path.support.toFinset at hzForbidden
    simp only [Finset.mem_union, List.mem_toFinset] at hzForbidden
    have hzRight := hqRightSupport z hz
    rcases hzForbidden with ((hzDeleted | hzCore) | hzLeft) | hzPath
    · exact (Finset.disjoint_left.1 hAdjustedDeleted hzDeleted
        (P.adjusted.rightEnd_verts_subset hzRight)).elim
    · exact (Finset.disjoint_left.1 P.adjusted.core_disjoint_right
        hzCore hzRight).elim
    · exact (Finset.disjoint_left.1 P.adjusted.ends_disjoint
        (reachingCandidateRootPath_support_subset i z hzLeft) hzRight).elim
    · exact (Finset.disjoint_left.1 P.opposite_disjoint_path
        hzRight (List.mem_toFinset.2 hzPath)).elim
  have hpRightAvoid' : pRight.Avoids (firstForbidden : Set V) ∅ := by
    intro z hz hzForbidden
    apply hpRightAvoid z hz
    change z ∈ deleted ∪ P.adjusted.core ∪
      (reachingCandidateRootPath i).support.toFinset ∪
        P.path.support.toFinset at hzForbidden
    change z ∈ deleted ∪ reachingCandidateBarrier i ∪ reachingCandidatePath i
    simp only [Finset.mem_union, List.mem_toFinset] at hzForbidden ⊢
    rcases hzForbidden with ((hzDeleted | hzCore) | hzRootPath) | hzPath
    · exact Or.inl (Or.inl hzDeleted)
    · exact Or.inl (Or.inr (Finset.mem_union_left _ (by
        change z ∈ reachingCandidateCore i
        exact hzCore)))
    · by_cases hzStart : z = P.start
      · subst z
        apply Or.inr
        change P.start ∈ P.path.support.toFinset
        exact List.mem_toFinset.2 P.path.start_mem_support
      · exact Or.inl (Or.inr (Finset.mem_union_right _ (by
          rw [Finset.mem_erase, List.mem_toFinset]
          exact ⟨hzStart, hzRootPath⟩)))
    · apply Or.inr
      change z ∈ P.path.support.toFinset
      exact List.mem_toFinset.2 hzPath
  have hcoreCard : P.adjusted.core.card ≤ 10 * maxRadius := by
    have hcore := P.adjusted.core_card_le
    have hradius := i.1.1.le_max
    nlinarith
  have hqLeftCard :
      (reachingCandidateRootPath i).support.toFinset.card ≤ maxRadius + 1 := by
    have hcard := List.toFinset_card_le (reachingCandidateRootPath i).support
    have hlen := reachingCandidateRootPath_length_le i
    have hradius := i.1.1.le_max
    rw [(reachingCandidateRootPath i).length_support] at hcard
    omega
  have hpLeftCard : P.path.support.toFinset.card ≤ connectionRadius + 1 := by
    simpa [P, reachingCandidatePath] using card_reachingCandidatePath_le i
  have hfirstCard : firstForbidden.card ≤
      deletedCap + 10 * maxRadius + (maxRadius + 1) +
        (connectionRadius + 1) := by
    have h₁ := Finset.card_union_le deleted P.adjusted.core
    have h₂ := Finset.card_union_le (deleted ∪ P.adjusted.core)
      (reachingCandidateRootPath i).support.toFinset
    have h₃ := Finset.card_union_le
      (deleted ∪ P.adjusted.core ∪
        (reachingCandidateRootPath i).support.toFinset) P.path.support.toFinset
    dsimp [firstForbidden]
    omega
  have hyDegree : targetOrder + firstForbidden.card ≤ G.degree y := by
    have hy : y ∈ highDegree := (Finset.mem_sdiff.1 hyHigh).1
    exact (Nat.add_le_add_left hfirstCard targetOrder).trans
      (hRightBudget.trans (hHighDegree y hy))
  have htHigh : P.finish ∈ highDegree :=
    (Finset.mem_sdiff.1 (hTargetSet P.finish_mem)).1
  have htDegree : targetOrder +
      (deleted.card + P.adjusted.core.card + targetOrder) ≤ G.degree P.finish := by
    have hbound : deleted.card + P.adjusted.core.card + targetOrder ≤
        deletedCap + 10 * maxRadius + targetOrder := by omega
    exact (Nat.add_le_add_left hbound targetOrder).trans
      (hLeftBudget.trans (hHighDegree P.finish htHigh))
  have holdRadius : i.1.1.radius ≤ totalRadius :=
    i.1.1.le_max.trans (by omega)
  obtain ⟨A', hA'core, hA'deleted⟩ :=
    P.adjusted.exists_replaceEnds_byTwoPathStars G deleted hAdjustedDeleted
      (reachingCandidateRootPath i) P.path qRight pRight
      (reachingCandidateRootPath_length_le i) P.length_le hqRightLength
      hpRightLength ⟨hqLeftAvoid, hpLeftAvoid⟩
      ⟨hqRightAvoid, hpRightAvoid'⟩ hTargetPos hyDegree htDegree
      (by have := i.1.1.le_max; omega) holdRadius
  exact hnoTarget ⟨A', hA'deleted⟩

/-- A large opposite-end ball plus the already chosen high-degree connection
constructs the forbidden target adjuster.  This is the deterministic final
step of Claim 4.5 after correlated Lemma 3.7 chooses its index. -/
theorem exists_targetAdjuster_of_large_reachingCandidate_ball
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {deleted highDegree protectedSet targetSet : Finset V}
    {separation connectionRadius ballRadius minRadius maxRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (i : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
    (targetOrder totalRadius Delta deletedCap : ℕ)
    (hTargetSet : targetSet ⊆ highDegree \ deleted)
    (hHighDegree : ∀ v ∈ highDegree, Delta ≤ G.degree v)
    (hballCard : targetOrder ≤ (ballAvoidingFrom G
      ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
        (reachingCandidatePath i : Set V))
      (reachingCandidateSeed i) ballRadius).card)
    (hTargetPos : 0 < targetOrder)
    (hDeletedCard : deleted.card ≤ deletedCap)
    (hDegreeBudget : targetOrder +
      (deletedCap + 10 * maxRadius + targetOrder) ≤ Delta)
    (hLeftRadius : maxRadius + connectionRadius + 1 ≤ totalRadius)
    (hRightRadius : maxRadius + ballRadius ≤ totalRadius) :
    ∃ A : Adjuster G targetOrder totalRadius 1, Disjoint deleted A.verts := by
  let P := reachingCandidateConnectionData i
  let W : Finset V :=
    deleted ∪ reachingCandidateBarrier i ∪ reachingCandidatePath i
  let ball : Finset V := ballAvoidingFrom G (W : Set V)
    (reachingCandidateSeed i) ballRadius
  have hseedW : Disjoint (reachingCandidateSeed i) W := by
    rw [Finset.disjoint_left]
    intro z hzSeed hzW
    change z ∈ deleted ∪ reachingCandidateBarrier i ∪
      reachingCandidatePath i at hzW
    simp only [Finset.mem_union] at hzW
    rcases hzW with (hzDeleted | hzBarrier) | hzPath
    · exact (Finset.disjoint_left.1
        (reachingCandidateSeed_disjoint_deleted_union_barrier i) hzSeed
        (Finset.mem_union_left _ hzDeleted)).elim
    · exact (Finset.disjoint_left.1
        (reachingCandidateSeed_disjoint_deleted_union_barrier i) hzSeed
        (Finset.mem_union_right _ hzBarrier)).elim
    · exact (Finset.disjoint_left.1 P.opposite_disjoint_path hzSeed
        (by change z ∈ P.path.support.toFinset; exact hzPath)).elim
  have hballW : Disjoint ball W := by
    exact disjoint_ballAvoidingFrom_forbidden G
      (reachingCandidateSeed i) W ballRadius hseedW
  let rightFull := P.adjusted.rightEnd.ofBallAvoidingFrom (W : Set V) ballRadius
  obtain ⟨rightSmall, hrightSmall⟩ := rightFull.proposition3_10 hTargetPos (by
    change targetOrder ≤
      (ballAvoidingFrom G (W : Set V) P.adjusted.rightEnd.verts ballRadius).card
    simpa only [W, Finset.coe_union, reachingCandidateSeed] using hballCard)
  let right : VertexExpansion G P.adjusted.rightRoot targetOrder totalRadius :=
    rightSmall.radiusMono (by
      exact (Nat.add_le_add_right i.1.1.le_max ballRadius).trans hRightRadius)
  have hrightBall : right.verts ⊆ ball := by
    change rightSmall.verts ⊆ ball
    have hrightSmall' := hrightSmall
    change rightSmall.verts ⊆
      ballAvoidingFrom G (W : Set V) P.adjusted.rightEnd.verts ballRadius at hrightSmall'
    simpa only [ball, P, reachingCandidateSeed] using hrightSmall'
  let leftForbidden : Finset V := deleted ∪ P.adjusted.core ∪ right.verts
  have hleftForbiddenCard : leftForbidden.card ≤
      deletedCap + 10 * maxRadius + targetOrder := by
    have hcore := P.adjusted.core_card_le
    have hradius := i.1.1.le_max
    have h₁ := Finset.card_union_le deleted P.adjusted.core
    have h₂ := Finset.card_union_le (deleted ∪ P.adjusted.core) right.verts
    rw [right.card_verts] at h₂
    dsimp [leftForbidden]
    nlinarith
  have hqSubsetW : ∀ z ∈ (reachingCandidateRootPath i).support, z ∈ W := by
    intro z hz
    change z ∈ deleted ∪ reachingCandidateBarrier i ∪ reachingCandidatePath i
    by_cases hzStart : z = P.start
    · subst z
      exact Finset.mem_union_right _ (by
        change P.start ∈ P.path.support.toFinset
        exact List.mem_toFinset.2 P.path.start_mem_support)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by
        rw [reachingCandidateBarrier, Finset.mem_union]
        exact Or.inr (by
          rw [Finset.mem_erase, List.mem_toFinset]
          exact ⟨hzStart, hz⟩)))
  have hqAvoid : (reachingCandidateRootPath i).Avoids
      (leftForbidden : Set V) ∅ := by
    intro z hz hzForbidden
    change z ∈ deleted ∪ P.adjusted.core ∪ right.verts at hzForbidden
    simp only [Finset.mem_union] at hzForbidden
    rcases hzForbidden with (hzDeleted | hzCore) | hzRight
    · have hzLeft := reachingCandidateRootPath_support_subset i z hz
      have hzVerts := P.adjusted.leftEnd_verts_subset hzLeft
      have hdeleted : Disjoint deleted P.adjusted.verts := by
        rw [P.verts_eq]
        exact i.1.2.1
      exact (Finset.disjoint_left.1 hdeleted hzDeleted hzVerts).elim
    · exact (Finset.disjoint_left.1 P.adjusted.core_disjoint_left hzCore
        (reachingCandidateRootPath_support_subset i z hz)).elim
    · exact (Finset.disjoint_left.1 hballW (hrightBall hzRight)
        (hqSubsetW z hz)).elim
  have hpAvoid : P.path.Avoids (leftForbidden : Set V) ∅ := by
    intro z hz hzForbidden
    change z ∈ deleted ∪ P.adjusted.core ∪ right.verts at hzForbidden
    simp only [Finset.mem_union] at hzForbidden
    rcases hzForbidden with (hzDeleted | hzCore) | hzRight
    · exact P.avoids z hz (Finset.mem_union_left _ hzDeleted)
    · exact P.avoids z hz (Finset.mem_union_right _ (by
        rw [← P.core_eq]
        exact hzCore))
    · exact (Finset.disjoint_left.1 hballW (hrightBall hzRight) (by
        change z ∈ W
        exact Finset.mem_union_right _ (by
          change z ∈ P.path.support.toFinset
          exact List.mem_toFinset.2 hz))).elim
  have hfinishHigh : P.finish ∈ highDegree :=
    (Finset.mem_sdiff.1 (hTargetSet P.finish_mem)).1
  have hfinishDegree : targetOrder + leftForbidden.card ≤ G.degree P.finish :=
    (Nat.add_le_add_left hleftForbiddenCard targetOrder).trans
      (hDegreeBudget.trans (hHighDegree P.finish hfinishHigh))
  obtain ⟨left, hleft⟩ := exists_expansion_of_two_paths_star_disjoint
    G (reachingCandidateRootPath i) P.path
      (reachingCandidateRootPath_length_le i) P.length_le leftForbidden
      hqAvoid hpAvoid hTargetPos hfinishDegree (by
        exact (Nat.add_le_add_right
          (Nat.add_le_add_right i.1.1.le_max connectionRadius) 1).trans
            hLeftRadius)
  have hcoreLeft : Disjoint P.adjusted.core left.verts := by
    apply (hleft.mono_right ?_).symm
    intro z hzCore
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hzCore)
  have hcoreRight : Disjoint P.adjusted.core right.verts := by
    apply (hballW.mono hrightBall ?_).symm
    intro z hzCore
    change z ∈ W
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (by
      exact Finset.mem_union_left _ hzCore))
  have hends : Disjoint left.verts right.verts := by
    apply hleft.mono_right
    intro z hzRight
    exact Finset.mem_union_right _ hzRight
  let A' : Adjuster G targetOrder totalRadius 1 :=
    P.adjusted.replaceEnds left right hcoreLeft hcoreRight hends (by
      exact i.1.1.le_max.trans (by omega))
  refine ⟨A', ?_⟩
  rw [Finset.disjoint_left]
  intro z hzDeleted hzA'
  change z ∈ left.verts ∪ right.verts ∪ P.adjusted.core at hzA'
  simp only [Finset.mem_union] at hzA'
  rcases hzA' with (hzLeft | hzRight) | hzCore
  · exact (Finset.disjoint_left.1 hleft hzLeft (by
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hzDeleted))).elim
  · exact (Finset.disjoint_left.1 hballW (hrightBall hzRight) (by
      change z ∈ W
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hzDeleted))).elim
  · have hdeleted : Disjoint deleted P.adjusted.verts := by
      rw [P.verts_eq]
      exact i.1.2.1
    exact (Finset.disjoint_left.1 hdeleted hzDeleted
      (P.adjusted.core_subset_verts hzCore)).elim

/-- Claim 4.6 endpoint replacement.

The opposite end is enlarged inside the correlated avoiding ball.  The
oriented shortest connection from the first end terminates in the concrete
auxiliary expansion `Z`; attaching `Z` after the internal root arm and that
connection gives the other end.  Thus both ends are constructed explicitly,
and the old simple-adjuster core is retained. -/
theorem exists_targetAdjuster_of_large_reachingCandidate_ball_expansion
    [Fintype V]
    {deleted highDegree protectedSet targetSet : Finset V}
    {separation connectionRadius ballRadius minRadius maxRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (i : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
    (targetOrder totalRadius farRadius : ℕ)
    {center : V} (Z : VertexExpansion G center targetOrder farRadius)
    (hfinishZ : (reachingCandidateConnectionData i).finish ∈ Z.verts)
    (hballCard : targetOrder ≤ (ballAvoidingFrom G
      ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
        (reachingCandidatePath i : Set V))
      (reachingCandidateSeed i) ballRadius).card)
    (hZWorkspace : Disjoint Z.verts
      (deleted ∪ (reachingCandidateConnectionData i).adjusted.core ∪
        ballAvoidingFrom G
          ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius))
    (hTargetPos : 0 < targetOrder)
    (hLeftRadius : maxRadius + connectionRadius + 2 * farRadius ≤ totalRadius)
    (hRightRadius : maxRadius + ballRadius ≤ totalRadius) :
    ∃ A : Adjuster G targetOrder totalRadius 1, Disjoint deleted A.verts := by
  let P := reachingCandidateConnectionData i
  let W : Finset V :=
    deleted ∪ reachingCandidateBarrier i ∪ reachingCandidatePath i
  let ball : Finset V := ballAvoidingFrom G (W : Set V)
    (reachingCandidateSeed i) ballRadius
  have hseedW : Disjoint (reachingCandidateSeed i) W := by
    rw [Finset.disjoint_left]
    intro z hzSeed hzW
    change z ∈ deleted ∪ reachingCandidateBarrier i ∪
      reachingCandidatePath i at hzW
    simp only [Finset.mem_union] at hzW
    rcases hzW with (hzDeleted | hzBarrier) | hzPath
    · exact (Finset.disjoint_left.1
        (reachingCandidateSeed_disjoint_deleted_union_barrier i) hzSeed
        (Finset.mem_union_left _ hzDeleted)).elim
    · exact (Finset.disjoint_left.1
        (reachingCandidateSeed_disjoint_deleted_union_barrier i) hzSeed
        (Finset.mem_union_right _ hzBarrier)).elim
    · exact (Finset.disjoint_left.1 P.opposite_disjoint_path hzSeed (by
        change z ∈ P.path.support.toFinset
        exact hzPath)).elim
  have hballW : Disjoint ball W :=
    disjoint_ballAvoidingFrom_forbidden G
      (reachingCandidateSeed i) W ballRadius hseedW
  let rightFull := P.adjusted.rightEnd.ofBallAvoidingFrom (W : Set V) ballRadius
  obtain ⟨rightSmall, hrightSmall⟩ := rightFull.proposition3_10 hTargetPos (by
    change targetOrder ≤
      (ballAvoidingFrom G (W : Set V) P.adjusted.rightEnd.verts ballRadius).card
    simpa only [W, Finset.coe_union, reachingCandidateSeed] using hballCard)
  let right : VertexExpansion G P.adjusted.rightRoot targetOrder totalRadius :=
    rightSmall.radiusMono
      ((Nat.add_le_add_right i.1.1.le_max ballRadius).trans hRightRadius)
  have hrightBall : right.verts ⊆ ball := by
    change rightSmall.verts ⊆ ball
    have hrightSmall' := hrightSmall
    change rightSmall.verts ⊆
      ballAvoidingFrom G (W : Set V) P.adjusted.rightEnd.verts ballRadius at hrightSmall'
    simpa only [ball, P, reachingCandidateSeed] using hrightSmall'
  let leftForbidden : Finset V := deleted ∪ P.adjusted.core ∪ right.verts
  have hqSubsetW : ∀ z ∈ (reachingCandidateRootPath i).support, z ∈ W := by
    intro z hz
    change z ∈ deleted ∪ reachingCandidateBarrier i ∪ reachingCandidatePath i
    by_cases hzStart : z = P.start
    · subst z
      exact Finset.mem_union_right _ (by
        change P.start ∈ P.path.support.toFinset
        exact List.mem_toFinset.2 P.path.start_mem_support)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by
        rw [reachingCandidateBarrier, Finset.mem_union]
        exact Or.inr (by
          rw [Finset.mem_erase, List.mem_toFinset]
          exact ⟨hzStart, hz⟩)))
  have hqAvoid : (reachingCandidateRootPath i).Avoids
      (leftForbidden : Set V) ∅ := by
    intro z hz hzForbidden
    change z ∈ deleted ∪ P.adjusted.core ∪ right.verts at hzForbidden
    simp only [Finset.mem_union] at hzForbidden
    rcases hzForbidden with (hzDeleted | hzCore) | hzRight
    · have hzLeft := reachingCandidateRootPath_support_subset i z hz
      have hzVerts := P.adjusted.leftEnd_verts_subset hzLeft
      have hdeleted : Disjoint deleted P.adjusted.verts := by
        rw [P.verts_eq]
        exact i.1.2.1
      exact (Finset.disjoint_left.1 hdeleted hzDeleted hzVerts).elim
    · exact (Finset.disjoint_left.1 P.adjusted.core_disjoint_left hzCore
        (reachingCandidateRootPath_support_subset i z hz)).elim
    · exact (Finset.disjoint_left.1 hballW (hrightBall hzRight)
        (hqSubsetW z hz)).elim
  have hpAvoid : P.path.Avoids (leftForbidden : Set V) ∅ := by
    intro z hz hzForbidden
    change z ∈ deleted ∪ P.adjusted.core ∪ right.verts at hzForbidden
    simp only [Finset.mem_union] at hzForbidden
    rcases hzForbidden with (hzDeleted | hzCore) | hzRight
    · exact P.avoids z hz (Finset.mem_union_left _ hzDeleted)
    · exact P.avoids z hz (Finset.mem_union_right _ (by
        rw [← P.core_eq]
        exact hzCore))
    · exact (Finset.disjoint_left.1 hballW (hrightBall hzRight) (by
        change z ∈ W
        exact Finset.mem_union_right _ (by
          change z ∈ P.path.support.toFinset
          exact List.mem_toFinset.2 hz))).elim
  have hZLeftForbidden : Disjoint Z.verts leftForbidden := by
    apply hZWorkspace.mono_right
    intro z hz
    change z ∈ deleted ∪ P.adjusted.core ∪ right.verts at hz
    simp only [Finset.mem_union] at hz ⊢
    rcases hz with (hzDeleted | hzCore) | hzRight
    · exact Or.inl (Or.inl hzDeleted)
    · exact Or.inl (Or.inr hzCore)
    · exact Or.inr (by
        simpa only [ball, W, Finset.coe_union] using hrightBall hzRight)
  obtain ⟨left, hleft⟩ := exists_expansion_of_two_paths_expansion_disjoint
    (reachingCandidateRootPath i) P.path
      (reachingCandidateRootPath_length_le i) P.length_le Z hfinishZ
      leftForbidden hqAvoid hpAvoid hZLeftForbidden
      ((Nat.add_le_add_right
        (Nat.add_le_add_right i.1.1.le_max connectionRadius)
        (2 * farRadius)).trans hLeftRadius)
  have hcoreLeft : Disjoint P.adjusted.core left.verts := by
    apply (hleft.mono_right ?_).symm
    intro z hzCore
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hzCore)
  have hcoreRight : Disjoint P.adjusted.core right.verts := by
    apply (hballW.mono hrightBall ?_).symm
    intro z hzCore
    change z ∈ W
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_union_left _ hzCore))
  have hends : Disjoint left.verts right.verts := by
    apply hleft.mono_right
    intro z hzRight
    exact Finset.mem_union_right _ hzRight
  let A' : Adjuster G targetOrder totalRadius 1 :=
    P.adjusted.replaceEnds left right hcoreLeft hcoreRight hends
      (i.1.1.le_max.trans (by omega))
  refine ⟨A', ?_⟩
  rw [Finset.disjoint_left]
  intro z hzDeleted hzA'
  change z ∈ left.verts ∪ right.verts ∪ P.adjusted.core at hzA'
  simp only [Finset.mem_union] at hzA'
  rcases hzA' with (hzLeft | hzRight) | hzCore
  · exact (Finset.disjoint_left.1 hleft hzLeft
      (Finset.mem_union_left _ (Finset.mem_union_left _ hzDeleted))).elim
  · exact (Finset.disjoint_left.1 hballW (hrightBall hzRight) (by
      change z ∈ W
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hzDeleted))).elim
  · have hdeleted : Disjoint deleted P.adjusted.verts := by
      rw [P.verts_eq]
      exact i.1.2.1
    exact (Finset.disjoint_left.1 hdeleted hzDeleted
      (P.adjusted.core_subset_verts hzCore)).elim

/-- The absence of a second high-degree route identifies the actual
`G-U-Bᵢ-Cᵢ` ball with the corresponding ball in `G-L-U-Bᵢ-Cᵢ`.  The one
high-degree vertex already reached by the chosen path belongs to `Cᵢ`, so an
avoiding path cannot end there. -/
theorem reachingCandidate_ball_eq_highDegree_of_no_second
    [Fintype V]
    {deleted highDegree protectedSet targetSet : Finset V}
    {separation connectionRadius ballRadius minRadius maxRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (i : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
    (hfinishHigh : (reachingCandidateConnectionData i).finish ∈ highDegree)
    (hnoSecond : ¬ HasShortAvoidingConnection G
      (deleted ∪ reachingCandidateBarrier i ∪ reachingCandidatePath i)
      (reachingCandidateSeed i)
      (highDegree \ (deleted ∪ {(reachingCandidateConnectionData i).finish}))
      ballRadius) :
    ballAvoidingFrom G
        ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
          (reachingCandidatePath i : Set V))
        (reachingCandidateSeed i) ballRadius =
      ballAvoidingFrom G
        ((deleted : Set V) ∪ (highDegree : Set V) ∪
          (reachingCandidateBarrier i : Set V) ∪
          (reachingCandidatePath i : Set V))
        (reachingCandidateSeed i) ballRadius := by
  let X : Finset V :=
    deleted ∪ reachingCandidateBarrier i ∪ reachingCandidatePath i
  have hseedX : Disjoint (reachingCandidateSeed i) X := by
    rw [Finset.disjoint_left]
    intro z hzSeed hzX
    change z ∈ deleted ∪ reachingCandidateBarrier i ∪
      reachingCandidatePath i at hzX
    simp only [Finset.mem_union] at hzX
    rcases hzX with (hzDeleted | hzBarrier) | hzPath
    · exact (Finset.disjoint_left.1
        (reachingCandidateSeed_disjoint_deleted_union_barrier i)
        hzSeed (Finset.mem_union_left _ hzDeleted)).elim
    · exact (Finset.disjoint_left.1
        (reachingCandidateSeed_disjoint_deleted_union_barrier i)
        hzSeed (Finset.mem_union_right _ hzBarrier)).elim
    · exact (Finset.disjoint_left.1
        (reachingCandidateConnectionData i).opposite_disjoint_path
        hzSeed (by
          change z ∈ (reachingCandidateConnectionData i).path.support.toFinset
          exact hzPath)).elim
  have hfar : ¬ HasShortAvoidingConnection G X
      (reachingCandidateSeed i) highDegree ballRadius := by
    intro h
    apply hnoSecond
    obtain ⟨a, ha, y, hyHigh, p, hp, hpAvoid, hpLength⟩ := h
    have hyDeleted : y ∉ deleted := by
      intro hy
      apply hpAvoid y p.end_mem_support
      change y ∈ X
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hy)
    have hyFinish : y ≠ (reachingCandidateConnectionData i).finish := by
      intro hy
      subst y
      apply hpAvoid (reachingCandidateConnectionData i).finish p.end_mem_support
      change (reachingCandidateConnectionData i).finish ∈ X
      exact Finset.mem_union_right _ (by
        simp [reachingCandidatePath])
    exact ⟨a, ha, y,
      Finset.mem_sdiff.2 ⟨hyHigh, by
        simp [hyDeleted, hyFinish]⟩,
      p, hp, hpAvoid, hpLength⟩
  have heq := ballAvoidingFrom_union_eq_of_no_shortAvoidingConnection
    G X highDegree (reachingCandidateSeed i) ballRadius hseedX hfar
  calc
    ballAvoidingFrom G
        ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
          (reachingCandidatePath i : Set V))
        (reachingCandidateSeed i) ballRadius =
      ballAvoidingFrom G (X : Set V) (reachingCandidateSeed i) ballRadius := by
        congr 2
        ext z
        simp only [X, Finset.coe_union, Set.mem_union, Finset.mem_coe]
    _ = ballAvoidingFrom G ((X : Set V) ∪ (highDegree : Set V))
        (reachingCandidateSeed i) ballRadius := heq.symm
    _ = ballAvoidingFrom G
        ((deleted : Set V) ∪ (highDegree : Set V) ∪
          (reachingCandidateBarrier i : Set V) ∪
          (reachingCandidatePath i : Set V))
        (reachingCandidateSeed i) ballRadius := by
          apply congrArg (fun W : Set V ↦
            ballAvoidingFrom G W (reachingCandidateSeed i) ballRadius)
          ext z
          simp only [X, Finset.coe_union, Set.mem_union, Finset.mem_coe]
          tauto

/-- Claim 4.6 uses candidates already known not to have a short route from
either end to `L \ U`.  For such a candidate, adding the whole high-degree
set to the forbidden set does not change the opposite-end avoiding ball.
This is the exact pointwise identity needed before the second application of
correlated Lemma 3.7. -/
theorem reachingCandidate_ball_eq_highDegree_of_no_highConnection
    [Fintype V]
    {deleted highDegree protectedSet targetSet : Finset V}
    {separation connectionRadius ballRadius highRadius minRadius maxRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (i : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
    (hnoHigh : ¬ i.1.1.ReachesAvoidingOwnCore deleted
      (highDegree \ deleted) highRadius)
    (hballRadius : ballRadius ≤ highRadius) :
    ballAvoidingFrom G
        ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
          (reachingCandidatePath i : Set V))
        (reachingCandidateSeed i) ballRadius =
      ballAvoidingFrom G
        ((deleted : Set V) ∪ (highDegree : Set V) ∪
          (reachingCandidateBarrier i : Set V) ∪
          (reachingCandidatePath i : Set V))
        (reachingCandidateSeed i) ballRadius := by
  let P := reachingCandidateConnectionData i
  let X : Finset V :=
    deleted ∪ reachingCandidateBarrier i ∪ reachingCandidatePath i
  have hseedX : Disjoint (reachingCandidateSeed i) X := by
    rw [Finset.disjoint_left]
    intro z hzSeed hzX
    change z ∈ deleted ∪ reachingCandidateBarrier i ∪
      reachingCandidatePath i at hzX
    simp only [Finset.mem_union] at hzX
    rcases hzX with (hzDeleted | hzBarrier) | hzPath
    · exact (Finset.disjoint_left.1
        (reachingCandidateSeed_disjoint_deleted_union_barrier i)
        hzSeed (Finset.mem_union_left _ hzDeleted)).elim
    · exact (Finset.disjoint_left.1
        (reachingCandidateSeed_disjoint_deleted_union_barrier i)
        hzSeed (Finset.mem_union_right _ hzBarrier)).elim
    · exact (Finset.disjoint_left.1 P.opposite_disjoint_path hzSeed (by
        change z ∈ P.path.support.toFinset
        exact hzPath)).elim
  have hfar : ¬ HasShortAvoidingConnection G X
      (reachingCandidateSeed i) highDegree ballRadius := by
    intro h
    apply hnoHigh
    obtain ⟨a, haSeed, y, hyHigh, p, hp, hpAvoid, hpLength⟩ := h
    have hyDeleted : y ∉ deleted := by
      intro hyDeleted
      exact hpAvoid y p.end_mem_support (by
        change y ∈ X
        exact Finset.mem_union_left _ (Finset.mem_union_left _ hyDeleted))
    refine ⟨a, reachingCandidateSeed_subset_ends i haSeed, y,
      Finset.mem_sdiff.2 ⟨hyHigh, hyDeleted⟩, p, hp, ?_,
      hpLength.trans hballRadius⟩
    intro z hz hzForbidden
    apply hpAvoid z hz
    change z ∈ X
    change z ∈ deleted ∪ i.1.1.adjuster.core at hzForbidden
    rw [Finset.mem_union] at hzForbidden
    rcases hzForbidden with hzDeleted | hzCore
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hzDeleted)
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      change z ∈ reachingCandidateBarrier i
      apply Finset.mem_union_left
      change z ∈ reachingCandidateCore i
      rw [reachingCandidateCore, P.core_eq]
      exact hzCore
  have heq := ballAvoidingFrom_union_eq_of_no_shortAvoidingConnection
    G X highDegree (reachingCandidateSeed i) ballRadius hseedX hfar
  calc
    ballAvoidingFrom G
        ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
          (reachingCandidatePath i : Set V))
        (reachingCandidateSeed i) ballRadius =
      ballAvoidingFrom G (X : Set V) (reachingCandidateSeed i) ballRadius := by
        apply congrArg (fun W : Set V ↦
          ballAvoidingFrom G W (reachingCandidateSeed i) ballRadius)
        ext z
        simp only [X, Finset.coe_union, Set.mem_union, Finset.mem_coe]
    _ = ballAvoidingFrom G ((X : Set V) ∪ (highDegree : Set V))
        (reachingCandidateSeed i) ballRadius := heq.symm
    _ = ballAvoidingFrom G
        ((deleted : Set V) ∪ (highDegree : Set V) ∪
          (reachingCandidateBarrier i : Set V) ∪
          (reachingCandidatePath i : Set V))
        (reachingCandidateSeed i) ballRadius := by
          apply congrArg (fun W : Set V ↦
            ballAvoidingFrom G W (reachingCandidateSeed i) ballRadius)
          ext z
          simp only [X, Finset.coe_union, Set.mem_union, Finset.mem_coe]
          tauto

/-- G1 forces every `G-(U∪L∪Bᵢ∪Cᵢ)` ball of admissible radius to avoid
the protected exceptional set `U₁`.  This is the geometric half of C4. -/
theorem reachingCandidate_high_ball_disjoint_protected
    [Fintype V]
    {deleted highDegree protectedSet targetSet : Finset V}
    {separation connectionRadius ballRadius minRadius maxRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (i : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
    (hradius : ballRadius ≤ separation) :
    Disjoint
      (ballAvoidingFrom G
        ((deleted : Set V) ∪ (highDegree : Set V) ∪
          (reachingCandidateBarrier i : Set V) ∪
          (reachingCandidatePath i : Set V))
        (reachingCandidateSeed i) ballRadius)
      protectedSet := by
  rw [Finset.disjoint_left]
  intro y hyBall hyProtected
  by_cases hyHigh : y ∈ highDegree
  · have hseedHigh : Disjoint (reachingCandidateSeed i) highDegree := by
      exact i.1.2.2.1.mono_left (reachingCandidateSeed_subset_ends i)
    exact ballAvoidingFrom_avoids_forbidden G
      ((deleted : Set V) ∪ (highDegree : Set V) ∪
        (reachingCandidateBarrier i : Set V) ∪
        (reachingCandidatePath i : Set V))
      (reachingCandidateSeed i) ballRadius
      (fun a ha haForbidden ↦ by
        rw [Set.mem_union, Set.mem_union, Set.mem_union] at haForbidden
        rcases haForbidden with ((haDeleted | haHigh) | haBarrier) | haPath
        · exact (Finset.disjoint_left.1
            (reachingCandidateSeed_disjoint_deleted_union_barrier i) ha
            (Finset.mem_union_left _ haDeleted)).elim
        · exact (Finset.disjoint_left.1 hseedHigh ha haHigh).elim
        · exact (Finset.disjoint_left.1
            (reachingCandidateSeed_disjoint_deleted_union_barrier i) ha
            (Finset.mem_union_right _ haBarrier)).elim
        · exact (Finset.disjoint_left.1
            (reachingCandidateConnectionData i).opposite_disjoint_path ha
            (by
              change a ∈ (reachingCandidateConnectionData i).path.support.toFinset
              exact haPath)).elim)
      y hyBall (by exact Or.inl (Or.inl (Or.inr hyHigh)))
  · apply i.1.2.2.2
    obtain ⟨a, haSeed, p, hp, hpLength⟩ :=
      (mem_ballAvoidingFrom G
        ((deleted : Set V) ∪ (highDegree : Set V) ∪
          (reachingCandidateBarrier i : Set V) ∪
          (reachingCandidatePath i : Set V))
        (reachingCandidateSeed i) ballRadius y).1 hyBall
    have haEnds : a ∈ i.1.1.ends := reachingCandidateSeed_subset_ends i haSeed
    have haHigh : a ∉ highDegree := by
      intro haHigh
      exact (Finset.disjoint_left.1 i.1.2.2.1 haEnds haHigh).elim
    have hpHigh : p.Avoids (highDegree : Set V) ∅ := by
      intro z hz hzHigh
      have hza := hp.2 z hz (Or.inl (Or.inl (Or.inr hzHigh)))
      have hzaEq : z = a := by simpa using hza
      exact haHigh (hzaEq ▸ hzHigh)
    exact ⟨a, haEnds, y, Finset.mem_sdiff.2 ⟨hyProtected, hyHigh⟩,
      p, hp.1, hpHigh, hpLength.trans hradius⟩

/-- C4 in the exact form consumed by correlated Lemma 3.7.  The protected
set contains both `U` and the vertices with too many neighbors in `U`; G1
and the pointwise ball identity therefore bound every degree into `U`. -/
theorem reachingCandidate_degreeInto_deleted_le
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {deleted highDegree protectedSet targetSet : Finset V}
    {separation connectionRadius ballRadius minRadius maxRadius degreeInto : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (i : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
    (hradius : ballRadius ≤ separation)
    (hprotected : deleted ∪ manyNeighborsInto G deleted degreeInto ⊆
      protectedSet)
    (hball :
      ballAvoidingFrom G
          ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius =
        ballAvoidingFrom G
          ((deleted : Set V) ∪ (highDegree : Set V) ∪
            (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius) :
    ∀ v ∈ ballAvoidingFrom G
      ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
        (reachingCandidatePath i : Set V))
      (reachingCandidateSeed i) ballRadius,
      (G.neighborFinset v ∩ deleted).card ≤ degreeInto := by
  let actual := ballAvoidingFrom G
    ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
      (reachingCandidatePath i : Set V))
    (reachingCandidateSeed i) ballRadius
  have hactualProtected : Disjoint actual protectedSet := by
    dsimp [actual]
    rw [hball]
    exact reachingCandidate_high_ball_disjoint_protected i hradius
  have hactualDeleted : Disjoint actual deleted :=
    hactualProtected.mono_right (Finset.Subset.trans
      Finset.subset_union_left hprotected)
  have hactualExceptional :
      Disjoint actual (manyNeighborsInto G deleted degreeInto) :=
    hactualProtected.mono_right (Finset.Subset.trans
      Finset.subset_union_right hprotected)
  have hdegree := neighborsInto_le_of_disjoint_manyNeighborsInto
    G deleted actual degreeInto hactualDeleted hactualExceptional
  intro v hv
  have hinter : G.neighborFinset v ∩ deleted =
      deleted.filter fun w ↦ G.Adj v w := by
    ext w
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      Finset.mem_filter]
    constructor
    · rintro ⟨hvw, hw⟩
      exact ⟨hw, hvw⟩
    · rintro ⟨hw, hvw⟩
      exact ⟨hvw, hw⟩
  rw [hinter]
  exact hdegree v hv

/-- Two eligible candidates conflict if they have the same key root or if
their ends are too close in the graph after avoiding the high-degree set. -/
def Conflict (A B : SmallSimpleAdjusterCandidate G minRadius maxRadius)
    (highDegree : Finset V) (separation : ℕ) : Prop :=
  A.adjuster.leftRoot = B.adjuster.leftRoot ∨
    HasShortAvoidingConnection G highDegree A.ends B.ends separation

theorem Conflict.symm
    {A B : SmallSimpleAdjusterCandidate G minRadius maxRadius}
    {highDegree : Finset V} {separation : ℕ}
    (h : Conflict A B highDegree separation) :
    Conflict B A highDegree separation := by
  rcases h with hroot | hpath
  · exact Or.inl hroot.symm
  · exact Or.inr hpath.symm

/-- Purely numerical data for Claim 4.4.

The extracted expander may have any order `n'` between the retained minimum
degree scale and the ambient order.  Consequently the short-cycle and
Lemma 4.2 certificates are functions of `n'`.  Every field below is an
arithmetic statement; in particular this structure contains no graph,
expansion, adjuster, path, or availability hypothesis. -/
structure LM44Scale
    (N d targetOrder totalRadius Delta deletedCap protectedCap separation
      minRadius maxRadius R : ℕ) (kappa : ℝ) where
  seedCap : ℕ
  ballCap : ℕ
  initialDegree : ℕ
  coreDegree : ℕ
  starBudget : ℕ
  coreRadius : ℕ → ℕ
  coreDeltaOne : ℕ → ℕ
  coreDeltaSquare : ℕ → ℕ
  coreLocalRadius : ℕ → ℕ
  coreExpansionRadius : ℕ → ℕ
  deleted_le_ten_target : deletedCap ≤ 10 * targetOrder
  seed_bound :
    protectedCap + 4 * R * (2 * maxRadius ^ 2 + 10 * maxRadius) ≤ seedCap
  ball_bound : seedCap * (Delta + 1) ^ separation ≤ ballCap
  deletion_proper : deletedCap + ballCap < N
  initial_density : ∀ u ≤ deletedCap,
    initialDegree * (N - u) ≤
      ((N - u) - 100 * targetOrder ^ 2) * (d - d / 2)
  retained_density :
    (8 * coreDegree) * N + 2 * (ballCap * Delta) ≤
      initialDegree * (N - deletedCap)
  coreDegree_pos : 0 < coreDegree
  five_le_coreDegree : 5 ≤ coreDegree
  kappa_pos : 0 < kappa
  target_pos : 0 < targetOrder
  one_le_total : 1 ≤ totalRadius
  max_le_total : maxRadius ≤ totalRadius
  star_workspace :
    deletedCap + 10 * maxRadius + targetOrder + 1 ≤ starBudget
  star_degree : targetOrder + starBudget ≤ Delta
  coreRadius_pos : ∀ n', coreDegree < n' → n' ≤ N →
    0 < coreRadius n'
  coreRadius_bounds : ∀ n', coreDegree < n' → n' ≤ N →
    minRadius ≤ coreRadius n' ∧ coreRadius n' ≤ maxRadius
  core_family_radius : ∀ n', coreDegree < n' → n' ≤ N →
    5 * coreExpansionRadius n' ≤ coreRadius n'
  num_one : ∀ n', coreDegree < n' → n' ≤ N →
    LM311Numerics (1 / 1024) kappa n' 4 coreDegree
    ((coreRadius n') ^ 3) (coreDeltaOne n') (coreLocalRadius n')
    (coreExpansionRadius n') 1
  num_square : ∀ n', coreDegree < n' → n' ≤ N →
    LM311Numerics (1 / 1024) kappa n' 4 coreDegree
    ((coreRadius n') ^ 3 * (coreRadius n') ^ 2) (coreDeltaSquare n')
    (coreLocalRadius n') (coreExpansionRadius n') 1
  connector_one : ∀ n' L, coreDegree < n' → n' ≤ N →
    L ≤ lm311GirthBudget n' →
    LM42ConnectorScale n' coreDegree 1 (coreRadius n') L (1 / 1024) kappa
  connector_square : ∀ n' L, coreDegree < n' → n' ≤ N →
    L ≤ lm311GirthBudget n' →
    LM42ConnectorScale n' coreDegree ((coreRadius n') ^ 2) (coreRadius n') L
      (1 / 1024) kappa

/-- The occupied seed of a putatively small maximal family has the cardinality
budget recorded by `LM44Scale`.  This is the first counting estimate in Claim
4.4; proof fields on eligible candidates play no role in the count. -/
theorem card_LM44_seed_le [Fintype V]
    {N d targetOrder totalRadius Delta deletedCap protectedCap separation
      minRadius maxRadius R : ℕ} {kappa : ℝ}
    (scale : LM44Scale N d targetOrder totalRadius Delta deletedCap protectedCap
      separation minRadius maxRadius R kappa)
    {deleted highDegree protectedSet : Finset V}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hprotected : protectedSet.card ≤ protectedCap) (hS : S.card ≤ 4 * R) :
    (((protectedSet ∪ S.biUnion fun A ↦ A.1.adjuster.verts) \ highDegree)).card ≤
      scale.seedCap := by
  let originalDecEq : DecidableEq V := inferInstance
  classical
  let : DecidableEq V := originalDecEq
  have hoccupied := card_biUnion_subtype_adjuster_verts_le_maxRadius S
  have hunion :
      (protectedSet ∪ S.biUnion fun A ↦ A.1.adjuster.verts).card ≤
        protectedSet.card + S.card * (2 * maxRadius ^ 2 + 10 * maxRadius) :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_left hoccupied _)
  have hseed :
      (((protectedSet ∪ S.biUnion fun A ↦ A.1.adjuster.verts) \ highDegree)).card ≤
        (protectedSet ∪ S.biUnion fun A ↦ A.1.adjuster.verts).card :=
    Finset.card_le_card Finset.sdiff_subset
  let cap : ℕ := 2 * maxRadius ^ 2 + 10 * maxRadius
  have hprod : S.card * cap ≤ (4 * R) * cap :=
    Nat.mul_le_mul_right cap hS
  exact hseed.trans (hunion.trans
    ((Nat.add_le_add hprotected hprod).trans (by
      simpa only [cap] using scale.seed_bound)))

/-- The preceding seed bound and the bounded-degree Moore estimate give the
literal ball budget in `LM44Scale`. -/
theorem card_LM44_ball_le [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {N d targetOrder totalRadius Delta deletedCap protectedCap separation
      minRadius maxRadius R : ℕ} {kappa : ℝ}
    (scale : LM44Scale N d targetOrder totalRadius Delta deletedCap protectedCap
      separation minRadius maxRadius R kappa)
    {deleted protectedSet : Finset V}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted (highDegreeVertices G Delta) protectedSet separation}}
    (hprotected : protectedSet.card ≤ protectedCap) (hS : S.card ≤ 4 * R) :
    (ballAvoidingFrom G (highDegreeVertices G Delta : Set V)
      (((protectedSet ∪ S.biUnion fun A ↦ A.1.adjuster.verts) \
        highDegreeVertices G Delta)) separation).card ≤ scale.ballCap := by
  let originalDecEq : DecidableEq V := inferInstance
  classical
  let : DecidableEq V := originalDecEq
  let seed : Finset V :=
    (protectedSet ∪ S.biUnion fun A ↦ A.1.adjuster.verts) \
      highDegreeVertices G Delta
  have hseedCard : seed.card ≤ scale.seedCap := by
    simpa only [seed] using card_LM44_seed_le scale hprotected hS
  have hseedHigh : Disjoint seed (highDegreeVertices G Delta) := by
    rw [Finset.disjoint_left]
    intro v hvSeed hvHigh
    exact (Finset.mem_sdiff.1 hvSeed).2 hvHigh
  have hball := card_ballAvoidingFrom_highDegreeVertices_le
    G seed Delta separation hseedHigh
  have hmul : seed.card * (Delta + 1) ^ separation ≤
      scale.seedCap * (Delta + 1) ^ separation :=
    Nat.mul_le_mul_right _ hseedCard
  exact hball.trans (hmul.trans scale.ball_bound)

/-- The finite maximal collection `A₀`, constructed without requiring a
finiteness instance on the proof-carrying adjuster type. -/
theorem exists_maximal_eligible_family [Fintype V]
    (deleted highDegree protectedSet : Finset V) (separation : ℕ) :
    ∃ S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted highDegree protectedSet separation},
      ((S : Set {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
        ¬ Conflict A.1 B.1 highDegree separation) ∧
      ∀ A : {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted highDegree protectedSet separation},
        ∃ B ∈ S, Conflict A.1 B.1 highDegree separation := by
  classical
  apply exists_finite_maximal_conflictFree_family
    (Candidate := {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
      A.Eligible deleted highDegree protectedSet separation})
    (Key := V)
    (fun A ↦ A.1.adjuster.leftRoot)
    (fun A B ↦ Conflict A.1 B.1 highDegree separation)
  · intro A B hroot
    exact Or.inl hroot
  · intro A B h
    exact h.symm

/-- The maximality contradiction used in Case I of Claim 4.4.

Let `occupied` be the union of the existing adjusters and grow a radius
`separation` ball from all occupied and protected vertices outside the
high-degree set.  Any new small adjuster lying completely outside both that
ball and `deleted`, with both ends outside the high-degree set, is eligible.
Moreover it cannot conflict with an existing family member: a same-root
conflict or a short avoiding connection would put one of its end vertices
back in the forbidden ball. -/
theorem false_of_new_candidate_outside_maximal_ball [Fintype V]
    {deleted highDegree protectedSet : Finset V}
    {separation minRadius maxRadius radius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hmax : ∀ A : {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation},
      ∃ B ∈ S, Conflict A.1 B.1 highDegree separation)
    (hminRadius : minRadius ≤ radius) (hmaxRadius : radius ≤ maxRadius)
    (A : Adjuster G (radius ^ 2) radius 1)
    (hendsHigh : Disjoint (A.leftEnd.verts ∪ A.rightEnd.verts) highDegree)
    (houtside : Disjoint
      (deleted ∪ ballAvoidingFrom G (highDegree : Set V)
        (((protectedSet ∪ S.biUnion fun B ↦ B.1.adjuster.verts) \ highDegree))
        separation)
      A.verts) : False := by
  let occupied : Finset V := S.biUnion fun B ↦ B.1.adjuster.verts
  let seed : Finset V := (protectedSet ∪ occupied) \ highDegree
  let ball : Finset V := ballAvoidingFrom G (highDegree : Set V) seed separation
  have hdeleted : Disjoint deleted A.verts := by
    apply houtside.mono_left Finset.subset_union_left
  have hballA : Disjoint ball A.verts := by
    apply houtside.mono_left Finset.subset_union_right
  have hreach : ∀ {x y : V}, x ∈ A.leftEnd.verts ∪ A.rightEnd.verts →
      y ∈ seed → ∀ p : G.Walk x y, p.IsPath →
      p.Avoids (highDegree : Set V) ∅ → p.length ≤ separation → False := by
    intro x y hx hy p hp hpAvoid hpLength
    have hxBall : x ∈ ball := by
      apply (mem_ballAvoidingFrom G (highDegree : Set V) seed separation x).2
      refine ⟨y, hy, p.reverse, ⟨hp.reverse, ?_⟩, ?_⟩
      · intro z hz hzHigh
        exact (hpAvoid.reverse z hz hzHigh).elim
      · simpa using hpLength
    have hxVerts : x ∈ A.verts := by
      rw [Finset.mem_union] at hx
      rcases hx with hx | hx
      · exact A.leftEnd_verts_subset hx
      · exact A.rightEnd_verts_subset hx
    exact (Finset.disjoint_left.1 hballA hxBall hxVerts).elim
  have hprotectedFar : ¬ HasShortAvoidingConnection G highDegree
      (A.leftEnd.verts ∪ A.rightEnd.verts) (protectedSet \ highDegree)
      separation := by
    intro h
    obtain ⟨x, hx, y, hy, p, hp, hpAvoid, hpLength⟩ := h
    have hySeed : y ∈ seed := by
      change y ∈ (protectedSet ∪ occupied) \ highDegree
      rw [Finset.mem_sdiff]
      exact ⟨Finset.mem_union_left _ (Finset.mem_sdiff.1 hy).1,
        (Finset.mem_sdiff.1 hy).2⟩
    exact hreach hx hySeed p hp hpAvoid hpLength
  let candidate : SmallSimpleAdjusterCandidate G minRadius maxRadius :=
    { radius := radius
      min_le := hminRadius
      le_max := hmaxRadius
      adjuster := A }
  have heligible : candidate.Eligible deleted highDegree protectedSet separation := by
    exact ⟨hdeleted, hendsHigh, hprotectedFar⟩
  let eligible : {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
      A.Eligible deleted highDegree protectedSet separation} :=
    ⟨candidate, heligible⟩
  obtain ⟨B, hBS, hconflict⟩ := hmax eligible
  rcases hconflict with hroot | hshort
  · have hBrootEnds : B.1.adjuster.leftRoot ∈ B.1.ends :=
      B.1.leftRoot_mem_ends
    have hBrootHigh : B.1.adjuster.leftRoot ∉ highDegree := by
      intro hHigh
      exact (Finset.disjoint_left.1 B.2.2.1 hBrootEnds hHigh).elim
    have hBrootSeed : B.1.adjuster.leftRoot ∈ seed := by
      change B.1.adjuster.leftRoot ∈ (protectedSet ∪ occupied) \ highDegree
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_union_right _ ?_, hBrootHigh⟩
      change B.1.adjuster.leftRoot ∈ S.biUnion fun B ↦ B.1.adjuster.verts
      rw [Finset.mem_biUnion]
      exact ⟨B, hBS, B.1.adjuster.leftRoot_mem_verts⟩
    have hrootBall : A.leftRoot ∈ ball := by
      rw [hroot]
      exact subset_ballAvoidingFrom G (highDegree : Set V) seed separation hBrootSeed
    exact (Finset.disjoint_left.1 hballA hrootBall A.leftRoot_mem_verts).elim
  · obtain ⟨x, hx, y, hy, p, hp, hpAvoid, hpLength⟩ := hshort
    have hyHigh : y ∉ highDegree := by
      intro hHigh
      exact (Finset.disjoint_left.1 B.2.2.1 hy hHigh).elim
    have hySeed : y ∈ seed := by
      change y ∈ (protectedSet ∪ occupied) \ highDegree
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_union_right _ ?_, hyHigh⟩
      change y ∈ S.biUnion fun B ↦ B.1.adjuster.verts
      rw [Finset.mem_biUnion]
      refine ⟨B, hBS, ?_⟩
      have hy' : y ∈ B.1.adjuster.leftEnd.verts ∪
          B.1.adjuster.rightEnd.verts := by
        simpa only [ends] using hy
      rw [Finset.mem_union] at hy'
      rcases hy' with hy | hy
      · exact B.1.adjuster.leftEnd_verts_subset hy
      · exact B.1.adjuster.rightEnd_verts_subset hy
    exact hreach hx hySeed p hp hpAvoid hpLength

/-- A conflict-free eligible family has pairwise disjoint end sets. -/
theorem pairwiseDisjoint_ends_of_conflictFree
    {deleted highDegree protectedSet : Finset V} {separation : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
      ¬ Conflict A.1 B.1 highDegree separation)) :
    (S : Set {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
      A.Eligible deleted highDegree protectedSet separation}).PairwiseDisjoint
        fun A ↦ A.1.ends := by
  intro A hA B hB hAB
  change Disjoint A.1.ends B.1.ends
  rw [Finset.disjoint_left]
  intro z hzA hzB
  have hzHigh : z ∉ highDegree := by
    intro hz
    exact (Finset.disjoint_left.1 A.2.2.1 hzA hz).elim
  have hshort : HasShortAvoidingConnection G highDegree A.1.ends B.1.ends
      separation :=
    hasShortAvoidingConnection_of_common_vertex hzA hzB hzHigh
  exact (hpair hA hB hAB) (Or.inr hshort)

/-- Exact cardinality of the union of all end sets in a conflict-free
eligible family. -/
theorem card_biUnion_ends_of_conflictFree
    {deleted highDegree protectedSet : Finset V} {separation : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
      ¬ Conflict A.1 B.1 highDegree separation)) :
    (S.biUnion fun A ↦ A.1.ends).card =
      ∑ A ∈ S, 2 * A.1.radius ^ 2 := by
  rw [card_biUnion_eq_sum_card
    (pairwiseDisjoint_ends_of_conflictFree hpair)]
  apply Finset.sum_congr rfl
  intro A hA
  exact A.1.card_ends

/-- Coarse occupied-vertex bound for any finite family of small candidates.
Unlike `card_biUnion_ends_of_conflictFree`, this also charges the cores and
therefore needs no cross-candidate disjointness assumption. -/
theorem card_biUnion_adjuster_verts_le
    (S : Finset (SmallSimpleAdjusterCandidate G minRadius maxRadius)) :
    (S.biUnion fun A ↦ A.adjuster.verts).card ≤
      S.card * (2 * maxRadius ^ 2 + 10 * maxRadius) := by
  calc
    (S.biUnion fun A ↦ A.adjuster.verts).card
        ≤ ∑ A ∈ S, A.adjuster.verts.card := Finset.card_biUnion_le
    _ ≤ ∑ _A ∈ S, (2 * maxRadius ^ 2 + 10 * maxRadius) := by
      apply Finset.sum_le_sum
      intro A hA
      exact A.card_adjuster_verts_le_maxRadius
    _ = S.card * (2 * maxRadius ^ 2 + 10 * maxRadius) := by simp

/-- The separation invariant of a conflict-free eligible family gives the
pairwise-disjoint avoiding balls required by the correlated Lemma 3.7, even
when each candidate has its own two additional deleted sets. -/
theorem pairwiseDisjoint_candidate_avoidingBalls
    [Fintype V]
    {deleted highDegree protectedSet : Finset V} {separation radius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
      ¬ Conflict A.1 B.1 highDegree separation))
    (hradius : radius + radius ≤ separation)
    (B Cset : S → Finset V) :
    ((Finset.univ : Finset S) : Set S).PairwiseDisjoint
      (fun i ↦ ballAvoidingFrom G
        ((highDegree : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V))
        i.1.1.ends radius) := by
  classical
  apply pairwiseDisjoint_ballAvoidingFrom_union_three_of_no_short_path
  intro i j hij a ha b hb p hp
  have hiOut : a ∉ highDegree := by
    intro haHigh
    exact (Finset.disjoint_left.1 i.1.2.2.1 ha haHigh).elim
  have hjOut : b ∉ highDegree := by
    intro hbHigh
    exact (Finset.disjoint_left.1 j.1.2.2.1 hb hbHigh).elim
  have hpEmpty : p.Avoids (highDegree : Set V) ∅ := by
    intro z hz hzHigh
    have hzEnds := hp.2 z hz hzHigh
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzEnds
    rcases hzEnds with rfl | rfl
    · exact hiOut hzHigh
    · exact hjOut hzHigh
  have hij' : i.1 ≠ j.1 := by
    intro h
    exact hij (Subtype.ext h)
  have hno := hpair i.2 j.2 hij'
  by_contra hlength
  apply hno
  apply Or.inr
  exact ⟨a, ha, b, hb, p, hp.1, hpEmpty, by omega⟩

/-- Subset-seed form of `pairwiseDisjoint_candidate_avoidingBalls`.

Claims 4.5 and 4.6 orient each simple adjuster and grow only the end opposite
the selected shortest path.  The seed therefore varies with the candidate,
but remains a subset of that candidate's two ends.  The same conflict-free
separation invariant still makes all of the resulting avoiding balls
pairwise disjoint. -/
theorem pairwiseDisjoint_candidate_seed_avoidingBalls
    [Fintype V]
    {deleted highDegree protectedSet : Finset V} {separation radius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
      ¬ Conflict A.1 B.1 highDegree separation))
    (hradius : radius + radius ≤ separation)
    (seed B Cset : S → Finset V)
    (hseed : ∀ i : S, seed i ⊆ i.1.1.ends) :
    ((Finset.univ : Finset S) : Set S).PairwiseDisjoint
      (fun i ↦ ballAvoidingFrom G
        ((highDegree : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V))
        (seed i) radius) := by
  classical
  apply pairwiseDisjoint_ballAvoidingFrom_union_three_of_no_short_path
  intro i j hij a ha b hb p hp
  have haEnds : a ∈ i.1.1.ends := hseed i ha
  have hbEnds : b ∈ j.1.1.ends := hseed j hb
  have hiOut : a ∉ highDegree := by
    intro haHigh
    exact (Finset.disjoint_left.1 i.1.2.2.1 haEnds haHigh).elim
  have hjOut : b ∉ highDegree := by
    intro hbHigh
    exact (Finset.disjoint_left.1 j.1.2.2.1 hbEnds hbHigh).elim
  have hpEmpty : p.Avoids (highDegree : Set V) ∅ := by
    intro z hz hzHigh
    have hzEnds := hp.2 z hz hzHigh
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzEnds
    rcases hzEnds with rfl | rfl
    · exact hiOut hzHigh
    · exact hjOut hzHigh
  have hij' : i.1 ≠ j.1 := by
    intro h
    exact hij (Subtype.ext h)
  have hno := hpair i.2 j.2 hij'
  by_contra hlength
  apply hno
  apply Or.inr
  exact ⟨a, haEnds, b, hbEnds, p, hp.1, hpEmpty, by omega⟩

/-- The conflict-free invariant supplies C5 for the oriented opposite ends,
after deleting the high-degree set and the literal `Bᵢ,Cᵢ`. -/
theorem pairwiseDisjoint_reachingCandidate_balls
    [Fintype V]
    {deleted highDegree protectedSet target : Finset V}
    {separation connectionRadius ballRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
      ¬ Conflict A.1 B.1 highDegree separation))
    (hradius : ballRadius + ballRadius ≤ separation) :
    ((Finset.univ : Finset
      {A // A ∈ reachingEligibleSubfamily S target connectionRadius}) :
        Set {A // A ∈ reachingEligibleSubfamily S target connectionRadius}).PairwiseDisjoint
      (fun i ↦ ballAvoidingFrom G
        ((highDegree : Set V) ∪ (reachingCandidateCore i : Set V) ∪
          (reachingCandidatePath i : Set V))
        (reachingCandidateSeed i) ballRadius) := by
  apply pairwiseDisjoint_candidate_seed_avoidingBalls
    (S := reachingEligibleSubfamily S target connectionRadius)
    (fun A hA B hB hAB ↦ hpair
      ((mem_reachingEligibleSubfamily S target connectionRadius A).1 hA).1
      ((mem_reachingEligibleSubfamily S target connectionRadius B).1 hB).1 hAB)
    hradius reachingCandidateSeed reachingCandidateCore reachingCandidatePath
    reachingCandidateSeed_subset_ends

/-- Source-faithful C5, using `Bᵢ = core ∪ (Qᵢ - start)`. -/
theorem pairwiseDisjoint_reachingCandidate_barrier_balls
    [Fintype V]
    {deleted highDegree protectedSet target : Finset V}
    {separation connectionRadius ballRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
      ¬ Conflict A.1 B.1 highDegree separation))
    (hradius : ballRadius + ballRadius ≤ separation) :
    ((Finset.univ : Finset
      {A // A ∈ reachingEligibleSubfamily S target connectionRadius}) :
        Set {A // A ∈ reachingEligibleSubfamily S target connectionRadius}).PairwiseDisjoint
      (fun i ↦ ballAvoidingFrom G
        ((highDegree : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
          (reachingCandidatePath i : Set V))
        (reachingCandidateSeed i) ballRadius) := by
  apply pairwiseDisjoint_candidate_seed_avoidingBalls
    (S := reachingEligibleSubfamily S target connectionRadius)
    (fun A hA B hB hAB ↦ hpair
      ((mem_reachingEligibleSubfamily S target connectionRadius A).1 hA).1
      ((mem_reachingEligibleSubfamily S target connectionRadius B).1 hB).1 hAB)
    hradius reachingCandidateSeed reachingCandidateBarrier reachingCandidatePath
    reachingCandidateSeed_subset_ends

/-- C5 after deleting both the ambient set `U` and the high-degree set `L`.
Adding `U` only shrinks the already pairwise-disjoint `G-L` balls. -/
theorem pairwiseDisjoint_reachingCandidate_deleted_high_barrier_balls
    [Fintype V]
    {deleted highDegree protectedSet target : Finset V}
    {separation connectionRadius ballRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
      ¬ Conflict A.1 B.1 highDegree separation))
    (hradius : ballRadius + ballRadius ≤ separation) :
    ((Finset.univ : Finset
      {A // A ∈ reachingEligibleSubfamily S target connectionRadius}) :
        Set {A // A ∈ reachingEligibleSubfamily S target connectionRadius}).PairwiseDisjoint
      (fun i ↦ ballAvoidingFrom G
        ((deleted : Set V) ∪ (highDegree : Set V) ∪
          (reachingCandidateBarrier i : Set V) ∪
          (reachingCandidatePath i : Set V))
        (reachingCandidateSeed i) ballRadius) := by
  have hhigh := pairwiseDisjoint_reachingCandidate_barrier_balls
    (G := G) (target := target) (connectionRadius := connectionRadius)
    (ballRadius := ballRadius) (S := S) hpair hradius
  intro i hi j hj hij
  change Disjoint
    (ballAvoidingFrom G
      ((deleted : Set V) ∪ (highDegree : Set V) ∪
        (reachingCandidateBarrier i : Set V) ∪
        (reachingCandidatePath i : Set V))
      (reachingCandidateSeed i) ballRadius)
    (ballAvoidingFrom G
      ((deleted : Set V) ∪ (highDegree : Set V) ∪
        (reachingCandidateBarrier j : Set V) ∪
        (reachingCandidatePath j : Set V))
      (reachingCandidateSeed j) ballRadius)
  apply (hhigh hi hj hij).mono
  · apply ballAvoidingFrom_forbidden_anti G
    intro z hz
    rw [Set.mem_union, Set.mem_union] at hz
    rcases hz with (hzHigh | hzBarrier) | hzPath
    · exact Or.inl (Or.inl (Or.inr hzHigh))
    · exact Or.inl (Or.inr hzBarrier)
    · exact Or.inr hzPath
  · apply ballAvoidingFrom_forbidden_anti G
    intro z hz
    rw [Set.mem_union, Set.mem_union] at hz
    rcases hz with (hzHigh | hzBarrier) | hzPath
    · exact Or.inl (Or.inl (Or.inr hzHigh))
    · exact Or.inl (Or.inr hzBarrier)
    · exact Or.inr hzPath

/-- Transfer C5 from the high-degree-deleted balls to the actual
candidate-indexed balls used in Lemma 3.7.  Claims 4.5 and 4.6 establish the
pointwise equality by ruling out a short route to a new high-degree vertex. -/
theorem pairwiseDisjoint_reachingCandidate_balls_of_eq
    [Fintype V]
    {deleted highDegree protectedSet target : Finset V}
    {separation connectionRadius ballRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
      ¬ Conflict A.1 B.1 highDegree separation))
    (hradius : ballRadius + ballRadius ≤ separation)
    (hball : ∀ i :
        {A // A ∈ reachingEligibleSubfamily S target connectionRadius},
      ballAvoidingFrom G
          ((deleted : Set V) ∪ (reachingCandidateCore i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius =
        ballAvoidingFrom G
          ((highDegree : Set V) ∪ (reachingCandidateCore i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius) :
    ((Finset.univ : Finset
      {A // A ∈ reachingEligibleSubfamily S target connectionRadius}) :
        Set {A // A ∈ reachingEligibleSubfamily S target connectionRadius}).PairwiseDisjoint
      (fun i ↦ ballAvoidingFrom G
        ((deleted : Set V) ∪ (reachingCandidateCore i : Set V) ∪
          (reachingCandidatePath i : Set V))
        (reachingCandidateSeed i) ballRadius) := by
  have hhigh := pairwiseDisjoint_reachingCandidate_balls
    (G := G) (target := target) (connectionRadius := connectionRadius)
    (ballRadius := ballRadius) (S := S) hpair hradius
  intro i hi j hj hij
  change Disjoint
    (ballAvoidingFrom G
      ((deleted : Set V) ∪ (reachingCandidateCore i : Set V) ∪
        (reachingCandidatePath i : Set V))
      (reachingCandidateSeed i) ballRadius)
    (ballAvoidingFrom G
      ((deleted : Set V) ∪ (reachingCandidateCore j : Set V) ∪
        (reachingCandidatePath j : Set V))
      (reachingCandidateSeed j) ballRadius)
  rw [hball i, hball j]
  exact hhigh hi hj hij

/-- Barrier version of the preceding transfer, used verbatim in Claims 4.5
and 4.6. -/
theorem pairwiseDisjoint_reachingCandidate_barrier_balls_of_eq
    [Fintype V]
    {deleted highDegree protectedSet target : Finset V}
    {separation connectionRadius ballRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
      ¬ Conflict A.1 B.1 highDegree separation))
    (hradius : ballRadius + ballRadius ≤ separation)
    (hball : ∀ i :
        {A // A ∈ reachingEligibleSubfamily S target connectionRadius},
      ballAvoidingFrom G
          ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius =
        ballAvoidingFrom G
          ((highDegree : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius) :
    ((Finset.univ : Finset
      {A // A ∈ reachingEligibleSubfamily S target connectionRadius}) :
        Set {A // A ∈ reachingEligibleSubfamily S target connectionRadius}).PairwiseDisjoint
      (fun i ↦ ballAvoidingFrom G
        ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
          (reachingCandidatePath i : Set V))
        (reachingCandidateSeed i) ballRadius) := by
  have hhigh := pairwiseDisjoint_reachingCandidate_barrier_balls
    (G := G) (target := target) (connectionRadius := connectionRadius)
    (ballRadius := ballRadius) (S := S) hpair hradius
  intro i hi j hj hij
  change Disjoint
    (ballAvoidingFrom G
      ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
        (reachingCandidatePath i : Set V))
      (reachingCandidateSeed i) ballRadius)
    (ballAvoidingFrom G
      ((deleted : Set V) ∪ (reachingCandidateBarrier j : Set V) ∪
        (reachingCandidatePath j : Set V))
      (reachingCandidateSeed j) ballRadius)
  rw [hball i, hball j]
  exact hhigh hi hj hij

/-- Final C5 form used by correlated Lemma 3.7: pointwise Claim 4.5/4.6 ball
identities transfer the preceding `G-(U∪L)` pairwise disjointness back to
the actual `G-U` balls. -/
theorem pairwiseDisjoint_reachingCandidate_actual_barrier_balls
    [Fintype V]
    {deleted highDegree protectedSet target : Finset V}
    {separation connectionRadius ballRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
      ¬ Conflict A.1 B.1 highDegree separation))
    (hradius : ballRadius + ballRadius ≤ separation)
    (hball : ∀ i :
        {A // A ∈ reachingEligibleSubfamily S target connectionRadius},
      ballAvoidingFrom G
          ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius =
        ballAvoidingFrom G
          ((deleted : Set V) ∪ (highDegree : Set V) ∪
            (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius) :
    ((Finset.univ : Finset
      {A // A ∈ reachingEligibleSubfamily S target connectionRadius}) :
        Set {A // A ∈ reachingEligibleSubfamily S target connectionRadius}).PairwiseDisjoint
      (fun i ↦ ballAvoidingFrom G
        ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
          (reachingCandidatePath i : Set V))
        (reachingCandidateSeed i) ballRadius) := by
  have hhigh := pairwiseDisjoint_reachingCandidate_deleted_high_barrier_balls
    (G := G) (target := target) (connectionRadius := connectionRadius)
    (ballRadius := ballRadius) (S := S) hpair hradius
  intro i hi j hj hij
  change Disjoint
    (ballAvoidingFrom G
      ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
        (reachingCandidatePath i : Set V))
      (reachingCandidateSeed i) ballRadius)
    (ballAvoidingFrom G
      ((deleted : Set V) ∪ (reachingCandidateBarrier j : Set V) ∪
        (reachingCandidatePath j : Set V))
      (reachingCandidateSeed j) ballRadius)
  rw [hball i, hball j]
  exact hhigh hi hj hij

end SmallSimpleAdjusterCandidate

private theorem Walk.IsPath.cycleSplice {x y c z : V}
    {P : G.Walk x c} {R : G.Walk c z} {Q : G.Walk y z}
    (hP : P.IsPath) (hR : R.IsPath) (hQ : Q.IsPath)
    (hPR : P.support.Disjoint R.support.tail)
    (hPRQ : (P.support ++ R.support.tail).Disjoint Q.reverse.support.tail) :
    ((P.append R).append Q.reverse).IsPath := by
  apply Walk.IsPath.mk'
  rw [Walk.support_append, Walk.support_append, List.nodup_append']
  refine ⟨?_, hQ.reverse.support_nodup.tail, hPRQ⟩
  exact List.nodup_append'.2
    ⟨hP.support_nodup, hR.support_nodup.tail, hPR⟩

/-- Package the two almost-antipodal routes through a cycle as a simple
adjuster.  All geometric inputs are literal walks and expansions; in the
application below the connector walks come from
`exists_expansion_root_connector_of_lmExpander_growth`. -/
noncomputable def simpleAdjusterOfCycleSplice {x y c z : V} {D m half : ℕ}
    (left : VertexExpansion G x D m) (right : VertexExpansion G y D m)
    (C : G.Walk c c) (P : G.Walk x c) (Q : G.Walk y z)
    (short long : G.Walk c z)
    (hP : P.IsPath) (hQ : Q.IsPath)
    (hshort : short.IsPath) (hlong : long.IsPath)
    (hhalf : 1 ≤ half)
    (hshortLen : short.length = half - 1)
    (hlongLen : long.length = half + 1)
    (hshortSupport : ∀ w ∈ short.support, w ∈ C.support)
    (hlongSupport : ∀ w ∈ long.support, w ∈ C.support)
    (hPshort : P.support.Disjoint short.support.tail)
    (hPshortQ : (P.support ++ short.support.tail).Disjoint Q.reverse.support.tail)
    (hPlong : P.support.Disjoint long.support.tail)
    (hPlongQ : (P.support ++ long.support.tail).Disjoint Q.reverse.support.tail)
    (hcoreLeft : Disjoint (cycleSpliceCore P Q C) left.verts)
    (hcoreRight : Disjoint (cycleSpliceCore P Q C) right.verts)
    (hends : Disjoint left.verts right.verts)
    (hcard : (cycleSpliceCore P Q C).card ≤ 10 * m) :
    Adjuster G D m 1 := by
  classical
  let core := cycleSpliceCore P Q C
  let shortRoute : G.Walk x y := (P.append short).append Q.reverse
  let longRoute : G.Walk x y := (P.append long).append Q.reverse
  have hshortRoute : shortRoute.IsPath :=
    Walk.IsPath.cycleSplice hP hshort hQ hPshort hPshortQ
  have hlongRoute : longRoute.IsPath :=
    Walk.IsPath.cycleSplice hP hlong hQ hPlong hPlongQ
  have route_supported : ∀ (R : G.Walk c z),
      (∀ w ∈ R.support, w ∈ C.support) →
      ∀ w ∈ ((P.append R).append Q.reverse).support,
        w ∈ insert x (insert y core) := by
    intro R hRsupport w hw
    have hwparts : w ∈ P.support ∨ w ∈ R.support ∨ w ∈ Q.support := by
      rw [Walk.mem_support_append_iff, Walk.mem_support_append_iff] at hw
      rcases hw with (hw | hw) | hw
      · exact Or.inl hw
      · exact Or.inr (Or.inl hw)
      · exact Or.inr (Or.inr (by
          simpa [Walk.support_reverse] using hw))
    by_cases hwx : w = x
    · simp [hwx]
    by_cases hwy : w = y
    · simp [hwy]
    have hwcarrier :
        w ∈ P.support.toFinset ∪ C.support.toFinset ∪ Q.support.toFinset := by
      rcases hwparts with hwP | hwR | hwQ
      · simp [hwP]
      · simp [hRsupport w hwR]
      · simp [hwQ]
    have hwcore : w ∈ core := by
      simp only [core, cycleSpliceCore, Finset.mem_sdiff,
        Finset.mem_insert, Finset.mem_singleton]
      exact ⟨hwcarrier, by simp [hwx, hwy]⟩
    simp [hwcore]
  let ell := P.length + short.length + Q.length
  have hshortSupported :
      HasSupportedPathLength G (insert x (insert y core)) x y ell := by
    refine ⟨shortRoute, hshortRoute, ?_, ?_⟩
    · exact route_supported short hshortSupport
    · simp [shortRoute, ell, Walk.length_append, Nat.add_assoc]
  have hlongLength : longRoute.length = ell + 2 := by
    simp [longRoute, ell, Walk.length_append, hshortLen, hlongLen]
    omega
  have hlongSupported :
      HasSupportedPathLength G (insert x (insert y core)) x y (ell + 2) := by
    exact ⟨longRoute, hlongRoute, route_supported long hlongSupport, hlongLength⟩
  exact simpleAdjusterOfTwoRoutes left right core hcoreLeft hcoreRight hends
    hcard hshortSupported hlongSupported

/-! ## Concrete simultaneous expansions for Lemma 4.2 -/

/-- The six (not necessarily distinct) centres used in the proof of
Liu--Montgomery Lemma 4.2.  Repeated centres are intentional. -/
def lemma42Roots (x₁ x₂ c z : V) : Fin 6 → V :=
  ![x₁, x₁, x₂, x₂, c, z]

/-- Orders of the six simultaneous expansions in Lemma 4.2. -/
def lemma42Orders (D m : ℕ) : Fin 6 → ℕ :=
  ![D, m ^ 3 * D, D, m ^ 2 * D, m ^ 3 * D, m ^ 2 * D]

/-- The ordered four distinct top-level roots in the source matrix
formulation of Lemma 3.11. -/
def lemma42FourRoots (x₁ x₂ c z : V) : Fin 4 → V :=
  ![x₁, x₂, c, z]

theorem lemma42FourRoots_injective (x₁ x₂ c z : V)
    (hx₁x₂ : x₁ ≠ x₂) (hx₁c : x₁ ≠ c) (hx₁z : x₁ ≠ z)
    (hx₂c : x₂ ≠ c) (hx₂z : x₂ ≠ z) (hcz : c ≠ z) :
    Function.Injective (lemma42FourRoots x₁ x₂ c z) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [lemma42FourRoots]

/-- The four roots packaged as an embedding. -/
def lemma42RootEmbedding (x₁ x₂ c z : V)
    (hx₁x₂ : x₁ ≠ x₂) (hx₁c : x₁ ≠ c) (hx₁z : x₁ ≠ z)
    (hx₂c : x₂ ≠ c) (hx₂z : x₂ ≠ z) (hcz : c ≠ z) :
    Fin 4 ↪ V where
  toFun := lemma42FourRoots x₁ x₂ c z
  inj' := lemma42FourRoots_injective x₁ x₂ c z
    hx₁x₂ hx₁c hx₁z hx₂c hx₂z hcz

/-- Matrix of orders for the source Lemma 3.11 call in Lemma 4.2.  Only six
entries are used; the other ten are harmless singleton expansions. -/
def lemma42MatrixOrders (D m : ℕ) : Fin 4 → Fin 4 → ℕ :=
  ![![D, m ^ 3 * D, 1, 1],
    ![D, m ^ 2 * D, 1, 1],
    ![m ^ 3 * D, 1, 1, 1],
    ![m ^ 2 * D, 1, 1, 1]]

/-- The six matrix entries used by Lemma 4.2, in the order of the older flat
six-expansion formulation.  Injectivity is what transfers the matrix
family's pairwise trimmed-disjointness to those six selected expansions. -/
def lemma42MatrixIndex : Fin 6 → Fin 4 × Fin 4 :=
  ![(0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (3, 0)]

theorem lemma42MatrixIndex_injective : Function.Injective lemma42MatrixIndex := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [lemma42MatrixIndex]

@[simp] theorem lemma42MatrixIndex_root (x₁ x₂ c z : V)
    (hx₁x₂ : x₁ ≠ x₂) (hx₁c : x₁ ≠ c) (hx₁z : x₁ ≠ z)
    (hx₂c : x₂ ≠ c) (hx₂z : x₂ ≠ z) (hcz : c ≠ z)
    (i : Fin 6) :
    lemma42RootEmbedding x₁ x₂ c z hx₁x₂ hx₁c hx₁z hx₂c hx₂z hcz
        (lemma42MatrixIndex i).1 = lemma42Roots x₁ x₂ c z i := by
  fin_cases i <;>
    rfl

@[simp] theorem lemma42MatrixIndex_order (D m : ℕ) (i : Fin 6) :
    lemma42MatrixOrders D m (lemma42MatrixIndex i).1
        (lemma42MatrixIndex i).2 = lemma42Orders D m i := by
  fin_cases i <;>
    rfl

/-- Select the six expansions used in Lemma 4.2 from the genuine
matrix-indexed conclusion of Lemma 3.11. -/
noncomputable def LM311ExpansionFamily.lemma42Selected
    {radius : ℕ} {reserved : Finset V}
    (x₁ x₂ c z : V)
    (hx₁x₂ : x₁ ≠ x₂) (hx₁c : x₁ ≠ c) (hx₁z : x₁ ≠ z)
    (hx₂c : x₂ ≠ c) (hx₂z : x₂ ≠ z) (hcz : c ≠ z)
    (D m : ℕ)
    (F : LM311ExpansionFamily G
      (lemma42RootEmbedding x₁ x₂ c z hx₁x₂ hx₁c hx₁z hx₂c hx₂z hcz)
      (lemma42MatrixOrders D m) radius reserved)
    (i : Fin 6) :
    VertexExpansion G (lemma42Roots x₁ x₂ c z i)
      (lemma42Orders D m i) radius := by
  simpa using F.expansion (lemma42MatrixIndex i).1 (lemma42MatrixIndex i).2

@[simp] theorem LM311ExpansionFamily.lemma42Selected_verts
    {radius : ℕ} {reserved : Finset V}
    (x₁ x₂ c z : V)
    (hx₁x₂ : x₁ ≠ x₂) (hx₁c : x₁ ≠ c) (hx₁z : x₁ ≠ z)
    (hx₂c : x₂ ≠ c) (hx₂z : x₂ ≠ z) (hcz : c ≠ z)
    (D m : ℕ)
    (F : LM311ExpansionFamily G
      (lemma42RootEmbedding x₁ x₂ c z hx₁x₂ hx₁c hx₁z hx₂c hx₂z hcz)
      (lemma42MatrixOrders D m) radius reserved)
    (i : Fin 6) :
    (F.lemma42Selected x₁ x₂ c z hx₁x₂ hx₁c hx₁z
      hx₂c hx₂z hcz D m i).verts =
      (F.expansion (lemma42MatrixIndex i).1
        (lemma42MatrixIndex i).2).verts := by
  fin_cases i <;> rfl

/-- The selected six expansions inherit avoidance of the complete reserved
set from the matrix conclusion of source Lemma 3.11. -/
theorem LM311ExpansionFamily.lemma42Selected_avoids_reserved
    {radius : ℕ} {reserved : Finset V}
    (x₁ x₂ c z : V)
    (hx₁x₂ : x₁ ≠ x₂) (hx₁c : x₁ ≠ c) (hx₁z : x₁ ≠ z)
    (hx₂c : x₂ ≠ c) (hx₂z : x₂ ≠ z) (hcz : c ≠ z)
    (D m : ℕ)
    (F : LM311ExpansionFamily G
      (lemma42RootEmbedding x₁ x₂ c z hx₁x₂ hx₁c hx₁z hx₂c hx₂z hcz)
      (lemma42MatrixOrders D m) radius reserved)
    (i : Fin 6) :
    Disjoint
      ((F.lemma42Selected x₁ x₂ c z hx₁x₂ hx₁c hx₁z
        hx₂c hx₂z hcz D m i).verts \ {lemma42Roots x₁ x₂ c z i})
      reserved := by
  rw [F.lemma42Selected_verts]
  simpa using F.avoids_protected
    (lemma42MatrixIndex i).1 (lemma42MatrixIndex i).2

/-- The six selected entries are still pairwise disjoint away from their
prescribed roots. -/
theorem LM311ExpansionFamily.lemma42Selected_pairwise_disjoint
    {radius : ℕ} {reserved : Finset V}
    (x₁ x₂ c z : V)
    (hx₁x₂ : x₁ ≠ x₂) (hx₁c : x₁ ≠ c) (hx₁z : x₁ ≠ z)
    (hx₂c : x₂ ≠ c) (hx₂z : x₂ ≠ z) (hcz : c ≠ z)
    (D m : ℕ)
    (F : LM311ExpansionFamily G
      (lemma42RootEmbedding x₁ x₂ c z hx₁x₂ hx₁c hx₁z hx₂c hx₂z hcz)
      (lemma42MatrixOrders D m) radius reserved)
    (i j : Fin 6) (hij : i ≠ j) :
    Disjoint
      ((F.lemma42Selected x₁ x₂ c z hx₁x₂ hx₁c hx₁z
        hx₂c hx₂z hcz D m i).verts \ {lemma42Roots x₁ x₂ c z i})
      ((F.lemma42Selected x₁ x₂ c z hx₁x₂ hx₁c hx₁z
        hx₂c hx₂z hcz D m j).verts \ {lemma42Roots x₁ x₂ c z j}) := by
  rw [F.lemma42Selected_verts, F.lemma42Selected_verts]
  simpa using F.pairwise_disjoint
    (lemma42MatrixIndex i) (lemma42MatrixIndex j)
    (lemma42MatrixIndex_injective.ne hij)

/-- Purely numerical hypotheses for the concrete proof of Lemma 4.2.

The first group is the finite form of Lemma 3.11 for the six expansions.
The second group is the uniform Lemma 3.4 estimate used for both connector
paths.  This contains no graph, path, expansion, or adjuster availability
assumption. -/
structure LM42Scale (N d D m cycleLength : ℕ) (epsilon kappa : ℝ) where
  qExpansion : ℕ
  expansionRadius : ℕ
  expansionBudget : ℕ
  connectorWorkspace : ℕ
  qConnector : ℕ
  connectorRadius : ℕ
  two_le_m : 2 ≤ m
  D_pos : 0 < D
  expansion_budget :
    cycleLength + 2 + 6 +
      (2 * D + 2 * (m ^ 3 * D) + 2 * (m ^ 2 * D)) ≤ expansionBudget
  expansion_seed :
    kappa / 2 ≤ ((d - 1 - expansionBudget : ℕ) : ℝ)
  expansion_rate : ∀ s : ℕ, d - 1 - expansionBudget ≤ s →
    s ≤ N / 2 →
    (((expansionBudget + qExpansion : ℕ) : ℝ) ≤
      expansionEpsilon epsilon kappa s * (s : ℝ))
  expansion_target :
    m ^ 3 * D ≤ d - 1 - expansionBudget + expansionRadius * qExpansion
  expansion_half : m ^ 3 * D ≤ N / 2 + 1
  expansion_radius : expansionRadius + 1 ≤ m
  connector_workspace_large :
    cycleLength + 2 + 2 * D + 2 * (m ^ 2 * D) ≤ connectorWorkspace
  connector_workspace_path :
    cycleLength + 2 + (3 * m + 1) + 2 * D ≤ connectorWorkspace
  connector_lower_sq : kappa / 2 ≤ ((m ^ 2 * D : ℕ) : ℝ)
  connector_lower_cube : kappa / 2 ≤ ((m ^ 3 * D : ℕ) : ℝ)
  connector_rate : ∀ s : ℕ, m ^ 2 * D ≤ s → s ≤ N / 2 →
    (((connectorWorkspace + qConnector : ℕ) : ℝ) ≤
      expansionEpsilon epsilon kappa s * (s : ℝ))
  connector_rate_cube : ∀ s : ℕ, m ^ 3 * D ≤ s → s ≤ N / 2 →
    (((connectorWorkspace + qConnector : ℕ) : ℝ) ≤
      expansionEpsilon epsilon kappa s * (s : ℝ))
  connector_steps_sq :
    N / 2 + 1 ≤ m ^ 2 * D + connectorRadius * qConnector
  connector_steps_cube :
    N / 2 + 1 ≤ m ^ 3 * D + connectorRadius * qConnector
  connector_radius : 2 * connectorRadius ≤ m
  cycle_length : cycleLength ≤ 2 * m

/-- Connector certificates are monotone in the asserted cycle-length bound. -/
def LM42ConnectorScale.cycleLengthMono
    {N d D m L L' : ℕ} {epsilon kappa : ℝ}
    (scale : LM42ConnectorScale N d D m L' epsilon kappa) (hLL' : L ≤ L') :
    LM42ConnectorScale N d D m L epsilon kappa where
  squareWorkspace := scale.squareWorkspace
  cubeWorkspace := scale.cubeWorkspace
  squareStart := scale.squareStart
  cubeStart := scale.cubeStart
  squareRadius := scale.squareRadius
  cubeRadius := scale.cubeRadius
  two_le_m := scale.two_le_m
  D_pos := scale.D_pos
  connector_workspace_large := scale.connector_workspace_large.trans' (by omega)
  connector_workspace_path := scale.connector_workspace_path.trans' (by omega)
  squareSeed := scale.squareSeed
  cubeSeed := scale.cubeSeed
  squareGrowth := scale.squareGrowth
  cubeGrowth := scale.cubeGrowth
  square_path_radius := scale.square_path_radius
  cube_path_radius := scale.cube_path_radius
  cycle_length := hLL'.trans scale.cycle_length

/-- A certificate proved at a larger cycle-length bound also applies to every
shorter cycle. -/
def LM42Scale.cycleLengthMono {N d D m L L' : ℕ} {epsilon kappa : ℝ}
    (scale : LM42Scale N d D m L' epsilon kappa) (hLL' : L ≤ L') :
    LM42Scale N d D m L epsilon kappa where
  qExpansion := scale.qExpansion
  expansionRadius := scale.expansionRadius
  expansionBudget := scale.expansionBudget
  connectorWorkspace := scale.connectorWorkspace
  qConnector := scale.qConnector
  connectorRadius := scale.connectorRadius
  two_le_m := scale.two_le_m
  D_pos := scale.D_pos
  expansion_budget := scale.expansion_budget.trans' (by omega)
  expansion_seed := scale.expansion_seed
  expansion_rate := scale.expansion_rate
  expansion_target := scale.expansion_target
  expansion_half := scale.expansion_half
  expansion_radius := scale.expansion_radius
  connector_workspace_large := scale.connector_workspace_large.trans' (by omega)
  connector_workspace_path := scale.connector_workspace_path.trans' (by omega)
  connector_lower_sq := scale.connector_lower_sq
  connector_lower_cube := scale.connector_lower_cube
  connector_rate := scale.connector_rate
  connector_rate_cube := scale.connector_rate_cube
  connector_steps_sq := scale.connector_steps_sq
  connector_steps_cube := scale.connector_steps_cube
  connector_radius := scale.connector_radius
  cycle_length := hLL'.trans scale.cycle_length

/-! ### Overlap bookkeeping for the source matrix form of Lemma 3.11 -/

/-- Two different members of a source Lemma 3.11 expansion family can meet
only at the root of the first member, provided the protected set contains all
prescribed roots. -/
theorem LM311ExpansionFamily.mem_eq_root_of_mem
    {k radius : ℕ} {root : Fin k ↪ V} {order : Fin k → Fin k → ℕ}
    {reserved : Finset V}
    (F : LM311ExpansionFamily G root order radius reserved)
    (hroots : Finset.univ.image root ⊆ reserved)
    {a b : Fin k × Fin k} (hab : a ≠ b) {v : V}
    (hva : v ∈ (F.expansion a.1 a.2).verts)
    (hvb : v ∈ (F.expansion b.1 b.2).verts) :
    v = root a.1 := by
  classical
  by_contra hvaroot
  by_cases hvbroot : v = root b.1
  · subst v
    apply (Finset.disjoint_left.1 (F.avoids_protected a.1 a.2))
    · rw [Finset.mem_sdiff, Finset.mem_singleton]
      exact ⟨hva, hvaroot⟩
    · apply hroots
      exact Finset.mem_image.2 ⟨b.1, Finset.mem_univ _, rfl⟩
  · apply (Finset.disjoint_left.1 (F.pairwise_disjoint a b hab))
    · rw [Finset.mem_sdiff, Finset.mem_singleton]
      exact ⟨hva, hvaroot⟩
    · rw [Finset.mem_sdiff, Finset.mem_singleton]
      exact ⟨hvb, hvbroot⟩

/-- Members attached to different top-level roots are fully disjoint. -/
theorem LM311ExpansionFamily.disjoint_of_root_ne
    {k radius : ℕ} {root : Fin k ↪ V} {order : Fin k → Fin k → ℕ}
    {reserved : Finset V}
    (F : LM311ExpansionFamily G root order radius reserved)
    (hroots : Finset.univ.image root ⊆ reserved)
    {a b : Fin k × Fin k} (hab : a ≠ b) (hroot : root a.1 ≠ root b.1) :
    Disjoint (F.expansion a.1 a.2).verts (F.expansion b.1 b.2).verts := by
  rw [Finset.disjoint_left]
  intro v hva hvb
  have ha := F.mem_eq_root_of_mem hroots hab hva hvb
  have hb := F.mem_eq_root_of_mem hroots (Ne.symm hab) hvb hva
  exact hroot (ha.symm.trans hb)

/-- A member of the family meets the protected set only at its root. -/
theorem LM311ExpansionFamily.mem_eq_root_of_mem_reserved
    {k radius : ℕ} {root : Fin k ↪ V} {order : Fin k → Fin k → ℕ}
    {reserved : Finset V}
    (F : LM311ExpansionFamily G root order radius reserved)
    {i j : Fin k} {v : V}
    (hvE : v ∈ (F.expansion i j).verts) (hvR : v ∈ reserved) :
    v = root i := by
  classical
  by_contra hvroot
  apply (Finset.disjoint_left.1 (F.avoids_protected i j))
  · rw [Finset.mem_sdiff, Finset.mem_singleton]
    exact ⟨hvE, hvroot⟩
  · exact hvR

/-- Any common vertex of two distinct selected expansions is the root of the
first one.  This is the overlap fact consumed by both connector barriers in
the source proof of Lemma 4.2. -/
theorem LM311ExpansionFamily.lemma42Selected_mem_eq_root_of_mem
    {radius : ℕ} {reserved : Finset V}
    (x₁ x₂ c z : V)
    (hx₁x₂ : x₁ ≠ x₂) (hx₁c : x₁ ≠ c) (hx₁z : x₁ ≠ z)
    (hx₂c : x₂ ≠ c) (hx₂z : x₂ ≠ z) (hcz : c ≠ z)
    (D m : ℕ)
    (F : LM311ExpansionFamily G
      (lemma42RootEmbedding x₁ x₂ c z hx₁x₂ hx₁c hx₁z hx₂c hx₂z hcz)
      (lemma42MatrixOrders D m) radius reserved)
    (hroots : Finset.univ.image
      (lemma42RootEmbedding x₁ x₂ c z hx₁x₂ hx₁c hx₁z hx₂c hx₂z hcz) ⊆
        reserved)
    {i j : Fin 6} (hij : i ≠ j) {v : V}
    (hvi : v ∈ (F.lemma42Selected x₁ x₂ c z hx₁x₂ hx₁c hx₁z
      hx₂c hx₂z hcz D m i).verts)
    (hvj : v ∈ (F.lemma42Selected x₁ x₂ c z hx₁x₂ hx₁c hx₁z
      hx₂c hx₂z hcz D m j).verts) :
    v = lemma42Roots x₁ x₂ c z i := by
  rw [F.lemma42Selected_verts] at hvi hvj
  have hindex : lemma42MatrixIndex i ≠ lemma42MatrixIndex j :=
    lemma42MatrixIndex_injective.ne hij
  have h := F.mem_eq_root_of_mem hroots hindex
    (v := v) hvi hvj
  simpa using h

/-- A selected expansion meets the matrix family's reserved set only at its
prescribed Lemma 4.2 root. -/
theorem LM311ExpansionFamily.lemma42Selected_mem_eq_root_of_mem_reserved
    {radius : ℕ} {reserved : Finset V}
    (x₁ x₂ c z : V)
    (hx₁x₂ : x₁ ≠ x₂) (hx₁c : x₁ ≠ c) (hx₁z : x₁ ≠ z)
    (hx₂c : x₂ ≠ c) (hx₂z : x₂ ≠ z) (hcz : c ≠ z)
    (D m : ℕ)
    (F : LM311ExpansionFamily G
      (lemma42RootEmbedding x₁ x₂ c z hx₁x₂ hx₁c hx₁z hx₂c hx₂z hcz)
      (lemma42MatrixOrders D m) radius reserved)
    {i : Fin 6} {v : V}
    (hvi : v ∈ (F.lemma42Selected x₁ x₂ c z hx₁x₂ hx₁c hx₁z
      hx₂c hx₂z hcz D m i).verts)
    (hvReserved : v ∈ reserved) :
    v = lemma42Roots x₁ x₂ c z i := by
  rw [F.lemma42Selected_verts] at hvi
  have h := F.mem_eq_root_of_mem_reserved
    (i := (lemma42MatrixIndex i).1) (j := (lemma42MatrixIndex i).2)
    (v := v) hvi hvReserved
  simpa using h

private theorem mem_eq_root_of_mem_expansions
    {t : ℕ} {root : Fin t → V} {order : Fin t → ℕ} {m : ℕ}
    (E : ∀ i, VertexExpansion G (root i) (order i) m)
    (hroots : ∀ i, Disjoint ((E i).verts \ {root i})
      (Finset.univ.image root))
    (hpair : ∀ i j, i ≠ j →
      Disjoint ((E i).verts \ {root i}) ((E j).verts \ {root j}))
    {i j : Fin t} (hij : i ≠ j) {v : V}
    (hvi : v ∈ (E i).verts) (hvj : v ∈ (E j).verts) :
    v = root i := by
  classical
  by_contra hviroot
  by_cases hvjroot : v = root j
  · subst v
    apply (Finset.disjoint_left.1 (hroots i))
    · rw [Finset.mem_sdiff, Finset.mem_singleton]
      exact ⟨hvi, hviroot⟩
    · exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩
  · apply (Finset.disjoint_left.1 (hpair i j hij))
    · rw [Finset.mem_sdiff, Finset.mem_singleton]
      exact ⟨hvi, hviroot⟩
    · rw [Finset.mem_sdiff, Finset.mem_singleton]
      exact ⟨hvj, hvjroot⟩

private theorem mem_eq_root_of_mem_expansion_protected
    {t : ℕ} {root : Fin t → V} {order : Fin t → ℕ} {m : ℕ}
    (E : ∀ i, VertexExpansion G (root i) (order i) m)
    {protectedSet : Finset V}
    (hprotected : ∀ i, Disjoint ((E i).verts \ {root i}) protectedSet)
    {i : Fin t} {v : V} (hvi : v ∈ (E i).verts)
    (hvP : v ∈ protectedSet) : v = root i := by
  classical
  by_contra hviroot
  apply (Finset.disjoint_left.1 (hprotected i))
  · rw [Finset.mem_sdiff, Finset.mem_singleton]
    exact ⟨hvi, hviroot⟩
  · exact hvP

private theorem Walk.IsPath.start_not_mem_tail {x y : V}
    {p : G.Walk x y} (hp : p.IsPath) : x ∉ p.support.tail := by
  have hn := hp.support_nodup
  rw [← p.cons_tail_support, List.nodup_cons] at hn
  exact hn.1

/-! ## A compact numeric interface to the concrete Lemma 3.7 -/

/-- There are at most `2 ^ |U|` bounded subsets of `U`. -/
theorem card_boundedSubsets_le_two_pow (U : Finset V) (C : ℕ) :
    (boundedSubsets U C).card ≤ 2 ^ U.card := by
  let originalDecEq : DecidableEq V := inferInstance
  classical
  let : DecidableEq V := originalDecEq
  calc
    (boundedSubsets U C).card ≤ U.powerset.card :=
      Finset.card_le_card (by
        intro Z hZ
        exact Finset.mem_powerset.2 ((mem_boundedSubsets U Z C).1 hZ).1)
    _ = 2 ^ U.card := Finset.card_powerset U

/-- Graph-free arithmetic data for the source-faithful, size-correlated form
of Lemma 3.7.  The actual candidate-dependent neighborhood inequality is
kept as a geometric input to the application theorem below. -/
structure LM37CorrelatedScale
    (N Ucap Icard contact radius M degreeIntoU : ℕ)
    (epsilon kappa : ℝ) where
  growth : ℕ → ℕ
  minSize : ℕ
  cutoff : ℕ
  D : ℕ
  T : ℕ
  qLarge : ℕ
  qSmall : ℕ → ℕ
  neighborBudget : ℕ → ℕ
  blockedBudget : ℕ → ℕ
  largeBudget : ℕ → ℕ
  stepLoss : ℕ → ℕ
  index : T ≤ Icard
  target_le_D : M ≤ D
  target_growth : M ≤ growth radius
  jump : ∀ ell : ℕ, 0 < ell → ell ≤ radius →
    growth ell ≤ growth (ell - 1) + 1 + stepLoss ell
  blocked_profile : ∀ s : ℕ, minSize ≤ s → s < cutoff →
    s * degreeIntoU ≤ blockedBudget s
  minSize_pos : 0 < minSize
  cutoff_pos : 0 < cutoff
  D_pos : 0 < D
  T_pos : 0 < T
  qSmall_pos : ∀ r : ℕ, minSize ≤ r → r < cutoff → 0 < qSmall r
  large_sample : qLarge * D ≤ (T + 1) / 2
  small_sample :
    ∑ r ∈ Finset.Ico minSize cutoff,
      r * (((blockedBudget r + 1) * (max 1 Ucap) ^ (blockedBudget r)) *
        qSmall r) ≤ (T + 1) / 2
  large_lower : kappa / 2 ≤ ((qLarge * cutoff : ℕ) : ℝ)
  large_upper : ((qLarge * D : ℕ) : ℝ) ≤ (N : ℝ) / 2
  large_rate : ∀ s : ℕ, qLarge * cutoff ≤ s → s ≤ qLarge * D →
    (((Ucap + largeBudget s : ℕ) : ℝ) <
      expansionEpsilon epsilon kappa s * (s : ℝ))
  small_lower : ∀ r : ℕ, minSize ≤ r → r < cutoff →
    kappa / 2 ≤ ((qSmall r * r : ℕ) : ℝ)
  small_upper : ∀ r : ℕ, minSize ≤ r → r < cutoff →
    ((qSmall r * r : ℕ) : ℝ) ≤ (N : ℝ) / 2
  small_rate : ∀ r : ℕ, minSize ≤ r → r < cutoff →
    (((blockedBudget r + qSmall r * neighborBudget r : ℕ) : ℝ) <
      expansionEpsilon epsilon kappa (qSmall r * r) *
        ((qSmall r * r : ℕ) : ℝ))

/-- The correlated Lemma 3.7 with its long arithmetic tail packaged in an
`LM37CorrelatedScale`. -/
theorem exists_large_avoiding_ball_of_LM37CorrelatedScale
    {I : Type*} [Fintype V] [Fintype I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (epsilon kappa : ℝ)
    (hexp : IsLMExpander G epsilon kappa)
    (U : Finset V) (A B Cset : I → Finset V)
    (Ucap Icard contact radius M degreeIntoU : ℕ)
    (scale : LM37CorrelatedScale (Fintype.card V) Ucap Icard contact radius M
      degreeIntoU epsilon kappa)
    (hU : U.card ≤ Ucap) (hI : Icard ≤ Fintype.card I)
    (hstart : ∀ i : I, scale.growth 0 < (A i).card)
    (hstartOne : ∀ i : I, scale.growth 1 < (ballAvoidingFrom G
      ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V)) (A i) 1).card)
    (hballOneLower : ∀ i : I, scale.minSize ≤ (ballAvoidingFrom G
      ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V)) (A i) 1).card)
    (hcontact : ∀ i : I,
      HasLimitedContactAfterDeletion G (A i) (U ∪ B i) (Cset i) contact)
    (hpairBalls : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i ↦ ballAvoidingFrom G
        ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V)) (A i) radius))
    (hneighborPoint : ∀ (i : I) (ell : ℕ), 0 < ell → ell ≤ radius →
      scale.growth (ell - 1) < (ballAvoidingFrom G
        ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V))
        (A i) (ell - 1)).card →
      scale.stepLoss ell + (B i).card + contact * ell ≤
        scale.neighborBudget (ballAvoidingFrom G
          ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V))
          (A i) (ell - 1)).card)
    (hdegreeU : ∀ i : I, ∀ v ∈ ballAvoidingFrom G
      ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V)) (A i) radius,
        (G.neighborFinset v ∩ U).card ≤ degreeIntoU)
    (hlargeBudgetSum : ∀ (J : Finset I) (f : I → ℕ),
      (∀ i ∈ J, scale.cutoff ≤ f i ∧ f i ≤ scale.D) →
      ∑ i ∈ J, scale.neighborBudget (f i) ≤ scale.largeBudget (∑ i ∈ J, f i)) :
    ∃ i : I, M ≤ (ballAvoidingFrom G
      ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V)) (A i) radius).card := by
  let originalDecAdj : DecidableRel G.Adj := inferInstance
  classical
  let : DecidableRel G.Adj := originalDecAdj
  apply liuMontgomery_lemma3_7_correlated G epsilon kappa hexp U A B Cset
    contact radius M scale.growth scale.minSize scale.cutoff scale.D scale.T
      scale.qLarge degreeIntoU scale.qSmall scale.neighborBudget scale.blockedBudget
      scale.largeBudget scale.stepLoss
  · exact hstart
  · exact hstartOne
  · exact hballOneLower
  · exact scale.target_growth
  · exact hcontact
  · exact hpairBalls
  · exact scale.index.trans hI
  · exact scale.target_le_D
  · exact scale.jump
  · exact hneighborPoint
  · intro i v hv
    refine (Finset.card_le_card ?_).trans (hdegreeU i v hv)
    intro w hw
    simpa only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] using hw
  · exact scale.blocked_profile
  · exact scale.minSize_pos
  · exact scale.cutoff_pos
  · exact scale.D_pos
  · exact scale.T_pos
  · exact scale.qSmall_pos
  · exact scale.large_sample
  · calc
      ∑ r ∈ Finset.Ico scale.minSize scale.cutoff,
          r * ((boundedSubsets U (scale.blockedBudget r)).card * scale.qSmall r)
          ≤ ∑ r ∈ Finset.Ico scale.minSize scale.cutoff,
            r * (((scale.blockedBudget r + 1) *
              (max 1 Ucap) ^ (scale.blockedBudget r)) * scale.qSmall r) := by
              apply Finset.sum_le_sum
              intro r hr
              exact Nat.mul_le_mul_left r (Nat.mul_le_mul_right (scale.qSmall r)
                ((card_boundedSubsets_le_mul_pow U (scale.blockedBudget r)).trans
                  (Nat.mul_le_mul_left (scale.blockedBudget r + 1)
                    (Nat.pow_le_pow_left (by omega : max 1 U.card ≤ max 1 Ucap)
                      (scale.blockedBudget r)))))
      _ ≤ (scale.T + 1) / 2 := scale.small_sample
  · exact scale.large_lower
  · simpa using scale.large_upper
  · exact hlargeBudgetSum
  · intro s hs hS
    have hnat : U.card + scale.largeBudget s ≤
        Ucap + scale.largeBudget s :=
      Nat.add_le_add_right hU (scale.largeBudget s)
    have hcast : ((U.card + scale.largeBudget s : ℕ) : ℝ) ≤
        ((Ucap + scale.largeBudget s : ℕ) : ℝ) := by
      exact_mod_cast hnat
    exact hcast.trans_lt (scale.large_rate s hs hS)
  · intro r hrmin hrmax
    exact scale.small_lower r hrmin hrmax
  · intro r hrmin hrmax
    simpa using scale.small_upper r hrmin hrmax
  · intro r hrmin hrmax
    exact scale.small_rate r hrmin hrmax

namespace SmallSimpleAdjusterCandidate

/-- Source-shaped Claim 4.5/4.6 application of correlated Lemma 3.7.

The candidate geometry supplies C1--C5: the seed is the opposite end, `Bᵢ`
is the core plus the selected internal arm, and `Cᵢ` is the globally shortest
connection.  The remaining hypotheses are literal arithmetic bounds on the
common profiles. -/
theorem exists_large_reachingCandidate_ball_of_LM37CorrelatedScale
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (epsilon kappa : ℝ) (hexp : IsLMExpander G epsilon kappa)
    {deleted highDegree protectedSet targetSet : Finset V}
    {separation connectionRadius ballRadius minRadius maxRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
      ¬ Conflict A.1 B.1 highDegree separation))
    (deletedCap Icard M degreeInto : ℕ)
    (scale : LM37CorrelatedScale (Fintype.card V) deletedCap Icard 2
      ballRadius M degreeInto epsilon kappa)
    (hdeleted : deleted.card ≤ deletedCap)
    (hindex : Icard ≤
      (reachingEligibleSubfamily S targetSet connectionRadius).card)
    (hradius : ballRadius + ballRadius ≤ separation)
    (hprotected : deleted ∪ manyNeighborsInto G deleted degreeInto ⊆
      protectedSet)
    (hball : ∀ i :
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      ballAvoidingFrom G
          ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius =
        ballAvoidingFrom G
          ((deleted : Set V) ∪ (highDegree : Set V) ∪
            (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius)
    (hstart : scale.growth 0 < minRadius ^ 2)
    (hstartOne : scale.growth 1 < minRadius ^ 2)
    (hminSize : scale.minSize ≤ minRadius ^ 2)
    (hneighbor : ∀ ell s, 0 < ell → ell ≤ ballRadius →
      scale.growth (ell - 1) < s →
      scale.stepLoss ell + (11 * maxRadius + 1) + 2 * ell ≤
        scale.neighborBudget s)
    (hlargeBudgetSum : ∀
      (J : Finset
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
      (f : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius} → ℕ),
      (∀ i ∈ J, scale.cutoff ≤ f i ∧ f i ≤ scale.D) →
      ∑ i ∈ J, scale.neighborBudget (f i) ≤
        scale.largeBudget (∑ i ∈ J, f i)) :
    ∃ i : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      M ≤ (ballAvoidingFrom G
        ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
          (reachingCandidatePath i : Set V))
        (reachingCandidateSeed i) ballRadius).card := by
  let originalDecAdj : DecidableRel G.Adj := inferInstance
  classical
  let : DecidableRel G.Adj := originalDecAdj
  let I := {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius}
  let Aseed : I → Finset V := fun i ↦ reachingCandidateSeed i
  let Bset : I → Finset V := fun i ↦ reachingCandidateBarrier i
  let Cset : I → Finset V := fun i ↦ reachingCandidatePath i
  apply exists_large_avoiding_ball_of_LM37CorrelatedScale
    G epsilon kappa hexp deleted Aseed Bset Cset deletedCap Icard 2
      ballRadius M degreeInto scale hdeleted
  · simpa [I] using hindex
  · intro i
    dsimp [Aseed]
    rw [card_reachingCandidateSeed]
    have hiradius := i.1.1.min_le
    nlinarith
  · intro i
    have hseed : minRadius ^ 2 ≤ (reachingCandidateSeed i).card := by
      rw [card_reachingCandidateSeed]
      exact Nat.pow_le_pow_left i.1.1.min_le 2
    have hsub := Finset.card_le_card (subset_ballAvoidingFrom G
      ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
        (reachingCandidatePath i : Set V)) (reachingCandidateSeed i) 1)
    exact hstartOne.trans_le (hseed.trans hsub)
  · intro i
    have hseed : minRadius ^ 2 ≤ (reachingCandidateSeed i).card := by
      rw [card_reachingCandidateSeed]
      exact Nat.pow_le_pow_left i.1.1.min_le 2
    have hsub := Finset.card_le_card (subset_ballAvoidingFrom G
      ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
        (reachingCandidatePath i : Set V)) (reachingCandidateSeed i) 1)
    exact hminSize.trans (hseed.trans hsub)
  · intro i
    simpa [Aseed, Bset, Cset] using reachingCandidate_limitedContact_barrier i
  · simpa [I, Aseed, Bset, Cset] using
      pairwiseDisjoint_reachingCandidate_actual_barrier_balls
        (G := G) hpair hradius hball
  · intro i ell hell hellRadius hslow
    dsimp [Bset]
    have hbarrier := card_reachingCandidateBarrier_le i
    have hbudget := hneighbor ell _ hell hellRadius hslow
    have hbarrierMax : (reachingCandidateBarrier i).card ≤
        11 * maxRadius + 1 :=
      hbarrier.trans (Nat.add_le_add_right
        (Nat.mul_le_mul_left 11 i.1.1.le_max) 1)
    have hle : scale.stepLoss ell + (reachingCandidateBarrier i).card +
        2 * ell ≤ scale.stepLoss ell + (11 * maxRadius + 1) + 2 * ell := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_left hbarrierMax (scale.stepLoss ell)) (2 * ell)
    exact hle.trans hbudget
  · intro i v hv
    dsimp [Aseed, Bset, Cset] at hv ⊢
    exact reachingCandidate_degreeInto_deleted_le G i
      (by omega) hprotected (hball i) v hv
  · exact hlargeBudgetSum

/-- Claim 4.5, with every numerical estimate exposed.

If `R` members of the maximal separated family had a short connection to
`highDegree \ deleted`, orient a shortest such connection for each member.
The opposite ends satisfy the correlated Lemma 3.7 hypotheses.  Its large
avoiding ball, together with the first high-degree connection, gives a
genuine target adjuster by attaching two concrete stars.  Hence fewer than
`R` members can be exceptional. -/
theorem card_reachingEligibleSubfamily_lt_of_no_targetAdjuster
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (epsilon kappa : ℝ) (hexp : IsLMExpander G epsilon kappa)
    {deleted highDegree protectedSet targetSet : Finset V}
    {separation connectionRadius minRadius maxRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
      ¬ Conflict A.1 B.1 highDegree separation))
    (targetOrder totalRadius Delta deletedCap R degreeInto : ℕ)
    (scale : LM37CorrelatedScale (Fintype.card V) deletedCap R 2
      connectionRadius targetOrder degreeInto epsilon kappa)
    (hdeleted : deleted.card ≤ deletedCap)
    (hTargetSet : targetSet ⊆ highDegree \ deleted)
    (hHighDegree : ∀ v ∈ highDegree, Delta ≤ G.degree v)
    (hnoTarget : ¬ ∃ A : Adjuster G targetOrder totalRadius 1,
      Disjoint deleted A.verts)
    (hradius : connectionRadius + connectionRadius ≤ separation)
    (hprotected : deleted ∪ manyNeighborsInto G deleted degreeInto ⊆
      protectedSet)
    (hstart : scale.growth 0 < minRadius ^ 2)
    (hstartOne : scale.growth 1 < minRadius ^ 2)
    (hminSize : scale.minSize ≤ minRadius ^ 2)
    (hneighbor : ∀ ell s, 0 < ell → ell ≤ connectionRadius →
      scale.growth (ell - 1) < s →
      scale.stepLoss ell + (11 * maxRadius + 1) + 2 * ell ≤
        scale.neighborBudget s)
    (hlargeBudgetSum : ∀
      (J : Finset
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
      (f : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius} → ℕ),
      (∀ i ∈ J, scale.cutoff ≤ f i ∧ f i ≤ scale.D) →
      ∑ i ∈ J, scale.neighborBudget (f i) ≤
        scale.largeBudget (∑ i ∈ J, f i))
    (hTargetPos : 0 < targetOrder)
    (hRightBudget : targetOrder +
      (deletedCap + 10 * maxRadius + (maxRadius + 1) +
        (connectionRadius + 1)) ≤ Delta)
    (hLeftBudget : targetOrder +
      (deletedCap + 10 * maxRadius + targetOrder) ≤ Delta)
    (hTotalRadius : maxRadius + connectionRadius + 1 ≤ totalRadius) :
    (reachingEligibleSubfamily S targetSet connectionRadius).card < R := by
  by_contra hcard
  have hindex : R ≤
      (reachingEligibleSubfamily S targetSet connectionRadius).card := by
    omega
  have hball : ∀ i :
      {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      ballAvoidingFrom G
          ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) connectionRadius =
        ballAvoidingFrom G
          ((deleted : Set V) ∪ (highDegree : Set V) ∪
            (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) connectionRadius := by
    intro i
    let P := reachingCandidateConnectionData i
    have hfinishHigh : P.finish ∈ highDegree :=
      (Finset.mem_sdiff.1 (hTargetSet P.finish_mem)).1
    have hnoSecond := no_second_highDegree_connection_of_no_targetAdjuster
      G i targetOrder totalRadius Delta deletedCap hTargetSet hHighDegree
        hnoTarget hTargetPos hdeleted hRightBudget hLeftBudget hTotalRadius
    exact reachingCandidate_ball_eq_highDegree_of_no_second i hfinishHigh hnoSecond
  obtain ⟨i, hiLarge⟩ :=
    exists_large_reachingCandidate_ball_of_LM37CorrelatedScale
      G epsilon kappa hexp hpair deletedCap R targetOrder degreeInto scale
        hdeleted hindex hradius hprotected hball hstart hstartOne hminSize
        hneighbor hlargeBudgetSum
  obtain ⟨A, hA⟩ := exists_targetAdjuster_of_large_reachingCandidate_ball
    G i targetOrder totalRadius Delta deletedCap hTargetSet hHighDegree hiLarge
      hTargetPos hdeleted hLeftBudget hTotalRadius (by omega)
  exact hnoTarget ⟨A, hA⟩

/-- Claim 4.6, with every numerical and separation estimate exposed.

Here `S` is a subfamily surviving Claim 4.5, so none of its members has a
short route to `highDegree \ deleted`.  If `R` members reached the auxiliary
expansion `Z`, the second correlated Lemma 3.7 application would enlarge the
opposite end; the preceding concrete expansion-attachment theorem would
then construct the forbidden target adjuster. -/
theorem card_reachingEligibleSubfamily_lt_of_no_targetAdjuster_expansion
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (epsilon kappa : ℝ) (hexp : IsLMExpander G epsilon kappa)
    {deleted highDegree protectedSet targetSet : Finset V}
    {separation connectionRadius ballRadius highRadius minRadius maxRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
      ¬ Conflict A.1 B.1 highDegree separation))
    (targetOrder totalRadius deletedCap R degreeInto farRadius : ℕ)
    (scale : LM37CorrelatedScale (Fintype.card V) deletedCap R 2
      ballRadius targetOrder degreeInto epsilon kappa)
    (hdeleted : deleted.card ≤ deletedCap)
    (hnoTarget : ¬ ∃ A : Adjuster G targetOrder totalRadius 1,
      Disjoint deleted A.verts)
    (hnoHigh : ∀ A ∈ S, ¬ A.1.ReachesAvoidingOwnCore deleted
      (highDegree \ deleted) highRadius)
    (hballHigh : ballRadius ≤ highRadius)
    {center : V} (Z : VertexExpansion G center targetOrder farRadius)
    (hTargetSet : targetSet ⊆ Z.verts)
    (hZWorkspace : ∀ i :
      {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      Disjoint Z.verts
        (deleted ∪ (reachingCandidateConnectionData i).adjusted.core ∪
          ballAvoidingFrom G
            ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
              (reachingCandidatePath i : Set V))
            (reachingCandidateSeed i) ballRadius))
    (hradius : ballRadius + ballRadius ≤ separation)
    (hprotected : deleted ∪ manyNeighborsInto G deleted degreeInto ⊆
      protectedSet)
    (hstart : scale.growth 0 < minRadius ^ 2)
    (hstartOne : scale.growth 1 < minRadius ^ 2)
    (hminSize : scale.minSize ≤ minRadius ^ 2)
    (hneighbor : ∀ ell s, 0 < ell → ell ≤ ballRadius →
      scale.growth (ell - 1) < s →
      scale.stepLoss ell + (11 * maxRadius + 1) + 2 * ell ≤
        scale.neighborBudget s)
    (hlargeBudgetSum : ∀
      (J : Finset
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
      (f : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius} → ℕ),
      (∀ i ∈ J, scale.cutoff ≤ f i ∧ f i ≤ scale.D) →
      ∑ i ∈ J, scale.neighborBudget (f i) ≤
        scale.largeBudget (∑ i ∈ J, f i))
    (hTargetPos : 0 < targetOrder)
    (hLeftRadius : maxRadius + connectionRadius + 2 * farRadius ≤ totalRadius)
    (hRightRadius : maxRadius + ballRadius ≤ totalRadius) :
    (reachingEligibleSubfamily S targetSet connectionRadius).card < R := by
  by_contra hcard
  have hindex : R ≤
      (reachingEligibleSubfamily S targetSet connectionRadius).card := by
    omega
  have hball : ∀ i :
      {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      ballAvoidingFrom G
          ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius =
        ballAvoidingFrom G
          ((deleted : Set V) ∪ (highDegree : Set V) ∪
            (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius := by
    intro i
    have hiS :=
      ((mem_reachingEligibleSubfamily S targetSet connectionRadius i.1).1 i.2).1
    exact reachingCandidate_ball_eq_highDegree_of_no_highConnection i
      (hnoHigh i.1 hiS) hballHigh
  obtain ⟨i, hiLarge⟩ :=
    exists_large_reachingCandidate_ball_of_LM37CorrelatedScale
      G epsilon kappa hexp hpair deletedCap R targetOrder degreeInto scale
        hdeleted hindex hradius hprotected hball hstart hstartOne hminSize
        hneighbor hlargeBudgetSum
  have hfinishZ : (reachingCandidateConnectionData i).finish ∈ Z.verts :=
    hTargetSet (reachingCandidateConnectionData i).finish_mem
  obtain ⟨A, hA⟩ :=
    exists_targetAdjuster_of_large_reachingCandidate_ball_expansion
      i targetOrder totalRadius farRadius Z hfinishZ hiLarge (hZWorkspace i)
        hTargetPos hLeftRadius hRightRadius
  exact hnoTarget ⟨A, hA⟩

/-- The counting step after Claim 4.5.  Starting from `4R` separated
candidates and discarding fewer than `R` that reach the high-degree set,
retain exactly `2R` candidates together with their pointwise non-reachability
certificate. -/
theorem exists_two_mul_nonreaching_subfamily
    {deleted highDegree protectedSet : Finset V}
    {separation highRadius minRadius maxRadius R : ℕ}
    (S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation})
    (hS : 4 * R ≤ S.card)
    (hbad : (reachingEligibleSubfamily S (highDegree \ deleted) highRadius).card < R) :
    ∃ T : Finset
        {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted highDegree protectedSet separation},
      T ⊆ S ∧ T.card = 2 * R ∧
        ∀ A ∈ T, ¬ A.1.ReachesAvoidingOwnCore deleted
          (highDegree \ deleted) highRadius := by
  let bad := reachingEligibleSubfamily S (highDegree \ deleted) highRadius
  have hbadS : bad ⊆ S := by
    intro A hA
    exact ((mem_reachingEligibleSubfamily S (highDegree \ deleted)
      highRadius A).1 hA).1
  obtain ⟨T, hT, hTcard⟩ :=
    exists_two_mul_subfamily_after_discard_lt S bad R hbadS hS (by
      simpa only [bad] using hbad)
  refine ⟨T, hT.trans Finset.sdiff_subset, hTcard, ?_⟩
  intro A hA hreach
  have hAbad : A ∈ bad :=
    (mem_reachingEligibleSubfamily S (highDegree \ deleted) highRadius A).2
      ⟨hT.trans Finset.sdiff_subset hA, hreach⟩
  exact (Finset.mem_sdiff.1 (hT hA)).2 hAbad

/-- The counting step after Claim 4.6.  From the `2R` Claim 4.5 survivors,
discard the fewer than `R` candidates that reach `targetSet`, and retain an
exact `R`-element family carrying both non-reachability certificates. -/
theorem exists_nonreaching_subfamily_card_eq
    {deleted highDegree protectedSet targetSet : Finset V}
    {separation highRadius targetRadius minRadius maxRadius R : ℕ}
    (S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation})
    (hScard : S.card = 2 * R)
    (hnoHigh : ∀ A ∈ S, ¬ A.1.ReachesAvoidingOwnCore deleted
      (highDegree \ deleted) highRadius)
    (hbad : (reachingEligibleSubfamily S targetSet targetRadius).card < R) :
    ∃ T : Finset
        {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted highDegree protectedSet separation},
      T ⊆ S ∧ T.card = R ∧
        (∀ A ∈ T, ¬ A.1.ReachesAvoidingOwnCore deleted
          (highDegree \ deleted) highRadius) ∧
        ∀ A ∈ T, ¬ A.1.ReachesAvoidingOwnCore deleted
          targetSet targetRadius := by
  let bad := reachingEligibleSubfamily S targetSet targetRadius
  have hbadS : bad ⊆ S := by
    intro A hA
    exact ((mem_reachingEligibleSubfamily S targetSet targetRadius A).1 hA).1
  have hcount : R + bad.card ≤ S.card := by
    have hbad' : bad.card < R := by simpa only [bad] using hbad
    omega
  obtain ⟨T, hT, hTcard⟩ :=
    exists_subset_sdiff_card_eq_of_add_card_le S bad R hbadS hcount
  refine ⟨T, hT.trans Finset.sdiff_subset, hTcard, ?_, ?_⟩
  · intro A hA
    exact hnoHigh A (hT.trans Finset.sdiff_subset hA)
  · intro A hA hreach
    have hAbad : A ∈ bad :=
      (mem_reachingEligibleSubfamily S targetSet targetRadius A).2
        ⟨hT.trans Finset.sdiff_subset hA, hreach⟩
    exact (Finset.mem_sdiff.1 (hT hA)).2 hAbad

end SmallSimpleAdjusterCandidate

/-- Concrete finite Liu--Montgomery Lemma 4.2.  The simultaneous expansions
come from the source matrix form of Lemma 3.11; `scale` contains only the two
subsequent Lemma 3.4 connector estimates. -/
theorem liuMontgomery_lemma4_2_finite [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Bipartition G) (epsilon kappa : ℝ)
    (hexp : IsLMExpander G epsilon kappa)
    (d D Delta ell₀ expansionRadius m protectedCard : ℕ)
    {c : V} (C : G.Walk c c) (hC : IsShortestCycle C)
    (x₁ x₂ : V) (hx₁x₂ : x₁ ≠ x₂)
    (hx₁C : x₁ ∉ C.support) (hx₂C : x₂ ∉ C.support)
    (forbidden : Finset V) (hforbidden : forbidden.card ≤ 1)
    (hforbiddenProtected : forbidden.card ≤ protectedCard)
    (hforbiddenCycle : Disjoint forbidden C.support.toFinset)
    (hx₁forbidden : x₁ ∉ forbidden) (hx₂forbidden : x₂ ∉ forbidden)
    (hmin : ∀ v : V, d - 1 ≤ G.degree v)
    (hfamilyRadius : 5 * expansionRadius ≤ m)
    (num : LM311Numerics epsilon kappa (Fintype.card V) 4 d (m ^ 3 * D)
      Delta ell₀ expansionRadius protectedCard)
    (scale : LM42ConnectorScale (Fintype.card V) d D m C.length epsilon kappa) :
    ∃ A : Adjuster G D m 1,
      A.leftRoot = x₁ ∧ A.rightRoot = x₂ ∧ C.support.toFinset ⊆ A.core ∧
        Disjoint forbidden A.verts := by
  let originalDecAdj : DecidableRel G.Adj := inferInstance
  classical
  let : DecidableRel G.Adj := originalDecAdj
  obtain ⟨half, z, short, long, hClen, hshort, hlong,
    hshortLen, hlongLen, hshortSupport, hlongSupport⟩ :=
      B.exists_cycle_arcs_diff_two C hC.1
  have hhalf : 2 ≤ half := by
    have := hC.1.three_le_length
    omega
  have hcz : c ≠ z := by
    intro h
    have hnil : short.Nil := hshort.nil_iff_eq.2 h
    have hzero := hnil.length_eq_zero
    omega
  have hcC : c ∈ C.support := C.start_mem_support
  have hzC : z ∈ C.support := hshortSupport z short.end_mem_support
  have hx₁c : x₁ ≠ c := fun h ↦ hx₁C (h ▸ hcC)
  have hx₂c : x₂ ≠ c := fun h ↦ hx₂C (h ▸ hcC)
  have hx₁z : x₁ ≠ z := fun h ↦ hx₁C (h ▸ hzC)
  have hx₂z : x₂ ≠ z := fun h ↦ hx₂C (h ▸ hzC)
  have hcForbidden : c ∉ forbidden := fun hc ↦
    Finset.disjoint_left.1 hforbiddenCycle hc (by simpa using hcC)
  have hzForbidden : z ∉ forbidden := fun hz ↦
    Finset.disjoint_left.1 hforbiddenCycle hz (by simpa using hzC)
  have hprotectedCard : C.support.toFinset.card ≤ C.length + 1 := by
    simpa [C.length_support] using List.toFinset_card_le C.support
  let roots : Fin 6 → V := lemma42Roots x₁ x₂ c z
  let orders : Fin 6 → ℕ := lemma42Orders D m
  have hmPos : 0 < m := lt_of_lt_of_le Nat.zero_lt_two scale.two_le_m
  have hDleCube : D ≤ m ^ 3 * D := by
    have hpow : 1 ≤ m ^ 3 := Nat.pow_pos hmPos
    simpa using Nat.mul_le_mul_right D hpow
  have hSquareLeCube : m ^ 2 * D ≤ m ^ 3 * D := by
    have hpow : m ^ 2 ≤ m ^ 3 :=
      Nat.pow_le_pow_right hmPos (by omega)
    exact Nat.mul_le_mul_right D hpow
  have hSquarePos : 0 < m ^ 2 * D :=
    Nat.mul_pos (Nat.pow_pos hmPos) scale.D_pos
  have hCubePos : 0 < m ^ 3 * D :=
    Nat.mul_pos (Nat.pow_pos hmPos) scale.D_pos
  let rootEmbedding : Fin 4 ↪ V :=
    lemma42RootEmbedding x₁ x₂ c z hx₁x₂ hx₁c hx₁z hx₂c hx₂z hcz
  let matrixOrders : Fin 4 → Fin 4 → ℕ := lemma42MatrixOrders D m
  have hmatrixPos : ∀ i j, 0 < matrixOrders i j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [matrixOrders, lemma42MatrixOrders, scale.D_pos, hSquarePos, hCubePos]
  have hmatrixLe : ∀ i j, matrixOrders i j ≤ m ^ 3 * D := by
    have hOneLe : 1 ≤ m ^ 3 * D := Nat.one_le_iff_ne_zero.2 (Nat.ne_of_gt hCubePos)
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [matrixOrders, lemma42MatrixOrders, hDleCube, hSquareLeCube, hOneLe]
  obtain ⟨F⟩ := liuMontgomery_lemma3_11_source G B epsilon kappa hexp
    4 d (m ^ 3 * D) Delta ell₀ expansionRadius protectedCard
    forbidden hforbiddenProtected C hC rootEmbedding matrixOrders hmin
    hmatrixPos hmatrixLe num
  let E : ∀ i : Fin 6,
      VertexExpansion G (roots i) (orders i) m := fun i ↦
    (F.lemma42Selected x₁ x₂ c z hx₁x₂ hx₁c hx₁z hx₂c hx₂z hcz D m i).radiusMono
      hfamilyRadius
  have hEreserved : ∀ i : Fin 6,
      Disjoint ((E i).verts \ {roots i})
        ((forbidden ∪ C.support.toFinset) ∪ Finset.univ.image rootEmbedding) := by
    intro i
    simpa [E, roots, rootEmbedding] using
      F.lemma42Selected_avoids_reserved x₁ x₂ c z hx₁x₂ hx₁c hx₁z
        hx₂c hx₂z hcz D m i
  have hEprotectedLocal : ∀ i : Fin 6,
      Disjoint ((E i).verts \ {roots i}) (forbidden ∪ C.support.toFinset) :=
    fun i ↦ (hEreserved i).mono_right Finset.subset_union_left
  have hErootsLocal : ∀ i : Fin 6,
      Disjoint ((E i).verts \ {roots i}) (Finset.univ.image roots) := by
    intro i
    apply (hEreserved i).mono_right
    intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨j, -, rfl⟩ := hv
    apply Finset.mem_union_right
    rw [Finset.mem_image]
    exact ⟨(lemma42MatrixIndex j).1, Finset.mem_univ _, by
      simp [roots, rootEmbedding]⟩
  have hEpairLocal : ∀ i j : Fin 6, i ≠ j →
      Disjoint ((E i).verts \ {roots i}) ((E j).verts \ {roots j}) := by
    intro i j hij
    simpa [E, roots] using
      F.lemma42Selected_pairwise_disjoint x₁ x₂ c z hx₁x₂ hx₁c hx₁z
        hx₂c hx₂z hcz D m i j hij
  have hEforbidden : ∀ i : Fin 6,
      Disjoint ((E i).verts \ {roots i}) forbidden := fun i ↦
    (hEprotectedLocal i).mono_right Finset.subset_union_left
  have hEcycle : ∀ i : Fin 6,
      Disjoint ((E i).verts \ {roots i}) C.support.toFinset := fun i ↦
    (hEprotectedLocal i).mono_right Finset.subset_union_right
  let E₁₁ := E (0 : Fin 6)
  let E₁₂ := E (1 : Fin 6)
  let E₂₁ := E (2 : Fin 6)
  let E₂₂ := E (3 : Fin 6)
  let E₃₁ := E (4 : Fin 6)
  let E₄₁ := E (5 : Fin 6)
  have meet (i j : Fin 6) (hij : i ≠ j) {v : V}
      (hvi : v ∈ (E i).verts) (hvj : v ∈ (E j).verts) :
      v = roots i :=
    mem_eq_root_of_mem_expansions E hErootsLocal hEpairLocal hij hvi hvj
  have meetC (i : Fin 6) {v : V} (hvi : v ∈ (E i).verts)
      (hvC : v ∈ C.support.toFinset) : v = roots i :=
    mem_eq_root_of_mem_expansion_protected E hEcycle hvi hvC
  have hfinalEnds : Disjoint E₁₁.verts E₂₁.verts := by
    rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    have hv := meet (0 : Fin 6) (2 : Fin 6) (by decide) hv₁ hv₂
    have hv' := meet (2 : Fin 6) (0 : Fin 6) (by decide) hv₂ hv₁
    simp [roots, lemma42Roots] at hv hv'
    exact hx₁x₂ (hv.symm.trans hv')
  let W₁ : Finset V :=
    (forbidden ∪ C.support.toFinset ∪ E₁₁.verts ∪ E₂₁.verts ∪
      E₂₂.verts ∪ E₄₁.verts) \ {x₁, c}
  have source_disjoint_W₁ (i : Fin 6) (hi : i = 1 ∨ i = 4) :
      Disjoint (E i).verts W₁ := by
    rw [Finset.disjoint_left]
    intro v hvi hvW
    obtain ⟨hvUnion, hvnot⟩ := Finset.mem_sdiff.1 hvW
    simp only [Finset.mem_union] at hvUnion
    rcases hvUnion with ((((hvForbidden | hvC) | hv₁₁) | hv₂₁) |
      hv₂₂) | hv₄₁
    · have hv := mem_eq_root_of_mem_expansion_protected E hEprotectedLocal hvi
          (Finset.mem_union_left _ hvForbidden)
      rcases hi with rfl | rfl <;>
        simp [roots, lemma42Roots] at hv <;> subst v <;> simp at hvnot
    · have hv := meetC i hvi hvC
      rcases hi with rfl | rfl <;>
        simp [roots, lemma42Roots] at hv <;> subst v <;> simp at hvnot
    · have hv := meet i (0 : Fin 6) (by rcases hi with rfl | rfl <;> decide)
          hvi hv₁₁
      rcases hi with rfl | rfl <;>
        simp [roots, lemma42Roots] at hv <;> subst v <;> simp at hvnot
    · have hv := meet i (2 : Fin 6) (by rcases hi with rfl | rfl <;> decide)
          hvi hv₂₁
      rcases hi with rfl | rfl <;>
        simp [roots, lemma42Roots] at hv <;> subst v <;> simp at hvnot
    · have hv := meet i (3 : Fin 6) (by rcases hi with rfl | rfl <;> decide)
          hvi hv₂₂
      rcases hi with rfl | rfl <;>
        simp [roots, lemma42Roots] at hv <;> subst v <;> simp at hvnot
    · have hv := meet i (5 : Fin 6) (by rcases hi with rfl | rfl <;> decide)
          hvi hv₄₁
      rcases hi with rfl | rfl <;>
        simp [roots, lemma42Roots] at hv <;> subst v <;> simp at hvnot
  have hW₁card : W₁.card ≤ scale.cubeWorkspace := by
    have hsdiff : W₁.card ≤
        (forbidden ∪ C.support.toFinset ∪ E₁₁.verts ∪ E₂₁.verts ∪
          E₂₂.verts ∪ E₄₁.verts).card := by
      exact Finset.card_le_card Finset.sdiff_subset
    have h₀ := Finset.card_union_le forbidden C.support.toFinset
    have h₁ := Finset.card_union_le (forbidden ∪ C.support.toFinset) E₁₁.verts
    have h₂ := Finset.card_union_le
      (forbidden ∪ C.support.toFinset ∪ E₁₁.verts) E₂₁.verts
    have h₃ := Finset.card_union_le
      (forbidden ∪ C.support.toFinset ∪ E₁₁.verts ∪ E₂₁.verts)
        E₂₂.verts
    have h₄ := Finset.card_union_le
      (forbidden ∪ C.support.toFinset ∪ E₁₁.verts ∪ E₂₁.verts ∪
        E₂₂.verts) E₄₁.verts
    have hunion :
        (forbidden ∪ C.support.toFinset ∪ E₁₁.verts ∪ E₂₁.verts ∪
          E₂₂.verts ∪ E₄₁.verts).card ≤
          forbidden.card + C.support.toFinset.card + E₁₁.verts.card +
            E₂₁.verts.card + E₂₂.verts.card + E₄₁.verts.card := by
      omega
    calc
      W₁.card ≤
          (forbidden ∪ C.support.toFinset ∪ E₁₁.verts ∪ E₂₁.verts ∪
            E₂₂.verts ∪ E₄₁.verts).card := hsdiff
      _ ≤ forbidden.card + C.support.toFinset.card + E₁₁.verts.card +
          E₂₁.verts.card + E₂₂.verts.card + E₄₁.verts.card := hunion
      _ = forbidden.card + C.support.toFinset.card + D + D +
          m ^ 2 * D + m ^ 2 * D := by
        simp [E₁₁, E₂₁, E₂₂, E₄₁, orders, lemma42Orders,
          VertexExpansion.card_verts]
      _ ≤ C.length + 2 + 2 * D + 2 * (m ^ 2 * D) := by omega
      _ ≤ scale.cubeWorkspace := scale.connector_workspace_large
  obtain ⟨P, hP, hPavoid, hPlen⟩ :=
    exists_expansion_root_connector_of_LM42GrowthSchedule G
      E₁₂ E₃₁ W₁ (source_disjoint_W₁ 1 (Or.inl rfl))
      (source_disjoint_W₁ 4 (Or.inr rfl)) epsilon kappa hexp
      (d - 1) hmin hW₁card
      (by simpa [E₁₂, orders, lemma42Orders, VertexExpansion.card_verts] using
        scale.cubeSeed)
      (by simpa [E₃₁, orders, lemma42Orders, VertexExpansion.card_verts] using
        scale.cubeSeed)
      scale.cubeGrowth
  have hPlen3 : P.length ≤ 3 * m := by
    have := scale.cube_path_radius
    omega
  have hE₂₂W₁ : E₂₂.verts ⊆ W₁ := by
    intro v hv
    apply Finset.mem_sdiff.2
    refine ⟨by simp [W₁, hv], ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl)
    · have h := meet (3 : Fin 6) (0 : Fin 6) (by decide) hv E₁₁.root_mem
      simp [roots, lemma42Roots] at h
      exact hx₁x₂ h
    · have h := meetC (3 : Fin 6) hv (by simpa using hcC)
      simp [roots, lemma42Roots] at h
      exact hx₂c h.symm
  have hE₄₁W₁ : E₄₁.verts ⊆ W₁ := by
    intro v hv
    apply Finset.mem_sdiff.2
    refine ⟨by simp [W₁, hv], ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl)
    · have h := meet (5 : Fin 6) (0 : Fin 6) (by decide) hv E₁₁.root_mem
      simp [roots, lemma42Roots] at h
      exact hx₁z h
    · have h := meetC (5 : Fin 6) hv (by simpa using hcC)
      simp [roots, lemma42Roots] at h
      exact hcz h
  have hPdisjE₂₂ : Disjoint P.support.toFinset E₂₂.verts := by
    rw [Finset.disjoint_left]
    intro v hvP hvE
    exact hPavoid v (by simpa using hvP) (hE₂₂W₁ hvE)
  have hPdisjE₄₁ : Disjoint P.support.toFinset E₄₁.verts := by
    rw [Finset.disjoint_left]
    intro v hvP hvE
    exact hPavoid v (by simpa using hvP) (hE₄₁W₁ hvE)
  let W₂ : Finset V :=
    (forbidden ∪ C.support.toFinset ∪ P.support.toFinset ∪ E₁₁.verts ∪
      E₂₁.verts) \ {x₂, z}
  have source_disjoint_W₂ (i : Fin 6) (hi : i = 3 ∨ i = 5) :
      Disjoint (E i).verts W₂ := by
    rw [Finset.disjoint_left]
    intro v hvi hvW
    obtain ⟨hvUnion, hvnot⟩ := Finset.mem_sdiff.1 hvW
    simp only [Finset.mem_union] at hvUnion
    rcases hvUnion with (((hvForbidden | hvC) | hvPmem) | hv₁₁) | hv₂₁
    · have hv := mem_eq_root_of_mem_expansion_protected E hEprotectedLocal hvi
          (Finset.mem_union_left _ hvForbidden)
      rcases hi with rfl | rfl <;>
        simp [roots, lemma42Roots] at hv <;> subst v <;> simp at hvnot
    · have hv := meetC i hvi hvC
      rcases hi with rfl | rfl <;>
        simp [roots, lemma42Roots] at hv <;> subst v <;> simp at hvnot
    · rcases hi with rfl | rfl
      · exact (Finset.disjoint_left.1 hPdisjE₂₂ hvPmem hvi).elim
      · exact (Finset.disjoint_left.1 hPdisjE₄₁ hvPmem hvi).elim
    · have hv := meet i (0 : Fin 6) (by rcases hi with rfl | rfl <;> decide)
          hvi hv₁₁
      rcases hi with rfl | rfl <;>
        simp [roots, lemma42Roots] at hv <;> subst v <;> simp at hvnot
    · have hv := meet i (2 : Fin 6) (by rcases hi with rfl | rfl <;> decide)
          hvi hv₂₁
      rcases hi with rfl | rfl <;>
        simp [roots, lemma42Roots] at hv <;> subst v <;> simp at hvnot
  have hW₂card : W₂.card ≤ scale.squareWorkspace := by
    have hsdiff : W₂.card ≤
        (forbidden ∪ C.support.toFinset ∪ P.support.toFinset ∪ E₁₁.verts ∪
          E₂₁.verts).card := Finset.card_le_card Finset.sdiff_subset
    have h₀ := Finset.card_union_le forbidden C.support.toFinset
    have h₁ := Finset.card_union_le (forbidden ∪ C.support.toFinset) P.support.toFinset
    have h₂ := Finset.card_union_le
      (forbidden ∪ C.support.toFinset ∪ P.support.toFinset) E₁₁.verts
    have h₃ := Finset.card_union_le
      (forbidden ∪ C.support.toFinset ∪ P.support.toFinset ∪ E₁₁.verts)
        E₂₁.verts
    have hPcard : P.support.toFinset.card ≤ P.length + 1 := by
      simpa [P.length_support] using List.toFinset_card_le P.support
    have hunion :
        (forbidden ∪ C.support.toFinset ∪ P.support.toFinset ∪ E₁₁.verts ∪
          E₂₁.verts).card ≤ forbidden.card + C.support.toFinset.card +
            P.support.toFinset.card + E₁₁.verts.card + E₂₁.verts.card := by
      omega
    calc
      W₂.card ≤
          (forbidden ∪ C.support.toFinset ∪ P.support.toFinset ∪ E₁₁.verts ∪
            E₂₁.verts).card := hsdiff
      _ ≤ forbidden.card + C.support.toFinset.card + P.support.toFinset.card +
          E₁₁.verts.card + E₂₁.verts.card := hunion
      _ = forbidden.card + C.support.toFinset.card + P.support.toFinset.card +
          D + D := by
        simp [E₁₁, E₂₁, orders, lemma42Orders, VertexExpansion.card_verts]
      _ ≤ C.length + 2 + (3 * m + 1) + 2 * D := by omega
      _ ≤ scale.squareWorkspace := scale.connector_workspace_path
  obtain ⟨Q, hQ, hQavoid, hQlen⟩ :=
    exists_expansion_root_connector_of_LM42GrowthSchedule G
      E₂₂ E₄₁ W₂ (source_disjoint_W₂ 3 (Or.inl rfl))
      (source_disjoint_W₂ 5 (Or.inr rfl)) epsilon kappa hexp
      (d - 1) hmin hW₂card
      (by simpa [E₂₂, orders, lemma42Orders, VertexExpansion.card_verts] using
        scale.squareSeed)
      (by simpa [E₄₁, orders, lemma42Orders, VertexExpansion.card_verts] using
        scale.squareSeed)
      scale.squareGrowth
  have hQlen3 : Q.length ≤ 3 * m := by
    have := scale.square_path_radius
    omega
  have hx₂W₁ : x₂ ∈ W₁ := by
    apply Finset.mem_sdiff.2
    refine ⟨?_, ?_⟩
    · apply Finset.mem_union_left E₄₁.verts
      apply Finset.mem_union_left E₂₂.verts
      exact Finset.mem_union_right _ E₂₁.root_mem
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hx₁x₂.symm, hx₂c⟩
  have hzW₁ : z ∈ W₁ := by
    apply Finset.mem_sdiff.2
    refine ⟨Finset.mem_union_right _ E₄₁.root_mem, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hx₁z.symm, hcz.symm⟩
  have hPnotx₂ : x₂ ∉ P.support := fun h ↦ hPavoid x₂ h hx₂W₁
  have hPnotz : z ∉ P.support := fun h ↦ hPavoid z h hzW₁
  have hPsubsetW₂ : P.support.toFinset ⊆ W₂ := by
    intro v hv
    apply Finset.mem_sdiff.2
    refine ⟨by simp [W₂, hv], ?_⟩
    intro hvRoot
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvRoot
    rcases hvRoot with hvx₂ | hvz
    · exact hPnotx₂ (by simpa [hvx₂] using hv)
    · exact hPnotz (by simpa [hvz] using hv)
  have hPQ : P.support.Disjoint Q.support := by
    rw [List.disjoint_left]
    intro v hvP hvQ
    exact hQavoid v hvQ (hPsubsetW₂ (by simpa using hvP))
  have hPcycle : ∀ v ∈ P.support, v ∈ C.support → v = c := by
    intro v hvP hvC
    by_contra hvc
    have hvx₁ : v ≠ x₁ := fun hv ↦ hx₁C (hv ▸ hvC)
    have hvW : v ∈ W₁ := by
      apply Finset.mem_sdiff.2
      exact ⟨by simp [W₁, hvC], by simp [hvx₁, hvc]⟩
    exact hPavoid v hvP hvW
  have hQcycle : ∀ v ∈ Q.support, v ∈ C.support → v = z := by
    intro v hvQ hvC
    by_contra hvz
    have hvx₂ : v ≠ x₂ := fun hv ↦ hx₂C (hv ▸ hvC)
    have hvW : v ∈ W₂ := by
      apply Finset.mem_sdiff.2
      exact ⟨by simp [W₂, hvC], by simp [hvx₂, hvz]⟩
    exact hQavoid v hvQ hvW
  have hE₂₁W₁ : E₂₁.verts ⊆ W₁ := by
    intro v hv
    apply Finset.mem_sdiff.2
    refine ⟨by simp [W₁, hv], ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl)
    · exact (Finset.disjoint_left.1 hfinalEnds E₁₁.root_mem hv).elim
    · have h := meetC (2 : Fin 6) hv (by simpa using hcC)
      simp [roots, lemma42Roots] at h
      exact hx₂c h.symm
  have hPdisjE₂₁ : Disjoint P.support.toFinset E₂₁.verts := by
    rw [Finset.disjoint_left]
    intro v hvP hvE
    exact hPavoid v (by simpa using hvP) (hE₂₁W₁ hvE)
  have hE₁₁W₂ : E₁₁.verts ⊆ W₂ := by
    intro v hv
    apply Finset.mem_sdiff.2
    refine ⟨by simp [W₂, hv], ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl)
    · exact (Finset.disjoint_left.1 hfinalEnds hv E₂₁.root_mem).elim
    · have h := meetC (0 : Fin 6) hv (by simpa using hzC)
      simp [roots, lemma42Roots] at h
      exact hx₁z h.symm
  have hQdisjE₁₁ : Disjoint Q.support.toFinset E₁₁.verts := by
    rw [Finset.disjoint_left]
    intro v hvQ hvE
    exact hQavoid v (by simpa using hvQ) (hE₁₁W₂ hvE)
  have hQE₂root : ∀ v ∈ Q.support, v ∈ E₂₁.verts → v = x₂ := by
    intro v hvQ hvE
    by_contra hvx₂
    have hvz : v ≠ z := by
      intro hv
      subst v
      have h := meetC (2 : Fin 6) hvE (by simpa using hzC)
      simp [roots, lemma42Roots] at h
      exact hx₂z h.symm
    have hvW : v ∈ W₂ := by
      apply Finset.mem_sdiff.2
      exact ⟨by simp [W₂, hvE], by simp [hvx₂, hvz]⟩
    exact hQavoid v hvQ hvW
  have hPshort : P.support.Disjoint short.support.tail := by
    rw [List.disjoint_left]
    intro v hvP hvS
    have hvC := hshortSupport v (List.tail_subset _ hvS)
    have hvc := hPcycle v hvP hvC
    subst v
    have hn := hshort.support_nodup
    rw [← short.cons_tail_support] at hn
    exact hn.notMem hvS
  have hPlong : P.support.Disjoint long.support.tail := by
    rw [List.disjoint_left]
    intro v hvP hvS
    have hvC := hlongSupport v (List.tail_subset _ hvS)
    have hvc := hPcycle v hvP hvC
    subst v
    have hn := hlong.support_nodup
    rw [← long.cons_tail_support] at hn
    exact hn.notMem hvS
  have spliceRight (R : G.Walk c z) (hRsupport : ∀ v ∈ R.support, v ∈ C.support) :
      (P.support ++ R.support.tail).Disjoint Q.reverse.support.tail := by
    rw [List.disjoint_left]
    intro v hvLeft hvQtail
    have hvQ : v ∈ Q.support := by
      have : v ∈ Q.reverse.support := List.tail_subset _ hvQtail
      simpa [Walk.support_reverse] using this
    rcases List.mem_append.1 hvLeft with hvP | hvR
    · exact (List.disjoint_left.1 hPQ) hvP hvQ
    · have hvC := hRsupport v (List.tail_subset _ hvR)
      have hvz := hQcycle v hvQ hvC
      subst v
      have hn := hQ.reverse.support_nodup
      rw [← Q.reverse.cons_tail_support] at hn
      exact hn.notMem hvQtail
  have hPshortQ := spliceRight short hshortSupport
  have hPlongQ := spliceRight long hlongSupport
  have hcycleLeft : Disjoint C.support.toFinset E₁₁.verts := by
    rw [Finset.disjoint_left]
    intro v hvC hvE
    have h := meetC (0 : Fin 6) hvE hvC
    simp [roots, lemma42Roots] at h
    exact hx₁C (by simpa [h] using hvC)
  have hcycleRight : Disjoint C.support.toFinset E₂₁.verts := by
    rw [Finset.disjoint_left]
    intro v hvC hvE
    have h := meetC (2 : Fin 6) hvE hvC
    simp [roots, lemma42Roots] at h
    exact hx₂C (by simpa [h] using hvC)
  have hPE₁root : ∀ v ∈ P.support, v ∈ E₁₁.verts → v = x₁ := by
    intro v hvP hvE
    by_contra hvx₁
    have hvc : v ≠ c := by
      intro hv
      subst v
      exact (Finset.disjoint_left.1 hcycleLeft (by simpa using hcC) hvE).elim
    have hvW : v ∈ W₁ := by
      apply Finset.mem_sdiff.2
      exact ⟨by simp [W₁, hvE], by simp [hvx₁, hvc]⟩
    exact hPavoid v hvP hvW
  have hcoreLeft : Disjoint (cycleSpliceCore P Q C) E₁₁.verts := by
    rw [Finset.disjoint_left]
    intro v hvCore hvE
    obtain ⟨hvUnion, hvRoots⟩ := Finset.mem_sdiff.1 hvCore
    simp only [Finset.mem_union] at hvUnion
    rcases hvUnion with (hvP | hvC) | hvQ
    · have hv := hPE₁root v (by simpa using hvP) hvE
      subst v
      exact hvRoots (Finset.mem_insert_self x₁ {x₂})
    · exact (Finset.disjoint_left.1 hcycleLeft hvC hvE).elim
    · exact (Finset.disjoint_left.1 hQdisjE₁₁ hvQ hvE).elim
  have hcoreRight : Disjoint (cycleSpliceCore P Q C) E₂₁.verts := by
    rw [Finset.disjoint_left]
    intro v hvCore hvE
    obtain ⟨hvUnion, hvRoots⟩ := Finset.mem_sdiff.1 hvCore
    simp only [Finset.mem_union] at hvUnion
    rcases hvUnion with (hvP | hvC) | hvQ
    · exact (Finset.disjoint_left.1 hPdisjE₂₁ hvP hvE).elim
    · exact (Finset.disjoint_left.1 hcycleRight hvC hvE).elim
    · have hv := hQE₂root v (by simpa using hvQ) hvE
      subst v
      exact hvRoots (Finset.mem_insert_of_mem (Finset.mem_singleton_self x₂))
  have hcoreCard : (cycleSpliceCore P Q C).card ≤ 10 * m :=
    cycleSpliceCore_card_le_ten_mul P Q C scale.two_le_m hPlen3 hQlen3
      scale.cycle_length
  have expansion_disjoint_forbidden (i : Fin 6) (hroot : roots i ∉ forbidden) :
      Disjoint forbidden (E i).verts := by
    rw [Finset.disjoint_left]
    intro v hvF hvE
    by_cases hvroot : v = roots i
    · exact hroot (hvroot ▸ hvF)
    · exact (Finset.disjoint_left.1 (hEforbidden i)
        (by simpa using ⟨hvE, hvroot⟩) hvF).elim
  have hleftForbidden : Disjoint forbidden E₁₁.verts :=
    expansion_disjoint_forbidden 0 (by simpa [roots, lemma42Roots] using hx₁forbidden)
  have hrightForbidden : Disjoint forbidden E₂₁.verts :=
    expansion_disjoint_forbidden 2 (by simpa [roots, lemma42Roots] using hx₂forbidden)
  have hcoreForbidden : Disjoint forbidden (cycleSpliceCore P Q C) := by
    rw [Finset.disjoint_left]
    intro v hvF hvCore
    obtain ⟨hvUnion, -⟩ := Finset.mem_sdiff.1 hvCore
    simp only [Finset.mem_union] at hvUnion
    rcases hvUnion with (hvP | hvC) | hvQ
    · have hvW : v ∈ W₁ := by
        apply Finset.mem_sdiff.2
        refine ⟨by simp [W₁, hvF], ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact fun h ↦ h.elim (fun hv ↦ hx₁forbidden (hv ▸ hvF))
          (fun hv ↦ hcForbidden (hv ▸ hvF))
      exact hPavoid v (by simpa using hvP) hvW
    · exact (Finset.disjoint_left.1 hforbiddenCycle hvF hvC).elim
    · have hvW : v ∈ W₂ := by
        apply Finset.mem_sdiff.2
        refine ⟨by simp [W₂, hvF], ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact fun h ↦ h.elim (fun hv ↦ hx₂forbidden (hv ▸ hvF))
          (fun hv ↦ hzForbidden (hv ▸ hvF))
      exact hQavoid v (by simpa using hvQ) hvW
  let A : Adjuster G D m 1 := simpleAdjusterOfCycleSplice
    E₁₁ E₂₁ C P Q short long hP hQ hshort hlong
    (by omega) hshortLen hlongLen hshortSupport hlongSupport
    hPshort hPshortQ hPlong hPlongQ hcoreLeft hcoreRight hfinalEnds hcoreCard
  refine ⟨A, rfl, rfl, ?_, ?_⟩
  intro v hvC
  apply Finset.mem_sdiff.2
  refine ⟨by simp [cycleSpliceCore, hvC], ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton]
  intro hvRoots
  rcases hvRoots with hv₁ | hv₂
  · subst v
    apply hx₁C
    exact List.mem_toFinset.1 hvC
  · subst v
    apply hx₂C
    exact List.mem_toFinset.1 hvC
  rw [Finset.disjoint_left]
  intro v hvF hvA
  change v ∈ E₁₁.verts ∪ E₂₁.verts ∪ cycleSpliceCore P Q C at hvA
  simp only [Finset.mem_union] at hvA
  rcases hvA with (hvLeft | hvRight) | hvCore
  · exact (Finset.disjoint_left.1 hleftForbidden hvF hvLeft).elim
  · exact (Finset.disjoint_left.1 hrightForbidden hvF hvRight).elim
  · exact (Finset.disjoint_left.1 hcoreForbidden hvF hvCore).elim

end Erdos63
