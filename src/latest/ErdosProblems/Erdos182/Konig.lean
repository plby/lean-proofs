import Mathlib.Combinatorics.SimpleGraph.Hall

/-!
# König's matching argument for regular bipartite graphs

This file contains the part of König's line-colouring theorem needed in the
formalization of Erdős Problem 182.  Namely, every finite positive regular
bipartite graph has a perfect matching, and consequently a `q`-regular
bipartite graph has a spanning `k`-regular subgraph for every `k ≤ q`.

The proof of the perfect-matching lemma verifies Hall's condition by counting
the edges between a set `u` on one side and its neighbourhood.
-/

open scoped Classical

namespace Erdos182

namespace Konig

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [instG : DecidableRel G.Adj]
  {s t u : Set V} {q k : ℕ}

/-- Hall's inequality on one side of a positive regular bipartite graph. -/
private lemma hall_side (hq : 0 < q) (hreg : G.IsRegularOfDegree q)
    (hbip : G.IsBipartiteWith s t) (hu : u ⊆ s) :
    u.ncard ≤ (⋃ v ∈ u, G.neighborSet v).ncard := by
  let N : Set V := ⋃ v ∈ u, G.neighborSet v
  let B : SimpleGraph V := G.between u N
  have hN : N ⊆ t := by
    intro w hw
    simp only [N, Set.mem_iUnion] at hw
    obtain ⟨v, hv, hw⟩ := hw
    exact hbip.mem_of_mem_adj (hu hv) hw
  have hud : Disjoint u N :=
    Set.disjoint_of_subset hu hN hbip.disjoint
  have hbB : B.IsBipartiteWith u N := by
    exact SimpleGraph.between_isBipartiteWith hud
  have hdeg_left (v : V) (hv : v ∈ u) : B.degree v = q := by
    have hn : B.neighborSet v = G.neighborSet v := by
      ext w
      constructor
      · intro hw
        exact (SimpleGraph.between_adj.mp hw).1
      · intro hw
        apply SimpleGraph.between_adj.mpr
        refine ⟨hw, Or.inl ⟨hv, ?_⟩⟩
        simp only [N, Set.mem_iUnion]
        exact ⟨v, hv, hw⟩
    have hnf : B.neighborFinset v = G.neighborFinset v := by
      ext w
      rw [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
      exact Set.ext_iff.mp hn w
    rw [SimpleGraph.degree, hnf]
    exact hreg.degree_eq v
  have hdeg_right (w : V) (_hw : w ∈ N) : B.degree w ≤ q := by
    exact (B.degree_le_of_le SimpleGraph.between_le).trans_eq (hreg.degree_eq w)
  have hcount : q * u.ncard ≤ q * N.ncard := by
    have hbBfin : B.IsBipartiteWith (u.toFinset : Set V) (N.toFinset : Set V) := by
      simpa using hbB
    calc
      q * u.ncard = ∑ _v ∈ u, q := by
        rw [Set.ncard_eq_toFinset_card u]
        simp [Nat.mul_comm]
      _ = ∑ v ∈ u, B.degree v := by
        apply Finset.sum_congr rfl
        intro v hv
        exact (hdeg_left v (Set.mem_toFinset.mp hv)).symm
      _ = B.edgeFinset.card :=
        SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hbBfin
      _ = ∑ w ∈ N, B.degree w :=
        (SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' hbBfin).symm
      _ ≤ ∑ _w ∈ N, q :=
        sum_le_sum fun w hw ↦ hdeg_right w (Set.mem_toFinset.mp hw)
      _ = q * N.ncard := by
        rw [Set.ncard_eq_toFinset_card N]
        simp [Nat.mul_comm]
  exact Nat.le_of_mul_le_mul_left hcount hq

/-- A finite positive regular bipartite graph has a perfect matching. -/
theorem exists_isPerfectMatching_of_isRegularOfDegree (hq : 0 < q)
    (hreg : G.IsRegularOfDegree q) (hbip : G.IsBipartiteWith s t) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  apply G.exists_isPerfectMatching_of_forall_ncard_le hbip
  intro u
  let us : Set V := u ∩ s
  let ut : Set V := u ∩ t
  let Ns : Set V := ⋃ v ∈ us, G.neighborSet v
  let Nt : Set V := ⋃ v ∈ ut, G.neighborSet v
  have hsupp : G.support = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro v
    rw [SimpleGraph.mem_support_iff_not_isIsolated, ← G.degree_pos,
      hreg.degree_eq v]
    exact hq
  have hcover : s ∪ t = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro v
    exact SimpleGraph.isBipartiteWith_support_subset hbip
      (hsupp.symm.subset (Set.mem_univ v))
  have hu_eq : u = us ∪ ut := by
    ext v
    simp only [us, ut, Set.mem_union, Set.mem_inter_iff]
    constructor
    · intro hv
      have : v ∈ s ∪ t := hcover.symm.subset (Set.mem_univ v)
      exact this.elim (fun hs ↦ Or.inl ⟨hv, hs⟩) (fun ht ↦ Or.inr ⟨hv, ht⟩)
    · exact fun h ↦ h.elim And.left And.left
  have hus : us ⊆ s := fun _ h ↦ h.2
  have hut : ut ⊆ t := fun _ h ↦ h.2
  have hhall_s : us.ncard ≤ Ns.ncard := hall_side hq hreg hbip hus
  have hhall_t : ut.ncard ≤ Nt.ncard := hall_side hq hreg hbip.symm hut
  have hNsu : Ns ⊆ (⋃ v ∈ u, G.neighborSet v) := by
    intro w hw
    simp only [Ns, Set.mem_iUnion] at hw ⊢
    obtain ⟨v, hv, hw⟩ := hw
    exact ⟨v, hv.1, hw⟩
  have hNtu : Nt ⊆ (⋃ v ∈ u, G.neighborSet v) := by
    intro w hw
    simp only [Nt, Set.mem_iUnion] at hw ⊢
    obtain ⟨v, hv, hw⟩ := hw
    exact ⟨v, hv.1, hw⟩
  have hNs : Ns ⊆ t := by
    intro w hw
    simp only [Ns, Set.mem_iUnion] at hw
    obtain ⟨v, hv, hw⟩ := hw
    exact hbip.mem_of_mem_adj (hus hv) hw
  have hNt : Nt ⊆ s := by
    intro w hw
    simp only [Nt, Set.mem_iUnion] at hw
    obtain ⟨v, hv, hw⟩ := hw
    exact hbip.symm.mem_of_mem_adj (hut hv) hw
  have hd_u : Disjoint us ut :=
    Set.disjoint_of_subset hus hut hbip.disjoint
  have hd_N : Disjoint Ns Nt :=
    Set.disjoint_of_subset hNs hNt hbip.disjoint.symm
  have h_union_subset : Ns ∪ Nt ⊆ (⋃ v ∈ u, G.neighborSet v) :=
    Set.union_subset hNsu hNtu
  calc
    u.ncard = us.ncard + ut.ncard := by rw [hu_eq, Set.ncard_union_eq hd_u]
    _ ≤ Ns.ncard + Nt.ncard := Nat.add_le_add hhall_s hhall_t
    _ = (Ns ∪ Nt).ncard := (Set.ncard_union_eq hd_N).symm
    _ ≤ (⋃ v ∈ u, G.neighborSet v).ncard :=
      Set.ncard_le_ncard h_union_subset (Set.toFinite _)

/-- Removing a perfect matching from a `(q+1)`-regular graph leaves a
`q`-regular graph. -/
private lemma isRegularOfDegree_sdiff_perfectMatching
    (hreg : G.IsRegularOfDegree (q + 1)) {M : G.Subgraph}
    (hM : M.IsPerfectMatching) :
    (G \ M.spanningCoe).IsRegularOfDegree q := by
  intro v
  have hsub : M.spanningCoe.neighborFinset v ⊆ G.neighborFinset v := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw ⊢
    exact M.spanningCoe_le hw
  have hMdeg : M.spanningCoe.degree v = 1 := by
    rw [M.degree_spanningCoe]
    exact (SimpleGraph.Subgraph.isPerfectMatching_iff_forall_degree.mp hM) v
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_sdiff,
    Finset.card_sdiff_of_subset hsub]
  change G.degree v - M.spanningCoe.degree v = q
  rw [hreg.degree_eq v, hMdeg]
  omega

/-- The regular-factor consequence of König's line-colouring theorem: a
finite `q`-regular bipartite graph has a spanning `k`-regular subgraph for
every `k ≤ q`.

We phrase the factor as a simple graph `H ≤ G`, avoiding any dependence on
the vertex-set field of `SimpleGraph.Subgraph`.
-/
theorem exists_regular_subgraph_of_le (hreg : G.IsRegularOfDegree q)
    (hbip : G.IsBipartiteWith s t) (hk : k ≤ q) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.IsRegularOfDegree k := by
  induction q generalizing G s t instG with
  | zero =>
      let : DecidableRel G.Adj := instG
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      refine ⟨(⊥ : SimpleGraph V), bot_le, ?_⟩
      intro v
      simpa [hk0] using SimpleGraph.bot_degree (G := (⊥ : SimpleGraph V)) v
  | succ q ih =>
      let : DecidableRel G.Adj := instG
      by_cases hkq : k = q + 1
      · subst k
        have hdec : (Classical.decRel G.Adj) = instG := Subsingleton.elim _ _
        cases hdec
        exact ⟨G, le_rfl, hreg⟩
      · have hk' : k ≤ q := by omega
        obtain ⟨M, hM⟩ :=
          exists_isPerfectMatching_of_isRegularOfDegree (q := q + 1)
            (by omega) hreg hbip
        let : DecidableRel M.spanningCoe.Adj := Classical.decRel _
        let G' : SimpleGraph V := G \ M.spanningCoe
        have hreg' : G'.IsRegularOfDegree q := by
          exact isRegularOfDegree_sdiff_perfectMatching hreg hM
        have hbip' : G'.IsBipartiteWith s t := by
          refine ⟨hbip.disjoint, fun _ _ hadj ↦ ?_⟩
          exact hbip.mem_of_adj hadj.1
        obtain ⟨H, hHG', hHreg⟩ := ih hreg' hbip' hk'
        exact ⟨H, hHG'.trans sdiff_le, hHreg⟩

end Konig

end Erdos182
