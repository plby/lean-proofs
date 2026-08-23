import ErdosProblems.Erdos1105.CycleCut

/-!
# Saturating a graph without long cycles

Maximal completion preserves the vertex set and turns every missing edge into
a long path between its endpoints. This is the saturation step of Kopylov's
proof, not a hypothesis added to the anti-Ramsey statement.
-/

namespace Erdos1105

open SimpleGraph Finset

def NoLongCycle {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (v : V) (p : G.Walk v v), p.IsCycle → p.length < k

theorem exists_cycle_saturated_extension {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (hG : NoLongCycle G k) :
    ∃ H : SimpleGraph V, G ≤ H ∧ NoLongCycle H k ∧
      ∀ J : SimpleGraph V, H ≤ J → NoLongCycle J k → J = H := by
  classical
  let P : Finset (SimpleGraph V) := univ.filter fun J ↦ G ≤ J ∧ NoLongCycle J k
  have hP : P.Nonempty := ⟨G, mem_filter.mpr ⟨mem_univ _, le_rfl, hG⟩⟩
  obtain ⟨H, hH, hmax⟩ := P.exists_max_image (fun J ↦ J.edgeFinset.card) hP
  have hGH := (mem_filter.mp hH).2.1
  refine ⟨H, hGH, (mem_filter.mp hH).2.2, ?_⟩
  intro J hHJ hJ
  have hcard := hmax J (mem_filter.mpr ⟨mem_univ _, hGH.trans hHJ, hJ⟩)
  exact (edgeFinset_inj.mp (eq_of_subset_of_card_le (edgeFinset_mono hHJ) hcard)).symm

/-- A newly created long cycle, after adding one edge, contains a long
old path joining the endpoints of that edge. -/
theorem long_path_of_added_edge_cycle {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (hG : NoLongCycle G k) {x y : V}
    (hnew : ¬NoLongCycle (G ⊔ edge x y) k) :
    ∃ p : G.Walk x y, p.IsPath ∧ k ≤ p.length + 1 := by
  classical
  let H := G ⊔ edge x y
  change ¬∀ (v : V) (p : H.Walk v v), p.IsCycle → p.length < k at hnew
  push Not at hnew
  obtain ⟨v, p, hp, hlen⟩ := hnew
  have hmem : s(x, y) ∈ p.edges := by
    by_contra h
    have hsub : ∀ e ∈ p.edges, e ∈ G.edgeSet := by
      intro e he
      have heH := p.edges_subset_edgeSet he
      change e ∈ (G ⊔ edge x y).edgeSet at heH
      rw [edgeSet_sup] at heH
      rcases heH with heG | heE
      · exact heG
      · have heq : e = s(x, y) := by
          have := edgeSet_edge_subset heE
          exact this
        exact (h (heq ▸ he)).elim
    have hh := hG v (p.transfer G hsub) (hp.transfer hsub)
    rw [Walk.length_transfer] at hh
    omega
  obtain ⟨d, hd, hdxy⟩ := List.mem_map.mp hmem
  obtain ⟨q, hq, hqlen⟩ := path_of_cycle_cut_dart p hp d hd
  have hdel : H.deleteEdges {d.edge} ≤ G := by
    intro a b hab
    rw [deleteEdges_adj, Set.mem_singleton_iff] at hab
    rcases hab.1 with hG | hE
    · exact hG
    · have heq : s(a, b) = s(x, y) := by
        exact edgeSet_edge_subset (show s(a, b) ∈ (edge x y).edgeSet from hE)
      exact (hab.2 (heq.trans hdxy.symm)).elim
  have hsub : ∀ e ∈ q.edges, e ∈ G.edgeSet :=
    fun _ he ↦ edgeSet_mono hdel (q.edges_subset_edgeSet he)
  let q' := q.transfer G hsub
  have hq' : q'.IsPath := hq.transfer hsub
  have hlen' : k ≤ q'.length + 1 := by
    rw [Walk.length_transfer, hqlen]
    exact hlen
  have heq : d.fst = x ∧ d.snd = y ∨ d.fst = y ∧ d.snd = x := Sym2.eq_iff.mp hdxy
  rcases heq with heq | heq
  · refine ⟨q'.reverse.copy heq.1 heq.2, ?_, ?_⟩
    · simpa only [Walk.isPath_copy] using hq'.reverse
    · simpa only [Walk.length_copy, Walk.length_reverse] using hlen'
  · refine ⟨q'.copy heq.2 heq.1, ?_, ?_⟩
    · simpa only [Walk.isPath_copy] using hq'
    · simpa only [Walk.length_copy] using hlen'

theorem long_path_of_saturated_nonedge {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (hG : NoLongCycle G k)
    (hmax : ∀ J : SimpleGraph V, G ≤ J → NoLongCycle J k → J = G)
    {x y : V} (hxy : x ≠ y) (hnxy : ¬G.Adj x y) :
    ∃ p : G.Walk x y, p.IsPath ∧ k ≤ p.length + 1 := by
  apply long_path_of_added_edge_cycle G k hG
  intro hJ
  have heq := hmax (G ⊔ edge x y) le_sup_left hJ
  have hadj : (G ⊔ edge x y).Adj x y :=
    Or.inr ((edge_adj x y x y).mpr ⟨Or.inl ⟨rfl, rfl⟩, hxy⟩)
  exact hnxy (heq ▸ hadj)

end Erdos1105

#print axioms Erdos1105.exists_cycle_saturated_extension
#print axioms Erdos1105.long_path_of_saturated_nonedge
