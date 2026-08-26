import ErdosProblems.Erdos19.Core

/-!
# Matching operations for the EFL completion argument
-/

namespace Erdos19

open _root_.SimpleGraph

/-- A finite graph has a matching maximizing any natural-number score. -/
lemma exists_matching_maximizing {V : Type*} [Fintype V]
    (G : SimpleGraph V) (score : G.Subgraph → ℕ) :
    ∃ M : G.Subgraph, M.IsMatching ∧
      ∀ N : G.Subgraph, N.IsMatching → score N ≤ score M := by
  classical
  let matchings : Finset G.Subgraph := Finset.univ.filter Subgraph.IsMatching
  have hbottom : (⊥ : G.Subgraph).IsMatching := by
    intro v hv
    simp at hv
  have hnonempty : matchings.Nonempty := by
    exact ⟨⊥, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbottom⟩⟩
  obtain ⟨M, hM, hmax⟩ := Finset.exists_max_image matchings score hnonempty
  exact ⟨M, (Finset.mem_filter.mp hM).2,
    fun N hN ↦ hmax N (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hN⟩)⟩

/-- Deleting the two endpoints of one matching edge leaves a matching. -/
lemma matching_delete_endpoints {V : Type*} {G : SimpleGraph V}
    (M : G.Subgraph) (hM : M.IsMatching) {a b : V} (hab : M.Adj a b) :
    (M.deleteVerts {a, b}).IsMatching := by
  intro x hx
  change x ∈ M.verts ∧ x ∉ ({a, b} : Set V) at hx
  obtain ⟨y, hxy, huniq⟩ := hM hx.1
  have hy : y ∉ ({a, b} : Set V) := by
    intro hy
    rcases hy with (rfl | rfl)
    · have hxb : x = b := hM.eq_of_adj_right hxy hab.symm
      exact hx.2 (by simp [hxb])
    · have hxa : x = a := hM.eq_of_adj_right hxy hab
      exact hx.2 (by simp [hxa])
  refine ⟨y, ?_, ?_⟩
  · exact Subgraph.deleteVerts_adj.mpr ⟨hx.1, hx.2, hxy.snd_mem, hy, hxy⟩
  · intro z hz
    exact huniq z (Subgraph.deleteVerts_adj.mp hz).2.2.2.2

/-- If each vertex has at most `d` nonneighbors (including itself), a maximum
matching leaves at most `d` vertices uncovered. -/
lemma exists_matching_few_uncovered {V : Type*} [Fintype V]
    (G : SimpleGraph V) (d : ℕ)
    (hnonadj : ∀ v, (G.neighborSet v)ᶜ.ncard ≤ d) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.vertsᶜ.ncard ≤ d := by
  classical
  obtain ⟨M, hM, hmax⟩ := exists_maximum_matching G
  refine ⟨M, hM, ?_⟩
  by_cases hnonempty : M.vertsᶜ.Nonempty
  · obtain ⟨v, hv⟩ := hnonempty
    have hind := maximum_matching_unmatched_pairwise_not_adj M hM hmax
    have hsub : M.vertsᶜ ⊆ (G.neighborSet v)ᶜ := by
      intro w hw
      change ¬G.Adj v w
      by_cases hvw : v = w
      · subst w
        exact fun h ↦ h.ne rfl
      · exact hind hv hw hvw
    exact (Set.ncard_le_ncard hsub).trans (hnonadj v)
  · simp [Set.not_nonempty_iff_eq_empty.mp hnonempty]

/-- A prescribed vertex set can be covered by a matching when each of its
vertices has at least as many neighbors as the size of the prescribed set.
This uses a matching maximizing coverage, followed by a one-edge rotation. -/
theorem exists_matching_covering_of_neighbor_ncard_ge
    {V : Type*} [Fintype V] (G : SimpleGraph V) (U : Set V)
    (hdegree : ∀ u ∈ U, U.ncard ≤ (G.neighborSet u).ncard) :
    ∃ M : G.Subgraph, M.IsMatching ∧ U ⊆ M.verts := by
  classical
  obtain ⟨M, hM, hmax⟩ := exists_matching_maximizing G
    (fun N ↦ (N.verts ∩ U).ncard)
  refine ⟨M, hM, ?_⟩
  intro u hu
  by_contra huM
  have improve (N : G.Subgraph) (hN : N.IsMatching)
      (hkeep : M.verts ∩ U ⊆ N.verts) (hnew : u ∈ N.verts) : False := by
    have hsub : insert u (M.verts ∩ U) ⊆ N.verts ∩ U := by
      intro x hx
      rcases hx with (rfl | hx)
      · exact ⟨hnew, hu⟩
      · exact ⟨hkeep hx, hx.2⟩
    have hnot : u ∉ M.verts ∩ U := fun h ↦ huM h.1
    have hcard := Set.ncard_le_ncard hsub
    rw [Set.ncard_insert_of_notMem hnot] at hcard
    have hbound := hmax N hN
    omega
  have hmates (v : V) (huv : G.Adj u v) : ∃ w, w ∈ U ∧ M.Adj v w := by
    let P : G.Subgraph := G.subgraphOfAdj huv
    have hP : P.IsMatching := Subgraph.IsMatching.subgraphOfAdj huv
    have hPverts : P.verts = {u, v} := by simp [P]
    have hPcover : P.support = {u, v} := by simp [P]
    have hvM : v ∈ M.verts := by
      by_contra hvM
      have hdisjoint : Disjoint M.support P.support := by
        rw [hM.support_eq_verts, hPcover, Set.disjoint_left]
        intro x hx hxP
        rcases hxP with (rfl | rfl)
        · exact huM hx
        · exact hvM hx
      have hN : (M ⊔ P).IsMatching := hM.sup hP hdisjoint
      apply improve (M ⊔ P) hN
      · intro x hx
        exact Or.inl hx.1
      · apply Or.inr
        rw [hPverts]
        exact Or.inl rfl
    obtain ⟨w, hvw, _⟩ := hM hvM
    by_cases hwU : w ∈ U
    · exact ⟨w, hwU, hvw⟩
    · exfalso
      let M' : G.Subgraph := M.deleteVerts {v, w}
      have hM' : M'.IsMatching := matching_delete_endpoints M hM hvw
      have hdisjoint : Disjoint M'.support P.support := by
        rw [hM'.support_eq_verts, hPcover, Set.disjoint_left]
        intro x hx hxP
        change x ∈ M.verts ∧ x ∉ ({v, w} : Set V) at hx
        rcases hxP with (rfl | rfl)
        · exact huM hx.1
        · exact hx.2 (Or.inl rfl)
      have hN : (M' ⊔ P).IsMatching := hM'.sup hP hdisjoint
      apply improve (M' ⊔ P) hN
      · intro x hx
        by_cases hxv : x = v
        · apply Or.inr
          rw [hPverts]
          exact Or.inr hxv
        · apply Or.inl
          refine ⟨hx.1, ?_⟩
          intro hxpair
          rcases hxpair with (hxv' | hxw)
          · exact hxv hxv'
          · exact hwU (hxw ▸ hx.2)
      · apply Or.inr
        rw [hPverts]
        exact Or.inl rfl
  have hm : ∀ v : G.neighborSet u, ∃ w, w ∈ U ∧ M.Adj v.1 w := by
    intro v
    exact hmates v.1 v.2
  choose mate hmateU hmateAdj using hm
  let f : G.neighborSet u → (U \ {u} : Set V) := fun v ↦
    ⟨mate v, hmateU v, fun h ↦ huM (h ▸ (hmateAdj v).snd_mem)⟩
  have hf : Function.Injective f := by
    intro v w h
    have hsame : mate v = mate w := congrArg Subtype.val h
    have hvw : M.Adj v.1 (mate w) := by
      rw [← hsame]
      exact hmateAdj v
    exact Subtype.ext (hM.eq_of_adj_right hvw (hmateAdj w))
  let _ : Fintype (G.neighborSet u) := Fintype.ofFinite _
  let _ : Fintype (U \ {u} : Set V) := Fintype.ofFinite _
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Set.fintypeCard_eq_ncard] at hcard
  rw [Set.ncard_sdiff (Set.singleton_subset_iff.mpr hu), Set.ncard_singleton] at hcard
  have hpos : 0 < U.ncard := (Set.ncard_pos (Set.toFinite U)).mpr ⟨u, hu⟩
  have hdeg := hdegree u hu
  omega

/-- A length-three augmenting path replaces its middle matching edge and
strictly increases the set of covered vertices. -/
lemma exists_matching_augment_three {V : Type*} {G : SimpleGraph V}
    (M : G.Subgraph) (hM : M.IsMatching) {u v a b : V}
    (hu : u ∉ M.verts) (hv : v ∉ M.verts) (huv : u ≠ v)
    (hab : M.Adj a b) (hua : G.Adj u a) (hbv : G.Adj b v) :
    ∃ N : G.Subgraph, N.IsMatching ∧ M.verts ⊂ N.verts := by
  let R := M.deleteVerts {a, b}
  let P := G.subgraphOfAdj hua
  let T := G.subgraphOfAdj hbv
  have hR : R.IsMatching := matching_delete_endpoints M hM hab
  have hP : P.IsMatching := Subgraph.IsMatching.subgraphOfAdj hua
  have hT : T.IsMatching := Subgraph.IsMatching.subgraphOfAdj hbv
  have hPv : P.verts = {u, a} := by simp [P]
  have hTv : T.verts = {b, v} := by simp [T]
  have hRP : Disjoint R.support P.support := by
    rw [hR.support_eq_verts, hP.support_eq_verts, hPv, Set.disjoint_left]
    intro x hx hxP
    change x ∈ M.verts ∧ x ∉ ({a, b} : Set V) at hx
    rcases hxP with (rfl | rfl)
    · exact hu hx.1
    · exact hx.2 (Or.inl rfl)
  have hRPmatch : (R ⊔ P).IsMatching := hR.sup hP hRP
  have hRPT : Disjoint (R ⊔ P).support T.support := by
    rw [hRPmatch.support_eq_verts, hT.support_eq_verts, hTv,
      Subgraph.verts_sup, hPv, Set.disjoint_left]
    intro x hx hxT
    rcases hx with hxR | hxP
    · change x ∈ M.verts ∧ x ∉ ({a, b} : Set V) at hxR
      rcases hxT with (rfl | rfl)
      · exact hxR.2 (Or.inr rfl)
      · exact hv hxR.1
    · rcases hxP with (rfl | rfl) <;> rcases hxT with (h | h)
      · exact hu (h.symm ▸ hab.snd_mem)
      · exact huv h
      · exact hab.ne h
      · exact hv (h ▸ hab.fst_mem)
  let N := (R ⊔ P) ⊔ T
  have hN : N.IsMatching := hRPmatch.sup hT hRPT
  have hkeep : M.verts ⊆ N.verts := by
    intro x hx
    by_cases hxa : x = a
    · exact Or.inl (Or.inr (hPv.symm ▸ Or.inr hxa))
    · by_cases hxb : x = b
      · exact Or.inr (hTv.symm ▸ Or.inl hxb)
      · exact Or.inl (Or.inl ⟨hx, fun h ↦ h.elim hxa hxb⟩)
  have hnew : u ∈ N.verts := Or.inl (Or.inr (hPv.symm ▸ Or.inl rfl))
  refine ⟨N, hN, Set.ssubset_iff_subset_ne.mpr ⟨hkeep, ?_⟩⟩
  intro heq
  exact hu (heq.symm ▸ hnew)

/-- An even-order graph of minimum degree at least half its order has a
perfect matching. The proof only uses a maximum matching and a length-three
augmentation, not a Hamiltonicity or graph-coloring theorem. -/
theorem exists_perfectMatching_of_two_mul_neighbor_ncard_ge
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (heven : Even (Fintype.card V))
    (hdegree : ∀ v, Fintype.card V ≤ 2 * (G.neighborSet v).ncard) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  classical
  obtain ⟨M, hM, hmax⟩ := exists_maximum_matching G
  have hmaxv (N : G.Subgraph) (hN : N.IsMatching) : N.verts.ncard ≤ M.verts.ncard := by
    rw [matching_verts_ncard_generic N hN, matching_verts_ncard_generic M hM]
    exact Nat.mul_le_mul_left 2 (hmax N hN)
  have hind := maximum_matching_unmatched_pairwise_not_adj M hM hmax
  have hneighbors (x : V) (hx : x ∉ M.verts) : G.neighborSet x ⊆ M.verts := by
    intro y hxy
    by_contra hy
    exact hind hx hy hxy.ne hxy
  refine ⟨M, hM, ?_⟩
  intro u
  by_contra hu
  have htotal : M.verts.ncard + M.vertsᶜ.ncard = Fintype.card V := by
    simpa using Set.ncard_add_ncard_compl M.verts
  have htwo : 1 < M.vertsᶜ.ncard := by
    have hpos : 0 < M.vertsᶜ.ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨u, hu⟩
    have hMcard := matching_verts_ncard_generic M hM
    obtain ⟨k, hk⟩ := heven
    omega
  obtain ⟨v, hv, hvu⟩ := Set.exists_ne_of_one_lt_ncard htwo u
  have hhas (a : G.neighborSet u) : ∃ b, M.Adj a.1 b :=
    (hM (hneighbors u hu a.2)).exists
  choose mate hmate using hhas
  have hnot (a : G.neighborSet u) : mate a ∉ G.neighborSet v := by
    intro hva
    obtain ⟨N, hN, hstrict⟩ := exists_matching_augment_three M hM hu hv hvu.symm
      (hmate a) a.2 hva.symm
    have hlt := Set.ncard_lt_ncard hstrict
    have hle := hmaxv N hN
    omega
  let f : G.neighborSet u → (M.verts \ G.neighborSet v : Set V) := fun a ↦
    ⟨mate a, (hmate a).snd_mem, hnot a⟩
  have hf : Function.Injective f := by
    intro a b h
    have hsame : mate a = mate b := congrArg Subtype.val h
    have hadj : M.Adj a.1 (mate b) := by
      rw [← hsame]
      exact hmate a
    exact Subtype.ext (hM.eq_of_adj_right hadj (hmate b))
  let _ : Fintype (G.neighborSet u) := Fintype.ofFinite _
  let _ : Fintype (M.verts \ G.neighborSet v : Set V) := Fintype.ofFinite _
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Set.fintypeCard_eq_ncard] at hcard
  rw [Set.ncard_sdiff (hneighbors v hv)] at hcard
  have hsubcard := Set.ncard_le_ncard (hneighbors v hv)
  have hdu := hdegree u
  have hdv := hdegree v
  omega

/-- One block-repair step. The buffer is disjoint from the vertices requiring
coverage and is at least as large as every local missing-neighbor set. The
resulting matching covers the required vertices and uses no buffer-buffer
edges, so every added edge can be charged to a required vertex. -/
theorem exists_matching_covering_with_buffer
    {V : Type*} [Fintype V] (G : SimpleGraph V) (A B : Set V) (d : ℕ)
    (hdisjoint : Disjoint A B) (hbuffer : d ≤ B.ncard)
    (hmissing : ∀ u ∈ A, ((A ∪ B) \ G.neighborSet u).ncard ≤ d) :
    ∃ M : G.Subgraph, M.IsMatching ∧ A ⊆ M.verts ∧ M.verts ⊆ A ∪ B ∧
      ∀ x y, M.Adj x y → x ∈ A ∨ y ∈ A := by
  let J : SimpleGraph V := {
    Adj := fun x y ↦ G.Adj x y ∧ x ∈ A ∪ B ∧ y ∈ A ∪ B ∧ (x ∈ A ∨ y ∈ A)
    symm := ⟨by
      intro x y h
      exact ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.symm⟩⟩
    loopless := ⟨by
      intro x h
      exact h.1.ne rfl⟩ }
  have hdegree : ∀ u ∈ A, A.ncard ≤ (J.neighborSet u).ncard := by
    intro u hu
    have heq : J.neighborSet u = (A ∪ B) ∩ G.neighborSet u := by
      ext v
      change (G.Adj u v ∧ u ∈ A ∪ B ∧ v ∈ A ∪ B ∧ (u ∈ A ∨ v ∈ A)) ↔
        v ∈ A ∪ B ∧ G.Adj u v
      constructor
      · exact fun h ↦ ⟨h.2.2.1, h.1⟩
      · exact fun h ↦ ⟨h.2, Or.inl hu, h.1, Or.inl hu⟩
    rw [heq]
    have hcard := Set.ncard_inter_add_ncard_sdiff_eq_ncard (A ∪ B) (G.neighborSet u)
    rw [Set.ncard_union_eq hdisjoint] at hcard
    have hmiss := hmissing u hu
    omega
  obtain ⟨M, hM, hcover⟩ := exists_matching_covering_of_neighbor_ncard_ge J A hdegree
  let N : G.Subgraph := {
    verts := M.verts
    Adj := M.Adj
    adj_sub := fun h ↦ (M.adj_sub h).1
    edge_vert := M.edge_vert
    symm := M.symm }
  refine ⟨N, hM, hcover, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hxy, _⟩ := hM hx
    exact (M.adj_sub hxy).2.1
  · intro x y hxy
    exact (M.adj_sub hxy).2.2.2

#print axioms exists_matching_maximizing
#print axioms matching_delete_endpoints
#print axioms exists_matching_few_uncovered
#print axioms exists_matching_covering_of_neighbor_ncard_ge
#print axioms exists_matching_augment_three
#print axioms exists_perfectMatching_of_two_mul_neighbor_ncard_ge
#print axioms exists_matching_covering_with_buffer

end Erdos19
