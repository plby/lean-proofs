import ErdosProblems.Erdos556.DeletionPaths

/-!
# Vertex separations

A disconnected graph after vertex deletion yields two nonempty parts with
no cross edge. Degree and edge counts are recorded in the original graph.
-/

namespace Erdos556

open SimpleGraph Finset

theorem exists_separation_of_not_preconnected {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (h : ¬ (G.induce (S : Set V)ᶜ).Preconnected) :
    ∃ A B : Finset V, A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
      Disjoint A S ∧ Disjoint B S ∧ A ∪ B ∪ S = univ ∧
      ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b := by
  classical
  let U := (S : Set V)ᶜ
  let H := G.induce U
  obtain ⟨u, v, huv⟩ : ∃ u v : U, ¬ H.Reachable u v := by
    simpa only [SimpleGraph.Preconnected, not_forall] using h
  let A := ({x : V | ∃ hx : x ∉ S, H.Reachable u ⟨x, hx⟩} : Set V).toFinset
  let B := (S ∪ A)ᶜ
  have hA (x : V) : x ∈ A ↔ ∃ hx : x ∉ S, H.Reachable u ⟨x, hx⟩ := by
    simp only [A, Set.mem_toFinset, Set.mem_ofPred_eq]
  have hAS : Disjoint A S := by
    rw [Finset.disjoint_left]
    intro x hx
    exact ((hA x).mp hx).choose
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    exact (mem_compl.mp hxB) (mem_union_right S hxA)
  have hBS : Disjoint B S := by
    rw [Finset.disjoint_left]
    intro x hxB hxS
    exact (mem_compl.mp hxB) (mem_union_left A hxS)
  have hAnon : A.Nonempty := ⟨u.val, (hA _).mpr ⟨u.property, .rfl⟩⟩
  have hBnon : B.Nonempty := by
    refine ⟨v.val, ?_⟩
    simp only [B, mem_compl, mem_union, not_or]
    refine ⟨v.property, ?_⟩
    intro hvA
    obtain ⟨_, hreach⟩ := (hA _).mp hvA
    exact huv hreach
  have hcover : A ∪ B ∪ S = univ := by
    calc
      A ∪ B ∪ S = (S ∪ A) ∪ (S ∪ A)ᶜ := by dsimp [B]; ac_rfl
      _ = univ := Finset.union_compl (S ∪ A)
  refine ⟨A, B, hAnon, hBnon, hAB, hAS, hBS, hcover, ?_⟩
  intro a ha b hb hab
  obtain ⟨haS, hreach⟩ := (hA a).mp ha
  have hbS : b ∉ S := fun h => (mem_compl.mp hb) (mem_union_left A h)
  have hadj : H.Adj ⟨a, haS⟩ ⟨b, hbS⟩ := hab
  have hbA : b ∈ A := (hA b).mpr ⟨hbS, hreach.trans hadj.reachable⟩
  exact (mem_compl.mp hb) (mem_union_right S hbA)

theorem degree_le_parts_of_separation {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B S : Finset V)
    (hcover : A ∪ B ∪ S = univ) (hcross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (a : V) (ha : a ∈ A) : G.degree a ≤ A.card + S.card := by
  have hsub : G.neighborFinset a ⊆ A ∪ S := by
    intro x hx
    have hall : x ∈ A ∪ B ∪ S := by rw [hcover]; exact mem_univ _
    rcases mem_union.mp hall with hAB | hS
    · rcases mem_union.mp hAB with hA | hB
      · exact mem_union_left _ hA
      · exact (hcross a ha x hB ((G.mem_neighborFinset a x).mp hx)).elim
    · exact mem_union_right _ hS
  rw [← G.card_neighborFinset_eq_degree a]
  exact (card_le_card hsub).trans (card_union_le A S)

#print axioms exists_separation_of_not_preconnected

theorem edge_count_le_of_separation {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B S : Finset V)
    (hcover : A ∪ B ∪ S = univ) (hcross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) :
    G.edgeFinset.card ≤ (G.induce (A : Set V)).edgeFinset.card +
      (G.induce (B : Set V)).edgeFinset.card + S.card * Fintype.card V := by
  classical
  let X := G.edgeFinset.filter (fun e => e.toFinset ⊆ A)
  let Y := G.edgeFinset.filter (fun e => e.toFinset ⊆ B)
  let Z := S.biUnion (fun v => G.incidenceFinset v)
  have hpart (v : V) (hv : v ∉ S) : v ∈ A ∨ v ∈ B := by
    have hall : v ∈ A ∪ B ∪ S := by rw [hcover]; exact mem_univ v
    exact mem_union.mp ((mem_union.mp hall).resolve_right hv)
  have hZmem (e : Sym2 V) (he : e ∈ G.edgeFinset) (v : V) (hv : v ∈ S) (hve : v ∈ e) :
      e ∈ Z := by
    apply mem_biUnion.mpr
    refine ⟨v, hv, ?_⟩
    rw [G.incidenceFinset_eq_filter]
    exact mem_filter.mpr ⟨he, hve⟩
  have hedgecover : G.edgeFinset ⊆ X ∪ Y ∪ Z := by
    intro e he
    rcases e with ⟨⟨u, v⟩⟩
    by_cases huS : u ∈ S
    · exact mem_union_right _ (hZmem _ he u huS (by simp))
    by_cases hvS : v ∈ S
    · exact mem_union_right _ (hZmem _ he v hvS (by simp))
    have huv : G.Adj u v := by simpa using he
    rcases hpart u huS with huA | huB <;> rcases hpart v hvS with hvA | hvB
    · apply mem_union_left
      apply mem_union_left
      exact mem_filter.mpr ⟨he, by simpa only [Sym2.toFinset_mk_eq,
        insert_subset_iff, singleton_subset_iff] using And.intro huA hvA⟩
    · exact (hcross u huA v hvB huv).elim
    · exact (hcross v hvA u huB huv.symm).elim
    · apply mem_union_left
      apply mem_union_right
      exact mem_filter.mpr ⟨he, by simpa only [Sym2.toFinset_mk_eq,
        insert_subset_iff, singleton_subset_iff] using And.intro huB hvB⟩
  have hX : X.card = (G.induce (A : Set V)).edgeFinset.card :=
    G.card_filter_edgeFinset_toFinset_subset A
  have hY : Y.card = (G.induce (B : Set V)).edgeFinset.card :=
    G.card_filter_edgeFinset_toFinset_subset B
  have hZ : Z.card ≤ S.card * Fintype.card V := by
    calc
      Z.card ≤ ∑ v ∈ S, (G.incidenceFinset v).card := card_biUnion_le
      _ ≤ ∑ _v ∈ S, Fintype.card V := by
        apply sum_le_sum
        intro v _
        rw [G.card_incidenceFinset_eq_degree]
        exact (G.degree_lt_card_verts v).le
      _ = S.card * Fintype.card V := by simp
  have h1 := card_le_card hedgecover
  have h2 := card_union_le (X ∪ Y) Z
  have h3 := card_union_le X Y
  omega

#print axioms edge_count_le_of_separation

end Erdos556
