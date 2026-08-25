import ErdosProblems.Erdos223.SphericalEuler.WeightedPlaneBound
import Wikipedia.SchoenfliesTheorem.Graph.Component

open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G : Graph α β} {a v : α}

/-- A component of `G - v`, with `v` put back, induces a connected subgraph of a
connected graph. -/
theorem Connected.induce_component_deleteVerts_union_singleton
    (hG : G.Connected) (hv : v ∈ V(G))
    (ha : a ∈ V(G.deleteVerts {v})) :
    (G.induce ((G.deleteVerts {v}).component a ∪ {v})).Connected := by
  let D := G.deleteVerts {v}
  let S := D.component a
  let Q := D.induce S
  let H := G.induce (S ∪ {v})
  have haS : a ∈ S := mem_component_self ha
  have hQc : Q.Connected := induce_component_connected ha
  have hQH : Q ≤ H := by
    refine ⟨fun x hx => Or.inl hx, ?_⟩
    intro e x y hxy
    change D.IsLink e x y ∧ x ∈ S ∧ y ∈ S at hxy
    change G.IsLink e x y ∧ x ∈ S ∪ {v} ∧ y ∈ S ∪ {v}
    exact ⟨hxy.1.mono deleteVerts_le, Or.inl hxy.2.1, Or.inl hxy.2.2⟩
  have haG : a ∈ V(G) := deleteVerts_le.vertexSet_mono ha
  obtain ⟨W, hW⟩ := hG.exists_isPath haG hv
  obtain ⟨p, hp, g, hg, t, ht, hgpt⟩ :=
    exists_isLink_out_of_component (G := G) (S := ({v} : Set α))
      (K := G) le_rfl hW.isWalk haS (by simp)
  have htv : t = v := by simpa using ht
  subst t
  have hlinkH : H.IsLink g v p := by
    change G.IsLink g v p ∧ v ∈ S ∪ {v} ∧ p ∈ S ∪ {v}
    exact ⟨hgpt.symm, Or.inr rfl, Or.inl hp⟩
  change H.Connected
  refine Connected.of_hub (show v ∈ S ∪ {v} from Or.inr rfl) ?_
  intro z hz
  change z ∈ S ∪ {v} at hz
  rcases hz with hzS | hzv
  · exact (Reaches.of_isLink hlinkH).trans
      ((hQc.reaches hp hzS).mono hQH)
  · subst z
    exact Reaches.refl (show v ∈ S ∪ {v} from Or.inr rfl)

#print axioms Graph.Connected.induce_component_deleteVerts_union_singleton

/-- The two connected induced pieces obtained by splitting at a cut vertex. -/
structure CutSplit (G : Graph α β) (v : α) where
  A : Graph α β
  B : Graph α β
  A_le : A ≤ G
  B_le : B ≤ G
  A_connected : A.Connected
  B_connected : B.Connected
  vertex_union : V(A) ∪ V(B) = V(G)
  vertex_inter : V(A) ∩ V(B) = {v}
  edge_union : E(A) ∪ E(B) = E(G)
  edge_disjoint : Disjoint E(A) E(B)
  two_le_A : 2 ≤ V(A).ncard
  two_le_B : 2 ≤ V(B).ncard
  A_card_lt : V(A).ncard < V(G).ncard
  B_card_lt : V(B).ncard < V(G).ncard

namespace CutSplit

theorem vertex_card_add (C : CutSplit G v) [G.Finite] :
    V(C.A).ncard + V(C.B).ncard = V(G).ncard + 1 := by
  have h := Set.ncard_union_add_ncard_inter V(C.A) V(C.B)
    ((finite_vertexSet G).subset C.A_le.vertexSet_mono)
    ((finite_vertexSet G).subset C.B_le.vertexSet_mono)
  rw [C.vertex_union, C.vertex_inter, Set.ncard_singleton] at h
  omega

theorem edge_card_add (C : CutSplit G v) [G.Finite] :
    E(C.A).ncard + E(C.B).ncard = E(G).ncard := by
  rw [← C.edge_union, Set.ncard_union_eq C.edge_disjoint
    ((finite_edgeSet G).subset C.A_le.edgeSet_mono)
    ((finite_edgeSet G).subset C.B_le.edgeSet_mono)]

end CutSplit

/-- A cut vertex of a finite loopless connected graph with at least three vertices gives two
strictly smaller connected induced pieces, meeting only in the cut vertex and partitioning
the edges. -/
theorem IsCutVertex.exists_cutSplit [G.Finite] [G.Loopless]
    (hcut : G.IsCutVertex v) (hconn : G.Connected)
    (hthree : G.HasThreeVertices) :
    Nonempty (CutSplit G v) := by
  classical
  let D := G.deleteVerts {v}
  have hDne : V(D).Nonempty := by
    obtain ⟨a, ha, hav, -⟩ := hthree.exists_ne_ne v v
    exact ⟨a, by
      rw [vertexSet_deleteVerts]
      exact ⟨ha, by simpa using hav⟩⟩
  have hpair : ∃ a ∈ V(D), ∃ b ∈ V(D), ¬ D.Reaches a b := by
    by_contra hn
    push_neg at hn
    exact hcut.2 ⟨hDne, fun u hu w hw => hn u hu w hw⟩
  obtain ⟨a, haD, b, hbD, hab⟩ := hpair
  let S := D.component a
  let H := G.induce (S ∪ {v})
  let K := G.induce (V(G) \ S)
  have haS : a ∈ S := mem_component_self haD
  have hbS : b ∉ S := hab
  have hSsubD : S ⊆ V(D) := component_subset_vertexSet
  have hSsubG : S ⊆ V(G) := hSsubD.trans deleteVerts_le.vertexSet_mono
  have hvG : v ∈ V(G) := hcut.1
  have hvS : v ∉ S := by
    intro hv
    exact (component_deleteVerts_subset hv).2 (by simp)
  have haG : a ∈ V(G) := deleteVerts_le.vertexSet_mono haD
  have hbG : b ∈ V(G) := deleteVerts_le.vertexSet_mono hbD
  have hav : a ≠ v := by
    intro h
    subst a
    rw [vertexSet_deleteVerts] at haD
    exact haD.2 (by simp)
  have hbv : b ≠ v := by
    intro h
    subst b
    rw [vertexSet_deleteVerts] at hbD
    exact hbD.2 (by simp)
  have hHG : H ≤ G := induce_le (Set.union_subset hSsubG (by simpa using hvG))
  have hKG : K ≤ G := induce_le Set.sdiff_subset
  have hHconn : H.Connected := by
    exact hconn.induce_component_deleteVerts_union_singleton hvG haD
  have hKconn : K.Connected := by
    refine Connected.of_hub (show v ∈ V(G) \ S from ⟨hvG, hvS⟩) ?_
    intro z hz
    change z ∈ V(G) \ S at hz
    by_cases hzv : z = v
    · subst z
      exact Reaches.refl (show v ∈ V(G) \ S from ⟨hvG, hvS⟩)
    · have hzD : z ∈ V(D) := by
        rw [vertexSet_deleteVerts]
        exact ⟨hz.1, by simpa using hzv⟩
      let C := D.component z
      let L := G.induce (C ∪ {v})
      have hzC : z ∈ C := mem_component_self hzD
      have hCS : Disjoint C S := by
        rcases component_eq_or_disjoint (G := D) z a with heq | hdis
        · have hzS : z ∈ S := by
            change z ∈ D.component a
            rw [← heq]
            exact hzC
          exact (hz.2 hzS).elim
        · exact hdis
      have hCsubK : C ∪ {v} ⊆ V(G) \ S := by
        intro x hx
        rcases hx with hxC | rfl
        · exact ⟨deleteVerts_le.vertexSet_mono (component_subset_vertexSet hxC),
            fun hxS => Set.disjoint_left.1 hCS hxC hxS⟩
        · exact ⟨hvG, hvS⟩
      have hLK : L ≤ K := by
        refine ⟨hCsubK, ?_⟩
        intro e x y hxy
        change G.IsLink e x y ∧ x ∈ C ∪ {v} ∧ y ∈ C ∪ {v} at hxy
        change G.IsLink e x y ∧ x ∈ V(G) \ S ∧ y ∈ V(G) \ S
        exact ⟨hxy.1, hCsubK hxy.2.1, hCsubK hxy.2.2⟩
      have hLconn : L.Connected :=
        hconn.induce_component_deleteVerts_union_singleton hvG hzD
      exact (hLconn.reaches (show v ∈ C ∪ {v} from Or.inr rfl)
        (show z ∈ C ∪ {v} from Or.inl hzC)).mono hLK
  have hVunion : V(H) ∪ V(K) = V(G) := by
    change (S ∪ {v}) ∪ (V(G) \ S) = V(G)
    ext x
    constructor
    · rintro ((hxS | rfl) | hx)
      · exact hSsubG hxS
      · exact hvG
      · exact hx.1
    · intro hx
      by_cases hxS : x ∈ S
      · exact Or.inl (Or.inl hxS)
      · exact Or.inr ⟨hx, hxS⟩
  have hVinter : V(H) ∩ V(K) = {v} := by
    change (S ∪ {v}) ∩ (V(G) \ S) = {v}
    ext x
    constructor
    · rintro ⟨hxS | hxv, hxG, hnotS⟩
      · exact (hnotS hxS).elim
      · simpa using hxv
    · rintro rfl
      exact ⟨Or.inr rfl, hvG, hvS⟩
  have hEunion : E(H) ∪ E(K) = E(G) := by
    apply Set.Subset.antisymm
    · exact Set.union_subset hHG.edgeSet_mono hKG.edgeSet_mono
    · intro e he
      obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
      by_cases hxS : x ∈ S
      · have hyH : y ∈ S ∪ {v} := by
          by_cases hyv : y = v
          · exact Or.inr hyv
          · exact Or.inl (mem_component_deleteVerts_of_isLink hxS hxy hyv)
        exact Or.inl (show e ∈ E(H) from
          (show H.IsLink e x y from ⟨hxy, Or.inl hxS, hyH⟩).edge_mem)
      · by_cases hyS : y ∈ S
        · have hxH : x ∈ S ∪ {v} := by
            by_cases hxv : x = v
            · exact Or.inr hxv
            · exact Or.inl (mem_component_deleteVerts_of_isLink hyS hxy.symm hxv)
          exact Or.inl (show e ∈ E(H) from
            (show H.IsLink e x y from ⟨hxy, hxH, Or.inl hyS⟩).edge_mem)
        · exact Or.inr (show e ∈ E(K) from
            (show K.IsLink e x y from
              ⟨hxy, ⟨hxy.left_mem, hxS⟩, ⟨hxy.right_mem, hyS⟩⟩).edge_mem)
  have hEdis : Disjoint E(H) E(K) := by
    rw [Set.disjoint_left]
    intro e heH heK
    obtain ⟨x, y, hHxy⟩ := exists_isLink_of_mem_edgeSet heH
    obtain ⟨p, q, hKpq⟩ := exists_isLink_of_mem_edgeSet heK
    change G.IsLink e x y ∧ x ∈ S ∪ {v} ∧ y ∈ S ∪ {v} at hHxy
    change G.IsLink e p q ∧ p ∈ V(G) \ S ∧ q ∈ V(G) \ S at hKpq
    rcases hHxy.1.eq_and_eq_or_eq_and_eq hKpq.1 with hpq | hpq
    · rcases hpq with ⟨rfl, rfl⟩
      have hxv : x = v := by
        rcases hHxy.2.1 with hxS | hxv
        · exact (hKpq.2.1.2 hxS).elim
        · simpa using hxv
      have hyv : y = v := by
        rcases hHxy.2.2 with hyS | hyv
        · exact (hKpq.2.2.2 hyS).elim
        · simpa using hyv
      subst x; subst y
      exact G.not_isLoopAt e v hHxy.1
    · rcases hpq with ⟨rfl, rfl⟩
      have hxv : x = v := by
        rcases hHxy.2.1 with hxS | hxv
        · exact (hKpq.2.2.2 hxS).elim
        · simpa using hxv
      have hyv : y = v := by
        rcases hHxy.2.2 with hyS | hyv
        · exact (hKpq.2.1.2 hyS).elim
        · simpa using hyv
      subst x; subst y
      exact G.not_isLoopAt e v hHxy.1
  have htwoH : 2 ≤ V(H).ncard := by
    have hlt : 1 < V(H).ncard := (Set.one_lt_ncard
      ((finite_vertexSet G).subset hHG.vertexSet_mono)).2
      ⟨a, Or.inl haS, v, Or.inr rfl, hav⟩
    omega
  have htwoK : 2 ≤ V(K).ncard := by
    have hlt : 1 < V(K).ncard := (Set.one_lt_ncard
      ((finite_vertexSet G).subset hKG.vertexSet_mono)).2
      ⟨b, ⟨hbG, hbS⟩, v, ⟨hvG, hvS⟩, hbv⟩
    omega
  have hltH : V(H).ncard < V(G).ncard := by
    apply Set.ncard_lt_ncard
      ⟨hHG.vertexSet_mono, fun hsub => hbS (show b ∈ S from by
        have hbH := hsub hbG
        change b ∈ S ∪ {v} at hbH
        exact hbH.resolve_right (by simpa using hbv))⟩
  have hltK : V(K).ncard < V(G).ncard := by
    apply Set.ncard_lt_ncard
      ⟨hKG.vertexSet_mono, fun hsub => (show a ∈ V(G) \ S from hsub haG).2 haS⟩
  exact ⟨⟨H, K, hHG, hKG, hHconn, hKconn, hVunion, hVinter, hEunion, hEdis,
    htwoH, htwoK, hltH, hltK⟩⟩

#print axioms Graph.IsCutVertex.exists_cutSplit

end Graph
