import ErdosProblems.Erdos19.MatchingRotation

/-! # A length-five alternating augmentation with edge accounting -/

namespace Erdos19

open _root_.SimpleGraph

theorem exists_matching_augment_five {V : Type*} [Fintype V]
    {G : _root_.SimpleGraph V} (M : G.Subgraph) (hM : M.IsMatching)
    (v : Fin 6 → V) (hinj : Function.Injective v)
    (h0 : v 0 ∉ M.verts) (h5 : v 5 ∉ M.verts)
    (h12 : M.Adj (v 1) (v 2)) (h34 : M.Adj (v 3) (v 4))
    (h01 : G.Adj (v 0) (v 1)) (h23 : G.Adj (v 2) (v 3)) (h45 : G.Adj (v 4) (v 5)) :
    ∃ N : G.Subgraph, N.IsMatching ∧
      N.verts = insert (v 0) (insert (v 5) M.verts) ∧
      N.edgeSet.ncard = M.edgeSet.ncard + 1 ∧
      N.edgeSet ⊆ M.edgeSet ∪ {s(v 0, v 1), s(v 2, v 3), s(v 4, v 5)} := by
  classical
  obtain ⟨M₁, hM₁, hM₁v, _, hM₁e, hM₁keep⟩ :=
    exists_matching_rotation_with_edge_control M hM h0 h12 h01
  have h34' : M₁.Adj (v 3) (v 4) := hM₁keep _ _ h34
    (hinj.ne (by decide)) (hinj.ne (by decide))
    (hinj.ne (by decide)) (hinj.ne (by decide))
  have h2 : v 2 ∉ M₁.verts := by
    rw [hM₁v]
    rintro (heq | hmem)
    · exact hinj.ne (by decide : (2 : Fin 6) ≠ 0) heq
    · exact hmem.2 rfl
  have h5' : v 5 ∉ M₁.verts := by
    rw [hM₁v]
    rintro (heq | hmem)
    · exact hinj.ne (by decide : (5 : Fin 6) ≠ 0) heq
    · exact h5 hmem.1
  obtain ⟨M₂, hM₂, hM₂v, _, hM₂e, _⟩ :=
    exists_matching_rotation_with_edge_control M₁ hM₁ h2 h34' h23
  have h4 : v 4 ∉ M₂.verts := by
    rw [hM₂v]
    rintro (heq | hmem)
    · exact hinj.ne (by decide : (4 : Fin 6) ≠ 2) heq
    · exact hmem.2 rfl
  have h5'' : v 5 ∉ M₂.verts := by
    rw [hM₂v]
    rintro (heq | hmem)
    · exact hinj.ne (by decide : (5 : Fin 6) ≠ 2) heq
    · exact h5' hmem.1
  let P := G.subgraphOfAdj h45
  have hP : P.IsMatching := Subgraph.IsMatching.subgraphOfAdj h45
  have hPv : P.verts = {v 4, v 5} := by simp [P]
  have hdis : Disjoint M₂.support P.support := by
    rw [hM₂.support_eq_verts, hP.support_eq_verts, hPv, Set.disjoint_left]
    intro x hx hxp
    rcases hxp with rfl | rfl
    · exact h4 hx
    · exact h5'' hx
  let N := M₂ ⊔ P
  have hN : N.IsMatching := hM₂.sup hP hdis
  have hNv : N.verts = insert (v 0) (insert (v 5) M.verts) := by
    calc
      N.verts = insert (v 5) (insert (v 4) M₂.verts) := by
        ext x
        simp only [N, Subgraph.verts_sup, hPv, Set.mem_union, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        tauto
      _ = insert (v 5) (insert (v 4) (insert (v 2) (M₁.verts \ {v 4}))) := by rw [hM₂v]
      _ = insert (v 5) (insert (v 2) (insert (v 4) (M₁.verts \ {v 4}))) := by
        rw [Set.insert_comm (v 4) (v 2)]
      _ = insert (v 5) (insert (v 2) M₁.verts) := by
        rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem h34'.snd_mem]
      _ = insert (v 5) (insert (v 2) (insert (v 0) (M.verts \ {v 2}))) := by rw [hM₁v]
      _ = insert (v 5) (insert (v 0) (insert (v 2) (M.verts \ {v 2}))) := by
        rw [Set.insert_comm (v 2) (v 0)]
      _ = insert (v 5) (insert (v 0) M.verts) := by
        rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem h12.snd_mem]
      _ = insert (v 0) (insert (v 5) M.verts) := Set.insert_comm _ _ _
  have hNcard : N.edgeSet.ncard = M.edgeSet.ncard + 1 := by
    have hvcard : N.verts.ncard = M.verts.ncard + 2 := by
      rw [hNv, Set.ncard_insert_of_notMem (by
        rintro (heq | hmem)
        · exact hinj.ne (by decide : (0 : Fin 6) ≠ 5) heq
        · exact h0 hmem), Set.ncard_insert_of_notMem h5]
    rw [matching_verts_ncard_generic N hN, matching_verts_ncard_generic M hM] at hvcard
    omega
  refine ⟨N, hN, hNv, hNcard, ?_⟩
  have hPe : P.edgeSet = {s(v 4, v 5)} := by simp [P]
  intro e he
  change e ∈ (M₂ ⊔ P).edgeSet at he
  rw [Subgraph.edgeSet_sup, hPe] at he
  rcases he with he | he
  · rcases hM₂e he with he | he
    · rcases hM₁e he with he | he
      · exact Or.inl he
      · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr (Or.inl he))
  · exact Or.inr (Or.inr (Or.inr he))

#print axioms exists_matching_augment_five

end Erdos19
