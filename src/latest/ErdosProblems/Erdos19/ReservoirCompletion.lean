import ErdosProblems.Erdos19.ReservoirAugmentation
import ErdosProblems.Erdos19.MatchingDeletion

/-! # Completing one matching with a bounded reservoir footprint

Each augmentation covers two new vertices and touches six vertices outside
the forbidden set. The factor seven in the degree margin allows all vertices
touched earlier in the round to be excluded from later augmentations.
-/

namespace Erdos19

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

theorem exists_perfect_matching_using_reservoir {V : Type*} [Fintype V] [DecidableEq V]
    (G R : _root_.SimpleGraph V) (hRG : R ≤ G) (heven : Even (Fintype.card V)) (q : ℕ)
    (hcut : ∀ A B : Finset V, Disjoint A B → A.card = q → B.card = q →
      q < (R.between (A : Set V) (B : Set V)).edgeFinset.card)
    (M : G.Subgraph) (hM : M.IsMatching) (Z : Finset V) (hZM : (Z : Set V) ⊆ M.verts)
    (hdegree : ∀ v, 2 * q + 2 * Z.card + 7 * M.vertsᶜ.ncard + 1 ≤ R.degree v) :
    ∃ N : G.Subgraph, ∃ T : Finset V, N.IsPerfectMatching ∧
      T.card ≤ 3 * M.vertsᶜ.ncard ∧ Disjoint T Z ∧
      ∀ e ∈ N.edgeSet \ M.edgeSet, e ∈ R.edgeSet ∧ ∀ x ∈ e, x ∈ T := by
  classical
  have aux : ∀ m : ℕ, ∀ M : G.Subgraph, M.IsMatching → M.vertsᶜ.ncard = m →
      ∀ Z : Finset V, (Z : Set V) ⊆ M.verts →
      (∀ v, 2 * q + 2 * Z.card + 7 * m + 1 ≤ R.degree v) →
      ∃ N : G.Subgraph, ∃ T : Finset V, N.IsPerfectMatching ∧
        T.card ≤ 3 * m ∧ Disjoint T Z ∧
        ∀ e ∈ N.edgeSet \ M.edgeSet, e ∈ R.edgeSet ∧ ∀ x ∈ e, x ∈ T := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro M hM hm Z hZM hd
      by_cases hm0 : m = 0
      · have hperfect : M.IsPerfectMatching := by
          refine ⟨hM, ?_⟩
          intro v
          by_contra hv
          have hpos := (Set.ncard_pos (Set.toFinite M.vertsᶜ)).mpr ⟨v, hv⟩
          omega
        refine ⟨M, ∅, hperfect, by simp, by simp, ?_⟩
        intro e he
        exact (he.2 he.1).elim
      have htotal : M.verts.ncard + m = Fintype.card V := by
        simpa only [hm, Nat.card_eq_fintype_card] using Set.ncard_add_ncard_compl M.verts
      have hm2 : 2 ≤ m := by
        obtain ⟨a, ha⟩ := heven
        have hverts := matching_verts_ncard_generic M hM
        omega
      obtain ⟨u, hu⟩ := (Set.ncard_pos (Set.toFinite M.vertsᶜ)).mp (show 0 < M.vertsᶜ.ncard by omega)
      obtain ⟨v, hv, hvu⟩ := Set.exists_ne_of_one_lt_ncard (show 1 < M.vertsᶜ.ncard by omega) u
      let Q := R.deleteEdges M.edgeSet
      let : DecidableRel Q.Adj := fun x y ↦ Classical.propDecidable (Q.Adj x y)
      have hQG : Q ≤ G := (R.deleteEdges_le M.edgeSet).trans hRG
      have hdis : Disjoint M.edgeSet Q.edgeSet := by
        rw [edgeSet_deleteEdges]
        exact Set.disjoint_sdiff_right
      have hdu : 2 * q + 2 * Z.card + M.vertsᶜ.ncard ≤ Q.degree u := by
        have h : R.degree u ≤ Q.degree u + 1 := by
          simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using
            degree_le_delete_matching_add_one R M hM u
        have h' := hd u
        omega
      have hdv : 2 * q + 2 * Z.card + M.vertsᶜ.ncard ≤ Q.degree v := by
        have h : R.degree v ≤ Q.degree v + 1 := by
          simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using
            degree_le_delete_matching_add_one R M hM v
        have h' := hd v
        omega
      have hQcut : ∀ A B : Finset V, Disjoint A B → A.card = q → B.card = q →
          ∃ x ∈ A, ∃ y ∈ B, Q.Adj x y := by
        intro A B hAB hA hB
        apply delete_matching_has_cross_edge R M hM A B hAB
        rw [hA]
        exact hcut A B hAB hA hB
      obtain ⟨M₁, T₁, hM₁, hM₁v, _, hT₁M, hT₁card, hT₁Z, hnew₁⟩ :=
        exists_reservoir_augmentation M hM Q hQG hdis Z u v hu hv hvu.symm
          (fun hz ↦ hu (hZM hz)) (fun hz ↦ hv (hZM hz)) q hdu hdv hQcut
      have hM₁card : M₁.verts.ncard = M.verts.ncard + 2 := by
        rw [hM₁v, Set.ncard_insert_of_notMem (by
          rintro (heq | hmem)
          · exact hvu heq.symm
          · exact hu hmem), Set.ncard_insert_of_notMem hv]
      have hremaining : M₁.vertsᶜ.ncard + 2 = m := by
        have ht := Set.ncard_add_ncard_compl M₁.verts
        rw [Nat.card_eq_fintype_card] at ht
        omega
      have hless : M₁.vertsᶜ.ncard < m := by omega
      let Z₁ := Z ∪ T₁
      have hZ₁M : (Z₁ : Set V) ⊆ M₁.verts := by
        intro x hx
        rcases mem_union.mp hx with hx | hx
        · rw [hM₁v]
          exact Or.inr (Or.inr (hZM hx))
        · exact hT₁M hx
      have hZ₁card : Z₁.card ≤ Z.card + 6 := by
        simpa only [hT₁card] using card_union_le Z T₁
      have hd₁ : ∀ v, 2 * q + 2 * Z₁.card + 7 * M₁.vertsᶜ.ncard + 1 ≤ R.degree v := by
        intro w
        have hw := hd w
        omega
      obtain ⟨N, T₂, hN, hT₂card, hT₂Z, hnew₂⟩ :=
        ih M₁.vertsᶜ.ncard hless M₁ hM₁ rfl Z₁ hZ₁M hd₁
      refine ⟨N, T₁ ∪ T₂, hN, ?_, ?_, ?_⟩
      · have hcard := card_union_le T₁ T₂
        omega
      · apply Finset.disjoint_left.mpr
        intro x hx hxZ
        rcases mem_union.mp hx with hx | hx
        · exact Finset.disjoint_left.mp hT₁Z hx hxZ
        · exact Finset.disjoint_left.mp hT₂Z hx (mem_union_left _ hxZ)
      · intro e he
        by_cases heM₁ : e ∈ M₁.edgeSet
        · obtain ⟨heQ, hsupport⟩ := hnew₁ e ⟨heM₁, he.2⟩
          have heR : e ∈ R.edgeSet := (by
            rw [edgeSet_deleteEdges] at heQ
            exact heQ.1)
          exact ⟨heR, fun x hx ↦ mem_union_left _ (hsupport x hx)⟩
        · obtain ⟨heR, hsupport⟩ := hnew₂ e ⟨he.1, heM₁⟩
          exact ⟨heR, fun x hx ↦ mem_union_right _ (hsupport x hx)⟩
  exact aux _ M hM rfl Z hZM hdegree

#print axioms exists_perfect_matching_using_reservoir

end Erdos19
