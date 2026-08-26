import ErdosProblems.Erdos19.ReservoirCompletion

/-! # Reservoir completion on a prescribed even vertex set

All graphs remain on the ambient vertex type. Omitted vertices contribute an
explicit term to the degree margin; the returned matching covers exactly the
prescribed set.
-/

namespace Erdos19

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

theorem exists_matching_on_set_using_reservoir {V : Type*} [Fintype V] [DecidableEq V]
    (G R : _root_.SimpleGraph V) (hRG : R ≤ G) (A : Set V) (heven : Even A.ncard) (q : ℕ)
    (hcut : ∀ X Y : Finset V, Disjoint X Y → X.card = q → Y.card = q →
      q < (R.between (X : Set V) (Y : Set V)).edgeFinset.card)
    (M : G.Subgraph) (hM : M.IsMatching) (hMA : M.verts ⊆ A)
    (Z : Finset V) (hZM : (Z : Set V) ⊆ M.verts)
    (hdegree : ∀ v ∈ A,
      2 * q + 2 * Z.card + 7 * (A \ M.verts).ncard + Aᶜ.ncard + 1 ≤ R.degree v) :
    ∃ N : G.Subgraph, ∃ T : Finset V, N.IsMatching ∧ N.verts = A ∧
      T.card ≤ 3 * (A \ M.verts).ncard ∧ Disjoint T Z ∧
      ∀ e ∈ N.edgeSet \ M.edgeSet, e ∈ R.edgeSet ∧ ∀ x ∈ e, x ∈ T := by
  classical
  have aux : ∀ m : ℕ, ∀ M : G.Subgraph, M.IsMatching → M.verts ⊆ A →
      (A \ M.verts).ncard = m → ∀ Z : Finset V, (Z : Set V) ⊆ M.verts →
      (∀ v ∈ A, 2 * q + 2 * Z.card + 7 * m + Aᶜ.ncard + 1 ≤ R.degree v) →
      ∃ N : G.Subgraph, ∃ T : Finset V, N.IsMatching ∧ N.verts = A ∧
        T.card ≤ 3 * m ∧ Disjoint T Z ∧
        ∀ e ∈ N.edgeSet \ M.edgeSet, e ∈ R.edgeSet ∧ ∀ x ∈ e, x ∈ T := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro M hM hMA hm Z hZM hd
      by_cases hm0 : m = 0
      · have hverts : M.verts = A := by
          apply Set.Subset.antisymm hMA
          intro v hv
          by_contra hvM
          have hpos := (Set.ncard_pos (Set.toFinite (A \ M.verts))).mpr ⟨v, hv, hvM⟩
          omega
        refine ⟨M, ∅, hM, hverts, by simp, by simp, ?_⟩
        intro e he
        exact (he.2 he.1).elim
      have htotal : M.verts.ncard + m = A.ncard := by
        rw [← hm, Set.ncard_sdiff hMA]
        have hle := Set.ncard_le_ncard hMA
        omega
      have hcompl : M.vertsᶜ.ncard = m + Aᶜ.ncard := by
        have h₁ := Set.ncard_add_ncard_compl M.verts
        have h₂ := Set.ncard_add_ncard_compl A
        omega
      have hm2 : 2 ≤ m := by
        obtain ⟨a, ha⟩ := heven
        have hverts := matching_verts_ncard_generic M hM
        omega
      obtain ⟨u, huA, hu⟩ := (Set.ncard_pos (Set.toFinite (A \ M.verts))).mp
        (show 0 < (A \ M.verts).ncard by omega)
      obtain ⟨v, hvAv, hvu⟩ := Set.exists_ne_of_one_lt_ncard
        (show 1 < (A \ M.verts).ncard by omega) u
      have hvA := hvAv.1
      have hv := hvAv.2
      let Q := R.deleteEdges M.edgeSet
      letI : DecidableRel Q.Adj := fun x y ↦ Classical.propDecidable (Q.Adj x y)
      have hQG : Q ≤ G := (R.deleteEdges_le M.edgeSet).trans hRG
      have hdis : Disjoint M.edgeSet Q.edgeSet := by
        rw [edgeSet_deleteEdges]
        exact Set.disjoint_sdiff_right
      have hdu : 2 * q + 2 * Z.card + M.vertsᶜ.ncard ≤ Q.degree u := by
        have h : R.degree u ≤ Q.degree u + 1 := by
          simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using
            degree_le_delete_matching_add_one R M hM u
        have h' := hd u huA
        omega
      have hdv : 2 * q + 2 * Z.card + M.vertsᶜ.ncard ≤ Q.degree v := by
        have h : R.degree v ≤ Q.degree v + 1 := by
          simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using
            degree_le_delete_matching_add_one R M hM v
        have h' := hd v hvA
        omega
      have hQcut : ∀ X Y : Finset V, Disjoint X Y → X.card = q → Y.card = q →
          ∃ x ∈ X, ∃ y ∈ Y, Q.Adj x y := by
        intro X Y hXY hX hY
        apply delete_matching_has_cross_edge R M hM X Y hXY
        rw [hX]
        exact hcut X Y hXY hX hY
      obtain ⟨M₁, T₁, hM₁, hM₁v, _, hT₁M, hT₁card, hT₁Z, hnew₁⟩ :=
        exists_reservoir_augmentation M hM Q hQG hdis Z u v hu hv hvu.symm
          (fun hz ↦ hu (hZM hz)) (fun hz ↦ hv (hZM hz)) q hdu hdv hQcut
      have hM₁A : M₁.verts ⊆ A := by
        rw [hM₁v]
        exact Set.insert_subset huA (Set.insert_subset hvA hMA)
      have hM₁card : M₁.verts.ncard = M.verts.ncard + 2 := by
        rw [hM₁v, Set.ncard_insert_of_notMem (by
          rintro (heq | hmem)
          · exact hvu heq.symm
          · exact hu hmem), Set.ncard_insert_of_notMem hv]
      have hremaining : (A \ M₁.verts).ncard + 2 = m := by
        rw [Set.ncard_sdiff hM₁A]
        have hle := Set.ncard_le_ncard hM₁A
        omega
      have hless : (A \ M₁.verts).ncard < m := by omega
      let Z₁ := Z ∪ T₁
      have hZ₁M : (Z₁ : Set V) ⊆ M₁.verts := by
        intro x hx
        rcases mem_union.mp hx with hx | hx
        · rw [hM₁v]
          exact Or.inr (Or.inr (hZM hx))
        · exact hT₁M hx
      have hZ₁card : Z₁.card ≤ Z.card + 6 := by
        simpa only [hT₁card] using card_union_le Z T₁
      have hd₁ : ∀ v ∈ A,
          2 * q + 2 * Z₁.card + 7 * (A \ M₁.verts).ncard + Aᶜ.ncard + 1 ≤ R.degree v := by
        intro w hwA
        have hw := hd w hwA
        omega
      obtain ⟨N, T₂, hN, hNA, hT₂card, hT₂Z, hnew₂⟩ :=
        ih (A \ M₁.verts).ncard hless M₁ hM₁ hM₁A rfl Z₁ hZ₁M hd₁
      refine ⟨N, T₁ ∪ T₂, hN, hNA, ?_, ?_, ?_⟩
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
          have heR : e ∈ R.edgeSet := (by rw [edgeSet_deleteEdges] at heQ; exact heQ.1)
          exact ⟨heR, fun x hx ↦ mem_union_left _ (hsupport x hx)⟩
        · obtain ⟨heR, hsupport⟩ := hnew₂ e ⟨he.1, heM₁⟩
          exact ⟨heR, fun x hx ↦ mem_union_right _ (hsupport x hx)⟩
  exact aux _ M hM hMA rfl Z hZM hdegree

#print axioms exists_matching_on_set_using_reservoir

end Erdos19
