import ErdosProblems.Erdos547.ForestPieces

/-!
# Small separators of finite forests

For every positive integer `q`, a forest has at most `n/q` cut vertices
after whose deletion each connected induced subset has at most `2*q-1`
vertices.  The proof removes disjoint pendant pieces and charges each cut
vertex to at least `q` removed vertices.
-/

namespace Erdos547

open Finset SimpleGraph

universe u

private theorem forest_separator_aux (n : ℕ) :
    ∀ (U : Type u) [Fintype U] (T : SimpleGraph U), T.IsAcyclic → Fintype.card U ≤ n →
      ∀ q : ℕ, 1 ≤ q → ∃ W : Finset U, q * W.card ≤ Fintype.card U ∧
        ∀ B : Finset U, Disjoint B W → (T.induce (B : Set U)).Connected →
          B.card ≤ 2 * q - 1 := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro U inst T hT hn q hq
      by_cases hsmall : ∀ B : Finset U, (T.induce (B : Set U)).Connected →
          B.card ≤ 2 * q - 1
      · exact ⟨∅, by simp, fun B _ hB ↦ hsmall B hB⟩
      push Not at hsmall
      obtain ⟨B₀, hB₀, hlarge⟩ := hsmall
      obtain ⟨S, r, hSlo, hShi, hS⟩ := exists_bounded_forest_piece T hT q hq
        B₀ hB₀ (by omega)
      let A : Finset U := Sᶜ
      let H : SimpleGraph (A : Set U) := T.induce (A : Set U)
      have htotal : A.card + S.card = Fintype.card U := by
        simpa only [A, Finset.card_univ] using Finset.card_compl_add_card S
      have hAn : Fintype.card ↥(A : Set U) < n := by
        have hh : A.card < n := by omega
        simpa using hh
      obtain ⟨W', hW'count, hW'⟩ := ih (Fintype.card ↥(A : Set U)) hAn
        ↥(A : Set U) H (hT.induce _) le_rfl q hq
      let W : Finset U := insert r (W'.image Subtype.val)
      have hrA : r ∉ A := fun h ↦ (Finset.mem_compl.mp h) hS.root_mem
      have hrW' : r ∉ W'.image Subtype.val := by
        intro hr
        obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hr
        exact hrA (heq ▸ v.property)
      have hWcard : W.card = W'.card + 1 := by
        simp only [W, Finset.card_insert_of_notMem hrW',
          Finset.card_image_of_injective _ Subtype.val_injective]
      refine ⟨W, ?_, ?_⟩
      · rw [hWcard]
        have hh : q * W'.card ≤ A.card := by simpa using hW'count
        nlinarith only [hh, hSlo, htotal]
      · intro B hdis hB
        have hrB : r ∉ B := by
          intro hr
          exact Finset.disjoint_left.mp hdis hr (Finset.mem_insert_self _ _)
        by_cases hmeet : ((B : Set U) ∩ (S : Set U)).Nonempty
        · have hsub := connected_subset_of_meets_rooted_piece T hS
            hB.preconnected hrB hmeet
          exact (Finset.card_le_card hsub).trans hShi
        have hBA : B ⊆ A := by
          intro v hv
          apply Finset.mem_compl.mpr
          intro hvS
          exact hmeet ⟨v, hv, hvS⟩
        let B' : Finset ↥(A : Set U) := B.subtype (fun v ↦ v ∈ A)
        have hB'card : B'.card = B.card := by
          simp only [B', Finset.card_subtype, Finset.filter_eq_self.mpr hBA]
        have hB'conn : (H.induce (B' : Set ↥(A : Set U))).Connected := by
          let f : (T.induce (B : Set U)) →g (H.induce (B' : Set ↥(A : Set U))) := {
            toFun := fun v ↦ ⟨⟨v.val, hBA v.property⟩, Finset.mem_subtype.mpr v.property⟩
            map_rel' := fun h ↦ h }
          have hsurj : Function.Surjective f := by
            rintro ⟨v, hv⟩
            exact ⟨⟨v.val, Finset.mem_subtype.mp hv⟩, rfl⟩
          exact hB.map f hsurj
        have hdis' : Disjoint B' W' := by
          apply Finset.disjoint_left.mpr
          intro v hvB hvW
          exact Finset.disjoint_left.mp hdis (Finset.mem_subtype.mp hvB)
            (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨v, hvW, rfl⟩))
        rw [← hB'card]
        exact hW' B' hdis' hB'conn

theorem exists_forest_separator {U : Type u} [Fintype U] (T : SimpleGraph U)
    (hT : T.IsAcyclic) (q : ℕ) (hq : 1 ≤ q) :
    ∃ W : Finset U, q * W.card ≤ Fintype.card U ∧
      ∀ B : Finset U, Disjoint B W → (T.induce (B : Set U)).Connected →
        B.card ≤ 2 * q - 1 :=
  forest_separator_aux (Fintype.card U) U T hT le_rfl q hq

open scoped Classical in
theorem exists_rooted_tree_separator {U : Type u} [Fintype U] (T : SimpleGraph U)
    (hT : T.IsTree) (r : U) (q : ℕ) (hq : 1 ≤ q) :
    ∃ W : Finset U, r ∈ W ∧ q * W.card ≤ Fintype.card U + q ∧
      ∀ B : Finset U, Disjoint B W → (T.induce (B : Set U)).Connected →
        B.card ≤ 2 * q - 1 := by
  classical
  obtain ⟨W, hcount, hcut⟩ := exists_forest_separator T hT.isAcyclic q hq
  refine ⟨insert r W, Finset.mem_insert_self _ _, ?_, ?_⟩
  · have hcard := Finset.card_insert_le r W
    calc
      q * (insert r W).card ≤ q * (W.card + 1) := Nat.mul_le_mul_left q hcard
      _ ≤ Fintype.card U + q := by nlinarith only [hcount]
  · intro B hdis hB
    exact hcut B (hdis.mono_right (Finset.subset_insert _ _)) hB

end Erdos547

#print axioms Erdos547.exists_forest_separator
#print axioms Erdos547.exists_rooted_tree_separator
