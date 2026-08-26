import ErdosProblems.Erdos547.ShrubState

/-!
# Counting images in disjoint clusters
-/

namespace Erdos547

open Finset
open scoped BigOperators

theorem card_coe_filter_univ {U : Type*} [DecidableEq U]
    (S : Finset U) (p : U → Prop) [DecidablePred p] :
    ((Finset.univ : Finset ↥S).filter (fun v ↦ p v.val)).card = (S.filter p).card := by
  rw [← Finset.attach_eq_univ, Finset.filter_attach, Finset.card_map, Finset.card_attach]

theorem card_cluster_image_le_two_parts {A V I : Type*} [Fintype A]
    [DecidableEq V] [DecidableEq I] (C : I → Finset V)
    (hC : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (f : A → V) (p : A → Prop) [DecidablePred p] (a b i : I)
    (ha : ∀ x, p x → f x ∈ C a) (hb : ∀ x, ¬p x → f x ∈ C b) :
    ((C i) ∩ Finset.univ.image f).card ≤
      (if a = i then (Finset.univ.filter p).card else 0) +
      (if b = i then (Finset.univ.filter (fun x ↦ ¬p x)).card else 0) := by
  classical
  let A₀ := if a = i then Finset.univ.filter p else ∅
  let A₁ := if b = i then Finset.univ.filter (fun x ↦ ¬p x) else ∅
  have hsub : C i ∩ Finset.univ.image f ⊆ A₀.image f ∪ A₁.image f := by
    intro v hv
    obtain ⟨hvi, hv⟩ := Finset.mem_inter.mp hv
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hv
    by_cases hp : p x
    · have hai : a = i := by
        by_contra hne
        exact Finset.disjoint_left.mp (hC a i hne) (ha x hp) hvi
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨x, ?_, rfl⟩
      simp only [A₀, if_pos hai, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hp
    · have hbi : b = i := by
        by_contra hne
        exact Finset.disjoint_left.mp (hC b i hne) (hb x hp) hvi
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨x, ?_, rfl⟩
      simp only [A₁, if_pos hbi, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hp
  calc
    _ ≤ (A₀.image f ∪ A₁.image f).card := Finset.card_le_card hsub
    _ ≤ (A₀.image f).card + (A₁.image f).card := Finset.card_union_le _ _
    _ ≤ A₀.card + A₁.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = _ := by simp only [A₀, A₁, apply_ite Finset.card, Finset.card_empty]

theorem card_inter_union_family_le {V A : Type*} [Fintype A] [DecidableEq V]
    (X W : Finset V) (F : A → Finset V) :
    (X ∩ (W ∪ Finset.univ.biUnion F)).card ≤ W.card + ∑ a, (X ∩ F a).card := by
  have hsub : X ∩ (W ∪ Finset.univ.biUnion F) ⊆
      W ∪ Finset.univ.biUnion (fun a ↦ X ∩ F a) := by
    intro v hv
    obtain ⟨hvX, hv⟩ := Finset.mem_inter.mp hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.mem_union_left _ hv
    · obtain ⟨a, ha, hva⟩ := Finset.mem_biUnion.mp hv
      exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_inter.mpr ⟨hvX, hva⟩⟩)
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_left Finset.card_biUnion_le W.card))

end Erdos547
