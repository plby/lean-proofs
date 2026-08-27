import Arxiv.Arxiv2411_18291.Decomposition
import Mathlib.Data.Nat.Choose.Bounds

/-!
# The codegree bound for clique removal

Two distinct edges force at least one extra vertex in any clique that
contains both. Consequently their common clique degree is at most
`n^(q-r-1)`, uniformly over every subfamily of the complete clique family.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem clique_root_count_le_power (H : Finset (Block V q)) (I : Finset V)
    (hIq : I.card ≤ q) :
    (H.filter fun Q => I ⊆ Q.val).card ≤ (Fintype.card V) ^ (q - I.card) := by
  have hsub : H.filter (fun Q => I ⊆ Q.val) ⊆
      univ.filter (fun Q : Block V q => I ⊆ Q.val ∧ Q.val ⊆ univ) := by
    intro Q hQ
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hQ).2, subset_univ _⟩
  calc
    _ ≤ (univ.filter fun Q : Block V q => I ⊆ Q.val ∧ Q.val ⊆ univ).card :=
      card_le_card hsub
    _ = ((Fintype.card V) - I.card).choose (q - I.card) := by
      simpa only [card_univ] using card_blocks_between I univ (subset_univ I) hIq
    _ ≤ ((Fintype.card V) - I.card) ^ (q - I.card) := Nat.choose_le_pow _ _
    _ ≤ _ := Nat.pow_le_pow_left (Nat.sub_le _ _) _

theorem clique_codegree_le_power (hqr : r < q) (H : Finset (Block V q))
    (e f : Block V r) (hef : e ≠ f) :
    (H.filter fun Q => e.val ⊆ Q.val ∧ f.val ⊆ Q.val).card ≤
      (Fintype.card V) ^ (q - r - 1) := by
  have hnot : ¬f.val ⊆ e.val := by
    intro h
    apply hef
    apply Subtype.ext
    exact (eq_of_subset_of_card_le h (by rw [e.property, f.property])).symm
  obtain ⟨x, hxf, hxe⟩ := not_subset.mp hnot
  let I := insert x e.val
  have hI : I.card = r + 1 := by simp only [I, card_insert_of_notMem hxe, e.property]
  have hsub : H.filter (fun Q => e.val ⊆ Q.val ∧ f.val ⊆ Q.val) ⊆
      H.filter (fun Q => I ⊆ Q.val) := by
    intro Q hQ
    obtain ⟨hQH, heQ, hfQ⟩ := mem_filter.mp hQ
    exact mem_filter.mpr ⟨hQH, insert_subset_iff.mpr ⟨hfQ hxf, heQ⟩⟩
  calc
    _ ≤ (H.filter fun Q => I ⊆ Q.val).card := card_le_card hsub
    _ ≤ (Fintype.card V) ^ (q - I.card) :=
      clique_root_count_le_power H I (by rw [hI]; omega)
    _ = _ := congrArg (fun k => (Fintype.card V) ^ k) (by omega)

end Arxiv2411_18291
