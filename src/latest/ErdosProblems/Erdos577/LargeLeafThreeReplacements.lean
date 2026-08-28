import ErdosProblems.Erdos577.LargeLeafThreeInside

/-! The exact low-column replacements and score comparisons for a three-contact leaf. -/

namespace Erdos577.LargeLeaf

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma three_leaf_low_replacement (q : Quadrilateral G) (x : V) (hx : x ∉ q.support)
    (hthree : degreeIn G x q.support = 3)
    (hrow : ∀ j : Fin 4, j ≠ 3 → G.Adj x (q j))
    (hd13 : G.Adj (q 1) (q 3)) (hd02 : ¬G.Adj (q 0) (q 2))
    (i : Fin 4) (hi : i = 0 ∨ i = 2) :
    QuadOn G (insert x (q.support.erase (q i))) ∧
      edgeCount G (insert x (q.support.erase (q i))) = edgeCount G q.support := by
  have hm : q i ∈ q.support := (q.mem_support _).mpr ⟨i, rfl⟩
  have hi3 : i ≠ 3 := by rcases hi with rfl | rfl <;> decide
  have herase := degreeIn_erase_add G x (q i) hm
  rw [if_pos (hrow i hi3), hthree] at herase
  have hlow : degreeIn G (q i) q.support = 2 := by
    rw [q.degreeIn_eq]
    rcases hi with rfl | rfl
    · change 2 + (if G.Adj (q 0) (q 2) then 1 else 0) = 2
      rw [if_neg hd02]
    · change 2 + (if G.Adj (q 2) (q 0) then 1 else 0) = 2
      rw [if_neg (fun hh ↦ hd02 hh.symm)]
  have hscore := edgeCount_replace G (q i) x hm hx
  exact ⟨q.three_contacts_universal_of_diagonal x hx hrow hd13 (q i) hm, by omega⟩

lemma two_contact_low_replacement (q : Quadrilateral G) (b : V) (hb : b ∉ q.support)
    (hd13 : G.Adj (q 1) (q 3)) (hdegree : 2 ≤ degreeIn G b q.support)
    (hnot : ¬(G.Adj b (q 0) ∧ G.Adj b (q 2))) :
    ∃ i : Fin 4, (i = 0 ∨ i = 2) ∧ QuadOn G (insert b (q.support.erase (q i))) := by
  obtain ⟨i, j, hij, hi, hj⟩ := q.exists_two_neighbor_indices b hdegree
  obtain ⟨tag, he⟩ := FullRow.PairTable.coverage i j hij
  have hfirst : G.Adj b (q (FullRow.PairTable.first tag)) := by
    rcases he with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rwa [h1]
  have hsecond : G.Adj b (q (FullRow.PairTable.second tag)) := by
    rcases he with ⟨_, h2⟩ | ⟨_, h2⟩ <;> rwa [h2]
  have htag : tag ≠ 1 := by
    intro hh
    subst tag
    exact hnot ⟨hfirst, hsecond⟩
  have hlow : ∀ t : Fin 6, t ≠ 1 →
      FullRow.PairTable.removed t = 0 ∨ FullRow.PairTable.removed t = 2 := by decide +kernel
  exact ⟨FullRow.PairTable.removed tag, hlow tag htag,
    FullRow.PairTable.replacement q b hb hd13 tag hfirst hsecond⟩

end Erdos577.LargeLeaf
