import ErdosProblems.Erdos577.FirstPawClassification
import ErdosProblems.Erdos577.WeightedRows
import ErdosProblems.Erdos577.PathRowCounts
import ErdosProblems.Erdos577.PawEleven

/-! A one-contact leaf permits at most nine total contacts in the first paw classification. -/

namespace Erdos577.PawBlock

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma ExactRows.contacts_eq (p : Paw G) (q : Quadrilateral G) (rows : Fin 4 → ℕ)
    (h : ExactRows p q rows) :
    contacts G p.support q.support = ∑ i : Fin 4, ∑ j : Fin 4, ((rows i).testBit j.val).toNat := by
  have hrow (i : Fin 4) := WeightedPawBlock.Row.degree p q i (rows i) (h i)
  rw [p.contacts_support, p.contacts_triangle]
  change degreeIn G (p.vertices 0) q.support + (degreeIn G (p.vertices 1) q.support +
    (degreeIn G (p.vertices 2) q.support + degreeIn G (p.vertices 3) q.support)) = _
  conv_rhs => rw [Fin.sum_univ_four]
  rw [hrow 0, hrow 1, hrow 2, hrow 3]
  omega

lemma PatternsWithOutside.one_leaf_bound (p : Paw G) (q : Quadrilateral G)
    (h : PatternsWithOutside p q) (hleaf : degreeIn G p.leaf q.support = 1) :
    contacts G p.support q.support ≤ 9 := by
  have hsum := p.contacts_support q.support
  rw [p.contacts_triangle] at hsum
  have h5 : ∀ j : Fin 4, (j = 0 ∨ j = 2) → (5 : ℕ).testBit j.val = true := by decide +kernel
  have h13 : ∀ j : Fin 4, j ≠ 1 → (13 : ℕ).testBit j.val = true := by decide +kernel
  have h7 : ∀ j : Fin 4, j ≠ 3 → (7 : ℕ).testBit j.val = true := by decide +kernel
  have hm5 : (∑ j : Fin 4, ((5 : ℕ).testBit j.val).toNat) = 2 := by decide +kernel
  have hm13 : (∑ j : Fin 4, ((13 : ℕ).testBit j.val).toNat) = 3 := by decide +kernel
  have hm7 : (∑ j : Fin 4, ((7 : ℕ).testBit j.val).toNat) = 3 := by decide +kernel
  rcases h with h | h | h | h | h | h
  · rw [h.1.2.contacts_eq p q ![1, 15, 9, 3]]
    decide +kernel
  · have hb := q.degree_le_mask (p.vertices 2) 5
      (fun j hj ↦ h5 j (h.2.2.2 j (Or.inr (Or.inl hj))))
    have hc := q.degree_le_mask (p.vertices 3) 5
      (fun j hj ↦ h5 j (h.2.2.2 j (Or.inr (Or.inr hj))))
    rw [hm5] at hb hc
    have hr := h.2.2.1
    change degreeIn G (p.vertices 1) q.support ≤ 4 at hr
    omega
  · have hr := q.degree_le_mask (p.vertices 1) 5
      (fun j hj ↦ h5 j (h.2.1 j (Or.inr hj)))
    have hb := q.degree_le_mask (p.vertices 2) 13 (fun j hj ↦ h13 j (h.2.2.1 j hj))
    have hc := q.degree_le_mask (p.vertices 3) 7 (fun j hj ↦ h7 j (h.2.2.2 j hj))
    rw [hm5] at hr
    rw [hm13] at hb
    rw [hm7] at hc
    omega
  · have hr := degreeIn_le_card G (p.vertices 1) q.support
    rw [q.card_support] at hr
    have hb := q.degree_le_mask (p.vertices 2) 7 (fun j hj ↦ h7 j (h.2.2.1 j hj))
    have hc := q.degree_le_mask (p.vertices 3) 1 (fun j hj ↦ by rw [h.2.2.2 j hj]; decide)
    rw [hm7] at hb
    have hm1 : (∑ j : Fin 4, ((1 : ℕ).testBit j.val).toNat) = 1 := by decide +kernel
    rw [hm1] at hc
    omega
  · rw [h.2.contacts_eq p q ![1, 7, 7, 5]]
    decide +kernel
  · rw [h.1.2.contacts_eq p q ![1, 15, 15, 0]]
    decide +kernel

lemma FullClassification.one_leaf_bound (p : Paw G) (q : Quadrilateral G)
    (h : FullClassification p q) (hleaf : degreeIn G p.leaf q.support = 1) :
    contacts G p.support q.support ≤ 9 := by
  obtain ⟨_, _, swap, q', hq', hpattern⟩ := h
  have hp' : degreeIn G (FirstPaw.normalizedPaw p swap).leaf q'.support = 1 := by
    rw [FirstPaw.normalizedPaw_leaf, hq']
    exact hleaf
  have hh := hpattern.one_leaf_bound (FirstPaw.normalizedPaw p swap) q' hp'
  rwa [FirstPaw.normalizedPaw_support, hq'] at hh

end Erdos577.PawBlock
