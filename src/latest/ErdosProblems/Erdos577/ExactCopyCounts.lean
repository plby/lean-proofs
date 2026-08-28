import ErdosProblems.Erdos577.UpperCounts

/-! Exact adjacency on an injectively labeled finite set preserves all induced counts. -/

namespace Erdos577

open Finset

variable {V W : Type*} [DecidableEq V]
variable (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]

lemma degreeIn_image_eq_of_adj (f : W → V) (hf : Function.Injective f)
    (i : W) (t : Finset W) (h : ∀ j ∈ t, G.Adj (f i) (f j) ↔ H.Adj i j) :
    degreeIn G (f i) (t.image f) = degreeIn H i t := by
  rw [degreeIn_image G (f i) t f hf]
  have he : degreeIn H i t = ∑ j ∈ t, if H.Adj i j then 1 else 0 := by
    simp only [degreeIn, card_eq_sum_ones, sum_filter]
  rw [he]
  apply sum_congr rfl
  intro j hj
  simp only [h j hj]

lemma contacts_image_eq_of_adj (f : W → V) (hf : Function.Injective f)
    (s t : Finset W) (h : ∀ i ∈ s, ∀ j ∈ t, G.Adj (f i) (f j) ↔ H.Adj i j) :
    contacts G (s.image f) (t.image f) = contacts H s t := by
  rw [contacts_image_left G s f hf]
  exact sum_congr rfl fun i hi ↦ degreeIn_image_eq_of_adj G H f hf i t (h i hi)

lemma edgeCount_image_eq_of_adj (f : W → V) (hf : Function.Injective f)
    (s : Finset W) (h : ∀ i ∈ s, ∀ j ∈ s, G.Adj (f i) (f j) ↔ H.Adj i j) :
    edgeCount G (s.image f) = edgeCount H s := by
  have he := contacts_image_eq_of_adj G H f hf s s h
  rw [contacts_self_eq_twice_edgeCount, contacts_self_eq_twice_edgeCount] at he
  omega

end Erdos577
