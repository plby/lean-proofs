import ErdosProblems.Erdos577.Counting

/-! Transfer upper contact bounds through an injective labeling and an adjacency implication. -/

namespace Erdos577

open Finset

variable {V W : Type*} [DecidableEq V]
variable (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]

lemma degreeIn_image_le_of_adj (f : W → V) (hf : Function.Injective f)
    (i : W) (t : Finset W)
    (h : ∀ j ∈ t, G.Adj (f i) (f j) → H.Adj i j) :
    degreeIn G (f i) (t.image f) ≤ degreeIn H i t := by
  rw [degreeIn_image G (f i) t f hf]
  have he : degreeIn H i t = ∑ j ∈ t, if H.Adj i j then 1 else 0 := by
    simp only [degreeIn, card_eq_sum_ones, sum_filter]
  rw [he]
  apply sum_le_sum
  intro j hj
  by_cases hij : G.Adj (f i) (f j)
  · rw [if_pos hij, if_pos (h j hj hij)]
  · simp only [if_neg hij, zero_le]

lemma contacts_image_le_of_adj (f : W → V) (hf : Function.Injective f)
    (s t : Finset W)
    (h : ∀ i ∈ s, ∀ j ∈ t, G.Adj (f i) (f j) → H.Adj i j) :
    contacts G (s.image f) (t.image f) ≤ contacts H s t := by
  rw [contacts_image_left G s f hf]
  exact sum_le_sum fun i hi ↦ degreeIn_image_le_of_adj G H f hf i t (h i hi)

end Erdos577
