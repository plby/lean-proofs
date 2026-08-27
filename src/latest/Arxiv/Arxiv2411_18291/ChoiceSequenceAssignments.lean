import Arxiv.Arxiv2411_18291.FiniteChoiceSequences
import Mathlib.Data.List.OfFn

/-!
# Indexed assignments represented by finite choice histories

Reading a history in reverse recovers the order in which its choices were
made. This encoding is injective and preserves each stage's prescribed
candidate family.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {X : Type*}

def choiceAssignment (A : ℕ → List X → Finset X) (t : ℕ) (xs : choiceSequences A t) :
    Fin t → X := fun i => xs.val.reverse.get ⟨i.val, by
      rw [List.length_reverse, choiceSequences_length A xs.property]
      exact i.isLt⟩

theorem choiceAssignment_injective (A : ℕ → List X → Finset X) (t : ℕ) :
    Function.Injective (choiceAssignment A t) := by
  intro xs ys hxy
  apply Subtype.ext
  apply List.reverse_injective
  apply List.ext_get
  · rw [List.length_reverse, List.length_reverse,
      choiceSequences_length A xs.property, choiceSequences_length A ys.property]
  · intro i hi _
    have hit : i < t := by
      simpa only [List.length_reverse, choiceSequences_length A xs.property] using hi
    exact congrFun hxy ⟨i, hit⟩

theorem choiceAssignment_mem_history (A : ℕ → List X → Finset X) (t : ℕ)
    (xs : choiceSequences A t) (i : Fin t) : choiceAssignment A t xs i ∈ xs.val := by
  exact List.mem_reverse.mp (List.get_mem _ _)

theorem choiceAssignment_property (A : ℕ → List X → Finset X) (P : ℕ → X → Prop)
    (hAP : ∀ n xs, xs ∈ choiceSequences A n → ∀ x ∈ A n xs, P n x)
    (t : ℕ) (xs : choiceSequences A t) (i : Fin t) : P i (choiceAssignment A t xs i) := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      obtain ⟨ys, hys, x, hx, hxy⟩ := (mem_choiceSequences_succ A t xs.val).mp xs.property
      have hlen := choiceSequences_length A hys
      by_cases hi : i.val < t
      · have he : choiceAssignment A (t + 1) xs i =
          choiceAssignment A t ⟨ys, hys⟩ ⟨i.val, hi⟩ := by
          simp only [choiceAssignment, ← hxy, List.reverse_cons, List.get_eq_getElem]
          rw [List.getElem_append_left (by simpa only [List.length_reverse, hlen] using hi)]
        rw [he]
        exact ih ⟨ys, hys⟩ ⟨i.val, hi⟩
      · have hit : i.val = t := by omega
        have he : choiceAssignment A (t + 1) xs i = x := by
          simp only [choiceAssignment, ← hxy, List.reverse_cons, List.get_eq_getElem]
          rw [List.getElem_append_right (by
            simp only [List.length_reverse, hlen, hit]
            exact le_rfl)]
          simp only [List.length_reverse, hlen, hit, Nat.sub_self, List.getElem_cons_zero]
        rw [he, hit]
        exact hAP t ys hys x hx

theorem choiceAssignment_mem (A : ℕ → List X → Finset X) (D : ℕ → Finset X)
    (hAD : ∀ n xs, A n xs ⊆ D n) (t : ℕ) (xs : choiceSequences A t) (i : Fin t) :
    choiceAssignment A t xs i ∈ D i :=
  choiceAssignment_property A (fun n x => x ∈ D n) (fun n xs _ _ hx => hAD n xs hx) t xs i

end Arxiv2411_18291
