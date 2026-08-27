import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

/-!
# Counting finite sequences with history-dependent choices

Each stage prepends one choice to the preceding history. Different histories
give disjoint branches. A uniform lower bound on every branch therefore
multiplies over the stages, without an independence assumption.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {X : Type*}

open Classical in
def choiceSequences (A : ℕ → List X → Finset X) : ℕ → Finset (List X)
  | 0 => {[]}
  | n + 1 => (choiceSequences A n).biUnion fun xs => (A n xs).image (fun x => x :: xs)

theorem mem_choiceSequences_succ (A : ℕ → List X → Finset X) (n : ℕ) (xs : List X) :
    xs ∈ choiceSequences A (n + 1) ↔
      ∃ ys ∈ choiceSequences A n, ∃ x ∈ A n ys, x :: ys = xs := by
  classical
  simp only [choiceSequences, mem_biUnion, mem_image]

theorem choiceSequences_length (A : ℕ → List X → Finset X) {n : ℕ} {xs : List X}
    (hxs : xs ∈ choiceSequences A n) : xs.length = n := by
  induction n generalizing xs with
  | zero =>
      have heq : xs = [] := mem_singleton.mp hxs
      simp only [heq, List.length_nil]
  | succ n ih =>
      obtain ⟨ys, hys, x, _, rfl⟩ := (mem_choiceSequences_succ A n xs).mp hxs
      simp only [List.length_cons, ih hys]

theorem choiceSequences_card_succ (A : ℕ → List X → Finset X) (n : ℕ) :
    (choiceSequences A (n + 1)).card = ∑ xs ∈ choiceSequences A n, (A n xs).card := by
  classical
  have hd : (choiceSequences A n : Set (List X)).Pairwise
      (fun xs ys => Disjoint ((A n xs).image (fun x => x :: xs))
        ((A n ys).image (fun y => y :: ys))) := by
    intro xs _ ys _ hxy
    apply disjoint_left.mpr
    intro zs hz1 hz2
    obtain ⟨x, _, hx⟩ := mem_image.mp hz1
    obtain ⟨y, _, hy⟩ := mem_image.mp hz2
    exact hxy (List.cons.inj (hx.trans hy.symm)).2
  rw [choiceSequences, card_biUnion hd]
  apply sum_congr rfl
  intro xs _
  exact card_image_of_injective _ (fun _ _ h => (List.cons.inj h).1)

theorem choiceSequences_card_lower (A : ℕ → List X → Finset X) (t : ℕ) {L : ℝ}
    (hL : 0 ≤ L)
    (hbranch : ∀ n < t, ∀ xs ∈ choiceSequences A n, L ≤ (A n xs).card) :
    L ^ t ≤ (choiceSequences A t).card := by
  induction t with
  | zero => simp only [choiceSequences, card_singleton, Nat.cast_one, pow_zero, le_refl]
  | succ t ih =>
      have ht := ih (fun n hn xs hxs => hbranch n (by omega) xs hxs)
      rw [pow_succ, choiceSequences_card_succ, Nat.cast_sum]
      calc
        _ ≤ (choiceSequences A t).card * L := mul_le_mul_of_nonneg_right ht hL
        _ = ∑ _xs ∈ choiceSequences A t, L := by rw [sum_const, nsmul_eq_mul]
        _ ≤ _ := sum_le_sum (fun xs hxs => hbranch t (Nat.lt_succ_self t) xs hxs)

end Arxiv2411_18291
