import ErdosProblems.Erdos118.Reused591.LeafSuffixCounts

namespace Erdos118.Reused591

/-!
# Exact cut balance at consecutive relaxed coordinate endpoints

The retained opposite endpoint continues to witness the first gap.
All later source coordinates are above it, so earlier opposite values
can no longer witness another gap. This is the freshness configuration
of the two partial histories at an aligned critical checkpoint.
-/

namespace Erdos591.Positive.Game.Payoff

theorem cut_card_append_before_crossing (x y : ℕ) (xs before ys : List ℕ)
    (hxy : x < y) (hfresh : ∀ z ∈ xs, y < z) (hold : ∀ z ∈ before, z < y) :
    (cutIndices (x :: xs) (before ++ y :: ys)).card =
      (cutIndices (x :: xs) (y :: ys)).card := by
  classical
  cases xs with
  | nil => rw [cutIndices_singleton_left, cutIndices_singleton_left]
  | cons a xs =>
      have hya : y < a := hfresh a (by simp)
      have hcut : Cut (x :: a :: xs) (y :: ys) 0 :=
        ⟨by simp, y, by simp, hxy, hya⟩
      have hcut' : Cut (x :: a :: xs) (before ++ y :: ys) 0 :=
        ⟨by simp, y, List.mem_append_right before (by simp), hxy, hya⟩
      have hbelow : ∀ z ∈ before, ∀ v ∈ a :: xs, z < v :=
        fun z hz v hv => (hold z hz).trans (hfresh v hv)
      rw [cutIndices_cons_card, cutIndices_cons_card x (a :: xs) (y :: ys),
        if_pos hcut, if_pos hcut', cutIndices_append_right_below (a :: xs) before (y :: ys) hbelow]

theorem consecutive_suffix_cut_balance {pre before xs ys : List ℕ} {x y : ℕ}
    (hx : (pre ++ x :: xs).Pairwise (· < ·))
    (hy : (before ++ y :: ys).Pairwise (· < ·))
    (hd : (pre ++ x :: xs).Disjoint (before ++ y :: ys))
    (hxy : x < y) (hfresh : ∀ z ∈ xs, y < z)
    (hlast : (y :: ys).getLastD 0 < (x :: xs).getLastD 0) :
    (cutIndices (x :: xs) (before ++ y :: ys)).card =
      (cutIndices (y :: ys) (pre ++ x :: xs)).card + 1 := by
  have hxTail := (List.pairwise_append.mp hx).2.1
  have hyTail := (List.pairwise_append.mp hy).2.1
  have hbefore : ∀ z ∈ before, z < y :=
    fun z hz => (List.pairwise_append.mp hy).2.2 z hz y (by simp)
  have hpre : ∀ z ∈ pre, ∀ v ∈ y :: ys, z < v :=
    prefix_below_other_of_head_lt hx hyTail (by simp) (by simp) hxy
  have hdTail : (x :: xs).Disjoint (y :: ys) := by
    intro z hzx hzy
    exact hd (List.mem_append_right pre hzx) (List.mem_append_right before hzy)
  rw [cut_card_append_before_crossing x y xs before ys hxy hfresh hbefore,
    cutIndices_append_right_below (y :: ys) pre (x :: xs) hpre]
  exact cut_count_inside hxTail hyTail hdTail (by simp) (by simp) hxy hlast

#print axioms cut_card_append_before_crossing
#print axioms consecutive_suffix_cut_balance

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
