import ErdosProblems.Erdos118.Reused591.SelectedLeafCounts
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace Erdos118.Reused591

/-!
# Counting occupied gaps of literal coordinate lists

Removing the least coordinate leaves all opposite gaps unchanged.
The exact finite cut set therefore satisfies a one-step recurrence.
These lemmas use the original `Payoff.Cut`, not a replacement notion.
-/

namespace Erdos591.Positive.Game.Payoff

theorem cut_cons_succ (x : ℕ) (xs ys : List ℕ) (k : ℕ) :
    Cut (x :: xs) ys (k + 1) ↔ Cut xs ys k := by
  simp only [Cut, List.length_cons, List.getD_cons_succ, Nat.add_lt_add_iff_right]

open Classical in
theorem cutIndices_cons_card (x : ℕ) (xs ys : List ℕ) :
    (cutIndices (x :: xs) ys).card =
      (if Cut (x :: xs) ys 0 then 1 else 0) + (cutIndices xs ys).card := by
  classical
  simp only [cutIndices, Finset.card_filter, List.length_cons, Finset.sum_range_succ']
  simp only [cut_cons_succ, Nat.add_comm]

theorem cutIndices_nil_left (ys : List ℕ) : (cutIndices [] ys).card = 0 := by
  simp [cutIndices]

theorem cutIndices_nil_right (xs : List ℕ) : (cutIndices xs []).card = 0 := by
  simp [cutIndices, Cut]

theorem cutIndices_singleton_left (x : ℕ) (ys : List ℕ) :
    (cutIndices [x] ys).card = 0 := by
  simp [cutIndices, Cut]

theorem cutIndices_drop_below (x : ℕ) (xs ys : List ℕ)
    (hbelow : ∀ z ∈ xs, x < z) : cutIndices xs (x :: ys) = cutIndices xs ys := by
  ext k
  simp only [mem_cutIndices]
  constructor
  · rintro ⟨hk, z, hz, hleft, hright⟩
    rcases List.mem_cons.mp hz with rfl | hz
    · have hm : xs.getD k 0 ∈ xs := by
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact List.getElem_mem _
      exact (not_lt_of_ge (hbelow _ hm).le hleft).elim
    · exact ⟨hk, z, hz, hleft, hright⟩
  · rintro ⟨hk, z, hz, hleft, hright⟩
    exact ⟨hk, z, List.mem_cons_of_mem x hz, hleft, hright⟩

theorem first_cut_of_head_lt {x a y : ℕ} {xs ys : List ℕ}
    (hxy : x < y) (hy : (y :: ys).Pairwise (· < ·)) :
    Cut (x :: a :: xs) (y :: ys) 0 ↔ y < a := by
  constructor
  · rintro ⟨_, z, hz, _hxz, hza⟩
    change z < a at hza
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hza
    · exact ((List.pairwise_cons.mp hy).1 z hz).trans hza
  · intro hya
    exact ⟨by simp, y, by simp, hxy, hya⟩

theorem head_lt_all {x y : ℕ} {ys : List ℕ}
    (hxy : x < y) (hy : (y :: ys).Pairwise (· < ·)) : ∀ z ∈ y :: ys, x < z := by
  intro z hz
  rcases List.mem_cons.mp hz with rfl | hz
  · exact hxy
  · exact hxy.trans ((List.pairwise_cons.mp hy).1 z hz)

theorem last_cons_cons (x a : ℕ) (xs : List ℕ) :
    (x :: a :: xs).getLastD 0 = (a :: xs).getLastD 0 := by
  cases xs <;> simp

theorem cut_count_balance (x y : ℕ) (xs ys : List ℕ)
    (hx : (x :: xs).Pairwise (· < ·)) (hy : (y :: ys).Pairwise (· < ·))
    (hd : (x :: xs).Disjoint (y :: ys)) :
    (cutIndices (x :: xs) (y :: ys)).card +
        (if (x :: xs).getLastD 0 < (y :: ys).getLastD 0 then 1 else 0) =
      (cutIndices (y :: ys) (x :: xs)).card + (if x < y then 1 else 0) := by
  classical
  have hne : x ≠ y := by
    intro heq
    exact (List.disjoint_cons_left.mp hd).1 (by simp [heq])
  by_cases hxy : x < y
  · have hbelow := head_lt_all hxy hy
    cases xs with
    | nil =>
        have hlast : x < (y :: ys).getLastD 0 := hbelow _
          (by simpa only [List.getLastD_cons] using
            (List.getLastD_mem_cons (a := y) (l := ys)))
        rw [cutIndices_singleton_left, cutIndices_drop_below x (y :: ys) [] hbelow,
          cutIndices_nil_right]
        rw [show [x].getLastD 0 = x from rfl, if_pos hlast, if_pos hxy]
    | cons a xs =>
        have hdt : (a :: xs).Disjoint (y :: ys) := (List.disjoint_cons_left.mp hd).2
        have ih := cut_count_balance a y xs ys (List.pairwise_cons.mp hx).2 hy hdt
        have hane : a ≠ y := by
          intro heq
          exact (List.disjoint_cons_left.mp hdt).1 (by simp [heq])
        rw [cutIndices_cons_card, first_cut_of_head_lt hxy hy,
          cutIndices_drop_below x (y :: ys) (a :: xs) hbelow, last_cons_cons]
        split_ifs at ih ⊢ <;> omega
  · have hyx : y < x := by omega
    have hbelow := head_lt_all hyx hx
    cases ys with
    | nil =>
        have hlast : y < (x :: xs).getLastD 0 := hbelow _
          (by simpa only [List.getLastD_cons] using
            (List.getLastD_mem_cons (a := x) (l := xs)))
        rw [cutIndices_drop_below y (x :: xs) [] hbelow,
          cutIndices_nil_right, cutIndices_singleton_left]
        rw [show [y].getLastD 0 = y from rfl, if_neg (not_lt_of_ge hlast.le), if_neg hxy]
    | cons a ys =>
        have hdt : (x :: xs).Disjoint (a :: ys) := (List.disjoint_cons_right.mp hd).2
        have ih := cut_count_balance x a xs ys hx (List.pairwise_cons.mp hy).2 hdt
        rw [cutIndices_drop_below y (x :: xs) (a :: ys) hbelow,
          cutIndices_cons_card y (a :: ys) (x :: xs), first_cut_of_head_lt hyx hx,
          last_cons_cons]
        split_ifs at ih ⊢ <;> omega
termination_by xs.length + ys.length

theorem cut_count_inside {xs ys : List ℕ}
    (hx : xs.Pairwise (· < ·)) (hy : ys.Pairwise (· < ·))
    (hd : xs.Disjoint ys) (hxs : xs ≠ []) (hys : ys ≠ [])
    (hfirst : xs.headD 0 < ys.headD 0) (hlast : ys.getLastD 0 < xs.getLastD 0) :
    (cutIndices xs ys).card = (cutIndices ys xs).card + 1 := by
  cases xs with
  | nil => exact (hxs rfl).elim
  | cons x xs =>
      cases ys with
      | nil => exact (hys rfl).elim
      | cons y ys =>
          have hxy : x < y := hfirst
          simpa only [if_pos hxy, if_neg (not_lt_of_ge hlast.le), Nat.add_zero] using
            cut_count_balance x y xs ys hx hy hd

#print axioms cutIndices_cons_card
#print axioms cutIndices_drop_below
#print axioms cut_count_balance
#print axioms cut_count_inside

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
