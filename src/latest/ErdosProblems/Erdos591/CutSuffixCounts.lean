import ErdosProblems.Erdos591.CoordinateCutCounts

/-!
# Exact suffix cuts and monotonicity under deleting opposite coordinates

Shifting suffix positions identifies their cuts with the full cut set
above the dropped prefix. Deleting opposite entries can only remove
cuts, and entries below the whole side cannot witness any cut.
-/

namespace Erdos591.Positive.Game.Payoff

theorem cut_drop_iff (xs ys : List ℕ) (k i : ℕ) :
    Cut (xs.drop k) ys i ↔ Cut xs ys (k + i) := by
  simp only [Cut, List.length_drop, List.getD_eq_getElem?_getD, List.getElem?_drop,
    Nat.add_assoc]
  constructor
  · rintro ⟨hi, hgap⟩
    exact ⟨by omega, hgap⟩
  · rintro ⟨hi, hgap⟩
    exact ⟨by omega, hgap⟩

theorem cutIndices_mono_right (xs : List ℕ) {ys zs : List ℕ} (hsub : ys ⊆ zs) :
    cutIndices xs ys ⊆ cutIndices xs zs := by
  intro i hi
  obtain ⟨hi, y, hy, hleft, hright⟩ := (mem_cutIndices _ _ _).mp hi
  exact (mem_cutIndices _ _ _).mpr ⟨hi, y, hsub hy, hleft, hright⟩

theorem cutIndices_card_mono_right (xs : List ℕ) {ys zs : List ℕ} (hsub : ys ⊆ zs) :
    (cutIndices xs ys).card ≤ (cutIndices xs zs).card :=
  Finset.card_le_card (cutIndices_mono_right xs hsub)

theorem cutIndices_append_right_below (xs pre ys : List ℕ)
    (hbelow : ∀ x ∈ pre, ∀ y ∈ xs, x < y) :
    cutIndices xs (pre ++ ys) = cutIndices xs ys := by
  induction pre with
  | nil => simp
  | cons x pre ih =>
      rw [List.cons_append, cutIndices_drop_below x xs (pre ++ ys)
        (fun y hy => hbelow x (by simp) y hy)]
      exact ih (fun y hy z hz => hbelow y (List.mem_cons_of_mem x hy) z hz)

theorem cutIndices_drop_card (xs ys : List ℕ) (k : ℕ) :
    (cutIndices (xs.drop k) ys).card = ((cutIndices xs ys).filter (k ≤ ·)).card := by
  apply Finset.card_bij (fun i _ => k + i)
  · intro i hi
    exact Finset.mem_filter.mpr
      ⟨(mem_cutIndices _ _ _).mpr ((cut_drop_iff xs ys k i).mp
        ((mem_cutIndices _ _ _).mp hi)), Nat.le_add_right _ _⟩
  · intro i hi j hj heq
    omega
  · intro i hi
    obtain ⟨hcut, hki⟩ := Finset.mem_filter.mp hi
    refine ⟨i - k, ?_, by omega⟩
    apply (mem_cutIndices _ _ _).mpr
    apply (cut_drop_iff xs ys k (i - k)).mpr
    simpa only [Nat.add_sub_of_le hki] using (mem_cutIndices _ _ _).mp hcut

theorem prefix_below_other_of_head_lt {pre xs ys : List ℕ}
    (hx : (pre ++ xs).Pairwise (· < ·)) (hy : ys.Pairwise (· < ·))
    (hxs : xs ≠ []) (hys : ys ≠ []) (hhead : xs.headD 0 < ys.headD 0) :
    ∀ x ∈ pre, ∀ y ∈ ys, x < y := by
  cases xs with
  | nil => exact (hxs rfl).elim
  | cons a xs =>
      cases ys with
      | nil => exact (hys rfl).elim
      | cons b ys =>
          have hab : a < b := hhead
          intro x hxmem y hymem
          have hxa : x < a := (List.pairwise_append.mp hx).2.2 x hxmem a (by simp)
          exact hxa.trans (head_lt_all hab hy y hymem)

theorem suffix_counts_of_head_lt {pre xs before ys : List ℕ}
    (hx : (pre ++ xs).Pairwise (· < ·)) (hy : (before ++ ys).Pairwise (· < ·))
    (hd : (pre ++ xs).Disjoint (before ++ ys)) (hxs : xs ≠ []) (hys : ys ≠ [])
    (hhead : xs.headD 0 < ys.headD 0) (hlast : ys.getLastD 0 < xs.getLastD 0) :
    (cutIndices ys (pre ++ xs)).card + 1 ≤ (cutIndices xs (before ++ ys)).card := by
  have hxTail := (List.pairwise_append.mp hx).2.1
  have hyTail := (List.pairwise_append.mp hy).2.1
  have hdTail : xs.Disjoint ys := by
    intro x hxm hym
    exact hd (List.mem_append_right pre hxm) (List.mem_append_right before hym)
  have hbelow := prefix_below_other_of_head_lt hx hyTail hxs hys hhead
  rw [cutIndices_append_right_below ys pre xs hbelow]
  rw [← cut_count_inside hxTail hyTail hdTail hxs hys hhead hlast]
  exact cutIndices_card_mono_right xs (fun _ h => List.mem_append_right before h)

theorem suffix_counts_of_head_gt {pre xs before ys : List ℕ}
    (hx : (pre ++ xs).Pairwise (· < ·)) (hy : (before ++ ys).Pairwise (· < ·))
    (hd : (pre ++ xs).Disjoint (before ++ ys)) (hxs : xs ≠ []) (hys : ys ≠ [])
    (hhead : ys.headD 0 < xs.headD 0) (hlast : ys.getLastD 0 < xs.getLastD 0) :
    (cutIndices xs (before ++ ys)).card ≤ (cutIndices ys (pre ++ xs)).card := by
  have hxTail := (List.pairwise_append.mp hx).2.1
  have hyTail := (List.pairwise_append.mp hy).2.1
  have hdTail : ys.Disjoint xs := by
    intro x hym hxm
    exact hd (List.mem_append_right pre hxm) (List.mem_append_right before hym)
  have hbelow := prefix_below_other_of_head_lt hy hxTail hys hxs hhead
  rw [cutIndices_append_right_below xs before ys hbelow]
  have heq : (cutIndices ys xs).card = (cutIndices xs ys).card := by
    cases xs with
    | nil => exact (hxs rfl).elim
    | cons x xs =>
        cases ys with
        | nil => exact (hys rfl).elim
        | cons y ys =>
            have hyx : y < x := hhead
            have hc := cut_count_balance y x ys xs hyTail hxTail hdTail
            simp only [if_pos hlast, if_pos hyx] at hc
            omega
  rw [← heq]
  exact cutIndices_card_mono_right ys (fun _ h => List.mem_append_right pre h)

#print axioms cut_drop_iff
#print axioms cutIndices_append_right_below
#print axioms cutIndices_drop_card
#print axioms suffix_counts_of_head_lt
#print axioms suffix_counts_of_head_gt

end Erdos591.Positive.Game.Payoff
