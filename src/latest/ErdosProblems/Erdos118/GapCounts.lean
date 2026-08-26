import ErdosProblems.Erdos118.CutIndices
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
Finite counts of occupied gaps of ordinary coordinate lists. The recurrence
and suffix proofs adapt the read-only Erdos591 CoordinateCutCounts and
CutSuffixCounts arguments, without importing their active game development.
The bridge to this task's exact selected labels is a separate obligation.
-/

namespace Erdos118.GapCounts

def Gap (xs ys : List ℕ) (k : ℕ) : Prop :=
  k + 1 < xs.length ∧ ∃ y ∈ ys, xs.getD k 0 < y ∧ y < xs.getD (k + 1) 0

noncomputable def gaps (xs ys : List ℕ) : Finset ℕ := by
  classical
  exact (Finset.range xs.length).filter (Gap xs ys)

theorem mem_gaps (xs ys : List ℕ) (k : ℕ) : k ∈ gaps xs ys ↔ Gap xs ys k := by
  classical
  constructor
  · intro hk
    exact (Finset.mem_filter.mp hk).2
  · intro hk
    have hlen := hk.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hk⟩

private theorem gap_cons_succ (x : ℕ) (xs ys : List ℕ) (k : ℕ) :
    Gap (x :: xs) ys (k + 1) ↔ Gap xs ys k := by
  simp only [Gap, List.length_cons, List.getD_cons_succ, Nat.add_lt_add_iff_right]

theorem gaps_cons_card (x : ℕ) (xs ys : List ℕ) :
    (gaps (x :: xs) ys).card =
      (if @decide (Gap (x :: xs) ys 0) (Classical.propDecidable _) then 1 else 0) +
        (gaps xs ys).card := by
  classical
  simp only [gaps, Finset.card_filter, List.length_cons, Finset.sum_range_succ']
  simp only [gap_cons_succ, Nat.add_comm, decide_eq_true_eq]

private theorem gaps_nil_right (xs : List ℕ) : (gaps xs []).card = 0 := by
  simp [gaps, Gap]

theorem gaps_singleton_left (x : ℕ) (ys : List ℕ) : (gaps [x] ys).card = 0 := by
  simp [gaps, Gap]

private theorem gaps_drop_below (x : ℕ) (xs ys : List ℕ)
    (hbelow : ∀ z ∈ xs, x < z) : gaps xs (x :: ys) = gaps xs ys := by
  ext k
  simp only [mem_gaps]
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

private theorem first_gap_of_head_lt {x a y : ℕ} {xs ys : List ℕ}
    (hxy : x < y) (hy : (y :: ys).Pairwise (· < ·)) :
    Gap (x :: a :: xs) (y :: ys) 0 ↔ y < a := by
  constructor
  · rintro ⟨_, z, hz, _, hza⟩
    change z < a at hza
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hza
    · exact ((List.pairwise_cons.mp hy).1 z hz).trans hza
  · intro hya
    exact ⟨by simp, y, by simp, hxy, hya⟩

private theorem head_lt_all {x y : ℕ} {ys : List ℕ}
    (hxy : x < y) (hy : (y :: ys).Pairwise (· < ·)) : ∀ z ∈ y :: ys, x < z := by
  intro z hz
  rcases List.mem_cons.mp hz with rfl | hz
  · exact hxy
  · exact hxy.trans ((List.pairwise_cons.mp hy).1 z hz)

private theorem last_cons_cons (x a : ℕ) (xs : List ℕ) :
    (x :: a :: xs).getLastD 0 = (a :: xs).getLastD 0 := by
  cases xs <;> simp

theorem count_balance (x y : ℕ) (xs ys : List ℕ)
    (hx : (x :: xs).Pairwise (· < ·)) (hy : (y :: ys).Pairwise (· < ·))
    (hd : (x :: xs).Disjoint (y :: ys)) :
    (gaps (x :: xs) (y :: ys)).card +
        (if (x :: xs).getLastD 0 < (y :: ys).getLastD 0 then 1 else 0) =
      (gaps (y :: ys) (x :: xs)).card + (if x < y then 1 else 0) := by
  classical
  have hne : x ≠ y := by
    intro heq
    exact (List.disjoint_cons_left.mp hd).1 (by simp [heq])
  by_cases hxy : x < y
  · have hbelow := head_lt_all hxy hy
    cases xs with
    | nil =>
      have hlast : x < (y :: ys).getLastD 0 := hbelow _
        (by simpa only [List.getLastD_cons] using (List.getLastD_mem_cons (a := y) (l := ys)))
      rw [gaps_singleton_left, gaps_drop_below x (y :: ys) [] hbelow, gaps_nil_right]
      rw [show [x].getLastD 0 = x from rfl, if_pos hlast, if_pos hxy]
    | cons a xs =>
      have hdt : (a :: xs).Disjoint (y :: ys) := (List.disjoint_cons_left.mp hd).2
      have ih := count_balance a y xs ys (List.pairwise_cons.mp hx).2 hy hdt
      have hane : a ≠ y := by
        intro heq
        exact (List.disjoint_cons_left.mp hdt).1 (by simp [heq])
      rw [gaps_cons_card]
      simp only [decide_eq_true_eq, first_gap_of_head_lt hxy hy]
      rw [gaps_drop_below x (y :: ys) (a :: xs) hbelow, last_cons_cons]
      split_ifs at ih ⊢ <;> omega
  · have hyx : y < x := by omega
    have hbelow := head_lt_all hyx hx
    cases ys with
    | nil =>
      have hlast : y < (x :: xs).getLastD 0 := hbelow _
        (by simpa only [List.getLastD_cons] using (List.getLastD_mem_cons (a := x) (l := xs)))
      rw [gaps_drop_below y (x :: xs) [] hbelow, gaps_nil_right, gaps_singleton_left]
      rw [show [y].getLastD 0 = y from rfl, if_neg (not_lt_of_ge hlast.le), if_neg hxy]
    | cons a ys =>
      have hdt : (x :: xs).Disjoint (a :: ys) := (List.disjoint_cons_right.mp hd).2
      have ih := count_balance x a xs ys hx (List.pairwise_cons.mp hy).2 hdt
      rw [gaps_drop_below y (x :: xs) (a :: ys) hbelow,
        gaps_cons_card y (a :: ys) (x :: xs)]
      simp only [decide_eq_true_eq, first_gap_of_head_lt hyx hx]
      rw [last_cons_cons]
      split_ifs at ih ⊢ <;> omega
termination_by xs.length + ys.length

theorem count_inside {xs ys : List ℕ}
    (hx : xs.Pairwise (· < ·)) (hy : ys.Pairwise (· < ·))
    (hd : xs.Disjoint ys) (hxs : xs ≠ []) (hys : ys ≠ [])
    (hfirst : xs.headD 0 < ys.headD 0) (hlast : ys.getLastD 0 < xs.getLastD 0) :
    (gaps xs ys).card = (gaps ys xs).card + 1 := by
  cases xs with
  | nil => exact (hxs rfl).elim
  | cons x xs =>
    cases ys with
    | nil => exact (hys rfl).elim
    | cons y ys =>
      have hxy : x < y := hfirst
      simpa only [if_pos hxy, if_neg (not_lt_of_ge hlast.le), Nat.add_zero] using
        count_balance x y xs ys hx hy hd

theorem gap_drop_iff (xs ys : List ℕ) (k i : ℕ) :
    Gap (xs.drop k) ys i ↔ Gap xs ys (k + i) := by
  simp only [Gap, List.length_drop, List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_assoc]
  constructor
  · rintro ⟨hi, hgap⟩
    exact ⟨by omega, hgap⟩
  · rintro ⟨hi, hgap⟩
    exact ⟨by omega, hgap⟩

private theorem gaps_mono_right (xs : List ℕ) {ys zs : List ℕ} (hsub : ys ⊆ zs) :
    gaps xs ys ⊆ gaps xs zs := by
  intro i hi
  obtain ⟨hi, y, hy, hleft, hright⟩ := (mem_gaps _ _ _).mp hi
  exact (mem_gaps _ _ _).mpr ⟨hi, y, hsub hy, hleft, hright⟩

private theorem gaps_card_mono_right (xs : List ℕ) {ys zs : List ℕ} (hsub : ys ⊆ zs) :
    (gaps xs ys).card ≤ (gaps xs zs).card := Finset.card_le_card (gaps_mono_right xs hsub)

theorem gaps_append_right_below (xs pre ys : List ℕ)
    (hbelow : ∀ x ∈ pre, ∀ y ∈ xs, x < y) : gaps xs (pre ++ ys) = gaps xs ys := by
  induction pre with
  | nil => simp
  | cons x pre ih =>
    rw [List.cons_append, gaps_drop_below x xs (pre ++ ys) (fun y hy ↦ hbelow x (by simp) y hy)]
    exact ih (fun y hy z hz ↦ hbelow y (List.mem_cons_of_mem x hy) z hz)

theorem gaps_drop_card (xs ys : List ℕ) (k : ℕ) :
    (gaps (xs.drop k) ys).card = ((gaps xs ys).filter (k ≤ ·)).card := by
  apply Finset.card_bij (fun i _ ↦ k + i)
  · intro i hi
    exact Finset.mem_filter.mpr
      ⟨(mem_gaps _ _ _).mpr ((gap_drop_iff xs ys k i).mp ((mem_gaps _ _ _).mp hi)),
        Nat.le_add_right _ _⟩
  · intro i hi j hj heq
    omega
  · intro i hi
    obtain ⟨hcut, hki⟩ := Finset.mem_filter.mp hi
    refine ⟨i - k, ?_, by omega⟩
    apply (mem_gaps _ _ _).mpr
    apply (gap_drop_iff xs ys k (i - k)).mpr
    simpa only [Nat.add_sub_of_le hki] using (mem_gaps _ _ _).mp hcut

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
    (gaps ys (pre ++ xs)).card + 1 ≤ (gaps xs (before ++ ys)).card := by
  have hxTail := (List.pairwise_append.mp hx).2.1
  have hyTail := (List.pairwise_append.mp hy).2.1
  have hdTail : xs.Disjoint ys := by
    intro x hxm hym
    exact hd (List.mem_append_right pre hxm) (List.mem_append_right before hym)
  have hbelow := prefix_below_other_of_head_lt hx hyTail hxs hys hhead
  rw [gaps_append_right_below ys pre xs hbelow]
  rw [← count_inside hxTail hyTail hdTail hxs hys hhead hlast]
  exact gaps_card_mono_right xs (fun _ h ↦ List.mem_append_right before h)

theorem suffix_counts_of_head_gt {pre xs before ys : List ℕ}
    (hx : (pre ++ xs).Pairwise (· < ·)) (hy : (before ++ ys).Pairwise (· < ·))
    (hd : (pre ++ xs).Disjoint (before ++ ys)) (hxs : xs ≠ []) (hys : ys ≠ [])
    (hhead : ys.headD 0 < xs.headD 0) (hlast : ys.getLastD 0 < xs.getLastD 0) :
    (gaps xs (before ++ ys)).card ≤ (gaps ys (pre ++ xs)).card := by
  have hxTail := (List.pairwise_append.mp hx).2.1
  have hyTail := (List.pairwise_append.mp hy).2.1
  have hdTail : ys.Disjoint xs := by
    intro x hym hxm
    exact hd (List.mem_append_right pre hxm) (List.mem_append_right before hym)
  have hbelow := prefix_below_other_of_head_lt hy hxTail hys hxs hhead
  rw [gaps_append_right_below xs before ys hbelow]
  have heq : (gaps ys xs).card = (gaps xs ys).card := by
    cases xs with
    | nil => exact (hxs rfl).elim
    | cons x xs =>
      cases ys with
      | nil => exact (hys rfl).elim
      | cons y ys =>
        have hyx : y < x := hhead
        have hc := count_balance y x ys xs hyTail hxTail hdTail
        simp only [if_pos hlast, if_pos hyx] at hc
        omega
  rw [← heq]
  exact gaps_card_mono_right ys (fun _ h ↦ List.mem_append_right pre h)

end Erdos118.GapCounts
