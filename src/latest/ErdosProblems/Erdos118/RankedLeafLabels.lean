import ErdosProblems.Erdos118.SharedFirstSecond
import ErdosProblems.Erdos118.LabelRanks

/-! Full source and target labels with the first target leaf at a
prescribed source rank, before the common marker is sampled. -/

namespace Erdos118.RankedLeafLabels

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open Erdos590.Larson

structure Labels (H : Set ℕ) (b k l s : ℕ) where
  lower : List ℕ
  upper : List ℕ
  lowerCard : lower.length = k + 1
  upperCard : upper.length = l + 1
  lowerIncreasing : lower.Pairwise (· < ·)
  upperIncreasing : upper.Pairwise (· < ·)
  selected : upper.headD 0 ∈ lower
  rank : LabelRanks.rank lower (upper.headD 0) = s
  lastCase : s = k + 1 → lower.getLastD 0 = upper.headD 0
  nonlastCase : s < k + 1 → upper.headD 0 < lower.getLastD 0 ∧
    lower.getLastD 0 ∈ upper ∧ ∀ x ∈ upper, upper.headD 0 < x → lower.getLastD 0 ≤ x
  lowerFresh : ∀ x ∈ lower, x ∈ H ∧ b < x
  upperFresh : ∀ x ∈ upper, x ∈ H ∧ b < x

theorem labels {H : Set ℕ} (hH : H.Infinite) (b k l s : ℕ)
    (hs : 0 < s) (hsk : s ≤ k + 1) (hl : 0 < l) : Nonempty (Labels H b k l s) := by
  classical
  obtain ⟨A, hAlen, hAi, hA⟩ := InteriorWords.fresh_list hH b (s - 1)
  obtain ⟨C, D, hCk, hDl, hCi, hDi, hfirst, halign, hC, hD⟩ :=
    SharedFirstSecond.labels hH (max b A.sum) (k + 1 - s) l (fun _ ↦ hl)
  have hCne : C ≠ [] := by intro he; simp [he] at hCk
  have hhead := first_mem hCne
  have hAC : ∀ x ∈ A, ∀ y ∈ C, x < y := fun x hx y hy ↦
    (nat_le_sum_of_mem hx).trans_lt ((le_max_right _ _).trans_lt (hC y hy).2)
  have hmin : ∀ x ∈ C, C.headD 0 ≤ x := by
    intro x hx
    have h := (hCi.imp Nat.le_of_lt).rel_head hx
    cases he : C with
    | nil => simp [he] at hx
    | cons c rest => simpa only [he, List.head_cons, List.headD_cons] using h
  have hlast : (A ++ C).getLastD 0 = C.getLastD 0 := by
    simp only [List.getLastD_eq_getLast?, List.getLast?_append_of_ne_nil A hCne]
  have hfilter : (A ++ C).toFinset.filter (· ≤ C.headD 0) = insert (C.headD 0) A.toFinset := by
    ext x
    simp only [List.toFinset_append, Finset.mem_filter, Finset.mem_union, List.mem_toFinset,
      Finset.mem_insert]
    constructor
    · rintro ⟨hx | hx, hxp⟩
      · exact Or.inr hx
      · exact Or.inl (le_antisymm hxp (hmin x hx))
    · rintro (rfl | hx)
      · exact ⟨Or.inr hhead, le_rfl⟩
      · exact ⟨Or.inl hx, (hAC x hx _ hhead).le⟩
  have hnot : C.headD 0 ∉ A.toFinset := by
    intro hm
    exact (Nat.lt_irrefl _) (hAC _ (List.mem_toFinset.mp hm) _ hhead)
  refine ⟨{
    lower := A ++ C, upper := D
    lowerCard := by simp only [List.length_append, hAlen, hCk]; omega
    upperCard := hDl, lowerIncreasing := List.pairwise_append.mpr ⟨hAi, hCi, hAC⟩
    upperIncreasing := hDi, selected := hfirst ▸ List.mem_append_right A hhead
    rank := by
      rw [LabelRanks.rank, ← hfirst, hfilter, Finset.card_insert_of_notMem hnot,
        List.toFinset_card_of_nodup hAi.nodup, hAlen]
      omega
    lastCase := ?_, nonlastCase := ?_
    lowerFresh := ?_, upperFresh := fun x hx ↦
      ⟨(hD x hx).1, (le_max_left _ _).trans_lt (hD x hx).2⟩ }⟩
  · intro he
    have hlen : C.length = 1 := by rw [he, Nat.sub_self] at hCk; exact hCk
    rw [hlast, ← hfirst]
    cases hc : C with
    | nil => simp [hc] at hlen
    | cons c rest =>
      have hr : rest = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [hc, List.length_cons] at hlen
        omega
      rw [hr]
      rfl
  · intro hlt
    rcases halign with hsingle | hnonlast
    · omega
    · rw [hlast, ← hfirst]
      exact hnonlast
  · intro x hx
    exact (List.mem_append.mp hx).elim (hA x)
      (fun hx ↦ ⟨(hC x hx).1, (le_max_left _ _).trans_lt (hC x hx).2⟩)

theorem body_setup (S : Stem) (hroom : S.done.length + 1 < S.root)
    {H : Set ℕ} (hH : H.Infinite) (b k l s : ℕ)
    (hs : 0 < s) (hsk : s ≤ k + 1) (hl : 0 < l) :
    ∃ A : BodyResponses.Setup S k, ∃ L : Labels H b k l s,
      A.position.label = L.lower ∧ (∀ x ∈ L.upper, x < A.position.size) ∧
      (∀ x ∈ BodyResponses.newWord A.position, x ∈ H ∧ b < x) := by
  let bound := max b S.decorated.sum
  obtain ⟨L⟩ := labels hH bound k l s hs hsk hl
  obtain ⟨n, hnH, hn⟩ := hH.exists_gt (max bound (max L.lower.sum L.upper.sum))
  have hbn : bound < n := (le_max_left _ _).trans_lt hn
  have hCn : ∀ x ∈ L.lower, x < n := fun x hx ↦ (nat_le_sum_of_mem hx).trans_lt
    (((le_max_left L.lower.sum L.upper.sum).trans (le_max_right bound _)).trans_lt hn)
  have hDn : ∀ x ∈ L.upper, x < n := fun x hx ↦ (nat_le_sum_of_mem hx).trans_lt
    (((le_max_right L.lower.sum L.upper.sum).trans (le_max_right bound _)).trans_lt hn)
  have hne : L.lower ≠ [] := by intro he; have hc := L.lowerCard; simp [he] at hc
  have hhead := first_mem hne
  have hpos : 0 < L.lower.headD 0 := (Nat.zero_le bound).trans_lt (L.lowerFresh _ hhead).2
  obtain ⟨u, hulen, hui, hu⟩ := InteriorWords.fresh_list hH n (L.lower.headD 0)
  have htail : (n :: u).Pairwise (· < ·) :=
    List.pairwise_cons.mpr ⟨fun x hx ↦ (hu x hx).2, hui⟩
  have hnew : (L.lower ++ n :: u).Pairwise (· < ·) := by
    refine List.pairwise_append.mpr ⟨L.lowerIncreasing, htail, ?_⟩
    intro x hx y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hCn x hx
    · exact (hCn x hx).trans (hu y hy).2
  have hfresh : ∀ x ∈ L.lower ++ n :: u, x ∈ H ∧ bound < x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact L.lowerFresh x hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨hnH, hbn⟩
      · exact ⟨(hu x hx).1, hbn.trans (hu x hx).2⟩
  let P : Position :=
    { stem := S, size := n, label := L.lower, entries := u, room := hroom
      started := hulen ▸ hpos, unfinished := hulen ▸ hCn _ hhead
      increasing := List.pairwise_append.mpr ⟨S.increasing, hnew,
        fun x hx y hy ↦ ((nat_le_sum_of_mem hx).trans (le_max_right _ _)).trans_lt
          (hfresh y hy).2⟩ }
  let A : BodyResponses.Setup S k := ⟨P, rfl, L.lowerCard, hulen⟩
  let L' : Labels H b k l s :=
    { lower := L.lower, upper := L.upper, lowerCard := L.lowerCard, upperCard := L.upperCard
      lowerIncreasing := L.lowerIncreasing, upperIncreasing := L.upperIncreasing
      selected := L.selected, rank := L.rank, lastCase := L.lastCase, nonlastCase := L.nonlastCase
      lowerFresh := fun x hx ↦ ⟨(L.lowerFresh x hx).1,
        (le_max_left _ _).trans_lt (L.lowerFresh x hx).2⟩
      upperFresh := fun x hx ↦ ⟨(L.upperFresh x hx).1,
        (le_max_left _ _).trans_lt (L.upperFresh x hx).2⟩ }
  exact ⟨A, L', rfl, hDn,
    fun x hx ↦ ⟨(hfresh x hx).1, (le_max_left _ _).trans_lt (hfresh x hx).2⟩⟩

end Erdos118.RankedLeafLabels
