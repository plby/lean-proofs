import Util.IncidenceGeometry.Basic

open Classical
noncomputable section

lemma PolygonalReplacementRetainedIntervalCutCoverage
    {α C : Type*} [LinearOrder α]
    (source target : α) (cuts : List C) (left right : C → α)
    (intervals : List (α × α))
    (intervals_len : intervals.length = cuts.length + 1)
    (intervals_head : intervals.head?.map Prod.fst = some source)
    (intervals_last : intervals.getLast?.map Prod.snd = some target)
    (interval_gap :
      ∀ (n : ℕ) (hn : n < cuts.length),
        intervals[n]?.map Prod.snd = some (left cuts[n]) ∧
          intervals[n + 1]?.map Prod.fst = some (right cuts[n])) :
    ∀ u, source ≤ u → u ≤ target →
      (∀ k (hk : k < cuts.length), ¬ (left cuts[k] < u ∧ u < right cuts[k])) →
        ∃ (n : ℕ), ∃ a b, intervals[n]? = some (a, b) ∧ a ≤ u ∧ u ≤ b := by
  classical
  intro u hsource_le hu_le_target havoid
  by_cases hex : ∃ k, ∃ hk : k < cuts.length, u ≤ left (cuts[k]'hk)
  · let k := Nat.find hex
    rcases Nat.find_spec hex with ⟨hk, hu_left⟩
    have hk_interval : k < intervals.length := by omega
    obtain ⟨a, b, hsome⟩ : ∃ a b, intervals[k]? = some (a, b) := by
      have hsome' : intervals[k]? = some intervals[k] := by
        rw [List.getElem?_eq_some_iff]
        exact ⟨hk_interval, rfl⟩
      exact ⟨(intervals[k]).1, (intervals[k]).2, by simpa using hsome'⟩
    refine ⟨k, a, b, hsome, ?_, ?_⟩
    · by_cases hk0 : k = 0
      · have hhead_some : intervals.head? = some (a, b) := by
          rw [List.head?_eq_getElem?]
          simpa [hk0] using hsome
        rw [hhead_some] at intervals_head
        have ha : a = source := by simpa using intervals_head
        rw [ha]
        exact hsource_le
      · let j := k - 1
        have hj_lt : j < cuts.length := by
          dsimp [j]
          omega
        have hj_add : j + 1 = k := by
          dsimp [j]
          omega
        have hnot_prev : ¬ u ≤ left cuts[j] := by
          intro hule
          have hj_prop : ∃ hj : j < cuts.length, u ≤ left (cuts[j]'hj) :=
            ⟨hj_lt, hule⟩
          have hk_min := Nat.find_min' hex (m := j) hj_prop
          omega
        have hleft_prev_lt : left cuts[j] < u := lt_of_not_ge hnot_prev
        have hright_prev_le : right cuts[j] ≤ u := by
          exact le_of_not_gt (by
            intro hu_lt_right
            exact havoid j hj_lt ⟨hleft_prev_lt, hu_lt_right⟩)
        have hmap := (interval_gap j hj_lt).2
        have hkSome : intervals[j + 1]? = some (a, b) := by
          simpa [hj_add] using hsome
        rw [hkSome] at hmap
        have ha : a = right cuts[j] := by simpa using hmap
        rw [ha]
        exact hright_prev_le
    · have hmap := (interval_gap k hk).1
      rw [hsome] at hmap
      have hb : b = left cuts[k] := by simpa using hmap
      rw [hb]
      exact hu_left
  · have hno : ∀ k (hk : k < cuts.length), ¬ u ≤ left (cuts[k]'hk) := by
      intro k hk hle
      exact hex ⟨k, hk, hle⟩
    by_cases hcuts0 : cuts.length = 0
    · have hlen1 : intervals.length = 1 := by omega
      obtain ⟨a, b, hsome⟩ : ∃ a b, intervals[0]? = some (a, b) := by
        have h0 : 0 < intervals.length := by omega
        have hsome' : intervals[0]? = some intervals[0] := by
          rw [List.getElem?_eq_some_iff]
          exact ⟨h0, rfl⟩
        exact ⟨(intervals[0]).1, (intervals[0]).2, by simpa using hsome'⟩
      refine ⟨0, a, b, hsome, ?_, ?_⟩
      · have hhead_some : intervals.head? = some (a, b) := by
          rw [List.head?_eq_getElem?]
          simpa [hsome]
        rw [hhead_some] at intervals_head
        have ha : a = source := by simpa using intervals_head
        rw [ha]
        exact hsource_le
      · have hlast_some : intervals.getLast? = some (a, b) := by
          rw [List.getLast?_eq_getElem?]
          have hidx : intervals.length - 1 = 0 := by omega
          rw [hidx]
          simpa [hsome]
        rw [hlast_some] at intervals_last
        have hb : b = target := by simpa using intervals_last
        rw [hb]
        exact hu_le_target
    · let k := cuts.length - 1
      have hk : k < cuts.length := by
        dsimp [k]
        omega
      have hlast_index : k + 1 = cuts.length := by
        dsimp [k]
        omega
      have hleft_lt : left cuts[k] < u := lt_of_not_ge (hno k hk)
      have hright_le : right cuts[k] ≤ u := by
        exact le_of_not_gt (by
          intro hu_lt_right
          exact havoid k hk ⟨hleft_lt, hu_lt_right⟩)
      have hidx_interval : cuts.length < intervals.length := by omega
      obtain ⟨a, b, hsome⟩ : ∃ a b, intervals[cuts.length]? = some (a, b) := by
        have hsome' : intervals[cuts.length]? =
            some intervals[cuts.length] := by
          rw [List.getElem?_eq_some_iff]
          exact ⟨hidx_interval, rfl⟩
        exact ⟨(intervals[cuts.length]).1, (intervals[cuts.length]).2,
          by simpa using hsome'⟩
      refine ⟨cuts.length, a, b, hsome, ?_, ?_⟩
      · have hmap := (interval_gap k hk).2
        have hsome' : intervals[k + 1]? = some (a, b) := by
          simpa [hlast_index] using hsome
        rw [hsome'] at hmap
        have ha : a = right cuts[k] := by simpa using hmap
        rw [ha]
        exact hright_le
      · have hlast_some : intervals.getLast? = some (a, b) := by
          rw [List.getLast?_eq_getElem?]
          have hidx : intervals.length - 1 = cuts.length := by omega
          rw [hidx]
          simpa [hsome]
        rw [hlast_some] at intervals_last
        have hb : b = target := by simpa using intervals_last
        rw [hb]
        exact hu_le_target
