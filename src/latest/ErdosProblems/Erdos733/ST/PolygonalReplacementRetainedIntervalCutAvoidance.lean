import ErdosProblems.Erdos733.ST.Preamble

open Classical
noncomputable section

-- [TABLET NODE: PolygonalReplacementRetainedIntervalCutAvoidance]
lemma PolygonalReplacementRetainedIntervalCutAvoidance
    {α C : Type*} [LinearOrder α]
    (cuts : List C) (left center right : C → α)
    (intervals : List (α × α))
    (intervals_len : intervals.length = cuts.length + 1)
    (interval_gap :
      ∀ (n : ℕ) (hn : n < cuts.length),
        intervals[n]?.map Prod.snd = some (left cuts[n]) ∧
          intervals[n + 1]?.map Prod.fst = some (right cuts[n]) ∧
            left cuts[n] < center cuts[n] ∧
              center cuts[n] < right cuts[n])
    (cut_interval_order :
      ∀ i j (hi : i < cuts.length) (hj : j < cuts.length), i < j →
        right cuts[i] < left cuts[j]) :
    ∀ (n : ℕ) (a b : α), intervals[n]? = some (a, b) →
      ∀ (k : ℕ) (hk : k < cuts.length) (u : α), a ≤ u → u ≤ b →
        ¬ (left cuts[k] < u ∧ u < right cuts[k]) := by
-- BODY
  classical
  intro n a b hnSome k hk u hau hub hinside
  rw [List.getElem?_eq_some_iff] at hnSome
  rcases hnSome with ⟨hn_intervals, hn_eq⟩
  have hn_le_cuts : n ≤ cuts.length := by omega
  by_cases hnk : n ≤ k
  · have hn_lt_cuts : n < cuts.length := lt_of_le_of_lt hnk hk
    have htarget_eq : b = left cuts[n] := by
      have hmap := (interval_gap n hn_lt_cuts).1
      have hsome : intervals[n]? = some intervals[n] := by
        rw [List.getElem?_eq_some_iff]
        exact ⟨hn_intervals, rfl⟩
      rw [hsome] at hmap
      have hb_interval : b = (intervals[n]).2 := by
        have hp := congrArg Prod.snd hn_eq
        simpa using hp.symm
      simpa [hb_interval] using hmap
    have hb_le_left_k : b ≤ left cuts[k] := by
      by_cases heq : n = k
      · subst k
        exact le_of_eq htarget_eq
      · have hlt : n < k := lt_of_le_of_ne hnk heq
        have hnmem : n < cuts.length := lt_trans hlt hk
        have hcut_order_n := (interval_gap n hnmem).2.2
        have hn_right_left_k := cut_interval_order n k hnmem hk hlt
        rw [htarget_eq]
        exact le_of_lt (lt_trans (lt_trans hcut_order_n.1 hcut_order_n.2)
          hn_right_left_k)
    exact not_lt_of_ge (le_trans hub hb_le_left_k) hinside.1
  · have hk_lt_n : k < n := by omega
    have hn_pos : 0 < n := lt_of_le_of_lt (Nat.zero_le k) hk_lt_n
    let m := n - 1
    have hm_lt_cuts : m < cuts.length := by
      dsimp [m]
      omega
    have hm_add : m + 1 = n := by
      dsimp [m]
      omega
    have hsource_eq : a = right cuts[m] := by
      have hmap := (interval_gap m hm_lt_cuts).2.1
      have hnSome : intervals[n]? = some (a, b) := by
        rw [List.getElem?_eq_some_iff]
        exact ⟨hn_intervals, hn_eq⟩
      have hmSome : intervals[m + 1]? = some (a, b) := by
        simpa [hm_add] using hnSome
      rw [hmSome] at hmap
      simpa using hmap
    have hright_k_le_a : right cuts[k] ≤ a := by
      by_cases heq : k = m
      · subst k
        exact le_of_eq hsource_eq.symm
      · have hkm : k < m := by
          have hkle : k ≤ m := by
            dsimp [m]
            omega
          exact lt_of_le_of_ne hkle heq
        have horder := cut_interval_order k m hk hm_lt_cuts hkm
        have hcut_order_m := (interval_gap m hm_lt_cuts).2.2
        rw [hsource_eq]
        exact le_of_lt (lt_trans horder
          (lt_trans hcut_order_m.1 hcut_order_m.2))
    exact not_lt_of_ge (le_trans hright_k_le_a hau) hinside.2
