import Util.IncidenceGeometry.Basic

open Classical
noncomputable section

open Set

lemma RealSegmentChainUnion
    (L : List (ℝ × ℝ)) (hpos : 0 < L.length)
    (hlink : ∀ n (hn : n + 1 < L.length),
      (L[n]).2 = (L[n + 1]).1)
    (hne : ∀ n (hn : n < L.length), (L[n]).1 ≠ (L[n]).2)
    (hinter : ∀ n (hn : n + 1 < L.length),
      segment ℝ (L[n]).1 (L[n]).2 ∩
          segment ℝ (L[n + 1]).1 (L[n + 1]).2 =
        ({(L[n]).2} : Set ℝ)) :
    (⋃ k : Fin L.length, segment ℝ (L[k.1]).1 (L[k.1]).2) =
      segment ℝ (L[0]).1
        (L[L.length - 1]'(Nat.sub_one_lt_of_lt hpos)).2 := by
  have real_segment_union_inc :
      ∀ {a b c : ℝ}, a ≤ b → b ≤ c →
        segment ℝ a b ∪ segment ℝ b c = segment ℝ a c := by
    intro a b c hab hbc
    ext x
    rw [segment_eq_Icc hab, segment_eq_Icc hbc, segment_eq_Icc (hab.trans hbc)]
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact ⟨hx.1, hx.2.trans hbc⟩
      · exact ⟨hab.trans hx.1, hx.2⟩
    · intro hx
      by_cases hxb : x ≤ b
      · exact Or.inl ⟨hx.1, hxb⟩
      · exact Or.inr ⟨le_of_not_ge hxb, hx.2⟩
  have real_segment_union_dec :
      ∀ {a b c : ℝ}, b ≤ a → c ≤ b →
        segment ℝ a b ∪ segment ℝ b c = segment ℝ a c := by
    intro a b c hba hcb
    ext x
    rw [segment_symm ℝ a b, segment_symm ℝ b c, segment_symm ℝ a c]
    rw [segment_eq_Icc hba, segment_eq_Icc hcb, segment_eq_Icc (hcb.trans hba)]
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact ⟨hcb.trans hx.1, hx.2⟩
      · exact ⟨hx.1, hx.2.trans hba⟩
    · intro hx
      by_cases hxb : x ≤ b
      · exact Or.inr ⟨hx.1, hxb⟩
      · exact Or.inl ⟨le_of_not_ge hxb, hx.2⟩
  have real_next_inc :
      ∀ {a b c : ℝ}, a < b → b ≠ c →
        segment ℝ a b ∩ segment ℝ b c = ({b} : Set ℝ) → b < c := by
    intro a b c hab hbc_ne hinter
    by_contra hnot
    have hcb : c ≤ b := le_of_not_gt hnot
    have hcb_lt : c < b := lt_of_le_of_ne hcb (Ne.symm hbc_ne)
    have hmax : max a c < b := max_lt hab hcb_lt
    let x : ℝ := (max a c + b) / 2
    have hax : a ≤ x := by
      dsimp [x]
      nlinarith [le_max_left a c]
    have hxb : x ≤ b := by
      dsimp [x]
      nlinarith [hmax]
    have hcx : c ≤ x := by
      dsimp [x]
      nlinarith [le_max_right a c]
    have hx_ne : x ≠ b := by
      dsimp [x]
      nlinarith [hmax]
    have hxmem : x ∈ segment ℝ a b ∩ segment ℝ b c := by
      rw [segment_eq_Icc hab.le, segment_symm ℝ b c, segment_eq_Icc hcb]
      exact ⟨⟨hax, hxb⟩, ⟨hcx, hxb⟩⟩
    rw [hinter] at hxmem
    exact hx_ne (by simpa using hxmem)
  have real_next_dec :
      ∀ {a b c : ℝ}, b < a → b ≠ c →
        segment ℝ a b ∩ segment ℝ b c = ({b} : Set ℝ) → c < b := by
    intro a b c hba hbc_ne hinter
    by_contra hnot
    have hbc : b ≤ c := le_of_not_gt hnot
    have hbc_lt : b < c := lt_of_le_of_ne hbc hbc_ne
    have hmin : b < min a c := lt_min hba hbc_lt
    let x : ℝ := (b + min a c) / 2
    have hbx : b ≤ x := by
      dsimp [x]
      nlinarith [hmin]
    have hxa : x ≤ a := by
      dsimp [x]
      nlinarith [min_le_left a c]
    have hxc : x ≤ c := by
      dsimp [x]
      nlinarith [min_le_right a c]
    have hx_ne : x ≠ b := by
      dsimp [x]
      nlinarith [hmin]
    have hxmem : x ∈ segment ℝ a b ∩ segment ℝ b c := by
      rw [segment_symm ℝ a b, segment_eq_Icc hba.le, segment_eq_Icc hbc]
      exact ⟨⟨hbx, hxa⟩, ⟨hbx, hxc⟩⟩
    rw [hinter] at hxmem
    exact hx_ne (by simpa using hxmem)
  have chain_inc :
      (L[0]).1 < (L[0]).2 →
        ∀ n (hn : n < L.length),
          (L[n]).1 < (L[n]).2 ∧ (L[0]).1 < (L[n]).2 ∧
            (⋃ k : Fin (n + 1), segment ℝ (L[k.1]).1 (L[k.1]).2) =
              segment ℝ (L[0]).1 (L[n]).2 := by
    intro hinc0 n
    induction n with
    | zero =>
        intro hn
        constructor
        · simpa using hinc0
        · constructor
          · simpa using hinc0
          · ext x
            simp
    | succ n ih =>
        intro hsucc
        have hn : n < L.length := Nat.lt_trans (Nat.lt_succ_self n) hsucc
        rcases ih hn with ⟨hincn, hfirstn, hunionn⟩
        have hconsec : n + 1 < L.length := by simpa using hsucc
        have hnext_ne : (L[n]).2 ≠ (L[n + 1]).2 := by
          have hne_next := hne (n + 1) hsucc
          rwa [← hlink n hconsec] at hne_next
        have hb_lt :
            (L[n]).2 < (L[n + 1]).2 := by
          exact real_next_inc hincn hnext_ne
            (by simpa [hlink n hconsec] using hinter n hconsec)
        have hnext_inc : (L[n + 1]).1 < (L[n + 1]).2 := by
          simpa [← hlink n hconsec] using hb_lt
        constructor
        · exact hnext_inc
        · have hprefix :
              (⋃ k : Fin (n + 1 + 1),
                  segment ℝ (L[k.1]).1 (L[k.1]).2)
                =
              (⋃ k : Fin (n + 1), segment ℝ (L[k.1]).1 (L[k.1]).2) ∪
                segment ℝ (L[n + 1]).1 (L[n + 1]).2 := by
            ext x
            constructor
            · intro hx
              rcases Set.mem_iUnion.mp hx with ⟨k, hk⟩
              by_cases hk_last : k.1 = n + 1
              · exact Or.inr (by simpa [hk_last] using hk)
              · have hklt : k.1 < n + 1 := by omega
                exact Or.inl (Set.mem_iUnion.2
                  ⟨⟨k.1, hklt⟩, by simpa using hk⟩)
            · intro hx
              rcases hx with hx | hx
              · rcases Set.mem_iUnion.mp hx with ⟨k, hk⟩
                exact Set.mem_iUnion.2
                  ⟨⟨k.1, Nat.lt_trans k.2 (Nat.lt_succ_self (n + 1))⟩,
                    by simpa using hk⟩
              · exact Set.mem_iUnion.2 ⟨⟨n + 1, by omega⟩, by simpa using hx⟩
          constructor
          · exact hfirstn.trans hb_lt
          · rw [hprefix, hunionn]
            have hle1 : (L[0]).1 ≤ (L[n]).2 := hfirstn.le
            have hle2 : (L[n]).2 ≤ (L[n + 1]).2 := hb_lt.le
            rw [← hlink n hconsec]
            exact real_segment_union_inc hle1 hle2
  have chain_dec :
      (L[0]).2 < (L[0]).1 →
        ∀ n (hn : n < L.length),
          (L[n]).2 < (L[n]).1 ∧ (L[n]).2 < (L[0]).1 ∧
            (⋃ k : Fin (n + 1), segment ℝ (L[k.1]).1 (L[k.1]).2) =
              segment ℝ (L[0]).1 (L[n]).2 := by
    intro hdec0 n
    induction n with
    | zero =>
        intro hn
        constructor
        · simpa using hdec0
        · constructor
          · simpa using hdec0
          · ext x
            simp
    | succ n ih =>
        intro hsucc
        have hn : n < L.length := Nat.lt_trans (Nat.lt_succ_self n) hsucc
        rcases ih hn with ⟨hdecn, hfirstn, hunionn⟩
        have hconsec : n + 1 < L.length := by simpa using hsucc
        have hnext_ne : (L[n]).2 ≠ (L[n + 1]).2 := by
          have hne_next := hne (n + 1) hsucc
          rwa [← hlink n hconsec] at hne_next
        have hb_gt :
            (L[n + 1]).2 < (L[n]).2 := by
          exact real_next_dec hdecn hnext_ne
            (by simpa [hlink n hconsec] using hinter n hconsec)
        have hnext_dec : (L[n + 1]).2 < (L[n + 1]).1 := by
          simpa [← hlink n hconsec] using hb_gt
        constructor
        · exact hnext_dec
        · have hprefix :
              (⋃ k : Fin (n + 1 + 1),
                  segment ℝ (L[k.1]).1 (L[k.1]).2)
                =
              (⋃ k : Fin (n + 1), segment ℝ (L[k.1]).1 (L[k.1]).2) ∪
                segment ℝ (L[n + 1]).1 (L[n + 1]).2 := by
            ext x
            constructor
            · intro hx
              rcases Set.mem_iUnion.mp hx with ⟨k, hk⟩
              by_cases hk_last : k.1 = n + 1
              · exact Or.inr (by simpa [hk_last] using hk)
              · have hklt : k.1 < n + 1 := by omega
                exact Or.inl (Set.mem_iUnion.2
                  ⟨⟨k.1, hklt⟩, by simpa using hk⟩)
            · intro hx
              rcases hx with hx | hx
              · rcases Set.mem_iUnion.mp hx with ⟨k, hk⟩
                exact Set.mem_iUnion.2
                  ⟨⟨k.1, Nat.lt_trans k.2 (Nat.lt_succ_self (n + 1))⟩,
                    by simpa using hk⟩
              · exact Set.mem_iUnion.2 ⟨⟨n + 1, by omega⟩, by simpa using hx⟩
          constructor
          · exact hb_gt.trans hfirstn
          · rw [hprefix, hunionn]
            have hle1 : (L[n]).2 ≤ (L[0]).1 := hfirstn.le
            have hle2 : (L[n + 1]).2 ≤ (L[n]).2 := hb_gt.le
            rw [← hlink n hconsec]
            exact real_segment_union_dec hle1 hle2
  have hfirst_ne : (L[0]).1 ≠ (L[0]).2 := hne 0 hpos
  have hlast : L.length - 1 < L.length := Nat.sub_one_lt_of_lt hpos
  have hlen : L.length - 1 + 1 = L.length := by omega
  have union_reindex :
      (⋃ k : Fin L.length, segment ℝ (L[k.1]).1 (L[k.1]).2) =
        (⋃ k : Fin (L.length - 1 + 1),
          segment ℝ (L[k.1]).1 (L[k.1]).2) := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨k, hk⟩
      exact Set.mem_iUnion.2 ⟨⟨k.1, by omega⟩, hk⟩
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨k, hk⟩
      exact Set.mem_iUnion.2 ⟨⟨k.1, by omega⟩, hk⟩
  rcases lt_or_gt_of_ne hfirst_ne with hinc0 | hdec0
  · have h := chain_inc hinc0 (L.length - 1) hlast
    exact union_reindex.trans h.2.2
  · have h := chain_dec hdec0 (L.length - 1) hlast
    exact union_reindex.trans h.2.2
