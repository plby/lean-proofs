import ErdosProblems.Erdos1166.Erdos1166HLOZIncompleteStoppedBlocks

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal ProbabilityTheory

namespace Erdos1166.HLOZMixedCreationBlocks

open HLOZDecomposition HLOZReconstruction HLOZActualStopped
  HLOZPrimedStopped HLOZIncompleteStoppedBlocks

noncomputable def horizontalChessBase (x : Site) : Site :=
  by
    classical
    exact if HLOZPairing.chessEven x then x else x + directionStep (1 : Direction)

theorem horizontalChessBase_chessEven (x : Site) :
    HLOZPairing.chessEven (horizontalChessBase x) := by
  classical
  unfold horizontalChessBase
  split_ifs with hx
  · exact hx
  · exact (chessEven_add_directionStep_iff x (1 : Direction)).mpr hx

theorem eq_horizontalChessBase_or_eq_add_paperE1 (x : Site) :
    x = horizontalChessBase x ∨ x = horizontalChessBase x + paperE1 := by
  classical
  unfold horizontalChessBase
  split_ifs with hx
  · exact Or.inl rfl
  · right
    ext <;> simp [directionStep, paperE1]

theorem exists_horizontal_chess_domino (y : Site) :
    ∃ x, HLOZPairing.chessEven x ∧ (y = x ∨ y = x + paperE1) := by
  exact ⟨horizontalChessBase y, horizontalChessBase_chessEven y,
    eq_horizontalChessBase_or_eq_add_paperE1 y⟩

theorem pairFree_X1_not_both_mem
    (C : Finset Site)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (x : Site) (hx : HLOZPairing.chessEven x) :
    ¬ (x ∈ C ∧ x + paperE1 ∈ C) := by
  rintro ⟨hxC, hxeC⟩
  apply hfree x hxC (x + paperE1) hxeC
  · exact (add_paperE1_ne_self x).symm
  · left
    refine ⟨hx, ?_⟩
    ext <;> simp [HLOZPairing.shift, HLOZPairing.vec,
      HLOZPairing.east, paperE1]

/-- The mixed horizontal-domino condition required by (4.7)--(4.8).
On a domino meeting the fixed creation set, the pair maximum equals `m`
and the unique level-`m` endpoint is the prescribed creation endpoint.
On every disjoint domino, the pair maximum is strictly below `m`. -/
def MixedX1DominoCondition
    (s : ℕ → Site) (T m : ℕ) (C : Finset Site) : Prop :=
  HLOZPairing.PairFree (HLOZPairing.XPair HLOZPairing.east) C ∧
    ∀ x, HLOZPairing.chessEven x →
      if _hC : x ∈ C ∨ x + paperE1 ∈ C then
        max (localTime s T x) (localTime s T (x + paperE1)) = m ∧
          (localTime s T x = m ↔ x ∈ C) ∧
          (localTime s T (x + paperE1) = m ↔ x + paperE1 ∈ C)
      else
        max (localTime s T x) (localTime s T (x + paperE1)) < m

theorem mixedX1DominoCondition_iff_level_sets
    (s : ℕ → Site) (T m : ℕ) (C : Finset Site)
    (hm : 0 < m)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C) :
    MixedX1DominoCondition s T m C ↔
      sitesAtLeastLevel s T m = C ∧
        sitesAtLeastLevel s T (m + 1) = ∅ := by
  constructor
  · rintro ⟨_, hmix⟩
    constructor
    · ext y
      obtain ⟨x, hx, hy⟩ := exists_horizontal_chess_domino y
      specialize hmix x hx
      split at hmix
      next hC =>
        rcases hmix with ⟨hmax, hxlevel, hxelevel⟩
        rcases hy with hy | hy
        · subst y
          simp only [sitesAtLeastLevel, Finset.mem_filter]
          constructor
          · exact fun h ↦ (hxlevel.mp (Nat.le_antisymm
              ((le_max_left _ _).trans_eq hmax) (by omega)))
          · intro hxC
            have hL : localTime s T x = m := hxlevel.mpr hxC
            refine ⟨?_, by omega⟩
            by_contra hxv
            have hz := localTime_eq_zero_of_not_mem_visitedSites hxv
            omega
        · subst y
          simp only [sitesAtLeastLevel, Finset.mem_filter]
          constructor
          · exact fun h ↦ (hxelevel.mp (Nat.le_antisymm
              ((le_max_right _ _).trans_eq hmax) (by omega)))
          · intro hxeC
            have hL : localTime s T (x + paperE1) = m := hxelevel.mpr hxeC
            refine ⟨?_, by omega⟩
            by_contra hxv
            have hz := localTime_eq_zero_of_not_mem_visitedSites hxv
            omega
      next hC =>
        rcases hy with hy | hy
        · subst y
          simp only [sitesAtLeastLevel, Finset.mem_filter]
          constructor
          · intro h
            have : m ≤ max (localTime s T x)
                (localTime s T (x + paperE1)) := h.2.trans (le_max_left _ _)
            omega
          · intro hxC
            exact (hC (Or.inl hxC)).elim
        · subst y
          simp only [sitesAtLeastLevel, Finset.mem_filter]
          constructor
          · intro h
            have : m ≤ max (localTime s T x)
                (localTime s T (x + paperE1)) := h.2.trans (le_max_right _ _)
            omega
          · intro hxeC
            exact (hC (Or.inr hxeC)).elim
    · apply Finset.eq_empty_iff_forall_notMem.mpr
      intro y hyplus
      obtain ⟨x, hx, hy⟩ := exists_horizontal_chess_domino y
      specialize hmix x hx
      split at hmix
      · rcases hmix with ⟨hmax, -⟩
        rcases hy with hy | hy
        · subst y
          have := (Finset.mem_filter.mp hyplus).2
          have hle := le_max_left (localTime s T x)
            (localTime s T (x + paperE1))
          omega
        · subst y
          have := (Finset.mem_filter.mp hyplus).2
          have hle := le_max_right (localTime s T x)
            (localTime s T (x + paperE1))
          omega
      · rcases hy with hy | hy
        · subst y
          have := (Finset.mem_filter.mp hyplus).2
          have hle := le_max_left (localTime s T x)
            (localTime s T (x + paperE1))
          omega
        · subst y
          have := (Finset.mem_filter.mp hyplus).2
          have hle := le_max_right (localTime s T x)
            (localTime s T (x + paperE1))
          omega
  · rintro ⟨hlevel, hplus⟩
    refine ⟨hfree, ?_⟩
    intro x hx
    have hle (y : Site) (hy : y ∈ C) : localTime s T y = m := by
      rw [← hlevel] at hy
      have hym := (Finset.mem_filter.mp hy).2
      have hynext : y ∉ sitesAtLeastLevel s T (m + 1) := by simp [hplus]
      have hylt : localTime s T y < m + 1 := by
        by_contra hnot
        apply hynext
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hy).1, by omega⟩
      omega
    split
    next hC =>
      have hmaxle : max (localTime s T x)
          (localTime s T (x + paperE1)) ≤ m := by
        apply max_le
        · by_contra hnot
          have hxv : x ∈ visitedSites s T := by
            by_contra hxv
            have hz := localTime_eq_zero_of_not_mem_visitedSites hxv
            omega
          have : x ∈ sitesAtLeastLevel s T (m + 1) :=
            Finset.mem_filter.mpr ⟨hxv, by omega⟩
          simp [hplus] at this
        · by_contra hnot
          have hxv : x + paperE1 ∈ visitedSites s T := by
            by_contra hxv
            have hz := localTime_eq_zero_of_not_mem_visitedSites hxv
            omega
          have : x + paperE1 ∈ sitesAtLeastLevel s T (m + 1) :=
            Finset.mem_filter.mpr ⟨hxv, by omega⟩
          simp [hplus] at this
      have hmaxge : m ≤ max (localTime s T x)
          (localTime s T (x + paperE1)) := by
        rcases hC with hxC | hxeC
        · rw [hle x hxC]
          exact le_max_left _ _
        · rw [hle (x + paperE1) hxeC]
          exact le_max_right _ _
      refine ⟨Nat.le_antisymm hmaxle hmaxge, ?_, ?_⟩
      · constructor
        · intro hxL
          rw [← hlevel]
          refine Finset.mem_filter.mpr ⟨?_, hxL.ge⟩
          by_contra hxv
          have hz := localTime_eq_zero_of_not_mem_visitedSites hxv
          omega
        · exact hle x
      · constructor
        · intro hxeL
          rw [← hlevel]
          refine Finset.mem_filter.mpr ⟨?_, hxeL.ge⟩
          by_contra hxv
          have hz := localTime_eq_zero_of_not_mem_visitedSites hxv
          omega
        · exact hle (x + paperE1)
    next hC =>
      apply lt_of_not_ge
      intro hge
      have hor : m ≤ localTime s T x ∨
          m ≤ localTime s T (x + paperE1) :=
        (le_max_iff.mp hge)
      rcases hor with hxL | hxeL
      · have hxv : x ∈ visitedSites s T := by
          by_contra hxv
          have hz := localTime_eq_zero_of_not_mem_visitedSites hxv
          omega
        apply hC (Or.inl ?_)
        rw [← hlevel]
        exact Finset.mem_filter.mpr ⟨hxv, hxL⟩
      · have hxv : x + paperE1 ∈ visitedSites s T := by
          by_contra hxv
          have hz := localTime_eq_zero_of_not_mem_visitedSites hxv
          omega
        apply hC (Or.inr ?_)
        rw [← hlevel]
        exact Finset.mem_filter.mpr ⟨hxv, hxeL⟩

theorem thresholdEventK_iff_next_level_empty_at_first
    (s : ℕ → Site) (m k T : ℕ)
    (hfirst : firstKSitesReachLevel m k s = T) :
    s ∈ hlozThresholdTimeEventK m k ↔
      sitesAtLeastLevel s T (m + 1) = ∅ := by
  change firstKSitesReachLevel m k s <
      firstKSitesReachLevel (m + 1) 1 s ↔ _
  rw [hfirst]
  constructor
  · intro hlt
    apply Finset.card_eq_zero.mp
    by_contra hne
    have hpos : 0 < (sitesAtLeastLevel s T (m + 1)).card :=
      Nat.pos_of_ne_zero hne
    have hmem : (sitesAtLeastLevel s T (m + 1)).card ∈ Set.Ici 1 := by
      exact hpos
    have hnot := notMem_of_lt_hittingAfter
      (u := fun n s ↦ (sitesAtLeastLevel s n (m + 1)).card)
      (s := Set.Ici 1) (n := 0) (k := T) (ω := s) hlt (Nat.zero_le T)
    exact hnot hmem
  · intro hempty
    by_contra hnot
    have hle : firstKSitesReachLevel (m + 1) 1 s ≤ (T : WithTop ℕ) := by
      simpa only [not_lt] using hnot
    change hittingAfter
        (fun n s ↦ (sitesAtLeastLevel s n (m + 1)).card)
        (Set.Ici 1) 0 s ≤ (T : WithTop ℕ) at hle
    obtain ⟨q, hq, hqmem⟩ := (hittingAfter_le_iff
      (u := fun n s ↦ (sitesAtLeastLevel s n (m + 1)).card)
      (s := Set.Ici 1) (n := 0) (ω := s) (i := T)).mp hle
    have hqnonempty : (sitesAtLeastLevel s q (m + 1)).Nonempty :=
      Finset.card_pos.mp (by exact hqmem)
    obtain ⟨x, hx⟩ := hqnonempty
    have hxT := sitesAtLeastLevel_mono_time
      (s := s) (m := m + 1) hq.2 hx
    rw [hempty] at hxT
    simp at hxT

theorem sourceCondition_at_first_iff_mixedX1
    (s : ℕ → Site) (m k T : ℕ) (C : Finset Site)
    (hm : 0 < m) (hk : 0 < k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hfirst : firstKSitesReachLevel m k s = T) :
    (s ∈ hlozThresholdTimeEventK m k ∧
        levelCreationSitesUpTo s m k = C) ↔
      MixedX1DominoCondition s T m C := by
  have hfinite : firstKSitesReachLevel m k s ≠ ⊤ := by simp [hfirst]
  have hlevel := sitesAtLeastLevel_at_threshold_eq_creationSites
    s m k hm hk hfinite
  have hTuntop : (firstKSitesReachLevel m k s).untopA = T := by
    rw [hfirst]
    rfl
  rw [hTuntop] at hlevel
  rw [mixedX1DominoCondition_iff_level_sets s T m C hm hfree,
    thresholdEventK_iff_next_level_empty_at_first s m k T hfirst]
  constructor
  · rintro ⟨hplus, hC⟩
    exact ⟨hlevel.trans hC, hplus⟩
  · rintro ⟨hC, hplus⟩
    exact ⟨hplus, hlevel.symm.trans hC⟩

end Erdos1166.HLOZMixedCreationBlocks
