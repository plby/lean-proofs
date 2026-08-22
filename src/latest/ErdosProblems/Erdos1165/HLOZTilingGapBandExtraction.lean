/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos1165.HLOZTilingGapRandomClockScreen
import ErdosProblems.Erdos1165.HLOZGapBetaArithmetic

/-!
# Pathwise failed-pair extraction for the all-tiling gap screen

This file removes the time bookkeeping from the remaining beta-band
selector.  A path in the on-time low-gap event supplies one of its three
successive failed pairs, the genuine capped clocks equal the corresponding
creation times, and the new point is separated from every old favorite
domino.  The subsequent finite beta clipping therefore only has to classify
the single natural deficit `m - localTime old new`.
-/

open Set

namespace Erdos1165.HLOZTilingGapBandExtraction

open HLOZGapBetaArithmetic HLOZGapCandidateRealization HLOZGapFixedPair
open HLOZGapRandomClockScreen HLOZPathEvents
open HLOZProposition48Candidates
open HLOZTilingGapRandomClockScreen
open HLOZSpatialAdapter HLOZUpperEstimates
open LowerAssembly StoppedInsertion VariableStoppedFiber
open PreStoppingSpatialLaw
open TilingLazyDecomposition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

theorem pathTruncatedLevelTime_eq_of_creation_le_cutoff
    {s : WalkPath} {m k n cutoff : ℕ}
    (hcreation : ThresholdCreation s m k n) (hle : n ≤ cutoff) :
    pathTruncatedLevelTime m k cutoff s = n := by
  classical
  let hreach : ReachesThreshold s m k := ⟨n, hcreation.1⟩
  have hfindLe : Nat.find hreach ≤ n := Nat.find_min' hreach hcreation.1
  have hnLe : n ≤ Nat.find hreach := by
    by_contra hnot
    have hlt : Nat.find hreach < n := Nat.lt_of_not_ge hnot
    exact (Nat.not_le_of_gt (hcreation.2 (Nat.find hreach) hlt))
      (Nat.find_spec hreach)
  have hfind : Nat.find hreach = n := Nat.le_antisymm hfindLe hnLe
  unfold pathTruncatedLevelTime
  rw [dif_pos hreach, hfind, min_eq_left hle]

theorem thresholdSites_eq_favoriteSites_at_creation_of_terminal
    {s : WalkPath} {m k n nTerminal : ℕ}
    (hk : 0 < k) (hcreation : ThresholdCreation s m k n)
    (htime : n ≤ nTerminal)
    (hnext : thresholdCount s nTerminal (m + 1) = 0) :
    thresholdSites s n m = favoriteSites s n := by
  have hmono := thresholdCount_mono_time s (m + 1) htime
  have hnextOld : thresholdCount s n (m + 1) = 0 := by
    change thresholdCount s n (m + 1) ≤
      thresholdCount s nTerminal (m + 1) at hmono
    rw [hnext] at hmono
    omega
  have hbelow : ∀ y : Point, localTime s n y < m + 1 :=
    (thresholdCount_eq_zero_iff_forall_lt s n (m + 1)
      (Nat.zero_lt_succ m)).mp hnextOld
  exact thresholdSites_eq_favoriteSites_of_terminal s n m k hk
    (thresholdCount_eq_of_creation hk hcreation) hbelow

theorem thresholdSites_eq_singleton_at_first_creation
    {s : WalkPath} {m n₁ : ℕ}
    (h₁ : ThresholdCreation s m 1 n₁) :
    thresholdSites s n₁ m = {s n₁} := by
  have hmem := position_mem_thresholdSites_of_creation (by omega) h₁
  have hcount := thresholdCount_eq_of_creation (by omega) h₁
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [Finset.mem_singleton] at hx
    subst x
    exact hmem
  · change thresholdCount s n₁ m ≤ ({s n₁} : Finset Point).card
    simp [hcount]

theorem thresholdSites_eq_pair_at_second_creation
    {s : WalkPath} {m n₁ n₂ : ℕ}
    (h₁ : ThresholdCreation s m 1 n₁)
    (h₂ : ThresholdCreation s m 2 n₂) :
    thresholdSites s n₂ m = {s n₁, s n₂} := by
  have htime : n₁ < n₂ := creation_time_lt (by omega) (by omega)
    (by omega) h₁ h₂
  have hmem₁ := thresholdSites_mono_time s m htime.le
    (position_mem_thresholdSites_of_creation (by omega) h₁)
  have hmem₂ := position_mem_thresholdSites_of_creation (by omega) h₂
  have hne := creation_locations_ne (by omega) (by omega) (by omega) h₁ h₂
  have hcount := thresholdCount_eq_of_creation (by omega) h₂
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hmem₁
    · exact hmem₂
  · change thresholdCount s n₂ m ≤ ({s n₁, s n₂} : Finset Point).card
    rw [hcount]
    simp [hne]

theorem thresholdSites_eq_triple_at_third_creation
    {s : WalkPath} {m n₁ n₂ n₃ : ℕ}
    (h₁ : ThresholdCreation s m 1 n₁)
    (h₂ : ThresholdCreation s m 2 n₂)
    (h₃ : ThresholdCreation s m 3 n₃) :
    thresholdSites s n₃ m = {s n₁, s n₂, s n₃} := by
  have htime₁₃ : n₁ < n₃ := creation_time_lt (by omega) (by omega)
    (by omega) h₁ h₃
  have htime₂₃ : n₂ < n₃ := creation_time_lt (by omega) (by omega)
    (by omega) h₂ h₃
  have hmem₁ := thresholdSites_mono_time s m htime₁₃.le
    (position_mem_thresholdSites_of_creation (by omega) h₁)
  have hmem₂ := thresholdSites_mono_time s m htime₂₃.le
    (position_mem_thresholdSites_of_creation (by omega) h₂)
  have hmem₃ := position_mem_thresholdSites_of_creation (by omega) h₃
  have hne₁₂ := creation_locations_ne (by omega) (by omega) (by omega) h₁ h₂
  have hne₁₃ := creation_locations_ne (by omega) (by omega) (by omega) h₁ h₃
  have hne₂₃ := creation_locations_ne (by omega) (by omega) (by omega) h₂ h₃
  have hcount := thresholdCount_eq_of_creation (by omega) h₃
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hmem₁
    · exact hmem₂
    · exact hmem₃
  · change thresholdCount s n₃ m ≤
      ({s n₁, s n₂, s n₃} : Finset Point).card
    rw [hcount]
    simp [hne₁₂, hne₁₃, hne₂₃]

/-- Exact path data left after selecting one of the three failed pairs. -/
structure LowGapFailedPair (t : DominoTiling) (m cutoff : ℕ)
    (s : WalkPath) where
  oldRank : ℕ
  newRank : ℕ
  nOld : ℕ
  nNew : ℕ
  nTerminal : ℕ
  scale : GapScale
  oldRank_pos : 0 < oldRank
  newRank_pos : 0 < newRank
  rank_lt : oldRank < newRank
  rank_succ : newRank = oldRank + 1
  newRank_le_four : newRank ≤ 4
  oldCreation : ThresholdCreation s m oldRank nOld
  newCreation : ThresholdCreation s m newRank nNew
  terminalCreation : ThresholdCreation s m 4 nTerminal
  noNext : thresholdCount s nTerminal (m + 1) = 0
  oldClock : pathTruncatedLevelTime m oldRank cutoff s = nOld
  newClock : pathTruncatedLevelTime m newRank cutoff s = nNew
  terminalClock : pathTruncatedLevelTime m 4 cutoff s = nTerminal
  scale_low : scale ∈ lowGapMesh
  scale_eq : gapScaleOf m (s nOld) (s nNew) = scale
  deficitFailure : localTime s nOld (s nNew) +
    gapDeficitCutoff m scale < m
  separated : ∀ y ∈ favoriteSites s nOld,
    s nNew ≠ y ∧ ¬Tilings.sameDomino t (s nNew) y

namespace LowGapFailedPair

/-- The missing local time at the old creation clock. -/
def deficit {t : DominoTiling} {m cutoff : ℕ} {s : WalkPath}
    (p : LowGapFailedPair t m cutoff s) : ℕ :=
  m - localTime s p.nOld (s p.nNew)

theorem localTime_add_deficit {t : DominoTiling} {m cutoff : ℕ}
    {s : WalkPath} (p : LowGapFailedPair t m cutoff s) :
    localTime s p.nOld (s p.nNew) + p.deficit = m := by
  unfold deficit
  exact Nat.add_sub_of_le (by
    have h := p.deficitFailure
    omega)

/-- A beta lower endpoint below the deficit supplies the exact number of
strict returns required by the stopped geometric screen. -/
theorem randomClockPairRealizes
    {t : DominoTiling} {m cutoff : ℕ} {s : WalkPath}
    (p : LowGapFailedPair t m cutoff s) (band : RandomClockBand)
    (hranks : band.oldRank = p.oldRank ∧ band.newRank = p.newRank)
    (hscale : band.scale = p.scale)
    (hreturns : band.returns + 1 ≤ p.deficit) :
    RandomClockPairRealizes m cutoff s band (s p.nNew) := by
  rcases hranks with ⟨hold, hnew⟩
  unfold RandomClockPairRealizes
  rw [hold, hnew, hscale, p.oldClock, p.newClock, p.terminalClock]
  simp only [FixedPairReturnRealizes, FixedPairRealizes]
  refine ⟨⟨p.oldCreation, p.newCreation, p.noNext, ?_, p.scale_eq,
    ⟨?_, ?_⟩, trivial⟩, ?_⟩
  · rcases p.newRank_le_four.lt_or_eq with hlt | heq
    · exact (creation_time_lt p.newRank_pos (by omega) hlt
        p.newCreation p.terminalCreation).le
    · exact (thresholdCreation_time_unique p.newCreation
        (heq ▸ p.terminalCreation)).le
  · rw [p.scale_eq]
    exact p.scale_low
  · simpa only [p.scale_eq] using p.deficitFailure
  · calc
      localTime s p.nOld (s p.nNew) + (band.returns + 1) ≤
          localTime s p.nOld (s p.nNew) + p.deficit :=
        Nat.add_le_add_left hreturns _
      _ = m := p.localTime_add_deficit

end LowGapFailedPair

/-- Discrete adjacent-band crossing.  No monotonicity of the displayed
thresholds is needed. -/
theorem exists_adjacent_threshold_band
    (threshold : ℕ → ℕ) (deficit bands : ℕ)
    (hfirst : threshold 0 ≤ deficit)
    (hlast : deficit < threshold bands) :
    ∃ j < bands, threshold j ≤ deficit ∧ deficit < threshold (j + 1) := by
  induction bands with
  | zero => omega
  | succ bands ih =>
      by_cases hprev : deficit < threshold bands
      · obtain ⟨j, hj, hlower, hupper⟩ := ih hprev
        exact ⟨j, by omega, hlower, hupper⟩
      · exact ⟨bands, by omega, Nat.le_of_not_gt hprev, by simpa using hlast⟩

private theorem separated_from_first
    {t : DominoTiling} {s : WalkPath} {m n₁ n₂ n₃ n₄ : ℕ}
    (h₁ : ThresholdCreation s m 1 n₁)
    (h₂ : ThresholdCreation s m 2 n₂)
    (h₄ : ThresholdCreation s m 4 n₄)
    (hnext : thresholdCount s n₄ (m + 1) = 0)
    (hsep : fourPointsSeparated t (s n₁) (s n₂) (s n₃) (s n₄)) :
    ∀ y ∈ favoriteSites s n₁,
      s n₂ ≠ y ∧ ¬Tilings.sameDomino t (s n₂) y := by
  have htime : n₁ ≤ n₄ := (creation_time_lt (by omega) (by omega)
    (by omega) h₁ h₄).le
  have hfavorite := thresholdSites_eq_favoriteSites_at_creation_of_terminal
    (by omega) h₁ htime hnext
  have hsites := thresholdSites_eq_singleton_at_first_creation h₁
  intro y hy
  rw [← hfavorite, hsites, Finset.mem_singleton] at hy
  subst y
  exact ⟨(creation_locations_ne (by omega) (by omega) (by omega) h₁ h₂).symm,
    fun hdom ↦ hsep.1 ((Tilings.sameDomino_comm _ _ _).mpr hdom)⟩

private theorem separated_from_second
    {t : DominoTiling} {s : WalkPath} {m n₁ n₂ n₃ n₄ : ℕ}
    (h₁ : ThresholdCreation s m 1 n₁)
    (h₂ : ThresholdCreation s m 2 n₂)
    (h₃ : ThresholdCreation s m 3 n₃)
    (h₄ : ThresholdCreation s m 4 n₄)
    (hnext : thresholdCount s n₄ (m + 1) = 0)
    (hsep : fourPointsSeparated t (s n₁) (s n₂) (s n₃) (s n₄)) :
    ∀ y ∈ favoriteSites s n₂,
      s n₃ ≠ y ∧ ¬Tilings.sameDomino t (s n₃) y := by
  have htime : n₂ ≤ n₄ := (creation_time_lt (by omega) (by omega)
    (by omega) h₂ h₄).le
  have hfavorite := thresholdSites_eq_favoriteSites_at_creation_of_terminal
    (by omega) h₂ htime hnext
  have hsites := thresholdSites_eq_pair_at_second_creation h₁ h₂
  intro y hy
  rw [← hfavorite, hsites] at hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl
  · exact ⟨(creation_locations_ne (by omega) (by omega) (by omega) h₁ h₃).symm,
      fun hdom ↦ hsep.2.1 ((Tilings.sameDomino_comm _ _ _).mpr hdom)⟩
  · exact ⟨(creation_locations_ne (by omega) (by omega) (by omega) h₂ h₃).symm,
      fun hdom ↦ hsep.2.2.2.1 ((Tilings.sameDomino_comm _ _ _).mpr hdom)⟩

private theorem separated_from_third
    {t : DominoTiling} {s : WalkPath} {m n₁ n₂ n₃ n₄ : ℕ}
    (h₁ : ThresholdCreation s m 1 n₁)
    (h₂ : ThresholdCreation s m 2 n₂)
    (h₃ : ThresholdCreation s m 3 n₃)
    (h₄ : ThresholdCreation s m 4 n₄)
    (hnext : thresholdCount s n₄ (m + 1) = 0)
    (hsep : fourPointsSeparated t (s n₁) (s n₂) (s n₃) (s n₄)) :
    ∀ y ∈ favoriteSites s n₃,
      s n₄ ≠ y ∧ ¬Tilings.sameDomino t (s n₄) y := by
  have htime : n₃ ≤ n₄ := (creation_time_lt (by omega) (by omega)
    (by omega) h₃ h₄).le
  have hfavorite := thresholdSites_eq_favoriteSites_at_creation_of_terminal
    (by omega) h₃ htime hnext
  have hsites := thresholdSites_eq_triple_at_third_creation h₁ h₂ h₃
  intro y hy
  rw [← hfavorite, hsites] at hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl
  · exact ⟨(creation_locations_ne (by omega) (by omega) (by omega) h₁ h₄).symm,
      fun hdom ↦ hsep.2.2.1 ((Tilings.sameDomino_comm _ _ _).mpr hdom)⟩
  · exact ⟨(creation_locations_ne (by omega) (by omega) (by omega) h₂ h₄).symm,
      fun hdom ↦ hsep.2.2.2.2.1 ((Tilings.sameDomino_comm _ _ _).mpr hdom)⟩
  · exact ⟨(creation_locations_ne (by omega) (by omega) (by omega) h₃ h₄).symm,
      fun hdom ↦ hsep.2.2.2.2.2 ((Tilings.sameDomino_comm _ _ _).mpr hdom)⟩

/-- An on-time low-gap path supplies one literal failed adjacent creation
pair.  In particular, all three stopped clocks in the selected pair are the
genuine creation times; there is no deterministic time enumeration. -/
theorem nonempty_lowGapFailedPair_of_mem_onTime
    {t : DominoTiling} {m : ℕ} {s : WalkPath}
    (hs : s ∈ onTimeLowGapDeficitExceptionalEvent t m) :
    Nonempty (LowGapFailedPair t m (levelCutoffTime upperTailDelta m) s) := by
  rcases hs.1 with
    ⟨n₁, n₂, n₃, n₄, h₁, h₂, h₃, h₄, hnext, hsep, hfailure⟩
  have hcount₄ : thresholdCount s n₄ m = 4 :=
    thresholdCount_eq_of_creation (by omega) h₄
  have hfavorite : levelFavorite s m 4 :=
    (levelFavorite_iff_thresholdCounts s m 4 (by omega)).2
      ⟨n₄, hcount₄, hnext⟩
  have hn₄floor : n₄ ≤ ⌊levelCutoff upperTailDelta m⌋₊ := by
    by_contra hnot
    apply hs.2
    refine ⟨?_, hfavorite⟩
    rw [thresholdTime_eq_creationTime h₄]
    exact_mod_cast Nat.lt_of_not_ge hnot
  have hn₄cutoff : n₄ ≤ levelCutoffTime upperTailDelta m := by
    exact hn₄floor.trans (by
      simpa only [levelCutoffTime] using
        (Nat.floor_le_ceil (levelCutoff upperTailDelta m)))
  have hclock₄ : pathTruncatedLevelTime m 4
      (levelCutoffTime upperTailDelta m) s = n₄ :=
    pathTruncatedLevelTime_eq_of_creation_le_cutoff h₄ hn₄cutoff
  have hn₁n₂ : n₁ < n₂ := creation_time_lt (by omega) (by omega)
    (by omega) h₁ h₂
  have hn₂n₃ : n₂ < n₃ := creation_time_lt (by omega) (by omega)
    (by omega) h₂ h₃
  have hn₃n₄ : n₃ < n₄ := creation_time_lt (by omega) (by omega)
    (by omega) h₃ h₄
  have hclock₁ : pathTruncatedLevelTime m 1
      (levelCutoffTime upperTailDelta m) s = n₁ :=
    pathTruncatedLevelTime_eq_of_creation_le_cutoff h₁
      ((hn₁n₂.trans (hn₂n₃.trans hn₃n₄)).le.trans hn₄cutoff)
  have hclock₂ : pathTruncatedLevelTime m 2
      (levelCutoffTime upperTailDelta m) s = n₂ :=
    pathTruncatedLevelTime_eq_of_creation_le_cutoff h₂
      ((hn₂n₃.trans hn₃n₄).le.trans hn₄cutoff)
  have hclock₃ : pathTruncatedLevelTime m 3
      (levelCutoffTime upperTailDelta m) s = n₃ :=
    pathTruncatedLevelTime_eq_of_creation_le_cutoff h₃
      (hn₃n₄.le.trans hn₄cutoff)
  rcases hfailure with hfailure | hfailure | hfailure
  · change gapScaleOf m (s n₁) (s n₂) ∈ lowGapMesh ∧
      localTime s n₁ (s n₂) +
        gapDeficitCutoff m (gapScaleOf m (s n₁) (s n₂)) < m at hfailure
    exact ⟨
      { oldRank := 1
        newRank := 2
        nOld := n₁
        nNew := n₂
        nTerminal := n₄
        scale := gapScaleOf m (s n₁) (s n₂)
        oldRank_pos := by omega
        newRank_pos := by omega
        rank_lt := by omega
        rank_succ := rfl
        newRank_le_four := by omega
        oldCreation := h₁
        newCreation := h₂
        terminalCreation := h₄
        noNext := hnext
        oldClock := hclock₁
        newClock := hclock₂
        terminalClock := hclock₄
        scale_low := hfailure.1
        scale_eq := rfl
        deficitFailure := hfailure.2
        separated := separated_from_first h₁ h₂ h₄ hnext hsep }⟩
  · change gapScaleOf m (s n₂) (s n₃) ∈ lowGapMesh ∧
      localTime s n₂ (s n₃) +
        gapDeficitCutoff m (gapScaleOf m (s n₂) (s n₃)) < m at hfailure
    exact ⟨
      { oldRank := 2
        newRank := 3
        nOld := n₂
        nNew := n₃
        nTerminal := n₄
        scale := gapScaleOf m (s n₂) (s n₃)
        oldRank_pos := by omega
        newRank_pos := by omega
        rank_lt := by omega
        rank_succ := rfl
        newRank_le_four := by omega
        oldCreation := h₂
        newCreation := h₃
        terminalCreation := h₄
        noNext := hnext
        oldClock := hclock₂
        newClock := hclock₃
        terminalClock := hclock₄
        scale_low := hfailure.1
        scale_eq := rfl
        deficitFailure := hfailure.2
        separated := separated_from_second h₁ h₂ h₃ h₄ hnext hsep }⟩
  · change gapScaleOf m (s n₃) (s n₄) ∈ lowGapMesh ∧
      localTime s n₃ (s n₄) +
        gapDeficitCutoff m (gapScaleOf m (s n₃) (s n₄)) < m at hfailure
    exact ⟨
      { oldRank := 3
        newRank := 4
        nOld := n₃
        nNew := n₄
        nTerminal := n₄
        scale := gapScaleOf m (s n₃) (s n₄)
        oldRank_pos := by omega
        newRank_pos := by omega
        rank_lt := by omega
        rank_succ := rfl
        newRank_le_four := by omega
        oldCreation := h₃
        newCreation := h₄
        terminalCreation := h₄
        noNext := hnext
        oldClock := hclock₃
        newClock := hclock₄
        terminalClock := hclock₄
        scale_low := hfailure.1
        scale_eq := rfl
        deficitFailure := hfailure.2
        separated := separated_from_third h₁ h₂ h₃ h₄ hnext hsep }⟩

/-! ## The finite rank/scale/phase/beta list -/

/-- A fixed finite number of beta steps.  The exact terminal coverage is kept
as a numerical hypothesis below, so this definition does not conceal any
asymptotic claim. -/
def betaBandCount : ℕ := 64

/-- Enumeration tag.  Physical creation times are deliberately absent. -/
structure CanonicalLowGapBandTag where
  pair : Fin 3
  scale : {a : GapScale // a ∈ lowGapMesh}
  orientation : LazyDecomposition.Orientation
  vertexPhase : Bool
  index : Fin betaBandCount
  deriving DecidableEq

/-- The actual random-clock band represented by one finite tag. -/
noncomputable def canonicalLowGapBand
    (m cap phaseThreshold : ℕ) (tag : CanonicalLowGapBandTag) :
    RandomClockBand where
  orientation := tag.orientation
  vertexPhase := tag.vertexPhase
  oldRank := tag.pair + 1
  newRank := tag.pair + 2
  returns := requiredReturns48 m
    (deficitExponent48 (meshExponent tag.scale.1) tag.index)
  externalThreshold := phaseThreshold
  lazyCap := cap
  beta := deficitExponent48 (meshExponent tag.scale.1) (tag.index + 1)
  scale := tag.scale.1
  oldRank_pos := by omega
  newRank_pos := by omega
  rank_lt := by omega
  newRank_le_four := by omega
  scale_proper := (mem_lowGapMesh_iff.mp tag.scale.2).1

/-- Exact remaining deterministic input for one selected beta strip.  The
lower bound drives the return schedule; the upper strip bound places the
site in the Proposition 4.8 candidate set. -/
def FailedPairBetaBand {t : DominoTiling} {m cutoff : ℕ} {s : WalkPath}
    (p : LowGapFailedPair t m cutoff s) (j : ℕ) : Prop :=
  Nat.ceil ((m : ℝ) ^ deficitExponent48 (meshExponent p.scale) j) ≤
      p.deficit ∧
    p.deficit / shellWidth48 m <
      shellCount48 m
        (deficitExponent48 (meshExponent p.scale) (j + 1))

end

end Erdos1165.HLOZTilingGapBandExtraction
