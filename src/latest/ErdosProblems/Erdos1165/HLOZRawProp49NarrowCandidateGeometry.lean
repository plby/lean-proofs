/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZRawProp49UnpaidProfile
import ErdosProblems.Erdos1165.HLOZPrefixedProp49CandidateWindowRatio

/-!
# Narrow dominant candidates in raw low transitions

For each successive threshold creation, the endpoint selected at the future
creation is below level `m` at the old creation clock, as is its tiling mate.
The complement of the literal low-gap deficit then puts the dominant endpoint
of that domino in the exact Proposition 4.9 narrow window.
-/

open Set

namespace Erdos1165.HLOZRawProp49NarrowCandidateGeometry

open HLOZNoLazyFilteredTransitions HLOZPathEvents
open HLOZPrefixedProp49CandidateWindowRatio
open HLOZProposition48Candidates HLOZRawFullGapProductPromotion
open HLOZThetaSourceBalance
open HLOZTilingGapBandExtraction
open LazyDecomposition TilingLazyDecomposition

noncomputable section

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := HLOZRawFullGapProductPromotion.GapTriple

/-- Exact pathwise geometry needed to select one Proposition 4.9 coordinate
at the old creation clock. -/
structure RawProp49NarrowCandidateProfile
    (t : DominoTiling) (m rank : ℕ) (a : GapScale) (s : WalkPath) : Prop where
  exists_times : ∃ nOld nNew,
    ThresholdCreation s m rank nOld ∧
    ThresholdCreation s m (rank + 1) nNew ∧
    gapScaleOf m (s nOld) (s nNew) = a ∧
    localTime s nOld
      (tilingDominantEndpointAt t s nOld (s nNew)) ∈
        prop49NarrowTotalWindow m a

private theorem dominant_mem_prop49NarrowTotalWindow
    {t : DominoTiling} {m nOld nNew : ℕ} {a : GapScale}
    {s : WalkPath}
    (ha : a ∈ lowGapMesh)
    (hscale : gapScaleOf m (s nOld) (s nNew) = a)
    (hnotFailure : ¬lowGapDeficitFailure s m nOld nNew)
    (hxlt : localTime s nOld (s nNew) < m)
    (hpartnerlt : localTime s nOld (tilingPartner t (s nNew)) < m) :
    localTime s nOld (tilingDominantEndpointAt t s nOld (s nNew)) ∈
      prop49NarrowTotalWindow m a := by
  have hlower : m - gapDeficitCutoff m a ≤
      localTime s nOld (s nNew) := by
    by_contra hlt
    apply hnotFailure
    unfold lowGapDeficitFailure
    rw [hscale]
    exact ⟨ha, by omega⟩
  rw [mem_prop49NarrowTotalWindow]
  unfold tilingDominantEndpointAt
  split
  next => exact ⟨hlower, hxlt⟩
  next hnot =>
    have hgreater : localTime s nOld (s nNew) <
        localTime s nOld (tilingPartner t (s nNew)) :=
      Nat.lt_of_not_ge hnot
    exact ⟨hlower.trans hgreater.le, hpartnerlt⟩

private theorem localTime_lt_of_not_mem_thresholdSites
    {s : WalkPath} {n m : ℕ} {x : Point} (hm : 0 < m)
    (hx : x ∉ thresholdSites s n m) :
    localTime s n x < m := by
  simpa only [mem_thresholdSites_iff s n m x hm, not_le] using hx

/-- Rank-one raw low transitions select a literal narrow dominant source
coordinate at their old creation clock. -/
theorem firstRawCandidatePreliminary_narrowCandidateProfile
    (t : DominoTiling) (m : ℕ) (a : GapTriple) (s : WalkPath)
    (hm : 1 < m)
    (ha : a.1.1 ∈ lowGapMesh)
    (hs : s ∈ firstRawCandidatePreliminary t m a) :
    RawProp49NarrowCandidateProfile t m 1 a.1.1 s := by
  rcases Set.mem_iUnion.mp hs.1 with ⟨n₁, hn₁⟩
  rcases Set.mem_iUnion.mp hn₁ with ⟨n₂, hpair⟩
  change ThresholdCreation s m 1 n₁ ∧ ThresholdCreation s m 2 n₂ ∧
    thresholdCount s n₂ (m + 1) = 0 ∧
    ¬Tilings.sameDomino t (s n₁) (s n₂) ∧
    gapScaleOf m (s n₁) (s n₂) = a.1.1 at hpair
  rcases hpair with ⟨h₁, h₂, hnext, hsep, hscale⟩
  have hnotFailure : ¬lowGapDeficitFailure s m n₁ n₂ := by
    intro hfailure
    apply hs.2
    exact Set.mem_iUnion_of_mem n₁ <| Set.mem_iUnion_of_mem n₂
      ⟨(show s ∈ pairConfiguration t m a.1.1 n₁ n₂ from
        ⟨h₁, h₂, hnext, hsep, hscale⟩), hfailure⟩
  have hsites := thresholdSites_eq_singleton_at_first_creation h₁
  have hxnot : s n₂ ∉ thresholdSites s n₁ m := by
    rw [hsites, Finset.mem_singleton]
    exact (creation_locations_ne (by omega) (by omega) (by omega) h₁ h₂).symm
  have hpartnerNot : tilingPartner t (s n₂) ∉ thresholdSites s n₁ m := by
    rw [hsites, Finset.mem_singleton]
    intro hpartner
    apply hsep
    exact (Tilings.sameDomino_comm t _ _).mp
      ((sameDomino_iff_partner_eq t (s n₂) (s n₁)).2 hpartner)
  refine ⟨n₁, n₂, h₁, h₂, hscale, ?_⟩
  exact dominant_mem_prop49NarrowTotalWindow ha hscale hnotFailure
    (localTime_lt_of_not_mem_thresholdSites (by omega) hxnot)
    (localTime_lt_of_not_mem_thresholdSites (by omega) hpartnerNot)

/-- Rank-two raw low transitions select the second narrow dominant source
coordinate at their rank-two creation clock. -/
theorem secondRawCandidatePreliminary_narrowCandidateProfile
    (t : DominoTiling) (m : ℕ) (a : GapTriple) (s : WalkPath)
    (hm : 1 < m)
    (ha : a.1.2 ∈ lowGapMesh)
    (hs : s ∈ secondRawCandidatePreliminary t m a) :
    RawProp49NarrowCandidateProfile t m 2 a.1.2 s := by
  rcases Set.mem_iUnion.mp hs.1 with ⟨n₁, hn₁⟩
  rcases Set.mem_iUnion.mp hn₁ with ⟨n₂, hn₂⟩
  rcases Set.mem_iUnion.mp hn₂ with ⟨n₃, htriple⟩
  change ThresholdCreation s m 1 n₁ ∧ ThresholdCreation s m 2 n₂ ∧
    ThresholdCreation s m 3 n₃ ∧ thresholdCount s n₃ (m + 1) = 0 ∧
    ¬Tilings.sameDomino t (s n₁) (s n₂) ∧
    ¬Tilings.sameDomino t (s n₁) (s n₃) ∧
    ¬Tilings.sameDomino t (s n₂) (s n₃) ∧
    gapScaleOf m (s n₁) (s n₂) = a.1.1 ∧
    gapScaleOf m (s n₂) (s n₃) = a.1.2 at htriple
  rcases htriple with
    ⟨h₁, h₂, h₃, hnext, h₁₂, h₁₃, h₂₃, hscale₁, hscale₂⟩
  have hnotFailure : ¬lowGapDeficitFailure s m n₂ n₃ := by
    intro hfailure
    apply hs.2
    exact Set.mem_iUnion_of_mem n₁ <| Set.mem_iUnion_of_mem n₂ <|
      Set.mem_iUnion_of_mem n₃
        ⟨(show s ∈ tripleConfiguration t m a.1.1 a.1.2 n₁ n₂ n₃ from
          ⟨h₁, h₂, h₃, hnext, h₁₂, h₁₃, h₂₃, hscale₁, hscale₂⟩),
          hfailure⟩
  have hsites := thresholdSites_eq_pair_at_second_creation h₁ h₂
  have hxnot : s n₃ ∉ thresholdSites s n₂ m := by
    rw [hsites]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    intro h
    rcases h with h | h
    · exact (creation_locations_ne (by omega) (by omega) (by omega)
        h₁ h₃).symm h
    · exact (creation_locations_ne (by omega) (by omega) (by omega)
        h₂ h₃).symm h
  have hpartnerNot : tilingPartner t (s n₃) ∉ thresholdSites s n₂ m := by
    rw [hsites]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    intro h
    rcases h with h | h
    · apply h₁₃
      exact (Tilings.sameDomino_comm t _ _).mp
        ((sameDomino_iff_partner_eq t (s n₃) (s n₁)).2 h)
    · apply h₂₃
      exact (Tilings.sameDomino_comm t _ _).mp
        ((sameDomino_iff_partner_eq t (s n₃) (s n₂)).2 h)
  refine ⟨n₂, n₃, h₂, h₃, hscale₂, ?_⟩
  exact dominant_mem_prop49NarrowTotalWindow ha hscale₂ hnotFailure
    (localTime_lt_of_not_mem_thresholdSites (by omega) hxnot)
    (localTime_lt_of_not_mem_thresholdSites (by omega) hpartnerNot)

/-- Rank-three raw low transitions select the third narrow dominant source
coordinate at their rank-three creation clock. -/
theorem thirdRawCandidatePreliminary_narrowCandidateProfile
    (t : DominoTiling) (m : ℕ) (a : GapTriple) (s : WalkPath)
    (hm : 1 < m)
    (ha : a.2 ∈ lowGapMesh)
    (hs : s ∈ thirdRawCandidatePreliminary t m a) :
    RawProp49NarrowCandidateProfile t m 3 a.2 s := by
  rcases Set.mem_iUnion.mp hs.1 with ⟨n₁, hn₁⟩
  rcases Set.mem_iUnion.mp hn₁ with ⟨n₂, hn₂⟩
  rcases Set.mem_iUnion.mp hn₂ with ⟨n₃, hn₃⟩
  rcases Set.mem_iUnion.mp hn₃ with ⟨n₄, hquad⟩
  change ThresholdCreation s m 1 n₁ ∧ ThresholdCreation s m 2 n₂ ∧
    ThresholdCreation s m 3 n₃ ∧ ThresholdCreation s m 4 n₄ ∧
    thresholdCount s n₄ (m + 1) = 0 ∧
    fourPointsSeparated t (s n₁) (s n₂) (s n₃) (s n₄) ∧
    gapScaleOf m (s n₁) (s n₂) = a.1.1 ∧
    gapScaleOf m (s n₂) (s n₃) = a.1.2 ∧
    gapScaleOf m (s n₃) (s n₄) = a.2 at hquad
  rcases hquad with
    ⟨h₁, h₂, h₃, h₄, hnext, hsep, hscale₁, hscale₂, hscale₃⟩
  rcases hsep with ⟨h₁₂, h₁₃, h₁₄, h₂₃, h₂₄, h₃₄⟩
  have hnotFailure : ¬lowGapDeficitFailure s m n₃ n₄ := by
    intro hfailure
    apply hs.2
    exact Set.mem_iUnion_of_mem n₁ <| Set.mem_iUnion_of_mem n₂ <|
      Set.mem_iUnion_of_mem n₃ <| Set.mem_iUnion_of_mem n₄
        ⟨(show s ∈ quadrupleConfiguration t m a.1.1 a.1.2 a.2
            n₁ n₂ n₃ n₄ from
          ⟨h₁, h₂, h₃, h₄, hnext,
            ⟨h₁₂, h₁₃, h₁₄, h₂₃, h₂₄, h₃₄⟩,
            hscale₁, hscale₂, hscale₃⟩), hfailure⟩
  have hsites := thresholdSites_eq_triple_at_third_creation h₁ h₂ h₃
  have hxnot : s n₄ ∉ thresholdSites s n₃ m := by
    rw [hsites]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    intro h
    rcases h with h | h | h
    · exact (creation_locations_ne (by omega) (by omega) (by omega)
        h₁ h₄).symm h
    · exact (creation_locations_ne (by omega) (by omega) (by omega)
        h₂ h₄).symm h
    · exact (creation_locations_ne (by omega) (by omega) (by omega)
        h₃ h₄).symm h
  have hpartnerNot : tilingPartner t (s n₄) ∉ thresholdSites s n₃ m := by
    rw [hsites]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    intro h
    rcases h with h | h | h
    · apply h₁₄
      exact (Tilings.sameDomino_comm t _ _).mp
        ((sameDomino_iff_partner_eq t (s n₄) (s n₁)).2 h)
    · apply h₂₄
      exact (Tilings.sameDomino_comm t _ _).mp
        ((sameDomino_iff_partner_eq t (s n₄) (s n₂)).2 h)
    · apply h₃₄
      exact (Tilings.sameDomino_comm t _ _).mp
        ((sameDomino_iff_partner_eq t (s n₄) (s n₃)).2 h)
  refine ⟨n₃, n₄, h₃, h₄, hscale₃, ?_⟩
  exact dominant_mem_prop49NarrowTotalWindow ha hscale₃ hnotFailure
    (localTime_lt_of_not_mem_thresholdSites (by omega) hxnot)
    (localTime_lt_of_not_mem_thresholdSites (by omega) hpartnerNot)

end

end Erdos1165.HLOZRawProp49NarrowCandidateGeometry
