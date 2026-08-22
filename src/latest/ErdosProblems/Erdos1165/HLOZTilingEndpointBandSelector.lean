/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZTilingEndpointBandExtraction

/-!
# The finite beta selector for endpoint-only low-gap bands

This module closes the deterministic adjacent-beta enumeration up to HLOZ's
broad-window exponent `alphaMax`.  It deliberately keeps the two path facts
which are not consequences of the bare low-gap-deficit event visible: the
new favorite must already have enough old-prefix local time after the lazy
cap is removed, and its deficit must lie in the broad window.
-/

open Set

namespace Erdos1165.HLOZTilingEndpointBandSelector

open HLOZGapBetaArithmetic HLOZPathEvents HLOZProposition48Candidates
open HLOZGapRandomClockScreen
open HLOZTilingEndpointBandExtraction HLOZTilingGapBandExtraction
open HLOZTilingGapRandomClockScreen ScreeningInstantiation

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The bare low-gap failure controls the deficit in the lower direction.
It does not provide the broad-window upper bound used below. -/
theorem gapDeficitCutoff_lt_deficit_of_lowGapFailedPair
    {t : DominoTiling} {m cutoff : ℕ} {s : WalkPath}
    (p : LowGapFailedPair t m cutoff s) :
    gapDeficitCutoff m p.scale < p.deficit := by
  have hsum := p.localTime_add_deficit
  have hfailure := p.deficitFailure
  omega

/-- Sixty-four affine beta steps cover the whole `alphaMax = 3/4`
broad window, uniformly over the low spatial mesh. -/
theorem alphaMax_lt_terminal_deficitExponent48
    {a : GapScale} (ha : a ∈ lowGapMesh) :
    alphaMax < deficitExponent48 (meshExponent a) betaBandCount := by
  have halpha : meshExponent a ≤ kappaTwo :=
    (mem_lowGapMesh_iff.mp ha).2
  unfold deficitExponent48 betaBandCount
  norm_num [kappaOne, kappaTwo, meshDelta, alphaMax] at halpha ⊢
  nlinarith

private theorem ceil_rpow_le_shell_product
    {m : ℕ} (hm : 0 < m) (beta : ℝ) :
    Nat.ceil ((m : ℝ) ^ beta) ≤
      shellWidth48 m * shellCount48 m beta := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hwidth : (m : ℝ) ^ kappaOne ≤ shellWidth48 m := by
    exact_mod_cast Nat.le_ceil ((m : ℝ) ^ kappaOne)
  have hcount : (m : ℝ) ^ (beta - kappaOne) ≤ shellCount48 m beta := by
    exact_mod_cast Nat.le_ceil ((m : ℝ) ^ (beta - kappaOne))
  apply Nat.ceil_le.mpr
  push_cast
  calc
    (m : ℝ) ^ beta =
        (m : ℝ) ^ kappaOne * (m : ℝ) ^ (beta - kappaOne) := by
      rw [← Real.rpow_add hmR]
      congr 1
      ring
    _ ≤ (shellWidth48 m : ℝ) * shellCount48 m beta := by
      exact mul_le_mul hwidth hcount (Real.rpow_nonneg hmR.le _)
        (by positivity)

/-- An upper threshold crossing gives the exact Proposition 4.8 shell label
bound used by `FailedPairBetaBand`. -/
theorem deficit_div_shellWidth_lt_shellCount_of_lt_ceil_rpow
    {m deficit : ℕ} {beta : ℝ} (hm : 0 < m)
    (hdeficit : deficit < Nat.ceil ((m : ℝ) ^ beta)) :
    deficit / shellWidth48 m < shellCount48 m beta := by
  have hwidth : 0 < shellWidth48 m := by
    unfold shellWidth48
    exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast hm) _)
  rw [Nat.div_lt_iff_lt_mul hwidth]
  exact hdeficit.trans_le (by
    simpa only [Nat.mul_comm] using ceil_rpow_le_shell_product hm beta)

/-- Every failed pair whose deficit is in the broad window lies in one of
the literal 64 adjacent beta strips. -/
theorem exists_failedPairBetaBand_of_broadWindow
    {t : DominoTiling} {m cutoff : ℕ} {s : WalkPath}
    (p : LowGapFailedPair t m cutoff s) (hm : 1 < m)
    (hbroad : p.deficit < Nat.ceil ((m : ℝ) ^ alphaMax)) :
    ∃ j < betaBandCount, FailedPairBetaBand p j := by
  let threshold : ℕ → ℕ := fun j =>
    Nat.ceil ((m : ℝ) ^ deficitExponent48 (meshExponent p.scale) j)
  have hfirst : threshold 0 ≤ p.deficit := by
    have hfailure := p.deficitFailure
    have hsum := p.localTime_add_deficit
    have hcutoff : gapDeficitCutoff m p.scale < p.deficit := by omega
    simpa only [threshold, deficitExponent48_zero, gapDeficitCutoff] using
      hcutoff.le
  have hexponent := alphaMax_lt_terminal_deficitExponent48 p.scale_low
  have hpower : (m : ℝ) ^ alphaMax <
      (m : ℝ) ^ deficitExponent48 (meshExponent p.scale) betaBandCount :=
    Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast hm) hexponent
  have hceil : Nat.ceil ((m : ℝ) ^ alphaMax) ≤
      threshold betaBandCount := by
    apply Nat.ceil_mono
    exact hpower.le
  obtain ⟨j, hj, hlower, hupper⟩ :=
    exists_adjacent_threshold_band threshold p.deficit betaBandCount
      hfirst (hbroad.trans_le hceil)
  refine ⟨j, hj, hlower, ?_⟩
  exact deficit_div_shellWidth_lt_shellCount_of_lt_ceil_rpow
    (by omega) hupper

/-! ## Full source beta mesh for the large-deficit branch -/

/-- A fixed count large enough for the affine beta mesh to pass exponent one
at every low spatial scale.  HLOZ use the equivalent bound
`< 1 / meshDelta + 1`. -/
def fullBetaBandCount : ℕ := 128

theorem one_lt_terminal_deficitExponent48
    {a : GapScale} (ha : a ∈ lowGapMesh) :
    1 < deficitExponent48 (meshExponent a) fullBetaBandCount := by
  have halpha : meshExponent a ≤ kappaTwo :=
    (mem_lowGapMesh_iff.mp ha).2
  unfold deficitExponent48 fullBetaBandCount
  norm_num [kappaOne, kappaTwo, meshDelta] at halpha ⊢
  nlinarith

/-- The complete affine mesh covers every possible natural deficit, since a
failed pair has deficit at most `m` and the final exponent is greater than
one. -/
theorem exists_failedPairBetaBand_full
    {t : DominoTiling} {m cutoff : ℕ} {s : WalkPath}
    (p : LowGapFailedPair t m cutoff s) (hm : 1 < m) :
    ∃ j < fullBetaBandCount, FailedPairBetaBand p j ∧
      p.deficit < Nat.ceil ((m : ℝ) ^
        deficitExponent48 (meshExponent p.scale) (j + 1)) := by
  let threshold : ℕ → ℕ := fun j =>
    Nat.ceil ((m : ℝ) ^ deficitExponent48 (meshExponent p.scale) j)
  have hfirst : threshold 0 ≤ p.deficit := by
    simpa only [threshold, deficitExponent48_zero, gapDeficitCutoff] using
      (gapDeficitCutoff_lt_deficit_of_lowGapFailedPair p).le
  have hexponent := one_lt_terminal_deficitExponent48 p.scale_low
  have hmR : (1 : ℝ) < m := by exact_mod_cast hm
  have hpower : (m : ℝ) <
      (m : ℝ) ^ deficitExponent48 (meshExponent p.scale)
        fullBetaBandCount := by
    calc
      (m : ℝ) = (m : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ < (m : ℝ) ^ deficitExponent48 (meshExponent p.scale)
          fullBetaBandCount :=
        Real.rpow_lt_rpow_of_exponent_lt hmR hexponent
  have hdeficit_le : p.deficit ≤ m := by
    have hsum := p.localTime_add_deficit
    omega
  have hlast : p.deficit < threshold fullBetaBandCount := by
    apply Nat.lt_ceil.mpr
    exact (by exact_mod_cast hdeficit_le : (p.deficit : ℝ) ≤ m).trans_lt hpower
  obtain ⟨j, hj, hlower, hupper⟩ :=
    exists_adjacent_threshold_band threshold p.deficit fullBetaBandCount
      hfirst hlast
  refine ⟨j, hj, ⟨hlower, ?_⟩, hupper⟩
  exact deficit_div_shellWidth_lt_shellCount_of_lt_ceil_rpow
    (by omega) hupper

/-- A beta strip selected for a deficit outside the broad window necessarily
has its upper exponent outside that window as well. -/
theorem alphaMax_lt_betaNext_of_large_failedPairBand
    {t : DominoTiling} {m cutoff j : ℕ} {s : WalkPath}
    (p : LowGapFailedPair t m cutoff s) (hm : 1 < m)
    (hlarge : Nat.ceil ((m : ℝ) ^ alphaMax) ≤ p.deficit)
    (hupper : p.deficit < Nat.ceil ((m : ℝ) ^
      deficitExponent48 (meshExponent p.scale) (j + 1))) :
    alphaMax < deficitExponent48 (meshExponent p.scale) (j + 1) := by
  by_contra hnot
  have hexponent : deficitExponent48 (meshExponent p.scale) (j + 1) ≤
      alphaMax := le_of_not_gt hnot
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.le
  have hpower : (m : ℝ) ^
        deficitExponent48 (meshExponent p.scale) (j + 1) ≤
      (m : ℝ) ^ alphaMax :=
    Real.rpow_le_rpow_of_exponent_le hm1 hexponent
  have hceil : Nat.ceil ((m : ℝ) ^
        deficitExponent48 (meshExponent p.scale) (j + 1)) ≤
      Nat.ceil ((m : ℝ) ^ alphaMax) := Nat.ceil_mono hpower
  omega

/-! ## Canonical band metadata -/

/-- The beta-strip index carried by a canonical endpoint band.  The
definition is total on arbitrary bands; the recovery theorem below is used
only for members of the canonical finite list. -/
noncomputable def canonicalEndpointBandIndex
    (m : ℕ) (band : RandomClockBand) : ℕ :=
  if h : ∃ j < betaBandCount,
      band.beta = deficitExponent48 (meshExponent band.scale) (j + 1) ∧
        band.returns = requiredReturns48 m
          (deficitExponent48 (meshExponent band.scale) j) then
    Classical.choose h
  else 0

/-- Membership recovers the actual strip index used to construct the band. -/
theorem canonicalEndpointBandIndex_spec
    {m cap externalThreshold : ℕ} {band : RandomClockBand}
    (hband : band ∈
      canonicalEndpointLowGapBands m cap externalThreshold) :
    canonicalEndpointBandIndex m band < betaBandCount ∧
      band.beta = deficitExponent48 (meshExponent band.scale)
        (canonicalEndpointBandIndex m band + 1) ∧
      band.returns = requiredReturns48 m
        (deficitExponent48 (meshExponent band.scale)
          (canonicalEndpointBandIndex m band)) := by
  obtain ⟨tag, hscale, rfl⟩ :=
    (mem_canonicalEndpointLowGapBands_iff
      m cap externalThreshold _).mp hband
  have hexists : ∃ j < betaBandCount,
      (canonicalEndpointLowGapBand m cap externalThreshold tag).beta =
          deficitExponent48
            (meshExponent
              (canonicalEndpointLowGapBand m cap externalThreshold tag).scale)
            (j + 1) ∧
        (canonicalEndpointLowGapBand m cap externalThreshold tag).returns =
          requiredReturns48 m
            (deficitExponent48
              (meshExponent
                (canonicalEndpointLowGapBand m cap externalThreshold tag).scale)
              j) := by
    refine ⟨tag.index, tag.index.isLt, ?_, ?_⟩
    · simp only [canonicalEndpointLowGapBand,
        endpointLowGapScale_eq_of_mem tag hscale]
    · simp only [canonicalEndpointLowGapBand,
        endpointLowGapScale_eq_of_mem tag hscale]
  rw [canonicalEndpointBandIndex, dif_pos hexists]
  exact Classical.choose_spec hexists

/-- The finite scale/index template set underlying all canonical endpoint
bands. -/
private def canonicalEndpointLowGapTemplateSet : Set (GapScale × ℕ) :=
  (↑lowGapMesh : Set GapScale) ×ˢ Set.Iio betaBandCount

private theorem canonicalEndpointLowGapTemplateSet_finite :
    canonicalEndpointLowGapTemplateSet.Finite := by
  let f : GapScale × Fin betaBandCount → GapScale × ℕ :=
    fun p ↦ (p.1, p.2)
  apply (Set.finite_range f).subset
  intro p hp
  change p.1 ∈ lowGapMesh ∧ p.2 < betaBandCount at hp
  exact ⟨(p.1, ⟨p.2, hp.2⟩), rfl⟩

noncomputable def canonicalEndpointLowGapTemplates :
    Finset (GapScale × ℕ) :=
  canonicalEndpointLowGapTemplateSet_finite.toFinset

theorem mem_canonicalEndpointLowGapTemplates_iff (p : GapScale × ℕ) :
    p ∈ canonicalEndpointLowGapTemplates ↔
      p.1 ∈ lowGapMesh ∧ p.2 < betaBandCount := by
  rw [canonicalEndpointLowGapTemplates,
    Set.Finite.mem_toFinset]
  rfl

theorem canonicalEndpointLowGapTemplate_scale
    {p : GapScale × ℕ} (hp : p ∈ canonicalEndpointLowGapTemplates) :
    p.1 ∈ lowGapMesh := by
  exact (mem_canonicalEndpointLowGapTemplates_iff p).mp hp |>.1

theorem canonicalEndpointLowGapBand_projects
    {m cap externalThreshold : ℕ} {band : RandomClockBand}
    (hband : band ∈
      canonicalEndpointLowGapBands m cap externalThreshold) :
    (band.scale, canonicalEndpointBandIndex m band) ∈
      canonicalEndpointLowGapTemplates := by
  apply (mem_canonicalEndpointLowGapTemplates_iff _).mpr
  exact ⟨canonicalEndpointLowGapBand_scale hband,
    (canonicalEndpointBandIndex_spec hband).1⟩

theorem canonicalEndpointLowGapBand_betaUpper
    {m cap externalThreshold : ℕ} {band : RandomClockBand}
    (hband : band ∈
      canonicalEndpointLowGapBands m cap externalThreshold) :
    band.beta ≤ deficitExponent48 (meshExponent band.scale)
      (canonicalEndpointBandIndex m band + 1) := by
  exact (canonicalEndpointBandIndex_spec hband).2.1.le

theorem canonicalEndpointLowGapBand_betaLower
    {m cap externalThreshold : ℕ} {band : RandomClockBand}
    (hband : band ∈
      canonicalEndpointLowGapBands m cap externalThreshold) :
    ScreeningInstantiation.kappaOne ≤ band.beta := by
  rw [(canonicalEndpointBandIndex_spec hband).2.1]
  exact kappaOne_le_deficitExponent48
    (meshExponent_add_delta_le_kappaOne_of_mem_lowGapMesh
      (canonicalEndpointLowGapBand_scale hband))
    (by omega)

theorem canonicalEndpointLowGapBand_returns
    {m cap externalThreshold : ℕ} {band : RandomClockBand}
    (hband : band ∈
      canonicalEndpointLowGapBands m cap externalThreshold) :
    requiredReturns48 m
        (deficitExponent48 (meshExponent band.scale)
          (canonicalEndpointBandIndex m band)) ≤
      band.returns := by
  exact (canonicalEndpointBandIndex_spec hband).2.2.symm.le

/-- Endpoint-only extraction after the two genuine screenability conditions
are supplied.  Rank, scale, orientation, phase, return count, shell label,
and finite band membership are all discharged here. -/
theorem tilingLazyGoodEndpointExtraction_of_broadWindow
    {t : DominoTiling} {gapEvent : Set WalkPath}
    {m cutoff cap externalThreshold : ℕ}
    (hm : 1 < m) (hthreshold : 0 < externalThreshold)
    (hsurplus : ∀ s ∈ tilingLazyGoodPart t
        (gapEvent ∩ VariableStoppedTracePartition.validStepWalk) m cap,
      ∀ p : LowGapFailedPair t m cutoff s,
        cap + externalThreshold ≤ localTime s p.nOld (s p.nNew))
    (hbroad : ∀ s ∈ tilingLazyGoodPart t
        (gapEvent ∩ VariableStoppedTracePartition.validStepWalk) m cap,
      ∀ p : LowGapFailedPair t m cutoff s,
        p.deficit < Nat.ceil ((m : ℝ) ^ alphaMax))
    (hpair : ∀ s ∈ tilingLazyGoodPart t
        (gapEvent ∩ VariableStoppedTracePartition.validStepWalk) m cap,
      Nonempty (LowGapFailedPair t m cutoff s)) :
    TilingLazyGoodRandomClockExtraction t
      (gapEvent ∩ VariableStoppedTracePartition.validStepWalk)
      m cutoff cap
      (canonicalEndpointLowGapBands m cap externalThreshold) := by
  apply tilingLazyGoodEndpointExtraction_of_failedPairBetaBands hthreshold
  intro s hs
  obtain ⟨p⟩ := hpair s hs
  exact ⟨p, hsurplus s hs p,
    exists_failedPairBetaBand_of_broadWindow p hm (hbroad s hs p)⟩

/-- Specialization to the actual on-time low-gap event.  The failed pair is
now extracted internally; only the two missing screenability branches remain
visible. -/
theorem tilingLazyGoodEndpointExtraction_onTime_of_broadWindow
    {t : DominoTiling} {m cap externalThreshold : ℕ}
    (hm : 1 < m) (hthreshold : 0 < externalThreshold)
    (hsurplus : ∀ s ∈ tilingLazyGoodPart t
        (onTimeLowGapDeficitExceptionalEvent t m ∩
          VariableStoppedTracePartition.validStepWalk) m cap,
      ∀ p : LowGapFailedPair t m
          (levelCutoffTime upperTailDelta m) s,
        cap + externalThreshold ≤ localTime s p.nOld (s p.nNew))
    (hbroad : ∀ s ∈ tilingLazyGoodPart t
        (onTimeLowGapDeficitExceptionalEvent t m ∩
          VariableStoppedTracePartition.validStepWalk) m cap,
      ∀ p : LowGapFailedPair t m
          (levelCutoffTime upperTailDelta m) s,
        p.deficit < Nat.ceil ((m : ℝ) ^ alphaMax)) :
    TilingLazyGoodRandomClockExtraction t
      (onTimeLowGapDeficitExceptionalEvent t m ∩
        VariableStoppedTracePartition.validStepWalk)
      m (levelCutoffTime upperTailDelta m) cap
      (canonicalEndpointLowGapBands m cap externalThreshold) := by
  apply tilingLazyGoodEndpointExtraction_of_broadWindow hm hthreshold
    hsurplus hbroad
  intro s hs
  exact nonempty_lowGapFailedPair_of_mem_onTime hs.1.1

/-- The old-prefix local-time threshold is a numerical consequence of the
broad-window upper endpoint.  This is the non-probabilistic cap interface
needed by the endpoint screen. -/
theorem cap_add_externalThreshold_le_oldLocalTime_of_broadWindow
    {t : DominoTiling} {m cutoff cap externalThreshold : ℕ}
    {s : WalkPath} (p : LowGapFailedPair t m cutoff s)
    (hcapacity : cap + externalThreshold +
        Nat.ceil ((m : ℝ) ^ alphaMax) ≤ m + 1)
    (hbroad : p.deficit < Nat.ceil ((m : ℝ) ^ alphaMax)) :
    cap + externalThreshold ≤ localTime s p.nOld (s p.nNew) := by
  have hsum := p.localTime_add_deficit
  omega

/-- The part of the on-time low-gap event covered by HLOZ's broad-window
beta strips.  The complementary large-deficit branch requires a different
estimate; it is intentionally not folded into this event. -/
def onTimeBroadLowGapDeficitExceptionalEvent
    (t : DominoTiling) (m : ℕ) : Set WalkPath :=
  onTimeLowGapDeficitExceptionalEvent t m ∩
    {s | ∀ p : LowGapFailedPair t m
        (levelCutoffTime upperTailDelta m) s,
      p.deficit < Nat.ceil ((m : ℝ) ^ alphaMax)}

/-- Complementary source branch: at least one failed adjacent pair has
deficit outside the Proposition 4.8 broad window.  HLOZ handle this branch
by extending the beta mesh and using the deterministic cardinality of the
spatial ball, rather than the near-favorite product screen. -/
def onTimeLargeDeficitLowGapExceptionalEvent
    (t : DominoTiling) (m : ℕ) : Set WalkPath :=
  onTimeLowGapDeficitExceptionalEvent t m ∩
    {s | ∃ p : LowGapFailedPair t m
        (levelCutoffTime upperTailDelta m) s,
      Nat.ceil ((m : ℝ) ^ alphaMax) ≤ p.deficit}

/-- Exact event cover separating the Proposition 4.8 broad window from the
large-deficit spatial-cardinality branch in the source proof of Lemma 4.10. -/
theorem onTimeLowGap_subset_broad_union_large
    (t : DominoTiling) (m : ℕ) :
    onTimeLowGapDeficitExceptionalEvent t m ⊆
      onTimeBroadLowGapDeficitExceptionalEvent t m ∪
        onTimeLargeDeficitLowGapExceptionalEvent t m := by
  intro s hs
  by_cases hbroad : ∀ p : LowGapFailedPair t m
      (levelCutoffTime upperTailDelta m) s,
      p.deficit < Nat.ceil ((m : ℝ) ^ alphaMax)
  · exact Or.inl ⟨hs, hbroad⟩
  · push Not at hbroad
    exact Or.inr ⟨hs, hbroad⟩

theorem broad_union_large_subset_onTimeLowGap
    (t : DominoTiling) (m : ℕ) :
    onTimeBroadLowGapDeficitExceptionalEvent t m ∪
        onTimeLargeDeficitLowGapExceptionalEvent t m ⊆
      onTimeLowGapDeficitExceptionalEvent t m := by
  rintro s (hs | hs)
  · exact hs.1
  · exact hs.1

theorem onTimeLowGap_eq_broad_union_large
    (t : DominoTiling) (m : ℕ) :
    onTimeLowGapDeficitExceptionalEvent t m =
      onTimeBroadLowGapDeficitExceptionalEvent t m ∪
        onTimeLargeDeficitLowGapExceptionalEvent t m :=
  Set.Subset.antisymm
    (onTimeLowGap_subset_broad_union_large t m)
    (broad_union_large_subset_onTimeLowGap t m)

/-- No pathwise selection premise remains on the corrected broad-window
event: the failed pair comes from the low-gap event, and every remaining
candidate condition follows from its beta strip and the scalar cap bound. -/
theorem tilingLazyGoodEndpointExtraction_onTimeBroad
    {t : DominoTiling} {m cap externalThreshold : ℕ}
    (hm : 1 < m) (hthreshold : 0 < externalThreshold)
    (hcapacity : cap + externalThreshold +
        Nat.ceil ((m : ℝ) ^ alphaMax) ≤ m + 1) :
    TilingLazyGoodRandomClockExtraction t
      (onTimeBroadLowGapDeficitExceptionalEvent t m ∩
        VariableStoppedTracePartition.validStepWalk)
      m (levelCutoffTime upperTailDelta m) cap
      (canonicalEndpointLowGapBands m cap externalThreshold) := by
  apply tilingLazyGoodEndpointExtraction_of_broadWindow
    hm hthreshold
  · intro s hs p
    exact cap_add_externalThreshold_le_oldLocalTime_of_broadWindow
      p hcapacity (hs.1.1.2 p)
  · intro s hs p
    exact hs.1.1.2 p
  · intro s hs
    exact nonempty_lowGapFailedPair_of_mem_onTime hs.1.1.1

/-- Corrected endpoint selector for the broad low-gap branch.  All pathwise
candidate facts, including the old-prefix local-time surplus, now follow
from the failed-pair data and one scalar cap inequality. -/
theorem tilingLazyGoodEndpointExtraction_onTime_of_broadWindow_capacity
    {t : DominoTiling} {m cap externalThreshold : ℕ}
    (hm : 1 < m) (hthreshold : 0 < externalThreshold)
    (hcapacity : cap + externalThreshold +
        Nat.ceil ((m : ℝ) ^ alphaMax) ≤ m + 1)
    (hbroad : ∀ s ∈ tilingLazyGoodPart t
        (onTimeLowGapDeficitExceptionalEvent t m ∩
          VariableStoppedTracePartition.validStepWalk) m cap,
      ∀ p : LowGapFailedPair t m
          (levelCutoffTime upperTailDelta m) s,
        p.deficit < Nat.ceil ((m : ℝ) ^ alphaMax)) :
    TilingLazyGoodRandomClockExtraction t
      (onTimeLowGapDeficitExceptionalEvent t m ∩
        VariableStoppedTracePartition.validStepWalk)
      m (levelCutoffTime upperTailDelta m) cap
      (canonicalEndpointLowGapBands m cap externalThreshold) := by
  apply tilingLazyGoodEndpointExtraction_onTime_of_broadWindow
    hm hthreshold
  · intro s hs p
    exact cap_add_externalThreshold_le_oldLocalTime_of_broadWindow
      p hcapacity (hbroad s hs p)
  · exact hbroad

end

end Erdos1165.HLOZTilingEndpointBandSelector
