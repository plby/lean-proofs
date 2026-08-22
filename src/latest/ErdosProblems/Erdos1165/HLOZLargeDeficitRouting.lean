/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZTilingEndpointBandSelector
import ErdosProblems.Erdos1165.HLOZGapMeshEscape

/-!
# Routing the large-deficit part of HLOZ Lemma 4.10

The proof of Lemma 4.10 in Hao--Li--Okada--Zheng does not stop its deficit
mesh at a fixed exponent below one.  For a deficit-band exponent at most
`7 / 10`, Proposition 4.8 bounds the cardinality of the near-favorite set.
For a larger exponent, the paper instead uses the deterministic bound on the
number of lattice points in the spatial ball around the old favorite.  The
geometric point-before-return estimate is then applied in both cases.

`onTimeBroadLowGapDeficitExceptionalEvent` contains precisely the paths for
which every available failed-pair witness has deficit below
`ceil (m ^ alphaMax)`.  This file names and routes its complement inside the
raw on-time event.  In particular, a path in that complement supplies a
failed pair with both the large-deficit lower bound and the original spatial
mesh-radius bound.  It also realizes every matching random-clock band whose
return count is at most the corresponding large-deficit count.

This is only the deterministic split and routing step.  A probability bound
for the large branch must enumerate the spatially restricted lattice ball;
the existing `tilingRandomClockBandSites` is not spatially restricted and so
its cardinality cannot be bounded by that argument alone.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZLargeDeficitRouting

open HLOZGapBetaArithmetic HLOZGapMeshEscape HLOZGapRandomClockScreen
open HLOZPathEvents HLOZTilingEndpointBandSelector
open HLOZTilingGapBandExtraction ScreeningInstantiation

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Short local name for the source-level large-deficit branch defined by
the endpoint band selector. -/
abbrev onTimeLargeLowGapDeficitExceptionalEvent :=
  onTimeLargeDeficitLowGapExceptionalEvent

theorem mem_onTimeLargeLowGapDeficitExceptionalEvent_iff
    {t : DominoTiling} {m : ℕ} {s : WalkPath} :
    s ∈ onTimeLargeLowGapDeficitExceptionalEvent t m ↔
      s ∈ onTimeLowGapDeficitExceptionalEvent t m ∧
        ∃ p : LowGapFailedPair t m
            (levelCutoffTime upperTailDelta m) s,
          Nat.ceil ((m : ℝ) ^ alphaMax) ≤ p.deficit :=
  Iff.rfl

/-- Exact case split: the raw event is the union of the already screened
broad-window branch and the large-deficit branch from Lemma 4.10. -/
theorem onTimeLowGapDeficitExceptionalEvent_eq_broad_union_large
    (t : DominoTiling) (m : ℕ) :
    onTimeLowGapDeficitExceptionalEvent t m =
      onTimeBroadLowGapDeficitExceptionalEvent t m ∪
        onTimeLargeLowGapDeficitExceptionalEvent t m :=
  onTimeLowGap_eq_broad_union_large t m

/-- The two routed branches are disjoint. -/
theorem disjoint_onTimeBroad_onTimeLarge
    (t : DominoTiling) (m : ℕ) :
    Disjoint (onTimeBroadLowGapDeficitExceptionalEvent t m)
      (onTimeLargeLowGapDeficitExceptionalEvent t m) := by
  rw [Set.disjoint_left]
  intro s hbroad hlarge
  obtain ⟨p, hp⟩ := hlarge.2
  exact (Nat.not_lt_of_ge hp) (hbroad.2 p)

/-- Probability-level routing.  No estimate on the missing large branch is
smuggled into this statement. -/
theorem simpleRandomWalk_onTimeLowGapDeficitExceptionalEvent_le_broad_add_large
    (t : DominoTiling) (m : ℕ) :
    simpleRandomWalk (onTimeLowGapDeficitExceptionalEvent t m) ≤
      simpleRandomWalk (onTimeBroadLowGapDeficitExceptionalEvent t m) +
        simpleRandomWalk
          (onTimeLargeLowGapDeficitExceptionalEvent t m) := by
  rw [onTimeLowGapDeficitExceptionalEvent_eq_broad_union_large]
  exact measure_union_le _ _

/-- A low-gap failed pair is automatically in its defining spatial ball.
This is the deterministic cardinality input used for the high deficit bands
in the source proof of Lemma 4.10. -/
theorem failedPair_latticeDistance_le_meshRadius
    {t : DominoTiling} {m cutoff : ℕ} {s : WalkPath}
    (p : LowGapFailedPair t m cutoff s) :
    latticeDistance (s p.nOld) (s p.nNew) ≤ meshRadius m p.scale := by
  exact latticeDistance_le_meshRadius_of_gapScaleOf_eq
    (mem_lowGapMesh_iff.mp p.scale_low).1 p.scale_eq

/-- The large branch supplies an actual failed pair carrying both the
large-deficit lower bound and the spatial restriction used to enumerate the
source paper's finite set `F_j`. -/
theorem exists_largeDeficitFailedPair_with_spatial_bound_of_mem
    {t : DominoTiling} {m : ℕ} {s : WalkPath}
    (hs : s ∈ onTimeLargeLowGapDeficitExceptionalEvent t m) :
    ∃ p : LowGapFailedPair t m
        (levelCutoffTime upperTailDelta m) s,
      Nat.ceil ((m : ℝ) ^ alphaMax) ≤ p.deficit ∧
        latticeDistance (s p.nOld) (s p.nNew) ≤
          meshRadius m p.scale := by
  obtain ⟨p, hp⟩ := hs.2
  exact ⟨p, hp, failedPair_latticeDistance_le_meshRadius p⟩

/-- A large-deficit failed pair realizes any matching random-clock band with
at most `requiredReturns48 m alphaMax` requested returns.  This is the exact
bridge from the large-deficit cutoff to the geometric-return part of the
HLOZ screen; only the deterministic spatial enumeration remains separate. -/
theorem LowGapFailedPair.randomClockPairRealizes_of_largeDeficit
    {t : DominoTiling} {m cutoff : ℕ} {s : WalkPath}
    (p : LowGapFailedPair t m cutoff s) (hm : 0 < m)
    (hlarge : Nat.ceil ((m : ℝ) ^ alphaMax) ≤ p.deficit)
    (band : RandomClockBand)
    (hranks : band.oldRank = p.oldRank ∧ band.newRank = p.newRank)
    (hscale : band.scale = p.scale)
    (hreturns : band.returns ≤ requiredReturns48 m alphaMax) :
    RandomClockPairRealizes m cutoff s band (s p.nNew) := by
  have hpow : 0 < (m : ℝ) ^ alphaMax :=
    Real.rpow_pos_of_pos (by exact_mod_cast hm) _
  have hreturnCount : band.returns + 1 ≤ p.deficit := by
    calc
      band.returns + 1 ≤ requiredReturns48 m alphaMax + 1 :=
        Nat.add_le_add_right hreturns 1
      _ = Nat.ceil ((m : ℝ) ^ alphaMax) :=
        requiredReturns48_add_one hpow
      _ ≤ p.deficit := hlarge
  exact p.randomClockPairRealizes band hranks hscale hreturnCount

/-- The cutoff used here is genuinely in the source paper's deterministic
high-band range: `alphaMax = 3/4` lies strictly above `7/10`. -/
theorem sevenTenths_lt_alphaMax : (7 / 10 : ℝ) < alphaMax := by
  norm_num [alphaMax]

end

end Erdos1165.HLOZLargeDeficitRouting
