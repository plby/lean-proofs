/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZTypedStoppedCandidateFamily
import ErdosProblems.Erdos1165.TilingShellZeroSourcePartition

/-!
# Prefix semantics of typed stopped candidates

This file supplies the deterministic bridge used before the low-scale
strong-Markov factor.

* The complete actual random-clock candidate `Finset` is observable at the
  old capped creation clock.  This is stronger than observability of one
  enumerated slot.
* The literal `D_eta` and `Theta_eta` statistics are invariant under equality
  of the physical path prefix on which they are evaluated.

No eligibility event and no transition-probability estimate is introduced
here.  In particular, the source-balance layer remains responsible for
constructing and paying the complement of its creation-time good event.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZTypedStoppedCandidateObservability

open HLOZGapRandomClockScreen HLOZPathEvents
open HLOZTilingGapRandomClockScreen StoppedInsertion
open TilingLazyDecomposition TilingShellZeroSourcePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-! ## Observability of the complete actual candidate set -/

/-- The full candidate Finset, rather than just one candidate slot, is a
stopped-past observable at the band's old-rank capped creation clock. -/
theorem tilingRandomClockBandSites_fiber_observable
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand)
    (S : Finset Point) :
    IsMeasurableAtStopping
      (truncatedLevelTime m band.oldRank cutoff)
      {omega | tilingRandomClockBandSites
        t m cutoff (trajectory omega) band = S} := by
  intro n
  let deterministicSites : StepPath → Finset Point := fun omega ↦
    tilingPrefixBandSites t band.orientation band.vertexPhase
      band.externalThreshold m band.beta
        (trajectoryPrefix (stepPrefix n omega))
  have hdetMeas : Measurable[incrementFiltration n] deterministicSites := by
    rw [incrementFiltration_apply]
    exact (measurable_of_countable
      (fun u : Fin n → Direction ↦
        tilingPrefixBandSites t band.orientation band.vertexPhase
          band.externalThreshold m band.beta (trajectoryPrefix u))).comp
      (comap_measurable (stepPrefix n))
  have heq :
      {omega | tilingRandomClockBandSites
          t m cutoff (trajectory omega) band = S} ∩
          {omega | truncatedLevelTime m band.oldRank cutoff omega = n} =
        {omega | deterministicSites omega = S} ∩
          {omega | truncatedLevelTime m band.oldRank cutoff omega = n} := by
    ext omega
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hsites, hclock⟩
      refine ⟨?_, hclock⟩
      have hclock' : pathTruncatedLevelTime m band.oldRank cutoff
          (trajectory omega) = n := by
        simpa only [pathTruncatedLevelTime_trajectory] using hclock
      simpa only [tilingRandomClockBandSites_eq_prefix_of_clock hclock',
        deterministicSites, trajectoryPrefix_stepPrefix] using hsites
    · rintro ⟨hsites, hclock⟩
      refine ⟨?_, hclock⟩
      have hclock' : pathTruncatedLevelTime m band.oldRank cutoff
          (trajectory omega) = n := by
        simpa only [pathTruncatedLevelTime_trajectory] using hclock
      simpa only [tilingRandomClockBandSites_eq_prefix_of_clock hclock',
        deterministicSites, trajectoryPrefix_stepPrefix] using hsites
  rw [heq]
  exact (measurableSet_eq_fun hdetMeas measurable_const).inter
    ((isFiniteStoppingTime_truncatedLevelTime
      m band.oldRank cutoff).measurableSet_eq n)

/-- Candidate overflow is itself known at the old capped creation clock. -/
theorem tilingRandomClockBandOverflow_observable
    (t : DominoTiling) (m cutoff budget : ℕ) (band : RandomClockBand) :
    IsMeasurableAtStopping
      (truncatedLevelTime m band.oldRank cutoff)
      {omega | budget <
        (tilingRandomClockBandSites
          t m cutoff (trajectory omega) band).card} := by
  intro n
  have heq :
      {omega | budget <
          (tilingRandomClockBandSites
            t m cutoff (trajectory omega) band).card} ∩
          {omega | truncatedLevelTime m band.oldRank cutoff omega = n} =
        ⋃ S : Finset Point, ⋃ (_hS : budget < S.card),
          ({omega | tilingRandomClockBandSites
              t m cutoff (trajectory omega) band = S} ∩
            {omega | truncatedLevelTime m band.oldRank cutoff omega = n}) := by
    ext omega
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨hoverflow, hclock⟩
      exact ⟨tilingRandomClockBandSites t m cutoff (trajectory omega) band,
        hoverflow, rfl, hclock⟩
    · rintro ⟨S, hS, hsites, hclock⟩
      exact ⟨hsites.symm ▸ hS, hclock⟩
  rw [heq]
  exact MeasurableSet.iUnion fun S ↦
    MeasurableSet.iUnion fun _hS ↦
      tilingRandomClockBandSites_fiber_observable t m cutoff band S n

/-! ## Fixed-prefix invariance of the literal source predicates -/

theorem localTime_eq_of_pathPrefix_eq
    {s s' : WalkPath} {n : ℕ} (hp : pathPrefix s n = pathPrefix s' n)
    (x : Point) :
    localTime s n x = localTime s' n x := by
  unfold localTime
  rw [hp]

theorem visitedTilingBases_eq_of_pathPrefix_eq
    (t : DominoTiling) {s s' : WalkPath} {n : ℕ}
    (hp : pathPrefix s n = pathPrefix s' n) :
    visitedTilingBases t s n = visitedTilingBases t s' n := by
  unfold visitedTilingBases visitedSites
  rw [hp]

theorem tilingDominoLocalTime_eq_of_pathPrefix_eq
    (t : DominoTiling) {s s' : WalkPath} {n : ℕ}
    (hp : pathPrefix s n = pathPrefix s' n) (b : Point) :
    tilingDominoLocalTime t s n b = tilingDominoLocalTime t s' n b := by
  unfold tilingDominoLocalTime localTime
  rw [hp]

theorem tilingExternalBaseLocalTime_eq_of_pathPrefix_eq
    (t : DominoTiling) {s s' : WalkPath} {n : ℕ}
    (hp : pathPrefix s n = pathPrefix s' n) (b : Point) :
    tilingExternalBaseLocalTime t s n b =
      tilingExternalBaseLocalTime t s' n b := by
  unfold tilingExternalBaseLocalTime
  rw [hp]

theorem tilingVOneAt_iff_of_pathPrefix_eq
    (t : DominoTiling) (m : ℕ) {s s' : WalkPath} {n : ℕ}
    (hp : pathPrefix s n = pathPrefix s' n) (b : Point) :
    tilingVOneAt t m s n b ↔ tilingVOneAt t m s' n b := by
  unfold tilingVOneAt localTime
  rw [hp]

theorem tilingVTwoAt_iff_of_pathPrefix_eq
    (t : DominoTiling) (window : Finset ℕ) {s s' : WalkPath} {n : ℕ}
    (hp : pathPrefix s n = pathPrefix s' n) (b : Point) :
    tilingVTwoAt t window s n b ↔ tilingVTwoAt t window s' n b := by
  unfold tilingVTwoAt localTime
  rw [hp]

theorem tilingVThreeAt_iff_of_pathPrefix_eq
    (t : DominoTiling) (m low : ℕ) {s s' : WalkPath} {n : ℕ}
    (hp : pathPrefix s n = pathPrefix s' n) (b : Point) :
    tilingVThreeAt t m low s n b ↔ tilingVThreeAt t m low s' n b := by
  unfold tilingVThreeAt localTime
  rw [hp]

theorem tilingVOneBases_eq_of_pathPrefix_eq
    (t : DominoTiling) (m : ℕ) {s s' : WalkPath} {n : ℕ}
    (hp : pathPrefix s n = pathPrefix s' n) :
    tilingVOneBases t m s n = tilingVOneBases t m s' n := by
  classical
  unfold tilingVOneBases visitedTilingBases visitedSites tilingVOneAt localTime
  rw [hp]

theorem tilingVTwoBases_eq_of_pathPrefix_eq
    (t : DominoTiling) (window : Finset ℕ) {s s' : WalkPath} {n : ℕ}
    (hp : pathPrefix s n = pathPrefix s' n) :
    tilingVTwoBases t window s n = tilingVTwoBases t window s' n := by
  classical
  unfold tilingVTwoBases visitedTilingBases visitedSites tilingVTwoAt localTime
  rw [hp]

theorem tilingThetaBases_eq_of_pathPrefix_eq
    (t : DominoTiling) (m w externalLow externalHigh : ℕ)
    {s s' : WalkPath} {n : ℕ}
    (hp : pathPrefix s n = pathPrefix s' n) :
    tilingThetaBases t m w externalLow externalHigh s n =
      tilingThetaBases t m w externalLow externalHigh s' n := by
  classical
  unfold tilingThetaBases visitedTilingBases visitedSites
    tilingExternalBaseLocalTime localTime
  rw [hp]

theorem tilingDEtaAt_iff_of_pathPrefix_eq
    (t : DominoTiling) (m k w low : ℕ) {s s' : WalkPath} {n : ℕ}
    (hp : pathPrefix s n = pathPrefix s' n) :
    tilingDEtaAt t m k w low s n ↔ tilingDEtaAt t m k w low s' n := by
  have hsn : s n = s' n := congrFun hp ⟨n, Nat.lt_succ_self n⟩
  unfold tilingDEtaAt tilingVOneBases visitedTilingBases visitedSites
    tilingVOneAt tilingVTwoAt tilingVThreeAt localTime
  rw [hp, hsn]

end

end Erdos1165.HLOZTypedStoppedCandidateObservability
