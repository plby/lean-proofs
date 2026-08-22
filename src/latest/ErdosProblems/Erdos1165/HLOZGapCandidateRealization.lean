import ErdosProblems.Erdos1165.HLOZGapFixedPair
import ErdosProblems.Erdos1165.HLOZProposition48Candidates
import ErdosProblems.Erdos1165.PreStoppingSpatialLaw

/-!
# Realizing failed gap pairs inside the stopped Proposition 4.8 candidates

This file is the deterministic path seam between a literal failed successive
favorite-creation pair and the concrete candidate family used by the HLOZ
Proposition 4.8 screen.  The only quantitative inputs retained in the final
theorem are the cap on the deleted (lazy) local time and the upper endpoint of
the displayed deficit band.
-/

namespace Erdos1165.HLOZGapCandidateRealization

open LazyDecomposition
open HLOZGapFixedPair HLOZPathEvents HLOZProposition48Candidates
open NearFavoriteShells ScreeningInstantiation
open PreStoppingSpatialLaw

noncomputable section

/-! ## The oriented local-time identity -/

/-- The fixed boundary contribution omitted by the oriented external path.
It is zero for the even decomposition and is the time-zero atom for the
shifted decomposition. -/
def orientedBoundaryLocalTime : Orientation → WalkPath → Point → ℕ
  | .even, _, _ => 0
  | .shifted, s, x => if s 0 = x then 1 else 0

/-- Local time carried by excursions deleted in the chosen orientation. -/
def orientedLazyLocalTime : Orientation → WalkPath → ℕ → Point → ℕ
  | .even, s, n, x => lazyLocalTime .even s n x
  | .shifted, s, n, x => shiftedLazyLocalTimeAt s n x

/-- Actual local time is the sum of the fixed boundary atom, oriented
external local time, and oriented lazy local time. -/
theorem localTime_eq_orientedBoundary_add_external_add_lazy
    (o : Orientation) (s : WalkPath) (n : ℕ) (x : Point) :
    localTime s n x =
      orientedBoundaryLocalTime o s x +
        ExternalThickCount.orientedExternalLocalTime o s n x +
          orientedLazyLocalTime o s n x := by
  cases o with
  | even =>
      simpa [orientedBoundaryLocalTime, orientedLazyLocalTime,
        ExternalThickCount.orientedExternalLocalTime, externalLocalTime,
        finiteExternalLocalTime] using
        localTime_split .even s n x
  | shifted =>
      simpa [orientedBoundaryLocalTime, orientedLazyLocalTime,
        ExternalThickCount.orientedExternalLocalTime, shiftedExternalLocalTimeAt,
        shiftedExternalLocalTime, add_assoc] using
        shiftedLocalTime_split s n x

/-- Subtraction form of the same identity. -/
theorem orientedExternalLocalTime_eq_sub
    (o : Orientation) (s : WalkPath) (n : ℕ) (x : Point) :
    ExternalThickCount.orientedExternalLocalTime o s n x =
      localTime s n x - orientedBoundaryLocalTime o s x -
        orientedLazyLocalTime o s n x := by
  have h := localTime_eq_orientedBoundary_add_external_add_lazy o s n x
  omega

/-- If the fixed boundary plus lazy contribution is capped by `lazyCap`, an
actual-local-time lower bound transports to the oriented external local
time. -/
theorem externalThreshold_le_orientedExternalLocalTime_of_lazyCap
    {o : Orientation} {s : WalkPath} {n : ℕ} {x : Point}
    {externalThreshold lazyCap : ℕ}
    (hlazy : orientedBoundaryLocalTime o s x +
        orientedLazyLocalTime o s n x ≤ lazyCap)
    (hactual : externalThreshold + lazyCap ≤ localTime s n x) :
    externalThreshold ≤
      ExternalThickCount.orientedExternalLocalTime o s n x := by
  have hsplit := localTime_eq_orientedBoundary_add_external_add_lazy o s n x
  omega

theorem orientationCompatible_iff_orientationClass
    (o : Orientation) (x : Point) :
    SpatialInsertionFiber.OrientationCompatible o x ↔
      ExternalThickCount.orientationClass o x := by
  cases o <;> rfl

/-- Positive external local time puts a compatible site in the selected
oriented external range. -/
theorem mem_orientedExternalVisitedSites_of_localTime_pos
    {o : Orientation} {s : WalkPath} {n : ℕ} {x : Point}
    (hx : SpatialInsertionFiber.OrientationCompatible o x)
    (hpos : 0 < ExternalThickCount.orientedExternalLocalTime o s n x) :
    x ∈ ExternalThickCount.orientedExternalVisitedSites o s n := by
  classical
  rw [ExternalThickCount.orientedExternalVisitedSites, Finset.mem_filter]
  refine ⟨?_, (orientationCompatible_iff_orientationClass o x).mp hx⟩
  rw [List.mem_toFinset]
  exact List.count_pos_iff.mp hpos

/-! ## Membership in the concrete candidate band -/

/-- Introduction rule exposing exactly the four fields of the literal
stopped Proposition 4.8 candidate definition. -/
theorem mem_stoppedCandidateSites48_of_external
    {o : Orientation} {n externalThreshold m : ℕ} {beta : ℝ}
    {distinguished : WalkPath → Finset Point}
    {totalLocalTime : WalkPath → Point → ℕ} {s : WalkPath} {x : Point}
    (hvisited : x ∈ ExternalThickCount.orientedExternalVisitedSites o s n)
    (hexternal : externalThreshold ≤
      ExternalThickCount.orientedExternalLocalTime o s n x)
    (hdistinguished : x ∉ distinguished s)
    (hband : (m - totalLocalTime s x) / shellWidth48 m < shellCount48 m beta) :
    x ∈ stoppedCandidateSites48 o n externalThreshold distinguished
      totalLocalTime m beta s := by
  rw [stoppedCandidateSites48, mem_boundedCandidates]
  refine ⟨?_, hband⟩
  simp only [externalThickCandidates, Finset.mem_filter]
  exact ⟨hvisited, hexternal, hdistinguished⟩

/-- The shell-label bound and its scale inequality imply the actual-local-time
lower bound needed by the preceding lazy-cap transport. -/
theorem external_add_lazyCap_le_localTime_of_deficitBand
    {m actual externalThreshold lazyCap width shellCount : ℕ}
    (hwidth : 0 < width)
    (hband : (m - actual) / width < shellCount)
    (hscale : externalThreshold + lazyCap + width * shellCount ≤ m + 1) :
    externalThreshold + lazyCap ≤ actual := by
  have hdeficit : m - actual < shellCount * width :=
    (Nat.div_lt_iff_lt_mul hwidth).mp hband
  have hmul : width * shellCount = shellCount * width := Nat.mul_comm _ _
  by_cases hle : actual ≤ m
  · have hadd : m - actual + actual = m := Nat.sub_add_cancel hle
    omega
  · have hlarge : m + 1 ≤ actual := by omega
    have hsmall : externalThreshold + lazyCap ≤ m + 1 := by omega
    exact hsmall.trans hlarge

/-- A compatible point in a genuine deficit band belongs to the concrete
candidate set as soon as its boundary-plus-lazy contribution obeys the cap.
In particular, positive external thickness also supplies the external-range
membership; it is not a separate assumption. -/
theorem mem_stoppedCandidateSites48_of_lazyCap_and_deficitBand
    {o : Orientation} {n externalThreshold lazyCap m : ℕ} {beta : ℝ}
    {distinguished : WalkPath → Finset Point} {s : WalkPath} {x : Point}
    (hthreshold : 0 < externalThreshold)
    (hcompatible : SpatialInsertionFiber.OrientationCompatible o x)
    (hlazy : orientedBoundaryLocalTime o s x +
        orientedLazyLocalTime o s n x ≤ lazyCap)
    (hdistinguished : x ∉ distinguished s)
    (hwidth : 0 < shellWidth48 m)
    (hband : (m - localTime s n x) / shellWidth48 m < shellCount48 m beta)
    (hscale : externalThreshold + lazyCap +
        shellWidth48 m * shellCount48 m beta ≤ m + 1) :
    x ∈ stoppedCandidateSites48 o n externalThreshold distinguished
      (fun s y ↦ localTime s n y) m beta s := by
  have hactual : externalThreshold + lazyCap ≤ localTime s n x :=
    external_add_lazyCap_le_localTime_of_deficitBand hwidth hband hscale
  have hexternal : externalThreshold ≤
      ExternalThickCount.orientedExternalLocalTime o s n x :=
    externalThreshold_le_orientedExternalLocalTime_of_lazyCap hlazy hactual
  have hvisited : x ∈
      ExternalThickCount.orientedExternalVisitedSites o s n :=
    mem_orientedExternalVisitedSites_of_localTime_pos hcompatible
      (hthreshold.trans_le hexternal)
  exact mem_stoppedCandidateSites48_of_external
    hvisited hexternal hdistinguished hband

/-! ## The literal failed creation pair -/

/-- At the old creation time of a fixed pair, the threshold sites are exactly
the actual favorite sites.  The no-next-level datum is recorded at the later
terminal creation, but monotonicity transports it back to the old prefix. -/
theorem thresholdSites_eq_favoriteSites_at_oldTime_of_fixedPair
    {m oldRank newRank nOld nNew nTerminal returns : ℕ}
    {a : GapScale} {s : WalkPath} {x : Point}
    (holdRank : 0 < oldRank) (hnewRank : 0 < newRank)
    (hrank : oldRank < newRank)
    (hrealizes : FixedPairReturnRealizes
      m oldRank newRank nOld nNew nTerminal returns a s () x) :
    thresholdSites s nOld m = favoriteSites s nOld := by
  have htimes : nOld < nNew := creation_time_lt holdRank hnewRank hrank
    hrealizes.1.1 hrealizes.1.2.1
  have hOldTerminal : nOld ≤ nTerminal :=
    htimes.le.trans hrealizes.1.2.2.2.1
  have hmono := thresholdCount_mono_time s (m + 1) hOldTerminal
  have hnextOld : thresholdCount s nOld (m + 1) = 0 := by
    change thresholdCount s nOld (m + 1) ≤
      thresholdCount s nTerminal (m + 1) at hmono
    rw [hrealizes.1.2.2.1] at hmono
    omega
  have hbelow : ∀ y : Point, localTime s nOld y < m + 1 :=
    (thresholdCount_eq_zero_iff_forall_lt s nOld (m + 1)
      (Nat.zero_lt_succ m)).mp hnextOld
  exact thresholdSites_eq_favoriteSites_of_terminal s nOld m oldRank holdRank
    (thresholdCount_eq_of_creation holdRank hrealizes.1.1) hbelow

/-- Separation from every old level-`m` site excludes the new compatible
site from the actual distinguished favorite-domino bases at the old prefix. -/
theorem not_mem_favoriteDominoBases_of_fixedPair_separation
    {o : Orientation} {m oldRank newRank nOld nNew nTerminal returns : ℕ}
    {a : GapScale} {s : WalkPath} {x : Point}
    (holdRank : 0 < oldRank) (hnewRank : 0 < newRank)
    (hrank : oldRank < newRank)
    (hrealizes : FixedPairReturnRealizes
      m oldRank newRank nOld nNew nTerminal returns a s () x)
    (hcompatible : SpatialInsertionFiber.OrientationCompatible o x)
    (hseparated : ∀ y ∈ thresholdSites s nOld m,
      dominoBase o y ≠ dominoBase o x) :
    x ∉ favoriteDominoBases o s nOld := by
  intro hx
  obtain ⟨y, hyFavorite, hyBase⟩ :=
    (mem_favoriteDominoBases_iff o s nOld x).mp hx
  have holdSites := thresholdSites_eq_favoriteSites_at_oldTime_of_fixedPair
    holdRank hnewRank hrank hrealizes
  have hyThreshold : y ∈ thresholdSites s nOld m := by
    rw [holdSites]
    exact hyFavorite
  apply hseparated y hyThreshold
  rw [dominoBase_eq_self_of_compatible hcompatible]
  exact hyBase

/-- The literal failed pair realizes a concrete stopped Proposition 4.8
candidate at the old creation time.  Thus the past used by the subsequent
Strong Markov return argument is `nOld`, not `nNew`: the new site already has
large external local time at `nOld` after subtracting its capped lazy
contribution. -/
theorem fixedPairReturnRealizes_mem_stoppedCandidateSites48
    {o : Orientation} {m oldRank newRank nOld nNew nTerminal returns : ℕ}
    {a : GapScale} {s : WalkPath} {x : Point}
    {externalThreshold lazyCap : ℕ} {beta : ℝ}
    (holdRank : 0 < oldRank) (hnewRank : 0 < newRank)
    (hrank : oldRank < newRank)
    (hrealizes : FixedPairReturnRealizes
      m oldRank newRank nOld nNew nTerminal returns a s () x)
    (hthreshold : 0 < externalThreshold)
    (hcompatible : SpatialInsertionFiber.OrientationCompatible o x)
    (hlazy : orientedBoundaryLocalTime o s x +
        orientedLazyLocalTime o s nOld x ≤ lazyCap)
    (hseparated : ∀ y ∈ thresholdSites s nOld m,
      dominoBase o y ≠ dominoBase o x)
    (hwidth : 0 < shellWidth48 m)
    (hband : (m - localTime s nOld x) / shellWidth48 m < shellCount48 m beta)
    (hscale : externalThreshold + lazyCap +
        shellWidth48 m * shellCount48 m beta ≤ m + 1) :
    x ∈ stoppedCandidateSites48 o nOld externalThreshold
      (fun s ↦ favoriteDominoBases o s nOld)
      (fun s y ↦ localTime s nOld y) m beta s := by
  apply mem_stoppedCandidateSites48_of_lazyCap_and_deficitBand
    hthreshold hcompatible hlazy
  · exact not_mem_favoriteDominoBases_of_fixedPair_separation
      holdRank hnewRank hrank hrealizes hcompatible hseparated
  · exact hwidth
  · exact hband
  · exact hscale

end

end Erdos1165.HLOZGapCandidateRealization
