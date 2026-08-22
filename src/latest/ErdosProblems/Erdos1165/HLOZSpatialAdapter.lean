/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/

import ErdosProblems.Erdos1165.HLOZPathEvents
import ErdosProblems.Erdos1165.PrefixConditionalLaw
import ErdosProblems.Erdos1165.SpatialInsertionClosedFiber

/-!
# Spatial insertion adapter for the HLOZ path transitions

`SpatialInsertionClosedFiber` proves the exact finite conditional product law
after the external retained word, the level condition, and a cap on every
insertion coordinate have been fixed.  `HLOZPathEvents` supplies the concrete
unbounded first, second, and screened-third transition events.

This file records both ends of the interface and isolates the only bridges
between them which are not finite calculations: disintegration of the stopped
past of the canonical walk into the closed insertion fibres, followed by
removal of the coordinate cap.  The second and third bridges are stated only
on explicit disjoint threshold-creation atoms.  In particular, none of the
exact finite negative-binomial or product laws is repeated as a hypothesis.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos1165
namespace HLOZSpatialAdapter

open HLOZPathEvents
open LazyDecomposition PathInsertion SpatialInsertionFiber

/- The literal even-prefix and shifted-prefix cutoff equivalences and product
laws are part of this adapter's public finite-fibre interface.  They include
the odd terminal singleton and the shifted time-zero atom. -/
export PrefixLevelTruncation
  (even_actualEndpointsBelow_iff_dominoTruncation
    shifted_actualEndpointsBelow_iff_dominoTruncation)

export PrefixConditionalLaw
  (EvenPrefixDominoTotals ShiftedPrefixDominoTotals
    evenPrefixTotals_conditional_factorization
    shiftedPrefixTotals_conditional_factorization)

/-! ## The checked finite-fibre input -/

/-- The normalized conditional point mass on a closed, capped insertion fibre.

This abbreviation is kept in the adapter so that a later stopped-time
disintegration theorem can state its cylinder weights without unfolding the
combinatorial construction of the fibre. -/
noncomputable abbrev closedFiberPointMass
    {o : Orientation} {i : ℕ}
    (x : Point) (r : Fin i → RetainedBlock o) (m cap : ℕ)
    (D : Finset Point) (a : RetainedBlock o)
    (q : CappedCoordinates i cap) : ℝ :=
  closedCappedDensity x r m cap D a q

/-- All finite probability input needed by the spatial screen is already
proved: after closing the terminal gap, the actual cylinder density is the
product of the normalized spatial-domino densities. -/
theorem closedFiberPointMass_factorization
    {o : Orientation} {i : ℕ}
    (x : Point) (r : Fin i → RetainedBlock o) (m cap : ℕ)
    (D : Finset Point) (a : RetainedBlock o)
    (q : CappedCoordinates i cap) :
    closedFiberPointMass x r m cap D a q =
      ∏ b : ExternalDomino x r,
        cappedDominoDensity x r m cap D b
          ((groupByDominoEquiv x r _ q) b) := by
  exact closedCappedDensity_factorization x r m cap D a q

/-- On a non-distinguished domino the marginal in the preceding product is
the normalized, endpoint-truncated HLOZ negative-binomial law.  This is the
point-mass form convenient for a path-to-fibre disintegration. -/
theorem awayDominoTotal_pointMass
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m : ℕ) (D : Finset Point)
    (b : AwayDomino x r D) (ℓ : ℕ)
    (hℓ : ℓ < m - fixedExternalDominoMax x r b.1) :
    fixedExternalJointMass (dominoExternalMultiplicity x r b.1) ℓ /
        (∑ j ∈ Finset.range (m - fixedExternalDominoMax x r b.1),
          fixedExternalJointMass (dominoExternalMultiplicity x r b.1) j) =
      truncatedDominoMass x r m b.1 ℓ := by
  exact dominoTotal_truncatedConditionalMass x r m b.1 ℓ hℓ

/-! ## The actual stopped-past atoms -/

/-- A threshold-creation time for a fixed rank is unique. -/
theorem thresholdCreation_time_unique {s : WalkPath} {m k n n' : ℕ}
    (h : ThresholdCreation s m k n) (h' : ThresholdCreation s m k n') :
    n = n' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (Nat.not_lt_of_ge h.1) (h'.2 n hlt)
  · exact (Nat.not_lt_of_ge h'.1) (h.2 n' hgt)

abbrev PairCreationIndex := ℕ × ℕ

abbrev TripleCreationIndex := (ℕ × ℕ) × ℕ

/-- The stopped-past atom fixing the first threshold-creation time. -/
def firstCreationAtom (m n : ℕ) : Set WalkPath :=
  thresholdCreationSet m 1 n

/-- A measurable stopped-past atom fixing the first two creation times. -/
def pairCreationAtom (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (z : PairCreationIndex) : Set WalkPath :=
  pairConfiguration t m a.1.1 z.1 z.2

/-- A measurable stopped-past atom fixing the first three creation times. -/
def tripleCreationAtom (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (z : TripleCreationIndex) : Set WalkPath :=
  tripleConfiguration t m a.1.1 a.1.2 z.1.1 z.1.2 z.2

theorem measurableSet_firstCreationAtom (m n : ℕ) :
    MeasurableSet (firstCreationAtom m n) :=
  measurableSet_thresholdCreationSet m 1 n

theorem measurableSet_pairCreationAtom (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) (z : PairCreationIndex) :
    MeasurableSet (pairCreationAtom t m a z) :=
  measurableSet_pairConfiguration t m a.1.1 z.1 z.2

theorem measurableSet_tripleCreationAtom (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) (z : TripleCreationIndex) :
    MeasurableSet (tripleCreationAtom t m a z) :=
  measurableSet_tripleConfiguration t m a.1.1 a.1.2 z.1.1 z.1.2 z.2

theorem firstCreationAtom_pairwiseDisjoint (m : ℕ) :
    Pairwise fun n n' : ℕ ↦
      Disjoint (firstCreationAtom m n) (firstCreationAtom m n') := by
  intro n n' hnn'
  rw [Set.disjoint_left]
  intro s hsn hsn'
  exact hnn' (thresholdCreation_time_unique hsn hsn')

theorem pairCreationAtom_pairwiseDisjoint (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) :
    Pairwise fun z w : PairCreationIndex ↦
      Disjoint (pairCreationAtom t m a z) (pairCreationAtom t m a w) := by
  intro z w hzw
  rw [Set.disjoint_left]
  intro s hsz hsw
  apply hzw
  apply Prod.ext
  · exact thresholdCreation_time_unique hsz.1 hsw.1
  · exact thresholdCreation_time_unique hsz.2.1 hsw.2.1

theorem tripleCreationAtom_pairwiseDisjoint (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) :
    Pairwise fun z w : TripleCreationIndex ↦
      Disjoint (tripleCreationAtom t m a z) (tripleCreationAtom t m a w) := by
  intro z w hzw
  rw [Set.disjoint_left]
  intro s hsz hsw
  apply hzw
  apply Prod.ext
  · apply Prod.ext
    · exact thresholdCreation_time_unique hsz.1 hsw.1
    · exact thresholdCreation_time_unique hsz.2.1 hsw.2.1
  · exact thresholdCreation_time_unique hsz.2.2.1 hsw.2.2.1

theorem iUnion_pairCreationAtom (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) :
    (⋃ z : PairCreationIndex, pairCreationAtom t m a z) =
      firstTransitionEvent t m a := by
  ext s
  simp only [pairCreationAtom, firstTransitionEvent, Set.mem_iUnion]
  constructor
  · rintro ⟨⟨n₁, n₂⟩, h⟩
    exact ⟨n₁, n₂, h⟩
  · rintro ⟨n₁, n₂, h⟩
    exact ⟨(n₁, n₂), h⟩

theorem iUnion_tripleCreationAtom (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) :
    (⋃ z : TripleCreationIndex, tripleCreationAtom t m a z) =
      secondTransitionEvent t m a := by
  ext s
  simp only [tripleCreationAtom, secondTransitionEvent, Set.mem_iUnion]
  constructor
  · rintro ⟨⟨⟨n₁, n₂⟩, n₃⟩, h⟩
    exact ⟨n₁, n₂, n₃, h⟩
  · rintro ⟨n₁, n₂, n₃, h⟩
    exact ⟨((n₁, n₂), n₃), h⟩

theorem firstTransitionEvent_subset_iUnion_firstCreationAtom
    (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) :
    firstTransitionEvent t m a ⊆ ⋃ n, firstCreationAtom m n := by
  intro s hs
  simp only [firstTransitionEvent, Set.mem_iUnion] at hs
  obtain ⟨n₁, n₂, hs⟩ := hs
  rw [Set.mem_iUnion]
  exact ⟨n₁, hs.1⟩

/-! ## Atomwise conditional domination -/

/-- Conditional domination only on the explicit stopped-past atoms.  Unlike
quantification over every measurable subset of a stage, this is compatible
with a transition cost strictly smaller than one. -/
abbrev PathTransitionDomination {ι : Type*} (piece : ι → Set WalkPath)
    (next : Set WalkPath) (q : ℝ≥0∞) : Prop :=
  ∀ z, simpleRandomWalk (piece z ∩ next) ≤ q * simpleRandomWalk (piece z)

/-- A finite-fibre screen on each explicit stopped-past atom.  The event
`screened z` can be larger than the transition event, but its probability is
measured only under the restriction to `piece z`.  Accordingly its coverage
condition is local: only `piece z ∩ next`, rather than all of `next`, must lie
in the screen.  Thus `bound` is exactly the genuine disintegration/cap-removal
seam left after the finite product law. -/
def AtomwiseRestrictedRealScreen {ι : Type*}
    (piece : ι → Set WalkPath) (next : Set WalkPath) (q : ℝ≥0∞) : Prop :=
  ∃ screened : ι → Set WalkPath,
    (∀ z, MeasurableSet (screened z)) ∧
    (∀ z, piece z ∩ next ⊆ screened z) ∧
    ∀ z, (simpleRandomWalk.restrict (piece z)).real (screened z) ≤
      (q * simpleRandomWalk (piece z)).toReal

/-- Sum atomwise transition bounds over a countable disjoint stopped-past
partition of the preceding stage. -/
theorem measure_next_le_of_atomwiseTransition
    {ι : Type*} [Countable ι] (piece : ι → Set WalkPath)
    {stage next : Set WalkPath} {q : ℝ≥0∞}
    (hmeas : ∀ z, MeasurableSet (piece z))
    (hdis : Pairwise fun z w ↦ Disjoint (piece z) (piece w))
    (hstage : (⋃ z, piece z) = stage) (hnext : next ⊆ stage)
    (hlocal : PathTransitionDomination piece next q) :
    simpleRandomWalk next ≤ q * simpleRandomWalk stage := by
  calc
    simpleRandomWalk next = simpleRandomWalk (stage ∩ next) := by
      rw [inter_eq_right.mpr hnext]
    _ = simpleRandomWalk ((⋃ z, piece z) ∩ next) := by rw [hstage]
    _ = simpleRandomWalk (⋃ z, piece z ∩ next) := by rw [iUnion_inter]
    _ ≤ ∑' z, simpleRandomWalk (piece z ∩ next) := measure_iUnion_le _
    _ ≤ ∑' z, q * simpleRandomWalk (piece z) :=
      ENNReal.tsum_le_tsum hlocal
    _ = q * ∑' z, simpleRandomWalk (piece z) := ENNReal.tsum_mul_left
    _ = q * simpleRandomWalk stage := by
      rw [← measure_iUnion hdis hmeas, hstage]

/-- Convert restricted-real shell screens on the explicit atoms into the
atomwise ENNReal domination consumed above.  The restricted screen is exactly
where the checked `hspatialBalance` and `hspatialGrowth` estimates are used;
the remaining input is the stopped-past disintegration/cap-removal identity. -/
theorem pathTransitionDomination_of_atomwiseRestrictedRealScreen
    {ι : Type*} (piece : ι → Set WalkPath) {next : Set WalkPath}
    {q : ℝ≥0∞} (hnextMeas : MeasurableSet next) (hq : q ≠ ∞)
    (hspatialScreen : AtomwiseRestrictedRealScreen piece next q) :
    PathTransitionDomination piece next q := by
  obtain ⟨screened, hscreenedMeas, hnext, hscreen⟩ := hspatialScreen
  intro z
  have hrestricted :
      (simpleRandomWalk.restrict (piece z)).real next ≤
        (simpleRandomWalk.restrict (piece z)).real (screened z) := by
    apply ENNReal.toReal_mono (by finiteness)
    rw [Measure.restrict_apply hnextMeas,
      Measure.restrict_apply (hscreenedMeas z)]
    apply measure_mono
    intro omega homega
    exact ⟨hnext z ⟨homega.2, homega.1⟩, homega.2⟩
  apply (ENNReal.toReal_le_toReal (by finiteness)
    (ENNReal.mul_ne_top hq (by finiteness))).1
  calc
    (simpleRandomWalk (piece z ∩ next)).toReal =
        (simpleRandomWalk.restrict (piece z)).real next := by
      change (simpleRandomWalk (piece z ∩ next)).toReal =
        ((simpleRandomWalk.restrict (piece z)) next).toReal
      rw [Measure.restrict_apply hnextMeas, inter_comm]
    _ ≤ (simpleRandomWalk.restrict (piece z)).real (screened z) := hrestricted
    _ ≤ (q * simpleRandomWalk (piece z)).toReal := hscreen z

/-- Sum first-transition screens over the first-creation atoms.  The union of
these atoms need not be all paths; its probability is at most one. -/
theorem firstTransition_measure_le
    {t : DominoTiling} {m : ℕ}
    {a : (GapScale × GapScale) × GapScale} {q : ℝ≥0∞}
    (h : PathTransitionDomination (firstCreationAtom m)
      (firstTransitionEvent t m a) q) :
    simpleRandomWalk (firstTransitionEvent t m a) ≤ q := by
  calc
    simpleRandomWalk (firstTransitionEvent t m a) ≤
        q * simpleRandomWalk (⋃ n, firstCreationAtom m n) :=
      measure_next_le_of_atomwiseTransition (firstCreationAtom m)
        (measurableSet_firstCreationAtom m)
        (firstCreationAtom_pairwiseDisjoint m) rfl
        (firstTransitionEvent_subset_iUnion_firstCreationAtom t m a) h
    _ ≤ q * 1 := by
      have hunion : simpleRandomWalk (⋃ n, firstCreationAtom m n) ≤ 1 := by
        have h := measure_mono (μ := simpleRandomWalk)
          (subset_univ (⋃ n, firstCreationAtom m n))
        simpa using h
      simpa only [mul_comm] using (mul_le_mul_left hunion q)
    _ = q := mul_one q

/-- Summation of the second-transition bounds over the pair-creation atoms. -/
theorem secondTransition_measure_le
    {t : DominoTiling} {m : ℕ}
    {a : (GapScale × GapScale) × GapScale} {q : ℝ≥0∞}
    (h : PathTransitionDomination (pairCreationAtom t m a)
      (secondTransitionEvent t m a) q) :
    simpleRandomWalk (secondTransitionEvent t m a) ≤
      q * simpleRandomWalk (firstTransitionEvent t m a) := by
  exact measure_next_le_of_atomwiseTransition (pairCreationAtom t m a)
    (measurableSet_pairCreationAtom t m a)
    (pairCreationAtom_pairwiseDisjoint t m a)
    (iUnion_pairCreationAtom t m a)
    (secondTransitionEvent_subset_first t m a) h

/-- Summation of screened-third bounds over the triple-creation atoms. -/
theorem screenedThirdTransition_measure_le
    {t : DominoTiling} {m : ℕ}
    {a : (GapScale × GapScale) × GapScale} {q : ℝ≥0∞}
    (h : PathTransitionDomination (tripleCreationAtom t m a)
      (screenedThirdTransitionEvent t m a) q) :
    simpleRandomWalk (screenedThirdTransitionEvent t m a) ≤
      q * simpleRandomWalk (secondTransitionEvent t m a) := by
  exact measure_next_le_of_atomwiseTransition (tripleCreationAtom t m a)
    (measurableSet_tripleCreationAtom t m a)
    (tripleCreationAtom_pairwiseDisjoint t m a)
    (iUnion_tripleCreationAtom t m a)
    (sdiff_subset.trans (thirdTransitionEvent_subset_second t m a)) h

/-! ## One named stopped-past input for the three concrete transitions -/

/-- Restricted-real finite-fibre screens localized at the first
threshold-creation time. -/
abbrev FirstStoppedPastSpatialDisintegration (K : ℝ≥0) : Prop :=
  (∀ (t : DominoTiling) (m : ℕ)
      (a : (GapScale × GapScale) × GapScale),
    AtomwiseRestrictedRealScreen (firstCreationAtom m)
      (firstTransitionEvent t m a) (UpperCanonical.hlozTransitionCost K m))

/-- Atomwise stopped-past disintegration for the second transition, localized
at the two threshold-creation times. -/
abbrev SecondStoppedPastSpatialDisintegration (K : ℝ≥0) : Prop :=
  (∀ (t : DominoTiling) (m : ℕ)
      (a : (GapScale × GapScale) × GapScale),
    AtomwiseRestrictedRealScreen (pairCreationAtom t m a)
      (secondTransitionEvent t m a) (UpperCanonical.hlozTransitionCost K m))

/-- Atomwise stopped-past disintegration for the screened third transition,
localized at the three threshold-creation times. -/
abbrev ThirdStoppedPastSpatialDisintegration (K : ℝ≥0) : Prop :=
  (∀ (t : DominoTiling) (m : ℕ)
      (a : (GapScale × GapScale) × GapScale),
    AtomwiseRestrictedRealScreen (tripleCreationAtom t m a)
      (screenedThirdTransitionEvent t m a)
      (UpperCanonical.hlozTransitionCost K m))

set_option linter.constructorNameAsVariable false in
/-- Direct adapter into the recurrence-backed HLOZ upper endgame.  After the
checked finite spatial insertion law, the only probabilistic premises here
are the stopped-past disintegration and summability of the already isolated
exceptional family. -/
theorem simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_spatialDisintegration
    (K : ℝ≥0)
    (hfirstSpatial : FirstStoppedPastSpatialDisintegration K)
    (hsecondSpatial : SecondStoppedPastSpatialDisintegration K)
    (hthirdSpatial : ThirdStoppedPastSpatialDisintegration K)
    (hexception : ∀ t,
      ∑' m, simpleRandomWalk (hlozExceptionalEvent t m) ≠ ∞) :
    ∀ᵐ s ∂simpleRandomWalk, ∀ᶠ n in Filter.atTop,
      favoriteCount s n ≤ 3 := by
  apply
    simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_path_transition_estimates
      K
  · intro t m a ha
    apply firstTransition_measure_le
    exact pathTransitionDomination_of_atomwiseRestrictedRealScreen
      (firstCreationAtom m) (measurableSet_firstTransitionEvent t m a)
      (by
        rw [UpperCanonical.hlozTransitionCost,
          UpperAssembly.pSeriesWeight]
        exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)
      (hfirstSpatial t m a)
  · intro t m a ha
    apply secondTransition_measure_le
    exact pathTransitionDomination_of_atomwiseRestrictedRealScreen
      (pairCreationAtom t m a) (measurableSet_secondTransitionEvent t m a)
      (by
        rw [UpperCanonical.hlozTransitionCost,
          UpperAssembly.pSeriesWeight]
        exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)
      (hsecondSpatial t m a)
  · intro t m a ha
    apply screenedThirdTransition_measure_le
    exact pathTransitionDomination_of_atomwiseRestrictedRealScreen
      (tripleCreationAtom t m a)
      (measurableSet_screenedThirdTransitionEvent t m a)
      (by
        rw [UpperCanonical.hlozTransitionCost,
          UpperAssembly.pSeriesWeight]
        exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)
      (hthirdSpatial t m a)
  · exact hexception

end HLOZSpatialAdapter
end Erdos1165
