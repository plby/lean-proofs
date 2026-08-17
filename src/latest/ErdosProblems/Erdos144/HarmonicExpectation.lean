/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos144.HarmonicStateEquiv
import ErdosProblems.Erdos144.HarmonicStageRegularity

/-!
# The unconditional harmonic signed-energy expectation

This file joins the ten-state product equivalence to the largest-coordinate
reconstruction estimates.  Predecessors are partitioned into eight-adic
octaves.  Low octaves use the unrestricted fibre estimate; high octaves use
the regular diagonal-tail generating function.
-/

open scoped BigOperators

namespace Erdos144.HarmonicExpectation

noncomputable section

attribute [local instance] Classical.propDecidable

open HarmonicBlocks HarmonicOctaves HarmonicDecomposition
  HarmonicStateExpectation HarmonicStateEquiv

/-- The union of the first `R` eight-adic octaves is the whole interval
from depth `R` to the top. -/
theorem biUnion_octave_range (D R : ℕ) :
    (Finset.range R).biUnion (octave D) =
      Finset.Ioc (D / 8 ^ R) D := by
  induction R with
  | zero => simp [octave]
  | succ R ih =>
      rw [Finset.range_add_one, Finset.biUnion_insert, ih]
      ext n
      simp only [Finset.mem_union, Finset.mem_Ioc, octave]
      have hdiv : D / 8 ^ (R + 1) ≤ D / 8 ^ R :=
        Nat.div_le_div_left
          (Nat.pow_le_pow_right (by norm_num : 0 < 8) (by omega)) (by positivity)
      have htop : D / 8 ^ R ≤ D := Nat.div_le_self _ _
      omega

/-- Ambient predecessors whose natural values lie in one octave. -/
def predecessorsInOctave (I : Finset ℕ) (D r : ℕ) : Finset ↑I :=
  Finset.univ.filter fun M ↦ M.1 ∈ octave D r

@[simp] theorem mem_predecessorsInOctave
    {I : Finset ℕ} {D r : ℕ} (M : ↑I) :
    M ∈ predecessorsInOctave I D r ↔ M.1 ∈ octave D r := by
  simp [predecessorsInOctave]

theorem restrictedPredecessorFibreMass_true_eq
    {I : Finset ℕ} (M : ↑I) :
    restrictedPredecessorFibreMass M (fun _ ↦ True) =
      predecessorFibreMass M := by
  simp [restrictedPredecessorFibreMass, predecessorFibreMass]

/-- A low-octave restricted reconstruction event is bounded by the concrete
low contribution. -/
theorem low_reconstructedProfileMass_le
    {I : Finset ℕ} (hI : ∀ i ∈ I, 1 ≤ i) (D r : ℕ) :
    restrictedReconstructedProfileMass
        (predecessorsInOctave I D r) (fun _ ↦ True) ≤
      lowContribution D r := by
  calc
    restrictedReconstructedProfileMass
        (predecessorsInOctave I D r) (fun _ ↦ True) ≤
        ∑ M ∈ predecessorsInOctave I D r,
          restrictedPredecessorFibreMass M (fun _ ↦ True) :=
      restrictedReconstructedProfileMass_le_fibres hI _ _
    _ = ∑ M ∈ predecessorsInOctave I D r,
        predecessorFibreMass M := by
      apply Finset.sum_congr rfl
      intro M _
      exact restrictedPredecessorFibreMass_true_eq M
    _ ≤ lowContribution D r := by
      apply sum_predecessorFibreMass_octave_le hI
      intro M hM
      exact mem_predecessorsInOctave M |>.mp hM

/-- A high-octave restricted reconstruction event is bounded by the
corresponding concrete high contribution. -/
theorem high_reconstructedProfileMass_le
    {I : Finset ℕ} (hI : ∀ i ∈ I, 1 ≤ i)
    {D s k : ℕ} :
    restrictedReconstructedProfileMass
        (predecessorsInOctave I D (s + k))
        (TailRegularTemplate (Finset.Ioc (D / 8 ^ (s + k)) D)
          (2 * k - 1)) ≤
      highContribution D s k := by
  have hnotTail : ∀ M ∈ predecessorsInOctave I D (s + k),
      M.1 ∉ Finset.Ioc (D / 8 ^ (s + k)) D := by
    intro M hM hMT
    have hOct := Finset.mem_Ioc.mp (mem_predecessorsInOctave M |>.mp hM)
    have hTail := Finset.mem_Ioc.mp hMT
    exact (not_lt_of_ge hOct.2) hTail.1
  calc
    restrictedReconstructedProfileMass
        (predecessorsInOctave I D (s + k))
        (TailRegularTemplate (Finset.Ioc (D / 8 ^ (s + k)) D)
          (2 * k - 1)) ≤
        ∑ M ∈ predecessorsInOctave I D (s + k),
          2 * (1 / (9 : ℝ) ^ k) * (1 / (M.1 : ℝ) ^ 2) := by
      exact restrictedReconstructedProfileMass_tailRegular_le hI _ _ _
        hnotTail (by omega)
    _ = 2 * (1 / (9 : ℝ) ^ k) *
        (∑ M ∈ predecessorsInOctave I D (s + k),
          1 / (M.1 : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * (1 / (9 : ℝ) ^ k) *
        (∑ M ∈ octave D (s + k), 1 / (M : ℝ) ^ 2) := by
      gcongr
      apply sum_subtype_reciprocalSquare_le
      intro M hM
      exact mem_predecessorsInOctave M |>.mp hM
    _ = highContribution D s k := by
      unfold highContribution
      rw [zpow_neg, zpow_natCast]
      ring

/-- The normalized mass of balanced non-diagonal profiles with regular
natural-valued support. -/
def regularBalancedProfileMass (I : Finset ℕ) (D R s : ℕ) : ℝ :=
  ∑ Q : ↑I → EnergyState,
    if OctaveRegular D R s (profileSelectedNaturals Q) ∧
        profileSignedDifference I Q = 0 ∧ ProfileNonDiagonal Q then
      energyProfileWeight I Q else 0

/-- Low-octave indicator attached to one ambient profile. -/
def lowReconstructionIndicator (I : Finset ℕ) (D r : ℕ)
    (Q : ↑I → EnergyState) : ℝ :=
  if HasRestrictedPredecessorReconstruction
      (predecessorsInOctave I D r) (fun _ ↦ True) Q then
    energyProfileWeight I Q else 0

/-- High-octave indicator attached to one ambient profile. -/
def highReconstructionIndicator (I : Finset ℕ) (D s k : ℕ)
    (Q : ↑I → EnergyState) : ℝ :=
  if HasRestrictedPredecessorReconstruction
      (predecessorsInOctave I D (s + k))
      (TailRegularTemplate (Finset.Ioc (D / 8 ^ (s + k)) D)
        (2 * k - 1)) Q then
    energyProfileWeight I Q else 0

theorem lowReconstructionIndicator_nonneg
    {I : Finset ℕ} (hI : ∀ i ∈ I, 1 ≤ i) (D r : ℕ)
    (Q : ↑I → EnergyState) :
    0 ≤ lowReconstructionIndicator I D r Q := by
  unfold lowReconstructionIndicator
  split <;> simp [energyProfileWeight_nonneg hI]

theorem highReconstructionIndicator_nonneg
    {I : Finset ℕ} (hI : ∀ i ∈ I, 1 ≤ i) (D s k : ℕ)
    (Q : ↑I → EnergyState) :
    0 ≤ highReconstructionIndicator I D s k Q := by
  unfold highReconstructionIndicator
  split <;> simp [energyProfileWeight_nonneg hI]

/-- The canonical largest-coordinate reconstruction lies in the low event
as soon as its predecessor belongs to the prescribed family. -/
theorem hasRestrictedPredecessorReconstruction_true_of_balanced
    {I : Finset ℕ} (hI : ∀ i ∈ I, 1 ≤ i)
    {Q : ↑I → EnergyState} (hQ : ProfileNonDiagonal Q)
    (hbal : profileSignedDifference I Q = 0)
    (B : Finset ↑I)
    (hMB : largestProfilePredecessor hI Q hQ hbal ∈ B) :
    HasRestrictedPredecessorReconstruction B (fun _ ↦ True) Q := by
  let L := largestProfileUnequalCoordinate Q hQ
  let M := largestProfilePredecessor hI Q hQ hbal
  obtain ⟨xy, hQL, hxy⟩ := largestProfileUnequalCoordinate_spec hQ
  let E := eraseProfileCoordinate Q L
  refine ⟨M, hMB, E, xy, L, trivial, ?_, ?_, ?_, ?_⟩
  · have hML : M < L := largestProfilePredecessor_lt hI hQ hbal
    have hne : M ≠ L := ne_of_lt hML
    unfold Selects
    change eraseProfileCoordinate Q L M ≠ none
    rw [eraseProfileCoordinate_ne Q hne]
    simpa only [Selects] using largestProfilePredecessor_selects hI hQ hbal
  · simp [unequalStatePairs, hxy]
  · apply mem_forcedProfileCoordinates_of_fillHole_balanced
    · exact largestProfilePredecessor_lt hI hQ hbal
    · simp [E]
    · have hfill : fillHole E L xy = Q := by
        funext i
        by_cases hi : i = L
        · subst i
          simpa [E] using hQL.symm
        · simp [fillHole, E, eraseProfileCoordinate, hi]
      simpa [hfill] using hbal
  · funext i
    by_cases hi : i = L
    · subst i
      simpa [E] using hQL
    · simp [fillHole, E, eraseProfileCoordinate, hi]

/-- Pointwise union bound over low and high predecessor octaves. -/
theorem regularBalancedProfile_le_octaveIndicators
    {D R s : ℕ}
    (Q : ↑(Finset.Ioc (D / 8 ^ R) D) → EnergyState) :
    (if OctaveRegular D R s (profileSelectedNaturals Q) ∧
          profileSignedDifference (Finset.Ioc (D / 8 ^ R) D) Q = 0 ∧
          ProfileNonDiagonal Q then
        energyProfileWeight (Finset.Ioc (D / 8 ^ R) D) Q else 0) ≤
      (∑ r ∈ Finset.range s,
        lowReconstructionIndicator (Finset.Ioc (D / 8 ^ R) D) D r Q) +
      ∑ k ∈ Finset.range (R - s),
        highReconstructionIndicator (Finset.Ioc (D / 8 ^ R) D) D s k Q := by
  let I := Finset.Ioc (D / 8 ^ R) D
  have hI : ∀ i ∈ I, 1 ≤ i := by
    intro i hi
    exact Nat.succ_le_iff.mpr <|
      lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hi).1
  change (if OctaveRegular D R s (profileSelectedNaturals Q) ∧
      profileSignedDifference I Q = 0 ∧ ProfileNonDiagonal Q then
        energyProfileWeight I Q else 0) ≤ _
  by_cases hgood : OctaveRegular D R s (profileSelectedNaturals Q) ∧
      profileSignedDifference I Q = 0 ∧ ProfileNonDiagonal Q
  · rw [if_pos hgood]
    have hregular := hgood.1
    have hbal := hgood.2.1
    have hnon := hgood.2.2
    let M := largestProfilePredecessor hI Q hnon hbal
    have hMUnion : M.1 ∈ (Finset.range R).biUnion (octave D) := by
      rw [biUnion_octave_range]
      exact M.2
    obtain ⟨r, hrR, hMr⟩ := Finset.mem_biUnion.mp hMUnion
    have hrltR : r < R := Finset.mem_range.mp hrR
    by_cases hrs : r < s
    · have hMB : M ∈ predecessorsInOctave I D r := by
        exact mem_predecessorsInOctave M |>.mpr hMr
      have hevent : HasRestrictedPredecessorReconstruction
          (predecessorsInOctave I D r) (fun _ ↦ True) Q :=
        hasRestrictedPredecessorReconstruction_true_of_balanced
          hI hnon hbal _ hMB
      have hterm : lowReconstructionIndicator I D r Q =
          energyProfileWeight I Q := by
        simp [lowReconstructionIndicator, hevent]
      calc
        energyProfileWeight I Q = lowReconstructionIndicator I D r Q := hterm.symm
        _ ≤ ∑ r' ∈ Finset.range s,
            lowReconstructionIndicator I D r' Q := by
          apply Finset.single_le_sum (f := fun r' ↦
            lowReconstructionIndicator I D r' Q)
          · intro r' _
            exact lowReconstructionIndicator_nonneg hI D r' Q
          · exact Finset.mem_range.mpr hrs
        _ ≤ (∑ r' ∈ Finset.range s,
              lowReconstructionIndicator I D r' Q) +
            ∑ k ∈ Finset.range (R - s),
              highReconstructionIndicator I D s k Q := by
          exact le_add_of_nonneg_right <|
            Finset.sum_nonneg fun k _ ↦
              highReconstructionIndicator_nonneg hI D s k Q
    · have hsr : s ≤ r := Nat.le_of_not_gt hrs
      let k := r - s
      have hrEq : s + k = r := by simp [k, Nat.add_sub_of_le hsr]
      have hklt : k < R - s := by omega
      have hMB : M ∈ predecessorsInOctave I D r := by
        exact mem_predecessorsInOctave M |>.mpr hMr
      have hrIcc : r ∈ Finset.Icc s R :=
        Finset.mem_Icc.mpr ⟨hsr, hrltR.le⟩
      have hMupper : M.1 ≤ D / 8 ^ r := (Finset.mem_Ioc.mp hMr).2
      have hevent0 := hasRestrictedPredecessorReconstruction_tailRegular
        hI hnon hbal hregular hrIcc hMupper
        (predecessorsInOctave I D r) hMB
      have hevent : HasRestrictedPredecessorReconstruction
          (predecessorsInOctave I D (s + k))
          (TailRegularTemplate (Finset.Ioc (D / 8 ^ (s + k)) D)
            (2 * k - 1)) Q := by
        simpa only [hrEq, k] using hevent0
      have hterm : highReconstructionIndicator I D s k Q =
          energyProfileWeight I Q := by
        simp [highReconstructionIndicator, hevent]
      calc
        energyProfileWeight I Q = highReconstructionIndicator I D s k Q := hterm.symm
        _ ≤ ∑ k' ∈ Finset.range (R - s),
            highReconstructionIndicator I D s k' Q := by
          apply Finset.single_le_sum (f := fun k' ↦
            highReconstructionIndicator I D s k' Q)
          · intro k' _
            exact highReconstructionIndicator_nonneg hI D s k' Q
          · exact Finset.mem_range.mpr hklt
        _ ≤ (∑ r' ∈ Finset.range s,
              lowReconstructionIndicator I D r' Q) +
            ∑ k' ∈ Finset.range (R - s),
              highReconstructionIndicator I D s k' Q := by
          exact le_add_of_nonneg_left <|
            Finset.sum_nonneg fun r' _ ↦
              lowReconstructionIndicator_nonneg hI D r' Q
  · rw [if_neg hgood]
    exact add_nonneg
      (Finset.sum_nonneg fun r _ ↦
        lowReconstructionIndicator_nonneg hI D r Q)
      (Finset.sum_nonneg fun k _ ↦
        highReconstructionIndicator_nonneg hI D s k Q)

/-- The profile mass is bounded by the concrete low/high octave sum. -/
theorem regularBalancedProfileMass_le_concrete
    {D R s : ℕ} :
    regularBalancedProfileMass (Finset.Ioc (D / 8 ^ R) D) D R s ≤
      (∑ r ∈ Finset.range s, lowContribution D r) +
        ∑ k ∈ Finset.range (R - s), highContribution D s k := by
  let I := Finset.Ioc (D / 8 ^ R) D
  have hI : ∀ i ∈ I, 1 ≤ i := by
    intro i hi
    exact Nat.succ_le_iff.mpr <|
      lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hi).1
  calc
    regularBalancedProfileMass I D R s ≤
        ∑ Q : ↑I → EnergyState,
          ((∑ r ∈ Finset.range s, lowReconstructionIndicator I D r Q) +
            ∑ k ∈ Finset.range (R - s),
              highReconstructionIndicator I D s k Q) := by
      unfold regularBalancedProfileMass
      gcongr with Q
      exact regularBalancedProfile_le_octaveIndicators Q
    _ = (∑ r ∈ Finset.range s,
          restrictedReconstructedProfileMass
            (predecessorsInOctave I D r) (fun _ ↦ True)) +
        ∑ k ∈ Finset.range (R - s),
          restrictedReconstructedProfileMass
            (predecessorsInOctave I D (s + k))
            (TailRegularTemplate (Finset.Ioc (D / 8 ^ (s + k)) D)
              (2 * k - 1)) := by
      rw [Finset.sum_add_distrib]
      congr 1
      · conv_lhs => rw [Finset.sum_comm]
        rfl
      · conv_lhs => rw [Finset.sum_comm]
        rfl
    _ ≤ (∑ r ∈ Finset.range s, lowContribution D r) +
        ∑ k ∈ Finset.range (R - s), highContribution D s k := by
      apply add_le_add
      · gcongr with r hr
        exact low_reconstructedProfileMass_le hI D r
      · gcongr with k hk
        exact high_reconstructedProfileMass_le hI

/-- Numerical form of the complete ten-state profile estimate. -/
theorem regularBalancedProfileMass_le_1200
    {D R s : ℕ} (hD : 0 < D) :
    regularBalancedProfileMass (Finset.Ioc (D / 8 ^ R) D) D R s ≤
      1200 * (8 : ℝ) ^ s / D := by
  exact regularBalancedProfileMass_le_concrete.trans <|
    octave_contribution_sum_le s (R - s)
      (lowContribution D) (highContribution D s) hD
      (fun r hr ↦ lowContribution_le hD hr)
      (fun k hk ↦ highContribution_le hD hk)

theorem stageTop_div_eight_pow_stageDepth (s j : ℕ) :
    Harmonic.stageTop s j /
        8 ^ HarmonicStageRegularity.stageDepth s j =
      Harmonic.lowerScale s := by
  rw [HarmonicStageRegularity.stageTop_eq_pow_lowerExponent_add_depth]
  simp [pow_add, Harmonic.lowerScale]

/-- Explicit-stage version of the complete profile-mass estimate. -/
theorem stage_regularBalancedProfileMass_le_1200 (s j : ℕ) :
    regularBalancedProfileMass
        (Finset.Ioc (Harmonic.lowerScale s) (Harmonic.stageTop s j))
        (Harmonic.stageTop s j)
        (HarmonicStageRegularity.stageDepth s j) s ≤
      1200 * (8 : ℝ) ^ s / Harmonic.stageTop s j := by
  have hD : 0 < Harmonic.stageTop s j := by
    simp [Harmonic.stageTop]
  simpa only [stageTop_div_eight_pow_stageDepth] using
    (regularBalancedProfileMass_le_1200
      (D := Harmonic.stageTop s j)
      (R := HarmonicStageRegularity.stageDepth s j) (s := s) hD)

/-- Exact identification of the original harmonic energy with the ten-state
profile mass used by the largest-coordinate argument. -/
theorem normalizedOffDiagonalExpectation_eq_regularBalancedProfileMass
    (I : Finset ℕ) (D R s : ℕ) :
    normalizedOffDiagonalExpectation I (OctaveRegular D R s) =
      regularBalancedProfileMass I D R s := by
  simpa only [regularBalancedProfileMass,
    supportValues_eq_profileSelectedNaturals] using
    (normalizedOffDiagonalExpectation_eq_profile_sum I
      (OctaveRegular D R s))

/-- The unconditional normalized signed-energy estimate at every explicit
harmonic stage. -/
theorem stage_normalizedOffDiagonalExpectation_le_1200 (s j : ℕ) :
    normalizedOffDiagonalExpectation
        (Finset.Ioc (Harmonic.lowerScale s) (Harmonic.stageTop s j))
        (OctaveRegular (Harmonic.stageTop s j)
          (HarmonicStageRegularity.stageDepth s j) s) ≤
      1200 * (8 : ℝ) ^ s / Harmonic.stageTop s j := by
  rw [normalizedOffDiagonalExpectation_eq_regularBalancedProfileMass]
  exact stage_regularBalancedProfileMass_le_1200 s j

end

end Erdos144.HarmonicExpectation
