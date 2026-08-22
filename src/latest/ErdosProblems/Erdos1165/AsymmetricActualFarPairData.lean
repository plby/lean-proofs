/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.Proposition13LiteralAssembly
import ErdosProblems.Erdos1165.AppendixPairTerminalCertificate
import ErdosProblems.Erdos1165.AsymmetricPairTwoStageMass
import ErdosProblems.Erdos1165.AppendixPairCrossingTailLiteral

/-!
# Canonical terminal constructor for asymmetric far-pair data

This module fills every local terminal-kernel field of
`ActualMarkedFarPairData` from the checked canonical terminal analytic
certificate.  Its three global inputs retain the source-correct two-stage
shape: a literal marked stopped-data decomposition, an asymmetric radial
continuation comparison, and a retained one-point bound.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AsymmetricActualFarPairData

open AppendixLocalTime AppendixPair AppendixPairMoment
open AppendixFirstMoment
open AppendixPairTerminalCertificate MarkedTerminalDisintegration
open AppendixPairCrossingTail AppendixPairCrossingTailLiteral
open AsymmetricPairTwoStageMass
open ProfileConditionalTailUpper ProfileListExponent ProfileWeightUpper
open MarkedBoundaryVisitKernel
open PoissonKernelMarkedAlgebra PoissonKernelMarkedHarnack
open Proposition13Assembly Proposition13LiteralAssembly Proposition13Scales
open TerminalExcursionPathwise
open TerminalMarkedParameterBounds TerminalMarkedSkeletonDecomposition
open TerminalParameterBounds TerminalSkeletonWords

noncomputable section

/-- Uniform post-separation radial-tail witness.  Conditional on a retained
outside atom, the separation crossing count is already fixed, so A.16 uses
the uniform A.11 tail envelope, not an average over unrelated prefix atoms.
The coefficient is the accumulated A.6 row loss. -/
structure ProfileRadialTailCertificate
    (delta : ℝ) (n : ℕ) (x y : Point) : Type where
  coefficient : ℝ
  tailStart : profileUpperTailStart ≤
    pairPrefixScale (scaleIndex delta n)
      (separationLevel (scaleIndex delta n) x y)
  start_le_scale : pairPrefixScale (scaleIndex delta n)
      (separationLevel (scaleIndex delta n) x y) ≤ scaleIndex delta n
  cutoff : GaussianGeometricCutoff.geometricCutoff ≤
    pairPrefixScale (scaleIndex delta n)
      (separationLevel (scaleIndex delta n) x y)
  start_pos : 1 ≤ pairPrefixScale (scaleIndex delta n)
    (separationLevel (scaleIndex delta n) x y)
  coefficient_nonneg : 0 ≤ coefficient
  coefficient_le_exp_one : coefficient ≤ Real.exp 1

/-- At the padded separation-prefix scale, the only geometric input needed
to construct the radial certificate is the checked Gaussian cutoff.  The
upper relation to the terminal scale and positivity then follow directly
from the definition of `pairPrefixScale`. -/
def ProfileRadialTailCertificate.of_geometricCutoff
    {delta : ℝ} {n : ℕ} {x y : Point}
    (coefficient : ℝ) (hcoefficient0 : 0 ≤ coefficient)
    (hcoefficient : coefficient ≤ Real.exp 1)
    (hcutoff : GaussianGeometricCutoff.geometricCutoff ≤
      pairPrefixScale (scaleIndex delta n)
        (separationLevel (scaleIndex delta n) x y)) :
    ProfileRadialTailCertificate delta n x y where
  coefficient := coefficient
  tailStart := le_trans
    (show profileUpperTailStart ≤ GaussianGeometricCutoff.geometricCutoff by
      norm_num [profileUpperTailStart,
        GaussianGeometricCutoff.geometricCutoff,
        GaussianGeometricCutoff.geometricCutoffBase]) hcutoff
  start_le_scale := by
    unfold pairPrefixScale
    exact min_le_left _ _
  cutoff := hcutoff
  start_pos := le_trans
    (show 1 ≤ GaussianGeometricCutoff.geometricCutoff by
      norm_num [GaussianGeometricCutoff.geometricCutoff,
        GaussianGeometricCutoff.geometricCutoffBase]) hcutoff
  coefficient_nonneg := hcoefficient0
  coefficient_le_exp_one := hcoefficient

/-- Canonical certificate using the full checked `exp 1` A.6 row budget. -/
def ProfileRadialTailCertificate.expOne
    {delta : ℝ} {n : ℕ} {x y : Point}
    (hcutoff : GaussianGeometricCutoff.geometricCutoff ≤
      pairPrefixScale (scaleIndex delta n)
        (separationLevel (scaleIndex delta n) x y)) :
    ProfileRadialTailCertificate delta n x y :=
  .of_geometricCutoff (Real.exp 1) (Real.exp_nonneg _) le_rfl hcutoff

/-- The canonical radial-tail certificate exists uniformly for every far
pair at all sufficiently large selected scales. -/
theorem eventually_profileRadialTailCertificate_expOne
    {delta : ℝ} :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ x y : Point,
      separationLevel (scaleIndex delta n) x y ≤
          decorrelationCutoff (scaleIndex delta n) →
        Nonempty (ProfileRadialTailCertificate delta n x y) := by
  filter_upwards [eventually_geometricCutoff_le_pairPrefixScale]
      with n hcutoff
  intro x y hlevel
  refine ⟨ProfileRadialTailCertificate.expOne (hcutoff _ ?_)⟩
  exact Finset.mem_Icc.mpr
    ⟨Nat.one_le_iff_ne_zero.mpr (separationLevel_ne_zero _ _ _), hlevel⟩

/-- The uniform coefficient-bearing A.11 tail envelope represented by this
certificate. -/
def ProfileRadialTailCertificate.radialTail
    {delta : ℝ} {n : ℕ} {x y : Point}
    (certificate : ProfileRadialTailCertificate delta n x y) : ℝ :=
  certificate.coefficient *
    Real.exp (-(2 * (scaleIndex delta n -
      pairPrefixScale (scaleIndex delta n)
        (separationLevel (scaleIndex delta n) x y) : ℕ) : ℝ) +
      profileUpperConstant * (scaleIndex delta n : ℝ) ^ (3 / 5 : ℝ))

theorem ProfileRadialTailCertificate.radial_nonneg
    {delta : ℝ} {n : ℕ} {x y : Point}
    (certificate : ProfileRadialTailCertificate delta n x y) :
    0 ≤ certificate.radialTail :=
  mul_nonneg certificate.coefficient_nonneg (Real.exp_nonneg _)

/-- Every fixed admissible profile prefix has coefficient-bearing
continuation mass bounded by the certificate's uniform radial envelope.
This is the row-wise A.11 estimate used after the retained asymmetric atom
has fixed the separation crossing count. -/
theorem ProfileRadialTailCertificate.coefficient_mul_constrainedTail_le
    {delta : ℝ} {n : ℕ} {x y : Point}
    (certificate : ProfileRadialTailCertificate delta n x y)
    (pref : Profile
      (pairPrefixScale (scaleIndex delta n)
        (separationLevel (scaleIndex delta n) x y))) :
    certificate.coefficient *
        constrainedProfileTailWeight
          (scaleIndex delta n)
          (pairPrefixScale (scaleIndex delta n)
            (separationLevel (scaleIndex delta n) x y))
          ((show 2 ≤ profileUpperTailStart by
            norm_num [profileUpperTailStart]).trans certificate.tailStart)
          certificate.start_le_scale pref profileUpperDelta ≤
      certificate.radialTail := by
  unfold ProfileRadialTailCertificate.radialTail
  exact mul_le_mul_of_nonneg_left
    (constrainedProfileTailWeight_le_profileUpperEnvelope
      certificate.tailStart certificate.start_le_scale pref)
    certificate.coefficient_nonneg

/-- Before the padded cutoff, the radial certificate removes only the
strictly deeper continuation.  The exact transition mass from an earlier
retained profile prefix to the padded prefix remains as a multiplicative
factor; in particular, intermediate prefixes are not counted uniformly. -/
theorem ProfileRadialTailCertificate.coefficient_mul_tail_le_radial_mul_intermediate
    {delta : ℝ} {n : ℕ} {x y : Point}
    (certificate : ProfileRadialTailCertificate delta n x y)
    {start : ℕ} (hstart : 2 ≤ start)
    (hstartPrefix : start ≤ pairPrefixScale (scaleIndex delta n)
      (separationLevel (scaleIndex delta n) x y))
    (pref : Profile start) :
    certificate.coefficient *
        constrainedProfileTailWeight (scaleIndex delta n) start hstart
          (hstartPrefix.trans certificate.start_le_scale) pref
          profileUpperDelta ≤
      certificate.radialTail *
        constrainedProfileTailWeight
          (pairPrefixScale (scaleIndex delta n)
            (separationLevel (scaleIndex delta n) x y))
          start hstart hstartPrefix pref profileUpperDelta := by
  apply coefficient_mul_constrainedProfileTailWeight_le_intermediate
    hstart hstartPrefix certificate.start_le_scale pref profileUpperDelta
      certificate.coefficient certificate.radialTail
  intro midPref _hmidPref
  exact certificate.coefficient_mul_constrainedTail_le midPref

/-- ENNReal adapter for a literal compatible-word row.  Once the exact
word factorization bounds the real row mass by the coefficient times one
fixed-prefix continuation weight, the uniform radial certificate supplies
the precise `htailWeight` field of the two-stage constructor. -/
theorem ProfileRadialTailCertificate.ennreal_le_of_toReal_le_constrainedTail
    {delta : ℝ} {n : ℕ} {x y : Point}
    (certificate : ProfileRadialTailCertificate delta n x y)
    (pref : Profile
      (pairPrefixScale (scaleIndex delta n)
        (separationLevel (scaleIndex delta n) x y)))
    {mass : ℝ≥0∞} (hmass : mass ≠ ∞)
    (hle : mass.toReal ≤ certificate.coefficient *
      constrainedProfileTailWeight
        (scaleIndex delta n)
        (pairPrefixScale (scaleIndex delta n)
          (separationLevel (scaleIndex delta n) x y))
        ((show 2 ≤ profileUpperTailStart by
          norm_num [profileUpperTailStart]).trans certificate.tailStart)
        certificate.start_le_scale pref profileUpperDelta) :
    mass ≤ ENNReal.ofReal certificate.radialTail :=
  ennreal_le_of_toReal_le hmass certificate.radial_nonneg
    (hle.trans (certificate.coefficient_mul_constrainedTail_le pref))

/-- Row-sum form of
`ennreal_le_of_toReal_le_constrainedTail`, ready for the literal family of
compatible post-separation return words. -/
theorem ProfileRadialTailCertificate.tsum_le_of_toReal_le_constrainedTail
    {delta : ℝ} {n : ℕ} {x y : Point}
    (certificate : ProfileRadialTailCertificate delta n x y)
    {TailCode : Type*} (tailWeight : TailCode → ℝ≥0∞)
    (pref : Profile
      (pairPrefixScale (scaleIndex delta n)
        (separationLevel (scaleIndex delta n) x y)))
    (hfinite : (∑' t, tailWeight t) ≠ ∞)
    (hle : (∑' t, tailWeight t).toReal ≤ certificate.coefficient *
      constrainedProfileTailWeight
        (scaleIndex delta n)
        (pairPrefixScale (scaleIndex delta n)
          (separationLevel (scaleIndex delta n) x y))
        ((show 2 ≤ profileUpperTailStart by
          norm_num [profileUpperTailStart]).trans certificate.tailStart)
        certificate.start_le_scale pref profileUpperDelta) :
    ∑' t, tailWeight t ≤ ENNReal.ofReal certificate.radialTail :=
  certificate.ennreal_le_of_toReal_le_constrainedTail pref hfinite hle

/-- One concrete admissible continuation is a summand of the uniform
fixed-prefix tail. -/
theorem transitionSegmentProduct_le_constrainedProfileTailWeight
    {n start : ℕ} (hstart : 2 ≤ start) (hstartn : start ≤ n)
    {m : Profile n} {delta : ℝ}
    (hm : m ∈ constrainedProfiles n delta) :
    transitionSegmentProduct start (n - start) (profileAtScale m) ≤
      constrainedProfileTailWeight n start hstart hstartn
        (profilePrefix hstart hstartn m) delta := by
  unfold constrainedProfileTailWeight
  exact Finset.single_le_sum
    (s := (constrainedProfiles n delta).filter fun m' ↦
      profilePrefix hstart hstartn m' = profilePrefix hstart hstartn m)
    (f := fun m' ↦ transitionSegmentProduct start (n - start)
      (profileAtScale m'))
    (fun m' _hm' ↦
      transitionSegmentProduct_nonneg start (n - start) (profileAtScale m'))
    (Finset.mem_filter.mpr ⟨hm, rfl⟩)

/-- Walk-facing row adapter.  It is enough to compare a literal compatible
word row with the transition product of its actual full constrained
profile; membership in the fixed-prefix tail sum is proved internally. -/
theorem ProfileRadialTailCertificate.ennreal_le_of_fullProfileRow
    {delta : ℝ} {n : ℕ} {x y : Point}
    (certificate : ProfileRadialTailCertificate delta n x y)
    (m : Profile (scaleIndex delta n))
    (hm : m ∈ constrainedProfiles (scaleIndex delta n) profileUpperDelta)
    {mass : ℝ≥0∞} (hmass : mass ≠ ∞)
    (hle : mass.toReal ≤ certificate.coefficient *
      transitionSegmentProduct
        (pairPrefixScale (scaleIndex delta n)
          (separationLevel (scaleIndex delta n) x y))
        (scaleIndex delta n -
          pairPrefixScale (scaleIndex delta n)
            (separationLevel (scaleIndex delta n) x y))
        (profileAtScale m)) :
    mass ≤ ENNReal.ofReal certificate.radialTail := by
  let hstart : 2 ≤ pairPrefixScale (scaleIndex delta n)
      (separationLevel (scaleIndex delta n) x y) :=
    ((show 2 ≤ profileUpperTailStart by
      norm_num [profileUpperTailStart]).trans certificate.tailStart)
  apply certificate.ennreal_le_of_toReal_le_constrainedTail
    (profilePrefix hstart certificate.start_le_scale m) hmass
  exact hle.trans (mul_le_mul_of_nonneg_left
    (transitionSegmentProduct_le_constrainedProfileTailWeight
      hstart certificate.start_le_scale hm)
    certificate.coefficient_nonneg)

theorem ProfileRadialTailCertificate.le_pairEnvelope_div_prefix
    {delta : ℝ} {n : ℕ} {x y : Point}
    (certificate : ProfileRadialTailCertificate delta n x y) :
    certificate.radialTail ≤ pairPointEnvelope delta n /
      prefixProfileLower
        (pairPrefixScale (scaleIndex delta n)
          (separationLevel (scaleIndex delta n) x y)) := by
  have hcoefficient : certificate.coefficient ≤
      Real.exp (prefixProfileCost
        (pairPrefixScale (scaleIndex delta n)
          (separationLevel (scaleIndex delta n) x y)) +
        prefixProfileCostDeficit) :=
    coefficient_le_exp_prefixProfileCost_add_deficit_of_le_exp_one
      certificate.start_pos certificate.coefficient_le_exp_one
  simpa only [ProfileRadialTailCertificate.radialTail,
    pairPointEnvelope] using
      (coefficient_mul_profileUpperTailEnvelope_le_pairEnvelope_div_prefix
        certificate.start_le_scale certificate.cutoff hcoefficient)

/-- Build the far-pair record at the literal HLOZ terminal radii.  All local
hit, escape, exit, normalization, and accumulated-loss fields are discharged
from `TerminalMarkedScaleCertificate`; only the actual asymmetric path-space
decomposition and its two-stage mass estimates remain as inputs. -/
def of_canonicalTerminal_twoStage
    {delta : ℝ} {n : ℕ} {harnackFactor : ℝ}
    {i : Fin (chosenBlockCount delta n)} {x y : Point}
    {Data : Type}
    (certificate : TerminalMarkedScaleCertificate delta (scaleIndex delta n))
    (successful retained : Set StepPath)
    (radialTail : ℝ)
    (skeletonWeight : Data →
      (Fin (requiredTerminalCount (scaleIndex delta n) chosenProfileDelta) →
        TerminalEntrance (scaleIndex delta n) y) →
      (Fin (requiredTerminalCount (scaleIndex delta n) chosenProfileDelta) →
        TerminalExit (scaleIndex delta n) y) → ℝ≥0∞)
    (decomposition : MarkedStoppedDataUpperDecomposition fairSteps
      (stoppedThickPointEvent
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta
          (chosenThickDelta delta) x ∩
        stoppedThickPointEvent
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta
          (chosenThickDelta delta) y)
      successful skeletonWeight
      (fun _ (u : TerminalEntrance (scaleIndex delta n) y)
          (z : TerminalExit (scaleIndex delta n) y) ↦
        terminalSkeletonKernel
          (terminalOuterBoundary (scaleIndex delta n) y) u.1 z.1)
      (fun _ (u : TerminalEntrance (scaleIndex delta n) y) k
          (z : TerminalExit (scaleIndex delta n) y) ↦
        terminalMarkedKernel
          (terminalOuterBoundary (scaleIndex delta n) y) y u.1 k z.1)
      Set.univ)
    (hloss : Real.exp (1 / 4) ≤ harnackFactor)
    (hradial0 : 0 ≤ radialTail)
    (hsuccessful : fairSteps.real successful ≤
      radialTail * fairSteps.real retained)
    (hretained : fairSteps.real retained ≤ pairPointEnvelope delta n)
    (hradial : radialTail ≤ pairPointEnvelope delta n /
      prefixProfileLower
        (pairPrefixScale (scaleIndex delta n)
          (separationLevel (scaleIndex delta n) x y))) :
    ActualMarkedFarPairData delta n harnackFactor i x y := by
  let s := scaleIndex delta n
  let m := requiredTerminalCount s chosenProfileDelta
  have hs2 : 2 ≤ s := by
    have hs4 := certificate.marked.scale_ge_four
    omega
  have hq1 : terminalHitProbability s < 1 := by
    linarith [certificate.parameters.hit_le_half]
  have hexitFactor : 0 ≤ 1 - terminalPoissonExitError s (s ^ 8) :=
    sub_nonneg.mpr certificate.marked.exitError_le_one
  have href : referenceEventMass
      (fun _ : Fin m ↦ fun k ↦ ENNReal.ofReal
        (visitMass (terminalHitProbability s)
          (terminalEscapeProbability s) k))
      Set.univ ≤ 1 := by
    rw [referenceEventMass_visitMass_eq_iidVisitMeasure
      m (terminalHitProbability s) (terminalEscapeProbability s)
      certificate.parameters.hit_nonneg
      certificate.parameters.hit_le_one
      certificate.parameters.escape_pos
      certificate.parameters.escape_le_one]
    calc
      _ ≤ AppendixLocalTime.iidVisitMeasure m
          (terminalHitProbability s) (terminalEscapeProbability s)
          certificate.parameters.hit_nonneg
          certificate.parameters.hit_le_one
          certificate.parameters.escape_pos
          certificate.parameters.escape_le_one Set.univ :=
        measure_mono (subset_univ _)
      _ = 1 := measure_univ
  refine
    { Data := Data
      Entrance := TerminalEntrance s y
      Exit := TerminalExit s y
      coordinateCount := m
      successful := successful
      retained := retained
      radialTail := radialTail
      boundary := fun _ ↦ terminalOuterBoundary s y
      target := fun _ ↦ y
      entrance := fun _ u ↦ u.1
      endpoint := fun _ z ↦ z.1
      hitProbability := fun _ ↦ terminalHitProbability s
      escapeProbability := fun _ ↦ terminalEscapeProbability s
      hitError := fun _ ↦ terminalHitRelativeError s
      exitError := fun _ ↦ terminalPoissonExitError s (s ^ 8)
      target_not_boundary := fun _ ↦ center_not_mem_terminalOuterBoundary s y hs2
      escape_nonneg := fun _ ↦ certificate.parameters.escape_pos.le
      escape_le_one := fun _ ↦ certificate.parameters.escape_le_one
      escape_eq := fun _ ↦ terminalEscapeProbability_eq_relativeBoundary s y
      hit_nonneg := fun _ ↦ certificate.parameters.hit_nonneg
      hit_lt_one := fun _ ↦ hq1
      hitError_nonneg := fun _ ↦ certificate.marked.hitError_nonneg
      exitError_nonneg := fun _ ↦ certificate.marked.exitError_nonneg
      hitFactor_nonneg := fun _ ↦ certificate.marked.hitFactor_nonneg
      exitFactor_nonneg := fun _ ↦ hexitFactor
      hitLower := fun _ u ↦ certificate.marked.hitLower y u
      hitUpper := fun _ u ↦ certificate.marked.hitUpper y u
      exitLower := ?_
      exitUpper := ?_
      visitEvent := Set.univ
      skeletonWeight := skeletonWeight
      decomposition := by simpa only [s, m] using decomposition
      referenceMass_le_one := by simpa only [s, m] using href
      accumulatedLoss_le := ?_
      radialTail_nonneg := hradial0
      successful_le := hsuccessful
      retained_le := hretained
      radialTail_le := hradial }
  · intro _ u z
    exact (terminalSkeletonKernel_terminalBoundary_toReal_two_sided
      s (s ^ 8) y (by omega) certificate.marked.cut_inner
      certificate.marked.cut_scale certificate.marked.cut_outer
      certificate.marked.greenLower_pos certificate.marked.exitError_le_one
      u z).1
  · intro _ u z
    exact (terminalSkeletonKernel_terminalBoundary_toReal_two_sided
      s (s ^ 8) y (by omega) certificate.marked.cut_inner
      certificate.marked.cut_scale certificate.marked.cut_outer
      certificate.marked.greenLower_pos certificate.marked.exitError_le_one
      u z).2
  · exact (terminalMarkedUpperLossProduct_le_exp_quarter s certificate.marked).trans hloss

/-- Literal-atom version of `of_canonicalTerminal_twoStage`.  Instead of
assuming the successful-mass comparison, it receives the retained stopped
atoms, the post-separation radial-word atoms, their exact factorization, and
the uniform sum bound on their conditional weights. -/
def of_canonicalTerminal_atomWeights
    {delta : ℝ} {n : ℕ} {harnackFactor : ℝ}
    {i : Fin (chosenBlockCount delta n)} {x y : Point}
    {Data : Type}
    (certificate : TerminalMarkedScaleCertificate delta (scaleIndex delta n))
    (successful retained : Set StepPath)
    (radialTail : ℝ)
    (skeletonWeight : Data →
      (Fin (requiredTerminalCount (scaleIndex delta n) chosenProfileDelta) →
        TerminalEntrance (scaleIndex delta n) y) →
      (Fin (requiredTerminalCount (scaleIndex delta n) chosenProfileDelta) →
        TerminalExit (scaleIndex delta n) y) → ℝ≥0∞)
    (decomposition : MarkedStoppedDataUpperDecomposition fairSteps
      (stoppedThickPointEvent
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta
          (chosenThickDelta delta) x ∩
        stoppedThickPointEvent
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta
          (chosenThickDelta delta) y)
      successful skeletonWeight
      (fun _ (u : TerminalEntrance (scaleIndex delta n) y)
          (z : TerminalExit (scaleIndex delta n) y) ↦
        terminalSkeletonKernel
          (terminalOuterBoundary (scaleIndex delta n) y) u.1 z.1)
      (fun _ (u : TerminalEntrance (scaleIndex delta n) y) k
          (z : TerminalExit (scaleIndex delta n) y) ↦
        terminalMarkedKernel
          (terminalOuterBoundary (scaleIndex delta n) y) y u.1 k z.1)
      Set.univ)
    {RetainedCode : Type*} [Countable RetainedCode]
    (TailCode : RetainedCode → Type*)
    [∀ r, Countable (TailCode r)]
    (retainedAtom : RetainedCode → Set StepPath)
    (tailAtom : ∀ r, TailCode r → Set StepPath)
    (tailWeight : ∀ r, TailCode r → ℝ≥0∞)
    (hradial0 : 0 ≤ radialTail)
    (hsuccessful : successful ⊆ ⋃ r, ⋃ t, tailAtom r t)
    (hretained : retained = ⋃ r, retainedAtom r)
    (hretainedMeasurable : ∀ r, MeasurableSet (retainedAtom r))
    (hretainedDisjoint : Pairwise fun r s ↦
      Disjoint (retainedAtom r) (retainedAtom s))
    (hatomMass : ∀ r t,
      fairSteps (tailAtom r t) =
        tailWeight r t * fairSteps (retainedAtom r))
    (htailWeight : ∀ r, ∑' t, tailWeight r t ≤
      ENNReal.ofReal radialTail)
    (hloss : Real.exp (1 / 4) ≤ harnackFactor)
    (hretainedUpper : fairSteps.real retained ≤ pairPointEnvelope delta n)
    (hradialUpper : radialTail ≤ pairPointEnvelope delta n /
      prefixProfileLower
        (pairPrefixScale (scaleIndex delta n)
          (separationLevel (scaleIndex delta n) x y))) :
    ActualMarkedFarPairData delta n harnackFactor i x y :=
  of_canonicalTerminal_twoStage certificate successful retained radialTail
    skeletonWeight decomposition hloss hradial0
    (fairSteps_real_le_radialTail_mul_retained_of_atom_weights
      TailCode successful retained retainedAtom tailAtom tailWeight radialTail
      hradial0 hsuccessful hretained hretainedMeasurable hretainedDisjoint
      hatomMass htailWeight)
    hretainedUpper hradialUpper

/-- Fully numerical two-stage constructor.  The radial upper field is
derived from an explicit constrained-profile mixture rather than supplied
as the desired scalar inequality. -/
def of_canonicalTerminal_profileAtomWeights
    {delta : ℝ} {n : ℕ} {harnackFactor : ℝ}
    {i : Fin (chosenBlockCount delta n)} {x y : Point}
    {Data : Type}
    (terminalCertificate :
      TerminalMarkedScaleCertificate delta (scaleIndex delta n))
    (radialCertificate : ProfileRadialTailCertificate delta n x y)
    (successful retained : Set StepPath)
    (skeletonWeight : Data →
      (Fin (requiredTerminalCount (scaleIndex delta n) chosenProfileDelta) →
        TerminalEntrance (scaleIndex delta n) y) →
      (Fin (requiredTerminalCount (scaleIndex delta n) chosenProfileDelta) →
        TerminalExit (scaleIndex delta n) y) → ℝ≥0∞)
    (decomposition : MarkedStoppedDataUpperDecomposition fairSteps
      (stoppedThickPointEvent
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta
          (chosenThickDelta delta) x ∩
        stoppedThickPointEvent
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta
          (chosenThickDelta delta) y)
      successful skeletonWeight
      (fun _ (u : TerminalEntrance (scaleIndex delta n) y)
          (z : TerminalExit (scaleIndex delta n) y) ↦
        terminalSkeletonKernel
          (terminalOuterBoundary (scaleIndex delta n) y) u.1 z.1)
      (fun _ (u : TerminalEntrance (scaleIndex delta n) y) k
          (z : TerminalExit (scaleIndex delta n) y) ↦
        terminalMarkedKernel
          (terminalOuterBoundary (scaleIndex delta n) y) y u.1 k z.1)
      Set.univ)
    {RetainedCode : Type*} [Countable RetainedCode]
    (TailCode : RetainedCode → Type*)
    [∀ r, Countable (TailCode r)]
    (retainedAtom : RetainedCode → Set StepPath)
    (tailAtom : ∀ r, TailCode r → Set StepPath)
    (tailWeight : ∀ r, TailCode r → ℝ≥0∞)
    (hsuccessful : successful ⊆ ⋃ r, ⋃ t, tailAtom r t)
    (hretained : retained = ⋃ r, retainedAtom r)
    (hretainedMeasurable : ∀ r, MeasurableSet (retainedAtom r))
    (hretainedDisjoint : Pairwise fun r s ↦
      Disjoint (retainedAtom r) (retainedAtom s))
    (hatomMass : ∀ r t,
      fairSteps (tailAtom r t) =
        tailWeight r t * fairSteps (retainedAtom r))
    (htailWeight : ∀ r, ∑' t, tailWeight r t ≤
      ENNReal.ofReal radialCertificate.radialTail)
    (hloss : Real.exp (1 / 4) ≤ harnackFactor)
    (hretainedUpper : fairSteps.real retained ≤ pairPointEnvelope delta n) :
    ActualMarkedFarPairData delta n harnackFactor i x y :=
  of_canonicalTerminal_atomWeights terminalCertificate successful retained
    radialCertificate.radialTail skeletonWeight decomposition TailCode
    retainedAtom tailAtom tailWeight radialCertificate.radial_nonneg
    hsuccessful hretained hretainedMeasurable hretainedDisjoint hatomMass
    htailWeight hloss hretainedUpper
    radialCertificate.le_pairEnvelope_div_prefix

end

end Erdos1165.AsymmetricActualFarPairData
