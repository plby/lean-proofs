/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47Canonical
import ErdosProblems.Erdos1166.Erdos1166HLOZProp45SourceEndpoints
import ErdosProblems.Erdos1166.Erdos1166HLOZProp45SourceAbsorption

/-!
# Fixed-profile assembly of HLOZ Proposition 4.5

This module joins the checked endpoint/Chernoff estimate to the exact
Proposition-4.7 stopped-`Theta` event.  The remaining premises are deliberately
source-local: a finite external-profile atomization, the deterministic
stopped/inverse-clock compatibility on each atom, Proposition 4.4's two
profile-cardinality conclusions, and the four Proposition 4.2
negative-binomial laws.  No premise is itself the desired Proposition-4.5
probability estimate.
-/

namespace Erdos1166.HLOZProp47Prop45Connector

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

open HLOZFoundation HLOZDecomposition HLOZProp47Parameters
open HLOZUrn
open HLOZProp47SourceObjects HLOZProp47SourceAssembly
open HLOZProp45SourceClock HLOZProp45SourceInterval
open HLOZProp45SourceMirrors HLOZProp45SourceEndpoints
open HLOZPrimedStopped HLOZProp47Canonical
open HLOZProp45SourceAbsorption
open HLOZProp45Theta
open HLOZPairing.ScreeningBridge

abbrev Path := ℕ → Site

/-- The exact data on one fixed external-profile atom needed by the checked
Proposition-4.5 endpoint theorem.  `theta_subset` is the pathwise
identification/transport obligation for the selected one of the six source
tilings; all remaining fields are literal hypotheses of Propositions 4.2
and 4.4 or deterministic inverse-clock compatibility. -/
structure FixedProfileAtomInputs
    (profiles : ExternalProfilePair) (m k : ℕ)
    (μ : Measure Path) (C H : Set Path) where
  q : ℕ
  qPrime : ℕ
  sites : Finset Site
  unprimedProfile : Site → ℕ
  primedProfile : Site → ℕ
  measurable_C : MeasurableSet C
  theta_subset :
    C ∩ H ∩ stoppedThetaEvent profiles 10 m k ⊆
      C ∩ H ∩ fullProp45StoppedEvent
        (concretePrimedShiftedDeletionClock m k qPrime) sites
        (sourceBandLowerNat m) m
  unprimedProfile_atom : C ⊆
    inverseClockProfileAtom q sites unprimedProfile
  unprimedMinus_compatible :
    C ∩ H ∩ intervalStoppedThetaMinusEvent
        sites m (sourceBandLowerNat m) k ⊆
      intervalClockPrefixCompatibleEvent q sites m
        (sourceBandLowerNat m) k unprimedProfile
  unprimedPlus_compatible :
    C ∩ H ∩ intervalStoppedThetaPlusEvent sites m m k ⊆
      intervalClockInitialPrefixCompatibleEvent q sites m m k
  primedProfile_atom : C ⊆ primedInverseProfileAtom
    (concretePrimedShiftedDeletionClock m k qPrime) sites primedProfile
  primedMinus_compatible :
    C ∩ H ∩ primedIntervalStoppedThetaMinusEvent
        (concretePrimedShiftedDeletionClock m k qPrime) sites
          (sourceBandLowerNat m) ⊆
      primedMinusPrefixCompatibleEvent
        (concretePrimedShiftedDeletionClock m k qPrime)
        sites (sourceBandLowerNat m) primedProfile
  primedPlus_compatible :
    C ∩ H ∩ primedIntervalStoppedThetaPlusEvent
        (concretePrimedShiftedDeletionClock m k qPrime) sites m ⊆
      primedPlusInitialPrefixCompatibleEvent
        (concretePrimedShiftedDeletionClock m k qPrime) sites m
  unprimed_prop44 :
    ((sourceProp44Candidates sites m unprimedProfile).card : ℝ) ≤
      Real.exp (16 * sourceRate m)
  primed_prop44 :
    ((sourceProp44Candidates sites m primedProfile).card : ℝ) ≤
      Real.exp (16 * sourceRate m)
  horizon_card :
    (sites.card : ℝ) ≤ Real.exp (16 * Real.sqrt (m : ℝ))
  unprimedMinus_law : ∀ x ∈ sites,
    HasLaw (fun s ↦ inverseClockHoldingPrefix s q
      (intervalDotIndex m (sourceBandLowerNat m) unprimedProfile x) x)
      (negBinMeasure
        (intervalDotIndex m (sourceBandLowerNat m) unprimedProfile x)) μ[|C]
  unprimedPlus_law : ∀ x ∈
      intervalPlusCandidates sites m m unprimedProfile,
    HasLaw (fun s ↦ inverseClockHoldingPrefix s q
      (intervalHighCut m m) x)
      (negBinMeasure (intervalHighCut m m)) μ[|C]
  primedMinus_law : ∀ x ∈ sites,
    HasLaw (fun s ↦ primedInverseClockHoldingPrefix s qPrime
      (intervalDotIndex m (sourceBandLowerNat m) primedProfile x) x)
      (negBinMeasure
        (intervalDotIndex m (sourceBandLowerNat m) primedProfile x)) μ[|C]
  primedPlus_law : ∀ x ∈
      intervalPlusCandidates sites m m primedProfile,
    HasLaw (fun s ↦ primedInverseClockHoldingPrefix s qPrime
      (intervalHighCut m m) x)
      (negBinMeasure (intervalHighCut m m)) μ[|C]

/-- The source endpoint theorem, specialized to one exact profile atom and
then restricted to the selected tiling's stopped-`Theta` event. -/
theorem FixedProfileAtomInputs.conditional_theta_le
    {profiles : ExternalProfilePair} {m k : ℕ}
    {μ : Measure Path} {C H : Set Path}
    (hs : SourceIntervalScale m (sourceBandLowerNat m) ∧
      SourceUpperScale m m)
    (h : FixedProfileAtomInputs profiles m k μ C H) :
    μ[|C] (C ∩ H ∩ stoppedThetaEvent profiles 10 m k) ≤
      sourceProp45FourBranchError m := by
  calc
    μ[|C] (C ∩ H ∩ stoppedThetaEvent profiles 10 m k) ≤
        μ[|C] (C ∩ H ∩ fullProp45StoppedEvent
          (concretePrimedShiftedDeletionClock m k h.qPrime) h.sites
          (sourceBandLowerNat m) m) := measure_mono h.theta_subset
    _ ≤ sourceProp45FourBranchError m :=
      cond_inter_fullProp45ConcretePrimedStoppedEvent_sourceBand_le
        h.q h.qPrime m k hs μ C H h.sites h.unprimedProfile
        h.primedProfile h.unprimedProfile_atom
        h.unprimedMinus_compatible h.unprimedPlus_compatible
        h.primedProfile_atom h.primedMinus_compatible
        h.primedPlus_compatible h.unprimed_prop44 h.primed_prop44
        h.horizon_card h.unprimedMinus_law h.unprimedPlus_law
        h.primedMinus_law h.primedPlus_law

/-! ### Arbitrary source intervals

The shorthand `stoppedThetaEvent` used by Proposition 4.7 is the top source
interval only.  Proposition 4.8, however, encounters every lower interval
between levels `1` and `sourceAlphaIntervalCount`.  The following package is
the exact arbitrary-endpoint version of `FixedProfileAtomInputs`; it prevents
those lower-level exceptions from being incorrectly identified with the
top-band event. -/

/-- Fixed-profile Proposition-4.5 data for an arbitrary source interval
`[a,b)`.  The event `thetaPath` is supplied by the stopped-profile
reconstruction at that level and is required only inside the contextual
history `H`. -/
structure FixedProfileIntervalAtomInputs
    (m a b k : ℕ) (μ : Measure Path)
    (C H thetaPath : Set Path) where
  q : ℕ
  qPrime : ℕ
  sites : Finset Site
  unprimedProfile : Site → ℕ
  primedProfile : Site → ℕ
  measurable_C : MeasurableSet C
  theta_subset :
    C ∩ H ∩ thetaPath ⊆ C ∩ H ∩
      fullProp45StoppedEvent
        (concretePrimedShiftedDeletionClock m k qPrime) sites a b
  unprimedProfile_atom : C ⊆
    inverseClockProfileAtom q sites unprimedProfile
  unprimedMinus_compatible :
    C ∩ H ∩ intervalStoppedThetaMinusEvent sites m a k ⊆
      intervalClockPrefixCompatibleEvent q sites m a k unprimedProfile
  unprimedPlus_compatible :
    C ∩ H ∩ intervalStoppedThetaPlusEvent sites m b k ⊆
      intervalClockInitialPrefixCompatibleEvent q sites m b k
  primedProfile_atom : C ⊆ primedInverseProfileAtom
    (concretePrimedShiftedDeletionClock m k qPrime) sites primedProfile
  primedMinus_compatible :
    C ∩ H ∩ primedIntervalStoppedThetaMinusEvent
        (concretePrimedShiftedDeletionClock m k qPrime) sites a ⊆
      primedMinusPrefixCompatibleEvent
        (concretePrimedShiftedDeletionClock m k qPrime) sites a primedProfile
  primedPlus_compatible :
    C ∩ H ∩ primedIntervalStoppedThetaPlusEvent
        (concretePrimedShiftedDeletionClock m k qPrime) sites b ⊆
      primedPlusInitialPrefixCompatibleEvent
        (concretePrimedShiftedDeletionClock m k qPrime) sites b
  unprimed_prop44 :
    ((sourceProp44Candidates sites m unprimedProfile).card : ℝ) ≤
      Real.exp (16 * sourceRate m)
  primed_prop44 :
    ((sourceProp44Candidates sites m primedProfile).card : ℝ) ≤
      Real.exp (16 * sourceRate m)
  horizon_card :
    (sites.card : ℝ) ≤ Real.exp (16 * Real.sqrt (m : ℝ))
  unprimedMinus_law : ∀ x ∈ sites,
    HasLaw (fun s ↦ inverseClockHoldingPrefix s q
      (intervalDotIndex m a unprimedProfile x) x)
      (negBinMeasure (intervalDotIndex m a unprimedProfile x)) μ[|C]
  unprimedPlus_law : ∀ x ∈
      intervalPlusCandidates sites m b unprimedProfile,
    HasLaw (fun s ↦ inverseClockHoldingPrefix s q
      (intervalHighCut m b) x)
      (negBinMeasure (intervalHighCut m b)) μ[|C]
  primedMinus_law : ∀ x ∈ sites,
    HasLaw (fun s ↦ primedInverseClockHoldingPrefix s qPrime
      (intervalDotIndex m a primedProfile x) x)
      (negBinMeasure (intervalDotIndex m a primedProfile x)) μ[|C]
  primedPlus_law : ∀ x ∈
      intervalPlusCandidates sites m b primedProfile,
    HasLaw (fun s ↦ primedInverseClockHoldingPrefix s qPrime
      (intervalHighCut m b) x)
      (negBinMeasure (intervalHighCut m b)) μ[|C]

/-- The arbitrary-interval fixed-profile estimate.  All four Chernoff
branches and the conditional-to-unconditional normalization are already
proved in the endpoint modules; this theorem only performs the deterministic
event transport supplied by `theta_subset`. -/
theorem FixedProfileIntervalAtomInputs.conditional_theta_le
    {m a b k : ℕ} {μ : Measure Path}
    {C H thetaPath : Set Path}
    (hsLower : SourceIntervalScale m a)
    (hsUpper : SourceUpperScale m b)
    (h : FixedProfileIntervalAtomInputs m a b k μ C H thetaPath) :
    μ[|C] (C ∩ H ∩ thetaPath) ≤ sourceProp45FourBranchError m := by
  calc
    μ[|C] (C ∩ H ∩ thetaPath) ≤
        μ[|C] (C ∩ H ∩ fullProp45StoppedEvent
          (concretePrimedShiftedDeletionClock m k h.qPrime) h.sites a b) :=
      measure_mono h.theta_subset
    _ ≤ sourceProp45FourBranchError m := by
      exact cond_inter_fullProp45ConcretePrimedStoppedEvent_le
        h.q h.qPrime m a b k hsLower hsUpper μ C H h.sites
        h.unprimedProfile h.primedProfile h.unprimedProfile_atom
        h.unprimedMinus_compatible h.unprimedPlus_compatible
        h.primedProfile_atom h.primedMinus_compatible
        h.primedPlus_compatible h.unprimed_prop44 h.primed_prop44
        h.horizon_card h.unprimedMinus_law h.unprimedPlus_law
        h.primedMinus_law h.primedPlus_law

/-- Unnormalized form of the arbitrary-interval estimate.  This is the
exact shape consumed by a disjoint stopped-atom union: the interval error
is multiplied by the mass of the fixed-profile atom. -/
theorem FixedProfileIntervalAtomInputs.theta_measure_le_mul
    {m a b k : ℕ} {μ : Measure Path}
    [IsFiniteMeasure μ]
    {C H thetaPath : Set Path}
    (hsLower : SourceIntervalScale m a)
    (hsUpper : SourceUpperScale m b)
    (h : FixedProfileIntervalAtomInputs m a b k μ C H thetaPath) :
    μ (C ∩ H ∩ thetaPath) ≤
      sourceProp45FourBranchError m * μ C := by
  have hcond := h.conditional_theta_le hsLower hsUpper
  have hmul := cond_mul_eq_inter h.measurable_C (C ∩ H ∩ thetaPath) μ
  have hinter : C ∩ (C ∩ H ∩ thetaPath) = C ∩ H ∩ thetaPath := by
    ext path
    simp only [Set.mem_inter_iff]
    tauto
  rw [hinter] at hmul
  calc
    μ (C ∩ H ∩ thetaPath) =
        μ[|C] (C ∩ H ∩ thetaPath) * μ C := hmul.symm
    _ ≤ sourceProp45FourBranchError m * μ C := by gcongr

/-- Finite conditional-profile aggregation.  The atom events are disjoint,
and the `bad` event contains the complement of the good horizon/profile
partition.  Multiplying the conditional estimate by each atom mass and
summing costs no factor because the atom masses sum to at most one. -/
theorem measure_le_bad_add_of_finite_conditional_partition
    {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (atoms : Finset ι) (C : ι → Set Ω)
    (E H bad : Set Ω) (ε badRate : ℝ≥0∞)
    (hCmeas : ∀ j ∈ atoms, MeasurableSet (C j))
    (hCdisj : (atoms : Set ι).PairwiseDisjoint C)
    (hcover : E ⊆ bad ∪ ⋃ j ∈ atoms, C j ∩ H ∩ E)
    (hbad : μ bad ≤ badRate)
    (hcond : ∀ j ∈ atoms, μ[|C j] (C j ∩ H ∩ E) ≤ ε) :
    μ E ≤ badRate + ε := by
  have hatom (j : ι) (hj : j ∈ atoms) :
      μ (C j ∩ H ∩ E) ≤ ε * μ (C j) := by
    have hmul := cond_mul_eq_inter (hCmeas j hj) (C j ∩ H ∩ E) μ
    have hinter : C j ∩ (C j ∩ H ∩ E) = C j ∩ H ∩ E := by
      ext ω
      simp only [Set.mem_inter_iff]
      tauto
    rw [hinter] at hmul
    calc
      μ (C j ∩ H ∩ E) = μ[|C j] (C j ∩ H ∩ E) * μ (C j) := hmul.symm
      _ ≤ ε * μ (C j) := by
        gcongr
        exact hcond j hj
  have hsumC : ∑ j ∈ atoms, μ (C j) ≤ 1 := by
    calc
      ∑ j ∈ atoms, μ (C j) = μ (⋃ j ∈ atoms, C j) :=
        (measure_biUnion_finset hCdisj hCmeas).symm
      _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  calc
    μ E ≤ μ (bad ∪ ⋃ j ∈ atoms, C j ∩ H ∩ E) := measure_mono hcover
    _ ≤ μ bad + μ (⋃ j ∈ atoms, C j ∩ H ∩ E) := measure_union_le _ _
    _ ≤ badRate + ∑ j ∈ atoms, μ (C j ∩ H ∩ E) := by
      gcongr
      exact measure_biUnion_finset_le atoms _
    _ ≤ badRate + ∑ j ∈ atoms, ε * μ (C j) := by
      gcongr with j hj
      exact hatom j hj
    _ = badRate + ε * ∑ j ∈ atoms, μ (C j) := by
      rw [Finset.mul_sum]
    _ ≤ badRate + ε * 1 := by gcongr
    _ = badRate + ε := by rw [mul_one]

/-- A source-shaped finite atomization at one level and one selected tiling.
Its fields expose the bad-horizon/profile charge and every fixed-profile
input, rather than assuming the resulting probability estimate. -/
structure CanonicalFiniteAtomization
    (m : ℕ) (i : Fin 6) (k badCoeff : ℕ) where
  atoms : Finset ℕ
  atom : ℕ → Set Path
  horizon : Set Path
  bad : Set Path
  atomInputs : ∀ j ∈ atoms,
    FixedProfileAtomInputs (canonicalProfiles i) m k
      simpleRandomWalkLaw (atom j) horizon
  pairwise : (atoms : Set ℕ).PairwiseDisjoint atom
  cover : stoppedThetaEvent (canonicalProfiles i) (canonicalCStar i) m k ⊆
    bad ∪ ⋃ j ∈ atoms,
      atom j ∩ horizon ∩
        stoppedThetaEvent (canonicalProfiles i) (canonicalCStar i) m k
  bad_bound : simpleRandomWalkLaw bad ≤
    sourceExceptionalRateWithPrefactor m badCoeff kappa

/-- Once the finite source atomization is supplied, all endpoint estimates,
conditional-to-unconditional multiplication, and error absorption are
automatic. -/
theorem CanonicalFiniteAtomization.theta_measure_le
    {m : ℕ} {i : Fin 6} {k badCoeff : ℕ}
    (hs : SourceIntervalScale m (sourceBandLowerNat m) ∧
      SourceUpperScale m m)
    (habsorb : sourceProp45FourBranchError m ≤
      sourceExceptionalRateWithPrefactor m 6 kappa)
    (h : CanonicalFiniteAtomization m i k badCoeff) :
    simpleRandomWalkLaw
        (stoppedThetaEvent (canonicalProfiles i) (canonicalCStar i) m k) ≤
      sourceExceptionalRateWithPrefactor m (badCoeff + 6) kappa := by
  have hcore := measure_le_bad_add_of_finite_conditional_partition
    simpleRandomWalkLaw h.atoms h.atom
    (stoppedThetaEvent (canonicalProfiles i) (canonicalCStar i) m k)
    h.horizon h.bad (sourceProp45FourBranchError m)
    (sourceExceptionalRateWithPrefactor m badCoeff kappa)
    (fun j hj ↦ (h.atomInputs j hj).measurable_C) h.pairwise h.cover h.bad_bound
    (fun j hj ↦ by
      simpa only [canonicalCStar] using
        (h.atomInputs j hj).conditional_theta_le hs)
  calc
    simpleRandomWalkLaw
        (stoppedThetaEvent (canonicalProfiles i) (canonicalCStar i) m k) ≤
      sourceExceptionalRateWithPrefactor m badCoeff kappa +
        sourceProp45FourBranchError m := hcore
    _ ≤ sourceExceptionalRateWithPrefactor m badCoeff kappa +
        sourceExceptionalRateWithPrefactor m 6 kappa := by gcongr
    _ = sourceExceptionalRateWithPrefactor m (badCoeff + 6) kappa := by
      simp only [sourceExceptionalRateWithPrefactor]
      push_cast
      ring

/-- The exact residual source premise for Proposition 4.5: eventually, each
of the six pairing-adapted deletions and each of the three stopping levels
admits the finite profile atomization above. -/
def HasCanonicalProp45FiniteAtomizations (badCoeff : ℕ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i : Fin 6, ∀ r : StageIndex,
    Nonempty (CanonicalFiniteAtomization m i (stageNumber r) badCoeff)

/-- Concrete canonical Proposition-4.7 Proposition-4.5 estimate.  The
distance-mesh parameter does not affect the stopped-`Theta` bound, so the
finite-profile conclusion applies uniformly to every low-scale mesh cell. -/
theorem prop47Prop45Estimate_of_canonicalFiniteAtomizations
    {badCoeff : ℕ}
    (hatoms : HasCanonicalProp45FiniteAtomizations badCoeff) :
    Prop47Prop45Estimate canonicalProfiles canonicalCStar (badCoeff + 6) := by
  filter_upwards [hatoms, eventually_sourceEndpointScales,
    eventually_sourceProp45FourBranchError_le] with m hatoms hs habsorb
  intro i r a _ha
  rcases hatoms i r with ⟨hatom⟩
  have htheta := hatom.theta_measure_le hs habsorb
  exact (measure_mono (by
    intro s hsFailure
    exact hsFailure.2)).trans htheta

end Erdos1166.HLOZProp47Prop45Connector
