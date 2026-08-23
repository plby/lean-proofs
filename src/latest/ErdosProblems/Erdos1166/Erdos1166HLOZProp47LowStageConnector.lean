/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1166.Erdos1166HLOZFiniteUnion
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47SourceAssembly
import ErdosProblems.Erdos1166.Erdos1166HLOZStoppedMapLawReduced
import ErdosProblems.Erdos1166.Erdos1166HLOZPrimedOddRightWinner
import ErdosProblems.Erdos1166.Erdos1166HLOZProp49Coordinate
import ErdosProblems.Erdos1166.Erdos1166HLOZTerminalParityWinner

/-!
# The low-distance transition in HLOZ Proposition 4.7

This file expands the formerly atomic `Prop47LowStageEstimate` into the two
conditional estimates used in equations (4.35)--(4.37) of the source.

* `Prop47SequentialEscapeEstimate` is the strong-Markov exit-before-return
  factor, with the complete preceding sequence of screens retained.
* `Prop47StoppedProfileProp49Estimate` is Proposition 4.9 after its bound,
  which is uniform in the stopped external profile, has been averaged over
  that profile while retaining the same preceding sequence of screens.

Their product is
`log(m+1)^2 (m+1)^(-(κ₁-2δ))`.  The strict inequality `κ₂ < κ₁`
absorbs the logarithm and gives the required one-stage rate
`(m+1)^(-κ)`, where `κ = κ₂-2δ`.

No premise below is a `StageBound`, and the conditioning event is the
recursive `prop47History` at the current stage rather than the final
four-site event.
-/

namespace Erdos1166.HLOZProp47LowStageConnector

open Filter MeasureTheory Set
open scoped ENNReal ProbabilityTheory

open HLOZPairing.ScreeningBridge HLOZScreeningAssembly
open HLOZProp47Parameters HLOZProp47SourceObjects
open HLOZProp49Coordinate HLOZLemma412Windows
open HLOZProp47SourceAssembly
open HLOZActualStopped HLOZIncompleteStoppedBlocks HLOZStoppedSourcePartition
open HLOZStoppedMapLaw HLOZStoppedMapLawReduced HLOZProp48Truncated
open HLOZPrimedOddRightWinner
open HLOZTerminalParityWinner
open HLOZStoppedMixedReconstruction HLOZPrimedOddMixedReconstruction
open HLOZPrimedStopped HLOZReconstruction HLOZSourceInstantiation
open HLOZFiniteUnion HLOZDecomposition

abbrev Path := ℕ → Site

/-- The exit-before-return cost in the first factor on the right of (4.37).
The harmless `m+1` convention avoids a separate zero-level case. -/
noncomputable def sourceLowEscapeRate
    (m escapeCoeff : ℕ) (alpha : ℝ) : ℝ≥0∞ :=
  (escapeCoeff : ℝ≥0∞) *
    ((m : ℝ≥0∞) + 1) ^ (-(alpha - delta))

/-- The uniform stopped-profile bound from Proposition 4.9, evaluated at
the near-favourite exponent `alpha + delta` appearing in (4.37). -/
noncomputable def sourceProp49ScreenRate
    (m A : ℕ) (alpha : ℝ) : ℝ≥0∞ :=
  (A : ℝ≥0∞) *
    ENNReal.ofReal (Real.log ((m : ℝ) + 1) ^ 2) *
      ((m : ℝ≥0∞) + 1) ^ (-(kappaOne - (alpha + delta)))

/-- The event obtained after fixing all preceding distance screens and then
requiring the Proposition-4.9 near-favourite screen at the current stopped
time. -/
noncomputable def prop47SequentialScreenEvent
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex) : Set Path :=
  prop47History profiles cStar m i a r.1 ∩
    lowScaleScreenEvent (profiles i) (cStar i) i m (stageNumber r)
      (alphaValue (tripleAlphaIndex a r) + delta)

/-- The source clean event on the right side of the deterministic inclusion
(4.37): the sequential history, the shifted exit-before-return event, and
the stopped near-favourite screen. -/
noncomputable def prop47SequentialExitScreenEvent
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex) : Set Path :=
  prop47History profiles cStar m i a r.1 ∩
    (exitBeforeReturnAtNextCreation m (stageNumber r)
        (distanceBinLower m (alphaValue (tripleAlphaIndex a r))) ∩
      lowScaleScreenEvent (profiles i) (cStar i) i m (stageNumber r)
        (alphaValue (tripleAlphaIndex a r) + delta))

/-- Multiplied-out strong-Markov estimate in (4.37), before Proposition 4.9
is applied.  The right side retains the exact preceding sequential history.
-/
def Prop47SequentialEscapeEstimate
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (escapeCoeff : ℕ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i a (r : StageIndex),
    alphaValue (tripleAlphaIndex a r) ≤ kappaTwo →
    simpleRandomWalkLaw
        (prop47SequentialExitScreenEvent profiles cStar m i a r) ≤
      sourceLowEscapeRate m escapeCoeff
          (alphaValue (tripleAlphaIndex a r)) *
        simpleRandomWalkLaw
          (prop47SequentialScreenEvent profiles cStar m i a r)

/-- Proposition 4.9 after disintegrating with respect to the stopped
external profile and then averaging its uniform estimate.  Crucially, the
conditioning event is the history through stage `r`, not `M_m^4` and not a
history in which later distance screens have already been exposed. -/
def Prop47StoppedProfileProp49Estimate
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (A : ℕ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i a (r : StageIndex),
    alphaValue (tripleAlphaIndex a r) ≤ kappaTwo →
    simpleRandomWalkLaw
        (prop47SequentialScreenEvent profiles cStar m i a r) ≤
      sourceProp49ScreenRate m A
          (alphaValue (tripleAlphaIndex a r)) *
        simpleRandomWalkLaw (prop47History profiles cStar m i a r.1)

/-- One-coordinate factor in Proposition 4.9 before the union over the at
most `log²(m+1)` candidate coordinates. -/
noncomputable def sourceProp49CoordinateRate
    (m A : ℕ) (alpha : ℝ) : ℝ≥0∞ :=
  (A : ℝ≥0∞) *
    ((m : ℝ≥0∞) + 1) ^ (-(kappaOne - (alpha + delta)))

/-- Direct finite-union estimate for the literal truncated
negative-binomial product measure supplied by the stopped map law. -/
theorem sourceTruncatedProfile_anyCoordinateInBand_le_card_mul
    {ι : Type*} [Fintype ι] (m : ℕ) (profile : ι → ℕ)
    (hprofile : ∀ x, profile x < m)
    (candidate : Finset ι) (band : ι → Set ℕ)
    (hbandMeasurable : ∀ x ∈ candidate, MeasurableSet (band x))
    {rate : ℝ≥0∞}
    (hband : ∀ x ∈ candidate,
      sourceTruncatedNegBinMeasure m (profile x) (band x) ≤ rate) :
    sourceTruncatedProfileMeasure m profile
        (anyCoordinateInBand candidate band) ≤
      (candidate.card : ℝ≥0∞) * rate := by
  letI (x : ι) : IsProbabilityMeasure
      (sourceTruncatedNegBinMeasure m (profile x)) :=
    ProbabilityTheory.cond_isProbabilityMeasure
      (negBinMeasure_sourceBelowSet_ne_zero m (profile x) (hprofile x))
  rw [sourceTruncatedProfileMeasure, anyCoordinateInBand]
  calc
    (Measure.pi fun x ↦ sourceTruncatedNegBinMeasure m (profile x))
          (⋃ x : ↥candidate, Function.eval x.1 ⁻¹' band x.1) ≤
        ∑ x : ↥candidate,
          (Measure.pi fun y ↦ sourceTruncatedNegBinMeasure m (profile y))
            (Function.eval x.1 ⁻¹' band x.1) :=
      measure_iUnion_fintype_le _ _
    _ = ∑ x : ↥candidate,
        sourceTruncatedNegBinMeasure m (profile x.1) (band x.1) := by
      apply Finset.sum_congr rfl
      intro x _hx
      calc
        (Measure.pi fun y ↦ sourceTruncatedNegBinMeasure m (profile y))
            (Function.eval x.1 ⁻¹' band x.1) =
            ((Measure.pi fun y ↦ sourceTruncatedNegBinMeasure m (profile y)).map
              (Function.eval x.1)) (band x.1) := by
          rw [Measure.map_apply (measurable_pi_apply x.1)
            (hbandMeasurable x.1 x.2)]
        _ = sourceTruncatedNegBinMeasure m (profile x.1) (band x.1) := by
          rw [(measurePreserving_eval
            (fun y ↦ sourceTruncatedNegBinMeasure m (profile y)) x.1).map_eq]
    _ ≤ ∑ _x : ↥candidate, rate := by
      exact Finset.sum_le_sum fun x _hx ↦ hband x.1 x.2
    _ = (candidate.card : ℝ≥0∞) * rate := by simp

/-- Internal analytic payload of a stopped source atom. Source-facing code
constructs this only through the four checked equation-(4.47) constructors
below; consequently no public disintegration premise supplies `map_law`.
The event-specific fields are the candidate band bounds and `screen_subset`. -/
structure StoppedTruncatedProp49AtomInput
    {ι : Type*} [Fintype ι]
    (m k A : ℕ) (alpha : ℝ) (screen : Set Path) where
  atom : Set Path
  measurable_atom : MeasurableSet atom
  lazyVector : Path → ι → ℕ
  nextDirection : Path → Direction
  profile : ι → ℕ
  profile_lt : ∀ x, profile x < m
  measurable_joint : Measurable fun s ↦ (lazyVector s, nextDirection s)
  map_law :
    (simpleRandomWalkLaw.restrict atom).map
        (fun s ↦ (lazyVector s, nextDirection s)) =
      simpleRandomWalkLaw atom •
        ((sourceTruncatedProfileMeasure m profile).prod directionLaw)
  candidate : Finset ι
  narrowBand : ι → Set ℕ
  narrowBand_measurable : ∀ x ∈ candidate, MeasurableSet (narrowBand x)
  candidate_card : (candidate.card : ℝ) ≤ Real.log ((m : ℝ) + 1) ^ 2
  coordinate_bound : ∀ x ∈ candidate,
    sourceTruncatedNegBinMeasure m (profile x) (narrowBand x) ≤
      sourceProp49CoordinateRate m A alpha
  screen_subset :
    atom ∩ screen ⊆ atom ∩
      (fun s ↦ (lazyVector s, nextDirection s)) ⁻¹'
        (anyCoordinateInBand candidate narrowBand ×ˢ Set.univ)

theorem StoppedTruncatedProp49AtomInput.profile_union_le
    {ι : Type*} [Fintype ι]
    {m k A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : @StoppedTruncatedProp49AtomInput ι _ m k A alpha screen) :
    sourceTruncatedProfileMeasure m D.profile
        (anyCoordinateInBand D.candidate D.narrowBand) ≤
      sourceProp49ScreenRate m A alpha := by
  have hfinite := sourceTruncatedProfile_anyCoordinateInBand_le_card_mul
    m D.profile D.profile_lt D.candidate D.narrowBand
      D.narrowBand_measurable D.coordinate_bound
  have hcardENN : (D.candidate.card : ℝ≥0∞) ≤
      ENNReal.ofReal (Real.log ((m : ℝ) + 1) ^ 2) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal D.candidate_card
  calc
    sourceTruncatedProfileMeasure m D.profile
        (anyCoordinateInBand D.candidate D.narrowBand) ≤
      (D.candidate.card : ℝ≥0∞) *
        sourceProp49CoordinateRate m A alpha := hfinite
    _ ≤ ENNReal.ofReal (Real.log ((m : ℝ) + 1) ^ 2) *
        sourceProp49CoordinateRate m A alpha := by gcongr
    _ = sourceProp49ScreenRate m A alpha := by
      rw [sourceProp49CoordinateRate, sourceProp49ScreenRate]
      ring

/-- The literal stopped truncated-NB map law and the narrow-band inclusion
imply the conditional Proposition-4.9 estimate on this one source atom. -/
theorem StoppedTruncatedProp49AtomInput.conditional_screen_le
    {ι : Type*} [Fintype ι]
    {m k A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : @StoppedTruncatedProp49AtomInput ι _ m k A alpha screen) :
    simpleRandomWalkLaw[|D.atom] (D.atom ∩ screen) ≤
      sourceProp49ScreenRate m A alpha := by
  let U : Set (ι → ℕ) :=
    anyCoordinateInBand D.candidate D.narrowBand
  let B : Set ((ι → ℕ) × Direction) := U ×ˢ Set.univ
  have hU : MeasurableSet U :=
    measurableSet_anyCoordinateInBand D.candidate D.narrowBand
      D.narrowBand_measurable
  have hB : MeasurableSet B := hU.prod MeasurableSet.univ
  have htarget :
      ((sourceTruncatedProfileMeasure m D.profile).prod directionLaw) B =
        sourceTruncatedProfileMeasure m D.profile U := by
    change ((sourceTruncatedProfileMeasure m D.profile).prod directionLaw)
      (U ×ˢ Set.univ) = sourceTruncatedProfileMeasure m D.profile U
    rw [Measure.prod_prod, measure_univ, mul_one]
  have hmapEvent :
      simpleRandomWalkLaw
          (D.atom ∩ (fun s ↦ (D.lazyVector s, D.nextDirection s)) ⁻¹' B) =
        simpleRandomWalkLaw D.atom *
          sourceTruncatedProfileMeasure m D.profile U := by
    calc
      simpleRandomWalkLaw
          (D.atom ∩ (fun s ↦ (D.lazyVector s, D.nextDirection s)) ⁻¹' B) =
          (simpleRandomWalkLaw.restrict D.atom)
            ((fun s ↦ (D.lazyVector s, D.nextDirection s)) ⁻¹' B) := by
        rw [Measure.restrict_apply (hB.preimage D.measurable_joint), inter_comm]
      _ = ((simpleRandomWalkLaw.restrict D.atom).map
            (fun s ↦ (D.lazyVector s, D.nextDirection s))) B := by
        rw [Measure.map_apply D.measurable_joint hB]
      _ = (simpleRandomWalkLaw D.atom •
            ((sourceTruncatedProfileMeasure m D.profile).prod directionLaw)) B := by
        rw [D.map_law]
      _ = simpleRandomWalkLaw D.atom *
          sourceTruncatedProfileMeasure m D.profile U := by
        rw [Measure.smul_apply, smul_eq_mul, htarget]
  have hnum : simpleRandomWalkLaw (D.atom ∩ screen) ≤
      simpleRandomWalkLaw D.atom *
        sourceTruncatedProfileMeasure m D.profile U := by
    exact (measure_mono D.screen_subset).trans hmapEvent.le
  have hinter : D.atom ∩ (D.atom ∩ screen) = D.atom ∩ screen := by
    ext s
    simp only [Set.mem_inter_iff]
    tauto
  rw [ProbabilityTheory.cond_apply D.measurable_atom, hinter]
  by_cases hzero : simpleRandomWalkLaw D.atom = 0
  · have hnumzero : simpleRandomWalkLaw (D.atom ∩ screen) = 0 :=
      measure_mono_null Set.inter_subset_left hzero
    simp [hzero, hnumzero]
  · calc
      (simpleRandomWalkLaw D.atom)⁻¹ *
          simpleRandomWalkLaw (D.atom ∩ screen) ≤
        (simpleRandomWalkLaw D.atom)⁻¹ *
          (simpleRandomWalkLaw D.atom *
            sourceTruncatedProfileMeasure m D.profile U) := by gcongr
      _ = sourceTruncatedProfileMeasure m D.profile U := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hzero
          (measure_ne_top simpleRandomWalkLaw D.atom), one_mul]
      _ ≤ sourceProp49ScreenRate m A alpha := D.profile_union_le

/-- The unnormalized form of the one-atom Proposition-4.9 estimate.  This is
the form used when summing a measurable disintegration: unlike the
conditional-probability statement, it remains meaningful on zero-mass
atoms. -/
theorem StoppedTruncatedProp49AtomInput.screen_measure_le
    {ι : Type*} [Fintype ι]
    {m k A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : @StoppedTruncatedProp49AtomInput ι _ m k A alpha screen) :
    simpleRandomWalkLaw (D.atom ∩ screen) ≤
      sourceProp49ScreenRate m A alpha * simpleRandomWalkLaw D.atom := by
  let U : Set (ι → ℕ) :=
    anyCoordinateInBand D.candidate D.narrowBand
  let B : Set ((ι → ℕ) × Direction) := U ×ˢ Set.univ
  have hU : MeasurableSet U :=
    measurableSet_anyCoordinateInBand D.candidate D.narrowBand
      D.narrowBand_measurable
  have hB : MeasurableSet B := hU.prod MeasurableSet.univ
  have htarget :
      ((sourceTruncatedProfileMeasure m D.profile).prod directionLaw) B =
        sourceTruncatedProfileMeasure m D.profile U := by
    change ((sourceTruncatedProfileMeasure m D.profile).prod directionLaw)
      (U ×ˢ Set.univ) = sourceTruncatedProfileMeasure m D.profile U
    rw [Measure.prod_prod, measure_univ, mul_one]
  have hmapEvent :
      simpleRandomWalkLaw
          (D.atom ∩ (fun s ↦ (D.lazyVector s, D.nextDirection s)) ⁻¹' B) =
        simpleRandomWalkLaw D.atom *
          sourceTruncatedProfileMeasure m D.profile U := by
    calc
      simpleRandomWalkLaw
          (D.atom ∩ (fun s ↦ (D.lazyVector s, D.nextDirection s)) ⁻¹' B) =
          (simpleRandomWalkLaw.restrict D.atom)
            ((fun s ↦ (D.lazyVector s, D.nextDirection s)) ⁻¹' B) := by
        rw [Measure.restrict_apply (hB.preimage D.measurable_joint), inter_comm]
      _ = ((simpleRandomWalkLaw.restrict D.atom).map
            (fun s ↦ (D.lazyVector s, D.nextDirection s))) B := by
        rw [Measure.map_apply D.measurable_joint hB]
      _ = (simpleRandomWalkLaw D.atom •
            ((sourceTruncatedProfileMeasure m D.profile).prod directionLaw)) B := by
        rw [D.map_law]
      _ = simpleRandomWalkLaw D.atom *
          sourceTruncatedProfileMeasure m D.profile U := by
        rw [Measure.smul_apply, smul_eq_mul, htarget]
  calc
    simpleRandomWalkLaw (D.atom ∩ screen) ≤
        simpleRandomWalkLaw D.atom *
          sourceTruncatedProfileMeasure m D.profile U :=
      (measure_mono D.screen_subset).trans hmapEvent.le
    _ ≤ simpleRandomWalkLaw D.atom * sourceProp49ScreenRate m A alpha := by
      gcongr
      exact D.profile_union_le
    _ = sourceProp49ScreenRate m A alpha * simpleRandomWalkLaw D.atom := by
      rw [mul_comm]

/-- A history-refined source atom carrying the exact conditional product law
from HLOZ Proposition 4.3/4.3'.  All deterministic coordinate data and the
one-coordinate local-limit bound are inherited from the checked coarse atom
`D`; the sole new probabilistic field is the same truncated product law after
the finer history conditioning. -/
structure StoppedTruncatedProp49RefinedAtomMapLaw
    {ι : Type*} [Fintype ι]
    {m k A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : @StoppedTruncatedProp49AtomInput ι _ m k A alpha screen)
    (refinedAtom : Set Path) where
  measurable_atom : MeasurableSet refinedAtom
  subset_atom : refinedAtom ⊆ D.atom
  map_law :
    (simpleRandomWalkLaw.restrict refinedAtom).map
        (fun s ↦ (D.lazyVector s, D.nextDirection s)) =
      simpleRandomWalkLaw refinedAtom •
        ((sourceTruncatedProfileMeasure m D.profile).prod directionLaw)

/-- Regard a refined conditional law as an ordinary stopped Proposition-4.9
atom.  The narrow-band inclusion restricts monotonically from the coarse
atom, so it needs no new source premise. -/
noncomputable def StoppedTruncatedProp49RefinedAtomMapLaw.toInput
    {ι : Type*} [Fintype ι]
    {m k A : ℕ} {alpha : ℝ} {screen : Set Path}
    {D : @StoppedTruncatedProp49AtomInput ι _ m k A alpha screen}
    {refinedAtom : Set Path}
    (F : StoppedTruncatedProp49RefinedAtomMapLaw D refinedAtom) :
    @StoppedTruncatedProp49AtomInput ι _ m k A alpha screen where
  atom := refinedAtom
  measurable_atom := F.measurable_atom
  lazyVector := D.lazyVector
  nextDirection := D.nextDirection
  profile := D.profile
  profile_lt := D.profile_lt
  measurable_joint := D.measurable_joint
  map_law := F.map_law
  candidate := D.candidate
  narrowBand := D.narrowBand
  narrowBand_measurable := D.narrowBand_measurable
  candidate_card := D.candidate_card
  coordinate_bound := D.coordinate_bound
  screen_subset := by
    intro s hs
    have hs' := D.screen_subset ⟨F.subset_atom hs.1, hs.2⟩
    exact ⟨hs.1, hs'.2⟩

/-- The refined conditional product law implies the complete unnormalized
atomwise Proposition-4.9 screen estimate. -/
theorem StoppedTruncatedProp49RefinedAtomMapLaw.screen_measure_le
    {ι : Type*} [Fintype ι]
    {m k A : ℕ} {alpha : ℝ} {screen : Set Path}
    {D : @StoppedTruncatedProp49AtomInput ι _ m k A alpha screen}
    {refinedAtom : Set Path}
    (F : StoppedTruncatedProp49RefinedAtomMapLaw D refinedAtom) :
    simpleRandomWalkLaw (refinedAtom ∩ screen) ≤
      sourceProp49ScreenRate m A alpha *
        simpleRandomWalkLaw refinedAtom := by
  exact F.toInput.screen_measure_le

/-- Abstract active/complement product estimate.  It is the measure-theoretic
form of the tower step needed when the preceding sequential history is not
constant on a coarse stopped atom: the screen uses the active coordinates,
while the history is measurable from an independent complement statistic. -/
theorem measure_active_complement_le
    {Ω X Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSpace Z]
    (μ : Measure Ω) (atom : Set Ω) (x : Ω → X) (z : Ω → Z)
    (ν : Measure X) [IsProbabilityMeasure ν] (ρ : Measure Z) [SFinite ρ]
    (U : Set X) (H : Set Z) (rate : ℝ≥0∞)
    (hx : Measurable x) (hz : Measurable z)
    (hU : MeasurableSet U) (hH : MeasurableSet H)
    (hmap : (μ.restrict atom).map (fun w ↦ (x w, z w)) =
      μ atom • (ν.prod ρ))
    (hbound : ν U ≤ rate) :
    μ (atom ∩ z ⁻¹' H ∩ x ⁻¹' U) ≤
      rate * μ (atom ∩ z ⁻¹' H) := by
  have hf : Measurable (fun w ↦ (x w, z w)) := hx.prodMk hz
  have hUH : MeasurableSet (U ×ˢ H) := hU.prod hH
  have hUnivH : MeasurableSet ((Set.univ : Set X) ×ˢ H) :=
    MeasurableSet.univ.prod hH
  have hnum := congrArg (fun M : Measure (X × Z) ↦ M (U ×ˢ H)) hmap
  have hden := congrArg
    (fun M : Measure (X × Z) ↦ M ((Set.univ : Set X) ×ˢ H)) hmap
  rw [Measure.map_apply hf hUH,
    Measure.restrict_apply (hUH.preimage hf),
    Measure.smul_apply, smul_eq_mul, Measure.prod_prod] at hnum
  rw [Measure.map_apply hf hUnivH,
    Measure.restrict_apply (hUnivH.preimage hf),
    Measure.smul_apply, smul_eq_mul, Measure.prod_prod,
    measure_univ, one_mul] at hden
  have hnumSet : (fun w ↦ (x w, z w)) ⁻¹' (U ×ˢ H) ∩ atom =
      atom ∩ z ⁻¹' H ∩ x ⁻¹' U := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod]
    tauto
  have hdenSet : (fun w ↦ (x w, z w)) ⁻¹'
      ((Set.univ : Set X) ×ˢ H) ∩ atom = atom ∩ z ⁻¹' H := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod,
      Set.mem_univ, true_and]
    tauto
  rw [hnumSet] at hnum
  rw [hdenSet] at hden
  rw [hnum, hden]
  calc
    μ atom * (ν U * ρ H) ≤ μ atom * (rate * ρ H) := by gcongr
    _ = rate * (μ atom * ρ H) := by ac_rfl

/-- Source-facing replacement for the false assertion that the sequential
history is constant on a coarse stopped atom.  It records the exact missing
tower property: active lazy coordinates and a complement statistic have a
joint product law, and the preceding history is a complement preimage. -/
structure StoppedTruncatedProp49HistoryFactorization
    {ι : Type*} [Fintype ι]
    {m k A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : @StoppedTruncatedProp49AtomInput ι _ m k A alpha screen)
    (history : Set Path) where
  Z : Type
  [measurableSpaceZ : MeasurableSpace Z]
  complementLaw : Measure Z
  [sFiniteComplementLaw : SFinite complementLaw]
  complement : Path → Z
  measurable_complement : Measurable complement
  historySet : Set Z
  measurable_historySet : MeasurableSet historySet
  history_eq : D.atom ∩ history = D.atom ∩ complement ⁻¹' historySet
  joint_map_law :
    (simpleRandomWalkLaw.restrict D.atom).map
        (fun s ↦ ((D.lazyVector s, D.nextDirection s), complement s)) =
      simpleRandomWalkLaw D.atom •
        (((sourceTruncatedProfileMeasure m D.profile).prod directionLaw).prod
          complementLaw)

/-- The joint active/complement factorization gives the exact atomwise tower
estimate with the complete preceding history retained. -/
theorem StoppedTruncatedProp49HistoryFactorization.history_screen_le
    {ι : Type*} [Fintype ι]
    {m k A : ℕ} {alpha : ℝ} {screen history : Set Path}
    (D : @StoppedTruncatedProp49AtomInput ι _ m k A alpha screen)
    (F : StoppedTruncatedProp49HistoryFactorization D history) :
    simpleRandomWalkLaw (D.atom ∩ history ∩ screen) ≤
      sourceProp49ScreenRate m A alpha *
        simpleRandomWalkLaw (D.atom ∩ history) := by
  letI : MeasurableSpace F.Z := F.measurableSpaceZ
  letI : SFinite F.complementLaw := F.sFiniteComplementLaw
  letI (x : ι) : IsProbabilityMeasure
      (sourceTruncatedNegBinMeasure m (D.profile x)) :=
    ProbabilityTheory.cond_isProbabilityMeasure
      (negBinMeasure_sourceBelowSet_ne_zero m (D.profile x) (D.profile_lt x))
  letI : IsProbabilityMeasure (sourceTruncatedProfileMeasure m D.profile) := by
    unfold sourceTruncatedProfileMeasure
    infer_instance
  letI : IsProbabilityMeasure
      ((sourceTruncatedProfileMeasure m D.profile).prod directionLaw) :=
    inferInstance
  let U : Set (ι → ℕ) :=
    anyCoordinateInBand D.candidate D.narrowBand
  let B : Set ((ι → ℕ) × Direction) := U ×ˢ Set.univ
  let X : Path → ((ι → ℕ) × Direction) :=
    fun s ↦ (D.lazyVector s, D.nextDirection s)
  have hU : MeasurableSet U :=
    measurableSet_anyCoordinateInBand D.candidate D.narrowBand
      D.narrowBand_measurable
  have hB : MeasurableSet B := hU.prod MeasurableSet.univ
  have hBmass :
      ((sourceTruncatedProfileMeasure m D.profile).prod directionLaw) B =
        sourceTruncatedProfileMeasure m D.profile U := by
    dsimp [B]
    rw [Measure.prod_prod, measure_univ, mul_one]
  have hBound :
      ((sourceTruncatedProfileMeasure m D.profile).prod directionLaw) B ≤
        sourceProp49ScreenRate m A alpha := by
    rw [hBmass]
    exact D.profile_union_le
  have hProduct := measure_active_complement_le simpleRandomWalkLaw D.atom
    X F.complement
    ((sourceTruncatedProfileMeasure m D.profile).prod directionLaw)
    F.complementLaw B F.historySet (sourceProp49ScreenRate m A alpha)
    D.measurable_joint F.measurable_complement hB F.measurable_historySet
    F.joint_map_law hBound
  have hsubset : D.atom ∩ history ∩ screen ⊆
      D.atom ∩ F.complement ⁻¹' F.historySet ∩ X ⁻¹' B := by
    intro s hs
    have hc : s ∈ D.atom ∩ F.complement ⁻¹' F.historySet := by
      rw [← F.history_eq]
      exact hs.1
    have hx : s ∈ D.atom ∩ X ⁻¹' B :=
      D.screen_subset ⟨hs.1.1, hs.2⟩
    exact ⟨⟨hc.1, hc.2⟩, hx.2⟩
  calc
    simpleRandomWalkLaw (D.atom ∩ history ∩ screen) ≤
        simpleRandomWalkLaw
          (D.atom ∩ F.complement ⁻¹' F.historySet ∩ X ⁻¹' B) :=
      measure_mono hsubset
    _ ≤ sourceProp49ScreenRate m A alpha *
        simpleRandomWalkLaw (D.atom ∩ F.complement ⁻¹' F.historySet) :=
      hProduct
    _ = sourceProp49ScreenRate m A alpha *
        simpleRandomWalkLaw (D.atom ∩ history) := by rw [F.history_eq]

/-! ### Concrete equation-(4.47) atom constructors

The following four constructors are the source-facing boundary of this
connector.  In particular, their callers do not provide a product map law:
it is filled by the checked nonterminal and full-terminal stopped
reconstruction theorems. The remaining event-specific premises are exactly
the Proposition-4.9 one-coordinate tail and the deterministic inclusion of
the screened event in the corresponding union of narrow bands. -/

/-- Concrete unprimed-even/left-winner stopped atom. -/
noncomputable def unprimedEvenLeftWinnerProp49AtomInput {q : ℕ}
    (m k A : ℕ) (alpha : ℝ) (screen : Set Path)
    (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (hm : 0 < m) (hk : 0 < k) (hcard : C.card = k)
    (hfree : HLOZPairing.PairFree (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : UnprimedEvenOffBaseMixedCondition labels m C)
    (hterminal : stoppedTerminalBase labels ∈ C)
    (hne : (actualAdmissibleStoppedVectors m k labels
      (unprimedEvenSourceConstraint m k C labels)).Nonempty)
    (candidateBases : Finset (StoppedExternalBase (0, 0) labels))
    (candidate : Finset (ActiveFreeStoppedBase (0, 0) labels C
      (unprimedEvenLeftWinnerBases labels candidateBases)))
    (narrowBand : ActiveFreeStoppedBase (0, 0) labels C
      (unprimedEvenLeftWinnerBases labels candidateBases) → Set ℕ)
    (hprofile : ∀ x, activeFreeStoppedShape (0, 0) labels C
      (unprimedEvenLeftWinnerBases labels candidateBases) x < m)
    (hbandMeasurable : ∀ x ∈ candidate, MeasurableSet (narrowBand x))
    (hcardCandidate : (candidate.card : ℝ) ≤ Real.log ((m : ℝ) + 1) ^ 2)
    (hcoordinate : ∀ x ∈ candidate,
      sourceTruncatedNegBinMeasure m
          (activeFreeStoppedShape (0, 0) labels C
            (unprimedEvenLeftWinnerBases labels candidateBases) x)
          (narrowBand x) ≤ sourceProp49CoordinateRate m A alpha)
    (hinclusion :
      let atom := simpleRandomWalk ''
        (actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
          stoppedSourceCondition m k C)
      atom ∩ screen ⊆ atom ∩
        (fun s ↦
          (unprimedEvenActiveFreePathLazy m k C labels
              (unprimedEvenLeftWinnerBases labels candidateBases) s,
            unprimedEvenActiveFreePathNext m k C labels
              (unprimedEvenLeftWinnerBases labels candidateBases) s)) ⁻¹'
          (anyCoordinateInBand candidate narrowBand ×ˢ Set.univ)) :
    StoppedTruncatedProp49AtomInput
      (ι := ActiveFreeStoppedBase (0, 0) labels C
        (unprimedEvenLeftWinnerBases labels candidateBases))
      m k A alpha screen := by
  let activeBases := unprimedEvenLeftWinnerBases labels candidateBases
  let atom := simpleRandomWalk ''
    (actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
      stoppedSourceCondition m k C)
  have hEvent : MeasurableSet
      (actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
        stoppedSourceCondition m k C) := by
    rw [unprimedEven_source_partition m k C labels hm hk hfree]
    exact measurableSet_actualStoppedVectorEvent _ _ _ _
  refine
    { atom := atom
      measurable_atom :=
        measurableEmbedding_simpleRandomWalk.measurableSet_image.2 hEvent
      lazyVector := unprimedEvenActiveFreePathLazy m k C labels activeBases
      nextDirection := unprimedEvenActiveFreePathNext m k C labels activeBases
      profile := activeFreeStoppedShape (0, 0) labels C activeBases
      profile_lt := hprofile
      measurable_joint := ?_
      map_law := ?_
      candidate := candidate
      narrowBand := narrowBand
      narrowBand_measurable := hbandMeasurable
      candidate_card := hcardCandidate
      coordinate_bound := hcoordinate
      screen_subset := hinclusion }
  · exact (measurable_unprimedEvenActiveFreePathLazy
      m k C labels hnondist activeBases).prodMk
        (measurable_unprimedEvenActiveFreePathNext
          m k C labels hnondist activeBases)
  · exact unprimedEven_leftWinner_StoppedEquation447Atom_map_law
      m k C labels hnondist hm hk hcard hfree hoff hterminal hne
        candidateBases

/-- Concrete primed-odd/strict-right-winner stopped atom.  The strict filter
makes this branch disjoint from the tie-left unprimed branch. -/
noncomputable def primedOddStrictRightWinnerProp49AtomInput {q : ℕ}
    (m k A : ℕ) (alpha : ℝ) (screen : Set Path)
    (C : Finset Site) (first : Direction) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (hm : 0 < m) (hk : 0 < k) (hcard : C.card = k)
    (hfree : HLOZPairing.PairFree (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : PrimedOddOffBaseMixedCondition first labels m C)
    (hterminal : primedStoppedTerminalSite first labels ∈ C)
    (hne : (actualAdmissiblePrimedStoppedVectors m k first labels
      (primedOddSourceConstraint m k C first labels)).Nonempty)
    (candidateBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels))
    (candidate : Finset (ActiveFreeStoppedBase (primedInitialBase first)
      labels C (primedOddStrictRightWinnerBases first labels candidateBases)))
    (narrowBand : ActiveFreeStoppedBase (primedInitialBase first) labels C
      (primedOddStrictRightWinnerBases first labels candidateBases) → Set ℕ)
    (hprofile : ∀ x,
      activeFreeStoppedShape (primedInitialBase first) labels C
        (primedOddStrictRightWinnerBases first labels candidateBases) x < m)
    (hbandMeasurable : ∀ x ∈ candidate, MeasurableSet (narrowBand x))
    (hcardCandidate : (candidate.card : ℝ) ≤ Real.log ((m : ℝ) + 1) ^ 2)
    (hcoordinate : ∀ x ∈ candidate,
      sourceTruncatedNegBinMeasure m
          (activeFreeStoppedShape (primedInitialBase first) labels C
            (primedOddStrictRightWinnerBases first labels candidateBases) x)
          (narrowBand x) ≤ sourceProp49CoordinateRate m A alpha)
    (hinclusion :
      let atom := simpleRandomWalk ''
        (actualPrimedStoppedVectorEvent m k first labels
            (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C)
      atom ∩ screen ⊆ atom ∩
        (fun s ↦
          (primedOddActiveFreePathLazy m k C first labels
              (primedOddStrictRightWinnerBases first labels candidateBases) s,
            primedOddActiveFreePathNext m k C first labels
              (primedOddStrictRightWinnerBases first labels candidateBases) s)) ⁻¹'
          (anyCoordinateInBand candidate narrowBand ×ˢ Set.univ)) :
    StoppedTruncatedProp49AtomInput
      (ι := ActiveFreeStoppedBase (primedInitialBase first) labels C
        (primedOddStrictRightWinnerBases first labels candidateBases))
      m k A alpha screen := by
  let activeBases := primedOddStrictRightWinnerBases first labels candidateBases
  let atom := simpleRandomWalk ''
    (actualPrimedStoppedVectorEvent m k first labels
        (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C)
  have hEvent : MeasurableSet
      (actualPrimedStoppedVectorEvent m k first labels
          (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C) := by
    rw [primedOdd_source_partition m k C first labels hm hk hfree]
    unfold actualPrimedStoppedVectorEvent
    exact MeasurableSet.iUnion fun v ↦ MeasurableSet.iUnion fun _ ↦
      measurableSet_stoppedPrefixAtom
        (reconstructedPrimedStoppedPrefix first labels v)
  refine
    { atom := atom
      measurable_atom :=
        measurableEmbedding_simpleRandomWalk.measurableSet_image.2 hEvent
      lazyVector := primedOddActiveFreePathLazy m k C first labels activeBases
      nextDirection := primedOddActiveFreePathNext m k C first labels activeBases
      profile := activeFreeStoppedShape (primedInitialBase first) labels C activeBases
      profile_lt := hprofile
      measurable_joint := ?_
      map_law := ?_
      candidate := candidate
      narrowBand := narrowBand
      narrowBand_measurable := hbandMeasurable
      candidate_card := hcardCandidate
      coordinate_bound := hcoordinate
      screen_subset := hinclusion }
  · exact (measurable_primedOddActiveFreePathLazy
      m k C first labels hnondist activeBases).prodMk
        (measurable_primedOddActiveFreePathNext
          m k C first labels hnondist activeBases)
  · exact primedOdd_strictRightWinner_StoppedEquation447Atom_map_law
      m k C first labels hnondist hm hk hcard hfree hoff hterminal hne
        candidateBases

/-- Concrete unprimed-odd terminal/tie-left stopped atom. The retained
direction is the first coordinate after the complete terminal pair. -/
noncomputable def unprimedOddTerminalTieLeftProp49AtomInput {q : ℕ}
    (m k A : ℕ) (alpha : ℝ) (screen : Set Path)
    (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (terminal : IncrementPair)
    (hm : 0 < m) (hk : 0 < k) (hcard : C.card = k)
    (hfree : HLOZPairing.PairFree (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : UnprimedOddOffBaseMixedCondition labels terminal m C)
    (hterminal : stoppedTerminalBase labels +
      directionStep (terminal 0) ∈ C)
    (hne : (actualAdmissibleOddStoppedVectors m k labels terminal
      (unprimedOddSourceConstraint m k C labels terminal)).Nonempty)
    (candidateBases : Finset (StoppedExternalBase (0, 0) labels))
    (candidate : Finset (ActiveFreeStoppedBase (0, 0) labels C
      (unprimedOddTieLeftWinnerBases labels
        (unprimedOddTerminalExternalRight labels terminal) candidateBases)))
    (narrowBand : ActiveFreeStoppedBase (0, 0) labels C
      (unprimedOddTieLeftWinnerBases labels
        (unprimedOddTerminalExternalRight labels terminal) candidateBases) → Set ℕ)
    (hprofile : ∀ x, activeFreeStoppedShape (0, 0) labels C
      (unprimedOddTieLeftWinnerBases labels
        (unprimedOddTerminalExternalRight labels terminal) candidateBases) x < m)
    (hbandMeasurable : ∀ x ∈ candidate, MeasurableSet (narrowBand x))
    (hcardCandidate : (candidate.card : ℝ) ≤ Real.log ((m : ℝ) + 1) ^ 2)
    (hcoordinate : ∀ x ∈ candidate,
      sourceTruncatedNegBinMeasure m
          (activeFreeStoppedShape (0, 0) labels C
            (unprimedOddTieLeftWinnerBases labels
              (unprimedOddTerminalExternalRight labels terminal)
                candidateBases) x)
          (narrowBand x) ≤ sourceProp49CoordinateRate m A alpha)
    (hinclusion :
      let atom := simpleRandomWalk ''
        (actualOddStoppedVectorEvent m k labels terminal
            (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C)
      atom ∩ screen ⊆ atom ∩
        (fun s ↦
          (unprimedOddActiveFreePathLazy m k C labels terminal
              (unprimedOddTieLeftWinnerBases labels
                (unprimedOddTerminalExternalRight labels terminal)
                  candidateBases) s,
            unprimedOddActiveFreePathNext m k C labels terminal
              (unprimedOddTieLeftWinnerBases labels
                (unprimedOddTerminalExternalRight labels terminal)
                  candidateBases) s)) ⁻¹'
          (anyCoordinateInBand candidate narrowBand ×ˢ Set.univ)) :
    StoppedTruncatedProp49AtomInput
      (ι := ActiveFreeStoppedBase (0, 0) labels C
        (unprimedOddTieLeftWinnerBases labels
          (unprimedOddTerminalExternalRight labels terminal) candidateBases))
      m k A alpha screen := by
  let activeBases := unprimedOddTieLeftWinnerBases labels
    (unprimedOddTerminalExternalRight labels terminal) candidateBases
  let atom := simpleRandomWalk ''
    (actualOddStoppedVectorEvent m k labels terminal
        (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C)
  have hEvent : MeasurableSet
      (actualOddStoppedVectorEvent m k labels terminal
          (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C) := by
    rw [unprimedOdd_source_partition m k C labels terminal hm hk hfree]
    unfold actualOddStoppedVectorEvent
    exact MeasurableSet.iUnion fun v ↦ MeasurableSet.iUnion fun _ ↦
      measurableSet_stoppedPrefixAtom
        (reconstructedOddStoppedPrefix labels v terminal)
  refine
    { atom := atom
      measurable_atom :=
        measurableEmbedding_simpleRandomWalk.measurableSet_image.2 hEvent
      lazyVector := unprimedOddActiveFreePathLazy
        m k C labels terminal activeBases
      nextDirection := unprimedOddActiveFreePathNext
        m k C labels terminal activeBases
      profile := activeFreeStoppedShape (0, 0) labels C activeBases
      profile_lt := hprofile
      measurable_joint := ?_
      map_law := ?_
      candidate := candidate
      narrowBand := narrowBand
      narrowBand_measurable := hbandMeasurable
      candidate_card := hcardCandidate
      coordinate_bound := hcoordinate
      screen_subset := hinclusion }
  · exact (measurable_unprimedOddActiveFreePathLazy
      m k C labels hnondist terminal activeBases).prodMk
        (measurable_unprimedOddActiveFreePathNext
          m k C labels hnondist terminal activeBases)
  · exact unprimedOdd_sourceTieLeftWinner_StoppedEquation447Atom_map_law
      m k C labels hnondist terminal hm hk hcard hfree hoff hterminal
        candidateBases hne

/-- Concrete primed-even terminal/strict-right stopped atom. -/
noncomputable def primedEvenTerminalStrictRightProp49AtomInput {q : ℕ}
    (m k A : ℕ) (alpha : ℝ) (screen : Set Path)
    (C : Finset Site) (first : Direction) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (terminal : IncrementPair)
    (hm : 0 < m) (hk : 0 < k) (hcard : C.card = k)
    (hfree : HLOZPairing.PairFree (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : PrimedEvenOffBaseMixedCondition first labels terminal m C)
    (hterminal : primedStoppedTerminalSite first labels +
      directionStep (terminal 0) ∈ C)
    (hne : (actualAdmissiblePrimedTerminalVectors m k first labels terminal
      (primedEvenSourceConstraint m k C first labels terminal)).Nonempty)
    (candidateBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels))
    (candidate : Finset (ActiveFreeStoppedBase (primedInitialBase first)
      labels C (primedEvenStrictRightWinnerBases first labels
        (primedEvenTerminalExternalLeft first labels terminal) candidateBases)))
    (narrowBand : ActiveFreeStoppedBase (primedInitialBase first) labels C
      (primedEvenStrictRightWinnerBases first labels
        (primedEvenTerminalExternalLeft first labels terminal)
          candidateBases) → Set ℕ)
    (hprofile : ∀ x,
      activeFreeStoppedShape (primedInitialBase first) labels C
        (primedEvenStrictRightWinnerBases first labels
          (primedEvenTerminalExternalLeft first labels terminal)
            candidateBases) x < m)
    (hbandMeasurable : ∀ x ∈ candidate, MeasurableSet (narrowBand x))
    (hcardCandidate : (candidate.card : ℝ) ≤ Real.log ((m : ℝ) + 1) ^ 2)
    (hcoordinate : ∀ x ∈ candidate,
      sourceTruncatedNegBinMeasure m
          (activeFreeStoppedShape (primedInitialBase first) labels C
            (primedEvenStrictRightWinnerBases first labels
              (primedEvenTerminalExternalLeft first labels terminal)
                candidateBases) x)
          (narrowBand x) ≤ sourceProp49CoordinateRate m A alpha)
    (hinclusion :
      let atom := simpleRandomWalk ''
        (actualPrimedTerminalVectorEvent m k first labels terminal
            (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C)
      atom ∩ screen ⊆ atom ∩
        (fun s ↦
          (primedEvenActiveFreePathLazy m k C first labels terminal
              (primedEvenStrictRightWinnerBases first labels
                (primedEvenTerminalExternalLeft first labels terminal)
                  candidateBases) s,
            primedEvenActiveFreePathNext m k C first labels terminal
              (primedEvenStrictRightWinnerBases first labels
                (primedEvenTerminalExternalLeft first labels terminal)
                  candidateBases) s)) ⁻¹'
          (anyCoordinateInBand candidate narrowBand ×ˢ Set.univ)) :
    StoppedTruncatedProp49AtomInput
      (ι := ActiveFreeStoppedBase (primedInitialBase first) labels C
        (primedEvenStrictRightWinnerBases first labels
          (primedEvenTerminalExternalLeft first labels terminal)
            candidateBases))
      m k A alpha screen := by
  let activeBases := primedEvenStrictRightWinnerBases first labels
    (primedEvenTerminalExternalLeft first labels terminal) candidateBases
  let atom := simpleRandomWalk ''
    (actualPrimedTerminalVectorEvent m k first labels terminal
        (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C)
  have hEvent : MeasurableSet
      (actualPrimedTerminalVectorEvent m k first labels terminal
          (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C) := by
    rw [primedEven_source_partition m k C first labels terminal hm hk hfree]
    unfold actualPrimedTerminalVectorEvent
    exact MeasurableSet.iUnion fun v ↦ MeasurableSet.iUnion fun _ ↦
      measurableSet_stoppedPrefixAtom
        (reconstructedPrimedTerminalStoppedPrefix first labels v terminal)
  refine
    { atom := atom
      measurable_atom :=
        measurableEmbedding_simpleRandomWalk.measurableSet_image.2 hEvent
      lazyVector := primedEvenActiveFreePathLazy
        m k C first labels terminal activeBases
      nextDirection := primedEvenActiveFreePathNext
        m k C first labels terminal activeBases
      profile := activeFreeStoppedShape
        (primedInitialBase first) labels C activeBases
      profile_lt := hprofile
      measurable_joint := ?_
      map_law := ?_
      candidate := candidate
      narrowBand := narrowBand
      narrowBand_measurable := hbandMeasurable
      candidate_card := hcardCandidate
      coordinate_bound := hcoordinate
      screen_subset := hinclusion }
  · exact (measurable_primedEvenActiveFreePathLazy
      m k C first labels hnondist terminal activeBases).prodMk
        (measurable_primedEvenActiveFreePathNext
          m k C first labels hnondist terminal activeBases)
  · exact primedEven_sourceStrictRightWinner_StoppedEquation447Atom_map_law
      m k C first labels hnondist terminal hm hk hcard hfree hoff hterminal
        candidateBases hne

/-- Source data for an unprimed left-winner atom.  Notice that this record
contains no law field: the law is reconstructed by
`unprimedEvenLeftWinnerProp49AtomInput`. -/
structure UnprimedEvenLeftWinnerProp49AtomData
    (m k A : ℕ) (alpha : ℝ) (screen : Set Path) where
  q : ℕ
  C : Finset Site
  labels : Fin q → IncrementPair
  nondistinguished : ∀ i, labels i ≠ distinguishedIncrementPair
  m_pos : 0 < m
  k_pos : 0 < k
  creation_card : C.card = k
  creation_pairFree : HLOZPairing.PairFree
    (HLOZPairing.XPair HLOZPairing.east) C
  offBase : UnprimedEvenOffBaseMixedCondition labels m C
  terminal_mem : stoppedTerminalBase labels ∈ C
  admissible_nonempty : (actualAdmissibleStoppedVectors m k labels
    (unprimedEvenSourceConstraint m k C labels)).Nonempty
  candidateBases : Finset (StoppedExternalBase (0, 0) labels)
  candidate : Finset (ActiveFreeStoppedBase (0, 0) labels C
    (unprimedEvenLeftWinnerBases labels candidateBases))
  candidate_card : (candidate.card : ℝ) ≤ Real.log ((m : ℝ) + 1) ^ 2
  comparisonCoeff : ℕ
  windowGrowth : SourceWindowGrowth comparisonCoeff m
  profile_window : ∀ x ∈ candidate, InEquation458ExternalWindow
    comparisonCoeff m (activeFreeStoppedShape (0, 0) labels C
      (unprimedEvenLeftWinnerBases labels candidateBases) x)
  alpha_nonneg : 0 ≤ alpha + delta
  alpha_lt : alpha + delta < kappaOne
  coefficient : 8 * Real.exp (sourceComparisonExponent comparisonCoeff) ≤ A
  screen_subset :
    let atom := simpleRandomWalk ''
      (actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
        stoppedSourceCondition m k C)
    atom ∩ screen ⊆ atom ∩
      (fun s ↦
        (unprimedEvenActiveFreePathLazy m k C labels
            (unprimedEvenLeftWinnerBases labels candidateBases) s,
          unprimedEvenActiveFreePathNext m k C labels
            (unprimedEvenLeftWinnerBases labels candidateBases) s)) ⁻¹'
        (anyCoordinateInBand candidate (fun x ↦ sourceProp49NarrowBand m
          (activeFreeStoppedShape (0, 0) labels C
            (unprimedEvenLeftWinnerBases labels candidateBases) x) alpha) ×ˢ
          Set.univ)

noncomputable def UnprimedEvenLeftWinnerProp49AtomData.atom
    {m k A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : UnprimedEvenLeftWinnerProp49AtomData m k A alpha screen) : Set Path :=
  simpleRandomWalk ''
    (actualStoppedVectorEvent m k D.labels (stoppedRunVectorBox D.q m) ∩
      stoppedSourceCondition m k D.C)

noncomputable def UnprimedEvenLeftWinnerProp49AtomData.toInput
    {m k A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : UnprimedEvenLeftWinnerProp49AtomData m k A alpha screen) :
    StoppedTruncatedProp49AtomInput
      (ι := ActiveFreeStoppedBase (0, 0) D.labels D.C
        (unprimedEvenLeftWinnerBases D.labels D.candidateBases))
      m k A alpha screen :=
  unprimedEvenLeftWinnerProp49AtomInput m k A alpha screen D.C D.labels
    D.nondistinguished D.m_pos D.k_pos D.creation_card D.creation_pairFree
    D.offBase D.terminal_mem D.admissible_nonempty D.candidateBases
    D.candidate (fun x ↦ sourceProp49NarrowBand m
      (activeFreeStoppedShape (0, 0) D.labels D.C
        (unprimedEvenLeftWinnerBases D.labels D.candidateBases) x) alpha)
    (unprimedEven_leftWinner_profile_lt_of_nonempty m k D.C D.labels
      D.m_pos D.creation_card D.creation_pairFree D.offBase D.terminal_mem
      D.admissible_nonempty D.candidateBases)
    (fun x hx ↦ measurableSet_sourceProp49NarrowBand _ _ _)
    D.candidate_card (fun x hx ↦ by
      rw [sourceProp49CoordinateRate]
      exact sourceTruncatedNegBinMeasure_sourceProp49NarrowBand_le
        D.comparisonCoeff m
          (activeFreeStoppedShape (0, 0) D.labels D.C
            (unprimedEvenLeftWinnerBases D.labels D.candidateBases) x)
          A alpha D.windowGrowth (D.profile_window x hx) D.alpha_nonneg
            D.alpha_lt D.coefficient)
    D.screen_subset

/-- Source data for the disjoint primed strict-right-winner atom. -/
structure PrimedOddStrictRightWinnerProp49AtomData
    (m k A : ℕ) (alpha : ℝ) (screen : Set Path) where
  q : ℕ
  C : Finset Site
  first : Direction
  labels : Fin q → IncrementPair
  nondistinguished : ∀ i, labels i ≠ primedDistinguishedIncrementPair
  m_pos : 0 < m
  k_pos : 0 < k
  creation_card : C.card = k
  creation_pairFree : HLOZPairing.PairFree
    (HLOZPairing.XPair HLOZPairing.east) C
  offBase : PrimedOddOffBaseMixedCondition first labels m C
  terminal_mem : primedStoppedTerminalSite first labels ∈ C
  admissible_nonempty : (actualAdmissiblePrimedStoppedVectors m k first labels
    (primedOddSourceConstraint m k C first labels)).Nonempty
  candidateBases : Finset
    (StoppedExternalBase (primedInitialBase first) labels)
  candidate : Finset (ActiveFreeStoppedBase (primedInitialBase first) labels C
    (primedOddStrictRightWinnerBases first labels candidateBases))
  candidate_card : (candidate.card : ℝ) ≤ Real.log ((m : ℝ) + 1) ^ 2
  comparisonCoeff : ℕ
  windowGrowth : SourceWindowGrowth comparisonCoeff m
  profile_window : ∀ x ∈ candidate, InEquation458ExternalWindow
    comparisonCoeff m (activeFreeStoppedShape (primedInitialBase first) labels C
      (primedOddStrictRightWinnerBases first labels candidateBases) x)
  alpha_nonneg : 0 ≤ alpha + delta
  alpha_lt : alpha + delta < kappaOne
  coefficient : 8 * Real.exp (sourceComparisonExponent comparisonCoeff) ≤ A
  screen_subset :
    let atom := simpleRandomWalk ''
      (actualPrimedStoppedVectorEvent m k first labels
          (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C)
    atom ∩ screen ⊆ atom ∩
      (fun s ↦
        (primedOddActiveFreePathLazy m k C first labels
            (primedOddStrictRightWinnerBases first labels candidateBases) s,
          primedOddActiveFreePathNext m k C first labels
            (primedOddStrictRightWinnerBases first labels candidateBases) s)) ⁻¹'
        (anyCoordinateInBand candidate (fun x ↦ sourceProp49NarrowBand m
          (activeFreeStoppedShape (primedInitialBase first) labels C
            (primedOddStrictRightWinnerBases first labels candidateBases) x) alpha) ×ˢ
          Set.univ)

noncomputable def PrimedOddStrictRightWinnerProp49AtomData.atom
    {m k A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : PrimedOddStrictRightWinnerProp49AtomData m k A alpha screen) : Set Path :=
  simpleRandomWalk ''
    (actualPrimedStoppedVectorEvent m k D.first D.labels
        (stoppedRunVectorBox D.q m) ∩ stoppedSourceCondition m k D.C)

noncomputable def PrimedOddStrictRightWinnerProp49AtomData.toInput
    {m k A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : PrimedOddStrictRightWinnerProp49AtomData m k A alpha screen) :
    StoppedTruncatedProp49AtomInput
      (ι := ActiveFreeStoppedBase (primedInitialBase D.first) D.labels D.C
        (primedOddStrictRightWinnerBases D.first D.labels D.candidateBases))
      m k A alpha screen :=
  primedOddStrictRightWinnerProp49AtomInput m k A alpha screen D.C D.first
    D.labels D.nondistinguished D.m_pos D.k_pos D.creation_card
    D.creation_pairFree D.offBase D.terminal_mem D.admissible_nonempty
    D.candidateBases D.candidate (fun x ↦ sourceProp49NarrowBand m
      (activeFreeStoppedShape (primedInitialBase D.first) D.labels D.C
        (primedOddStrictRightWinnerBases D.first D.labels D.candidateBases) x) alpha)
    (primedOdd_strictRightWinner_profile_lt_of_nonempty m k D.C D.first
      D.labels D.m_pos D.creation_card D.creation_pairFree D.offBase
      D.terminal_mem D.admissible_nonempty D.candidateBases)
    (fun x hx ↦ measurableSet_sourceProp49NarrowBand _ _ _)
    D.candidate_card (fun x hx ↦ by
      rw [sourceProp49CoordinateRate]
      exact sourceTruncatedNegBinMeasure_sourceProp49NarrowBand_le
        D.comparisonCoeff m
          (activeFreeStoppedShape (primedInitialBase D.first) D.labels D.C
            (primedOddStrictRightWinnerBases D.first D.labels D.candidateBases) x)
          A alpha D.windowGrowth (D.profile_window x hx) D.alpha_nonneg
            D.alpha_lt D.coefficient)
    D.screen_subset

/-- Source data for the unprimed-odd terminal tie-left atom. -/
structure UnprimedOddTerminalTieLeftProp49AtomData
    (m k A : ℕ) (alpha : ℝ) (screen : Set Path) where
  q : ℕ
  C : Finset Site
  labels : Fin q → IncrementPair
  nondistinguished : ∀ i, labels i ≠ distinguishedIncrementPair
  terminal : IncrementPair
  m_pos : 0 < m
  k_pos : 0 < k
  creation_card : C.card = k
  creation_pairFree : HLOZPairing.PairFree
    (HLOZPairing.XPair HLOZPairing.east) C
  offBase : UnprimedOddOffBaseMixedCondition labels terminal m C
  terminal_mem : stoppedTerminalBase labels +
    directionStep (terminal 0) ∈ C
  admissible_nonempty : (actualAdmissibleOddStoppedVectors m k labels terminal
    (unprimedOddSourceConstraint m k C labels terminal)).Nonempty
  candidateBases : Finset (StoppedExternalBase (0, 0) labels)
  candidate : Finset (ActiveFreeStoppedBase (0, 0) labels C
    (unprimedOddTieLeftWinnerBases labels
      (unprimedOddTerminalExternalRight labels terminal) candidateBases))
  candidate_card : (candidate.card : ℝ) ≤ Real.log ((m : ℝ) + 1) ^ 2
  comparisonCoeff : ℕ
  windowGrowth : SourceWindowGrowth comparisonCoeff m
  profile_window : ∀ x ∈ candidate, InEquation458ExternalWindow
    comparisonCoeff m (activeFreeStoppedShape (0, 0) labels C
      (unprimedOddTieLeftWinnerBases labels
        (unprimedOddTerminalExternalRight labels terminal) candidateBases) x)
  alpha_nonneg : 0 ≤ alpha + delta
  alpha_lt : alpha + delta < kappaOne
  coefficient : 8 * Real.exp (sourceComparisonExponent comparisonCoeff) ≤ A
  screen_subset :
    let atom := simpleRandomWalk ''
      (actualOddStoppedVectorEvent m k labels terminal
          (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C)
    atom ∩ screen ⊆ atom ∩
      (fun s ↦
        (unprimedOddActiveFreePathLazy m k C labels terminal
            (unprimedOddTieLeftWinnerBases labels
              (unprimedOddTerminalExternalRight labels terminal)
                candidateBases) s,
          unprimedOddActiveFreePathNext m k C labels terminal
            (unprimedOddTieLeftWinnerBases labels
              (unprimedOddTerminalExternalRight labels terminal)
                candidateBases) s)) ⁻¹'
        (anyCoordinateInBand candidate (fun x ↦ sourceProp49NarrowBand m
          (activeFreeStoppedShape (0, 0) labels C
            (unprimedOddTieLeftWinnerBases labels
              (unprimedOddTerminalExternalRight labels terminal)
                candidateBases) x) alpha) ×ˢ Set.univ)

noncomputable def UnprimedOddTerminalTieLeftProp49AtomData.atom
    {m k A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : UnprimedOddTerminalTieLeftProp49AtomData m k A alpha screen) :
    Set Path :=
  simpleRandomWalk ''
    (actualOddStoppedVectorEvent m k D.labels D.terminal
        (stoppedRunVectorBox D.q m) ∩ stoppedSourceCondition m k D.C)

noncomputable def UnprimedOddTerminalTieLeftProp49AtomData.toInput
    {m k A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : UnprimedOddTerminalTieLeftProp49AtomData m k A alpha screen) :
    StoppedTruncatedProp49AtomInput
      (ι := ActiveFreeStoppedBase (0, 0) D.labels D.C
        (unprimedOddTieLeftWinnerBases D.labels
          (unprimedOddTerminalExternalRight D.labels D.terminal)
            D.candidateBases))
      m k A alpha screen :=
  unprimedOddTerminalTieLeftProp49AtomInput m k A alpha screen D.C D.labels
    D.nondistinguished D.terminal D.m_pos D.k_pos D.creation_card
    D.creation_pairFree D.offBase D.terminal_mem D.admissible_nonempty
    D.candidateBases D.candidate (fun x ↦ sourceProp49NarrowBand m
      (activeFreeStoppedShape (0, 0) D.labels D.C
        (unprimedOddTieLeftWinnerBases D.labels
          (unprimedOddTerminalExternalRight D.labels D.terminal)
            D.candidateBases) x) alpha)
    (unprimedOdd_tieLeftWinner_profile_lt_of_nonempty
      m k D.C D.labels D.terminal D.m_pos D.creation_card
        D.creation_pairFree D.offBase D.terminal_mem D.admissible_nonempty
        D.candidateBases)
    (fun x hx ↦ measurableSet_sourceProp49NarrowBand _ _ _)
    D.candidate_card (fun x hx ↦ by
      rw [sourceProp49CoordinateRate]
      exact sourceTruncatedNegBinMeasure_sourceProp49NarrowBand_le
        D.comparisonCoeff m
          (activeFreeStoppedShape (0, 0) D.labels D.C
            (unprimedOddTieLeftWinnerBases D.labels
              (unprimedOddTerminalExternalRight D.labels D.terminal)
                D.candidateBases) x)
          A alpha D.windowGrowth (D.profile_window x hx) D.alpha_nonneg
            D.alpha_lt D.coefficient)
    D.screen_subset

/-- Source data for the primed-even terminal strict-right atom. -/
structure PrimedEvenTerminalStrictRightProp49AtomData
    (m k A : ℕ) (alpha : ℝ) (screen : Set Path) where
  q : ℕ
  C : Finset Site
  first : Direction
  labels : Fin q → IncrementPair
  nondistinguished : ∀ i, labels i ≠ primedDistinguishedIncrementPair
  terminal : IncrementPair
  m_pos : 0 < m
  k_pos : 0 < k
  creation_card : C.card = k
  creation_pairFree : HLOZPairing.PairFree
    (HLOZPairing.XPair HLOZPairing.east) C
  offBase : PrimedEvenOffBaseMixedCondition first labels terminal m C
  terminal_mem : primedStoppedTerminalSite first labels +
    directionStep (terminal 0) ∈ C
  admissible_nonempty :
    (actualAdmissiblePrimedTerminalVectors m k first labels terminal
      (primedEvenSourceConstraint m k C first labels terminal)).Nonempty
  candidateBases : Finset
    (StoppedExternalBase (primedInitialBase first) labels)
  candidate : Finset (ActiveFreeStoppedBase (primedInitialBase first) labels C
    (primedEvenStrictRightWinnerBases first labels
      (primedEvenTerminalExternalLeft first labels terminal) candidateBases))
  candidate_card : (candidate.card : ℝ) ≤ Real.log ((m : ℝ) + 1) ^ 2
  comparisonCoeff : ℕ
  windowGrowth : SourceWindowGrowth comparisonCoeff m
  profile_window : ∀ x ∈ candidate, InEquation458ExternalWindow
    comparisonCoeff m
      (activeFreeStoppedShape (primedInitialBase first) labels C
        (primedEvenStrictRightWinnerBases first labels
          (primedEvenTerminalExternalLeft first labels terminal)
            candidateBases) x)
  alpha_nonneg : 0 ≤ alpha + delta
  alpha_lt : alpha + delta < kappaOne
  coefficient : 8 * Real.exp (sourceComparisonExponent comparisonCoeff) ≤ A
  screen_subset :
    let atom := simpleRandomWalk ''
      (actualPrimedTerminalVectorEvent m k first labels terminal
          (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C)
    atom ∩ screen ⊆ atom ∩
      (fun s ↦
        (primedEvenActiveFreePathLazy m k C first labels terminal
            (primedEvenStrictRightWinnerBases first labels
              (primedEvenTerminalExternalLeft first labels terminal)
                candidateBases) s,
          primedEvenActiveFreePathNext m k C first labels terminal
            (primedEvenStrictRightWinnerBases first labels
              (primedEvenTerminalExternalLeft first labels terminal)
                candidateBases) s)) ⁻¹'
        (anyCoordinateInBand candidate (fun x ↦ sourceProp49NarrowBand m
          (activeFreeStoppedShape (primedInitialBase first) labels C
            (primedEvenStrictRightWinnerBases first labels
              (primedEvenTerminalExternalLeft first labels terminal)
                candidateBases) x) alpha) ×ˢ Set.univ)

noncomputable def PrimedEvenTerminalStrictRightProp49AtomData.atom
    {m k A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : PrimedEvenTerminalStrictRightProp49AtomData m k A alpha screen) :
    Set Path :=
  simpleRandomWalk ''
    (actualPrimedTerminalVectorEvent m k D.first D.labels D.terminal
        (stoppedRunVectorBox D.q m) ∩ stoppedSourceCondition m k D.C)

noncomputable def PrimedEvenTerminalStrictRightProp49AtomData.toInput
    {m k A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : PrimedEvenTerminalStrictRightProp49AtomData m k A alpha screen) :
    StoppedTruncatedProp49AtomInput
      (ι := ActiveFreeStoppedBase (primedInitialBase D.first) D.labels D.C
        (primedEvenStrictRightWinnerBases D.first D.labels
          (primedEvenTerminalExternalLeft D.first D.labels D.terminal)
            D.candidateBases))
      m k A alpha screen :=
  primedEvenTerminalStrictRightProp49AtomInput m k A alpha screen D.C D.first
    D.labels D.nondistinguished D.terminal D.m_pos D.k_pos D.creation_card
    D.creation_pairFree D.offBase D.terminal_mem D.admissible_nonempty
    D.candidateBases D.candidate (fun x ↦ sourceProp49NarrowBand m
      (activeFreeStoppedShape (primedInitialBase D.first) D.labels D.C
        (primedEvenStrictRightWinnerBases D.first D.labels
          (primedEvenTerminalExternalLeft D.first D.labels D.terminal)
            D.candidateBases) x) alpha)
    (primedEven_strictRightWinner_profile_lt_of_nonempty
      m k D.C D.first D.labels D.terminal D.m_pos D.creation_card
        D.creation_pairFree D.offBase D.terminal_mem D.admissible_nonempty
        D.candidateBases)
    (fun x hx ↦ measurableSet_sourceProp49NarrowBand _ _ _)
    D.candidate_card (fun x hx ↦ by
      rw [sourceProp49CoordinateRate]
      exact sourceTruncatedNegBinMeasure_sourceProp49NarrowBand_le
        D.comparisonCoeff m
          (activeFreeStoppedShape (primedInitialBase D.first) D.labels D.C
            (primedEvenStrictRightWinnerBases D.first D.labels
              (primedEvenTerminalExternalLeft D.first D.labels D.terminal)
                D.candidateBases) x)
          A alpha D.windowGrowth (D.profile_window x hx) D.alpha_nonneg
            D.alpha_lt D.coefficient)
    D.screen_subset

/-- The four literal equation-(4.47) stopped atom types, split by the
unprimed/primed convention and by whether the threshold time occurs before
or inside the terminal pair. This declaration makes no cross-branch cover or
disjointness claim. -/
inductive ConcreteStoppedProp49AtomData
    (m k A : ℕ) (alpha : ℝ) (screen : Set Path) where
  | unprimedEvenLeft
      (data : UnprimedEvenLeftWinnerProp49AtomData m k A alpha screen)
  | primedOddStrictRight
      (data : PrimedOddStrictRightWinnerProp49AtomData m k A alpha screen)
  | unprimedOddTerminalTieLeft
      (data : UnprimedOddTerminalTieLeftProp49AtomData m k A alpha screen)
  | primedEvenTerminalStrictRight
      (data : PrimedEvenTerminalStrictRightProp49AtomData m k A alpha screen)

noncomputable def ConcreteStoppedProp49AtomData.atom
    {m k A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : ConcreteStoppedProp49AtomData m k A alpha screen) : Set Path :=
  match D with
  | .unprimedEvenLeft data => data.atom
  | .primedOddStrictRight data => data.atom
  | .unprimedOddTerminalTieLeft data => data.atom
  | .primedEvenTerminalStrictRight data => data.atom

/-- A literal one of the four stopped parity/winner atoms together with the
source conditional product law after refining by a prescribed history atom.
The coordinate type differs between the four branches, so this dependent
dispatcher keeps each exact law paired with its checked coarse input. -/
inductive ConcreteStoppedProp49RefinedAtomMapLaw
    {m k A : ℕ} {alpha : ℝ} {screen : Set Path}
    (refinedAtom : Set Path) :
    ConcreteStoppedProp49AtomData m k A alpha screen → Prop where
  | unprimedEvenLeft
      (data : UnprimedEvenLeftWinnerProp49AtomData m k A alpha screen)
      (law : StoppedTruncatedProp49RefinedAtomMapLaw
        data.toInput refinedAtom) :
      ConcreteStoppedProp49RefinedAtomMapLaw refinedAtom
        (.unprimedEvenLeft data)
  | primedOddStrictRight
      (data : PrimedOddStrictRightWinnerProp49AtomData m k A alpha screen)
      (law : StoppedTruncatedProp49RefinedAtomMapLaw
        data.toInput refinedAtom) :
      ConcreteStoppedProp49RefinedAtomMapLaw refinedAtom
        (.primedOddStrictRight data)
  | unprimedOddTerminalTieLeft
      (data : UnprimedOddTerminalTieLeftProp49AtomData m k A alpha screen)
      (law : StoppedTruncatedProp49RefinedAtomMapLaw
        data.toInput refinedAtom) :
      ConcreteStoppedProp49RefinedAtomMapLaw refinedAtom
        (.unprimedOddTerminalTieLeft data)
  | primedEvenTerminalStrictRight
      (data : PrimedEvenTerminalStrictRightProp49AtomData
        m k A alpha screen)
      (law : StoppedTruncatedProp49RefinedAtomMapLaw
        data.toInput refinedAtom) :
      ConcreteStoppedProp49RefinedAtomMapLaw refinedAtom
        (.primedEvenTerminalStrictRight data)

/-- Every one of the four source conditional product laws implies the same
history-refined Proposition-4.9 estimate. -/
theorem ConcreteStoppedProp49RefinedAtomMapLaw.screen_measure_le
    {m k A : ℕ} {alpha : ℝ} {screen refinedAtom : Set Path}
    {D : ConcreteStoppedProp49AtomData m k A alpha screen}
    (F : ConcreteStoppedProp49RefinedAtomMapLaw refinedAtom D) :
    simpleRandomWalkLaw (refinedAtom ∩ screen) ≤
      sourceProp49ScreenRate m A alpha *
        simpleRandomWalkLaw refinedAtom := by
  cases F with
  | unprimedEvenLeft data law => exact law.screen_measure_le
  | primedOddStrictRight data law => exact law.screen_measure_le
  | unprimedOddTerminalTieLeft data law => exact law.screen_measure_le
  | primedEvenTerminalStrictRight data law => exact law.screen_measure_le

theorem ConcreteStoppedProp49AtomData.conditional_screen_le
    {m k A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : ConcreteStoppedProp49AtomData m k A alpha screen) :
    simpleRandomWalkLaw[|D.atom] (D.atom ∩ screen) ≤
      sourceProp49ScreenRate m A alpha := by
  cases D with
  | unprimedEvenLeft data =>
      exact data.toInput.conditional_screen_le
  | primedOddStrictRight data =>
      exact data.toInput.conditional_screen_le
  | unprimedOddTerminalTieLeft data =>
      exact data.toInput.conditional_screen_le
  | primedEvenTerminalStrictRight data =>
      exact data.toInput.conditional_screen_le

/-- A literal stopped atom together with the joint active/complement
factorization that keeps a prescribed preceding history.  This is the honest
source object for the sequential Proposition-4.9 averaging step. -/
inductive ConcreteStoppedProp49HistoryAtomData
    (m k A : ℕ) (alpha : ℝ) (screen history : Set Path) where
  | unprimedEvenLeft
      (data : UnprimedEvenLeftWinnerProp49AtomData m k A alpha screen)
      (factor : StoppedTruncatedProp49HistoryFactorization data.toInput history)
  | primedOddStrictRight
      (data : PrimedOddStrictRightWinnerProp49AtomData m k A alpha screen)
      (factor : StoppedTruncatedProp49HistoryFactorization data.toInput history)
  | unprimedOddTerminalTieLeft
      (data : UnprimedOddTerminalTieLeftProp49AtomData m k A alpha screen)
      (factor : StoppedTruncatedProp49HistoryFactorization data.toInput history)
  | primedEvenTerminalStrictRight
      (data : PrimedEvenTerminalStrictRightProp49AtomData m k A alpha screen)
      (factor : StoppedTruncatedProp49HistoryFactorization data.toInput history)

noncomputable def ConcreteStoppedProp49HistoryAtomData.atom
    {m k A : ℕ} {alpha : ℝ} {screen history : Set Path}
    (D : ConcreteStoppedProp49HistoryAtomData m k A alpha screen history) :
    Set Path :=
  match D with
  | .unprimedEvenLeft data _ => data.atom
  | .primedOddStrictRight data _ => data.atom
  | .unprimedOddTerminalTieLeft data _ => data.atom
  | .primedEvenTerminalStrictRight data _ => data.atom

theorem ConcreteStoppedProp49HistoryAtomData.history_screen_le
    {m k A : ℕ} {alpha : ℝ} {screen history : Set Path}
    (D : ConcreteStoppedProp49HistoryAtomData m k A alpha screen history) :
    simpleRandomWalkLaw (D.atom ∩ history ∩ screen) ≤
      sourceProp49ScreenRate m A alpha *
        simpleRandomWalkLaw (D.atom ∩ history) := by
  cases D with
  | unprimedEvenLeft data factor =>
      exact factor.history_screen_le data.toInput
  | primedOddStrictRight data factor =>
      exact factor.history_screen_le data.toInput
  | unprimedOddTerminalTieLeft data factor =>
      exact factor.history_screen_le data.toInput
  | primedEvenTerminalStrictRight data factor =>
      exact factor.history_screen_le data.toInput

/-- Summing a uniform conditional estimate over a countable measurable
partition.  This is the measure-theoretic averaging step between the
profile-wise statement (4.35) and the sequential conditional probability
in (4.37). -/
theorem measure_inter_le_mul_of_countable_conditional_partition
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (history screen : Set Ω) (atom : ι → Set Ω)
    (rate : ℝ≥0∞)
    (hdisjoint : Pairwise fun j l ↦ Disjoint (atom j) (atom l))
    (hmeasurable : ∀ j, MeasurableSet (atom j))
    (hhistory : history = ⋃ j, atom j)
    (hconditional : ∀ j, μ[|(atom j)] (atom j ∩ screen) ≤ rate) :
    μ (history ∩ screen) ≤ rate * μ history := by
  have hcover : history ∩ screen ⊆ ⋃ j, atom j ∩ screen := by
    rintro ω ⟨hHistory, hScreen⟩
    rw [hhistory] at hHistory
    rcases Set.mem_iUnion.mp hHistory with ⟨j, hj⟩
    exact Set.mem_iUnion_of_mem j ⟨hj, hScreen⟩
  have hlocal (j : ι) : μ (atom j ∩ screen) ≤ rate * μ (atom j) := by
    have hmul := ProbabilityTheory.cond_mul_eq_inter
      (hmeasurable j) (atom j ∩ screen) μ
    have hinter : atom j ∩ (atom j ∩ screen) = atom j ∩ screen := by
      ext ω
      simp only [Set.mem_inter_iff]
      tauto
    rw [hinter] at hmul
    calc
      μ (atom j ∩ screen) = μ[|(atom j)] (atom j ∩ screen) * μ (atom j) :=
        hmul.symm
      _ ≤ rate * μ (atom j) := by
        gcongr
        exact hconditional j
  calc
    μ (history ∩ screen) ≤ μ (⋃ j, atom j ∩ screen) := measure_mono hcover
    _ ≤ ∑' j, μ (atom j ∩ screen) := measure_iUnion_le _
    _ ≤ ∑' j, rate * μ (atom j) := ENNReal.tsum_le_tsum hlocal
    _ = rate * ∑' j, μ (atom j) := by rw [ENNReal.tsum_mul_left]
    _ = rate * μ (⋃ j, atom j) := by
      rw [measure_iUnion hdisjoint hmeasurable]
    _ = rate * μ history := by rw [← hhistory]

/-- Countable averaging when each coarse atom already carries the exact
history-conditioned unnormalized bound.  Unlike the provisional criterion
below, this theorem requires no constancy of the history on a raw atom. -/
theorem measure_history_inter_le_mul_of_countable_atomwise
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (history screen : Set Ω) (atom : ι → Set Ω)
    (rate : ℝ≥0∞)
    (hdisjoint : Pairwise fun j l ↦ Disjoint (atom j) (atom l))
    (hmeasurable : ∀ j, MeasurableSet (atom j))
    (hhistoryMeasurable : MeasurableSet history)
    (hcover : history ⊆ ⋃ j, atom j)
    (hlocal : ∀ j,
      μ (atom j ∩ history ∩ screen) ≤ rate * μ (atom j ∩ history)) :
    μ (history ∩ screen) ≤ rate * μ history := by
  let selected : ι → Set Ω := fun j ↦ atom j ∩ history
  have hselectedDisjoint : Pairwise fun j l ↦
      Disjoint (selected j) (selected l) := by
    intro j l hjl
    exact (hdisjoint hjl).mono inter_subset_left inter_subset_left
  have hselectedMeasurable : ∀ j, MeasurableSet (selected j) :=
    fun j ↦ (hmeasurable j).inter hhistoryMeasurable
  have hhistory : history = ⋃ j, selected j := by
    ext s
    constructor
    · intro hs
      rcases Set.mem_iUnion.mp (hcover hs) with ⟨j, hj⟩
      exact Set.mem_iUnion_of_mem j ⟨hj, hs⟩
    · intro hs
      rcases Set.mem_iUnion.mp hs with ⟨j, hj⟩
      exact hj.2
  have hscreen : history ∩ screen ⊆ ⋃ j, selected j ∩ screen := by
    rintro s ⟨hs, ht⟩
    rw [hhistory] at hs
    rcases Set.mem_iUnion.mp hs with ⟨j, hj⟩
    exact Set.mem_iUnion_of_mem j ⟨hj, ht⟩
  calc
    μ (history ∩ screen) ≤ μ (⋃ j, selected j ∩ screen) :=
      measure_mono hscreen
    _ ≤ ∑' j, μ (selected j ∩ screen) := measure_iUnion_le _
    _ ≤ ∑' j, rate * μ (selected j) :=
      ENNReal.tsum_le_tsum hlocal
    _ = rate * ∑' j, μ (selected j) := by rw [ENNReal.tsum_mul_left]
    _ = rate * μ (⋃ j, selected j) := by
      rw [measure_iUnion hselectedDisjoint hselectedMeasurable]
    _ = rate * μ history := by rw [← hhistory]

/-- Countable atomwise averaging when the atoms need cover only the screened
part of the history. -/
theorem measure_history_inter_screen_le_mul_of_countable_atomwise
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (history screen : Set Ω) (atom : ι → Set Ω) (rate : ℝ≥0∞)
    (hdisjoint : Pairwise fun j l ↦ Disjoint (atom j) (atom l))
    (hmeasurable : ∀ j, MeasurableSet (atom j))
    (hhistoryMeasurable : MeasurableSet history)
    (hcover : history ∩ screen ⊆ ⋃ j, atom j)
    (hlocal : ∀ j,
      μ (atom j ∩ history ∩ screen) ≤ rate * μ (atom j ∩ history)) :
    μ (history ∩ screen) ≤ rate * μ history := by
  let selected : ι → Set Ω := fun j ↦ atom j ∩ history
  have hselectedDisjoint : Pairwise fun j l ↦
      Disjoint (selected j) (selected l) := by
    intro j l hjl
    exact (hdisjoint hjl).mono inter_subset_left inter_subset_left
  have hselectedMeasurable : ∀ j, MeasurableSet (selected j) :=
    fun j ↦ (hmeasurable j).inter hhistoryMeasurable
  have hscreen : history ∩ screen ⊆ ⋃ j, selected j ∩ screen := by
    rintro s hs
    rcases Set.mem_iUnion.mp (hcover hs) with ⟨j, hj⟩
    exact Set.mem_iUnion_of_mem j ⟨⟨hj, hs.1⟩, hs.2⟩
  have hselectedSubset : (⋃ j, selected j) ⊆ history := by
    rintro s hs
    rcases Set.mem_iUnion.mp hs with ⟨j, hj⟩
    exact hj.2
  calc
    μ (history ∩ screen) ≤ μ (⋃ j, selected j ∩ screen) :=
      measure_mono hscreen
    _ ≤ ∑' j, μ (selected j ∩ screen) := measure_iUnion_le _
    _ ≤ ∑' j, rate * μ (selected j) := ENNReal.tsum_le_tsum hlocal
    _ = rate * ∑' j, μ (selected j) := by rw [ENNReal.tsum_mul_left]
    _ = rate * μ (⋃ j, selected j) := by
      rw [measure_iUnion hselectedDisjoint hselectedMeasurable]
    _ ≤ rate * μ history := mul_le_mul' le_rfl (measure_mono hselectedSubset)

/-- Finite union of phase-specific, separately disjoint countable conditioning
families.  Atoms from different branches may overlap. -/
theorem measure_history_inter_le_mul_of_finiteBranch_countable_atomwise
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (branchCount : ℕ) (history fullScreen : Set Ω)
    (branchScreen : Fin branchCount → Set Ω)
    (atom : Fin branchCount → ℕ → Set Ω) (rate : ℝ≥0∞)
    (hdisjoint : ∀ j, Pairwise fun n l ↦ Disjoint (atom j n) (atom j l))
    (hmeasurable : ∀ j n, MeasurableSet (atom j n))
    (hhistoryMeasurable : MeasurableSet history)
    (hbranchCover : history ∩ fullScreen ⊆
      ⋃ j, history ∩ branchScreen j)
    (hatomCover : ∀ j, history ∩ branchScreen j ⊆ ⋃ n, atom j n)
    (hlocal : ∀ j n,
      μ (atom j n ∩ history ∩ branchScreen j) ≤
        rate * μ (atom j n ∩ history)) :
    μ (history ∩ fullScreen) ≤
      (branchCount : ℝ≥0∞) * rate * μ history := by
  have hbranch (j : Fin branchCount) :
      μ (history ∩ branchScreen j) ≤ rate * μ history :=
    measure_history_inter_screen_le_mul_of_countable_atomwise
      μ history (branchScreen j) (atom j) rate
      (hdisjoint j) (hmeasurable j) hhistoryMeasurable
      (hatomCover j) (hlocal j)
  calc
    μ (history ∩ fullScreen) ≤ μ (⋃ j, history ∩ branchScreen j) :=
      measure_mono hbranchCover
    _ ≤ ∑ j, μ (history ∩ branchScreen j) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin branchCount, rate * μ history := by
      apply Finset.sum_le_sum
      intro j _
      exact hbranch j
    _ = (branchCount : ℝ≥0∞) * rate * μ history := by
      simp [mul_assoc]

/-- Strongest source-facing Proposition-4.9 interface.

Each finite branch has a separately disjoint countable family of refined
conditioning atoms.  Only the sequential history must be covered, and the
source supplies the direct unnormalized inequality on each refined atom.
There is no cross-branch disjointness, raw-atom history constancy, or asserted
active/complement independence. -/
def Prop47StoppedProfileProp49RefinedFiniteBranchEstimate
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (branchCount localCoeff : ℕ)
    (branchScreen : ℕ → Fin 6 → AlphaTriple → StageIndex →
      Fin branchCount → Set Path)
    (refinedAtom : ℕ → Fin 6 → AlphaTriple → StageIndex →
      Fin branchCount → ℕ → Set Path) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i a (r : StageIndex),
    alphaValue (tripleAlphaIndex a r) ≤ kappaTwo →
    let atom := refinedAtom m i a r
    let history := prop47History profiles cStar m i a r.1
    let fullScreen := lowScaleScreenEvent (profiles i) (cStar i) i m
      (stageNumber r) (alphaValue (tripleAlphaIndex a r) + delta)
    let screen := branchScreen m i a r
    (∀ j, Pairwise fun n l ↦ Disjoint (atom j n) (atom j l)) ∧
    (∀ j n, MeasurableSet (atom j n)) ∧
    history ∩ fullScreen ⊆ ⋃ j, history ∩ screen j ∧
    (∀ j, history ∩ screen j ⊆ ⋃ n, atom j n) ∧
    ∀ j n, simpleRandomWalkLaw (atom j n ∩ history ∩ screen j) ≤
      sourceProp49ScreenRate m localCoeff
          (alphaValue (tripleAlphaIndex a r)) *
        simpleRandomWalkLaw (atom j n ∩ history)

/-- Finite-branch refined conditioning atoms imply the averaged sequential
Proposition-4.9 estimate, with the branch count absorbed into its coefficient.
-/
theorem prop47StoppedProfileProp49Estimate_of_refinedFiniteBranches
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (branchCount localCoeff : ℕ)
    (branchScreen : ℕ → Fin 6 → AlphaTriple → StageIndex →
      Fin branchCount → Set Path)
    (refinedAtom : ℕ → Fin 6 → AlphaTriple → StageIndex →
      Fin branchCount → ℕ → Set Path)
    (hAtoms : Prop47StoppedProfileProp49RefinedFiniteBranchEstimate
      profiles cStar branchCount localCoeff branchScreen refinedAtom) :
    Prop47StoppedProfileProp49Estimate profiles cStar
      (branchCount * localCoeff) := by
  filter_upwards [hAtoms] with m hm
  intro i a r halpha
  rcases hm i a r halpha with
    ⟨hdisjoint, hmeasurable, hbranchCover, hatomCover, hlocal⟩
  have haggregate :=
    measure_history_inter_le_mul_of_finiteBranch_countable_atomwise
      simpleRandomWalkLaw branchCount
      (prop47History profiles cStar m i a r.1)
      (lowScaleScreenEvent (profiles i) (cStar i) i m (stageNumber r)
        (alphaValue (tripleAlphaIndex a r) + delta))
      (branchScreen m i a r)
      (refinedAtom m i a r)
      (sourceProp49ScreenRate m localCoeff
        (alphaValue (tripleAlphaIndex a r)))
      hdisjoint hmeasurable
      (measurableSet_prop47History profiles cStar m i a r.1)
      hbranchCover hatomCover hlocal
  rw [sourceProp49ScreenRate] at haggregate ⊢
  simpa only [prop47SequentialScreenEvent, Nat.cast_mul, mul_assoc] using
    haggregate

/-- Provisional raw-atom disintegration criterion.

The containment/disjointness field is *not* supplied by labels and the
creation set: ordered creation history need not be constant on those coarse
atoms.  It records the exact deterministic obstruction left by the current
stopped-grouping API.  A source instantiation must instead prove this field,
or replace it by a joint active/complement factorization in which the history
is measurable with respect to the complement coordinates. -/
def Prop47StoppedProfileProp49SourceAtomEstimate
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (A : ℕ)
    (profileAtom :
      ℕ → Fin 6 → AlphaTriple → StageIndex → ℕ → Set Path) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i a (r : StageIndex),
    alphaValue (tripleAlphaIndex a r) ≤ kappaTwo →
    let atom := profileAtom m i a r
    let screen := lowScaleScreenEvent (profiles i) (cStar i) i m
      (stageNumber r) (alphaValue (tripleAlphaIndex a r) + delta)
    (Pairwise fun n l ↦ Disjoint (atom n) (atom l)) ∧
    (∀ n, MeasurableSet (atom n)) ∧
    prop47History profiles cStar m i a r.1 ⊆ ⋃ n, atom n ∧
    (∀ n, atom n ⊆ prop47History profiles cStar m i a r.1 ∨
      Disjoint (atom n) (prop47History profiles cStar m i a r.1)) ∧
    ∀ n, ∃ D : ConcreteStoppedProp49AtomData m (stageNumber r) A
        (alphaValue (tripleAlphaIndex a r)) screen,
      D.atom = atom n

/-- Literal stopped-profile Proposition 4.9 implies its averaged
sequential-history form. -/
theorem prop47StoppedProfileProp49Estimate_of_sourceAtoms
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (A : ℕ)
    (profileAtom :
      ℕ → Fin 6 → AlphaTriple → StageIndex → ℕ → Set Path)
    (hAtoms : Prop47StoppedProfileProp49SourceAtomEstimate
      profiles cStar A profileAtom) :
    Prop47StoppedProfileProp49Estimate profiles cStar A := by
  classical
  filter_upwards [hAtoms] with m hm
  intro i a r halpha
  rcases hm i a r halpha with
    ⟨hdisjoint, hmeasurable, hcover, hconstant, hsource⟩
  have hcondRaw (n : ℕ) :
      simpleRandomWalkLaw[|profileAtom m i a r n]
          (profileAtom m i a r n ∩
            lowScaleScreenEvent (profiles i) (cStar i) i m (stageNumber r)
              (alphaValue (tripleAlphaIndex a r) + delta)) ≤
        sourceProp49ScreenRate m A
          (alphaValue (tripleAlphaIndex a r)) := by
    rcases hsource n with ⟨D, hD⟩
    rw [← hD]
    exact D.conditional_screen_le
  let history := prop47History profiles cStar m i a r.1
  let atom := profileAtom m i a r
  let selected : ℕ → Set Path := fun n ↦
    if atom n ⊆ history then atom n else ∅
  have hselectedDisjoint : Pairwise fun n l ↦
      Disjoint (selected n) (selected l) := by
    intro n l hne
    by_cases hn : atom n ⊆ history
    · by_cases hl : atom l ⊆ history
      · simpa [selected, hn, hl] using hdisjoint hne
      · simp [selected, hn, hl]
    · simp [selected, hn]
  have hselectedMeasurable : ∀ n, MeasurableSet (selected n) := by
    intro n
    by_cases hn : atom n ⊆ history
    · simpa [selected, hn] using hmeasurable n
    · simp [selected, hn]
  have hhistory : history = ⋃ n, selected n := by
    ext s
    constructor
    · intro hs
      rcases Set.mem_iUnion.mp (hcover hs) with ⟨n, hn⟩
      rcases hconstant n with hsub | hdisj
      · change atom n ⊆ history at hsub
        exact Set.mem_iUnion_of_mem n (by simpa [selected, hsub] using hn)
      · exact (Set.disjoint_left.1 hdisj hn hs).elim
    · intro hs
      rcases Set.mem_iUnion.mp hs with ⟨n, hn⟩
      by_cases hsub : atom n ⊆ history
      · exact hsub (by simpa [selected, hsub] using hn)
      · simpa [selected, hsub] using hn
  have hcond (n : ℕ) :
      simpleRandomWalkLaw[|selected n]
          (selected n ∩
            lowScaleScreenEvent (profiles i) (cStar i) i m (stageNumber r)
              (alphaValue (tripleAlphaIndex a r) + delta)) ≤
        sourceProp49ScreenRate m A
          (alphaValue (tripleAlphaIndex a r)) := by
    by_cases hsub : atom n ⊆ history
    · simpa [selected, hsub, atom] using hcondRaw n
    · simp [selected, hsub]
  exact measure_inter_le_mul_of_countable_conditional_partition
    simpleRandomWalkLaw
    (prop47History profiles cStar m i a r.1)
    (lowScaleScreenEvent (profiles i) (cStar i) i m (stageNumber r)
      (alphaValue (tripleAlphaIndex a r) + delta))
    selected
    (sourceProp49ScreenRate m A (alphaValue (tripleAlphaIndex a r)))
    hselectedDisjoint hselectedMeasurable hhistory hcond

/-- Optional sufficient route for Proposition 4.9.  Each coarse stopped atom
keeps its nondegenerate truncated product law and additionally supplies a
joint active/complement factorization that makes the preceding history a
complement event.  This factorization is stronger than the direct
history-intersected estimates used in the source-facing finite-branch
interface above. -/
def Prop47StoppedProfileProp49FactorizedSourceAtomEstimate
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (A : ℕ)
    (profileAtom :
      ℕ → Fin 6 → AlphaTriple → StageIndex → ℕ → Set Path) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i a (r : StageIndex),
    alphaValue (tripleAlphaIndex a r) ≤ kappaTwo →
    let atom := profileAtom m i a r
    let history := prop47History profiles cStar m i a r.1
    let screen := lowScaleScreenEvent (profiles i) (cStar i) i m
      (stageNumber r) (alphaValue (tripleAlphaIndex a r) + delta)
    (Pairwise fun n l ↦ Disjoint (atom n) (atom l)) ∧
    (∀ n, MeasurableSet (atom n)) ∧
    history ⊆ ⋃ n, atom n ∧
    ∀ n, ∃ D : ConcreteStoppedProp49HistoryAtomData
        m (stageNumber r) A (alphaValue (tripleAlphaIndex a r))
          screen history,
      D.atom = atom n

/-- The factorized literal atom family implies the averaged sequential
Proposition-4.9 estimate without any raw-atom constancy hypothesis. -/
theorem prop47StoppedProfileProp49Estimate_of_factorizedSourceAtoms
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (A : ℕ)
    (profileAtom :
      ℕ → Fin 6 → AlphaTriple → StageIndex → ℕ → Set Path)
    (hAtoms : Prop47StoppedProfileProp49FactorizedSourceAtomEstimate
      profiles cStar A profileAtom) :
    Prop47StoppedProfileProp49Estimate profiles cStar A := by
  filter_upwards [hAtoms] with m hm
  intro i a r halpha
  rcases hm i a r halpha with
    ⟨hdisjoint, hmeasurable, hcover, hsource⟩
  let history := prop47History profiles cStar m i a r.1
  let screen := lowScaleScreenEvent (profiles i) (cStar i) i m
    (stageNumber r) (alphaValue (tripleAlphaIndex a r) + delta)
  have hlocal (n : ℕ) :
      simpleRandomWalkLaw (profileAtom m i a r n ∩ history ∩ screen) ≤
        sourceProp49ScreenRate m A
            (alphaValue (tripleAlphaIndex a r)) *
          simpleRandomWalkLaw (profileAtom m i a r n ∩ history) := by
    rcases hsource n with ⟨D, hD⟩
    rw [← hD]
    exact D.history_screen_le
  exact measure_history_inter_le_mul_of_countable_atomwise
    simpleRandomWalkLaw history screen (profileAtom m i a r)
    (sourceProp49ScreenRate m A (alphaValue (tripleAlphaIndex a r)))
    hdisjoint hmeasurable
    (measurableSet_prop47History profiles cStar m i a r.1)
    hcover hlocal

theorem sourceLowEscape_mul_sourceProp49ScreenRate
    (m escapeCoeff A : ℕ) (alpha : ℝ) :
    sourceLowEscapeRate m escapeCoeff alpha *
        sourceProp49ScreenRate m A alpha =
      (A : ℝ≥0∞) * ((escapeCoeff : ℝ≥0∞) *
        ENNReal.ofReal (Real.log ((m : ℝ) + 1) ^ 2)) *
        ((m : ℝ≥0∞) + 1) ^ (-(kappaOne - 2 * delta)) := by
  rw [sourceLowEscapeRate, sourceProp49ScreenRate]
  calc
    (escapeCoeff : ℝ≥0∞) *
        ((m : ℝ≥0∞) + 1) ^ (-(alpha - delta)) *
          ((A : ℝ≥0∞) * ENNReal.ofReal (Real.log ((m : ℝ) + 1) ^ 2) *
            ((m : ℝ≥0∞) + 1) ^ (-(kappaOne - (alpha + delta)))) =
        (A : ℝ≥0∞) * ((escapeCoeff : ℝ≥0∞) *
          ENNReal.ofReal (Real.log ((m : ℝ) + 1) ^ 2)) *
          (((m : ℝ≥0∞) + 1) ^ (-(alpha - delta)) *
            ((m : ℝ≥0∞) + 1) ^ (-(kappaOne - (alpha + delta)))) := by
      ring
    _ = (A : ℝ≥0∞) * ((escapeCoeff : ℝ≥0∞) *
        ENNReal.ofReal (Real.log ((m : ℝ) + 1) ^ 2)) *
        ((m : ℝ≥0∞) + 1) ^
          (-(alpha - delta) + -(kappaOne - (alpha + delta))) := by
      rw [ENNReal.rpow_add] <;> simp
    _ = (A : ℝ≥0∞) * ((escapeCoeff : ℝ≥0∞) *
        ENNReal.ofReal (Real.log ((m : ℝ) + 1) ^ 2)) *
        ((m : ℝ≥0∞) + 1) ^ (-(kappaOne - 2 * delta)) := by
      congr 1
      ring_nf

/-- The exponent arithmetic at the end of (4.37).  The bound is uniform in
the mesh exponent `alpha`; it has disappeared from the product before this
analytic absorption is used. -/
theorem eventually_sourceLowRates_le_sourceStageRate
    (escapeCoeff A : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ alpha : ℝ,
      sourceLowEscapeRate m escapeCoeff alpha *
          sourceProp49ScreenRate m A alpha ≤
        sourceStageRate m A kappa := by
  have hgap : 0 < kappaOne - kappaTwo := by
    linarith [kappaTwo_between_one_third_and_kappaOne.2]
  by_cases hcoeff : escapeCoeff = 0
  · subst escapeCoeff
    filter_upwards [] with m
    intro alpha
    simp [sourceLowEscapeRate]
  have hcoeffpos : (0 : ℝ) < escapeCoeff := by
    exact_mod_cast Nat.pos_of_ne_zero hcoeff
  have hlog := (tendsto_add_atTop_nat 1).eventually
    (HLOZLemma411.eventually_const_mul_log_sq_le_rpow
      (c := (escapeCoeff : ℝ)) (c₁ := (1 : ℝ))
      (a := kappaOne - kappaTwo) hcoeffpos (by norm_num) hgap)
  filter_upwards [hlog] with m hm
  intro alpha
  rw [sourceLowEscape_mul_sourceProp49ScreenRate, sourceStageRate]
  have hbase : ENNReal.ofReal ((m : ℝ) + 1) = (m : ℝ≥0∞) + 1 := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    simp
  have hlogENN :
      (escapeCoeff : ℝ≥0∞) *
          ENNReal.ofReal (Real.log ((m : ℝ) + 1) ^ 2) ≤
        ((m : ℝ≥0∞) + 1) ^ (kappaOne - kappaTwo) := by
    rw [← ENNReal.ofReal_natCast escapeCoeff,
      ← ENNReal.ofReal_mul (by positivity),
      ← hbase, ENNReal.ofReal_rpow_of_pos (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    simpa [Nat.cast_add, Nat.cast_one] using hm
  have hcore :
      ((escapeCoeff : ℝ≥0∞) *
          ENNReal.ofReal (Real.log ((m : ℝ) + 1) ^ 2)) *
          ((m : ℝ≥0∞) + 1) ^ (-(kappaOne - 2 * delta)) ≤
        ((m : ℝ≥0∞) + 1) ^ (-kappa) := by
    calc
      ((escapeCoeff : ℝ≥0∞) *
          ENNReal.ofReal (Real.log ((m : ℝ) + 1) ^ 2)) *
          ((m : ℝ≥0∞) + 1) ^ (-(kappaOne - 2 * delta)) ≤
        ((m : ℝ≥0∞) + 1) ^ (kappaOne - kappaTwo) *
          ((m : ℝ≥0∞) + 1) ^ (-(kappaOne - 2 * delta)) := by
        gcongr
      _ = ((m : ℝ≥0∞) + 1) ^
          ((kappaOne - kappaTwo) + -(kappaOne - 2 * delta)) := by
        rw [ENNReal.rpow_add] <;> simp
      _ = ((m : ℝ≥0∞) + 1) ^ (-kappa) := by
        congr 1
        rw [kappa]
        ring
  rw [mul_assoc]
  simpa only [mul_comm] using mul_le_mul_left hcore (A : ℝ≥0∞)

theorem prop47History_succ_eq_currentStage
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex) :
    prop47History profiles cStar m i a (r.1 + 1) =
      prop47History profiles cStar m i a r.1 ∩
        prop47StageEvent profiles cStar i m r
          (alphaValue (tripleAlphaIndex a r)) := by
  rw [prop47History, screeningHistory_succ]
  simp only [r.isLt, dite_true]

/-- Exact deterministic use of (4.37): after the low branch is selected,
the next recursive history is contained in the sequential exit-and-screen
event. -/
theorem prop47History_succ_subset_sequentialExitScreen
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (halpha : alphaValue (tripleAlphaIndex a r) ≤ kappaTwo) :
    prop47History profiles cStar m i a (r.1 + 1) ⊆
      prop47SequentialExitScreenEvent profiles cStar m i a r := by
  rw [prop47History_succ_eq_currentStage]
  rintro s ⟨hHistory, hStage⟩
  refine ⟨hHistory, ?_⟩
  rw [prop47StageEvent, if_pos halpha] at hStage
  exact lowScaleStage_subset_exit_and_screen
    (profiles i) (cStar i) i m (stageNumber r)
      (alphaValue (tripleAlphaIndex a r)) hStage.2

/-- Fixed-stage composition of the two source factors.  This is the only
place where they are converted into the assembly's `StageBound`. -/
theorem lowStageBound_of_sequential_escape_and_prop49
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m escapeCoeff A B : ℕ) (i : Fin 6) (a : AlphaTriple)
    (r : StageIndex)
    (halpha : alphaValue (tripleAlphaIndex a r) ≤ kappaTwo)
    (hEscape :
      simpleRandomWalkLaw
          (prop47SequentialExitScreenEvent profiles cStar m i a r) ≤
        sourceLowEscapeRate m escapeCoeff
            (alphaValue (tripleAlphaIndex a r)) *
          simpleRandomWalkLaw
            (prop47SequentialScreenEvent profiles cStar m i a r))
    (hProp49 :
      simpleRandomWalkLaw
          (prop47SequentialScreenEvent profiles cStar m i a r) ≤
        sourceProp49ScreenRate m A (alphaValue (tripleAlphaIndex a r)) *
          simpleRandomWalkLaw (prop47History profiles cStar m i a r.1))
    (hRates :
      sourceLowEscapeRate m escapeCoeff
          (alphaValue (tripleAlphaIndex a r)) *
          sourceProp49ScreenRate m A (alphaValue (tripleAlphaIndex a r)) ≤
        sourceStageRate m A kappa) :
    StageBound simpleRandomWalkLaw (sourceStageRate m A kappa)
      (sourceExceptionalRateWithPrefactor m B kappa)
      (prop47History profiles cStar m i a r.1)
      (prop47History profiles cStar m i a (r.1 + 1)) := by
  refine ⟨screeningHistory_succ_subset _ _ r.1, ?_⟩
  calc
    simpleRandomWalkLaw (prop47History profiles cStar m i a (r.1 + 1)) ≤
        simpleRandomWalkLaw
          (prop47SequentialExitScreenEvent profiles cStar m i a r) :=
      measure_mono (prop47History_succ_subset_sequentialExitScreen
        profiles cStar m i a r halpha)
    _ ≤ sourceLowEscapeRate m escapeCoeff
          (alphaValue (tripleAlphaIndex a r)) *
          simpleRandomWalkLaw
            (prop47SequentialScreenEvent profiles cStar m i a r) := hEscape
    _ ≤ sourceLowEscapeRate m escapeCoeff
          (alphaValue (tripleAlphaIndex a r)) *
          (sourceProp49ScreenRate m A (alphaValue (tripleAlphaIndex a r)) *
            simpleRandomWalkLaw (prop47History profiles cStar m i a r.1)) := by
      gcongr
    _ = (sourceLowEscapeRate m escapeCoeff
          (alphaValue (tripleAlphaIndex a r)) *
          sourceProp49ScreenRate m A (alphaValue (tripleAlphaIndex a r))) *
            simpleRandomWalkLaw (prop47History profiles cStar m i a r.1) := by
      rw [mul_assoc]
    _ ≤ sourceStageRate m A kappa *
          simpleRandomWalkLaw (prop47History profiles cStar m i a r.1) := by
      gcongr
    _ ≤ sourceStageRate m A kappa *
          simpleRandomWalkLaw (prop47History profiles cStar m i a r.1) +
            sourceExceptionalRateWithPrefactor m B kappa := by
      exact le_add_right le_rfl

/-- Reduction of the low-stage bound to sequential escape and the averaged
Proposition-4.9 screen estimate. -/
theorem prop47LowStageEstimate_of_sequential_escape_and_prop49
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (escapeCoeff A B : ℕ)
    (hEscape : Prop47SequentialEscapeEstimate profiles cStar escapeCoeff)
    (hProp49 : Prop47StoppedProfileProp49Estimate profiles cStar A) :
    Prop47LowStageEstimate profiles cStar A B := by
  filter_upwards [hEscape, hProp49,
    eventually_sourceLowRates_le_sourceStageRate escapeCoeff A] with
      m hEscapeM hProp49M hRatesM
  intro i a r halpha
  exact lowStageBound_of_sequential_escape_and_prop49
    profiles cStar m escapeCoeff A B i a r halpha
      (hEscapeM i a r halpha) (hProp49M i a r halpha)
      (hRatesM (alphaValue (tripleAlphaIndex a r)))

/-- Legacy coarse-atom version of the low-stage connector.  Its source-atom
predicate retains the explicit history/atom obstruction documented above. -/
theorem prop47LowStageEstimate_of_sourceAtoms
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (escapeCoeff A B : ℕ)
    (profileAtom :
      ℕ → Fin 6 → AlphaTriple → StageIndex → ℕ → Set Path)
    (hEscape : Prop47SequentialEscapeEstimate profiles cStar escapeCoeff)
    (hProp49Atoms : Prop47StoppedProfileProp49SourceAtomEstimate
      profiles cStar A profileAtom) :
    Prop47LowStageEstimate profiles cStar A B :=
  prop47LowStageEstimate_of_sequential_escape_and_prop49
    profiles cStar escapeCoeff A B hEscape
      (prop47StoppedProfileProp49Estimate_of_sourceAtoms
        profiles cStar A profileAtom hProp49Atoms)

/-- Source-facing low-stage connector with phase-specific screens and finite
families of separately disjoint refined conditioning atoms. -/
theorem prop47LowStageEstimate_of_refinedFiniteBranches
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (branchCount localCoeff escapeCoeff B : ℕ)
    (branchScreen : ℕ → Fin 6 → AlphaTriple → StageIndex →
      Fin branchCount → Set Path)
    (refinedAtom : ℕ → Fin 6 → AlphaTriple → StageIndex →
      Fin branchCount → ℕ → Set Path)
    (hEscape : Prop47SequentialEscapeEstimate profiles cStar escapeCoeff)
    (hProp49Atoms : Prop47StoppedProfileProp49RefinedFiniteBranchEstimate
      profiles cStar branchCount localCoeff branchScreen refinedAtom) :
    Prop47LowStageEstimate profiles cStar (branchCount * localCoeff) B :=
  prop47LowStageEstimate_of_sequential_escape_and_prop49
    profiles cStar escapeCoeff (branchCount * localCoeff) B hEscape
      (prop47StoppedProfileProp49Estimate_of_refinedFiniteBranches
        profiles cStar branchCount localCoeff branchScreen refinedAtom
        hProp49Atoms)

/-- Optional stronger sufficient route using joint active/complement
factorization, with no coarse-atom history-constancy premise. -/
theorem prop47LowStageEstimate_of_factorizedSourceAtoms
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (escapeCoeff A B : ℕ)
    (profileAtom :
      ℕ → Fin 6 → AlphaTriple → StageIndex → ℕ → Set Path)
    (hEscape : Prop47SequentialEscapeEstimate profiles cStar escapeCoeff)
    (hProp49Atoms : Prop47StoppedProfileProp49FactorizedSourceAtomEstimate
      profiles cStar A profileAtom) :
    Prop47LowStageEstimate profiles cStar A B :=
  prop47LowStageEstimate_of_sequential_escape_and_prop49
    profiles cStar escapeCoeff A B hEscape
      (prop47StoppedProfileProp49Estimate_of_factorizedSourceAtoms
        profiles cStar A profileAtom hProp49Atoms)

set_option linter.constructorNameAsVariable false in
/-- Fully named Proposition-4.7 wrapper in which the low-stage
`StageBound` is no longer assumed.  `hProp48Cardinality` is the existing
named estimate for the `#M^k(m,κ₁) ≤ log² m` screen supplied by the
Proposition-4.8/Lemmas-4.11--4.12 branch; `hProp49` is the uniform stopped-
profile screen in Proposition 4.9. -/
theorem hlozPlanarConclusion_of_prop47_low_source_estimates
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (escapeCoeff stageCoeff farCoeff lemma410Coeff prop45Coeff
      prop48CardinalityCoeff : ℕ)
    (hFar : Prop47FarGapEstimate farCoeff)
    (hLemma410 : Prop47Lemma410Estimate lemma410Coeff)
    (hProp45 : Prop47Prop45Estimate profiles cStar prop45Coeff)
    (hProp48Cardinality :
      Prop47Lemma411412Estimate prop48CardinalityCoeff)
    (hEscape : Prop47SequentialEscapeEstimate profiles cStar escapeCoeff)
    (hProp49 :
      Prop47StoppedProfileProp49Estimate profiles cStar stageCoeff)
    (hHigh : Prop47HighStageEstimate profiles cStar stageCoeff
      (prop47FailurePrefactor farCoeff lemma410Coeff prop45Coeff
        prop48CardinalityCoeff)) :
    HLOZPlanarConclusion := by
  exact hlozPlanarConclusion_of_prop47_named_source_estimates
    profiles cStar stageCoeff farCoeff lemma410Coeff prop45Coeff
      prop48CardinalityCoeff hFar hLemma410 hProp45 hProp48Cardinality
      (prop47LowStageEstimate_of_sequential_escape_and_prop49
        profiles cStar escapeCoeff stageCoeff
          (prop47FailurePrefactor farCoeff lemma410Coeff prop45Coeff
            prop48CardinalityCoeff) hEscape hProp49)
      hHigh

set_option linter.constructorNameAsVariable false in
/-- The same source-facing conclusion with Proposition 4.9 left at its
literal stopped-profile-atom interface. -/
theorem hlozPlanarConclusion_of_prop47_low_source_atom_estimates
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (escapeCoeff stageCoeff farCoeff lemma410Coeff prop45Coeff
      prop48CardinalityCoeff : ℕ)
    (profileAtom :
      ℕ → Fin 6 → AlphaTriple → StageIndex → ℕ → Set Path)
    (hFar : Prop47FarGapEstimate farCoeff)
    (hLemma410 : Prop47Lemma410Estimate lemma410Coeff)
    (hProp45 : Prop47Prop45Estimate profiles cStar prop45Coeff)
    (hProp48Cardinality :
      Prop47Lemma411412Estimate prop48CardinalityCoeff)
    (hEscape : Prop47SequentialEscapeEstimate profiles cStar escapeCoeff)
    (hProp49Atoms : Prop47StoppedProfileProp49SourceAtomEstimate
      profiles cStar stageCoeff profileAtom)
    (hHigh : Prop47HighStageEstimate profiles cStar stageCoeff
      (prop47FailurePrefactor farCoeff lemma410Coeff prop45Coeff
        prop48CardinalityCoeff)) :
    HLOZPlanarConclusion := by
  exact hlozPlanarConclusion_of_prop47_named_source_estimates
    profiles cStar stageCoeff farCoeff lemma410Coeff prop45Coeff
      prop48CardinalityCoeff hFar hLemma410 hProp45 hProp48Cardinality
      (prop47LowStageEstimate_of_sourceAtoms profiles cStar escapeCoeff stageCoeff
        (prop47FailurePrefactor farCoeff lemma410Coeff prop45Coeff
          prop48CardinalityCoeff) profileAtom hEscape hProp49Atoms)
      hHigh

end Erdos1166.HLOZProp47LowStageConnector
