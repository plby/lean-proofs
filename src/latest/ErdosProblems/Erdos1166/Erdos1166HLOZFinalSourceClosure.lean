/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1166.Erdos1166HLOZAppendixADiskSuccess
import ErdosProblems.Erdos1166.Erdos1166HLOZLemma410Prop48XDirections
import ErdosProblems.Erdos1166.Erdos1166HLOZLemma410CodedAtoms
import ErdosProblems.Erdos1166.Erdos1166HLOZLemma410Prop48YColumns
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47FarGap
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47Lemma411412Connector
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47Lemma411412SourceAtoms
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47Lemma411412AllDirections
import ErdosProblems.Erdos1166.Erdos1166HLOZLemma411412CodedAtoms
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47Prop45YColumns
import ErdosProblems.Erdos1166.Erdos1166HLOZProp49CanonicalRefinement
import ErdosProblems.Erdos1166.Erdos1166HLOZStoppedHistoryFactorization

/-!
# Literal source closure for Erdős 1166

This module composes the strongest source-facing pieces without
reintroducing the abstract named estimates.  The Euclidean Appendix input is
reduced to literal stopped-annulus atoms, primitive exit/tail lower bounds,
and four scale-uniform analytic fields.  Its two-point field is the
corner-normalized canonical-right certificate; the legacy potential-boundary
alternative is not part of this literal cut.  The Lemma 4.10 input is reduced to
the four proved checkerboard parity/winner packages plus the two literal
terminal column phases.  Lemmas
4.11--4.12 use the canonical quarter-log-square threshold in every branch,
and Proposition 4.9 uses refined
atoms that already contain the complete preceding history.

The theorem below is deliberately still conditional on the genuinely open
source data: the literal stopped-source witnesses and deterministic
candidate pullbacks on the nonempty Lemma-4.10 code fibres, and the global
full-walk-prefix switch for equation (4.47).  In the Lemma-4.10 layer the
outer stopped atoms are fibres of natural-valued codes, so their covers and
within-branch disjointness are proved by Lean rather than retained as source
fields.  For equation (4.47), each bad or artificial-`I_0` witness atom is a
finite family of genuine first-stopping prefixes.  Lean transports those
cylinders to path space, proves their exact masses as finite sums of
`4^{-length}`, and derives (4.54) path disjointness from the source's
fixed-count disjoint finite prefix families and the stopping-time prefix
property.  No global witness-label function, or coherence between different
counts, is assumed.  On each fixed nonempty deleted-path bad fibre the source
now retains a finite witness family, its explicit bad/witness equivalence, a
nonzero upper singleton in every selected coordinate, the cross-multiplied
relative weight identity for each matched prefix, and the one-coordinate
likelihood ratio.  Lean proves the all-upper product is nonzero, reconstructs the common
background weight by division, sums the two encoded fibres, chooses
the optimal binomial layer, fixes the witness stopping horizon to the
creation of the `(k + t_*)`-th level-`m` site, and derives both
common-normalizer categorical identities, the exponential rate, and the
comparison of the two finite prefix-weight sums.  Lean gives an empty bad
fibre the empty witness family, its unique empty equivalence, and the inactive
Dirac category, so none of those data or their likelihood proof is a source
obligation there.  This is a genuinely global
path switch: the
deleted nearest-neighbor path remains fixed in each source fibre, but the
artificial `I_0` holding-coordinate assignment may change the full-walk
stopped horizon and leave the original below-`m` profile atom.  No
same-below-`m`-profile rectangular surrogate is used by this closure.  The
four checkerboard pairings and two temporal
column phases are included in the four branch families; the reflected
profile exception for `Y'` is paid as an auxiliary theta event rather than
identified with the canonical temporal event.  We do not derive the base
step from the below-`m` adjacent-band comparison used for the later
recursion: that comparison only sees genuine levels `ell >= 2`, whereas
(4.47) changes full-walk holding blocks and hence the stopped prefix length
in order to use `I_0` above `m`.
The final input is the refined-history Proposition 4.9 data.  At the first
screening stage for all six pairings, the checked parity/winner or terminal
column stopped laws supply the narrow-band estimate internally once the
raw-code fibre is identified with literal data.  The branch screens are the
canonical winner/parity intersections; their cover of the full screen is
proved internally from (4.40), quarter turns, and the assembled `Y`/`Y'`
reflection.
Quarter-turn invariance handles the four checkerboard pairings, while exact
ordered-history reflection handles `Y'` after the two temporal `Y` phases.
At a later checkerboard stage the source may provide either the literal
unnormalized history-conditioned narrow-band estimate from Proposition 4.9
or the deterministic full-complement fibre criterion that lets the checked
joint law imply it.  At a genuinely later
unreflected `Y` stage the source may likewise use either the literal
unnormalized history-conditioned narrow-band estimate from Proposition 4.9
or the deterministic full-complement fibre criterion for the checked
profile-generic terminal law.  The reflected `Y'` stage has the same
alternative after reflecting the complete joint law; its criterion is stated
against the actual `Y'` history, so no equality of the two later histories is
assumed.  Neither interface postulates an exact product law after
conditioning on the complete preceding history.
For every nonempty code fibre the strongest source package now supplies only
the one case selected by its pairing index and by whether the stage is zero;
Lean reconstructs the former six implication-shaped alternatives internally.
The six pairing indices are assembled internally by
quarter-turn and reflection transport.  This is an integration theorem, not
an assertion that those estimates have already been proved.  All six entries
now use the literal temporal-parity deletion profiles of HLOZ (2.12).
-/

namespace Erdos1166.HLOZFinalSourceClosure

open Filter MeasureTheory
open scoped ENNReal Topology

open HLOZAppendixADiskSuccess HLOZLemma410Prop48XDirections
open HLOZAppendixAShapeBridge HLOZProp13FromAppendix HLOZProp47Canonical
open HLOZProp47FarGap HLOZProp47Parameters HLOZProp47SourceAssembly
open HLOZProp47Prop45YColumns HLOZPairing HLOZPairingProfiles
open HLOZProp47Lemma411412Connector HLOZStoppedHistoryFactorization
open HLOZProp47Lemma411412SourceAtoms
open HLOZProp47Lemma411412XEastBridge
open HLOZProp47Lemma411412XDirections
open HLOZProp47Lemma411412AllDirections HLOZColumnSourceConsumers
open HLOZProp49CanonicalRefinement
open HLOZLemma410Prop48YColumns
open HLOZLemma410CodedAtoms
open HLOZLemma411412CodedAtoms
open HLOZEquation447

abbrev Path := ℕ → Site

/-- The canonical threshold retained after the four-way
winner/parity pigeonhole step in equations (4.39)--(4.40). -/
noncomputable def sourceEquation447ThresholdCoeff : ℝ := 1 / 4

lemma sourceEquation447ThresholdCoeff_pos :
    0 < sourceEquation447ThresholdCoeff := by
  norm_num [sourceEquation447ThresholdCoeff]

/-! ### Canonical all-six Equation-(4.47) branch events -/

/-- The four X-east winner/stopping-parity events in their canonical order. -/
def sourceEquation447XEastBranchEvent
    (m : ℕ) (r : StageIndex) : Fin 4 → Set Path := ![
  xEastEquation447UnprimedEvenBranch m r,
  xEastEquation447UnprimedOddBranch m r,
  xEastEquation447PrimedOddBranch m r,
  xEastEquation447PrimedEvenBranch m r]

/-- Duplicate the two temporal column phases into the common four-branch
index type.  This is only a finite-union bookkeeping device; no
cross-branch disjointness is asserted. -/
def sourceEquation447ColumnBranchIndex : Fin 4 → Fin 2 := ![0, 1, 0, 1]

/-- The two unreflected temporal column events. -/
def sourceEquation447YBranchEvent
    (m : ℕ) (r : StageIndex) : Fin 2 → Set Path := ![
  yEquation447ForwardBranch m r,
  yEquation447BackwardBranch m r]

/-- Canonical branch event for every pairing index.  The four checkerboard
events are inverse quarter-turn pullbacks of X-east.  The final two entries
are the reunited Y phases and their reflection pullback. -/
def sourceEquation447CanonicalBranchEvent
    (m : ℕ) (i : Fin 6) (r : StageIndex) : Fin 4 → Set Path :=
  match i.1 with
  | 0 => sourceEquation447XEastBranchEvent m r
  | 1 => fun j ↦ orientPath (rotationInverseDir (1 : Dir)) ⁻¹'
      sourceEquation447XEastBranchEvent m r j
  | 2 => fun j ↦ orientPath (rotationInverseDir (2 : Dir)) ⁻¹'
      sourceEquation447XEastBranchEvent m r j
  | 3 => fun j ↦ orientPath (rotationInverseDir (3 : Dir)) ⁻¹'
      sourceEquation447XEastBranchEvent m r j
  | 4 => fun j ↦ sourceEquation447YBranchEvent m r
      (sourceEquation447ColumnBranchIndex j)
  | _ => fun j ↦ reflectPath ⁻¹' sourceEquation447YBranchEvent m r
      (sourceEquation447ColumnBranchIndex j)

/-- The fixed four branch events cover the canonical cardinality failure
for all six pairings. -/
theorem lemma411412CardinalityFailureEvent_subset_canonicalBranchEvents
    (m : ℕ) (i : Fin 6) (r : StageIndex) (hm : 0 < m) :
    lemma411412CardinalityFailureEvent m i r ⊆
      ⋃ j, sourceEquation447CanonicalBranchEvent m i r j := by
  fin_cases i
  · intro s hs
    have h := lemma411412CardinalityFailureEvent_xEast_subset_canonicalBranches
      m r hm hs
    rcases h with ((h | h) | h) | h
    · exact Set.mem_iUnion.mpr ⟨0, h⟩
    · exact Set.mem_iUnion.mpr ⟨1, h⟩
    · exact Set.mem_iUnion.mpr ⟨2, h⟩
    · exact Set.mem_iUnion.mpr ⟨3, h⟩
  · intro s hs
    have hsEast : orientPath (rotationInverseDir (1 : Dir)) s ∈
        lemma411412CardinalityFailureEvent m (xIndex east) r := by
      change s ∈ orientPath (rotationInverseDir (1 : Dir)) ⁻¹'
        lemma411412CardinalityFailureEvent m (xIndex east) r
      rw [lemma411412CardinalityFailureEvent_x_preimage_inverse]
      simpa [xIndex] using hs
    have h := lemma411412CardinalityFailureEvent_xEast_subset_canonicalBranches
      m r hm hsEast
    rcases h with ((h | h) | h) | h
    · exact Set.mem_iUnion.mpr ⟨0, h⟩
    · exact Set.mem_iUnion.mpr ⟨1, h⟩
    · exact Set.mem_iUnion.mpr ⟨2, h⟩
    · exact Set.mem_iUnion.mpr ⟨3, h⟩
  · intro s hs
    have hsEast : orientPath (rotationInverseDir (2 : Dir)) s ∈
        lemma411412CardinalityFailureEvent m (xIndex east) r := by
      change s ∈ orientPath (rotationInverseDir (2 : Dir)) ⁻¹'
        lemma411412CardinalityFailureEvent m (xIndex east) r
      rw [lemma411412CardinalityFailureEvent_x_preimage_inverse]
      simpa [xIndex] using hs
    have h := lemma411412CardinalityFailureEvent_xEast_subset_canonicalBranches
      m r hm hsEast
    rcases h with ((h | h) | h) | h
    · exact Set.mem_iUnion.mpr ⟨0, h⟩
    · exact Set.mem_iUnion.mpr ⟨1, h⟩
    · exact Set.mem_iUnion.mpr ⟨2, h⟩
    · exact Set.mem_iUnion.mpr ⟨3, h⟩
  · intro s hs
    have hsEast : orientPath (rotationInverseDir (3 : Dir)) s ∈
        lemma411412CardinalityFailureEvent m (xIndex east) r := by
      change s ∈ orientPath (rotationInverseDir (3 : Dir)) ⁻¹'
        lemma411412CardinalityFailureEvent m (xIndex east) r
      rw [lemma411412CardinalityFailureEvent_x_preimage_inverse]
      simpa [xIndex] using hs
    have h := lemma411412CardinalityFailureEvent_xEast_subset_canonicalBranches
      m r hm hsEast
    rcases h with ((h | h) | h) | h
    · exact Set.mem_iUnion.mpr ⟨0, h⟩
    · exact Set.mem_iUnion.mpr ⟨1, h⟩
    · exact Set.mem_iUnion.mpr ⟨2, h⟩
    · exact Set.mem_iUnion.mpr ⟨3, h⟩
  · intro s hs
    have h := lemma411412CardinalityFailureEvent_y_subset_canonicalBranches
      m r hs
    rcases h with h | h
    · exact Set.mem_iUnion.mpr ⟨0, h⟩
    · exact Set.mem_iUnion.mpr ⟨1, h⟩
  · intro s hs
    have hsY : reflectPath s ∈
        lemma411412CardinalityFailureEvent m yIndex r := by
      change s ∈ reflectPath ⁻¹'
        lemma411412CardinalityFailureEvent m yIndex r
      rw [lemma411412CardinalityFailureEvent_yPrime_preimage]
      simpa [yIndex'] using hs
    have h := lemma411412CardinalityFailureEvent_y_subset_canonicalBranches
      m r hsY
    rcases h with h | h
    · exact Set.mem_iUnion.mpr ⟨0, h⟩
    · exact Set.mem_iUnion.mpr ⟨1, h⟩

/-- Strongest all-six Equation-(4.47) source interface used by the final
closure.  Branch events, their cover, and the quarter-log-square threshold
are all fixed and proved above; the source supplies only one literal finite
prefix encoding, indexed by a natural-valued deleted-path code, and its direct
cylinder cover on each fixed branch.  No auxiliary code type or countability
instance remains in this interface.  The
generic connector reconstructs its internal count-indexed event family from
those cylinders.  A standalone IID theorem derives the
exact quarter probability for
any stopped-past raw event, so neither ordinary nor stopped-past measurability
is stored in this package.  For the possibly fresh-step-dependent auxiliary
`Theta` event, Lean instead proves that the four prescribed-direction events
cover the post-`Theta` branch on the random-walk support, canonically selects
one of maximal probability, and derives the factor-four reduction by finite
subadditivity.  Thus neither a direction choice nor a post-`Theta` probability
inequality is stored in this package. -/
def Prop47Lemma411412CanonicalStoppedPrefixCategoricalEncodingInputs
    (ratioC : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i : Fin 6, ∀ r : StageIndex,
    Nonempty ((j : Fin 4) →
      Equation447StoppedPrefixCategoricalForcedDirectionBranchData
        m (stageNumber r) ratioC
          (sourceEquation447CanonicalBranchEvent m i r j)
          (sourceEquation447ThetaTarget m i r)
          (sourceEquation447ThresholdCoeff * Real.log (m : ℝ) ^ 2))

/-- Forget the canonical choices to obtain the flexible all-six encoding
interface used by the generic connector. -/
theorem
    finiteBranchStoppedPrefixCategoricalEncodingAuxThetaInputs_of_canonical
    (ratioC : ℝ)
    (h : Prop47Lemma411412CanonicalStoppedPrefixCategoricalEncodingInputs
      ratioC) :
    Prop47Lemma411412FiniteBranchStoppedPrefixCategoricalEncodingAuxThetaInputs
      sourceEquation447ThetaTarget 4 ratioC := by
  filter_upwards [h, eventually_ge_atTop (1 : ℕ)] with m hm hmOne
  intro i r
  rcases hm i r with ⟨branches⟩
  refine ⟨sourceEquation447CanonicalBranchEvent m i r,
    fun _ ↦ sourceEquation447ThresholdCoeff * Real.log (m : ℝ) ^ 2,
    fun j ↦ (branches j).toCategoricalEncodingBranchData, ?_, ?_⟩
  · exact lemma411412CardinalityFailureEvent_subset_canonicalBranchEvents
      m i r (by omega)
  · intro j
    exact le_rfl

/-- The exact remaining literal source cut, bundled as one reusable object.

Unlike the public compatibility wrapper in `Erdos1166.lean`, this record does
not assume `HLOZPlanarConclusion` or any of the four named Proposition-4.7
estimates.  Its fields are precisely the stopped-annulus cylinder input, the
theta-free four-X and two-column Lemma-4.10 packages, the literal X/Y
equation-(4.47) packages, and the later-stage coded Proposition-4.9 input. -/
structure LiteralSourceInputs where
  prop49LocalCoeff : ℕ
  prop410Window : ℕ
  Csmall : ℝ
  Csmall_pos : 0 < Csmall
  xLemma410 : Prop47Lemma410Prop48CanonicalCodedRectangularXEastLowBandInputs
    prop410Window
      (Real.exp (HLOZBandRatios.sourceAdjacentComparisonExponent
        prop410Window)) Csmall
  yLemma410 : Prop47Lemma410Prop48CanonicalCodedRectangularYTwoPhaseLowBandInputs
    prop410Window
      (Real.exp (HLOZBandRatios.sourceAdjacentComparisonExponent
        prop410Window)) Csmall
  /- The base-step source package is global path-space data.  Each bad and
  artificial-`I₀` witness atom is a finite family of genuine first-stopping
  prefixes, so Lean derives its exact `4^{-length}` mass, measurability, and
  (4.54) path-event witness disjointness from fixed-count disjointness of the
  finite witness-prefix families.  It does not supply a global witness label
  coherent across counts.  On each fixed nonempty deleted-path bad fibre the
  source supplies a finite witness family and bad/witness equivalence, nonzero
  upper coordinate cells, the relative bad/witness prefix-weight identity,
  and the raw one-coordinate likelihood ratio.  Lean proves nonvanishing of
  their finite product,
  constructs the common background normalizer by division, sums these
  encodings, chooses the optimal binomial layer, fixes
  the witness stopping horizon to `k + t_*`, and
  derives the two categorical identities, exponential rate, and
  prefix-weight comparison.  Empty bad fibres receive an internal empty
  witness family, its unique empty equivalence, and the inactive Dirac
  category; they require no corresponding source data or likelihood proof. -/
  equation447 :
    Prop47Lemma411412CanonicalStoppedPrefixCategoricalEncodingInputs
      (Real.exp (HLOZBandRatios.sourceAdjacentComparisonExponent
        prop410Window))
  diskC : ℝ
  diskE : ℝ
  diskAnnulusCost : ℝ
  disk : ∀ᶠ n : ℕ in atTop,
    Nonempty (EuclideanDiskFiniteCylinderLengthPackage
      n diskC diskE diskAnnulusCost)
  prop49 : ∀ᶠ m : ℕ in atTop,
    Nonempty
      (Prop47CanonicalScreensCodedLaterStagePackage m prop49LocalCoeff)

set_option linter.constructorNameAsVariable false in
/-- The strongest fully assembled closure currently exposed.

Its equation-(4.47) input uses finite families of genuine stopped prefixes
for the all-upper paths and their artificial-lower changed-path witnesses.
Lean fixes their witness stopping count to `k + t_*`, proves the exact
cylinder masses and (4.54) disjointness, and sums the
count layers, absorbing the geometric loss above the canonical
quarter-log-square threshold.  Thus no path-event probability,
measurability, or path-event witness-disjointness statement is stored as source data.
This theorem is still a conditional source closure: it does not assert that
the finite changed-prefix families and their relative categorical weight
identities, or the
remaining Appendix and Proposition-4.9 fibre source
packages, have already been constructed.

Compared with
`hlozPlanarConclusion_of_named_estimates_terminalY_refinedProp49Branches`,
the far-gap input is constructed from literal stopped-annulus atoms and
primitive exit/tail estimates, the Lemma 4.10 input is constructed from
natural-valued codes for the four X branches and the two temporal column
phases (so cover and within-branch disjointness are automatic), the
Lemmas 4.11--4.12 estimate is constructed from its
finite branch atomization, and the Proposition 4.9 connector is constructed
from history-contained refined atoms.  The X-east Proposition 4.5
atomization is also constructed internally from Appendix A, Proposition 4.4,
and the X-east stopped-clock compatibility is derived internally from the
certainly completed upper prefix.  The two literal temporal column cases of
Proposition 4.5 are bounded internally by the same pairing-independent
threshold event.  The Proposition-4.9 branch type is fixed to the four
winner/stopping-parity cases rather than supplied by the caller.  At each of
the four checkerboard pairings Lean also reconstructs the unique quarter-turn
direction directly from the pairing index, so neither that direction nor its
index equality is retained in the literal source package.  Its Proposition-4.9
code need not be measurable: a literal atom package is required only for an
ordered fibre that actually meets its canonical branch screen, and all other
refined atoms are discarded as empty before the finite-union connector. -/
theorem hlozPlanarConclusion_of_literalSourceInputs
    (prop49LocalCoeff : ℕ)
    (prop410Window : ℕ)
    (Csmall : ℝ)
    (hCsmall : 0 < Csmall)
    (hX : Prop47Lemma410Prop48CanonicalCodedRectangularXEastLowBandInputs
      prop410Window
        (Real.exp (HLOZBandRatios.sourceAdjacentComparisonExponent
          prop410Window)) Csmall)
    (hY : Prop47Lemma410Prop48CanonicalCodedRectangularYTwoPhaseLowBandInputs
      prop410Window
        (Real.exp (HLOZBandRatios.sourceAdjacentComparisonExponent
          prop410Window)) Csmall)
    (h411Prefixes :
      Prop47Lemma411412CanonicalStoppedPrefixCategoricalEncodingInputs
        (Real.exp (HLOZBandRatios.sourceAdjacentComparisonExponent
          prop410Window)))
    (diskC diskE diskAnnulusCost : ℝ)
    (hDisk : ∀ᶠ n : ℕ in atTop,
      Nonempty (EuclideanDiskFiniteCylinderLengthPackage
        n diskC diskE diskAnnulusCost))
    (hProp49Packages : ∀ᶠ m : ℕ in atTop,
      Nonempty
        (Prop47CanonicalScreensCodedLaterStagePackage
          m prop49LocalCoeff)) :
    HLOZPlanarConclusion := by
  have hEuclidean : EuclideanAppendixDiskEstimate :=
    euclideanAppendixDiskEstimate_of_eventually_finiteCylinderLengthPackages
      diskC diskE diskAnnulusCost hDisk
  have hFar : Prop47FarGapEstimate 1 :=
    prop47FarGapEstimate_of_euclideanAppendixDiskEstimate hEuclidean
  have hSquareDisk : AppendixDiskEstimate :=
    appendixDiskEstimate_of_euclidean hEuclidean
  have hProp45 : Prop47Prop45Estimate sourceCanonicalProfiles canonicalCStar 10 :=
    sourceCanonical_prop45Estimate hSquareDisk
  let equation447Ratio :=
    Real.exp (HLOZBandRatios.sourceAdjacentComparisonExponent prop410Window)
  have hEquation447Ratio : 0 < equation447Ratio := by
    exact Real.exp_pos _
  let equation447Rate := categoricalOptimalRate equation447Ratio
  have hEquation447Rate : 0 < equation447Rate := by
    simpa only [equation447Rate] using
      categoricalOptimalRate_pos equation447Ratio hEquation447Ratio
  have h411Categorical :
      Prop47Lemma411412FiniteBranchStoppedPrefixOptimalCategoricalAuxThetaInputs
        sourceEquation447ThetaTarget 4 equation447Ratio := by
    have h411Encoded :
        Prop47Lemma411412FiniteBranchStoppedPrefixCategoricalEncodingAuxThetaInputs
          sourceEquation447ThetaTarget 4 equation447Ratio := by
      simpa only [equation447Ratio] using
        finiteBranchStoppedPrefixCategoricalEncodingAuxThetaInputs_of_canonical
          equation447Ratio h411Prefixes
    exact
      finiteBranchStoppedPrefixOptimalCategoricalAuxThetaInputs_of_encoding
        sourceEquation447ThetaTarget 4 equation447Ratio h411Encoded
  have h411PrefixSwitch :
      Prop47Lemma411412FiniteBranchStoppedPrefixChangedPathAuxThetaInputs
        sourceEquation447ThetaTarget 4 equation447Rate
          sourceEquation447ThresholdCoeff := by
    simpa only [equation447Ratio, equation447Rate,
      sourceEquation447ThresholdCoeff] using
      finiteBranchStoppedPrefixChangedPathAuxThetaInputs_of_optimalCategorical
        sourceEquation447ThetaTarget 4 equation447Ratio
          hEquation447Ratio h411Categorical
  have hXPathWitness :
      Prop47Lemma410Prop48CanonicalCodedPathWitnessXEastLowBandInputs
        prop410Window equation447Rate Csmall := by
    simpa only [equation447Ratio, equation447Rate] using
      codedPathWitnessXEastLowBandInputs_of_rectangular
        prop410Window hEquation447Ratio hX
  have hYPathWitness :
      Prop47Lemma410Prop48CanonicalCodedPathWitnessYTwoPhaseLowBandInputs
        prop410Window equation447Rate Csmall := by
    simpa only [equation447Ratio, equation447Rate] using
      codedPathWitnessYTwoPhaseLowBandInputs_of_rectangular
        prop410Window hEquation447Ratio hY
  let xBase := equation447Rate / 8
  let yBase := equation447Rate / 8
  let imbalance := HLOZLemma411Recursion.imbalanceRate
    (Real.exp (HLOZBandRatios.sourceAdjacentComparisonExponent
      prop410Window))
  have hxBase : 0 < xBase := by
    dsimp [xBase]
    positivity
  have hyBase : 0 < yBase := by
    dsimp [yBase]
    positivity
  let xRate := min xBase imbalance / 2
  let yRate := min yBase imbalance / 2
  let d : ℝ :=
    min xRate yRate / 16
  have himbalance : 0 < imbalance := by
    dsimp [imbalance]
    exact
    HLOZLemma411Recursion.imbalanceRate_pos
      (Real.one_le_exp (by positivity))
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hcommonNonneg : 0 ≤ min xRate yRate := by
    dsimp [xRate, yRate]
    positivity
  have hcompareX : 16 * d ≤
      min (equation447Rate / 8)
        (HLOZLemma411Recursion.imbalanceRate
          (Real.exp (HLOZBandRatios.sourceAdjacentComparisonExponent
            prop410Window))) / 2 := by
    change 16 * d ≤ xRate
    dsimp [d]
    nlinarith [min_le_left xRate yRate]
  have hcompareY : 8 * d ≤
      min (equation447Rate / 8)
        (HLOZLemma411Recursion.imbalanceRate
          (Real.exp (HLOZBandRatios.sourceAdjacentComparisonExponent
            prop410Window))) / 2 := by
    change 8 * d ≤ yRate
    dsimp [d]
    nlinarith [hcommonNonneg, min_le_right xRate yRate]
  have hXEstimate : Prop47Lemma410EstimateXDirections 11 :=
    prop47Lemma410EstimateXDirections_of_codedPathWitness_inputs
      prop410Window 10 hEquation447Rate hCsmall (by rfl) hd
        hcompareX hXPathWitness hProp45
  have hYEstimate : HLOZLemma410Prop48YColumns.Prop47Lemma410EstimateYColumns 11 :=
    prop47Lemma410EstimateYColumns_of_codedPathWitness_inputs
      prop410Window 10 hEquation447Rate hCsmall (by rfl) hd
        hcompareY hYPathWitness hProp45
  have hLemma410 : Prop47Lemma410Estimate 11 :=
    HLOZLemma410Prop48YColumns.prop47Lemma410Estimate_of_x_y_inputs
      hXEstimate hYEstimate
  have h411 : Prop47Lemma411412FiniteBranchChangedPathAuxThetaInputs
      sourceEquation447ThetaTarget 4 equation447Rate
        sourceEquation447ThresholdCoeff := by
    exact finiteBranchChangedPathAuxThetaInputs_of_stoppedPrefixes
      sourceEquation447ThetaTarget 4 equation447Rate
        sourceEquation447ThresholdCoeff h411PrefixSwitch
  have h411Theta : Prop47Lemma411412AuxThetaEstimate
      sourceEquation447ThetaTarget 10 :=
    sourceEquation447AuxThetaEstimate_of_prop45 10 hProp45
  have hLemma411412 : Prop47Lemma411412Estimate 21 :=
    prop47Lemma411412Estimate_of_finiteBranchChangedPathAuxThetaInputs
      sourceEquation447ThetaTarget 4 10 10
      hEquation447Rate sourceEquation447ThresholdCoeff_pos
      h411 hProp45 h411Theta
  let branchScreen := canonicalProp49BranchScreen
  let rawCode := selectedCanonicalProp49RawCode prop49LocalCoeff
  let refinedAtom := fun m i a r j code ↦ canonicalScreenedOrderedHistoryAtom
    (rawCodeFiber (rawCode m i a r j)) sourceCanonicalProfiles canonicalCStar
      m i a r (branchScreen m i a r j) code
  have hProp49Contained :
      Prop47StoppedProfileProp49HistoryContainedFiniteBranchEstimate
        sourceCanonicalProfiles canonicalCStar
        4 prop49LocalCoeff branchScreen refinedAtom := by
    simpa only [branchScreen, rawCode, refinedAtom] using
      prop47StoppedProfileProp49HistoryContainedFiniteBranchEstimate_of_canonicalPackages
        prop49LocalCoeff hProp49Packages
  have hProp49 :
      HLOZProp47LowStageConnector.Prop47StoppedProfileProp49RefinedFiniteBranchEstimate
        sourceCanonicalProfiles canonicalCStar
        4 prop49LocalCoeff
        branchScreen refinedAtom :=
    prop47StoppedProfileProp49RefinedFiniteBranchEstimate_of_historyContained
      sourceCanonicalProfiles canonicalCStar 4
      prop49LocalCoeff branchScreen refinedAtom hProp49Contained
  have hLowBase : Prop47LowStageEstimate sourceCanonicalProfiles canonicalCStar
      (4 * prop49LocalCoeff)
      (prop47FailurePrefactor 1 11 10 21) :=
    HLOZProp47LowStageConnector.prop47LowStageEstimate_of_refinedFiniteBranches
      sourceCanonicalProfiles canonicalCStar 4 prop49LocalCoeff 128
      (prop47FailurePrefactor 1 11 10 21)
      branchScreen refinedAtom
      HLOZProp47LowEscape.sourceCanonical_prop47SequentialEscapeEstimate hProp49
  let stageCoeff : ℕ := max 64 (4 * prop49LocalCoeff)
  have hLow : Prop47LowStageEstimate sourceCanonicalProfiles canonicalCStar
      stageCoeff (prop47FailurePrefactor 1 11 10 21) :=
    prop47LowStageEstimate_mono_stageCoeff sourceCanonicalProfiles canonicalCStar
      (Nat.le_max_right 64 (4 * prop49LocalCoeff)) hLowBase
  have hHigh : Prop47HighStageEstimate sourceCanonicalProfiles canonicalCStar
      stageCoeff
      (prop47FailurePrefactor 1 11 10 21) :=
    HLOZProp47HighStageConnector.prop47HighStageEstimate_of_highEscape
      sourceCanonicalProfiles canonicalCStar
      stageCoeff
      (prop47FailurePrefactor 1 11 10 21)
      (HLOZProp47HighEscape.sourceCanonical_prop47HighEscapeEstimate_mono
        stageCoeff (Nat.le_max_left 64 (4 * prop49LocalCoeff)))
  exact hlozPlanarConclusion_of_prop47_named_source_estimates
    sourceCanonicalProfiles canonicalCStar
    stageCoeff 1 11
    10 21
    hFar hLemma410 hProp45 hLemma411412 hLow hHigh

/-- The bundled literal source cut implies the planar HLOZ conclusion. -/
theorem LiteralSourceInputs.toPlanarConclusion
    (I : LiteralSourceInputs) : HLOZPlanarConclusion :=
  hlozPlanarConclusion_of_literalSourceInputs
    I.prop49LocalCoeff I.prop410Window
    I.Csmall I.Csmall_pos
    I.xLemma410 I.yLemma410
    I.equation447
    I.diskC I.diskE I.diskAnnulusCost I.disk
    I.prop49

/-- Direct Erdős-1166 endpoint from the exact literal source cut.  This
wrapper makes explicit that no separate `HLOZPlanarConclusion` assumption is
needed once a `LiteralSourceInputs` package has been constructed. -/
theorem erdos1166_of_literalSourceInputs (I : LiteralSourceInputs) :
    ∀ᵐ s ∂simpleRandomWalkLaw, HasCumulativeFavoriteLogSqBound s :=
  Erdos1166.erdos_1166_of_hloz I.toPlanarConclusion

#print axioms hlozPlanarConclusion_of_literalSourceInputs
#print axioms erdos1166_of_literalSourceInputs

end Erdos1166.HLOZFinalSourceClosure
