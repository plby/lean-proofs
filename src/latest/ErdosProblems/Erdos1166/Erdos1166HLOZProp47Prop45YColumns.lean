/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1166.Erdos1166HLOZColumnPairRuns
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47Prop45XRotations
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47HighEscape
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47SequentialEscape

/-!
# The two column encodings in HLOZ Proposition 4.5

The column pairing is not a translate of the origin-started `X₁` walk.
Accordingly this file records a genuinely separate finite atomization for
each phase of `Y`.  Its irreducible probabilistic inputs are the fixed-column
inverse-clock negative-binomial laws.  Only after the two phases have been
assembled is the full event transported to `Y'`, using reflection in the
vertical axis, which fixes the origin and preserves the random-walk law.
-/

namespace Erdos1166.HLOZProp47Prop45YColumns

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

open HLOZFoundation HLOZDecomposition HLOZUrn
open HLOZProp47Parameters HLOZProp47SourceObjects
open HLOZProp45SourceClock HLOZProp45SourceInterval
open HLOZProp45SourceMirrors HLOZProp45SourceEndpoints
open HLOZProp45SourceAbsorption HLOZProp47Canonical
open HLOZProp47Prop45Connector HLOZProp47SourceAssembly
open HLOZPairing HLOZPairingProfiles HLOZPairing.ScreeningBridge
open HLOZProp47Prop45XRotations
open HLOZProp47Prop45XEast
open HLOZSourceInstantiation
open HLOZColumnPairRuns HLOZReconstruction HLOZPrimedStopped
open HLOZProp42InverseLaw

abbrev Path := ℕ → Site

noncomputable def yUnprimedThetaEvent (m k : ℕ) : Set Path :=
  {s | (stoppedThetaHalfSites
        (deletionExternalLocalTime yDeletion true)
        yDeletion.distinguished false 10 s m k ∪
      stoppedThetaHalfSites
        (deletionExternalLocalTime yDeletion true)
        yDeletion.distinguished true 10 s m k).Nonempty}

noncomputable def yPrimedThetaEvent (m k : ℕ) : Set Path :=
  {s | (stoppedThetaHalfSites
        (deletionExternalLocalTime yDeletion false)
        (fun x ↦ ¬ yDeletion.distinguished x) false 10 s m k ∪
      stoppedThetaHalfSites
        (deletionExternalLocalTime yDeletion false)
        (fun x ↦ ¬ yDeletion.distinguished x) true 10 s m k).Nonempty}

/-! ### The exact fixed-column parser interface

For a fixed deleted column path there is one chronological vector of
two-step holding counts.  Its coordinates have the product geometric law;
the holding prefix at a site is the sum over the first distinct coordinates
at which the deleted path visits that site.  This is the precise interface
between the adaptive column parser and Proposition 4.5.  In particular, the
two scalar negative-binomial laws used below are consequences, rather than
independent per-site assumptions. -/

/-- A fixed-phase column parser on a conditioning atom `C`.  The remaining
probabilistic content is a *single joint* iid-geometric law for the parsed
holding vector.  `prefix_eq` is the deterministic decoder statement that
identifies the phase's inverse clock with chronological subvector sums. -/
structure YPhaseColumnParser
    (m k : ℕ) (C : Set Path) (clock : PrimedShiftedDeletionClock m k) where
  q : ℕ
  holdingVector : Path → Fin q → ℕ
  visitIndices : Site → List (Fin q)
  visitIndices_nodup : ∀ x, (visitIndices x).Nodup
  measurable_atom : MeasurableSet C
  holdingVector_law : HasLaw holdingVector (runVectorMeasure q)
    simpleRandomWalkLaw[|C]
  prefix_eq : ∀ (x : Site) (cut : ℕ)
    (hcut : cut ≤ (visitIndices x).length), ∀ s ∈ C,
      clock.inverseHoldingPrefix s cut x =
        ∑ i : Fin cut,
          holdingVector s ((visitIndices x).get (Fin.castLE hcut i))

/-- Purely deterministic data connecting an adaptive finite pair encoding
to one column inverse clock.  The iid-geometric law is intentionally absent:
`toColumnParser` derives it from
`pathConditionalSelectiveRunVector_hasLaw`. -/
structure YPhaseSelectiveParserInputs
    (m k start : ℕ) (specs : List (Bool × IncrementPair))
    (e : SelectivePairVectorEncoding start specs)
    (clock : PrimedShiftedDeletionClock m k) where
  valid : SelectiveTerminalValid specs
  visitIndices : Site → List (Fin e.q)
  visitIndices_nodup : ∀ x, (visitIndices x).Nodup
  prefix_eq : ∀ (x : Site) (cut : ℕ)
    (hcut : cut ≤ (visitIndices x).length),
    ∀ s ∈ selectiveTerminalPathAtom start specs,
      clock.inverseHoldingPrefix s cut x =
        ∑ i : Fin cut,
          pathConditionalSelectiveRunVector e s
            ((visitIndices x).get (Fin.castLE hcut i))

/-- Build the Proposition-4.5 column parser from finite adaptive parser
data.  This theorem is the law bridge: only deterministic coverage,
uniqueness, and inverse-clock identification remain in the input. -/
noncomputable def YPhaseSelectiveParserInputs.toColumnParser
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    {e : SelectivePairVectorEncoding start specs}
    {clock : PrimedShiftedDeletionClock m k}
    (h : YPhaseSelectiveParserInputs m k start specs e clock) :
    YPhaseColumnParser m k (selectiveTerminalPathAtom start specs) clock where
  q := e.q
  holdingVector := pathConditionalSelectiveRunVector e
  visitIndices := h.visitIndices
  visitIndices_nodup := h.visitIndices_nodup
  measurable_atom := measurableSet_selectiveTerminalPathAtom start specs
  holdingVector_law := pathConditionalSelectiveRunVector_hasLaw e h.valid
  prefix_eq := h.prefix_eq

/-- Primed/backward analogue of `YPhaseSelectiveParserInputs`.  Its atom
fixes `(-e₁,+e₁)` runs at odd-column endpoints and is conditioned
separately from the forward atom. -/
structure YPrimedPhaseSelectiveParserInputs
    (m k start : ℕ) (specs : List (Bool × IncrementPair))
    (e : PrimedSelectivePairVectorEncoding start specs)
    (clock : PrimedShiftedDeletionClock m k) where
  valid : PrimedSelectiveTerminalValid specs
  visitIndices : Site → List (Fin e.q)
  visitIndices_nodup : ∀ x, (visitIndices x).Nodup
  prefix_eq : ∀ (x : Site) (cut : ℕ)
    (hcut : cut ≤ (visitIndices x).length),
    ∀ s ∈ primedSelectiveTerminalPathAtom start specs,
      clock.inverseHoldingPrefix s cut x =
        ∑ i : Fin cut,
          pathConditionalPrimedSelectiveRunVector e s
            ((visitIndices x).get (Fin.castLE hcut i))

/-- Build the primed Proposition-4.5 column parser from the backward
adaptive encoding.  The vector law is discharged by adjacent-pair
reversal, not assumed. -/
noncomputable def YPrimedPhaseSelectiveParserInputs.toColumnParser
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    {e : PrimedSelectivePairVectorEncoding start specs}
    {clock : PrimedShiftedDeletionClock m k}
    (h : YPrimedPhaseSelectiveParserInputs m k start specs e clock) :
    YPhaseColumnParser m k
      (primedSelectiveTerminalPathAtom start specs) clock where
  q := e.q
  holdingVector := pathConditionalPrimedSelectiveRunVector e
  visitIndices := h.visitIndices
  visitIndices_nodup := h.visitIndices_nodup
  measurable_atom :=
    measurableEmbedding_simpleRandomWalk.measurableSet_image.2
      (measurableSet_primedSelectiveTerminalLabelsEqFrom start specs)
  holdingVector_law :=
    pathConditionalPrimedSelectiveRunVector_hasLaw e h.valid
  prefix_eq := h.prefix_eq

/-! ### Canonical visit lists from parser coordinates -/

/-- Chronological coordinates whose fixed deleted-path base is `x`.
This definition removes an arbitrary per-site visit list from the parser
interface. -/
noncomputable def columnVisitIndices {q : ℕ}
    (baseAt : Fin q → Site) (x : Site) : List (Fin q) :=
  (List.finRange q).filter fun i ↦ baseAt i = x

theorem columnVisitIndices_nodup {q : ℕ}
    (baseAt : Fin q → Site) (x : Site) :
    (columnVisitIndices baseAt x).Nodup :=
  (List.nodup_finRange q).filter _

/-- Reduced deterministic input for the forward column phase.  The only
coordinate data are the base attached to each parsed run; all chronological
visit lists and their no-duplication proofs are derived.  The remaining
identity is exactly the unavoidable pathwise statement equating the
phase-specific deletion clock with those parsed holding counts. -/
structure YPhaseSelectiveClockInputs
    (m k start : ℕ) (specs : List (Bool × IncrementPair))
    (e : SelectivePairVectorEncoding start specs)
    (clock : PrimedShiftedDeletionClock m k) where
  valid : SelectiveTerminalValid specs
  baseAt : Fin e.q → Site
  clock_eq : ∀ (x : Site) (cut : ℕ)
    (hcut : cut ≤ (columnVisitIndices baseAt x).length),
    ∀ s ∈ selectiveTerminalPathAtom start specs,
      clock.inverseHoldingPrefix s cut x =
        ∑ i : Fin cut,
          pathConditionalSelectiveRunVector e s
            ((columnVisitIndices baseAt x).get (Fin.castLE hcut i))

noncomputable def YPhaseSelectiveClockInputs.toColumnParser
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    {e : SelectivePairVectorEncoding start specs}
    {clock : PrimedShiftedDeletionClock m k}
    (h : YPhaseSelectiveClockInputs m k start specs e clock) :
    YPhaseColumnParser m k (selectiveTerminalPathAtom start specs) clock :=
  (YPhaseSelectiveParserInputs.mk h.valid
    (columnVisitIndices h.baseAt)
    (columnVisitIndices_nodup h.baseAt) h.clock_eq).toColumnParser

/-- Reduced deterministic input for the independently conditioned primed
column phase. -/
structure YPrimedPhaseSelectiveClockInputs
    (m k start : ℕ) (specs : List (Bool × IncrementPair))
    (e : PrimedSelectivePairVectorEncoding start specs)
    (clock : PrimedShiftedDeletionClock m k) where
  valid : PrimedSelectiveTerminalValid specs
  baseAt : Fin e.q → Site
  clock_eq : ∀ (x : Site) (cut : ℕ)
    (hcut : cut ≤ (columnVisitIndices baseAt x).length),
    ∀ s ∈ primedSelectiveTerminalPathAtom start specs,
      clock.inverseHoldingPrefix s cut x =
        ∑ i : Fin cut,
          pathConditionalPrimedSelectiveRunVector e s
            ((columnVisitIndices baseAt x).get (Fin.castLE hcut i))

noncomputable def YPrimedPhaseSelectiveClockInputs.toColumnParser
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    {e : PrimedSelectivePairVectorEncoding start specs}
    {clock : PrimedShiftedDeletionClock m k}
    (h : YPrimedPhaseSelectiveClockInputs m k start specs e clock) :
    YPhaseColumnParser m k
      (primedSelectiveTerminalPathAtom start specs) clock :=
  (YPrimedPhaseSelectiveParserInputs.mk h.valid
    (columnVisitIndices h.baseAt)
    (columnVisitIndices_nodup h.baseAt) h.clock_eq).toColumnParser

/-! ### The concrete decoded column clock

The abstract clock used by the two-sided Chernoff estimate has four fields.
For a column atom its inverse profile and holding prefix are not extra
probabilistic data: they are read directly from the fixed chronological
base list and the single parsed holding vector.  The stopped external field
is the literal pairing deletion, while the stopped lazy field is its
complement inside local time.  The next construction packages these facts
and makes the remaining pathwise `clock_eq` judgmental. -/

theorem deletionExternalLocalTime_le_localTime
    (D : DeletionData) (forward : Bool) (s : Path) (n : ℕ) (x : Site) :
    deletionExternalLocalTime D forward s n x ≤ localTime s n x := by
  unfold deletionExternalLocalTime deletionRetainedTimes localTime
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter] at hj ⊢
  exact ⟨(Finset.mem_sdiff.mp hj.1).1, hj.2⟩

/-- A pairing-specific clock decoded from one chronological holding vector.
This is deliberately parametrized by the phase's own vector: forward and
primed atoms therefore remain separate objects. -/
noncomputable def decodedColumnClock
    (m k q : ℕ) (D : DeletionData) (forward : Bool)
    (holdingVector : Path → Fin q → ℕ) (baseAt : Fin q → Site) :
    PrimedShiftedDeletionClock m k where
  stoppedExternal s x :=
    deletionExternalLocalTime D forward s (favoriteCreationHorizon m k s) x
  stoppedLazy s x :=
    localTime s (favoriteCreationHorizon m k s) x -
      deletionExternalLocalTime D forward s (favoriteCreationHorizon m k s) x
  inverseProfile _ x := (columnVisitIndices baseAt x).length
  inverseHoldingPrefix s cut x :=
    ∑ i : Fin cut,
      if hi : i.1 < (columnVisitIndices baseAt x).length then
        holdingVector s ((columnVisitIndices baseAt x).get ⟨i.1, hi⟩)
      else 0
  stopped_decomposition s x := by
    rw [Nat.add_sub_of_le]
    exact deletionExternalLocalTime_le_localTime D forward s
      (favoriteCreationHorizon m k s) x

@[simp] theorem decodedColumnClock_stoppedExternal
    (m k q : ℕ) (D : DeletionData) (forward : Bool)
    (holdingVector : Path → Fin q → ℕ) (baseAt : Fin q → Site)
    (s : Path) (x : Site) :
    (decodedColumnClock m k q D forward holdingVector baseAt).stoppedExternal s x =
      deletionExternalLocalTime D forward s
        (favoriteCreationHorizon m k s) x := rfl

@[simp] theorem decodedColumnClock_inverseProfile
    (m k q : ℕ) (D : DeletionData) (forward : Bool)
    (holdingVector : Path → Fin q → ℕ) (baseAt : Fin q → Site)
    (s : Path) (x : Site) :
    (decodedColumnClock m k q D forward holdingVector baseAt).inverseProfile s x =
      (columnVisitIndices baseAt x).length := rfl

theorem decodedColumnClock_inverseHoldingPrefix
    (m k q : ℕ) (D : DeletionData) (forward : Bool)
    (holdingVector : Path → Fin q → ℕ) (baseAt : Fin q → Site)
    (s : Path) (x : Site) (cut : ℕ)
    (hcut : cut ≤ (columnVisitIndices baseAt x).length) :
    (decodedColumnClock m k q D forward holdingVector baseAt).inverseHoldingPrefix
        s cut x =
      ∑ i : Fin cut,
        holdingVector s
          ((columnVisitIndices baseAt x).get (Fin.castLE hcut i)) := by
  change (∑ i : Fin cut,
      if hi : i.1 < (columnVisitIndices baseAt x).length then
        holdingVector s ((columnVisitIndices baseAt x).get ⟨i.1, hi⟩)
      else 0) = _
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with hi
  · congr 1
  · exact (hi (lt_of_lt_of_le i.2 hcut)).elim

/-- Forward column parser data with no inverse-clock equality premise.
The decoded clock is constructed from the parser itself. -/
structure YPhaseDecodedClockInputs
    (m k start : ℕ) (specs : List (Bool × IncrementPair))
    (e : SelectivePairVectorEncoding start specs) where
  valid : SelectiveTerminalValid specs
  baseAt : Fin e.q → Site

noncomputable def YPhaseDecodedClockInputs.clock
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    {e : SelectivePairVectorEncoding start specs}
    (h : YPhaseDecodedClockInputs m k start specs e) :
    PrimedShiftedDeletionClock m k :=
  decodedColumnClock m k e.q yDeletion true
    (pathConditionalSelectiveRunVector e) h.baseAt

noncomputable def YPhaseDecodedClockInputs.toClockInputs
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    {e : SelectivePairVectorEncoding start specs}
    (h : YPhaseDecodedClockInputs m k start specs e) :
    YPhaseSelectiveClockInputs m k start specs e h.clock where
  valid := h.valid
  baseAt := h.baseAt
  clock_eq x cut hcut s _ :=
    decodedColumnClock_inverseHoldingPrefix m k e.q yDeletion true
      (pathConditionalSelectiveRunVector e) h.baseAt s x cut hcut

noncomputable def YPhaseDecodedClockInputs.toColumnParser
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    {e : SelectivePairVectorEncoding start specs}
    (h : YPhaseDecodedClockInputs m k start specs e) :
    YPhaseColumnParser m k (selectiveTerminalPathAtom start specs) h.clock :=
  h.toClockInputs.toColumnParser

/-- Independently conditioned backward-column data, again with the clock
decoded rather than assumed. -/
structure YPrimedPhaseDecodedClockInputs
    (m k start : ℕ) (specs : List (Bool × IncrementPair))
    (e : PrimedSelectivePairVectorEncoding start specs) where
  valid : PrimedSelectiveTerminalValid specs
  baseAt : Fin e.q → Site

noncomputable def YPrimedPhaseDecodedClockInputs.clock
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    {e : PrimedSelectivePairVectorEncoding start specs}
    (h : YPrimedPhaseDecodedClockInputs m k start specs e) :
    PrimedShiftedDeletionClock m k :=
  decodedColumnClock m k e.q yDeletion false
    (pathConditionalPrimedSelectiveRunVector e) h.baseAt

noncomputable def YPrimedPhaseDecodedClockInputs.toClockInputs
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    {e : PrimedSelectivePairVectorEncoding start specs}
    (h : YPrimedPhaseDecodedClockInputs m k start specs e) :
    YPrimedPhaseSelectiveClockInputs m k start specs e h.clock where
  valid := h.valid
  baseAt := h.baseAt
  clock_eq x cut hcut s _ :=
    decodedColumnClock_inverseHoldingPrefix m k e.q yDeletion false
      (pathConditionalPrimedSelectiveRunVector e) h.baseAt s x cut hcut

noncomputable def YPrimedPhaseDecodedClockInputs.toColumnParser
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    {e : PrimedSelectivePairVectorEncoding start specs}
    (h : YPrimedPhaseDecodedClockInputs m k start specs e) :
    YPhaseColumnParser m k
      (primedSelectiveTerminalPathAtom start specs) h.clock :=
  h.toClockInputs.toColumnParser

/-! ### Parser inputs determined by a terminal specification

The preceding decoded-clock structures still accepted a vector encoding as
an index.  The canonical constructors in `HLOZColumnPairRuns` show that this
index is determined by the terminal specification and its validity proof.
These wrappers leave only the chronological base attached to each active
entry as deterministic input. -/

/-- Forward column data determined by a valid terminal specification. -/
structure YPhaseTerminalClockInputs
    (m k start : ℕ) (specs : List (Bool × IncrementPair)) where
  valid : SelectiveTerminalValid specs
  baseAt : Fin (selectiveActiveCount specs) → Site

noncomputable def YPhaseTerminalClockInputs.encoding
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs) :
    SelectivePairVectorEncoding start specs :=
  canonicalSelectivePairVectorEncoding start specs h.valid

noncomputable def YPhaseTerminalClockInputs.decoded
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs) :
    YPhaseDecodedClockInputs m k start specs h.encoding where
  valid := h.valid
  baseAt := h.baseAt

noncomputable def YPhaseTerminalClockInputs.toColumnParser
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs) :
    YPhaseColumnParser m k (selectiveTerminalPathAtom start specs)
      h.decoded.clock :=
  h.decoded.toColumnParser

theorem YPhaseTerminalClockInputs.toColumnParser_visitIndices
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs) :
    h.toColumnParser.visitIndices = columnVisitIndices h.baseAt := by
  rfl

/-- Backward/primed column data determined by its own valid terminal
specification.  This is deliberately a distinct object from the forward
phase. -/
structure YPrimedPhaseTerminalClockInputs
    (m k start : ℕ) (specs : List (Bool × IncrementPair)) where
  valid : PrimedSelectiveTerminalValid specs
  baseAt : Fin (canonicalPrimedSelectivePairVectorEncoding
    start specs valid).q → Site

noncomputable def YPrimedPhaseTerminalClockInputs.encoding
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs) :
    PrimedSelectivePairVectorEncoding start specs :=
  canonicalPrimedSelectivePairVectorEncoding start specs h.valid

noncomputable def YPrimedPhaseTerminalClockInputs.decoded
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs) :
    YPrimedPhaseDecodedClockInputs m k start specs h.encoding where
  valid := h.valid
  baseAt := h.baseAt

noncomputable def YPrimedPhaseTerminalClockInputs.toColumnParser
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs) :
    YPhaseColumnParser m k (primedSelectiveTerminalPathAtom start specs)
      h.decoded.clock :=
  h.decoded.toColumnParser

theorem YPrimedPhaseTerminalClockInputs.toColumnParser_visitIndices
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs) :
    h.toColumnParser.visitIndices = columnVisitIndices h.baseAt := by
  rfl

/-! ### Reconstructing the chronological bases from a terminal path

The terminal labels determine all displacements after the beginning of the
cylinder, but they do not determine the absolute position at that beginning.
Once that single initial site is supplied, every active holding-run base is
canonical.  Coordinates in the canonical run vector are ordered with the
first active entry at `Fin.last`, matching `canonicalSelectiveRuns`. -/

/-- Absolute base of every active entry in a selective terminal
specification, reconstructed from its initial site. -/
def selectiveActiveBaseAt :
    (a : Site) → (specs : List (Bool × IncrementPair)) →
      Fin (selectiveActiveCount specs) → Site
  | _, [], i => Fin.elim0 i
  | a, (false, p) :: specs, i =>
      selectiveActiveBaseAt (pairEndpoint a p) specs i
  | a, (true, p) :: specs, i =>
      Fin.lastCases a
        (selectiveActiveBaseAt (pairEndpoint a p) specs) i

/-- The forward terminal mask is exactly the even-column mask computed
along the fixed terminal path. -/
def YForwardTerminalMaskValid :
    Site → List (Bool × IncrementPair) → Prop
  | _, [] => True
  | a, (active, p) :: specs =>
      active = decide (Even a.1) ∧
        YForwardTerminalMaskValid (pairEndpoint a p) specs

/-- The independently conditioned primed mask is exactly the odd-column
mask computed along the same kind of fixed terminal path. -/
def YPrimedTerminalMaskValid :
    Site → List (Bool × IncrementPair) → Prop
  | _, [] => True
  | a, (active, p) :: specs =>
      active = decide (Odd a.1) ∧
        YPrimedTerminalMaskValid (pairEndpoint a p) specs

theorem yForwardTerminalSpec_maskValid (a : Site)
    (labels : List IncrementPair) :
    YForwardTerminalMaskValid a (yForwardTerminalSpec a labels) := by
  induction labels generalizing a with
  | nil => trivial
  | cons p labels ih =>
      exact ⟨rfl, ih (pairEndpoint a p)⟩

theorem yPrimedTerminalSpec_maskValid (a : Site)
    (labels : List IncrementPair) :
    YPrimedTerminalMaskValid a (yPrimedTerminalSpec a labels) := by
  induction labels generalizing a with
  | nil => trivial
  | cons p labels ih =>
      exact ⟨rfl, ih (pairEndpoint a p)⟩

theorem YForwardTerminalMaskValid.eq_terminalSpec
    {a : Site} {specs : List (Bool × IncrementPair)}
    (h : YForwardTerminalMaskValid a specs) :
    yForwardTerminalSpec a (specs.map Prod.snd) = specs := by
  induction specs generalizing a with
  | nil => rfl
  | cons spec specs ih =>
      rcases spec with ⟨active, p⟩
      rw [YForwardTerminalMaskValid] at h
      simp only [List.map_cons, yForwardTerminalSpec]
      rw [← h.1, ih h.2]

theorem YPrimedTerminalMaskValid.eq_terminalSpec
    {a : Site} {specs : List (Bool × IncrementPair)}
    (h : YPrimedTerminalMaskValid a specs) :
    yPrimedTerminalSpec a (specs.map Prod.snd) = specs := by
  induction specs generalizing a with
  | nil => rfl
  | cons spec specs ih =>
      rcases spec with ⟨active, p⟩
      rw [YPrimedTerminalMaskValid] at h
      simp only [List.map_cons, yPrimedTerminalSpec]
      rw [← h.1, ih h.2]

/-- A fixed increment sequence has only one length and terminal label at the
end of a distinguished-pair run.  This is the local uniqueness step for the
adaptive column cylinders. -/
private theorem distinguishedPairRunSegmentWithLabel_eq
    {start t u : ℕ} {p q : IncrementPair} {omega : ℕ → Direction}
    (hp : p ≠ distinguishedIncrementPair)
    (hq : q ≠ distinguishedIncrementPair)
    (ht : omega ∈ distinguishedPairRunSegmentWithLabel start t p)
    (hu : omega ∈ distinguishedPairRunSegmentWithLabel start u q) :
    t = u ∧ p = q := by
  have htu : t = u := by
    rcases lt_trichotomy t u with hlt | heq | hgt
    · have hdist : incrementPair (start + t) omega =
          distinguishedIncrementPair := hu.1 t hlt
      exact False.elim (hp (ht.2.symm.trans hdist))
    · exact heq
    · have hdist : incrementPair (start + u) omega =
          distinguishedIncrementPair := ht.1 u hgt
      exact False.elim (hq (hu.2.symm.trans hdist))
  subst u
  exact ⟨rfl, ht.2.symm.trans hu.2⟩

/-- Equal-depth valid forward terminal cylinders based at the same site are
disjoint unless their literal label lists agree. -/
theorem yForwardTerminalLabels_eq_of_mem
    {a : Site} {start : ℕ} {labels labels' : List IncrementPair}
    {omega : ℕ → Direction}
    (hlen : labels.length = labels'.length)
    (hvalid : SelectiveTerminalValid (yForwardTerminalSpec a labels))
    (hvalid' : SelectiveTerminalValid (yForwardTerminalSpec a labels'))
    (homega : omega ∈ selectiveTerminalLabelsEqFrom start
      (yForwardTerminalSpec a labels))
    (homega' : omega ∈ selectiveTerminalLabelsEqFrom start
      (yForwardTerminalSpec a labels')) :
    labels = labels' := by
  induction labels generalizing a start labels' with
  | nil =>
      exact (List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)).symm
  | cons p labels ih =>
      cases labels' with
      | nil => simp at hlen
      | cons q labels' =>
          have hlenTail : labels.length = labels'.length := by
            simp only [List.length_cons] at hlen
            omega
          by_cases hactive : Even a.1
          · simp only [yForwardTerminalSpec, hactive, decide_true,
              selectiveTerminalLabelsEqFrom] at homega homega'
            rcases Set.mem_iUnion.mp homega with ⟨t, ht, htail⟩
            rcases Set.mem_iUnion.mp homega' with ⟨u, hu, htail'⟩
            have hp : p ≠ distinguishedIncrementPair :=
              hvalid (true, p) (by
                simp [yForwardTerminalSpec, hactive]) rfl
            have hq : q ≠ distinguishedIncrementPair :=
              hvalid' (true, q) (by
                simp [yForwardTerminalSpec, hactive]) rfl
            rcases distinguishedPairRunSegmentWithLabel_eq hp hq ht hu with
              ⟨htu, hpq⟩
            subst u
            subst q
            have hvalidTail : SelectiveTerminalValid
                (yForwardTerminalSpec (pairEndpoint a p) labels) := by
              intro spec hspec hspecActive
              exact hvalid spec (by
                simp only [yForwardTerminalSpec, hactive, decide_true,
                  List.mem_cons]
                exact Or.inr hspec) hspecActive
            have hvalidTail' : SelectiveTerminalValid
                (yForwardTerminalSpec (pairEndpoint a p) labels') := by
              intro spec hspec hspecActive
              exact hvalid' spec (by
                simp only [yForwardTerminalSpec, hactive, decide_true,
                  List.mem_cons]
                exact Or.inr hspec) hspecActive
            rw [ih hlenTail hvalidTail hvalidTail' htail htail']
          · simp only [yForwardTerminalSpec, hactive, decide_false,
              selectiveTerminalLabelsEqFrom] at homega homega'
            have hpq : p = q := homega.1.symm.trans homega'.1
            subst q
            have hvalidTail : SelectiveTerminalValid
                (yForwardTerminalSpec (pairEndpoint a p) labels) := by
              intro spec hspec hspecActive
              exact hvalid spec (by
                simp only [yForwardTerminalSpec, hactive, decide_false,
                  List.mem_cons]
                exact Or.inr hspec) hspecActive
            have hvalidTail' : SelectiveTerminalValid
                (yForwardTerminalSpec (pairEndpoint a p) labels') := by
              intro spec hspec hspecActive
              exact hvalid' spec (by
                simp only [yForwardTerminalSpec, hactive, decide_false,
                  List.mem_cons]
                exact Or.inr hspec) hspecActive
            rw [ih hlenTail hvalidTail hvalidTail' homega.2 homega'.2]

/-- Equal-depth valid primed terminal cylinders based at the same site are
disjoint unless their literal label lists agree. -/
theorem yPrimedTerminalLabels_eq_of_mem
    {a : Site} {start : ℕ} {labels labels' : List IncrementPair}
    {omega : ℕ → Direction}
    (hlen : labels.length = labels'.length)
    (hvalid : PrimedSelectiveTerminalValid (yPrimedTerminalSpec a labels))
    (hvalid' : PrimedSelectiveTerminalValid (yPrimedTerminalSpec a labels'))
    (homega : omega ∈ primedSelectiveTerminalLabelsEqFrom start
      (yPrimedTerminalSpec a labels))
    (homega' : omega ∈ primedSelectiveTerminalLabelsEqFrom start
      (yPrimedTerminalSpec a labels')) :
    labels = labels' := by
  induction labels generalizing a start labels' with
  | nil =>
      exact (List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)).symm
  | cons p labels ih =>
      cases labels' with
      | nil => simp at hlen
      | cons q labels' =>
          have hlenTail : labels.length = labels'.length := by
            simp only [List.length_cons] at hlen
            omega
          change swapAdjacentPairs omega ∈ selectiveTerminalLabelsEqFrom start
            ((yPrimedTerminalSpec a (p :: labels)).map
              reverseSelectiveTerminalLabel) at homega
          change swapAdjacentPairs omega ∈ selectiveTerminalLabelsEqFrom start
            ((yPrimedTerminalSpec a (q :: labels')).map
              reverseSelectiveTerminalLabel) at homega'
          by_cases hactive : Odd a.1
          · simp only [yPrimedTerminalSpec, List.map_cons,
              reverseSelectiveTerminalLabel, hactive, decide_true,
              selectiveTerminalLabelsEqFrom] at homega homega'
            rcases Set.mem_iUnion.mp homega with ⟨t, ht, htail⟩
            rcases Set.mem_iUnion.mp homega' with ⟨u, hu, htail'⟩
            have hp : reverseIncrementPair p ≠ distinguishedIncrementPair :=
              (reverse_specs_valid hvalid) (true, reverseIncrementPair p) (by
                simp [yPrimedTerminalSpec, hactive,
                  reverseSelectiveTerminalLabel]) rfl
            have hq : reverseIncrementPair q ≠ distinguishedIncrementPair :=
              (reverse_specs_valid hvalid') (true, reverseIncrementPair q) (by
                simp [yPrimedTerminalSpec, hactive,
                  reverseSelectiveTerminalLabel]) rfl
            rcases distinguishedPairRunSegmentWithLabel_eq hp hq ht hu with
              ⟨htu, hpqReverse⟩
            have hpq : p = q := by
              have := congrArg reverseIncrementPair hpqReverse
              simpa only [reverseIncrementPair_reverseIncrementPair] using this
            subst u
            subst q
            have hvalidTail : PrimedSelectiveTerminalValid
                (yPrimedTerminalSpec (pairEndpoint a p) labels) := by
              intro spec hspec hspecActive
              exact hvalid spec (by
                simp only [yPrimedTerminalSpec, hactive, decide_true,
                  List.mem_cons]
                exact Or.inr hspec) hspecActive
            have hvalidTail' : PrimedSelectiveTerminalValid
                (yPrimedTerminalSpec (pairEndpoint a p) labels') := by
              intro spec hspec hspecActive
              exact hvalid' spec (by
                simp only [yPrimedTerminalSpec, hactive, decide_true,
                  List.mem_cons]
                exact Or.inr hspec) hspecActive
            apply congrArg (List.cons p)
            exact ih hlenTail hvalidTail hvalidTail' htail htail'
          · simp only [yPrimedTerminalSpec, List.map_cons,
              reverseSelectiveTerminalLabel, hactive, decide_false,
              selectiveTerminalLabelsEqFrom] at homega homega'
            have hpqReverse : reverseIncrementPair p = reverseIncrementPair q :=
              homega.1.symm.trans homega'.1
            have hpq : p = q := by
              have := congrArg reverseIncrementPair hpqReverse
              simpa only [reverseIncrementPair_reverseIncrementPair] using this
            subst q
            have hvalidTail : PrimedSelectiveTerminalValid
                (yPrimedTerminalSpec (pairEndpoint a p) labels) := by
              intro spec hspec hspecActive
              exact hvalid spec (by
                simp only [yPrimedTerminalSpec, hactive, decide_false,
                  List.mem_cons]
                exact Or.inr hspec) hspecActive
            have hvalidTail' : PrimedSelectiveTerminalValid
                (yPrimedTerminalSpec (pairEndpoint a p) labels') := by
              intro spec hspec hspecActive
              exact hvalid' spec (by
                simp only [yPrimedTerminalSpec, hactive, decide_false,
                  List.mem_cons]
                exact Or.inr hspec) hspecActive
            apply congrArg (List.cons p)
            exact ih hlenTail hvalidTail hvalidTail' homega.2 homega'.2

theorem disjoint_yForwardTerminalPathAtom_of_ne
    {a : Site} {start : ℕ} {labels labels' : List IncrementPair}
    (hlen : labels.length = labels'.length)
    (hvalid : SelectiveTerminalValid (yForwardTerminalSpec a labels))
    (hvalid' : SelectiveTerminalValid (yForwardTerminalSpec a labels'))
    (hne : labels ≠ labels') :
    Disjoint
      (selectiveTerminalPathAtom start (yForwardTerminalSpec a labels))
      (selectiveTerminalPathAtom start (yForwardTerminalSpec a labels')) := by
  rw [Set.disjoint_left]
  intro s hs hs'
  rcases hs with ⟨omega, homega, rfl⟩
  rcases hs' with ⟨omega', homega', hpath⟩
  have heq : omega' = omega := simpleRandomWalk_injective hpath
  subst omega'
  exact hne (yForwardTerminalLabels_eq_of_mem hlen hvalid hvalid'
    homega homega')

theorem disjoint_yPrimedTerminalPathAtom_of_ne
    {a : Site} {start : ℕ} {labels labels' : List IncrementPair}
    (hlen : labels.length = labels'.length)
    (hvalid : PrimedSelectiveTerminalValid (yPrimedTerminalSpec a labels))
    (hvalid' : PrimedSelectiveTerminalValid (yPrimedTerminalSpec a labels'))
    (hne : labels ≠ labels') :
    Disjoint
      (primedSelectiveTerminalPathAtom start (yPrimedTerminalSpec a labels))
      (primedSelectiveTerminalPathAtom start
        (yPrimedTerminalSpec a labels')) := by
  rw [Set.disjoint_left]
  intro s hs hs'
  rcases hs with ⟨omega, homega, rfl⟩
  rcases hs' with ⟨omega', homega', hpath⟩
  have heq : omega' = omega := simpleRandomWalk_injective hpath
  subst omega'
  exact hne (yPrimedTerminalLabels_eq_of_mem hlen hvalid hvalid'
    homega homega')

/-! ### Fixed-depth terminal-parser completeness

The local terminal parser has no probabilistic loss.  At an active column
there are exactly fifteen admissible terminal pairs, each with mass `1/15`;
at an inactive column there are all sixteen pairs, each with mass `1/16`.
The endpoint-dependent active mask does not change this normalization.
The next lemmas record that calculation before any Proposition-4.4 or
stopped-clock exceptional event is imposed. -/

private theorem terminalLabelTupleSum_succ {A R : Type*} [Fintype A]
    [AddCommMonoid R] (n : ℕ) (F : (Fin (n + 1) → A) → R) :
    ∑ w, F w = ∑ a : A, ∑ u : Fin n → A, F (Fin.cons a u) := by
  let e := Fin.consEquiv (fun _ : Fin (n + 1) ↦ A)
  calc
    ∑ w, F w = ∑ z : A × (Fin n → A), F (e z) :=
      (Equiv.sum_comp e F).symm
    _ = ∑ a : A, ∑ u : Fin n → A, F (Fin.cons a u) := by
      rw [Fintype.sum_prod_type]
      rfl

private theorem terminalActiveFactor_sum (forbidden : IncrementPair) :
    (∑ p : IncrementPair,
      if p = forbidden then (0 : ℝ≥0∞) else (15 : ℝ≥0∞)⁻¹) = 1 := by
  classical
  rw [Finset.sum_ite]
  simp only [Finset.filter_eq', Finset.sum_const]
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp only [Finset.card_univ]
  rw [show Fintype.card IncrementPair = 16 by simp [IncrementPair]]
  norm_num [nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

private theorem terminalInactiveFactor_sum :
    (∑ _p : IncrementPair, (16 : ℝ≥0∞)⁻¹) = 1 := by
  rw [Finset.sum_const, Finset.card_univ]
  rw [show Fintype.card IncrementPair = 16 by simp [IncrementPair]]
  norm_num [nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

theorem yForwardTerminalValid_cons_iff (a : Site) (p : IncrementPair)
    (labels : List IncrementPair) :
    SelectiveTerminalValid (yForwardTerminalSpec a (p :: labels)) ↔
      (Even a.1 → p ≠ distinguishedIncrementPair) ∧
        SelectiveTerminalValid
          (yForwardTerminalSpec (pairEndpoint a p) labels) := by
  simp only [yForwardTerminalSpec]
  constructor
  · intro h
    constructor
    · intro heven
      exact h (decide (Even a.1), p) (by simp) (by simpa using heven)
    · intro spec hspec hactive
      exact h spec (by simp [hspec]) hactive
  · rintro ⟨hp, htail⟩ spec hspec hactive
    simp only [List.mem_cons] at hspec
    rcases hspec with rfl | hspec
    · exact hp (by simpa using hactive)
    · exact htail spec hspec hactive

/-- Total mass assigned to one forward label vector, with invalid terminal
vectors assigned mass zero. -/
noncomputable def yForwardTerminalLabelMass (a : Site) {q : ℕ}
    (labels : Fin q → IncrementPair) : ℝ≥0∞ := by
  classical
  exact if SelectiveTerminalValid
      (yForwardTerminalSpec a (List.ofFn labels)) then
    ((yForwardTerminalSpec a (List.ofFn labels)).map
      selectiveTerminalFactor).prod
  else 0

private theorem yForwardTerminalLabelMass_cons_even
    (a : Site) (p : IncrementPair) {q : ℕ}
    (labels : Fin q → IncrementPair) (ha : Even a.1) :
    yForwardTerminalLabelMass a (Fin.cons p labels) =
      if p = distinguishedIncrementPair then 0
      else (15 : ℝ≥0∞)⁻¹ *
        yForwardTerminalLabelMass (pairEndpoint a p) labels := by
  classical
  simp only [yForwardTerminalLabelMass, List.ofFn_cons]
  rw [yForwardTerminalValid_cons_iff]
  simp only [ha, true_implies, yForwardTerminalSpec, decide_true,
    selectiveTerminalFactor, List.map_cons, List.prod_cons]
  by_cases hp : p = distinguishedIncrementPair
  · simp [hp]
  · simp [hp]

private theorem yForwardTerminalLabelMass_cons_not_even
    (a : Site) (p : IncrementPair) {q : ℕ}
    (labels : Fin q → IncrementPair) (ha : ¬ Even a.1) :
    yForwardTerminalLabelMass a (Fin.cons p labels) =
      (16 : ℝ≥0∞)⁻¹ *
        yForwardTerminalLabelMass (pairEndpoint a p) labels := by
  classical
  simp only [yForwardTerminalLabelMass, List.ofFn_cons]
  rw [yForwardTerminalValid_cons_iff]
  simp only [ha, false_implies, true_and, yForwardTerminalSpec, decide_false,
    selectiveTerminalFactor, List.map_cons, List.prod_cons]
  by_cases hvalid : SelectiveTerminalValid
      (yForwardTerminalSpec (pairEndpoint a p) (List.ofFn labels))
  · simp [hvalid]
  · simp [hvalid]

theorem yForwardTerminalLabelMass_sum (a : Site) (q : ℕ) :
    ∑ labels : Fin q → IncrementPair,
      yForwardTerminalLabelMass a labels = 1 := by
  induction q generalizing a with
  | zero =>
      classical
      simp [yForwardTerminalLabelMass, SelectiveTerminalValid,
        yForwardTerminalSpec]
  | succ q ih =>
      rw [terminalLabelTupleSum_succ]
      by_cases ha : Even a.1
      · simp_rw [yForwardTerminalLabelMass_cons_even a _ _ ha]
        calc
          (∑ p : IncrementPair, ∑ labels : Fin q → IncrementPair,
              if p = distinguishedIncrementPair then 0
              else (15 : ℝ≥0∞)⁻¹ *
                yForwardTerminalLabelMass (pairEndpoint a p) labels) =
              ∑ p : IncrementPair,
                if p = distinguishedIncrementPair then 0
                else (15 : ℝ≥0∞)⁻¹ *
                  ∑ labels : Fin q → IncrementPair,
                    yForwardTerminalLabelMass (pairEndpoint a p) labels := by
            apply Finset.sum_congr rfl
            intro p _
            by_cases hp : p = distinguishedIncrementPair
            · simp [hp]
            · simp only [hp, if_false, Finset.mul_sum]
          _ = ∑ p : IncrementPair,
                if p = distinguishedIncrementPair then 0
                else (15 : ℝ≥0∞)⁻¹ := by
            apply Finset.sum_congr rfl
            intro p _
            rw [ih]
            simp
          _ = 1 := terminalActiveFactor_sum distinguishedIncrementPair
      · simp_rw [yForwardTerminalLabelMass_cons_not_even a _ _ ha]
        calc
          (∑ p : IncrementPair, ∑ labels : Fin q → IncrementPair,
              (16 : ℝ≥0∞)⁻¹ *
                yForwardTerminalLabelMass (pairEndpoint a p) labels) =
              ∑ p : IncrementPair, (16 : ℝ≥0∞)⁻¹ *
                ∑ labels : Fin q → IncrementPair,
                  yForwardTerminalLabelMass (pairEndpoint a p) labels := by
            apply Finset.sum_congr rfl
            intro p _
            rw [Finset.mul_sum]
          _ = ∑ _p : IncrementPair, (16 : ℝ≥0∞)⁻¹ := by
            apply Finset.sum_congr rfl
            intro p _
            rw [ih, mul_one]
          _ = 1 := terminalInactiveFactor_sum

theorem simpleRandomWalkLaw_yForwardTerminalPathAtom
    (a : Site) (start : ℕ) (labels : List IncrementPair)
    (hvalid : SelectiveTerminalValid (yForwardTerminalSpec a labels)) :
    simpleRandomWalkLaw
        (selectiveTerminalPathAtom start (yForwardTerminalSpec a labels)) =
      ((yForwardTerminalSpec a labels).map
        selectiveTerminalFactor).prod := by
  rw [simpleRandomWalkLaw]
  have hmeas : MeasurableSet
      (selectiveTerminalPathAtom start (yForwardTerminalSpec a labels)) :=
    measurableSet_selectiveTerminalPathAtom _ _
  rw [Measure.map_apply measurable_simpleRandomWalk hmeas]
  change incrementLaw
      (simpleRandomWalk ⁻¹' (simpleRandomWalk ''
        selectiveTerminalLabelsEqFrom start
          (yForwardTerminalSpec a labels))) = _
  rw [Set.preimage_image_eq _ simpleRandomWalk_injective]
  exact selectiveTerminalLabelsEqFrom_prob _ _ hvalid

/-- The union of every valid forward terminal cylinder at one fixed depth. -/
noncomputable def yForwardValidTerminalPathUnion
    (a : Site) (start q : ℕ) : Set Path := by
  classical
  exact ⋃ labels : Fin q → IncrementPair,
    if SelectiveTerminalValid
        (yForwardTerminalSpec a (List.ofFn labels)) then
      selectiveTerminalPathAtom start
        (yForwardTerminalSpec a (List.ofFn labels))
    else ∅

theorem simpleRandomWalkLaw_yForwardValidTerminalPathUnion
    (a : Site) (start q : ℕ) :
    simpleRandomWalkLaw (yForwardValidTerminalPathUnion a start q) = 1 := by
  classical
  unfold yForwardValidTerminalPathUnion
  rw [measure_iUnion]
  · rw [tsum_fintype]
    calc
      (∑ labels : Fin q → IncrementPair,
          simpleRandomWalkLaw
            (if SelectiveTerminalValid
                (yForwardTerminalSpec a (List.ofFn labels)) then
              selectiveTerminalPathAtom start
                (yForwardTerminalSpec a (List.ofFn labels))
            else ∅)) =
          ∑ labels : Fin q → IncrementPair,
            yForwardTerminalLabelMass a labels := by
        apply Finset.sum_congr rfl
        intro labels _
        by_cases hvalid : SelectiveTerminalValid
            (yForwardTerminalSpec a (List.ofFn labels))
        · simp only [hvalid, if_true, yForwardTerminalLabelMass]
          exact simpleRandomWalkLaw_yForwardTerminalPathAtom
            a start (List.ofFn labels) hvalid
        · simp [hvalid, yForwardTerminalLabelMass]
      _ = 1 := yForwardTerminalLabelMass_sum a q
  · intro labels labels' hne
    change Disjoint
      (if SelectiveTerminalValid
          (yForwardTerminalSpec a (List.ofFn labels)) then
        selectiveTerminalPathAtom start
          (yForwardTerminalSpec a (List.ofFn labels))
      else ∅)
      (if SelectiveTerminalValid
          (yForwardTerminalSpec a (List.ofFn labels')) then
        selectiveTerminalPathAtom start
          (yForwardTerminalSpec a (List.ofFn labels'))
      else ∅)
    by_cases hvalid : SelectiveTerminalValid
        (yForwardTerminalSpec a (List.ofFn labels))
    · by_cases hvalid' : SelectiveTerminalValid
          (yForwardTerminalSpec a (List.ofFn labels'))
      · simp only [hvalid, hvalid', if_true]
        apply disjoint_yForwardTerminalPathAtom_of_ne
        · simp
        · exact hvalid
        · exact hvalid'
        · exact fun heq ↦ hne (List.ofFn_injective heq)
      · simp [hvalid']
    · simp [hvalid]
  · intro labels
    change MeasurableSet
      (if SelectiveTerminalValid
          (yForwardTerminalSpec a (List.ofFn labels)) then
        selectiveTerminalPathAtom start
          (yForwardTerminalSpec a (List.ofFn labels))
      else ∅)
    by_cases hvalid : SelectiveTerminalValid
        (yForwardTerminalSpec a (List.ofFn labels))
    · simpa [hvalid] using measurableSet_selectiveTerminalPathAtom start
          (yForwardTerminalSpec a (List.ofFn labels))
    · simp [hvalid]

theorem measurableSet_yForwardValidTerminalPathUnion
    (a : Site) (start q : ℕ) :
    MeasurableSet (yForwardValidTerminalPathUnion a start q) := by
  classical
  unfold yForwardValidTerminalPathUnion
  apply MeasurableSet.iUnion
  intro labels
  by_cases hvalid : SelectiveTerminalValid
      (yForwardTerminalSpec a (List.ofFn labels))
  · simpa [hvalid] using measurableSet_selectiveTerminalPathAtom start
      (yForwardTerminalSpec a (List.ofFn labels))
  · simp [hvalid]

theorem simpleRandomWalkLaw_yForwardValidTerminalPathUnion_compl
    (a : Site) (start q : ℕ) :
    simpleRandomWalkLaw (yForwardValidTerminalPathUnion a start q)ᶜ = 0 := by
  rw [measure_compl (measurableSet_yForwardValidTerminalPathUnion a start q)
      (measure_ne_top _ _),
    simpleRandomWalkLaw_yForwardValidTerminalPathUnion, measure_univ]
  simp

theorem yPrimedTerminalValid_cons_iff (a : Site) (p : IncrementPair)
    (labels : List IncrementPair) :
    PrimedSelectiveTerminalValid (yPrimedTerminalSpec a (p :: labels)) ↔
      (Odd a.1 → p ≠ primedDistinguishedIncrementPair) ∧
        PrimedSelectiveTerminalValid
          (yPrimedTerminalSpec (pairEndpoint a p) labels) := by
  simp only [yPrimedTerminalSpec]
  constructor
  · intro h
    constructor
    · intro hodd
      simpa using h (decide (Odd a.1), p) (by simp)
        (by simpa using hodd)
    · intro spec hspec hactive
      exact h spec (by simp [hspec]) hactive
  · rintro ⟨hp, htail⟩ spec hspec hactive
    simp only [List.mem_cons] at hspec
    rcases hspec with rfl | hspec
    · simpa using hp (by simpa using hactive)
    · exact htail spec hspec hactive

/-- Total mass assigned to one primed label vector, with invalid terminal
vectors assigned mass zero. -/
noncomputable def yPrimedTerminalLabelMass (a : Site) {q : ℕ}
    (labels : Fin q → IncrementPair) : ℝ≥0∞ := by
  classical
  exact if PrimedSelectiveTerminalValid
      (yPrimedTerminalSpec a (List.ofFn labels)) then
    ((yPrimedTerminalSpec a (List.ofFn labels)).map
      selectiveTerminalFactor).prod
  else 0

private theorem yPrimedTerminalLabelMass_cons_odd
    (a : Site) (p : IncrementPair) {q : ℕ}
    (labels : Fin q → IncrementPair) (ha : Odd a.1) :
    yPrimedTerminalLabelMass a (Fin.cons p labels) =
      if p = primedDistinguishedIncrementPair then 0
      else (15 : ℝ≥0∞)⁻¹ *
        yPrimedTerminalLabelMass (pairEndpoint a p) labels := by
  classical
  simp only [yPrimedTerminalLabelMass, List.ofFn_cons]
  rw [yPrimedTerminalValid_cons_iff]
  simp only [ha, true_implies, yPrimedTerminalSpec, decide_true,
    selectiveTerminalFactor, List.map_cons, List.prod_cons]
  by_cases hp : p = primedDistinguishedIncrementPair
  · simp [hp]
  · simp [hp]

private theorem yPrimedTerminalLabelMass_cons_not_odd
    (a : Site) (p : IncrementPair) {q : ℕ}
    (labels : Fin q → IncrementPair) (ha : ¬ Odd a.1) :
    yPrimedTerminalLabelMass a (Fin.cons p labels) =
      (16 : ℝ≥0∞)⁻¹ *
        yPrimedTerminalLabelMass (pairEndpoint a p) labels := by
  classical
  simp only [yPrimedTerminalLabelMass, List.ofFn_cons]
  rw [yPrimedTerminalValid_cons_iff]
  simp only [ha, false_implies, true_and, yPrimedTerminalSpec, decide_false,
    selectiveTerminalFactor, List.map_cons, List.prod_cons]
  by_cases hvalid : PrimedSelectiveTerminalValid
      (yPrimedTerminalSpec (pairEndpoint a p) (List.ofFn labels))
  · simp [hvalid]
  · simp [hvalid]

theorem yPrimedTerminalLabelMass_sum (a : Site) (q : ℕ) :
    ∑ labels : Fin q → IncrementPair,
      yPrimedTerminalLabelMass a labels = 1 := by
  induction q generalizing a with
  | zero =>
      classical
      simp [yPrimedTerminalLabelMass, PrimedSelectiveTerminalValid,
        yPrimedTerminalSpec]
  | succ q ih =>
      rw [terminalLabelTupleSum_succ]
      by_cases ha : Odd a.1
      · simp_rw [yPrimedTerminalLabelMass_cons_odd a _ _ ha]
        calc
          (∑ p : IncrementPair, ∑ labels : Fin q → IncrementPair,
              if p = primedDistinguishedIncrementPair then 0
              else (15 : ℝ≥0∞)⁻¹ *
                yPrimedTerminalLabelMass (pairEndpoint a p) labels) =
              ∑ p : IncrementPair,
                if p = primedDistinguishedIncrementPair then 0
                else (15 : ℝ≥0∞)⁻¹ *
                  ∑ labels : Fin q → IncrementPair,
                    yPrimedTerminalLabelMass (pairEndpoint a p) labels := by
            apply Finset.sum_congr rfl
            intro p _
            by_cases hp : p = primedDistinguishedIncrementPair
            · simp [hp]
            · simp only [hp, if_false, Finset.mul_sum]
          _ = ∑ p : IncrementPair,
                if p = primedDistinguishedIncrementPair then 0
                else (15 : ℝ≥0∞)⁻¹ := by
            apply Finset.sum_congr rfl
            intro p _
            rw [ih]
            simp
          _ = 1 := terminalActiveFactor_sum primedDistinguishedIncrementPair
      · simp_rw [yPrimedTerminalLabelMass_cons_not_odd a _ _ ha]
        calc
          (∑ p : IncrementPair, ∑ labels : Fin q → IncrementPair,
              (16 : ℝ≥0∞)⁻¹ *
                yPrimedTerminalLabelMass (pairEndpoint a p) labels) =
              ∑ p : IncrementPair, (16 : ℝ≥0∞)⁻¹ *
                ∑ labels : Fin q → IncrementPair,
                  yPrimedTerminalLabelMass (pairEndpoint a p) labels := by
            apply Finset.sum_congr rfl
            intro p _
            rw [Finset.mul_sum]
          _ = ∑ _p : IncrementPair, (16 : ℝ≥0∞)⁻¹ := by
            apply Finset.sum_congr rfl
            intro p _
            rw [ih, mul_one]
          _ = 1 := terminalInactiveFactor_sum

private theorem terminalFactor_map_reverse
    (specs : List (Bool × IncrementPair)) :
    ((specs.map reverseSelectiveTerminalLabel).map
        selectiveTerminalFactor).prod =
      (specs.map selectiveTerminalFactor).prod := by
  induction specs with
  | nil => rfl
  | cons spec specs ih =>
      rcases spec with ⟨active, p⟩
      cases active with
      | false =>
          simp only [List.map_cons, reverseSelectiveTerminalLabel,
            selectiveTerminalFactor, List.prod_cons]
          rw [ih]
      | true =>
          simp only [List.map_cons, reverseSelectiveTerminalLabel,
            selectiveTerminalFactor, List.prod_cons]
          rw [ih]

theorem simpleRandomWalkLaw_yPrimedTerminalPathAtom
    (a : Site) (start : ℕ) (labels : List IncrementPair)
    (hvalid : PrimedSelectiveTerminalValid
      (yPrimedTerminalSpec a labels)) :
    simpleRandomWalkLaw
        (primedSelectiveTerminalPathAtom start
          (yPrimedTerminalSpec a labels)) =
      ((yPrimedTerminalSpec a labels).map
        selectiveTerminalFactor).prod := by
  rw [simpleRandomWalkLaw]
  have hsource : MeasurableSet
      (primedSelectiveTerminalLabelsEqFrom start
        (yPrimedTerminalSpec a labels)) :=
    measurableSet_primedSelectiveTerminalLabelsEqFrom _ _
  have hpath : MeasurableSet
      (primedSelectiveTerminalPathAtom start
        (yPrimedTerminalSpec a labels)) :=
    measurableEmbedding_simpleRandomWalk.measurableSet_image.2 hsource
  rw [Measure.map_apply measurable_simpleRandomWalk hpath]
  change incrementLaw
      (simpleRandomWalk ⁻¹' (simpleRandomWalk ''
        primedSelectiveTerminalLabelsEqFrom start
          (yPrimedTerminalSpec a labels))) = _
  rw [Set.preimage_image_eq _ simpleRandomWalk_injective]
  change incrementLaw (swapAdjacentPairs ⁻¹'
      selectiveTerminalLabelsEqFrom start
        ((yPrimedTerminalSpec a labels).map
          reverseSelectiveTerminalLabel)) = _
  rw [← Measure.map_apply measurable_swapAdjacentPairs
    (measurableSet_selectiveTerminalLabelsEqFrom _ _),
    swapAdjacentPairs_hasLaw.map_eq,
    selectiveTerminalLabelsEqFrom_prob _ _ (reverse_specs_valid hvalid),
    terminalFactor_map_reverse]

/-- The union of every valid primed terminal cylinder at one fixed depth. -/
noncomputable def yPrimedValidTerminalPathUnion
    (a : Site) (start q : ℕ) : Set Path := by
  classical
  exact ⋃ labels : Fin q → IncrementPair,
    if PrimedSelectiveTerminalValid
        (yPrimedTerminalSpec a (List.ofFn labels)) then
      primedSelectiveTerminalPathAtom start
        (yPrimedTerminalSpec a (List.ofFn labels))
    else ∅

theorem simpleRandomWalkLaw_yPrimedValidTerminalPathUnion
    (a : Site) (start q : ℕ) :
    simpleRandomWalkLaw (yPrimedValidTerminalPathUnion a start q) = 1 := by
  classical
  unfold yPrimedValidTerminalPathUnion
  rw [measure_iUnion]
  · rw [tsum_fintype]
    calc
      (∑ labels : Fin q → IncrementPair,
          simpleRandomWalkLaw
            (if PrimedSelectiveTerminalValid
                (yPrimedTerminalSpec a (List.ofFn labels)) then
              primedSelectiveTerminalPathAtom start
                (yPrimedTerminalSpec a (List.ofFn labels))
            else ∅)) =
          ∑ labels : Fin q → IncrementPair,
            yPrimedTerminalLabelMass a labels := by
        apply Finset.sum_congr rfl
        intro labels _
        by_cases hvalid : PrimedSelectiveTerminalValid
            (yPrimedTerminalSpec a (List.ofFn labels))
        · simp only [hvalid, if_true, yPrimedTerminalLabelMass]
          exact simpleRandomWalkLaw_yPrimedTerminalPathAtom
            a start (List.ofFn labels) hvalid
        · simp [hvalid, yPrimedTerminalLabelMass]
      _ = 1 := yPrimedTerminalLabelMass_sum a q
  · intro labels labels' hne
    change Disjoint
      (if PrimedSelectiveTerminalValid
          (yPrimedTerminalSpec a (List.ofFn labels)) then
        primedSelectiveTerminalPathAtom start
          (yPrimedTerminalSpec a (List.ofFn labels))
      else ∅)
      (if PrimedSelectiveTerminalValid
          (yPrimedTerminalSpec a (List.ofFn labels')) then
        primedSelectiveTerminalPathAtom start
          (yPrimedTerminalSpec a (List.ofFn labels'))
      else ∅)
    by_cases hvalid : PrimedSelectiveTerminalValid
        (yPrimedTerminalSpec a (List.ofFn labels))
    · by_cases hvalid' : PrimedSelectiveTerminalValid
          (yPrimedTerminalSpec a (List.ofFn labels'))
      · simp only [hvalid, hvalid', if_true]
        apply disjoint_yPrimedTerminalPathAtom_of_ne
        · simp
        · exact hvalid
        · exact hvalid'
        · exact fun heq ↦ hne (List.ofFn_injective heq)
      · simp [hvalid']
    · simp [hvalid]
  · intro labels
    change MeasurableSet
      (if PrimedSelectiveTerminalValid
          (yPrimedTerminalSpec a (List.ofFn labels)) then
        primedSelectiveTerminalPathAtom start
          (yPrimedTerminalSpec a (List.ofFn labels))
      else ∅)
    by_cases hvalid : PrimedSelectiveTerminalValid
        (yPrimedTerminalSpec a (List.ofFn labels))
    · simp only [hvalid, if_true]
      exact measurableEmbedding_simpleRandomWalk.measurableSet_image.2
        (measurableSet_primedSelectiveTerminalLabelsEqFrom _ _)
    · simp [hvalid]

theorem measurableSet_yPrimedValidTerminalPathUnion
    (a : Site) (start q : ℕ) :
    MeasurableSet (yPrimedValidTerminalPathUnion a start q) := by
  classical
  unfold yPrimedValidTerminalPathUnion
  apply MeasurableSet.iUnion
  intro labels
  by_cases hvalid : PrimedSelectiveTerminalValid
      (yPrimedTerminalSpec a (List.ofFn labels))
  · simp only [hvalid, if_true]
    exact measurableEmbedding_simpleRandomWalk.measurableSet_image.2
      (measurableSet_primedSelectiveTerminalLabelsEqFrom _ _)
  · simp [hvalid]

theorem simpleRandomWalkLaw_yPrimedValidTerminalPathUnion_compl
    (a : Site) (start q : ℕ) :
    simpleRandomWalkLaw (yPrimedValidTerminalPathUnion a start q)ᶜ = 0 := by
  rw [measure_compl (measurableSet_yPrimedValidTerminalPathUnion a start q)
      (measure_ne_top _ _),
    simpleRandomWalkLaw_yPrimedValidTerminalPathUnion, measure_univ]
  simp

@[simp] theorem selectiveActiveCount_map_reverseSelectiveTerminalLabel
    (specs : List (Bool × IncrementPair)) :
    selectiveActiveCount (specs.map reverseSelectiveTerminalLabel) =
      selectiveActiveCount specs := by
  induction specs with
  | nil => rfl
  | cons spec specs ih =>
      rcases spec with ⟨active, p⟩
      cases active <;>
        simp [selectiveActiveCount, reverseSelectiveTerminalLabel, ih]

theorem selectiveActiveCount_le_length
    (specs : List (Bool × IncrementPair)) :
    selectiveActiveCount specs ≤ specs.length := by
  induction specs with
  | nil => simp [selectiveActiveCount]
  | cons spec specs ih =>
      rcases spec with ⟨active, p⟩
      cases active <;> simp only [selectiveActiveCount, List.length_cons] <;>
        omega

@[simp] theorem canonicalPrimedSelectivePairVectorEncoding_q
    (start : ℕ) (specs : List (Bool × IncrementPair))
    (hvalid : PrimedSelectiveTerminalValid specs) :
    (canonicalPrimedSelectivePairVectorEncoding start specs hvalid).q =
      selectiveActiveCount specs := by
  simp [canonicalPrimedSelectivePairVectorEncoding,
    canonicalSelectivePairVectorEncoding,
    SelectivePairVectorEncoding.toPrimed]

/-- Source-facing forward clock data.  The arbitrary chronological base map
has disappeared: it is reconstructed from one absolute initial site and the
fixed terminal labels. -/
structure YPhaseInitialTerminalClockInputs
    (m k start : ℕ) (specs : List (Bool × IncrementPair)) where
  initialSite : Site
  valid : SelectiveTerminalValid specs
  mask_valid : YForwardTerminalMaskValid initialSite specs

noncomputable def YPhaseInitialTerminalClockInputs.toTerminalClockInputs
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseInitialTerminalClockInputs m k start specs) :
    YPhaseTerminalClockInputs m k start specs where
  valid := h.valid
  baseAt := selectiveActiveBaseAt h.initialSite specs

def YPhaseInitialTerminalClockInputs.ofLabels
    (m k start : ℕ) (initialSite : Site) (labels : List IncrementPair)
    (hvalid : SelectiveTerminalValid
      (yForwardTerminalSpec initialSite labels)) :
    YPhaseInitialTerminalClockInputs m k start
      (yForwardTerminalSpec initialSite labels) where
  initialSite := initialSite
  valid := hvalid
  mask_valid := yForwardTerminalSpec_maskValid initialSite labels

/-- Source-facing primed clock data with the odd-column mask and the same
canonical reconstruction of absolute active bases. -/
structure YPrimedPhaseInitialTerminalClockInputs
    (m k start : ℕ) (specs : List (Bool × IncrementPair)) where
  initialSite : Site
  valid : PrimedSelectiveTerminalValid specs
  mask_valid : YPrimedTerminalMaskValid initialSite specs

noncomputable def
    YPrimedPhaseInitialTerminalClockInputs.toTerminalClockInputs
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseInitialTerminalClockInputs m k start specs) :
    YPrimedPhaseTerminalClockInputs m k start specs where
  valid := h.valid
  baseAt := fun i ↦ selectiveActiveBaseAt h.initialSite specs
    (Fin.cast (canonicalPrimedSelectivePairVectorEncoding_q
      start specs h.valid) i)

def YPrimedPhaseInitialTerminalClockInputs.ofLabels
    (m k start : ℕ) (initialSite : Site) (labels : List IncrementPair)
    (hvalid : PrimedSelectiveTerminalValid
      (yPrimedTerminalSpec initialSite labels)) :
    YPrimedPhaseInitialTerminalClockInputs m k start
      (yPrimedTerminalSpec initialSite labels) where
  initialSite := initialSite
  valid := hvalid
  mask_valid := yPrimedTerminalSpec_maskValid initialSite labels

/-! ### Canonical finite site/profile data for a terminal column atom -/

/-- The finite set of column bases which actually occur in a terminal
parser.  No caller-selected ambient site set is needed. -/
noncomputable def yPhaseCanonicalSites {q : ℕ}
    (baseAt : Fin q → Site) : Finset Site :=
  Finset.univ.image baseAt

/-- The inverse external profile fixed by a decoded column parser. -/
noncomputable def yPhaseCanonicalProfile {q : ℕ}
    (baseAt : Fin q → Site) (x : Site) : ℕ :=
  (columnVisitIndices baseAt x).length

theorem yPhaseCanonicalSites_card_le {q : ℕ}
    (baseAt : Fin q → Site) :
    (yPhaseCanonicalSites baseAt).card ≤ q := by
  calc
    (yPhaseCanonicalSites baseAt).card ≤
        (Finset.univ : Finset (Fin q)).card := Finset.card_image_le
    _ = q := by simp

/-- Embed the first `cut` chronological visits to `x` into the parser's
joint holding vector. -/
noncomputable def yPhasePrefixEmbedding
    {m k : ℕ} {C : Set Path} {clock : PrimedShiftedDeletionClock m k}
    (p : YPhaseColumnParser m k C clock) (x : Site) (cut : ℕ)
    (hcut : cut ≤ (p.visitIndices x).length) : Fin cut → Fin p.q :=
  fun i ↦ (p.visitIndices x).get (Fin.castLE hcut i)

theorem yPhasePrefixEmbedding_injective
    {m k : ℕ} {C : Set Path} {clock : PrimedShiftedDeletionClock m k}
    (p : YPhaseColumnParser m k C clock) (x : Site) (cut : ℕ)
    (hcut : cut ≤ (p.visitIndices x).length) :
    Function.Injective (yPhasePrefixEmbedding p x cut hcut) := by
  intro i j hij
  have hindices := (p.visitIndices_nodup x).get_inj_iff.mp hij
  exact (Fin.castLE_injective hcut) hindices

/-- Every chronological fixed-site prefix decoded by the column parser has
the negative-binomial law.  This is the reusable probability calculation:
it follows from the one joint vector law and injectivity of the chronological
coordinate list. -/
theorem YPhaseColumnParser.holdingPrefix_hasLaw
    {m k : ℕ} {C : Set Path} {clock : PrimedShiftedDeletionClock m k}
    (p : YPhaseColumnParser m k C clock) (x : Site) (cut : ℕ)
    (hcut : cut ≤ (p.visitIndices x).length) :
    HasLaw (fun s ↦ clock.inverseHoldingPrefix s cut x)
      (negBinMeasure cut) simpleRandomWalkLaw[|C] := by
  have hsum : HasLaw
      (fun v : Fin p.q → ℕ ↦
        ∑ i : Fin cut, v (yPhasePrefixEmbedding p x cut hcut i))
      (negBinMeasure cut) (runVectorMeasure p.q) :=
    runSubvectorSum_hasLaw (yPhasePrefixEmbedding p x cut hcut)
      (yPhasePrefixEmbedding_injective p x cut hcut)
  have hdecoded := hsum.fun_comp p.holdingVector_law
  apply hdecoded.congr
  filter_upwards [ae_cond_mem p.measurable_atom] with s hs
  simpa only [Function.comp_apply, yPhasePrefixEmbedding] using
    p.prefix_eq x cut hcut s hs

/-- One fixed atom of one column phase.  Unlike the `X₁` structures, this
does not smuggle in the paper's time-parity inverse clock: `clock` is the
column phase's own deleted/holding-time clock.  Its scalar laws are derived
from one phase-specific column parser; the two phases still use different
conditioning atoms and different parser values. -/
structure YPhaseExternalAtomInputs
    (m k : ℕ) (theta C H : Set Path) where
  clock : PrimedShiftedDeletionClock m k
  parser : YPhaseColumnParser m k C clock
  sites : Finset Site
  profile : Site → ℕ
  profile_atom : C ⊆ primedInverseProfileAtom clock sites profile
  minus_capacity : ∀ x ∈ sites,
    intervalDotIndex m (sourceBandLowerNat m) profile x ≤
      (parser.visitIndices x).length
  plus_capacity : ∀ x ∈ intervalPlusCandidates sites m m profile,
    intervalHighCut m m ≤ (parser.visitIndices x).length
  theta_subset : C ∩ H ∩ theta ⊆ C ∩ H ∩
    (primedIntervalStoppedThetaMinusEvent clock sites (sourceBandLowerNat m) ∪
      primedIntervalStoppedThetaPlusEvent clock sites m)
  minus_compatible : C ∩ H ∩
      primedIntervalStoppedThetaMinusEvent clock sites (sourceBandLowerNat m) ⊆
    primedMinusPrefixCompatibleEvent clock sites
      (sourceBandLowerNat m) profile
  plus_compatible : C ∩ H ∩
      primedIntervalStoppedThetaPlusEvent clock sites m ⊆
    primedPriorPlusInitialPrefixCompatibleEvent clock sites m
  prop44_card : ((sourceProp44Candidates sites m profile).card : ℝ) ≤
    Real.exp (16 * sourceRate m)
  horizon_card : (sites.card : ℝ) ≤
    Real.exp (16 * Real.sqrt (m : ℝ))

/-! ### Source-facing fixed terminal atoms

For actual column atoms the conditioning set is a terminal-label cylinder,
the encoding is canonical, and the clock is the decoded clock above.  These
two phase-specific structures expose only the remaining deterministic
profile, compatibility, and cardinality statements. -/

/-- One forward fixed-terminal atom, with its parser and joint geometric law
constructed rather than assumed. -/
structure YPhaseTerminalExternalAtomInputs
    (m k start : ℕ) (specs : List (Bool × IncrementPair))
    (theta H : Set Path) where
  clockData : YPhaseTerminalClockInputs m k start specs
  sites : Finset Site
  profile : Site → ℕ
  profile_atom : selectiveTerminalPathAtom start specs ⊆
    primedInverseProfileAtom clockData.decoded.clock sites profile
  minus_capacity : ∀ x ∈ sites,
    intervalDotIndex m (sourceBandLowerNat m) profile x ≤
      (columnVisitIndices clockData.baseAt x).length
  plus_capacity : ∀ x ∈ intervalPlusCandidates sites m m profile,
    intervalHighCut m m ≤ (columnVisitIndices clockData.baseAt x).length
  theta_subset : selectiveTerminalPathAtom start specs ∩ H ∩ theta ⊆
    selectiveTerminalPathAtom start specs ∩ H ∩
      (primedIntervalStoppedThetaMinusEvent clockData.decoded.clock sites
          (sourceBandLowerNat m) ∪
        primedIntervalStoppedThetaPlusEvent clockData.decoded.clock sites m)
  minus_compatible : selectiveTerminalPathAtom start specs ∩ H ∩
      primedIntervalStoppedThetaMinusEvent clockData.decoded.clock sites
        (sourceBandLowerNat m) ⊆
    primedMinusPrefixCompatibleEvent clockData.decoded.clock sites
      (sourceBandLowerNat m) profile
  plus_compatible : selectiveTerminalPathAtom start specs ∩ H ∩
      primedIntervalStoppedThetaPlusEvent clockData.decoded.clock sites m ⊆
    primedPriorPlusInitialPrefixCompatibleEvent
      clockData.decoded.clock sites m
  prop44_card : ((sourceProp44Candidates sites m profile).card : ℝ) ≤
    Real.exp (16 * sourceRate m)
  horizon_card : (sites.card : ℝ) ≤
    Real.exp (16 * Real.sqrt (m : ℝ))

noncomputable def YPhaseTerminalExternalAtomInputs.toExternalAtomInputs
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    {theta H : Set Path}
    (h : YPhaseTerminalExternalAtomInputs m k start specs theta H) :
    YPhaseExternalAtomInputs m k theta
      (selectiveTerminalPathAtom start specs) H where
  clock := h.clockData.decoded.clock
  parser := h.clockData.toColumnParser
  sites := h.sites
  profile := h.profile
  profile_atom := h.profile_atom
  minus_capacity := by
    intro x hx
    rw [h.clockData.toColumnParser_visitIndices]
    exact h.minus_capacity x hx
  plus_capacity := by
    intro x hx
    rw [h.clockData.toColumnParser_visitIndices]
    exact h.plus_capacity x hx
  theta_subset := h.theta_subset
  minus_compatible := h.minus_compatible
  plus_compatible := h.plus_compatible
  prop44_card := h.prop44_card
  horizon_card := h.horizon_card

/-- One independently conditioned backward/primed terminal atom. -/
structure YPrimedPhaseTerminalExternalAtomInputs
    (m k start : ℕ) (specs : List (Bool × IncrementPair))
    (theta H : Set Path) where
  clockData : YPrimedPhaseTerminalClockInputs m k start specs
  sites : Finset Site
  profile : Site → ℕ
  profile_atom : primedSelectiveTerminalPathAtom start specs ⊆
    primedInverseProfileAtom clockData.decoded.clock sites profile
  minus_capacity : ∀ x ∈ sites,
    intervalDotIndex m (sourceBandLowerNat m) profile x ≤
      (columnVisitIndices clockData.baseAt x).length
  plus_capacity : ∀ x ∈ intervalPlusCandidates sites m m profile,
    intervalHighCut m m ≤ (columnVisitIndices clockData.baseAt x).length
  theta_subset : primedSelectiveTerminalPathAtom start specs ∩ H ∩ theta ⊆
    primedSelectiveTerminalPathAtom start specs ∩ H ∩
      (primedIntervalStoppedThetaMinusEvent clockData.decoded.clock sites
          (sourceBandLowerNat m) ∪
        primedIntervalStoppedThetaPlusEvent clockData.decoded.clock sites m)
  minus_compatible : primedSelectiveTerminalPathAtom start specs ∩ H ∩
      primedIntervalStoppedThetaMinusEvent clockData.decoded.clock sites
        (sourceBandLowerNat m) ⊆
    primedMinusPrefixCompatibleEvent clockData.decoded.clock sites
      (sourceBandLowerNat m) profile
  plus_compatible : primedSelectiveTerminalPathAtom start specs ∩ H ∩
      primedIntervalStoppedThetaPlusEvent clockData.decoded.clock sites m ⊆
    primedPriorPlusInitialPrefixCompatibleEvent
      clockData.decoded.clock sites m
  prop44_card : ((sourceProp44Candidates sites m profile).card : ℝ) ≤
    Real.exp (16 * sourceRate m)
  horizon_card : (sites.card : ℝ) ≤
    Real.exp (16 * Real.sqrt (m : ℝ))

noncomputable def YPrimedPhaseTerminalExternalAtomInputs.toExternalAtomInputs
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    {theta H : Set Path}
    (h : YPrimedPhaseTerminalExternalAtomInputs m k start specs theta H) :
    YPhaseExternalAtomInputs m k theta
      (primedSelectiveTerminalPathAtom start specs) H where
  clock := h.clockData.decoded.clock
  parser := h.clockData.toColumnParser
  sites := h.sites
  profile := h.profile
  profile_atom := h.profile_atom
  minus_capacity := by
    intro x hx
    rw [h.clockData.toColumnParser_visitIndices]
    exact h.minus_capacity x hx
  plus_capacity := by
    intro x hx
    rw [h.clockData.toColumnParser_visitIndices]
    exact h.plus_capacity x hx
  theta_subset := h.theta_subset
  minus_compatible := h.minus_compatible
  plus_compatible := h.plus_compatible
  prop44_card := h.prop44_card
  horizon_card := h.horizon_card

/-! ### Canonically derived terminal atom data -/

/-- A forward terminal atom with only the genuinely pathwise compatibility
data left explicit.  Its finite sites, fixed inverse profile, capacity
bounds, and Proposition-4.4/horizon cardinalities are all derived from the
chronological parser coordinates. -/
structure YPhaseCanonicalTerminalExternalAtomInputs
    (m k start : ℕ) (specs : List (Bool × IncrementPair))
    (theta H : Set Path) where
  clockData : YPhaseTerminalClockInputs m k start specs
  theta_subset : selectiveTerminalPathAtom start specs ∩ H ∩ theta ⊆
    selectiveTerminalPathAtom start specs ∩ H ∩
      (primedIntervalStoppedThetaMinusEvent clockData.decoded.clock
          (yPhaseCanonicalSites clockData.baseAt) (sourceBandLowerNat m) ∪
        primedIntervalStoppedThetaPlusEvent clockData.decoded.clock
          (yPhaseCanonicalSites clockData.baseAt) m)
  minus_compatible : selectiveTerminalPathAtom start specs ∩ H ∩
      primedIntervalStoppedThetaMinusEvent clockData.decoded.clock
        (yPhaseCanonicalSites clockData.baseAt) (sourceBandLowerNat m) ⊆
    primedMinusPrefixCompatibleEvent clockData.decoded.clock
      (yPhaseCanonicalSites clockData.baseAt) (sourceBandLowerNat m)
      (yPhaseCanonicalProfile clockData.baseAt)
  plus_compatible : selectiveTerminalPathAtom start specs ∩ H ∩
      primedIntervalStoppedThetaPlusEvent clockData.decoded.clock
        (yPhaseCanonicalSites clockData.baseAt) m ⊆
    primedPriorPlusInitialPrefixCompatibleEvent clockData.decoded.clock
      (yPhaseCanonicalSites clockData.baseAt) m
  prop44_card : ((sourceProp44Candidates
      (yPhaseCanonicalSites clockData.baseAt) m
      (yPhaseCanonicalProfile clockData.baseAt)).card : ℝ) ≤
    Real.exp (16 * sourceRate m)
  coordinate_card : (clockData.encoding.q : ℝ) ≤
    Real.exp (16 * Real.sqrt (m : ℝ))

noncomputable def
    YPhaseCanonicalTerminalExternalAtomInputs.toTerminalExternalAtomInputs
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    {theta H : Set Path}
    (h : YPhaseCanonicalTerminalExternalAtomInputs
      m k start specs theta H) :
    YPhaseTerminalExternalAtomInputs m k start specs theta H where
  clockData := h.clockData
  sites := yPhaseCanonicalSites h.clockData.baseAt
  profile := yPhaseCanonicalProfile h.clockData.baseAt
  profile_atom := by
    intro s _
    intro x _
    rfl
  minus_capacity := by
    intro x _
    exact min_le_left _ _
  plus_capacity := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  theta_subset := h.theta_subset
  minus_compatible := h.minus_compatible
  plus_compatible := h.plus_compatible
  prop44_card := h.prop44_card
  horizon_card := by
    calc
      ((yPhaseCanonicalSites h.clockData.baseAt).card : ℝ) ≤
          (h.clockData.encoding.q : ℝ) := by
        exact_mod_cast yPhaseCanonicalSites_card_le h.clockData.baseAt
      _ ≤ Real.exp (16 * Real.sqrt (m : ℝ)) := h.coordinate_card

/-- The analogous independently conditioned backward terminal atom. -/
structure YPrimedPhaseCanonicalTerminalExternalAtomInputs
    (m k start : ℕ) (specs : List (Bool × IncrementPair))
    (theta H : Set Path) where
  clockData : YPrimedPhaseTerminalClockInputs m k start specs
  theta_subset : primedSelectiveTerminalPathAtom start specs ∩ H ∩ theta ⊆
    primedSelectiveTerminalPathAtom start specs ∩ H ∩
      (primedIntervalStoppedThetaMinusEvent clockData.decoded.clock
          (yPhaseCanonicalSites clockData.baseAt) (sourceBandLowerNat m) ∪
        primedIntervalStoppedThetaPlusEvent clockData.decoded.clock
          (yPhaseCanonicalSites clockData.baseAt) m)
  minus_compatible : primedSelectiveTerminalPathAtom start specs ∩ H ∩
      primedIntervalStoppedThetaMinusEvent clockData.decoded.clock
        (yPhaseCanonicalSites clockData.baseAt) (sourceBandLowerNat m) ⊆
    primedMinusPrefixCompatibleEvent clockData.decoded.clock
      (yPhaseCanonicalSites clockData.baseAt) (sourceBandLowerNat m)
      (yPhaseCanonicalProfile clockData.baseAt)
  plus_compatible : primedSelectiveTerminalPathAtom start specs ∩ H ∩
      primedIntervalStoppedThetaPlusEvent clockData.decoded.clock
        (yPhaseCanonicalSites clockData.baseAt) m ⊆
    primedPriorPlusInitialPrefixCompatibleEvent clockData.decoded.clock
      (yPhaseCanonicalSites clockData.baseAt) m
  prop44_card : ((sourceProp44Candidates
      (yPhaseCanonicalSites clockData.baseAt) m
      (yPhaseCanonicalProfile clockData.baseAt)).card : ℝ) ≤
    Real.exp (16 * sourceRate m)
  coordinate_card : (clockData.encoding.q : ℝ) ≤
    Real.exp (16 * Real.sqrt (m : ℝ))

noncomputable def
    YPrimedPhaseCanonicalTerminalExternalAtomInputs.toTerminalExternalAtomInputs
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    {theta H : Set Path}
    (h : YPrimedPhaseCanonicalTerminalExternalAtomInputs
      m k start specs theta H) :
    YPrimedPhaseTerminalExternalAtomInputs m k start specs theta H where
  clockData := h.clockData
  sites := yPhaseCanonicalSites h.clockData.baseAt
  profile := yPhaseCanonicalProfile h.clockData.baseAt
  profile_atom := by
    intro s _
    intro x _
    rfl
  minus_capacity := by
    intro x _
    exact min_le_left _ _
  plus_capacity := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  theta_subset := h.theta_subset
  minus_compatible := h.minus_compatible
  plus_compatible := h.plus_compatible
  prop44_card := h.prop44_card
  horizon_card := by
    calc
      ((yPhaseCanonicalSites h.clockData.baseAt).card : ℝ) ≤
          (h.clockData.encoding.q : ℝ) := by
        exact_mod_cast yPhaseCanonicalSites_card_le h.clockData.baseAt
      _ ≤ Real.exp (16 * Real.sqrt (m : ℝ)) := h.coordinate_card

/-! ### Initial-site source atoms

These final local wrappers remove the last arbitrary parser function.  The
base of each active coordinate is the recursively reconstructed site from
`initialSite` and the fixed terminal labels; the supplied mask proof checks
that these are precisely the even (respectively odd) column entries. -/

/-- Forward atom whose chronological base map is reconstructed rather than
chosen by the caller. -/
structure YPhaseInitialCanonicalTerminalExternalAtomInputs
    (m k start : ℕ) (specs : List (Bool × IncrementPair))
    (theta H : Set Path) where
  clockData : YPhaseInitialTerminalClockInputs m k start specs
  theta_subset : selectiveTerminalPathAtom start specs ∩ H ∩ theta ⊆
    selectiveTerminalPathAtom start specs ∩ H ∩
      (primedIntervalStoppedThetaMinusEvent
          clockData.toTerminalClockInputs.decoded.clock
          (yPhaseCanonicalSites clockData.toTerminalClockInputs.baseAt)
          (sourceBandLowerNat m) ∪
        primedIntervalStoppedThetaPlusEvent
          clockData.toTerminalClockInputs.decoded.clock
          (yPhaseCanonicalSites clockData.toTerminalClockInputs.baseAt) m)
  minus_compatible : selectiveTerminalPathAtom start specs ∩ H ∩
      primedIntervalStoppedThetaMinusEvent
        clockData.toTerminalClockInputs.decoded.clock
        (yPhaseCanonicalSites clockData.toTerminalClockInputs.baseAt)
        (sourceBandLowerNat m) ⊆
    primedMinusPrefixCompatibleEvent
      clockData.toTerminalClockInputs.decoded.clock
      (yPhaseCanonicalSites clockData.toTerminalClockInputs.baseAt)
      (sourceBandLowerNat m)
      (yPhaseCanonicalProfile clockData.toTerminalClockInputs.baseAt)
  plus_compatible : selectiveTerminalPathAtom start specs ∩ H ∩
      primedIntervalStoppedThetaPlusEvent
        clockData.toTerminalClockInputs.decoded.clock
        (yPhaseCanonicalSites clockData.toTerminalClockInputs.baseAt) m ⊆
    primedPriorPlusInitialPrefixCompatibleEvent
      clockData.toTerminalClockInputs.decoded.clock
      (yPhaseCanonicalSites clockData.toTerminalClockInputs.baseAt) m
  prop44_card : ((sourceProp44Candidates
      (yPhaseCanonicalSites clockData.toTerminalClockInputs.baseAt) m
      (yPhaseCanonicalProfile
        clockData.toTerminalClockInputs.baseAt)).card : ℝ) ≤
    Real.exp (16 * sourceRate m)
  spec_length_le : specs.length ≤
    HLOZExternalUpper.externalLabelCount (HLOZProp44.prop44Psi m)

noncomputable def
    YPhaseInitialCanonicalTerminalExternalAtomInputs.toCanonical
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    {theta H : Set Path}
    (h : YPhaseInitialCanonicalTerminalExternalAtomInputs
      m k start specs theta H)
    (hdepth :
      (HLOZExternalUpper.externalLabelCount
        (HLOZProp44.prop44Psi m) : ℝ) ≤
          Real.exp (16 * Real.sqrt (m : ℝ))) :
    YPhaseCanonicalTerminalExternalAtomInputs
      m k start specs theta H where
  clockData := h.clockData.toTerminalClockInputs
  theta_subset := h.theta_subset
  minus_compatible := h.minus_compatible
  plus_compatible := h.plus_compatible
  prop44_card := h.prop44_card
  coordinate_card := by
    calc
      (h.clockData.toTerminalClockInputs.encoding.q : ℝ) ≤
          (specs.length : ℝ) := by
        exact_mod_cast selectiveActiveCount_le_length specs
      _ ≤ (HLOZExternalUpper.externalLabelCount
          (HLOZProp44.prop44Psi m) : ℝ) := by
        exact_mod_cast h.spec_length_le
      _ ≤ Real.exp (16 * Real.sqrt (m : ℝ)) := hdepth

/-- Primed atom with the analogously reconstructed odd-column base map. -/
structure YPrimedPhaseInitialCanonicalTerminalExternalAtomInputs
    (m k start : ℕ) (specs : List (Bool × IncrementPair))
    (theta H : Set Path) where
  clockData : YPrimedPhaseInitialTerminalClockInputs m k start specs
  theta_subset : primedSelectiveTerminalPathAtom start specs ∩ H ∩ theta ⊆
    primedSelectiveTerminalPathAtom start specs ∩ H ∩
      (primedIntervalStoppedThetaMinusEvent
          clockData.toTerminalClockInputs.decoded.clock
          (yPhaseCanonicalSites clockData.toTerminalClockInputs.baseAt)
          (sourceBandLowerNat m) ∪
        primedIntervalStoppedThetaPlusEvent
          clockData.toTerminalClockInputs.decoded.clock
          (yPhaseCanonicalSites clockData.toTerminalClockInputs.baseAt) m)
  minus_compatible : primedSelectiveTerminalPathAtom start specs ∩ H ∩
      primedIntervalStoppedThetaMinusEvent
        clockData.toTerminalClockInputs.decoded.clock
        (yPhaseCanonicalSites clockData.toTerminalClockInputs.baseAt)
        (sourceBandLowerNat m) ⊆
    primedMinusPrefixCompatibleEvent
      clockData.toTerminalClockInputs.decoded.clock
      (yPhaseCanonicalSites clockData.toTerminalClockInputs.baseAt)
      (sourceBandLowerNat m)
      (yPhaseCanonicalProfile clockData.toTerminalClockInputs.baseAt)
  plus_compatible : primedSelectiveTerminalPathAtom start specs ∩ H ∩
      primedIntervalStoppedThetaPlusEvent
        clockData.toTerminalClockInputs.decoded.clock
        (yPhaseCanonicalSites clockData.toTerminalClockInputs.baseAt) m ⊆
    primedPriorPlusInitialPrefixCompatibleEvent
      clockData.toTerminalClockInputs.decoded.clock
      (yPhaseCanonicalSites clockData.toTerminalClockInputs.baseAt) m
  prop44_card : ((sourceProp44Candidates
      (yPhaseCanonicalSites clockData.toTerminalClockInputs.baseAt) m
      (yPhaseCanonicalProfile
        clockData.toTerminalClockInputs.baseAt)).card : ℝ) ≤
    Real.exp (16 * sourceRate m)
  spec_length_le : specs.length ≤
    HLOZExternalUpper.externalLabelCount (HLOZProp44.prop44Psi m)

noncomputable def
    YPrimedPhaseInitialCanonicalTerminalExternalAtomInputs.toCanonical
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    {theta H : Set Path}
    (h : YPrimedPhaseInitialCanonicalTerminalExternalAtomInputs
      m k start specs theta H)
    (hdepth :
      (HLOZExternalUpper.externalLabelCount
        (HLOZProp44.prop44Psi m) : ℝ) ≤
          Real.exp (16 * Real.sqrt (m : ℝ))) :
    YPrimedPhaseCanonicalTerminalExternalAtomInputs
      m k start specs theta H where
  clockData := h.clockData.toTerminalClockInputs
  theta_subset := h.theta_subset
  minus_compatible := h.minus_compatible
  plus_compatible := h.plus_compatible
  prop44_card := h.prop44_card
  coordinate_card := by
    calc
      (h.clockData.toTerminalClockInputs.encoding.q : ℝ) ≤
          (specs.length : ℝ) := by
        have hq : h.clockData.toTerminalClockInputs.encoding.q =
            selectiveActiveCount specs := by
          apply canonicalPrimedSelectivePairVectorEncoding_q
        rw [hq]
        exact_mod_cast selectiveActiveCount_le_length specs
      _ ≤ (HLOZExternalUpper.externalLabelCount
          (HLOZProp44.prop44Psi m) : ℝ) := by
        exact_mod_cast h.spec_length_le
      _ ≤ Real.exp (16 * Real.sqrt (m : ℝ)) := hdepth

/-! ### Literal-label source atoms

The following records use `yForwardTerminalSpec` and
`yPrimedTerminalSpec` directly.  Consequently neither an arbitrary active
mask nor a proof identifying that mask remains in the source cut. -/

/-- Forward source atom indexed only by an initial site and terminal pair
labels. -/
structure YPhaseLiteralTerminalExternalAtomInputs
    (m k start : ℕ) (initialSite : Site) (labels : List IncrementPair)
    (theta H : Set Path) where
  valid : SelectiveTerminalValid (yForwardTerminalSpec initialSite labels)
  theta_subset : selectiveTerminalPathAtom start
      (yForwardTerminalSpec initialSite labels) ∩ H ∩ theta ⊆
    selectiveTerminalPathAtom start
        (yForwardTerminalSpec initialSite labels) ∩ H ∩
      (primedIntervalStoppedThetaMinusEvent
          ((YPhaseInitialTerminalClockInputs.ofLabels
            m k start initialSite labels valid).toTerminalClockInputs.decoded.clock)
          (yPhaseCanonicalSites
            (YPhaseInitialTerminalClockInputs.ofLabels
              m k start initialSite labels valid).toTerminalClockInputs.baseAt)
          (sourceBandLowerNat m) ∪
        primedIntervalStoppedThetaPlusEvent
          ((YPhaseInitialTerminalClockInputs.ofLabels
            m k start initialSite labels valid).toTerminalClockInputs.decoded.clock)
          (yPhaseCanonicalSites
            (YPhaseInitialTerminalClockInputs.ofLabels
              m k start initialSite labels valid).toTerminalClockInputs.baseAt) m)
  minus_compatible : selectiveTerminalPathAtom start
      (yForwardTerminalSpec initialSite labels) ∩ H ∩
      primedIntervalStoppedThetaMinusEvent
        ((YPhaseInitialTerminalClockInputs.ofLabels
          m k start initialSite labels valid).toTerminalClockInputs.decoded.clock)
        (yPhaseCanonicalSites
          (YPhaseInitialTerminalClockInputs.ofLabels
            m k start initialSite labels valid).toTerminalClockInputs.baseAt)
        (sourceBandLowerNat m) ⊆
    primedMinusPrefixCompatibleEvent
      ((YPhaseInitialTerminalClockInputs.ofLabels
        m k start initialSite labels valid).toTerminalClockInputs.decoded.clock)
      (yPhaseCanonicalSites
        (YPhaseInitialTerminalClockInputs.ofLabels
          m k start initialSite labels valid).toTerminalClockInputs.baseAt)
      (sourceBandLowerNat m)
      (yPhaseCanonicalProfile
        (YPhaseInitialTerminalClockInputs.ofLabels
          m k start initialSite labels valid).toTerminalClockInputs.baseAt)
  plus_compatible : selectiveTerminalPathAtom start
      (yForwardTerminalSpec initialSite labels) ∩ H ∩
      primedIntervalStoppedThetaPlusEvent
        ((YPhaseInitialTerminalClockInputs.ofLabels
          m k start initialSite labels valid).toTerminalClockInputs.decoded.clock)
        (yPhaseCanonicalSites
          (YPhaseInitialTerminalClockInputs.ofLabels
            m k start initialSite labels valid).toTerminalClockInputs.baseAt) m ⊆
    primedPriorPlusInitialPrefixCompatibleEvent
      ((YPhaseInitialTerminalClockInputs.ofLabels
        m k start initialSite labels valid).toTerminalClockInputs.decoded.clock)
      (yPhaseCanonicalSites
        (YPhaseInitialTerminalClockInputs.ofLabels
          m k start initialSite labels valid).toTerminalClockInputs.baseAt) m
  prop44_card : ((sourceProp44Candidates
      (yPhaseCanonicalSites
        (YPhaseInitialTerminalClockInputs.ofLabels
          m k start initialSite labels valid).toTerminalClockInputs.baseAt) m
      (yPhaseCanonicalProfile
        (YPhaseInitialTerminalClockInputs.ofLabels
          m k start initialSite labels valid).toTerminalClockInputs.baseAt)).card : ℝ) ≤
    Real.exp (16 * sourceRate m)
  label_length_le : labels.length ≤
    HLOZExternalUpper.externalLabelCount (HLOZProp44.prop44Psi m)

noncomputable def YPhaseLiteralTerminalExternalAtomInputs.toInitial
    {m k start : ℕ} {initialSite : Site} {labels : List IncrementPair}
    {theta H : Set Path}
    (h : YPhaseLiteralTerminalExternalAtomInputs
      m k start initialSite labels theta H) :
    YPhaseInitialCanonicalTerminalExternalAtomInputs m k start
      (yForwardTerminalSpec initialSite labels) theta H where
  clockData := YPhaseInitialTerminalClockInputs.ofLabels
    m k start initialSite labels h.valid
  theta_subset := h.theta_subset
  minus_compatible := h.minus_compatible
  plus_compatible := h.plus_compatible
  prop44_card := h.prop44_card
  spec_length_le := by
    simpa only [yForwardTerminalSpec_length] using h.label_length_le

/-- Primed source atom indexed by the analogous fixed label list. -/
structure YPrimedPhaseLiteralTerminalExternalAtomInputs
    (m k start : ℕ) (initialSite : Site) (labels : List IncrementPair)
    (theta H : Set Path) where
  valid : PrimedSelectiveTerminalValid
    (yPrimedTerminalSpec initialSite labels)
  theta_subset : primedSelectiveTerminalPathAtom start
      (yPrimedTerminalSpec initialSite labels) ∩ H ∩ theta ⊆
    primedSelectiveTerminalPathAtom start
        (yPrimedTerminalSpec initialSite labels) ∩ H ∩
      (primedIntervalStoppedThetaMinusEvent
          ((YPrimedPhaseInitialTerminalClockInputs.ofLabels
            m k start initialSite labels valid).toTerminalClockInputs.decoded.clock)
          (yPhaseCanonicalSites
            (YPrimedPhaseInitialTerminalClockInputs.ofLabels
              m k start initialSite labels valid).toTerminalClockInputs.baseAt)
          (sourceBandLowerNat m) ∪
        primedIntervalStoppedThetaPlusEvent
          ((YPrimedPhaseInitialTerminalClockInputs.ofLabels
            m k start initialSite labels valid).toTerminalClockInputs.decoded.clock)
          (yPhaseCanonicalSites
            (YPrimedPhaseInitialTerminalClockInputs.ofLabels
              m k start initialSite labels valid).toTerminalClockInputs.baseAt) m)
  minus_compatible : primedSelectiveTerminalPathAtom start
      (yPrimedTerminalSpec initialSite labels) ∩ H ∩
      primedIntervalStoppedThetaMinusEvent
        ((YPrimedPhaseInitialTerminalClockInputs.ofLabels
          m k start initialSite labels valid).toTerminalClockInputs.decoded.clock)
        (yPhaseCanonicalSites
          (YPrimedPhaseInitialTerminalClockInputs.ofLabels
            m k start initialSite labels valid).toTerminalClockInputs.baseAt)
        (sourceBandLowerNat m) ⊆
    primedMinusPrefixCompatibleEvent
      ((YPrimedPhaseInitialTerminalClockInputs.ofLabels
        m k start initialSite labels valid).toTerminalClockInputs.decoded.clock)
      (yPhaseCanonicalSites
        (YPrimedPhaseInitialTerminalClockInputs.ofLabels
          m k start initialSite labels valid).toTerminalClockInputs.baseAt)
      (sourceBandLowerNat m)
      (yPhaseCanonicalProfile
        (YPrimedPhaseInitialTerminalClockInputs.ofLabels
          m k start initialSite labels valid).toTerminalClockInputs.baseAt)
  plus_compatible : primedSelectiveTerminalPathAtom start
      (yPrimedTerminalSpec initialSite labels) ∩ H ∩
      primedIntervalStoppedThetaPlusEvent
        ((YPrimedPhaseInitialTerminalClockInputs.ofLabels
          m k start initialSite labels valid).toTerminalClockInputs.decoded.clock)
        (yPhaseCanonicalSites
          (YPrimedPhaseInitialTerminalClockInputs.ofLabels
            m k start initialSite labels valid).toTerminalClockInputs.baseAt) m ⊆
    primedPriorPlusInitialPrefixCompatibleEvent
      ((YPrimedPhaseInitialTerminalClockInputs.ofLabels
        m k start initialSite labels valid).toTerminalClockInputs.decoded.clock)
      (yPhaseCanonicalSites
        (YPrimedPhaseInitialTerminalClockInputs.ofLabels
          m k start initialSite labels valid).toTerminalClockInputs.baseAt) m
  prop44_card : ((sourceProp44Candidates
      (yPhaseCanonicalSites
        (YPrimedPhaseInitialTerminalClockInputs.ofLabels
          m k start initialSite labels valid).toTerminalClockInputs.baseAt) m
      (yPhaseCanonicalProfile
        (YPrimedPhaseInitialTerminalClockInputs.ofLabels
          m k start initialSite labels valid).toTerminalClockInputs.baseAt)).card : ℝ) ≤
    Real.exp (16 * sourceRate m)
  label_length_le : labels.length ≤
    HLOZExternalUpper.externalLabelCount (HLOZProp44.prop44Psi m)

noncomputable def YPrimedPhaseLiteralTerminalExternalAtomInputs.toInitial
    {m k start : ℕ} {initialSite : Site} {labels : List IncrementPair}
    {theta H : Set Path}
    (h : YPrimedPhaseLiteralTerminalExternalAtomInputs
      m k start initialSite labels theta H) :
    YPrimedPhaseInitialCanonicalTerminalExternalAtomInputs m k start
      (yPrimedTerminalSpec initialSite labels) theta H where
  clockData := YPrimedPhaseInitialTerminalClockInputs.ofLabels
    m k start initialSite labels h.valid
  theta_subset := h.theta_subset
  minus_compatible := h.minus_compatible
  plus_compatible := h.plus_compatible
  prop44_card := h.prop44_card
  spec_length_le := by
    simpa only [yPrimedTerminalSpec_length] using h.label_length_le

private theorem YPhaseExternalAtomInputs.minus_law
    {m k : ℕ} {theta C H : Set Path}
    (h : YPhaseExternalAtomInputs m k theta C H)
    (x : Site) (hx : x ∈ h.sites) :
    HasLaw (fun s ↦ h.clock.inverseHoldingPrefix s
      (intervalDotIndex m (sourceBandLowerNat m) h.profile x) x)
      (negBinMeasure
        (intervalDotIndex m (sourceBandLowerNat m) h.profile x))
      simpleRandomWalkLaw[|C] :=
  h.parser.holdingPrefix_hasLaw x _ (h.minus_capacity x hx)

private theorem YPhaseExternalAtomInputs.plus_law
    {m k : ℕ} {theta C H : Set Path}
    (h : YPhaseExternalAtomInputs m k theta C H)
    (x : Site) (hx : x ∈ intervalPlusCandidates h.sites m m h.profile) :
    HasLaw (fun s ↦ h.clock.inverseHoldingPrefix s
      (intervalPriorHighCut m m) x)
      (negBinMeasure (intervalPriorHighCut m m)) simpleRandomWalkLaw[|C] :=
  h.parser.holdingPrefix_hasLaw x _
    ((Nat.sub_le (intervalHighCut m m) 1).trans (h.plus_capacity x hx))

theorem YPhaseExternalAtomInputs.conditional_theta_le
    {m k : ℕ} {theta C H : Set Path}
    (hs : SourceIntervalScale m (sourceBandLowerNat m) ∧
      SourceUpperScale m m)
    (h : YPhaseExternalAtomInputs m k theta C H) :
    simpleRandomWalkLaw[|C] (C ∩ H ∩ theta) ≤
      sourceProp45OneSideError m := by
  let minusEvent := primedIntervalStoppedThetaMinusEvent h.clock h.sites
    (sourceBandLowerNat m)
  let plusEvent := primedIntervalStoppedThetaPlusEvent h.clock h.sites m
  have hminusSubset : C ∩ H ∩ minusEvent ⊆
      primedIntervalCanonicalDotThetaMinusEvent h.clock h.sites
        (sourceBandLowerNat m) h.profile := by
    intro s hs'
    apply primedStoppedThetaMinus_subset_canonicalDotTheta
      h.clock h.sites (sourceBandLowerNat m) h.profile
    exact ⟨⟨hs'.2, h.profile_atom hs'.1.1⟩,
      h.minus_compatible hs'⟩
  have hplusSubset : C ∩ H ∩ plusEvent ⊆
      primedIntervalCanonicalPriorDotThetaPlusEvent
        h.clock h.sites m h.profile := by
    intro s hs'
    apply primedStoppedThetaPlus_subset_canonicalPriorDotTheta
      h.clock h.sites m h.profile
    exact ⟨⟨hs'.2, h.profile_atom hs'.1.1⟩,
      h.plus_compatible hs'⟩
  have hminus : simpleRandomWalkLaw[|C] (C ∩ H ∩ minusEvent) ≤
      ENNReal.ofReal (Real.exp (-sourceRate m)) +
        ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ))) :=
    cond_inter_primedStoppedThetaMinus_le_two_scale h.clock
      (sourceBandLowerNat m) hs.1 simpleRandomWalkLaw C H h.sites h.profile
      hminusSubset h.prop44_card h.horizon_card h.minus_law
  have hplus : simpleRandomWalkLaw[|C] (C ∩ H ∩ plusEvent) ≤
      ENNReal.ofReal (Real.exp (-sourceRate m)) :=
    cond_inter_primedStoppedThetaPriorPlus_le_exp h.clock m hs.2
      simpleRandomWalkLaw C H h.sites h.profile hplusSubset h.prop44_card
      h.plus_law
  calc
    simpleRandomWalkLaw[|C] (C ∩ H ∩ theta) ≤
        simpleRandomWalkLaw[|C] (C ∩ H ∩ (minusEvent ∪ plusEvent)) :=
      measure_mono h.theta_subset
    _ ≤ simpleRandomWalkLaw[|C] (C ∩ H ∩ minusEvent) +
        simpleRandomWalkLaw[|C] (C ∩ H ∩ plusEvent) := by
      have hunion : C ∩ H ∩ (minusEvent ∪ plusEvent) =
          (C ∩ H ∩ minusEvent) ∪ (C ∩ H ∩ plusEvent) := by
        ext s
        simp only [Set.mem_inter_iff, Set.mem_union]
        tauto
      rw [hunion]
      exact measure_union_le _ _
    _ ≤ sourceProp45OneSideError m := add_le_add hminus hplus

/-- A finite conditional partition for exactly one phase of the `Y`
deletion.  A second value of this structure is required for the other phase;
there is no common atom family in this interface. -/
structure YPhaseFiniteAtomization
    (m k badCoeff : ℕ) (theta : Set Path) where
  atoms : Finset ℕ
  atom : ℕ → Set Path
  horizon : Set Path
  bad : Set Path
  measurable_atom : ∀ j ∈ atoms, MeasurableSet (atom j)
  atomInputs : ∀ j ∈ atoms,
    YPhaseExternalAtomInputs m k theta (atom j) horizon
  pairwise : (atoms : Set ℕ).PairwiseDisjoint atom
  cover : theta ⊆ bad ∪ ⋃ j ∈ atoms,
    atom j ∩ horizon ∩ theta
  bad_bound : simpleRandomWalkLaw bad ≤
    sourceExceptionalRateWithPrefactor m badCoeff kappa

/-- A forward finite atomization whose atoms are literal fixed terminal
paths.  Its vector encoding, iid-geometric law, decoded inverse clock, and
measurability are all constructed internally. -/
structure YPhaseTerminalFiniteAtomization
    (m k badCoeff : ℕ) (theta : Set Path) where
  atoms : Finset ℕ
  start : ℕ → ℕ
  specs : ℕ → List (Bool × IncrementPair)
  horizon : Set Path
  bad : Set Path
  atomInputs : ∀ j ∈ atoms,
    YPhaseTerminalExternalAtomInputs m k (start j) (specs j) theta horizon
  pairwise : (atoms : Set ℕ).PairwiseDisjoint fun j ↦
    selectiveTerminalPathAtom (start j) (specs j)
  cover : theta ⊆ bad ∪ ⋃ j ∈ atoms,
    selectiveTerminalPathAtom (start j) (specs j) ∩ horizon ∩ theta
  bad_bound : simpleRandomWalkLaw bad ≤
    sourceExceptionalRateWithPrefactor m badCoeff kappa

noncomputable def YPhaseTerminalFiniteAtomization.toPhaseFiniteAtomization
    {m k badCoeff : ℕ} {theta : Set Path}
    (h : YPhaseTerminalFiniteAtomization m k badCoeff theta) :
    YPhaseFiniteAtomization m k badCoeff theta where
  atoms := h.atoms
  atom := fun j ↦ selectiveTerminalPathAtom (h.start j) (h.specs j)
  horizon := h.horizon
  bad := h.bad
  measurable_atom := fun j _ ↦
    measurableSet_selectiveTerminalPathAtom (h.start j) (h.specs j)
  atomInputs := fun j hj ↦ (h.atomInputs j hj).toExternalAtomInputs
  pairwise := h.pairwise
  cover := h.cover
  bad_bound := h.bad_bound

/-- The backward/primed finite atomization uses its own terminal families;
it is not a joint conditioning with the forward family. -/
structure YPrimedPhaseTerminalFiniteAtomization
    (m k badCoeff : ℕ) (theta : Set Path) where
  atoms : Finset ℕ
  start : ℕ → ℕ
  specs : ℕ → List (Bool × IncrementPair)
  horizon : Set Path
  bad : Set Path
  atomInputs : ∀ j ∈ atoms,
    YPrimedPhaseTerminalExternalAtomInputs m k (start j) (specs j) theta horizon
  pairwise : (atoms : Set ℕ).PairwiseDisjoint fun j ↦
    primedSelectiveTerminalPathAtom (start j) (specs j)
  cover : theta ⊆ bad ∪ ⋃ j ∈ atoms,
    primedSelectiveTerminalPathAtom (start j) (specs j) ∩ horizon ∩ theta
  bad_bound : simpleRandomWalkLaw bad ≤
    sourceExceptionalRateWithPrefactor m badCoeff kappa

noncomputable def
    YPrimedPhaseTerminalFiniteAtomization.toPhaseFiniteAtomization
    {m k badCoeff : ℕ} {theta : Set Path}
    (h : YPrimedPhaseTerminalFiniteAtomization m k badCoeff theta) :
    YPhaseFiniteAtomization m k badCoeff theta where
  atoms := h.atoms
  atom := fun j ↦ primedSelectiveTerminalPathAtom (h.start j) (h.specs j)
  horizon := h.horizon
  bad := h.bad
  measurable_atom := fun j _ ↦
    measurableEmbedding_simpleRandomWalk.measurableSet_image.2
      (measurableSet_primedSelectiveTerminalLabelsEqFrom
        (h.start j) (h.specs j))
  atomInputs := fun j hj ↦ (h.atomInputs j hj).toExternalAtomInputs
  pairwise := h.pairwise
  cover := h.cover
  bad_bound := h.bad_bound

/-- Source-facing forward finite atomization after canonicalizing the site
set and inverse profile. -/
structure YPhaseCanonicalTerminalFiniteAtomization
    (m k badCoeff : ℕ) (theta : Set Path) where
  atoms : Finset ℕ
  start : ℕ → ℕ
  specs : ℕ → List (Bool × IncrementPair)
  horizon : Set Path
  bad : Set Path
  atomInputs : ∀ j ∈ atoms,
    YPhaseCanonicalTerminalExternalAtomInputs
      m k (start j) (specs j) theta horizon
  pairwise : (atoms : Set ℕ).PairwiseDisjoint fun j ↦
    selectiveTerminalPathAtom (start j) (specs j)
  cover : theta ⊆ bad ∪ ⋃ j ∈ atoms,
    selectiveTerminalPathAtom (start j) (specs j) ∩ horizon ∩ theta
  bad_bound : simpleRandomWalkLaw bad ≤
    sourceExceptionalRateWithPrefactor m badCoeff kappa

noncomputable def
    YPhaseCanonicalTerminalFiniteAtomization.toTerminalFiniteAtomization
    {m k badCoeff : ℕ} {theta : Set Path}
    (h : YPhaseCanonicalTerminalFiniteAtomization m k badCoeff theta) :
    YPhaseTerminalFiniteAtomization m k badCoeff theta where
  atoms := h.atoms
  start := h.start
  specs := h.specs
  horizon := h.horizon
  bad := h.bad
  atomInputs := fun j hj ↦
    (h.atomInputs j hj).toTerminalExternalAtomInputs
  pairwise := h.pairwise
  cover := h.cover
  bad_bound := h.bad_bound

/-- Source-facing backward finite atomization with the same canonical
site/profile reduction. -/
structure YPrimedPhaseCanonicalTerminalFiniteAtomization
    (m k badCoeff : ℕ) (theta : Set Path) where
  atoms : Finset ℕ
  start : ℕ → ℕ
  specs : ℕ → List (Bool × IncrementPair)
  horizon : Set Path
  bad : Set Path
  atomInputs : ∀ j ∈ atoms,
    YPrimedPhaseCanonicalTerminalExternalAtomInputs
      m k (start j) (specs j) theta horizon
  pairwise : (atoms : Set ℕ).PairwiseDisjoint fun j ↦
    primedSelectiveTerminalPathAtom (start j) (specs j)
  cover : theta ⊆ bad ∪ ⋃ j ∈ atoms,
    primedSelectiveTerminalPathAtom (start j) (specs j) ∩ horizon ∩ theta
  bad_bound : simpleRandomWalkLaw bad ≤
    sourceExceptionalRateWithPrefactor m badCoeff kappa

noncomputable def
    YPrimedPhaseCanonicalTerminalFiniteAtomization.toTerminalFiniteAtomization
    {m k badCoeff : ℕ} {theta : Set Path}
    (h : YPrimedPhaseCanonicalTerminalFiniteAtomization
      m k badCoeff theta) :
    YPrimedPhaseTerminalFiniteAtomization m k badCoeff theta where
  atoms := h.atoms
  start := h.start
  specs := h.specs
  horizon := h.horizon
  bad := h.bad
  atomInputs := fun j hj ↦
    (h.atomInputs j hj).toTerminalExternalAtomInputs
  pairwise := h.pairwise
  cover := h.cover
  bad_bound := h.bad_bound

/-- Forward finite terminal atomization after reconstructing the active
base map from one initial site per atom. -/
structure YPhaseInitialCanonicalTerminalFiniteAtomization
    (m k badCoeff : ℕ) (theta : Set Path) where
  atoms : Finset ℕ
  start : ℕ → ℕ
  specs : ℕ → List (Bool × IncrementPair)
  horizon : Set Path
  bad : Set Path
  atomInputs : ∀ j ∈ atoms,
    YPhaseInitialCanonicalTerminalExternalAtomInputs
      m k (start j) (specs j) theta horizon
  pairwise : (atoms : Set ℕ).PairwiseDisjoint fun j ↦
    selectiveTerminalPathAtom (start j) (specs j)
  cover : theta ⊆ bad ∪ ⋃ j ∈ atoms,
    selectiveTerminalPathAtom (start j) (specs j) ∩ horizon ∩ theta
  bad_bound : simpleRandomWalkLaw bad ≤
    sourceExceptionalRateWithPrefactor m badCoeff kappa

noncomputable def
    YPhaseInitialCanonicalTerminalFiniteAtomization.toCanonical
    {m k badCoeff : ℕ} {theta : Set Path}
    (h : YPhaseInitialCanonicalTerminalFiniteAtomization
      m k badCoeff theta)
    (hdepth :
      (HLOZExternalUpper.externalLabelCount
        (HLOZProp44.prop44Psi m) : ℝ) ≤
          Real.exp (16 * Real.sqrt (m : ℝ))) :
    YPhaseCanonicalTerminalFiniteAtomization m k badCoeff theta where
  atoms := h.atoms
  start := h.start
  specs := h.specs
  horizon := h.horizon
  bad := h.bad
  atomInputs := fun j hj ↦ (h.atomInputs j hj).toCanonical hdepth
  pairwise := h.pairwise
  cover := h.cover
  bad_bound := h.bad_bound

/-- Primed finite terminal atomization with the odd-column mask and
initial-site base reconstruction checked atomwise. -/
structure YPrimedPhaseInitialCanonicalTerminalFiniteAtomization
    (m k badCoeff : ℕ) (theta : Set Path) where
  atoms : Finset ℕ
  start : ℕ → ℕ
  specs : ℕ → List (Bool × IncrementPair)
  horizon : Set Path
  bad : Set Path
  atomInputs : ∀ j ∈ atoms,
    YPrimedPhaseInitialCanonicalTerminalExternalAtomInputs
      m k (start j) (specs j) theta horizon
  pairwise : (atoms : Set ℕ).PairwiseDisjoint fun j ↦
    primedSelectiveTerminalPathAtom (start j) (specs j)
  cover : theta ⊆ bad ∪ ⋃ j ∈ atoms,
    primedSelectiveTerminalPathAtom (start j) (specs j) ∩ horizon ∩ theta
  bad_bound : simpleRandomWalkLaw bad ≤
    sourceExceptionalRateWithPrefactor m badCoeff kappa

noncomputable def
    YPrimedPhaseInitialCanonicalTerminalFiniteAtomization.toCanonical
    {m k badCoeff : ℕ} {theta : Set Path}
    (h : YPrimedPhaseInitialCanonicalTerminalFiniteAtomization
      m k badCoeff theta)
    (hdepth :
      (HLOZExternalUpper.externalLabelCount
        (HLOZProp44.prop44Psi m) : ℝ) ≤
          Real.exp (16 * Real.sqrt (m : ℝ))) :
    YPrimedPhaseCanonicalTerminalFiniteAtomization m k badCoeff theta where
  atoms := h.atoms
  start := h.start
  specs := h.specs
  horizon := h.horizon
  bad := h.bad
  atomInputs := fun j hj ↦ (h.atomInputs j hj).toCanonical hdepth
  pairwise := h.pairwise
  cover := h.cover
  bad_bound := h.bad_bound

/-- Forward finite atomization by literal fixed terminal label lists. -/
structure YPhaseLiteralTerminalFiniteAtomization
    (m k badCoeff : ℕ) (theta : Set Path) where
  atoms : Finset ℕ
  start : ℕ → ℕ
  initialSite : ℕ → Site
  labels : ℕ → List IncrementPair
  horizon : Set Path
  bad : Set Path
  atomInputs : ∀ j ∈ atoms,
    YPhaseLiteralTerminalExternalAtomInputs m k (start j)
      (initialSite j) (labels j) theta horizon
  pairwise : (atoms : Set ℕ).PairwiseDisjoint fun j ↦
    selectiveTerminalPathAtom (start j)
      (yForwardTerminalSpec (initialSite j) (labels j))
  cover : theta ⊆ bad ∪ ⋃ j ∈ atoms,
    selectiveTerminalPathAtom (start j)
      (yForwardTerminalSpec (initialSite j) (labels j)) ∩ horizon ∩ theta
  bad_bound : simpleRandomWalkLaw bad ≤
    sourceExceptionalRateWithPrefactor m badCoeff kappa

noncomputable def YPhaseLiteralTerminalFiniteAtomization.toInitial
    {m k badCoeff : ℕ} {theta : Set Path}
    (h : YPhaseLiteralTerminalFiniteAtomization m k badCoeff theta) :
    YPhaseInitialCanonicalTerminalFiniteAtomization m k badCoeff theta where
  atoms := h.atoms
  start := h.start
  specs := fun j ↦ yForwardTerminalSpec (h.initialSite j) (h.labels j)
  horizon := h.horizon
  bad := h.bad
  atomInputs := fun j hj ↦ (h.atomInputs j hj).toInitial
  pairwise := h.pairwise
  cover := h.cover
  bad_bound := h.bad_bound

/-- Primed finite atomization by literal fixed terminal label lists. -/
structure YPrimedPhaseLiteralTerminalFiniteAtomization
    (m k badCoeff : ℕ) (theta : Set Path) where
  atoms : Finset ℕ
  start : ℕ → ℕ
  initialSite : ℕ → Site
  labels : ℕ → List IncrementPair
  horizon : Set Path
  bad : Set Path
  atomInputs : ∀ j ∈ atoms,
    YPrimedPhaseLiteralTerminalExternalAtomInputs m k (start j)
      (initialSite j) (labels j) theta horizon
  pairwise : (atoms : Set ℕ).PairwiseDisjoint fun j ↦
    primedSelectiveTerminalPathAtom (start j)
      (yPrimedTerminalSpec (initialSite j) (labels j))
  cover : theta ⊆ bad ∪ ⋃ j ∈ atoms,
    primedSelectiveTerminalPathAtom (start j)
      (yPrimedTerminalSpec (initialSite j) (labels j)) ∩ horizon ∩ theta
  bad_bound : simpleRandomWalkLaw bad ≤
    sourceExceptionalRateWithPrefactor m badCoeff kappa

noncomputable def YPrimedPhaseLiteralTerminalFiniteAtomization.toInitial
    {m k badCoeff : ℕ} {theta : Set Path}
    (h : YPrimedPhaseLiteralTerminalFiniteAtomization m k badCoeff theta) :
    YPrimedPhaseInitialCanonicalTerminalFiniteAtomization
      m k badCoeff theta where
  atoms := h.atoms
  start := h.start
  specs := fun j ↦ yPrimedTerminalSpec (h.initialSite j) (h.labels j)
  horizon := h.horizon
  bad := h.bad
  atomInputs := fun j hj ↦ (h.atomInputs j hj).toInitial
  pairwise := h.pairwise
  cover := h.cover
  bad_bound := h.bad_bound

/-! ### Origin-started literal terminal atoms

The canonical random walk starts at the origin, and the terminal pair
cylinders used for the column decomposition may be read from pair index
zero.  In that auxiliary form neither the beginning pair index nor its
absolute site is atom data.  The more general package above remains useful
for tail cylinders.  These records are retained as sufficient formal routes,
but the final source closure now uses the direct column estimate instead. -/

/-- Forward terminal atomization read from pair index zero at the origin. -/
structure YPhaseOriginTerminalFiniteAtomization
    (m k badCoeff : ℕ) (theta : Set Path) where
  atoms : Finset ℕ
  labels : ℕ → List IncrementPair
  horizon : Set Path
  bad : Set Path
  atomInputs : ∀ j ∈ atoms,
    YPhaseLiteralTerminalExternalAtomInputs m k 0 (0, 0)
      (labels j) theta horizon
  pairwise : (atoms : Set ℕ).PairwiseDisjoint fun j ↦
    selectiveTerminalPathAtom 0
      (yForwardTerminalSpec (0, 0) (labels j))
  cover : theta ⊆ bad ∪ ⋃ j ∈ atoms,
    selectiveTerminalPathAtom 0
      (yForwardTerminalSpec (0, 0) (labels j)) ∩ horizon ∩ theta
  bad_bound : simpleRandomWalkLaw bad ≤
    sourceExceptionalRateWithPrefactor m badCoeff kappa

noncomputable def YPhaseOriginTerminalFiniteAtomization.toLiteral
    {m k badCoeff : ℕ} {theta : Set Path}
    (h : YPhaseOriginTerminalFiniteAtomization m k badCoeff theta) :
    YPhaseLiteralTerminalFiniteAtomization m k badCoeff theta where
  atoms := h.atoms
  start := fun _ ↦ 0
  initialSite := fun _ ↦ (0, 0)
  labels := h.labels
  horizon := h.horizon
  bad := h.bad
  atomInputs := h.atomInputs
  pairwise := h.pairwise
  cover := h.cover
  bad_bound := h.bad_bound

/-- Primed terminal atomization read from pair index zero at the origin. -/
structure YPrimedPhaseOriginTerminalFiniteAtomization
    (m k badCoeff : ℕ) (theta : Set Path) where
  atoms : Finset ℕ
  labels : ℕ → List IncrementPair
  horizon : Set Path
  bad : Set Path
  atomInputs : ∀ j ∈ atoms,
    YPrimedPhaseLiteralTerminalExternalAtomInputs m k 0 (0, 0)
      (labels j) theta horizon
  pairwise : (atoms : Set ℕ).PairwiseDisjoint fun j ↦
    primedSelectiveTerminalPathAtom 0
      (yPrimedTerminalSpec (0, 0) (labels j))
  cover : theta ⊆ bad ∪ ⋃ j ∈ atoms,
    primedSelectiveTerminalPathAtom 0
      (yPrimedTerminalSpec (0, 0) (labels j)) ∩ horizon ∩ theta
  bad_bound : simpleRandomWalkLaw bad ≤
    sourceExceptionalRateWithPrefactor m badCoeff kappa

noncomputable def YPrimedPhaseOriginTerminalFiniteAtomization.toLiteral
    {m k badCoeff : ℕ} {theta : Set Path}
    (h : YPrimedPhaseOriginTerminalFiniteAtomization m k badCoeff theta) :
    YPrimedPhaseLiteralTerminalFiniteAtomization m k badCoeff theta where
  atoms := h.atoms
  start := fun _ ↦ 0
  initialSite := fun _ ↦ (0, 0)
  labels := h.labels
  horizon := h.horizon
  bad := h.bad
  atomInputs := h.atomInputs
  pairwise := h.pairwise
  cover := h.cover
  bad_bound := h.bad_bound

/-- Forward origin-started atoms on the canonical near-critical horizon.
The horizon complement and its probability are supplied globally by
Appendix A, rather than repeated as fields of this column package. -/
structure YPhaseOriginCanonicalHorizonAtomization
    (m k : ℕ) (theta : Set Path) where
  atoms : Finset ℕ
  labels : ℕ → List IncrementPair
  atomInputs : ∀ j ∈ atoms,
    YPhaseLiteralTerminalExternalAtomInputs m k 0 (0, 0)
      (labels j) theta
        (HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k)
  pairwise : (atoms : Set ℕ).PairwiseDisjoint fun j ↦
    selectiveTerminalPathAtom 0
      (yForwardTerminalSpec (0, 0) (labels j))
  cover : theta ⊆
    (HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k)ᶜ ∪
      ⋃ j ∈ atoms,
        selectiveTerminalPathAtom 0
          (yForwardTerminalSpec (0, 0) (labels j)) ∩
            HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k ∩ theta

noncomputable def YPhaseOriginCanonicalHorizonAtomization.toOrigin
    {m k : ℕ} {theta : Set Path}
    (h : YPhaseOriginCanonicalHorizonAtomization m k theta)
    (hHorizon : simpleRandomWalkLaw
        (HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k)ᶜ ≤
      sourceExceptionalRateWithPrefactor m 1 kappa) :
    YPhaseOriginTerminalFiniteAtomization m k 1 theta where
  atoms := h.atoms
  labels := h.labels
  horizon := HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k
  bad := (HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k)ᶜ
  atomInputs := h.atomInputs
  pairwise := h.pairwise
  cover := h.cover
  bad_bound := hHorizon

/-- Primed origin-started atoms on the same canonical near-critical
horizon. -/
structure YPrimedPhaseOriginCanonicalHorizonAtomization
    (m k : ℕ) (theta : Set Path) where
  atoms : Finset ℕ
  labels : ℕ → List IncrementPair
  atomInputs : ∀ j ∈ atoms,
    YPrimedPhaseLiteralTerminalExternalAtomInputs m k 0 (0, 0)
      (labels j) theta
        (HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k)
  pairwise : (atoms : Set ℕ).PairwiseDisjoint fun j ↦
    primedSelectiveTerminalPathAtom 0
      (yPrimedTerminalSpec (0, 0) (labels j))
  cover : theta ⊆
    (HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k)ᶜ ∪
      ⋃ j ∈ atoms,
        primedSelectiveTerminalPathAtom 0
          (yPrimedTerminalSpec (0, 0) (labels j)) ∩
            HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k ∩ theta

noncomputable def YPrimedPhaseOriginCanonicalHorizonAtomization.toOrigin
    {m k : ℕ} {theta : Set Path}
    (h : YPrimedPhaseOriginCanonicalHorizonAtomization m k theta)
    (hHorizon : simpleRandomWalkLaw
        (HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k)ᶜ ≤
      sourceExceptionalRateWithPrefactor m 1 kappa) :
    YPrimedPhaseOriginTerminalFiniteAtomization m k 1 theta where
  atoms := h.atoms
  labels := h.labels
  horizon := HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k
  bad := (HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k)ᶜ
  atomInputs := h.atomInputs
  pairwise := h.pairwise
  cover := h.cover
  bad_bound := hHorizon

/-- Forward canonical-horizon atoms at one fixed terminal-label depth.
Distinct indices must carry distinct label vectors; the parser uniqueness
theorem then supplies pairwise disjointness automatically. -/
noncomputable def fixedTerminalLabelEmbedding (q : ℕ) :
    (Fin q → IncrementPair) ↪ ℕ :=
  (Fintype.equivFin (Fin q → IncrementPair)).toEmbedding.trans
    Fin.valEmbedding

noncomputable def fixedTerminalLabelOfCode (q j : ℕ) :
    Fin q → IncrementPair :=
  if hj : j < Fintype.card (Fin q → IncrementPair) then
    (Fintype.equivFin (Fin q → IncrementPair)).symm ⟨j, hj⟩
  else default

@[simp] theorem fixedTerminalLabelOfCode_embedding
    (q : ℕ) (v : Fin q → IncrementPair) :
    fixedTerminalLabelOfCode q (fixedTerminalLabelEmbedding q v) = v := by
  let e := Fintype.equivFin (Fin q → IncrementPair)
  change (if hj : (e v).val < Fintype.card (Fin q → IncrementPair) then
      e.symm ⟨(e v).val, hj⟩ else default) = v
  rw [dif_pos (e v).isLt]
  exact e.symm_apply_apply v

structure YPhaseOriginCanonicalFixedDepthAtomization
    (m k q : ℕ) (theta : Set Path) where
  atoms : Finset ℕ
  labels : ℕ → Fin q → IncrementPair
  labels_injective : Set.InjOn labels atoms
  atomInputs : ∀ j ∈ atoms,
    YPhaseLiteralTerminalExternalAtomInputs m k 0 (0, 0)
      (List.ofFn (labels j)) theta
        (HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k)
  cover : theta ⊆
    (HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k)ᶜ ∪
      ⋃ j ∈ atoms,
        selectiveTerminalPathAtom 0
          (yForwardTerminalSpec (0, 0) (List.ofFn (labels j))) ∩
            HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k ∩ theta

noncomputable def
    YPhaseOriginCanonicalFixedDepthAtomization.toCanonicalHorizon
    {m k q : ℕ} {theta : Set Path}
    (h : YPhaseOriginCanonicalFixedDepthAtomization m k q theta) :
    YPhaseOriginCanonicalHorizonAtomization m k theta where
  atoms := h.atoms
  labels := fun j ↦ List.ofFn (h.labels j)
  atomInputs := h.atomInputs
  pairwise := by
    intro j hj l hl hjl
    apply disjoint_yForwardTerminalPathAtom_of_ne
    · simp
    · exact (h.atomInputs j hj).valid
    · exact (h.atomInputs l hl).valid
    · intro heq
      apply hjl
      exact h.labels_injective hj hl (List.ofFn_injective heq)
  cover := h.cover

/-- Primed canonical-horizon atoms at one fixed terminal-label depth. -/
structure YPrimedPhaseOriginCanonicalFixedDepthAtomization
    (m k q : ℕ) (theta : Set Path) where
  atoms : Finset ℕ
  labels : ℕ → Fin q → IncrementPair
  labels_injective : Set.InjOn labels atoms
  atomInputs : ∀ j ∈ atoms,
    YPrimedPhaseLiteralTerminalExternalAtomInputs m k 0 (0, 0)
      (List.ofFn (labels j)) theta
        (HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k)
  cover : theta ⊆
    (HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k)ᶜ ∪
      ⋃ j ∈ atoms,
        primedSelectiveTerminalPathAtom 0
          (yPrimedTerminalSpec (0, 0) (List.ofFn (labels j))) ∩
            HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k ∩ theta

/-- Source-facing forward fixed-depth atoms indexed directly by their
literal label vectors.  The conversion below supplies a canonical numeric
encoding, so the source data need not carry an arbitrary injective index. -/
structure YPhaseOriginCanonicalLabelAtomization
    (m k q : ℕ) (theta : Set Path) where
  atoms : Finset (Fin q → IncrementPair)
  atomInputs : ∀ labels ∈ atoms,
    YPhaseLiteralTerminalExternalAtomInputs m k 0 (0, 0)
      (List.ofFn labels) theta
        (HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k)
  cover : theta ⊆
    (HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k)ᶜ ∪
      ⋃ labels ∈ atoms,
        selectiveTerminalPathAtom 0
          (yForwardTerminalSpec (0, 0) (List.ofFn labels)) ∩
            HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k ∩ theta

noncomputable def YPhaseOriginCanonicalLabelAtomization.toFixedDepth
    {m k q : ℕ} {theta : Set Path}
    (h : YPhaseOriginCanonicalLabelAtomization m k q theta) :
    YPhaseOriginCanonicalFixedDepthAtomization m k q theta where
  atoms := h.atoms.map (fixedTerminalLabelEmbedding q)
  labels := fixedTerminalLabelOfCode q
  labels_injective := by
    intro j hj l hl hjl
    rcases Finset.mem_map.1 hj with ⟨v, hv, rfl⟩
    rcases Finset.mem_map.1 hl with ⟨w, hw, rfl⟩
    simpa using congrArg (fixedTerminalLabelEmbedding q) hjl
  atomInputs := by
    intro j hj
    rcases Finset.mem_map.1 hj with ⟨v, hv, rfl⟩
    simpa using h.atomInputs v hv
  cover := by
    intro omega homega
    have hcover := h.cover homega
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_iUnion] at hcover ⊢
    rcases hcover with hbad | ⟨v, hv, hmem⟩
    · exact Or.inl hbad
    · exact Or.inr ⟨fixedTerminalLabelEmbedding q v,
        Finset.mem_map.2 ⟨v, hv, rfl⟩, by simpa using hmem⟩

/-- Primed source-facing fixed-depth atoms indexed directly by labels. -/
structure YPrimedPhaseOriginCanonicalLabelAtomization
    (m k q : ℕ) (theta : Set Path) where
  atoms : Finset (Fin q → IncrementPair)
  atomInputs : ∀ labels ∈ atoms,
    YPrimedPhaseLiteralTerminalExternalAtomInputs m k 0 (0, 0)
      (List.ofFn labels) theta
        (HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k)
  cover : theta ⊆
    (HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k)ᶜ ∪
      ⋃ labels ∈ atoms,
        primedSelectiveTerminalPathAtom 0
          (yPrimedTerminalSpec (0, 0) (List.ofFn labels)) ∩
            HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k ∩ theta

noncomputable def YPrimedPhaseOriginCanonicalLabelAtomization.toFixedDepth
    {m k q : ℕ} {theta : Set Path}
    (h : YPrimedPhaseOriginCanonicalLabelAtomization m k q theta) :
    YPrimedPhaseOriginCanonicalFixedDepthAtomization m k q theta where
  atoms := h.atoms.map (fixedTerminalLabelEmbedding q)
  labels := fixedTerminalLabelOfCode q
  labels_injective := by
    intro j hj l hl hjl
    rcases Finset.mem_map.1 hj with ⟨v, hv, rfl⟩
    rcases Finset.mem_map.1 hl with ⟨w, hw, rfl⟩
    simpa using congrArg (fixedTerminalLabelEmbedding q) hjl
  atomInputs := by
    intro j hj
    rcases Finset.mem_map.1 hj with ⟨v, hv, rfl⟩
    simpa using h.atomInputs v hv
  cover := by
    intro omega homega
    have hcover := h.cover homega
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_iUnion] at hcover ⊢
    rcases hcover with hbad | ⟨v, hv, hmem⟩
    · exact Or.inl hbad
    · exact Or.inr ⟨fixedTerminalLabelEmbedding q v,
        Finset.mem_map.2 ⟨v, hv, rfl⟩, by simpa using hmem⟩

noncomputable def
    YPrimedPhaseOriginCanonicalFixedDepthAtomization.toCanonicalHorizon
    {m k q : ℕ} {theta : Set Path}
    (h : YPrimedPhaseOriginCanonicalFixedDepthAtomization m k q theta) :
    YPrimedPhaseOriginCanonicalHorizonAtomization m k theta where
  atoms := h.atoms
  labels := fun j ↦ List.ofFn (h.labels j)
  atomInputs := h.atomInputs
  pairwise := by
    intro j hj l hl hjl
    apply disjoint_yPrimedTerminalPathAtom_of_ne
    · simp
    · exact (h.atomInputs j hj).valid
    · exact (h.atomInputs l hl).valid
    · intro heq
      apply hjl
      exact h.labels_injective hj hl (List.ofFn_injective heq)
  cover := h.cover

theorem YPhaseFiniteAtomization.theta_measure_le
    {m k badCoeff : ℕ} {theta : Set Path}
    (hs : SourceIntervalScale m (sourceBandLowerNat m) ∧
      SourceUpperScale m m)
    (habsorb : sourceProp45OneSideError m ≤
      sourceExceptionalRateWithPrefactor m 3 kappa)
    (h : YPhaseFiniteAtomization m k badCoeff theta) :
    simpleRandomWalkLaw theta ≤
      sourceExceptionalRateWithPrefactor m (badCoeff + 3) kappa := by
  have hcore := measure_le_bad_add_of_finite_conditional_partition
    simpleRandomWalkLaw h.atoms h.atom theta h.horizon h.bad
    (sourceProp45OneSideError m)
    (sourceExceptionalRateWithPrefactor m badCoeff kappa)
    h.measurable_atom h.pairwise h.cover h.bad_bound
    (fun j hj ↦ (h.atomInputs j hj).conditional_theta_le hs)
  calc
    simpleRandomWalkLaw theta ≤
      sourceExceptionalRateWithPrefactor m badCoeff kappa +
        sourceProp45OneSideError m := hcore
    _ ≤ sourceExceptionalRateWithPrefactor m badCoeff kappa +
        sourceExceptionalRateWithPrefactor m 3 kappa := by gcongr
    _ = sourceExceptionalRateWithPrefactor m (badCoeff + 3) kappa := by
      simp only [sourceExceptionalRateWithPrefactor]
      push_cast
      ring

theorem stoppedThetaEvent_y_eq (m k : ℕ) :
    stoppedThetaEvent (canonicalProfiles ⟨4, by omega⟩)
      (canonicalCStar ⟨4, by omega⟩) m k =
        yUnprimedThetaEvent m k ∪ yPrimedThetaEvent m k := by
  ext s
  simp only [stoppedThetaEvent, stoppedThetaSites, canonicalProfiles,
    pairingProfiles, pairingDeletion, deletionProfilePair, canonicalCStar,
    yUnprimedThetaEvent, yPrimedThetaEvent, Set.mem_setOf_eq, Set.mem_union,
    Finset.union_nonempty]
  tauto

/-- The unprimed half of the actual Proposition-4.5 source event.  The
pairing history is essential: Proposition 4.5 estimates `Θ ∩ M`, not the
unconditional stopped imbalance event. -/
noncomputable def yUnprimedSourceEvent (m k : ℕ) : Set Path :=
  prefixPairingEvent m ⟨4, by omega⟩ (k + 1) ∩ yUnprimedThetaEvent m k

/-- The separately conditioned primed half of the same source event. -/
noncomputable def yPrimedSourceEvent (m k : ℕ) : Set Path :=
  prefixPairingEvent m ⟨4, by omega⟩ (k + 1) ∩ yPrimedThetaEvent m k

theorem prefixPairing_inter_stoppedThetaEvent_y_eq (m k : ℕ) :
    prefixPairingEvent m ⟨4, by omega⟩ (k + 1) ∩
        stoppedThetaEvent (canonicalProfiles ⟨4, by omega⟩)
          (canonicalCStar ⟨4, by omega⟩) m k =
      yUnprimedSourceEvent m k ∪ yPrimedSourceEvent m k := by
  rw [stoppedThetaEvent_y_eq]
  ext s
  simp only [yUnprimedSourceEvent, yPrimedSourceEvent, Set.mem_inter_iff,
    Set.mem_union]
  tauto

structure YSeparateFiniteAtomizations
    (m k unprimedBadCoeff primedBadCoeff : ℕ) where
  unprimed : YPhaseFiniteAtomization m k unprimedBadCoeff
    (yUnprimedThetaEvent m k)
  primed : YPhaseFiniteAtomization m k primedBadCoeff
    (yPrimedThetaEvent m k)

/-- An auxiliary residual column cut for the endpoint-adapted formal column
profiles: the two phases are atomized separately, and each cover is restricted
to the required pairing history.  No estimate of bare `Θ` is requested.

This package is a sufficient formal route, but it is not identified here with
the temporal-parity deletion in HLOZ (2.12).  A source-level use therefore
needs a separate event-identification/coverage theorem. -/
structure YSourceSeparateFiniteAtomizations
    (m k unprimedBadCoeff primedBadCoeff : ℕ) where
  unprimed : YPhaseFiniteAtomization m k unprimedBadCoeff
    (yUnprimedSourceEvent m k)
  primed : YPhaseFiniteAtomization m k primedBadCoeff
    (yPrimedSourceEvent m k)

/-- The narrowed auxiliary cut after constructing both adaptive parsers and
their laws: only terminal-path covers and the deterministic
compatibility/cardinality data on those atoms remain. -/
structure YSourceTerminalSeparateFiniteAtomizations
    (m k unprimedBadCoeff primedBadCoeff : ℕ) where
  unprimed : YPhaseTerminalFiniteAtomization m k unprimedBadCoeff
    (yUnprimedSourceEvent m k)
  primed : YPrimedPhaseTerminalFiniteAtomization m k primedBadCoeff
    (yPrimedSourceEvent m k)

/-- A narrow terminal-column Proposition-4.5 package for the auxiliary
adaptive-parser route.  Site/profile/capacity data are canonical; the
remaining local fields are the candidate bound and the three pathwise
stopped-clock inclusions. -/
structure YSourceCanonicalTerminalSeparateFiniteAtomizations
    (m k unprimedBadCoeff primedBadCoeff : ℕ) where
  unprimed : YPhaseCanonicalTerminalFiniteAtomization m k unprimedBadCoeff
    (yUnprimedSourceEvent m k)
  primed : YPrimedPhaseCanonicalTerminalFiniteAtomization m k primedBadCoeff
    (yPrimedSourceEvent m k)

/-- Literal terminal-column source package with no arbitrary base map.
Each phase supplies only an initial site, fixed labels, the checked parity
mask, and the genuine event/cardinality inputs. -/
structure YSourceInitialCanonicalTerminalSeparateFiniteAtomizations
    (m k unprimedBadCoeff primedBadCoeff : ℕ) where
  unprimed : YPhaseInitialCanonicalTerminalFiniteAtomization
    m k unprimedBadCoeff (yUnprimedSourceEvent m k)
  primed : YPrimedPhaseInitialCanonicalTerminalFiniteAtomization
    m k primedBadCoeff (yPrimedSourceEvent m k)

/-- Narrowest current terminal-column package: both phases are finite
families of literal pair-label cylinders, based at one initial site per
atom. -/
structure YSourceLiteralTerminalSeparateFiniteAtomizations
    (m k unprimedBadCoeff primedBadCoeff : ℕ) where
  unprimed : YPhaseLiteralTerminalFiniteAtomization
    m k unprimedBadCoeff (yUnprimedSourceEvent m k)
  primed : YPrimedPhaseLiteralTerminalFiniteAtomization
    m k primedBadCoeff (yPrimedSourceEvent m k)

/-- Origin-started terminal-column source package.  Both phases are indexed
only by literal pair-label lists; their cylinder start and initial site are
the canonical zero values of `simpleRandomWalk`. -/
structure YSourceOriginTerminalSeparateFiniteAtomizations
    (m k unprimedBadCoeff primedBadCoeff : ℕ) where
  unprimed : YPhaseOriginTerminalFiniteAtomization
    m k unprimedBadCoeff (yUnprimedSourceEvent m k)
  primed : YPrimedPhaseOriginTerminalFiniteAtomization
    m k primedBadCoeff (yPrimedSourceEvent m k)

/-- Both origin-started terminal phases on the canonical near-critical
horizon.  No arbitrary horizon or exceptional-set estimate remains in this
auxiliary parser package. -/
structure YSourceOriginCanonicalHorizonSeparateAtomizations
    (m k : ℕ) where
  unprimed : YPhaseOriginCanonicalHorizonAtomization
    m k (yUnprimedSourceEvent m k)
  primed : YPrimedPhaseOriginCanonicalHorizonAtomization
    m k (yPrimedSourceEvent m k)

/-- Fixed-depth form of the canonical origin-started column package.  The
depth is the deterministic external-label budget from Proposition 4.4. -/
structure YSourceOriginCanonicalFixedDepthSeparateAtomizations
    (m k : ℕ) where
  unprimed : YPhaseOriginCanonicalFixedDepthAtomization m k
    (HLOZExternalUpper.externalLabelCount (HLOZProp44.prop44Psi m))
      (yUnprimedSourceEvent m k)
  primed : YPrimedPhaseOriginCanonicalFixedDepthAtomization m k
    (HLOZExternalUpper.externalLabelCount (HLOZProp44.prop44Psi m))
      (yPrimedSourceEvent m k)

/-- Canonical fixed-depth column atoms indexed directly by their literal
label vectors.  This is the source-facing package: numeric encodings and
their injectivity are constructed internally. -/
structure YSourceOriginCanonicalLabelSeparateAtomizations
    (m k : ℕ) where
  unprimed : YPhaseOriginCanonicalLabelAtomization m k
    (HLOZExternalUpper.externalLabelCount (HLOZProp44.prop44Psi m))
      (yUnprimedSourceEvent m k)
  primed : YPrimedPhaseOriginCanonicalLabelAtomization m k
    (HLOZExternalUpper.externalLabelCount (HLOZProp44.prop44Psi m))
      (yPrimedSourceEvent m k)

noncomputable def yCanonicalTerminalLabelDepth (m : ℕ) : ℕ :=
  HLOZExternalUpper.externalLabelCount (HLOZProp44.prop44Psi m)

/-- The canonical finite set of forward labels on which all remaining
literal Proposition-4.5 atom data are available. -/
noncomputable def yForwardCanonicalGoodLabels (m k : ℕ) :
    Finset (Fin (yCanonicalTerminalLabelDepth m) → IncrementPair) := by
  classical
  exact Finset.univ.filter fun labels ↦ Nonempty
      (YPhaseLiteralTerminalExternalAtomInputs m k 0 (0, 0)
        (List.ofFn labels) (yUnprimedSourceEvent m k)
          (HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k))

/-- The analogous canonical set for the primed/backward phase. -/
noncomputable def yPrimedCanonicalGoodLabels (m k : ℕ) :
    Finset (Fin (yCanonicalTerminalLabelDepth m) → IncrementPair) := by
  classical
  exact Finset.univ.filter fun labels ↦ Nonempty
      (YPrimedPhaseLiteralTerminalExternalAtomInputs m k 0 (0, 0)
        (List.ofFn labels) (yPrimedSourceEvent m k)
          (HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k))

theorem yForwardCanonicalGoodLabels_nonempty_input
    {m k : ℕ}
    {labels : Fin (yCanonicalTerminalLabelDepth m) → IncrementPair}
    (hlabels : labels ∈ yForwardCanonicalGoodLabels m k) : Nonempty
      (YPhaseLiteralTerminalExternalAtomInputs m k 0 (0, 0)
        (List.ofFn labels) (yUnprimedSourceEvent m k)
          (HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k)) := by
  simpa only [yForwardCanonicalGoodLabels, Finset.mem_filter,
    Finset.mem_univ, true_and] using hlabels

theorem yPrimedCanonicalGoodLabels_nonempty_input
    {m k : ℕ}
    {labels : Fin (yCanonicalTerminalLabelDepth m) → IncrementPair}
    (hlabels : labels ∈ yPrimedCanonicalGoodLabels m k) : Nonempty
      (YPrimedPhaseLiteralTerminalExternalAtomInputs m k 0 (0, 0)
        (List.ofFn labels) (yPrimedSourceEvent m k)
          (HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k)) := by
  simpa only [yPrimedCanonicalGoodLabels, Finset.mem_filter,
    Finset.mem_univ, true_and] using hlabels

noncomputable def yForwardCanonicalGoodLabelUnion (m k : ℕ) : Set Path :=
  ⋃ labels ∈ yForwardCanonicalGoodLabels m k,
    selectiveTerminalPathAtom 0
      (yForwardTerminalSpec (0, 0) (List.ofFn labels))

noncomputable def yPrimedCanonicalGoodLabelUnion (m k : ℕ) : Set Path :=
  ⋃ labels ∈ yPrimedCanonicalGoodLabels m k,
    primedSelectiveTerminalPathAtom 0
      (yPrimedTerminalSpec (0, 0) (List.ofFn labels))

/-- The honest forward residual: paths in the source event and canonical
horizon which are not captured by any label carrying the local
Proposition-4.4/stopped-clock data. -/
noncomputable def yForwardCanonicalGoodLabelFailureEvent
    (m k : ℕ) : Set Path :=
  yUnprimedSourceEvent m k ∩
    HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k ∩
      (yForwardCanonicalGoodLabelUnion m k)ᶜ

noncomputable def yPrimedCanonicalGoodLabelFailureEvent
    (m k : ℕ) : Set Path :=
  yPrimedSourceEvent m k ∩
    HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k ∩
      (yPrimedCanonicalGoodLabelUnion m k)ᶜ

/-- The forward residual after parser completeness has been discharged:
the label is a valid terminal label, but it does not carry all of the local
Proposition-4.4/stopped-clock data. -/
noncomputable def yForwardCanonicalBadDataLabelUnion (m k : ℕ) : Set Path :=
  by
    classical
    exact ⋃ labels : Fin (yCanonicalTerminalLabelDepth m) → IncrementPair,
      if SelectiveTerminalValid
          (yForwardTerminalSpec (0, 0) (List.ofFn labels)) ∧
          labels ∉ yForwardCanonicalGoodLabels m k then
        selectiveTerminalPathAtom 0
          (yForwardTerminalSpec (0, 0) (List.ofFn labels))
      else ∅

noncomputable def yPrimedCanonicalBadDataLabelUnion (m k : ℕ) : Set Path :=
  by
    classical
    exact ⋃ labels : Fin (yCanonicalTerminalLabelDepth m) → IncrementPair,
      if PrimedSelectiveTerminalValid
          (yPrimedTerminalSpec (0, 0) (List.ofFn labels)) ∧
          labels ∉ yPrimedCanonicalGoodLabels m k then
        primedSelectiveTerminalPathAtom 0
          (yPrimedTerminalSpec (0, 0) (List.ofFn labels))
      else ∅

noncomputable def yForwardCanonicalBadDataFailureEvent
    (m k : ℕ) : Set Path :=
  yUnprimedSourceEvent m k ∩
    HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k ∩
      yForwardCanonicalBadDataLabelUnion m k

noncomputable def yPrimedCanonicalBadDataFailureEvent
    (m k : ℕ) : Set Path :=
  yPrimedSourceEvent m k ∩
    HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k ∩
      yPrimedCanonicalBadDataLabelUnion m k

private theorem yForwardGoodLabelFailure_subset_badData_union_parserNull
    (m k : ℕ) :
    yForwardCanonicalGoodLabelFailureEvent m k ⊆
      yForwardCanonicalBadDataFailureEvent m k ∪
        (yForwardValidTerminalPathUnion (0, 0) 0
          (yCanonicalTerminalLabelDepth m))ᶜ := by
  classical
  intro omega homega
  by_cases hvalidUnion : omega ∈
      yForwardValidTerminalPathUnion (0, 0) 0
        (yCanonicalTerminalLabelDepth m)
  · left
    simp only [yForwardValidTerminalPathUnion, Set.mem_iUnion] at hvalidUnion
    rcases hvalidUnion with ⟨labels, hlabelsAtom⟩
    by_cases hvalid : SelectiveTerminalValid
        (yForwardTerminalSpec (0, 0) (List.ofFn labels))
    · simp only [hvalid, if_true] at hlabelsAtom
      have hnotGood : labels ∉ yForwardCanonicalGoodLabels m k := by
        intro hgood
        apply homega.2
        simp only [yForwardCanonicalGoodLabelUnion, Set.mem_iUnion]
        exact ⟨labels, hgood, hlabelsAtom⟩
      exact ⟨homega.1, by
        simp only [yForwardCanonicalBadDataLabelUnion, Set.mem_iUnion]
        exact ⟨labels, by simp [hvalid, hnotGood, hlabelsAtom]⟩⟩
    · simp [hvalid] at hlabelsAtom
  · right
    exact hvalidUnion

private theorem yForwardBadDataFailure_subset_goodLabelFailure
    (m k : ℕ) :
    yForwardCanonicalBadDataFailureEvent m k ⊆
      yForwardCanonicalGoodLabelFailureEvent m k := by
  classical
  intro omega homega
  refine ⟨homega.1, ?_⟩
  intro hgoodUnion
  have hB := homega.2
  simp only [yForwardCanonicalBadDataLabelUnion, Set.mem_iUnion] at hB
  rcases hB with ⟨labels, hbad⟩
  by_cases hvalid : SelectiveTerminalValid
      (yForwardTerminalSpec (0, 0) (List.ofFn labels)) ∧
      labels ∉ yForwardCanonicalGoodLabels m k
  · simp only [hvalid, if_true] at hbad
    simp only [yForwardCanonicalGoodLabelUnion, Set.mem_iUnion] at hgoodUnion
    rcases hgoodUnion with ⟨labels', hlabelsGood, hgoodAtom⟩
    have hvalid' : SelectiveTerminalValid
        (yForwardTerminalSpec (0, 0) (List.ofFn labels')) :=
      (Classical.choice
        (yForwardCanonicalGoodLabels_nonempty_input hlabelsGood)).valid
    by_cases heq : labels = labels'
    · exact hvalid.2 (heq ▸ hlabelsGood)
    · exact Set.disjoint_left.mp
        (disjoint_yForwardTerminalPathAtom_of_ne
          (by simp) hvalid.1 hvalid'
          (fun hlist ↦ heq (List.ofFn_injective hlist))) hbad hgoodAtom
  · simp [hvalid] at hbad

theorem simpleRandomWalkLaw_yForwardGoodLabelFailure_eq_badDataFailure
    (m k : ℕ) :
    simpleRandomWalkLaw (yForwardCanonicalGoodLabelFailureEvent m k) =
      simpleRandomWalkLaw (yForwardCanonicalBadDataFailureEvent m k) := by
  apply le_antisymm
  · calc
      simpleRandomWalkLaw (yForwardCanonicalGoodLabelFailureEvent m k) ≤
          simpleRandomWalkLaw
            (yForwardCanonicalBadDataFailureEvent m k ∪
              (yForwardValidTerminalPathUnion (0, 0) 0
                (yCanonicalTerminalLabelDepth m))ᶜ) :=
        measure_mono (yForwardGoodLabelFailure_subset_badData_union_parserNull
          m k)
      _ ≤ simpleRandomWalkLaw (yForwardCanonicalBadDataFailureEvent m k) +
          simpleRandomWalkLaw
            (yForwardValidTerminalPathUnion (0, 0) 0
              (yCanonicalTerminalLabelDepth m))ᶜ := measure_union_le _ _
      _ = simpleRandomWalkLaw
          (yForwardCanonicalBadDataFailureEvent m k) := by
        rw [simpleRandomWalkLaw_yForwardValidTerminalPathUnion_compl,
          add_zero]
  · exact measure_mono
      (yForwardBadDataFailure_subset_goodLabelFailure m k)

private theorem yPrimedGoodLabelFailure_subset_badData_union_parserNull
    (m k : ℕ) :
    yPrimedCanonicalGoodLabelFailureEvent m k ⊆
      yPrimedCanonicalBadDataFailureEvent m k ∪
        (yPrimedValidTerminalPathUnion (0, 0) 0
          (yCanonicalTerminalLabelDepth m))ᶜ := by
  classical
  intro omega homega
  by_cases hvalidUnion : omega ∈
      yPrimedValidTerminalPathUnion (0, 0) 0
        (yCanonicalTerminalLabelDepth m)
  · left
    simp only [yPrimedValidTerminalPathUnion, Set.mem_iUnion] at hvalidUnion
    rcases hvalidUnion with ⟨labels, hlabelsAtom⟩
    by_cases hvalid : PrimedSelectiveTerminalValid
        (yPrimedTerminalSpec (0, 0) (List.ofFn labels))
    · simp only [hvalid, if_true] at hlabelsAtom
      have hnotGood : labels ∉ yPrimedCanonicalGoodLabels m k := by
        intro hgood
        apply homega.2
        simp only [yPrimedCanonicalGoodLabelUnion, Set.mem_iUnion]
        exact ⟨labels, hgood, hlabelsAtom⟩
      exact ⟨homega.1, by
        simp only [yPrimedCanonicalBadDataLabelUnion, Set.mem_iUnion]
        exact ⟨labels, by simp [hvalid, hnotGood, hlabelsAtom]⟩⟩
    · simp [hvalid] at hlabelsAtom
  · right
    exact hvalidUnion

private theorem yPrimedBadDataFailure_subset_goodLabelFailure
    (m k : ℕ) :
    yPrimedCanonicalBadDataFailureEvent m k ⊆
      yPrimedCanonicalGoodLabelFailureEvent m k := by
  classical
  intro omega homega
  refine ⟨homega.1, ?_⟩
  intro hgoodUnion
  have hB := homega.2
  simp only [yPrimedCanonicalBadDataLabelUnion, Set.mem_iUnion] at hB
  rcases hB with ⟨labels, hbad⟩
  by_cases hvalid : PrimedSelectiveTerminalValid
      (yPrimedTerminalSpec (0, 0) (List.ofFn labels)) ∧
      labels ∉ yPrimedCanonicalGoodLabels m k
  · simp only [hvalid, if_true] at hbad
    simp only [yPrimedCanonicalGoodLabelUnion, Set.mem_iUnion] at hgoodUnion
    rcases hgoodUnion with ⟨labels', hlabelsGood, hgoodAtom⟩
    have hvalid' : PrimedSelectiveTerminalValid
        (yPrimedTerminalSpec (0, 0) (List.ofFn labels')) :=
      (Classical.choice
        (yPrimedCanonicalGoodLabels_nonempty_input hlabelsGood)).valid
    by_cases heq : labels = labels'
    · exact hvalid.2 (heq ▸ hlabelsGood)
    · exact Set.disjoint_left.mp
        (disjoint_yPrimedTerminalPathAtom_of_ne
          (by simp) hvalid.1 hvalid'
          (fun hlist ↦ heq (List.ofFn_injective hlist))) hbad hgoodAtom
  · simp [hvalid] at hbad

theorem simpleRandomWalkLaw_yPrimedGoodLabelFailure_eq_badDataFailure
    (m k : ℕ) :
    simpleRandomWalkLaw (yPrimedCanonicalGoodLabelFailureEvent m k) =
      simpleRandomWalkLaw (yPrimedCanonicalBadDataFailureEvent m k) := by
  apply le_antisymm
  · calc
      simpleRandomWalkLaw (yPrimedCanonicalGoodLabelFailureEvent m k) ≤
          simpleRandomWalkLaw
            (yPrimedCanonicalBadDataFailureEvent m k ∪
              (yPrimedValidTerminalPathUnion (0, 0) 0
                (yCanonicalTerminalLabelDepth m))ᶜ) :=
        measure_mono (yPrimedGoodLabelFailure_subset_badData_union_parserNull
          m k)
      _ ≤ simpleRandomWalkLaw (yPrimedCanonicalBadDataFailureEvent m k) +
          simpleRandomWalkLaw
            (yPrimedValidTerminalPathUnion (0, 0) 0
              (yCanonicalTerminalLabelDepth m))ᶜ := measure_union_le _ _
      _ = simpleRandomWalkLaw
          (yPrimedCanonicalBadDataFailureEvent m k) := by
        rw [simpleRandomWalkLaw_yPrimedValidTerminalPathUnion_compl,
          add_zero]
  · exact measure_mono
      (yPrimedBadDataFailure_subset_goodLabelFailure m k)

theorem yForwardCanonicalGoodLabelInput
    {m k : ℕ}
    {labels : Fin (yCanonicalTerminalLabelDepth m) → IncrementPair}
    (hlabels : labels ∈ yForwardCanonicalGoodLabels m k) :
    YPhaseLiteralTerminalExternalAtomInputs m k 0 (0, 0)
      (List.ofFn labels) (yUnprimedSourceEvent m k)
        (HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k) :=
  Classical.choice (yForwardCanonicalGoodLabels_nonempty_input hlabels)

theorem yPrimedCanonicalGoodLabelInput
    {m k : ℕ}
    {labels : Fin (yCanonicalTerminalLabelDepth m) → IncrementPair}
    (hlabels : labels ∈ yPrimedCanonicalGoodLabels m k) :
    YPrimedPhaseLiteralTerminalExternalAtomInputs m k 0 (0, 0)
      (List.ofFn labels) (yPrimedSourceEvent m k)
        (HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k) :=
  Classical.choice (yPrimedCanonicalGoodLabels_nonempty_input hlabels)

noncomputable def yForwardOriginAtomization_of_goodLabelFailure
    {m k : ℕ}
    (hHorizon : simpleRandomWalkLaw
        (HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k)ᶜ ≤
      sourceExceptionalRateWithPrefactor m 1 kappa)
    (hFailure : simpleRandomWalkLaw
        (yForwardCanonicalGoodLabelFailureEvent m k) ≤
      sourceExceptionalRateWithPrefactor m 1 kappa) :
    YPhaseOriginTerminalFiniteAtomization m k 2
      (yUnprimedSourceEvent m k) where
  atoms := (yForwardCanonicalGoodLabels m k).map
    (fixedTerminalLabelEmbedding (yCanonicalTerminalLabelDepth m))
  labels := fun j ↦ List.ofFn
    (fixedTerminalLabelOfCode (yCanonicalTerminalLabelDepth m) j)
  horizon := HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k
  bad := (HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k)ᶜ ∪
    yForwardCanonicalGoodLabelFailureEvent m k
  atomInputs := by
    intro j hj
    rcases Finset.mem_map.1 hj with ⟨labels, hlabels, rfl⟩
    simpa using yForwardCanonicalGoodLabelInput hlabels
  pairwise := by
    intro j hj l hl hjl
    rcases Finset.mem_map.1 hj with ⟨labels, hlabels, rfl⟩
    rcases Finset.mem_map.1 hl with ⟨labels', hlabels', rfl⟩
    apply disjoint_yForwardTerminalPathAtom_of_ne
    · simp
    · simpa only [fixedTerminalLabelOfCode_embedding] using
        (yForwardCanonicalGoodLabelInput hlabels).valid
    · simpa only [fixedTerminalLabelOfCode_embedding] using
        (yForwardCanonicalGoodLabelInput hlabels').valid
    · intro heq
      simp only [fixedTerminalLabelOfCode_embedding] at heq
      apply hjl
      exact congrArg (fixedTerminalLabelEmbedding
        (yCanonicalTerminalLabelDepth m)) (List.ofFn_injective heq)
  cover := by
    intro omega homega
    by_cases hH : omega ∈
        HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k
    · by_cases hgood : omega ∈ yForwardCanonicalGoodLabelUnion m k
      · right
        simp only [yForwardCanonicalGoodLabelUnion, Set.mem_iUnion] at hgood
        rcases hgood with ⟨labels, hlabels, hatom⟩
        simp only [Set.mem_iUnion]
        exact ⟨fixedTerminalLabelEmbedding (yCanonicalTerminalLabelDepth m)
            labels, Finset.mem_map.2 ⟨labels, hlabels, rfl⟩,
          by simpa using And.intro (And.intro hatom hH) homega⟩
      · left
        right
        exact ⟨⟨homega, hH⟩, hgood⟩
    · left
      left
      exact hH
  bad_bound := by
    calc
      simpleRandomWalkLaw
          ((HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k)ᶜ ∪
            yForwardCanonicalGoodLabelFailureEvent m k) ≤
        simpleRandomWalkLaw
            (HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k)ᶜ +
          simpleRandomWalkLaw
            (yForwardCanonicalGoodLabelFailureEvent m k) := measure_union_le _ _
      _ ≤ sourceExceptionalRateWithPrefactor m 1 kappa +
          sourceExceptionalRateWithPrefactor m 1 kappa :=
        add_le_add hHorizon hFailure
      _ = sourceExceptionalRateWithPrefactor m 2 kappa := by
        simp only [sourceExceptionalRateWithPrefactor]
        push_cast
        ring

noncomputable def yPrimedOriginAtomization_of_goodLabelFailure
    {m k : ℕ}
    (hHorizon : simpleRandomWalkLaw
        (HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k)ᶜ ≤
      sourceExceptionalRateWithPrefactor m 1 kappa)
    (hFailure : simpleRandomWalkLaw
        (yPrimedCanonicalGoodLabelFailureEvent m k) ≤
      sourceExceptionalRateWithPrefactor m 1 kappa) :
    YPrimedPhaseOriginTerminalFiniteAtomization m k 2
      (yPrimedSourceEvent m k) where
  atoms := (yPrimedCanonicalGoodLabels m k).map
    (fixedTerminalLabelEmbedding (yCanonicalTerminalLabelDepth m))
  labels := fun j ↦ List.ofFn
    (fixedTerminalLabelOfCode (yCanonicalTerminalLabelDepth m) j)
  horizon := HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k
  bad := (HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k)ᶜ ∪
    yPrimedCanonicalGoodLabelFailureEvent m k
  atomInputs := by
    intro j hj
    rcases Finset.mem_map.1 hj with ⟨labels, hlabels, rfl⟩
    simpa using yPrimedCanonicalGoodLabelInput hlabels
  pairwise := by
    intro j hj l hl hjl
    rcases Finset.mem_map.1 hj with ⟨labels, hlabels, rfl⟩
    rcases Finset.mem_map.1 hl with ⟨labels', hlabels', rfl⟩
    apply disjoint_yPrimedTerminalPathAtom_of_ne
    · simp
    · simpa only [fixedTerminalLabelOfCode_embedding] using
        (yPrimedCanonicalGoodLabelInput hlabels).valid
    · simpa only [fixedTerminalLabelOfCode_embedding] using
        (yPrimedCanonicalGoodLabelInput hlabels').valid
    · intro heq
      simp only [fixedTerminalLabelOfCode_embedding] at heq
      apply hjl
      exact congrArg (fixedTerminalLabelEmbedding
        (yCanonicalTerminalLabelDepth m)) (List.ofFn_injective heq)
  cover := by
    intro omega homega
    by_cases hH : omega ∈
        HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k
    · by_cases hgood : omega ∈ yPrimedCanonicalGoodLabelUnion m k
      · right
        simp only [yPrimedCanonicalGoodLabelUnion, Set.mem_iUnion] at hgood
        rcases hgood with ⟨labels, hlabels, hatom⟩
        simp only [Set.mem_iUnion]
        exact ⟨fixedTerminalLabelEmbedding (yCanonicalTerminalLabelDepth m)
            labels, Finset.mem_map.2 ⟨labels, hlabels, rfl⟩,
          by simpa using And.intro (And.intro hatom hH) homega⟩
      · left
        right
        exact ⟨⟨homega, hH⟩, hgood⟩
    · left
      left
      exact hH
  bad_bound := by
    calc
      simpleRandomWalkLaw
          ((HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k)ᶜ ∪
            yPrimedCanonicalGoodLabelFailureEvent m k) ≤
        simpleRandomWalkLaw
            (HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k)ᶜ +
          simpleRandomWalkLaw
            (yPrimedCanonicalGoodLabelFailureEvent m k) := measure_union_le _ _
      _ ≤ sourceExceptionalRateWithPrefactor m 1 kappa +
          sourceExceptionalRateWithPrefactor m 1 kappa :=
        add_le_add hHorizon hFailure
      _ = sourceExceptionalRateWithPrefactor m 2 kappa := by
        simp only [sourceExceptionalRateWithPrefactor]
        push_cast
        ring

/-- Narrowest current Y-column cut.  The good-label sets are canonical;
the only supplied facts are that they cover the two source events on the
canonical horizon.  Membership itself contains exactly the remaining
literal Proposition-4.4 and stopped-clock data. -/
structure YSourceOriginCanonicalGoodLabelCovers (m k : ℕ) where
  unprimed_cover : yUnprimedSourceEvent m k ⊆
    (HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k)ᶜ ∪
      ⋃ labels ∈ yForwardCanonicalGoodLabels m k,
        selectiveTerminalPathAtom 0
          (yForwardTerminalSpec (0, 0) (List.ofFn labels)) ∩
            HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k ∩
              yUnprimedSourceEvent m k
  primed_cover : yPrimedSourceEvent m k ⊆
    (HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k)ᶜ ∪
      ⋃ labels ∈ yPrimedCanonicalGoodLabels m k,
        primedSelectiveTerminalPathAtom 0
          (yPrimedTerminalSpec (0, 0) (List.ofFn labels)) ∩
            HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k ∩
              yPrimedSourceEvent m k

noncomputable def YSourceOriginCanonicalGoodLabelCovers.toLabelAtomizations
    {m k : ℕ} (h : YSourceOriginCanonicalGoodLabelCovers m k) :
    YSourceOriginCanonicalLabelSeparateAtomizations m k where
  unprimed := {
    atoms := yForwardCanonicalGoodLabels m k
    atomInputs := fun _ hlabels ↦
      Classical.choice (yForwardCanonicalGoodLabels_nonempty_input hlabels)
    cover := h.unprimed_cover }
  primed := {
    atoms := yPrimedCanonicalGoodLabels m k
    atomInputs := fun _ hlabels ↦
      Classical.choice (yPrimedCanonicalGoodLabels_nonempty_input hlabels)
    cover := h.primed_cover }

noncomputable def
    YSourceOriginCanonicalLabelSeparateAtomizations.toFixedDepth
    {m k : ℕ}
    (h : YSourceOriginCanonicalLabelSeparateAtomizations m k) :
    YSourceOriginCanonicalFixedDepthSeparateAtomizations m k where
  unprimed := h.unprimed.toFixedDepth
  primed := h.primed.toFixedDepth

noncomputable def
    YSourceOriginCanonicalFixedDepthSeparateAtomizations.toCanonicalHorizon
    {m k : ℕ}
    (h : YSourceOriginCanonicalFixedDepthSeparateAtomizations m k) :
    YSourceOriginCanonicalHorizonSeparateAtomizations m k where
  unprimed := h.unprimed.toCanonicalHorizon
  primed := h.primed.toCanonicalHorizon

noncomputable def
    YSourceOriginCanonicalHorizonSeparateAtomizations.toOrigin
    {m k : ℕ}
    (h : YSourceOriginCanonicalHorizonSeparateAtomizations m k)
    (hHorizon : simpleRandomWalkLaw
        (HLOZProp47Prop45XEastPrimed.xEastCanonicalHorizonEvent m k)ᶜ ≤
      sourceExceptionalRateWithPrefactor m 1 kappa) :
    YSourceOriginTerminalSeparateFiniteAtomizations m k 1 1 where
  unprimed := h.unprimed.toOrigin hHorizon
  primed := h.primed.toOrigin hHorizon

noncomputable def
    YSourceOriginTerminalSeparateFiniteAtomizations.toLiteral
    {m k unprimedBadCoeff primedBadCoeff : ℕ}
    (h : YSourceOriginTerminalSeparateFiniteAtomizations
      m k unprimedBadCoeff primedBadCoeff) :
    YSourceLiteralTerminalSeparateFiniteAtomizations
      m k unprimedBadCoeff primedBadCoeff where
  unprimed := h.unprimed.toLiteral
  primed := h.primed.toLiteral

noncomputable def
    YSourceLiteralTerminalSeparateFiniteAtomizations.toInitial
    {m k unprimedBadCoeff primedBadCoeff : ℕ}
    (h : YSourceLiteralTerminalSeparateFiniteAtomizations
      m k unprimedBadCoeff primedBadCoeff) :
    YSourceInitialCanonicalTerminalSeparateFiniteAtomizations
      m k unprimedBadCoeff primedBadCoeff where
  unprimed := h.unprimed.toInitial
  primed := h.primed.toInitial

noncomputable def
    YSourceInitialCanonicalTerminalSeparateFiniteAtomizations.toCanonical
    {m k unprimedBadCoeff primedBadCoeff : ℕ}
    (h : YSourceInitialCanonicalTerminalSeparateFiniteAtomizations
      m k unprimedBadCoeff primedBadCoeff)
    (hdepth :
      (HLOZExternalUpper.externalLabelCount
        (HLOZProp44.prop44Psi m) : ℝ) ≤
          Real.exp (16 * Real.sqrt (m : ℝ))) :
    YSourceCanonicalTerminalSeparateFiniteAtomizations
      m k unprimedBadCoeff primedBadCoeff where
  unprimed := h.unprimed.toCanonical hdepth
  primed := h.primed.toCanonical hdepth

noncomputable def
    YSourceCanonicalTerminalSeparateFiniteAtomizations.toTerminal
    {m k unprimedBadCoeff primedBadCoeff : ℕ}
    (h : YSourceCanonicalTerminalSeparateFiniteAtomizations m k
      unprimedBadCoeff primedBadCoeff) :
    YSourceTerminalSeparateFiniteAtomizations m k
      unprimedBadCoeff primedBadCoeff where
  unprimed := h.unprimed.toTerminalFiniteAtomization
  primed := h.primed.toTerminalFiniteAtomization

noncomputable def
    YSourceTerminalSeparateFiniteAtomizations.toSourceSeparateFiniteAtomizations
    {m k unprimedBadCoeff primedBadCoeff : ℕ}
    (h : YSourceTerminalSeparateFiniteAtomizations m k
      unprimedBadCoeff primedBadCoeff) :
    YSourceSeparateFiniteAtomizations m k
      unprimedBadCoeff primedBadCoeff where
  unprimed := h.unprimed.toPhaseFiniteAtomization
  primed := h.primed.toPhaseFiniteAtomization

theorem YSeparateFiniteAtomizations.theta_measure_le
    {m k unprimedBadCoeff primedBadCoeff : ℕ}
    (hs : SourceIntervalScale m (sourceBandLowerNat m) ∧
      SourceUpperScale m m)
    (habsorb : sourceProp45OneSideError m ≤
      sourceExceptionalRateWithPrefactor m 3 kappa)
    (h : YSeparateFiniteAtomizations m k
      unprimedBadCoeff primedBadCoeff) :
    simpleRandomWalkLaw
        (stoppedThetaEvent (canonicalProfiles ⟨4, by omega⟩)
          (canonicalCStar ⟨4, by omega⟩) m k) ≤
      sourceExceptionalRateWithPrefactor m
        (unprimedBadCoeff + primedBadCoeff + 6) kappa := by
  rw [stoppedThetaEvent_y_eq]
  calc
    simpleRandomWalkLaw
        (yUnprimedThetaEvent m k ∪ yPrimedThetaEvent m k) ≤
      simpleRandomWalkLaw (yUnprimedThetaEvent m k) +
        simpleRandomWalkLaw (yPrimedThetaEvent m k) := measure_union_le _ _
    _ ≤ sourceExceptionalRateWithPrefactor m (unprimedBadCoeff + 3) kappa +
        sourceExceptionalRateWithPrefactor m (primedBadCoeff + 3) kappa :=
      add_le_add (h.unprimed.theta_measure_le hs habsorb)
        (h.primed.theta_measure_le hs habsorb)
    _ = sourceExceptionalRateWithPrefactor m
        (unprimedBadCoeff + primedBadCoeff + 6) kappa := by
      simp only [sourceExceptionalRateWithPrefactor]
      push_cast
      ring

theorem YSourceSeparateFiniteAtomizations.source_measure_le
    {m k unprimedBadCoeff primedBadCoeff : ℕ}
    (hs : SourceIntervalScale m (sourceBandLowerNat m) ∧
      SourceUpperScale m m)
    (habsorb : sourceProp45OneSideError m ≤
      sourceExceptionalRateWithPrefactor m 3 kappa)
    (h : YSourceSeparateFiniteAtomizations m k
      unprimedBadCoeff primedBadCoeff) :
    simpleRandomWalkLaw
        (prefixPairingEvent m ⟨4, by omega⟩ (k + 1) ∩
          stoppedThetaEvent (canonicalProfiles ⟨4, by omega⟩)
            (canonicalCStar ⟨4, by omega⟩) m k) ≤
      sourceExceptionalRateWithPrefactor m
        (unprimedBadCoeff + primedBadCoeff + 6) kappa := by
  rw [prefixPairing_inter_stoppedThetaEvent_y_eq]
  calc
    simpleRandomWalkLaw
        (yUnprimedSourceEvent m k ∪ yPrimedSourceEvent m k) ≤
      simpleRandomWalkLaw (yUnprimedSourceEvent m k) +
        simpleRandomWalkLaw (yPrimedSourceEvent m k) := measure_union_le _ _
    _ ≤ sourceExceptionalRateWithPrefactor m (unprimedBadCoeff + 3) kappa +
        sourceExceptionalRateWithPrefactor m (primedBadCoeff + 3) kappa :=
      add_le_add (h.unprimed.theta_measure_le hs habsorb)
        (h.primed.theta_measure_le hs habsorb)
    _ = sourceExceptionalRateWithPrefactor m
        (unprimedBadCoeff + primedBadCoeff + 6) kappa := by
      simp only [sourceExceptionalRateWithPrefactor]
      push_cast
      ring

def HasYBareThetaSeparateFiniteAtomizations
    (unprimedBadCoeff primedBadCoeff : ℕ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
    Nonempty (YSeparateFiniteAtomizations m (stageNumber r)
      unprimedBadCoeff primedBadCoeff)

def HasYSeparateFiniteAtomizations
    (unprimedBadCoeff primedBadCoeff : ℕ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
    Nonempty (YSourceSeparateFiniteAtomizations m (stageNumber r)
      unprimedBadCoeff primedBadCoeff)

def HasYTerminalSeparateFiniteAtomizations
    (unprimedBadCoeff primedBadCoeff : ℕ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
    Nonempty (YSourceTerminalSeparateFiniteAtomizations m (stageNumber r)
      unprimedBadCoeff primedBadCoeff)

def HasYCanonicalTerminalSeparateFiniteAtomizations
    (unprimedBadCoeff primedBadCoeff : ℕ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
    Nonempty (YSourceCanonicalTerminalSeparateFiniteAtomizations
      m (stageNumber r) unprimedBadCoeff primedBadCoeff)

def HasYInitialCanonicalTerminalSeparateFiniteAtomizations
    (unprimedBadCoeff primedBadCoeff : ℕ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
    Nonempty (YSourceInitialCanonicalTerminalSeparateFiniteAtomizations
      m (stageNumber r) unprimedBadCoeff primedBadCoeff)

def HasYLiteralTerminalSeparateFiniteAtomizations
    (unprimedBadCoeff primedBadCoeff : ℕ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
    Nonempty (YSourceLiteralTerminalSeparateFiniteAtomizations
      m (stageNumber r) unprimedBadCoeff primedBadCoeff)

/-- Eventual origin-started literal terminal atomizations for both column
phases.  This is the terminal-column premise consumed by the final literal
source closure. -/
def HasYOriginTerminalSeparateFiniteAtomizations
    (unprimedBadCoeff primedBadCoeff : ℕ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
    Nonempty (YSourceOriginTerminalSeparateFiniteAtomizations
      m (stageNumber r) unprimedBadCoeff primedBadCoeff)

/-- Eventual literal terminal-column atomizations on the canonical
near-critical horizon. -/
def HasYOriginCanonicalHorizonSeparateAtomizations : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
    Nonempty (YSourceOriginCanonicalHorizonSeparateAtomizations
      m (stageNumber r))

/-- Eventual origin-started atomizations at the canonical fixed label
depth.  Pairwise disjointness is derived from parser uniqueness. -/
def HasYOriginCanonicalFixedDepthSeparateAtomizations : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
    Nonempty (YSourceOriginCanonicalFixedDepthSeparateAtomizations
      m (stageNumber r))

/-- Eventual canonical column atomizations indexed by literal label
vectors themselves.  Unlike the fixed-depth numeric wrapper, this carries
no arbitrary indexing or injectivity premise. -/
def HasYOriginCanonicalLabelSeparateAtomizations : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
    Nonempty (YSourceOriginCanonicalLabelSeparateAtomizations
      m (stageNumber r))

/-- Eventual coverage by the canonical good-label sets for the auxiliary
adaptive-parser route. -/
def HasYOriginCanonicalGoodLabelCovers : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
    Nonempty (YSourceOriginCanonicalGoodLabelCovers m (stageNumber r))

/-- Within the auxiliary parser model, an honest replacement for a pathwise
all-good cover: paths not captured by a canonical good label form an explicit
exceptional event, whose Proposition-4.4-scale probability bound is assumed. -/
structure YSourceOriginCanonicalGoodLabelFailureBounds (m k : ℕ) where
  unprimed : simpleRandomWalkLaw
      (yForwardCanonicalGoodLabelFailureEvent m k) ≤
    sourceExceptionalRateWithPrefactor m 1 kappa
  primed : simpleRandomWalkLaw
      (yPrimedCanonicalGoodLabelFailureEvent m k) ≤
    sourceExceptionalRateWithPrefactor m 1 kappa

def HasYOriginCanonicalGoodLabelFailureBounds : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
    Nonempty (YSourceOriginCanonicalGoodLabelFailureBounds
      m (stageNumber r))

/-- Parser-complete form of the Y residual.  Invalid terminal parsing has
probability zero by the fixed-depth normalization above, so the only events
left here consist of valid labels missing some local Proposition-4.4 or
stopped-clock datum. -/
structure YSourceOriginCanonicalBadDataFailureBounds (m k : ℕ) where
  unprimed : simpleRandomWalkLaw
      (yForwardCanonicalBadDataFailureEvent m k) ≤
    sourceExceptionalRateWithPrefactor m 1 kappa
  primed : simpleRandomWalkLaw
      (yPrimedCanonicalBadDataFailureEvent m k) ≤
    sourceExceptionalRateWithPrefactor m 1 kappa

def HasYOriginCanonicalBadDataFailureBounds : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
    Nonempty (YSourceOriginCanonicalBadDataFailureBounds
      m (stageNumber r))

theorem hasYOriginCanonicalGoodLabelFailureBounds_of_badData
    (h : HasYOriginCanonicalBadDataFailureBounds) :
    HasYOriginCanonicalGoodLabelFailureBounds := by
  filter_upwards [h] with m hm
  intro r
  rcases hm r with ⟨hbad⟩
  exact ⟨{
    unprimed := by
      rw [simpleRandomWalkLaw_yForwardGoodLabelFailure_eq_badDataFailure]
      exact hbad.unprimed
    primed := by
      rw [simpleRandomWalkLaw_yPrimedGoodLabelFailure_eq_badDataFailure]
      exact hbad.primed }⟩

theorem hasYOriginTerminalSeparateFiniteAtomizations_of_goodLabelFailure
    (hdisk : HLOZProp13FromAppendix.AppendixDiskEstimate)
    (h : HasYOriginCanonicalGoodLabelFailureBounds) :
    HasYOriginTerminalSeparateFiniteAtomizations 2 2 := by
  filter_upwards [h,
    HLOZProp47Prop45XEastPrimed.eventually_xEastCanonicalHorizon_compl_measure_le
      hdisk]
    with m hm hHorizon
  intro r
  rcases hm r with ⟨hFailure⟩
  exact ⟨{
    unprimed := yForwardOriginAtomization_of_goodLabelFailure
      (hHorizon (stageNumber r)) hFailure.unprimed
    primed := yPrimedOriginAtomization_of_goodLabelFailure
      (hHorizon (stageNumber r)) hFailure.primed }⟩

theorem hasYOriginTerminalSeparateFiniteAtomizations_of_badDataFailure
    (hdisk : HLOZProp13FromAppendix.AppendixDiskEstimate)
    (h : HasYOriginCanonicalBadDataFailureBounds) :
    HasYOriginTerminalSeparateFiniteAtomizations 2 2 :=
  hasYOriginTerminalSeparateFiniteAtomizations_of_goodLabelFailure hdisk
    (hasYOriginCanonicalGoodLabelFailureBounds_of_badData h)

theorem hasYOriginCanonicalLabelSeparateAtomizations_of_goodLabelCovers
    (h : HasYOriginCanonicalGoodLabelCovers) :
    HasYOriginCanonicalLabelSeparateAtomizations := by
  filter_upwards [h] with m hm
  intro r
  rcases hm r with ⟨covers⟩
  exact ⟨covers.toLabelAtomizations⟩

theorem hasYOriginCanonicalFixedDepthSeparateAtomizations_of_labels
    (h : HasYOriginCanonicalLabelSeparateAtomizations) :
    HasYOriginCanonicalFixedDepthSeparateAtomizations := by
  filter_upwards [h] with m hm
  intro r
  rcases hm r with ⟨atoms⟩
  exact ⟨atoms.toFixedDepth⟩

theorem hasYOriginCanonicalHorizonSeparateAtomizations_of_fixedDepth
    (h : HasYOriginCanonicalFixedDepthSeparateAtomizations) :
    HasYOriginCanonicalHorizonSeparateAtomizations := by
  filter_upwards [h] with m hm
  intro r
  rcases hm r with ⟨atoms⟩
  exact ⟨atoms.toCanonicalHorizon⟩

theorem hasYOriginTerminalSeparateFiniteAtomizations_of_canonicalHorizon
    (hdisk : HLOZProp13FromAppendix.AppendixDiskEstimate)
    (h : HasYOriginCanonicalHorizonSeparateAtomizations) :
    HasYOriginTerminalSeparateFiniteAtomizations 1 1 := by
  filter_upwards [h,
    HLOZProp47Prop45XEastPrimed.eventually_xEastCanonicalHorizon_compl_measure_le
      hdisk]
    with m hm hHorizon
  intro r
  rcases hm r with ⟨atoms⟩
  exact ⟨atoms.toOrigin (hHorizon (stageNumber r))⟩

theorem hasYLiteralTerminalSeparateFiniteAtomizations_of_origin
    {unprimedBadCoeff primedBadCoeff : ℕ}
    (h : HasYOriginTerminalSeparateFiniteAtomizations
      unprimedBadCoeff primedBadCoeff) :
    HasYLiteralTerminalSeparateFiniteAtomizations
      unprimedBadCoeff primedBadCoeff := by
  filter_upwards [h] with m hm
  intro r
  rcases hm r with ⟨atoms⟩
  exact ⟨atoms.toLiteral⟩

theorem hasYInitialCanonicalTerminalSeparateFiniteAtomizations_of_literal
    {unprimedBadCoeff primedBadCoeff : ℕ}
    (h : HasYLiteralTerminalSeparateFiniteAtomizations
      unprimedBadCoeff primedBadCoeff) :
    HasYInitialCanonicalTerminalSeparateFiniteAtomizations
      unprimedBadCoeff primedBadCoeff := by
  filter_upwards [h] with m hm
  intro r
  rcases hm r with ⟨atoms⟩
  exact ⟨atoms.toInitial⟩

theorem hasYCanonicalTerminalSeparateFiniteAtomizations_of_initial
    {unprimedBadCoeff primedBadCoeff : ℕ}
    (h : HasYInitialCanonicalTerminalSeparateFiniteAtomizations
      unprimedBadCoeff primedBadCoeff) :
    HasYCanonicalTerminalSeparateFiniteAtomizations
      unprimedBadCoeff primedBadCoeff := by
  filter_upwards [h,
    HLOZProp44ExternalChain.eventually_externalLabelCount_prop44Psi_le_exp_sixteen_sqrt]
    with m hm hdepth
  intro r
  rcases hm r with ⟨atoms⟩
  exact ⟨atoms.toCanonical hdepth⟩

theorem hasYTerminalSeparateFiniteAtomizations_of_canonical
    {unprimedBadCoeff primedBadCoeff : ℕ}
    (h : HasYCanonicalTerminalSeparateFiniteAtomizations
      unprimedBadCoeff primedBadCoeff) :
    HasYTerminalSeparateFiniteAtomizations
      unprimedBadCoeff primedBadCoeff := by
  filter_upwards [h] with m hm
  intro r
  rcases hm r with ⟨atoms⟩
  exact ⟨atoms.toTerminal⟩

theorem hasYSeparateFiniteAtomizations_of_terminal
    {unprimedBadCoeff primedBadCoeff : ℕ}
    (h : HasYTerminalSeparateFiniteAtomizations
      unprimedBadCoeff primedBadCoeff) :
    HasYSeparateFiniteAtomizations unprimedBadCoeff primedBadCoeff := by
  filter_upwards [h] with m hm
  intro r
  rcases hm r with ⟨atoms⟩
  exact ⟨atoms.toSourceSeparateFiniteAtomizations⟩

theorem y_stoppedThetaEstimate_of_separateAtomizations
    {unprimedBadCoeff primedBadCoeff : ℕ}
    (hatoms : HasYBareThetaSeparateFiniteAtomizations
      unprimedBadCoeff primedBadCoeff) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
      simpleRandomWalkLaw
          (stoppedThetaEvent (canonicalProfiles ⟨4, by omega⟩)
            (canonicalCStar ⟨4, by omega⟩) m (stageNumber r)) ≤
        sourceExceptionalRateWithPrefactor m
          (unprimedBadCoeff + primedBadCoeff + 6) kappa := by
  filter_upwards [hatoms, eventually_sourceEndpointScales,
    eventually_sourceProp45OneSideError_le] with m hatoms hs habsorb
  intro r
  rcases hatoms r with ⟨hatom⟩
  exact hatom.theta_measure_le hs habsorb

/-! ### Origin-fixing reflection from `Y` to `Y'` -/

theorem localTime_reflectPath (s : Path) (n : ℕ) (x : Site) :
    localTime (reflectPath s) n (reflectSite x) = localTime s n x := by
  unfold localTime reflectPath
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter]
  exact and_congr_right fun _ ↦ reflectSite_injective.eq_iff

theorem visitedSites_reflectPath (s : Path) (n : ℕ) :
    visitedSites (reflectPath s) n =
      (visitedSites s n).image reflectSite := by
  unfold visitedSites reflectPath
  rw [Finset.image_image]
  rfl

theorem sitesAtLeastLevel_reflectPath (s : Path) (n m : ℕ) :
    sitesAtLeastLevel (reflectPath s) n m =
      (sitesAtLeastLevel s n m).image reflectSite := by
  ext y
  rw [sitesAtLeastLevel, sitesAtLeastLevel, visitedSites_reflectPath]
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hm⟩
    exact ⟨x, ⟨hx, by simpa only [localTime_reflectPath] using hm⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hm⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, by simpa only [localTime_reflectPath] using hm⟩

theorem card_sitesAtLeastLevel_reflectPath (s : Path) (n m : ℕ) :
    (sitesAtLeastLevel (reflectPath s) n m).card =
      (sitesAtLeastLevel s n m).card := by
  rw [sitesAtLeastLevel_reflectPath]
  exact Finset.card_image_of_injective _ reflectSite_injective

theorem firstKSitesReachLevel_reflectPath (s : Path) (m k : ℕ) :
    firstKSitesReachLevel m k (reflectPath s) =
      firstKSitesReachLevel m k s := by
  have heq (j : ℕ) :
      (sitesAtLeastLevel (reflectPath s) j m).card =
        (sitesAtLeastLevel s j m).card :=
    card_sitesAtLeastLevel_reflectPath s j m
  unfold firstKSitesReachLevel hittingAfter
  by_cases h : ∃ j, 0 ≤ j ∧ (sitesAtLeastLevel s j m).card ∈ Set.Ici k
  · have hr : ∃ j, 0 ≤ j ∧
        (sitesAtLeastLevel (reflectPath s) j m).card ∈ Set.Ici k := by
      simpa only [heq] using h
    simp only [hr, h, if_true, heq]
  · have hr : ¬ ∃ j, 0 ≤ j ∧
        (sitesAtLeastLevel (reflectPath s) j m).card ∈ Set.Ici k := by
      simpa only [heq] using h
    simp only [hr, h, if_false]

theorem levelCreationSite_reflectPath (s : Path) (m k : ℕ) :
    levelCreationSite (reflectPath s) m k =
      reflectSite (levelCreationSite s m k) := by
  unfold levelCreationSite
  change reflectSite
      (s (firstKSitesReachLevel m k (reflectPath s)).untopA) =
    reflectSite (s (firstKSitesReachLevel m k s).untopA)
  rw [firstKSitesReachLevel_reflectPath]

theorem levelCreationSitesUpTo_reflectPath (s : Path) (m k : ℕ) :
    levelCreationSitesUpTo (reflectPath s) m k =
      (levelCreationSitesUpTo s m k).image reflectSite := by
  unfold levelCreationSitesUpTo
  rw [Finset.image_image]
  apply Finset.image_congr
  intro j hj
  exact levelCreationSite_reflectPath s m j

/-- Reflection in the vertical axis sends the even-left column tiling to
the odd-left tiling. -/
theorem yPair_reflect_iff (x y : Site) :
    YPair' (reflectSite x) (reflectSite y) ↔ YPair x y := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  simp only [YPair', YPair, reflectSite, shift, vec, east,
    Matrix.cons_val_zero]
  constructor
  · rintro (⟨hyodd, heq⟩ | ⟨hxodd, heq⟩)
    · right
      refine ⟨?_, ?_⟩
      · rcases hyodd with ⟨z, hz⟩
        simp only [Prod.mk.injEq] at heq
        refine ⟨-z - 1, ?_⟩
        omega
      · simp only [Prod.mk.injEq] at heq ⊢
        omega
    · left
      refine ⟨?_, ?_⟩
      · rcases hxodd with ⟨z, hz⟩
        simp only [Prod.mk.injEq] at heq
        refine ⟨-z - 1, ?_⟩
        omega
      · simp only [Prod.mk.injEq] at heq ⊢
        omega
  · rintro (⟨hxeven, heq⟩ | ⟨hyeven, heq⟩)
    · right
      refine ⟨?_, ?_⟩
      · rcases hxeven with ⟨z, hz⟩
        simp only [Prod.mk.injEq] at heq
        refine ⟨-z - 1, ?_⟩
        omega
      · simp only [Prod.mk.injEq] at heq ⊢
        omega
    · left
      refine ⟨?_, ?_⟩
      · rcases hyeven with ⟨z, hz⟩
        simp only [Prod.mk.injEq] at heq
        refine ⟨-z - 1, ?_⟩
        omega
      · simp only [Prod.mk.injEq] at heq ⊢
        omega

theorem pairFree_y_reflect_iff (A : Finset Site) :
    PairFree YPair' (A.image reflectSite) ↔ PairFree YPair A := by
  constructor
  · intro h x hx y hy hxy hpair
    exact h (reflectSite x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      (reflectSite y) (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
      (fun heq ↦ hxy (reflectSite_injective heq))
      ((yPair_reflect_iff x y).2 hpair)
  · intro h x hx y hy hxy hpair
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨b, hb, hab⟩
    subst y
    apply h a ha b hb
    · intro heq
      exact hxy (congrArg reflectSite heq)
    · exact (yPair_reflect_iff a b).1 hpair

theorem prefixPairingEvent_y_reflect_iff (s : Path) (m k : ℕ) :
    reflectPath s ∈ prefixPairingEvent m ⟨5, by omega⟩ k ↔
      s ∈ prefixPairingEvent m ⟨4, by omega⟩ k := by
  rw [prefixPairingEvent, prefixPairingEvent]
  constructor
  · rintro ⟨htime, hfree⟩
    refine ⟨?_, ?_⟩
    · change firstKSitesReachLevel m k s <
        firstKSitesReachLevel (m + 1) 1 s
      change firstKSitesReachLevel m k (reflectPath s) <
        firstKSitesReachLevel (m + 1) 1 (reflectPath s) at htime
      simpa only [firstKSitesReachLevel_reflectPath] using htime
    · change PairFree YPair'
        (levelCreationSitesUpTo (reflectPath s) m k) at hfree
      change PairFree YPair' _ at hfree
      rw [levelCreationSitesUpTo_reflectPath] at hfree
      exact (pairFree_y_reflect_iff _).1 hfree
  · rintro ⟨htime, hfree⟩
    refine ⟨?_, ?_⟩
    · change firstKSitesReachLevel m k s <
        firstKSitesReachLevel (m + 1) 1 s at htime
      change firstKSitesReachLevel m k (reflectPath s) <
        firstKSitesReachLevel (m + 1) 1 (reflectPath s)
      simpa only [firstKSitesReachLevel_reflectPath] using htime
    · change PairFree YPair (levelCreationSitesUpTo s m k) at hfree
      change PairFree YPair' _
      rw [levelCreationSitesUpTo_reflectPath]
      exact (pairFree_y_reflect_iff _).2 hfree

theorem directCreationTime_reflectPath (s : Path) (m k : ℕ) :
    directCreationTime m k (reflectPath s) = directCreationTime m k s := by
  unfold directCreationTime
  rw [firstKSitesReachLevel_reflectPath]

theorem reflectSite_surjective : Function.Surjective reflectSite := by
  intro y
  exact ⟨reflectSite y, by
    rcases y with ⟨y₁, y₂⟩
    simp [reflectSite]⟩

theorem mem_stoppedThetaHalfSites_y_reflect
    (forward upper : Bool) (cStar : ℝ)
    (s : Path) (m k : ℕ) (x : Site) :
    reflectSite x ∈ stoppedThetaHalfSites
        (deletionExternalLocalTime yDeletion' (!forward))
        (if !forward then yDeletion'.distinguished
          else fun y ↦ ¬ yDeletion'.distinguished y)
        upper cStar (reflectPath s) m k ↔
      x ∈ stoppedThetaHalfSites
        (deletionExternalLocalTime yDeletion forward)
        (if forward then yDeletion.distinguished
          else fun y ↦ ¬ yDeletion.distinguished y)
        upper cStar s m k := by
  simp only [stoppedThetaHalfSites, Finset.mem_filter,
    directCreationTime_reflectPath, firstKSitesReachLevel_reflectPath]
  have hvisited : reflectSite x ∈
      (visitedSites s (directCreationTime m k s)).image reflectSite ↔
      x ∈ visitedSites s (directCreationTime m k s) := by
    constructor
    · intro hmem
      obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hmem
      exact (reflectSite_injective hxy).symm ▸ hy
    · intro hx
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  rw [visitedSites_reflectPath, hvisited, localTime_reflectPath,
    deletionExternalLocalTime_y_reflect]
  cases forward
  · simp only [Bool.not_false, if_true, Bool.false_eq_true, if_false,
      yDeletion, yDeletion', odd_reflectSite]
    rw [Int.not_even_iff_odd]
  · simp only [Bool.not_true, Bool.false_eq_true, if_false, if_true,
      yDeletion, yDeletion', odd_reflectSite]
    rw [Int.not_odd_iff_even]

theorem nonempty_stoppedThetaHalfSites_y_reflect
    (forward upper : Bool) (cStar : ℝ) (s : Path) (m k : ℕ) :
    (stoppedThetaHalfSites
      (deletionExternalLocalTime yDeletion forward)
      (if forward then yDeletion.distinguished
        else fun y ↦ ¬ yDeletion.distinguished y)
      upper cStar s m k).Nonempty ↔
    (stoppedThetaHalfSites
      (deletionExternalLocalTime yDeletion' (!forward))
      (if !forward then yDeletion'.distinguished
        else fun y ↦ ¬ yDeletion'.distinguished y)
      upper cStar (reflectPath s) m k).Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨reflectSite x,
      (mem_stoppedThetaHalfSites_y_reflect
        forward upper cStar s m k x).2 hx⟩
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := reflectSite_surjective y
    exact ⟨x, (mem_stoppedThetaHalfSites_y_reflect
      forward upper cStar s m k x).1 hy⟩

theorem stoppedThetaEvent_y_reflect_iff
    (cStar : ℝ) (s : Path) (m k : ℕ) :
    s ∈ stoppedThetaEvent (deletionProfilePair yDeletion) cStar m k ↔
      reflectPath s ∈
        stoppedThetaEvent (deletionProfilePair yDeletion') cStar m k := by
  have h₀ := nonempty_stoppedThetaHalfSites_y_reflect
    true false cStar s m k
  have h₁ := nonempty_stoppedThetaHalfSites_y_reflect
    true true cStar s m k
  have h₂ := nonempty_stoppedThetaHalfSites_y_reflect
    false false cStar s m k
  have h₃ := nonempty_stoppedThetaHalfSites_y_reflect
    false true cStar s m k
  simp only [Bool.not_true, Bool.false_eq_true, if_false, if_true] at h₀ h₁
  simp only [Bool.not_false, Bool.true_eq, if_true, if_false] at h₂ h₃
  simp only [stoppedThetaEvent, Set.mem_setOf_eq, stoppedThetaSites,
    deletionProfilePair, Finset.union_nonempty]
  constructor
  · rintro (((hx | hx) | hx) | hx)
    · exact Or.inl (Or.inr (h₀.mp hx))
    · exact Or.inr (h₁.mp hx)
    · exact Or.inl (Or.inl (Or.inl (h₂.mp hx)))
    · exact Or.inl (Or.inl (Or.inr (h₃.mp hx)))
  · rintro (((hx | hx) | hx) | hx)
    · exact Or.inl (Or.inr (h₂.mpr hx))
    · exact Or.inr (h₃.mpr hx)
    · exact Or.inl (Or.inl (Or.inl (h₀.mpr hx)))
    · exact Or.inl (Or.inl (Or.inr (h₁.mpr hx)))

/-- Source-correct reflection bridge.  The pairing-history factor is
transported together with the stopped imbalance event. -/
theorem prefixPairingThetaEvent_y_reflect_iff
    (s : Path) (m k : ℕ) :
    s ∈ prefixPairingEvent m ⟨4, by omega⟩ (k + 1) ∩
        stoppedThetaEvent (deletionProfilePair yDeletion) 10 m k ↔
      reflectPath s ∈ prefixPairingEvent m ⟨5, by omega⟩ (k + 1) ∩
        stoppedThetaEvent (deletionProfilePair yDeletion') 10 m k := by
  exact and_congr
    (prefixPairingEvent_y_reflect_iff s m (k + 1)).symm
    (stoppedThetaEvent_y_reflect_iff 10 s m k)

theorem measurable_reflectPath : Measurable reflectPath := by
  apply measurable_pi_lambda
  intro n
  exact (measurable_of_countable reflectSite).comp (measurable_pi_apply n)

theorem measurable_reflectIncrements : Measurable reflectIncrements := by
  apply measurable_pi_lambda
  intro n
  exact (measurable_from_top : Measurable reflectDirection).comp
    (measurable_pi_apply n)

theorem simpleRandomWalkLaw_map_reflectPath :
    simpleRandomWalkLaw.map reflectPath = simpleRandomWalkLaw := by
  unfold simpleRandomWalkLaw
  calc
    Measure.map reflectPath (Measure.map simpleRandomWalk incrementLaw) =
        Measure.map (reflectPath ∘ simpleRandomWalk) incrementLaw :=
      Measure.map_map measurable_reflectPath measurable_simpleRandomWalk
    _ = Measure.map (simpleRandomWalk ∘ reflectIncrements) incrementLaw := by
      apply Measure.map_congr
      filter_upwards [] with ω
      funext n
      exact (simpleRandomWalk_reflectIncrements ω n).symm
    _ = Measure.map simpleRandomWalk
        (Measure.map reflectIncrements incrementLaw) :=
      (Measure.map_map measurable_simpleRandomWalk
        measurable_reflectIncrements).symm
    _ = Measure.map simpleRandomWalk incrementLaw := by
      rw [incrementLaw_map_reflectIncrements]

theorem simpleRandomWalkLaw_stoppedThetaEvent_y'_eq_y
    (cStar : ℝ) (m k : ℕ) :
    simpleRandomWalkLaw
        (stoppedThetaEvent (deletionProfilePair yDeletion') cStar m k) =
      simpleRandomWalkLaw
        (stoppedThetaEvent (deletionProfilePair yDeletion) cStar m k) := by
  let E := stoppedThetaEvent (deletionProfilePair yDeletion') cStar m k
  have hE : MeasurableSet E := measurableSet_stoppedThetaEvent _ _ _ _
  calc
    simpleRandomWalkLaw E = (simpleRandomWalkLaw.map reflectPath) E := by
      rw [simpleRandomWalkLaw_map_reflectPath]
    _ = simpleRandomWalkLaw (reflectPath ⁻¹' E) :=
      Measure.map_apply measurable_reflectPath hE
    _ = simpleRandomWalkLaw
        (stoppedThetaEvent (deletionProfilePair yDeletion) cStar m k) := by
      congr 1
      ext s
      exact (stoppedThetaEvent_y_reflect_iff cStar s m k).symm

theorem simpleRandomWalkLaw_prefixPairingThetaEvent_y'_eq_y
    (m k : ℕ) :
    simpleRandomWalkLaw
        (prefixPairingEvent m ⟨5, by omega⟩ (k + 1) ∩
          stoppedThetaEvent (deletionProfilePair yDeletion') 10 m k) =
      simpleRandomWalkLaw
        (prefixPairingEvent m ⟨4, by omega⟩ (k + 1) ∩
          stoppedThetaEvent (deletionProfilePair yDeletion) 10 m k) := by
  let E := prefixPairingEvent m ⟨5, by omega⟩ (k + 1) ∩
    stoppedThetaEvent (deletionProfilePair yDeletion') 10 m k
  have hE : MeasurableSet E :=
    (measurableSet_prefixPairingEvent m ⟨5, by omega⟩ (k + 1)).inter
      (measurableSet_stoppedThetaEvent _ _ _ _)
  calc
    simpleRandomWalkLaw E = (simpleRandomWalkLaw.map reflectPath) E := by
      rw [simpleRandomWalkLaw_map_reflectPath]
    _ = simpleRandomWalkLaw (reflectPath ⁻¹' E) :=
      Measure.map_apply measurable_reflectPath hE
    _ = simpleRandomWalkLaw
        (prefixPairingEvent m ⟨4, by omega⟩ (k + 1) ∩
          stoppedThetaEvent (deletionProfilePair yDeletion) 10 m k) := by
      congr 1
      ext s
      exact (prefixPairingThetaEvent_y_reflect_iff s m k).symm

theorem stoppedThetaEvent_y'_le_of_y (m k : ℕ) (R : ℝ≥0∞)
    (hY : simpleRandomWalkLaw
      (stoppedThetaEvent (canonicalProfiles ⟨4, by omega⟩)
        (canonicalCStar ⟨4, by omega⟩) m k) ≤ R) :
    simpleRandomWalkLaw
      (stoppedThetaEvent (canonicalProfiles ⟨5, by omega⟩)
        (canonicalCStar ⟨5, by omega⟩) m k) ≤ R := by
  rw [show canonicalProfiles ⟨5, by omega⟩ =
      deletionProfilePair yDeletion' by rfl,
    show canonicalCStar ⟨5, by omega⟩ = 10 by rfl,
    simpleRandomWalkLaw_stoppedThetaEvent_y'_eq_y]
  simpa only [canonicalProfiles, pairingProfiles, pairingDeletion,
    canonicalCStar] using hY

theorem prefixPairingThetaEvent_y'_le_of_y (m k : ℕ) (R : ℝ≥0∞)
    (hY : simpleRandomWalkLaw
      (prefixPairingEvent m ⟨4, by omega⟩ (k + 1) ∩
        stoppedThetaEvent (canonicalProfiles ⟨4, by omega⟩)
          (canonicalCStar ⟨4, by omega⟩) m k) ≤ R) :
    simpleRandomWalkLaw
      (prefixPairingEvent m ⟨5, by omega⟩ (k + 1) ∩
        stoppedThetaEvent (canonicalProfiles ⟨5, by omega⟩)
          (canonicalCStar ⟨5, by omega⟩) m k) ≤ R := by
  rw [show canonicalProfiles ⟨5, by omega⟩ =
      deletionProfilePair yDeletion' by rfl,
    show canonicalCStar ⟨5, by omega⟩ = 10 by rfl,
    simpleRandomWalkLaw_prefixPairingThetaEvent_y'_eq_y]
  simpa only [canonicalProfiles, pairingProfiles, pairingDeletion,
    canonicalCStar] using hY

/-- The exact unresolved Proposition-4.5 estimate for the two formal column
indices.  Keeping this as a direct event estimate avoids treating the
fixed-pair adaptive parser below as a source identification: the parser is a
checked sufficient route to this predicate, while a literal reading of HLOZ
(2.12) still requires a separate temporal-parity/column-tiling connector. -/
def Prop47Prop45YColumnsEstimate (badCoeff : ℕ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i : Fin 6, 4 ≤ i.1 →
    ∀ r : StageIndex, ∀ a : AlphaIndex, alphaValue a ≤ kappaTwo →
    simpleRandomWalkLaw
        (prop45FailureEvent canonicalProfiles canonicalCStar m i r
          (alphaValue a)) ≤
      sourceExceptionalRateWithPrefactor m badCoeff kappa

/-- Literal temporal-deletion estimate for the two column tilings.  The
fixed-label X₁ atomization already bounds the larger event obtained by
discarding `PairFree`; hence no endpoint-adapted column parser is needed.
This is the direct formal counterpart of HLOZ's instruction that the proof
for (4.32) is the same after changing the domino tiling. -/
theorem sourceTemporal_yColumns_prop45Estimate_of_xAtomizations
    {unprimedBadCoeff primedBadCoeff : ℕ}
    (hatoms :
      HLOZProp47Prop45XEastPrimed.HasXEastSeparateFiniteAtomizations
        unprimedBadCoeff primedBadCoeff) :
    ∀ᶠ m : ℕ in atTop, ∀ i : Fin 6, 4 ≤ i.1 →
      ∀ r : StageIndex, ∀ a : AlphaIndex, alphaValue a ≤ kappaTwo →
      simpleRandomWalkLaw
          (prop45FailureEvent sourceCanonicalProfiles canonicalCStar m i r
            (alphaValue a)) ≤
        sourceExceptionalRateWithPrefactor m
          (unprimedBadCoeff + primedBadCoeff + 6) kappa := by
  filter_upwards [
    HLOZProp47Prop45XEastPrimed.temporalThreshold_stoppedThetaEstimate_of_separateAtomizations
      hatoms] with m htheta
  intro i hi r a _ha
  have hprofile : sourceCanonicalProfiles i =
      canonicalProfiles ⟨0, by omega⟩ := by
    have hiCases : i.1 = 4 ∨ i.1 = 5 := by omega
    rcases hiCases with hi4 | hi5
    · have hiEq : i = ⟨4, by omega⟩ := Fin.ext hi4
      rw [hiEq, sourceCanonicalProfiles_y, canonicalProfiles_xEast]
    · have hiEq : i = ⟨5, by omega⟩ := Fin.ext hi5
      rw [hiEq, sourceCanonicalProfiles_y', canonicalProfiles_xEast]
  apply (measure_mono ?_).trans (htheta r)
  intro s hs
  refine ⟨hs.1.1.1.1, ?_⟩
  simpa only [hprofile, canonicalCStar] using hs.2

/-- All six Proposition-4.5 estimates for the literal HLOZ profile family.
The first four cases use quarter-turn invariance; the final two use the
pairing-independent temporal threshold estimate above. -/
theorem sourceCanonical_prop45Estimate_of_xAtomizations
    {unprimedBadCoeff primedBadCoeff : ℕ}
    (hatoms :
      HLOZProp47Prop45XEastPrimed.HasXEastSeparateFiniteAtomizations
        unprimedBadCoeff primedBadCoeff) :
    Prop47Prop45Estimate sourceCanonicalProfiles canonicalCStar
      (unprimedBadCoeff + primedBadCoeff + 6) := by
  filter_upwards [
    HLOZProp47Prop45XRotations.xDirections_prop45Estimate_of_separateAtomizations
      hatoms,
    sourceTemporal_yColumns_prop45Estimate_of_xAtomizations hatoms]
    with m hx hy
  intro i r a ha
  by_cases hi : i.1 < 4
  · let d : Dir := ⟨i.1, hi⟩
    have hxi := hx d r a ha
    have hidx : (⟨d.1, by omega⟩ : Fin 6) = i := by
      apply Fin.ext
      rfl
    have hprofiles : sourceCanonicalProfiles i = canonicalProfiles i := by
      rw [← hidx]
      exact sourceCanonicalProfiles_x d
    rw [hidx] at hxi
    simpa only [prop45FailureEvent, hprofiles] using hxi
  · exact hy i (by omega) r a ha

/-- Fully internal literal-source Proposition-4.5 estimate. -/
theorem sourceCanonical_prop45Estimate
    (hdisk : HLOZProp13FromAppendix.AppendixDiskEstimate) :
    Prop47Prop45Estimate sourceCanonicalProfiles canonicalCStar 10 := by
  simpa using sourceCanonical_prop45Estimate_of_xAtomizations
    (HLOZProp47Prop45XEastPrimed.hasXEastSeparateFiniteAtomizations_canonical
      hdisk)

theorem yColumns_prop45Estimate_of_separateAtomizations
    {unprimedBadCoeff primedBadCoeff : ℕ}
    (hatoms : HasYSeparateFiniteAtomizations
      unprimedBadCoeff primedBadCoeff) :
    ∀ᶠ m : ℕ in atTop, ∀ i : Fin 6, 4 ≤ i.1 →
      ∀ r : StageIndex, ∀ a : AlphaIndex, alphaValue a ≤ kappaTwo →
      simpleRandomWalkLaw
          (prop45FailureEvent canonicalProfiles canonicalCStar m i r
            (alphaValue a)) ≤
        sourceExceptionalRateWithPrefactor m
          (unprimedBadCoeff + primedBadCoeff + 6) kappa := by
  filter_upwards [hatoms, eventually_sourceEndpointScales,
    eventually_sourceProp45OneSideError_le] with m hatoms hs habsorb
  intro i hi r a _ha
  rcases hatoms r with ⟨hatom⟩
  have hY := hatom.source_measure_le hs habsorb
  have hsource : simpleRandomWalkLaw
      (prefixPairingEvent m i (stageNumber r + 1) ∩
        stoppedThetaEvent (canonicalProfiles i) (canonicalCStar i)
          m (stageNumber r)) ≤
      sourceExceptionalRateWithPrefactor m
        (unprimedBadCoeff + primedBadCoeff + 6) kappa := by
    fin_cases i
    · norm_num at hi
    · norm_num at hi
    · norm_num at hi
    · norm_num at hi
    · simpa only using hY
    · simpa only using
        prefixPairingThetaEvent_y'_le_of_y m (stageNumber r) _ hY
  exact (measure_mono (by
    intro s hs
    exact ⟨hs.1.1.1, hs.2⟩)).trans hsource

/-- The adaptive column atomization is a sufficient route to the direct
two-column estimate.  This theorem deliberately makes no claim that its
fixed temporal pair cylinders are the literal deletion events of HLOZ
(2.12). -/
theorem prop47Prop45YColumnsEstimate_of_separateAtomizations
    {unprimedBadCoeff primedBadCoeff : ℕ}
    (hatoms : HasYSeparateFiniteAtomizations
      unprimedBadCoeff primedBadCoeff) :
    Prop47Prop45YColumnsEstimate
      (unprimedBadCoeff + primedBadCoeff + 6) :=
  yColumns_prop45Estimate_of_separateAtomizations hatoms

theorem sourceExceptionalRateWithPrefactor_mono_coeff
    (m B C : ℕ) (hBC : B ≤ C) :
    sourceExceptionalRateWithPrefactor m B kappa ≤
      sourceExceptionalRateWithPrefactor m C kappa := by
  unfold sourceExceptionalRateWithPrefactor
  gcongr

/-- Auxiliary all-six Proposition-4.5 interface obtained when the formal
column profiles have been atomized by the adaptive parser.  The four `X_j`
cases use the two separate `X₁` phase partitions and full-event rotations;
the two formal column cases use the two separate phases and origin-fixing
reflection. -/
theorem allSix_prop45Estimate_of_separateAtomizations
    {xUnprimedBadCoeff xPrimedBadCoeff
      yUnprimedBadCoeff yPrimedBadCoeff : ℕ}
    (hxAtoms :
      HLOZProp47Prop45XEastPrimed.HasXEastSeparateFiniteAtomizations
        xUnprimedBadCoeff xPrimedBadCoeff)
    (hyAtoms : HasYSeparateFiniteAtomizations
      yUnprimedBadCoeff yPrimedBadCoeff) :
    ∀ᶠ m : ℕ in atTop, ∀ i : Fin 6, ∀ r : StageIndex,
      ∀ a : AlphaIndex, alphaValue a ≤ kappaTwo →
      simpleRandomWalkLaw
          (prop45FailureEvent canonicalProfiles canonicalCStar m i r
            (alphaValue a)) ≤
        sourceExceptionalRateWithPrefactor m
          (xUnprimedBadCoeff + xPrimedBadCoeff +
            yUnprimedBadCoeff + yPrimedBadCoeff + 12) kappa := by
  filter_upwards [
    HLOZProp47Prop45XRotations.xDirections_prop45Estimate_of_separateAtomizations
      hxAtoms,
    yColumns_prop45Estimate_of_separateAtomizations hyAtoms] with m hx hy
  intro i r a ha
  by_cases hi : i.1 < 4
  · let d : Dir := ⟨i.1, hi⟩
    have hxi := hx d r a ha
    have hidx : (⟨d.1, by omega⟩ : Fin 6) = i := by
      apply Fin.ext
      rfl
    rw [hidx] at hxi
    exact hxi.trans (sourceExceptionalRateWithPrefactor_mono_coeff m _ _
      (by omega))
  · have hyi := hy i (by omega) r a ha
    exact hyi.trans (sourceExceptionalRateWithPrefactor_mono_coeff m _ _
      (by omega))

/-- Honest all-six assembly boundary.  The four checkerboard directions are
constructed from the proved `X₁` atomization, while the two column estimates
are supplied directly.  In particular, this theorem does not smuggle a
fixed-pair parser/event-identification assertion into the source cut. -/
theorem prop47Prop45Estimate_of_xAtomizations_and_yEstimate
    {xUnprimedBadCoeff xPrimedBadCoeff yBadCoeff : ℕ}
    (hxAtoms :
      HLOZProp47Prop45XEastPrimed.HasXEastSeparateFiniteAtomizations
        xUnprimedBadCoeff xPrimedBadCoeff)
    (hy : Prop47Prop45YColumnsEstimate yBadCoeff) :
    Prop47Prop45Estimate canonicalProfiles canonicalCStar
      (xUnprimedBadCoeff + xPrimedBadCoeff + 6 + yBadCoeff) := by
  filter_upwards [
    HLOZProp47Prop45XRotations.xDirections_prop45Estimate_of_separateAtomizations
      hxAtoms,
    hy] with m hx hyM
  intro i r a ha
  by_cases hi : i.1 < 4
  · let d : Dir := ⟨i.1, hi⟩
    have hxi := hx d r a ha
    have hidx : (⟨d.1, by omega⟩ : Fin 6) = i := by
      apply Fin.ext
      rfl
    rw [hidx] at hxi
    exact hxi.trans (sourceExceptionalRateWithPrefactor_mono_coeff m _ _
      (by omega))
  · have hyi := hyM i (by omega) r a ha
    exact hyi.trans (sourceExceptionalRateWithPrefactor_mono_coeff m _ _
      (by omega))

theorem prop47Prop45Estimate_of_separateAtomizations
    {xUnprimedBadCoeff xPrimedBadCoeff
      yUnprimedBadCoeff yPrimedBadCoeff : ℕ}
    (hxAtoms :
      HLOZProp47Prop45XEastPrimed.HasXEastSeparateFiniteAtomizations
        xUnprimedBadCoeff xPrimedBadCoeff)
    (hyAtoms : HasYSeparateFiniteAtomizations
      yUnprimedBadCoeff yPrimedBadCoeff) :
    Prop47Prop45Estimate canonicalProfiles canonicalCStar
      (xUnprimedBadCoeff + xPrimedBadCoeff +
        yUnprimedBadCoeff + yPrimedBadCoeff + 12) :=
  allSix_prop45Estimate_of_separateAtomizations hxAtoms hyAtoms

set_option linter.constructorNameAsVariable false in
/-- Source-facing current closure of Proposition 4.7.  This version makes
the two honest residual cuts explicit: the unprimed/primed `X₁` stopped
external-path atomizations and the two independently conditioned `Y`
column-phase atomizations.  Proposition 4.5 is then supplied by the
all-six assembly above; all other hypotheses are exactly the named source
estimates used by `hlozPlanarConclusion_of_prop47_named_source_estimates`. -/
theorem hlozPlanarConclusion_of_named_estimates_and_separateAtomizations
    (stageCoeff farCoeff lemma410Coeff lemma411412Coeff
      xUnprimedBadCoeff xPrimedBadCoeff
      yUnprimedBadCoeff yPrimedBadCoeff : ℕ)
    (hFar : Prop47FarGapEstimate farCoeff)
    (hLemma410 : Prop47Lemma410Estimate lemma410Coeff)
    (hxAtoms :
      HLOZProp47Prop45XEastPrimed.HasXEastSeparateFiniteAtomizations
        xUnprimedBadCoeff xPrimedBadCoeff)
    (hyAtoms : HasYSeparateFiniteAtomizations
      yUnprimedBadCoeff yPrimedBadCoeff)
    (hLemma411412 : Prop47Lemma411412Estimate lemma411412Coeff)
    (hLow : Prop47LowStageEstimate canonicalProfiles canonicalCStar
      stageCoeff
      (prop47FailurePrefactor farCoeff lemma410Coeff
        (xUnprimedBadCoeff + xPrimedBadCoeff +
          yUnprimedBadCoeff + yPrimedBadCoeff + 12)
        lemma411412Coeff))
    (hHigh : Prop47HighStageEstimate canonicalProfiles canonicalCStar
      stageCoeff
      (prop47FailurePrefactor farCoeff lemma410Coeff
        (xUnprimedBadCoeff + xPrimedBadCoeff +
          yUnprimedBadCoeff + yPrimedBadCoeff + 12)
        lemma411412Coeff)) :
    HLOZPlanarConclusion := by
  exact hlozPlanarConclusion_of_prop47_named_source_estimates
    canonicalProfiles canonicalCStar stageCoeff farCoeff lemma410Coeff
    (xUnprimedBadCoeff + xPrimedBadCoeff +
      yUnprimedBadCoeff + yPrimedBadCoeff + 12)
    lemma411412Coeff hFar hLemma410
    (prop47Prop45Estimate_of_separateAtomizations hxAtoms hyAtoms)
    hLemma411412 hLow hHigh

set_option linter.constructorNameAsVariable false in
/-- The current source-facing closure with the canonical high-distance
branch discharged.  A common coefficient at least `64` is sufficient by the
checked Green/strong-Markov estimate. -/
theorem hlozPlanarConclusion_of_named_estimates_separateAtomizations_low
    (stageCoeff farCoeff lemma410Coeff lemma411412Coeff
      xUnprimedBadCoeff xPrimedBadCoeff
      yUnprimedBadCoeff yPrimedBadCoeff : ℕ)
    (hStageCoeff : 64 ≤ stageCoeff)
    (hFar : Prop47FarGapEstimate farCoeff)
    (hLemma410 : Prop47Lemma410Estimate lemma410Coeff)
    (hxAtoms :
      HLOZProp47Prop45XEastPrimed.HasXEastSeparateFiniteAtomizations
        xUnprimedBadCoeff xPrimedBadCoeff)
    (hyAtoms : HasYSeparateFiniteAtomizations
      yUnprimedBadCoeff yPrimedBadCoeff)
    (hLemma411412 : Prop47Lemma411412Estimate lemma411412Coeff)
    (hLow : Prop47LowStageEstimate canonicalProfiles canonicalCStar
      stageCoeff
      (prop47FailurePrefactor farCoeff lemma410Coeff
        (xUnprimedBadCoeff + xPrimedBadCoeff +
          yUnprimedBadCoeff + yPrimedBadCoeff + 12)
        lemma411412Coeff)) :
    HLOZPlanarConclusion := by
  exact hlozPlanarConclusion_of_named_estimates_and_separateAtomizations
    stageCoeff farCoeff lemma410Coeff lemma411412Coeff
    xUnprimedBadCoeff xPrimedBadCoeff yUnprimedBadCoeff yPrimedBadCoeff
    hFar hLemma410 hxAtoms hyAtoms hLemma411412 hLow
    (HLOZProp47HighStageConnector.prop47HighStageEstimate_of_highEscape
      canonicalProfiles canonicalCStar stageCoeff
        (prop47FailurePrefactor farCoeff lemma410Coeff
          (xUnprimedBadCoeff + xPrimedBadCoeff +
            yUnprimedBadCoeff + yPrimedBadCoeff + 12)
          lemma411412Coeff)
      (HLOZProp47HighEscape.canonical_prop47HighEscapeEstimate_mono
        stageCoeff hStageCoeff))

set_option linter.constructorNameAsVariable false in
/-- The strongest current source-facing closure: the high-distance branch is
proved, and the `Y` atomizations are required in the concrete terminal form
whose column-run product laws are derived internally. -/
theorem hlozPlanarConclusion_of_named_estimates_terminalY_low
    (stageCoeff farCoeff lemma410Coeff lemma411412Coeff
      xUnprimedBadCoeff xPrimedBadCoeff
      yUnprimedBadCoeff yPrimedBadCoeff : ℕ)
    (hStageCoeff : 64 ≤ stageCoeff)
    (hFar : Prop47FarGapEstimate farCoeff)
    (hLemma410 : Prop47Lemma410Estimate lemma410Coeff)
    (hxAtoms :
      HLOZProp47Prop45XEastPrimed.HasXEastSeparateFiniteAtomizations
        xUnprimedBadCoeff xPrimedBadCoeff)
    (hyAtoms : HasYTerminalSeparateFiniteAtomizations
      yUnprimedBadCoeff yPrimedBadCoeff)
    (hLemma411412 : Prop47Lemma411412Estimate lemma411412Coeff)
    (hLow : Prop47LowStageEstimate canonicalProfiles canonicalCStar
      stageCoeff
      (prop47FailurePrefactor farCoeff lemma410Coeff
        (xUnprimedBadCoeff + xPrimedBadCoeff +
          yUnprimedBadCoeff + yPrimedBadCoeff + 12)
        lemma411412Coeff)) :
    HLOZPlanarConclusion := by
  exact hlozPlanarConclusion_of_named_estimates_separateAtomizations_low
    stageCoeff farCoeff lemma410Coeff lemma411412Coeff
    xUnprimedBadCoeff xPrimedBadCoeff yUnprimedBadCoeff yPrimedBadCoeff
    hStageCoeff hFar hLemma410 hxAtoms
    (hasYSeparateFiniteAtomizations_of_terminal hyAtoms)
    hLemma411412 hLow

set_option linter.constructorNameAsVariable false in
/-- Legacy coarse-atom closure.  Its Proposition-4.9 input includes a
history/atom compatibility premise not supplied merely by stopped labels and
an unordered creation set. -/
theorem hlozPlanarConclusion_of_named_estimates_terminalY_prop49Atoms
    (stageCoeff farCoeff lemma410Coeff lemma411412Coeff
      xUnprimedBadCoeff xPrimedBadCoeff
      yUnprimedBadCoeff yPrimedBadCoeff : ℕ)
    (hStageCoeff : 64 ≤ stageCoeff)
    (hFar : Prop47FarGapEstimate farCoeff)
    (hLemma410 : Prop47Lemma410Estimate lemma410Coeff)
    (hxAtoms :
      HLOZProp47Prop45XEastPrimed.HasXEastSeparateFiniteAtomizations
        xUnprimedBadCoeff xPrimedBadCoeff)
    (hyAtoms : HasYTerminalSeparateFiniteAtomizations
      yUnprimedBadCoeff yPrimedBadCoeff)
    (hLemma411412 : Prop47Lemma411412Estimate lemma411412Coeff)
    (profileAtom :
      ℕ → Fin 6 → AlphaTriple → StageIndex → ℕ → Set Path)
    (hProp49Atoms :
      HLOZProp47LowStageConnector.Prop47StoppedProfileProp49SourceAtomEstimate
        canonicalProfiles canonicalCStar stageCoeff profileAtom) :
    HLOZPlanarConclusion := by
  exact hlozPlanarConclusion_of_named_estimates_terminalY_low
    stageCoeff farCoeff lemma410Coeff lemma411412Coeff
    xUnprimedBadCoeff xPrimedBadCoeff yUnprimedBadCoeff yPrimedBadCoeff
    hStageCoeff hFar hLemma410 hxAtoms hyAtoms hLemma411412
    (HLOZProp47LowStageConnector.prop47LowStageEstimate_of_sourceAtoms
      canonicalProfiles canonicalCStar 128 stageCoeff
      (prop47FailurePrefactor farCoeff lemma410Coeff
        (xUnprimedBadCoeff + xPrimedBadCoeff +
          yUnprimedBadCoeff + yPrimedBadCoeff + 12)
        lemma411412Coeff)
      profileAtom
      HLOZProp47LowEscape.canonical_prop47SequentialEscapeEstimate
      hProp49Atoms)

set_option linter.constructorNameAsVariable false in
/-- Strongest current source-facing closure.  Proposition 4.9 is supplied by
finite phase/winner branches, each with its own screen and separately
disjoint refined conditioning atoms.  Branches need not be mutually
disjoint; their finite union is absorbed into the stage coefficient. -/
theorem hlozPlanarConclusion_of_named_estimates_terminalY_refinedProp49Branches
    (branchCount localCoeff farCoeff lemma410Coeff lemma411412Coeff
      xUnprimedBadCoeff xPrimedBadCoeff
      yUnprimedBadCoeff yPrimedBadCoeff : ℕ)
    (hStageCoeff : 64 ≤ branchCount * localCoeff)
    (hFar : Prop47FarGapEstimate farCoeff)
    (hLemma410 : Prop47Lemma410Estimate lemma410Coeff)
    (hxAtoms :
      HLOZProp47Prop45XEastPrimed.HasXEastSeparateFiniteAtomizations
        xUnprimedBadCoeff xPrimedBadCoeff)
    (hyAtoms : HasYTerminalSeparateFiniteAtomizations
      yUnprimedBadCoeff yPrimedBadCoeff)
    (hLemma411412 : Prop47Lemma411412Estimate lemma411412Coeff)
    (branchScreen : ℕ → Fin 6 → AlphaTriple → StageIndex →
      Fin branchCount → Set Path)
    (refinedAtom : ℕ → Fin 6 → AlphaTriple → StageIndex →
      Fin branchCount → ℕ → Set Path)
    (hProp49Atoms :
      HLOZProp47LowStageConnector.Prop47StoppedProfileProp49RefinedFiniteBranchEstimate
        canonicalProfiles canonicalCStar branchCount localCoeff
        branchScreen refinedAtom) :
    HLOZPlanarConclusion := by
  exact hlozPlanarConclusion_of_named_estimates_terminalY_low
    (branchCount * localCoeff) farCoeff lemma410Coeff lemma411412Coeff
    xUnprimedBadCoeff xPrimedBadCoeff yUnprimedBadCoeff yPrimedBadCoeff
    hStageCoeff hFar hLemma410 hxAtoms hyAtoms hLemma411412
    (HLOZProp47LowStageConnector.prop47LowStageEstimate_of_refinedFiniteBranches
      canonicalProfiles canonicalCStar branchCount localCoeff 128
      (prop47FailurePrefactor farCoeff lemma410Coeff
        (xUnprimedBadCoeff + xPrimedBadCoeff +
          yUnprimedBadCoeff + yPrimedBadCoeff + 12)
        lemma411412Coeff)
      branchScreen refinedAtom
      HLOZProp47LowEscape.canonical_prop47SequentialEscapeEstimate
      hProp49Atoms)

set_option linter.constructorNameAsVariable false in
/-- Optional stronger sufficient closure: Proposition 4.9 is supplied through
a joint active/complement stopped-atom factorization.  This factorization is
not asserted by the HLOZ source and is retained as a reusable sufficient
route. -/
theorem hlozPlanarConclusion_of_named_estimates_terminalY_factorizedProp49Atoms
    (stageCoeff farCoeff lemma410Coeff lemma411412Coeff
      xUnprimedBadCoeff xPrimedBadCoeff
      yUnprimedBadCoeff yPrimedBadCoeff : ℕ)
    (hStageCoeff : 64 ≤ stageCoeff)
    (hFar : Prop47FarGapEstimate farCoeff)
    (hLemma410 : Prop47Lemma410Estimate lemma410Coeff)
    (hxAtoms :
      HLOZProp47Prop45XEastPrimed.HasXEastSeparateFiniteAtomizations
        xUnprimedBadCoeff xPrimedBadCoeff)
    (hyAtoms : HasYTerminalSeparateFiniteAtomizations
      yUnprimedBadCoeff yPrimedBadCoeff)
    (hLemma411412 : Prop47Lemma411412Estimate lemma411412Coeff)
    (profileAtom :
      ℕ → Fin 6 → AlphaTriple → StageIndex → ℕ → Set Path)
    (hProp49Atoms :
      HLOZProp47LowStageConnector.Prop47StoppedProfileProp49FactorizedSourceAtomEstimate
        canonicalProfiles canonicalCStar stageCoeff profileAtom) :
    HLOZPlanarConclusion := by
  exact hlozPlanarConclusion_of_named_estimates_terminalY_low
    stageCoeff farCoeff lemma410Coeff lemma411412Coeff
    xUnprimedBadCoeff xPrimedBadCoeff yUnprimedBadCoeff yPrimedBadCoeff
    hStageCoeff hFar hLemma410 hxAtoms hyAtoms hLemma411412
    (HLOZProp47LowStageConnector.prop47LowStageEstimate_of_factorizedSourceAtoms
      canonicalProfiles canonicalCStar 128 stageCoeff
      (prop47FailurePrefactor farCoeff lemma410Coeff
        (xUnprimedBadCoeff + xPrimedBadCoeff +
          yUnprimedBadCoeff + yPrimedBadCoeff + 12)
        lemma411412Coeff)
      profileAtom
      HLOZProp47LowEscape.canonical_prop47SequentialEscapeEstimate
      hProp49Atoms)

end Erdos1166.HLOZProp47Prop45YColumns
