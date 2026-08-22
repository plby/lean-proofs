/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingSpatialInsertionFiber
import ErdosProblems.Erdos1165.ExternalCountTransport
import ErdosProblems.Erdos1165.TilingInsertedLocalTime
import ErdosProblems.Erdos1165.VariableStoppedTracePartition

/-!
# Endpoint/midpoint phases of an all-six tiling external path

The state-dependent tiling deletion retains a two-step block path, hence its
vertices alternate between the endpoint chain and block midpoints.  This
module splits those two phases exactly.  At every site one of the two phases
carries at least half of the unfiltered external local time, allowing the
endpoint-chain one-point estimates to be applied after a finite phase choice.
-/

namespace Erdos1165.TilingExternalPhaseSplit

open LazyDecomposition PathInsertion
open TilingLazyDecomposition TilingSpatialInsertionFiber
open ExternalCountTransport ExternalThickCount
open ShiftedPrefixBridge SpatialInsertionFiber
open VariableStoppedTracePartition

abbrev DominoTiling := Tilings.Tiling

attribute [local instance] Classical.propDecidable

/-- The two alternating vertex classes in a completed two-step block path. -/
inductive ExternalVertexPhase
  | endpoint
  | midpoint
  deriving DecidableEq

instance : Finite ExternalVertexPhase :=
  Finite.of_injective
    (fun phase : ExternalVertexPhase ↦
      match phase with
      | .endpoint => false
      | .midpoint => true)
    (by intro a b h; cases a <;> cases b <;> simp_all)

noncomputable instance : Fintype ExternalVertexPhase := Fintype.ofFinite _

/-- Vertices in even list positions, including the initial endpoint. -/
def endpointPhaseVertices : List Point → List Point
  | [] => []
  | [a] => [a]
  | a :: _b :: rest => a :: endpointPhaseVertices rest

/-- Vertices in odd list positions, namely the block midpoints. -/
def midpointPhaseVertices : List Point → List Point
  | [] => []
  | [_a] => []
  | _a :: b :: rest => b :: midpointPhaseVertices rest

def phaseVertices : ExternalVertexPhase → List Point → List Point
  | .endpoint => endpointPhaseVertices
  | .midpoint => midpointPhaseVertices

/-- Every occurrence belongs to exactly one alternating vertex phase. -/
theorem count_eq_endpointPhase_add_midpointPhase (p : List Point) (x : Point) :
    p.count x =
      (endpointPhaseVertices p).count x +
        (midpointPhaseVertices p).count x := by
  induction p using List.twoStepInduction with
  | nil => rfl
  | singleton a => simp [endpointPhaseVertices, midpointPhaseVertices]
  | cons_cons a b rest ih _ =>
      simp only [List.count_cons, endpointPhaseVertices,
        midpointPhaseVertices]
      omega

/-- Midpoint chain of a block word, with one point for each block. -/
def blockMidpointPath (x : Point) : List Block → List Point
  | [] => []
  | b :: bs => blockMiddle x b :: blockMidpointPath (blockEnd x b) bs

/-- The even vertices of a block path are exactly its endpoint chain. -/
theorem endpointPhaseVertices_blockPath (x : Point) (bs : List Block) :
    endpointPhaseVertices (blockPath x bs) = blockEndpointPath x bs := by
  induction bs generalizing x with
  | nil => rfl
  | cons b bs ih =>
      change x :: endpointPhaseVertices (blockPath (blockEnd x b) bs) =
        x :: blockEndpointPath (blockEnd x b) bs
      rw [ih]

/-- The odd vertices of a block path are exactly its block midpoints. -/
theorem midpointPhaseVertices_blockPath (x : Point) (bs : List Block) :
    midpointPhaseVertices (blockPath x bs) = blockMidpointPath x bs := by
  induction bs generalizing x with
  | nil => rfl
  | cons b bs ih =>
      change blockMiddle x b ::
          midpointPhaseVertices (blockPath (blockEnd x b) bs) =
        blockMiddle x b :: blockMidpointPath (blockEnd x b) bs
      rw [ih]

theorem endpointPhaseVertices_blockPath_append_singleton
    (x z : Point) (bs : List Block) :
    endpointPhaseVertices (blockPath x bs ++ [z]) =
      blockEndpointPath x bs := by
  induction bs generalizing x with
  | nil => rfl
  | cons b bs ih =>
      change x :: endpointPhaseVertices
          (blockPath (blockEnd x b) bs ++ [z]) =
        x :: blockEndpointPath (blockEnd x b) bs
      rw [ih]

theorem midpointPhaseVertices_blockPath_append_singleton
    (x z : Point) (bs : List Block) :
    midpointPhaseVertices (blockPath x bs ++ [z]) =
      blockMidpointPath x bs ++ [z] := by
  induction bs generalizing x with
  | nil => rfl
  | cons b bs ih =>
      change blockMiddle x b :: midpointPhaseVertices
          (blockPath (blockEnd x b) bs ++ [z]) =
        blockMiddle x b :: (blockMidpointPath (blockEnd x b) bs ++ [z])
      rw [ih]

/-! ## Phase-filtered state-dependent external data -/

def tilingExternalPhasePath (t : DominoTiling) (phase : ExternalVertexPhase)
    (p : List Point) : List Point :=
  phaseVertices phase (tilingExternalPath t p)

def tilingExternalPhaseLocalTime (t : DominoTiling)
    (phase : ExternalVertexPhase) (p : List Point) (x : Point) : ℕ :=
  listLocalTime (tilingExternalPhasePath t phase p) x

def tilingExternalPhaseVisitedSites (t : DominoTiling)
    (phase : ExternalVertexPhase) (p : List Point) : Finset Point :=
  (tilingExternalPhasePath t phase p).toFinset

/-- Exact split of unfiltered state-dependent external local time into the
endpoint and midpoint phases. -/
theorem tilingExternalLocalTime_eq_phase_sum (t : DominoTiling)
    (p : List Point) (x : Point) :
    listLocalTime (tilingExternalPath t p) x =
      tilingExternalPhaseLocalTime t .endpoint p x +
        tilingExternalPhaseLocalTime t .midpoint p x := by
  exact count_eq_endpointPhase_add_midpointPhase
    (tilingExternalPath t p) x

/-- On a block path, the endpoint phase is literally the endpoint chain of
the statefully deleted word. -/
theorem tilingExternalEndpointPhase_blockPath (t : DominoTiling)
    (x : Point) (bs : List Block) :
    tilingExternalPhasePath t .endpoint (blockPath x bs) =
      blockEndpointPath x (deleteTilingBlocks t x bs) := by
  unfold tilingExternalPhasePath phaseVertices
  rw [tilingExternalPath_blockPath]
  change endpointPhaseVertices
      (blockPath x (deleteTilingBlocks t x bs)) = _
  exact endpointPhaseVertices_blockPath x (deleteTilingBlocks t x bs)

/-- On a block path, the midpoint phase is literally the midpoint chain of
the statefully deleted word. -/
theorem tilingExternalMidpointPhase_blockPath (t : DominoTiling)
    (x : Point) (bs : List Block) :
    tilingExternalPhasePath t .midpoint (blockPath x bs) =
      blockMidpointPath x (deleteTilingBlocks t x bs) := by
  unfold tilingExternalPhasePath phaseVertices
  rw [tilingExternalPath_blockPath]
  change midpointPhaseVertices
      (blockPath x (deleteTilingBlocks t x bs)) = _
  exact midpointPhaseVertices_blockPath x (deleteTilingBlocks t x bs)

theorem mem_tilingExternalPhaseVisitedSites_iff (t : DominoTiling)
    (phase : ExternalVertexPhase) (p : List Point) (x : Point) :
    x ∈ tilingExternalPhaseVisitedSites t phase p ↔
      0 < tilingExternalPhaseLocalTime t phase p x := by
  rw [tilingExternalPhaseVisitedSites, List.mem_toFinset,
    ← List.count_pos_iff]
  rfl

/-- At every site, one of the two phases carries at least half of the full
external local time, stated without division. -/
theorem exists_phase_fullLocalTime_le_two_mul (t : DominoTiling)
    (p : List Point) (x : Point) :
    ∃ phase : ExternalVertexPhase,
      listLocalTime (tilingExternalPath t p) x ≤
        2 * tilingExternalPhaseLocalTime t phase p x := by
  rw [tilingExternalLocalTime_eq_phase_sum]
  by_cases hle :
      tilingExternalPhaseLocalTime t .endpoint p x ≤
        tilingExternalPhaseLocalTime t .midpoint p x
  · exact ⟨.midpoint, by omega⟩
  · exact ⟨.endpoint, by omega⟩

/-- Floor-half form of the same finite phase selection. -/
theorem exists_phase_half_le_localTime (t : DominoTiling)
    (p : List Point) (x : Point) :
    ∃ phase : ExternalVertexPhase,
      listLocalTime (tilingExternalPath t p) x / 2 ≤
        tilingExternalPhaseLocalTime t phase p x := by
  obtain ⟨phase, hphase⟩ :=
    exists_phase_fullLocalTime_le_two_mul t p x
  exact ⟨phase, by omega⟩

/-- A lower bound on unfiltered external local time yields a phase carrying
the corresponding floor-half threshold. -/
theorem exists_phase_threshold_half_le (t : DominoTiling)
    (p : List Point) (x : Point) (threshold : ℕ)
    (hthreshold : threshold ≤ listLocalTime (tilingExternalPath t p) x) :
    ∃ phase : ExternalVertexPhase,
      threshold / 2 ≤ tilingExternalPhaseLocalTime t phase p x := by
  obtain ⟨phase, hphase⟩ := exists_phase_half_le_localTime t p x
  exact ⟨phase, (Nat.div_le_div_right hthreshold).trans hphase⟩

/-- Positive half-threshold selection also places the site in that phase's
finite visited set. -/
theorem exists_phase_threshold_half_le_and_mem (t : DominoTiling)
    (p : List Point) (x : Point) (threshold : ℕ) (hpositive : 2 ≤ threshold)
    (hthreshold : threshold ≤ listLocalTime (tilingExternalPath t p) x) :
    ∃ phase : ExternalVertexPhase,
      threshold / 2 ≤ tilingExternalPhaseLocalTime t phase p x ∧
        x ∈ tilingExternalPhaseVisitedSites t phase p := by
  obtain ⟨phase, hphase⟩ :=
    exists_phase_threshold_half_le t p x threshold hthreshold
  refine ⟨phase, hphase, ?_⟩
  rw [mem_tilingExternalPhaseVisitedSites_iff]
  have : 0 < threshold / 2 := Nat.div_pos (by omega) (by omega)
  exact this.trans_le hphase

/-! ## Compatibility with the existing temporal-phase API -/

/-- Endpoint/midpoint refinement of one of the two temporal pairing phases. -/
def phasedExternalVertexPath (t : DominoTiling) (o : Orientation)
    (phase : ExternalVertexPhase) (p : List Point) : List Point :=
  tilingExternalPhasePath t phase (phasedInput o p)

def phasedExternalVertexLocalTime (t : DominoTiling) (o : Orientation)
    (phase : ExternalVertexPhase) (p : List Point) (x : Point) : ℕ :=
  tilingExternalPhaseLocalTime t phase (phasedInput o p) x

def phasedExternalVertexVisitedSites (t : DominoTiling) (o : Orientation)
    (phase : ExternalVertexPhase) (p : List Point) : Finset Point :=
  tilingExternalPhaseVisitedSites t phase (phasedInput o p)

/-- Exact endpoint/midpoint refinement of `phasedExternalLocalTime`. -/
theorem phasedExternalLocalTime_eq_vertexPhase_sum (t : DominoTiling)
    (o : Orientation) (p : List Point) (x : Point) :
    phasedExternalLocalTime t o p x =
      phasedExternalVertexLocalTime t o .endpoint p x +
        phasedExternalVertexLocalTime t o .midpoint p x := by
  exact tilingExternalLocalTime_eq_phase_sum t (phasedInput o p) x

/-- Direct selector in the vocabulary of the random-clock band modules. -/
theorem exists_vertexPhase_phasedExternal_threshold_half_le_and_mem
    (t : DominoTiling) (o : Orientation) (p : List Point) (x : Point)
    (threshold : ℕ) (hpositive : 2 ≤ threshold)
    (hthreshold : threshold ≤ phasedExternalLocalTime t o p x) :
    ∃ phase : ExternalVertexPhase,
      threshold / 2 ≤ phasedExternalVertexLocalTime t o phase p x ∧
        x ∈ phasedExternalVertexVisitedSites t o phase p := by
  exact exists_phase_threshold_half_le_and_mem
    t (phasedInput o p) x threshold hpositive hthreshold

/-! ## Checkerboard-compatible sites lie in the endpoint phase -/

/-- Exact state-dependent external path of the even temporal prefix. -/
theorem tilingExternalPath_even_prefix_blocks (t : DominoTiling)
    (omega : StepPath) (n : ℕ) :
    tilingExternalPath t
        (phasedInput .even
          (finitePathList (pathPrefix (trajectory omega) n))) =
      blockPath (0, 0)
          (deleteTilingBlocks t (0, 0) (completePrefixBlocks omega n)) ++
        prefixRemainder omega n := by
  rw [prefixPath_eq_blockPath_append_remainder]
  unfold prefixRemainder
  by_cases hmod : n % 2 = 0
  · simp only [hmod, if_pos, List.append_nil]
    change tilingExternalPath t
        (blockPath (0, 0) (completePrefixBlocks omega n)) = _
    exact tilingExternalPath_blockPath t (0, 0)
      (completePrefixBlocks omega n)
  · simp only [hmod, if_false]
    change tilingExternalPath t
        (blockPath (0, 0) (completePrefixBlocks omega n) ++
          [trajectory omega n]) = _
    exact TilingInsertedLocalTime.tilingExternalPath_blockPath_append_singleton
      t (0, 0) (trajectory omega n) (completePrefixBlocks omega n)

/-- Exact state-dependent external path of the shifted temporal prefix. -/
theorem tilingExternalPath_shifted_prefix_blocks (t : DominoTiling)
    (omega : StepPath) (n : ℕ) (hn : 0 < n) :
    tilingExternalPath t
        (phasedInput .shifted
          (finitePathList (pathPrefix (trajectory omega) n))) =
      blockPath (trajectory omega 1)
          (deleteTilingBlocks t (trajectory omega 1)
            (shiftedCompletePrefixBlocks omega n)) ++
        shiftedPrefixRemainder omega n := by
  rw [finitePathList_cons_tail]
  change tilingExternalPath t
      (shiftedInput (pathPrefix (trajectory omega) n)) = _
  rw [shiftedInput_eq_segmentPath omega n hn,
    segmentPath_eq_blockPath_append_remainder]
  unfold shiftedPrefixRemainder shiftedCompletePrefixBlocks segmentRemainder
  by_cases hmod : (n - 1) % 2 = 0
  · simp [hmod, tilingExternalPath_blockPath]
  · simp only [hmod, if_false]
    exact TilingInsertedLocalTime.tilingExternalPath_blockPath_append_singleton
      t (trajectory omega 1) (trajectory omega (1 + (n - 1)))
        (completeSegmentBlocks omega 1 (n - 1))

/-- Filtering an all-six phased external prefix to its compatible
checkerboard class is exactly its endpoint vertex phase.  The possible
unpaired terminal vertex has the opposite checkerboard parity. -/
theorem filter_tilingExternalPath_phasedInput_eq_endpointPhase
    (t : DominoTiling) (o : Orientation) (omega : StepPath) (n : ℕ) :
    (tilingExternalPath t
        (phasedInput o
          (finitePathList (pathPrefix (trajectory omega) n)))).filter
        (fun x ↦ decide (orientationClass o x)) =
      endpointPhaseVertices
        (tilingExternalPath t
          (phasedInput o
            (finitePathList (pathPrefix (trajectory omega) n)))) := by
  cases o with
  | even =>
      rw [tilingExternalPath_even_prefix_blocks]
      rw [List.filter_append, filter_prefixRemainder_even, List.append_nil]
      rw [blockPath_filter_orientationClass]
      · unfold prefixRemainder
        by_cases hmod : n % 2 = 0
        · simp [hmod, endpointPhaseVertices_blockPath]
        · simp [hmod, endpointPhaseVertices_blockPath_append_singleton]
      · simp [OrientationCompatible, EvenPoint, pointParity]
  | shifted =>
      by_cases hn : n = 0
      · subst n
        rfl
      · have hpos : 0 < n := Nat.pos_of_ne_zero hn
        rw [tilingExternalPath_shifted_prefix_blocks t omega n hpos]
        rw [List.filter_append, filter_shiftedPrefixRemainder, List.append_nil]
        rw [blockPath_filter_orientationClass]
        · unfold shiftedPrefixRemainder segmentRemainder
          by_cases hmod : (n - 1) % 2 = 0
          · simp [hmod, endpointPhaseVertices_blockPath]
          · simp [hmod, endpointPhaseVertices_blockPath_append_singleton]
        · exact shifted_start_compatible omega

/-- For a genuine increment path, every occurrence of a point compatible
with the chosen temporal checkerboard class lies in the endpoint phase. -/
theorem phasedExternalLocalTime_eq_endpoint_of_compatible
    (t : DominoTiling) (o : Orientation) (omega : StepPath) (n : ℕ)
    (x : Point) (hx : OrientationCompatible o x) :
    phasedExternalLocalTime t o
        (finitePathList (pathPrefix (trajectory omega) n)) x =
      phasedExternalVertexLocalTime t o .endpoint
        (finitePathList (pathPrefix (trajectory omega) n)) x := by
  let p := finitePathList (pathPrefix (trajectory omega) n)
  let external := tilingExternalPath t (phasedInput o p)
  have hfilter : external.filter (fun y ↦ decide (orientationClass o y)) =
      endpointPhaseVertices external :=
    filter_tilingExternalPath_phasedInput_eq_endpointPhase t o omega n
  have hxclass : orientationClass o x :=
    (orientationClass_iff_compatible o x).2 hx
  have hcount :
      listLocalTime
          (external.filter (fun y ↦ decide (orientationClass o y))) x =
        listLocalTime external x := by
    unfold listLocalTime
    exact List.count_filter
      (p := fun y ↦ decide (orientationClass o y))
      (decide_eq_true hxclass)
  change listLocalTime external x =
    listLocalTime (endpointPhaseVertices external) x
  rw [← hcount, hfilter]

/-- A point in the opposite checkerboard class cannot occur in the endpoint
phase of the selected temporal pairing.  This is the converse support
statement to `phasedExternalLocalTime_eq_endpoint_of_compatible`; it is
important for column tilings, whose canonical bases meet both checkerboard
classes. -/
theorem phasedExternalEndpointLocalTime_eq_zero_of_incompatible
    (t : DominoTiling) (o : Orientation) (omega : StepPath) (n : ℕ)
    (x : Point) (hx : ¬ OrientationCompatible o x) :
    phasedExternalVertexLocalTime t o .endpoint
        (finitePathList (pathPrefix (trajectory omega) n)) x = 0 := by
  let p := finitePathList (pathPrefix (trajectory omega) n)
  let external := tilingExternalPath t (phasedInput o p)
  have hfilter : external.filter (fun y ↦ decide (orientationClass o y)) =
      endpointPhaseVertices external :=
    filter_tilingExternalPath_phasedInput_eq_endpointPhase t o omega n
  have hxclass : ¬ orientationClass o x := by
    exact fun h ↦ hx ((orientationClass_iff_compatible o x).1 h)
  change listLocalTime (endpointPhaseVertices external) x = 0
  rw [← hfilter]
  unfold listLocalTime
  rw [List.count_eq_zero]
  simp only [List.mem_filter]
  intro hmem
  exact hxclass (of_decide_eq_true hmem.2)

/-- In the incompatible checkerboard class the whole retained local time is
carried by block midpoints, not block endpoints.  Thus `IsTilingBase t x`
alone cannot justify applying an endpoint-chain estimate: column-tiling bases
occur in both alternatives of this exact dichotomy. -/
theorem phasedExternalLocalTime_eq_midpoint_of_incompatible
    (t : DominoTiling) (o : Orientation) (omega : StepPath) (n : ℕ)
    (x : Point) (hx : ¬ OrientationCompatible o x) :
    phasedExternalLocalTime t o
        (finitePathList (pathPrefix (trajectory omega) n)) x =
      phasedExternalVertexLocalTime t o .midpoint
        (finitePathList (pathPrefix (trajectory omega) n)) x := by
  rw [phasedExternalLocalTime_eq_vertexPhase_sum,
    phasedExternalEndpointLocalTime_eq_zero_of_incompatible t o omega n x hx,
    zero_add]

/-- Walk-path wrapper on the exact support of simple random walk. -/
theorem pathPhasedExternalLocalTime_eq_endpoint_of_compatible
    (t : DominoTiling) (o : Orientation) (s : WalkPath) (n : ℕ)
    (x : Point) (hvalid : s ∈ validStepWalk)
    (hx : OrientationCompatible o x) :
    pathPhasedExternalLocalTime t o s n x =
      phasedExternalVertexLocalTime t o .endpoint
        (finitePathList (pathPrefix s n)) x := by
  unfold validStepWalk at hvalid
  rw [← hvalid]
  exact phasedExternalLocalTime_eq_endpoint_of_compatible
    t o (stepsOfWalk s) n x hx

/-- Under the same parity hypothesis, full external visited membership is
equivalent to endpoint-phase visited membership. -/
theorem mem_phasedExternalVisitedSites_iff_endpoint_of_compatible
    (t : DominoTiling) (o : Orientation) (omega : StepPath) (n : ℕ)
    (x : Point) (hx : OrientationCompatible o x) :
    x ∈ phasedExternalVisitedSites t o
        (finitePathList (pathPrefix (trajectory omega) n)) ↔
      x ∈ phasedExternalVertexVisitedSites t o .endpoint
        (finitePathList (pathPrefix (trajectory omega) n)) := by
  rw [phasedExternalVisitedSites, List.mem_toFinset,
    phasedExternalVertexVisitedSites, tilingExternalPhaseVisitedSites,
    List.mem_toFinset, ← List.count_pos_iff, ← List.count_pos_iff]
  change 0 < phasedExternalLocalTime t o
      (finitePathList (pathPrefix (trajectory omega) n)) x ↔
    0 < phasedExternalVertexLocalTime t o .endpoint
      (finitePathList (pathPrefix (trajectory omega) n)) x
  rw [phasedExternalLocalTime_eq_endpoint_of_compatible t o omega n x hx]

/-! ## A canonical-base midpoint counterexample

The following five-point nearest-neighbor word is a concrete obstruction to
the tempting but false claim that canonical tiling bases always occur in the
endpoint phase.  For the even-column tiling, `columnMidpointBase = (0,1)` is a
canonical base.  It occurs twice, both times as a midpoint of the unshifted
two-step pairing, while the shifted state-dependent deletion sees it only
once.  Hence the phase-free local time used by an unshifted deletion is not
the source's shifted endpoint local time at this base.
-/

def columnMidpointCounterexamplePath : List Point :=
  [(0, 0), (0, 1), (1, 1), (0, 1), (0, 2)]

def columnMidpointBase : Point := (0, 1)

theorem columnMidpointBase_isTilingBase :
    IsTilingBase .evenColumns columnMidpointBase := by
  decide

theorem columnMidpointCounterexample_externalPath :
    tilingExternalPath .evenColumns columnMidpointCounterexamplePath =
      columnMidpointCounterexamplePath := by
  decide

theorem columnMidpointCounterexample_endpointLocalTime :
    tilingExternalPhaseLocalTime .evenColumns .endpoint
        columnMidpointCounterexamplePath columnMidpointBase = 0 := by
  decide

theorem columnMidpointCounterexample_midpointLocalTime :
    tilingExternalPhaseLocalTime .evenColumns .midpoint
        columnMidpointCounterexamplePath columnMidpointBase = 2 := by
  decide

theorem columnMidpointCounterexample_fullExternalLocalTime :
    listLocalTime
        (tilingExternalPath .evenColumns columnMidpointCounterexamplePath)
        columnMidpointBase = 2 := by
  decide

theorem columnMidpointCounterexample_shiftedExternalLocalTime :
    phasedExternalLocalTime .evenColumns .shifted
        columnMidpointCounterexamplePath columnMidpointBase = 1 := by
  decide

/-- The checked counterexample in the exact form needed by the source audit:
even though the point is a canonical base, the phase-free retained local time
is not its shifted endpoint-chain local time. -/
theorem columnMidpointCounterexample_phaseFree_ne_shifted :
    listLocalTime
        (tilingExternalPath .evenColumns columnMidpointCounterexamplePath)
        columnMidpointBase ≠
      phasedExternalLocalTime .evenColumns .shifted
        columnMidpointCounterexamplePath columnMidpointBase := by
  rw [columnMidpointCounterexample_fullExternalLocalTime,
    columnMidpointCounterexample_shiftedExternalLocalTime]
  decide

end Erdos1165.TilingExternalPhaseSplit
