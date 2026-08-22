/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingExternalPhaseSplit

/-!
# Source-oriented external local time

The external local time in HLOZ's source screen is attached to one of the two
temporal pairings.  It is the local time on the retained **endpoint chain** of
that pairing.  It is not the local time on the full statefully retained path,
which also contains block midpoints.

This distinction is essential for the column tilings: their canonical bases
meet both checkerboard classes.  `TilingExternalPhaseSplit` contains a checked
five-step counterexample showing that a canonical column base can occur only
as a midpoint in the unshifted pairing.  Consequently every source predicate
must carry the endpoint band's explicit `orientation` parameter.
-/

open Set

namespace Erdos1165.HLOZSourceOrientedExternalLocalTime

open LazyDecomposition SpatialInsertionFiber
open TilingExternalPhaseSplit TilingLazyDecomposition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

attribute [local instance] Classical.propDecidable

/-- Prefix form of the source external local time.  The endpoint phase is
built into the definition; no validity hypothesis is needed to state it. -/
def prefixTilingSourceExternalBaseLocalTime {n : ℕ}
    (t : DominoTiling) (o : Orientation) (u : Fin (n + 1) → Point)
    (b : Point) : ℕ :=
  phasedExternalVertexLocalTime t o .endpoint (finitePathList u) b

/-- Walk-path form of the source external local time at physical time `n`. -/
def tilingSourceExternalBaseLocalTime
    (t : DominoTiling) (o : Orientation) (s : WalkPath)
    (n : ℕ) (b : Point) : ℕ :=
  prefixTilingSourceExternalBaseLocalTime t o (pathPrefix s n) b

@[simp] theorem tilingSourceExternalBaseLocalTime_eq_prefix
    (t : DominoTiling) (o : Orientation) (s : WalkPath)
    (n : ℕ) (b : Point) :
    tilingSourceExternalBaseLocalTime t o s n b =
      prefixTilingSourceExternalBaseLocalTime t o (pathPrefix s n) b := rfl

/-- On a genuine nearest-neighbor walk and at a site in the band's temporal
class, the full phased retained local time equals the source endpoint-chain
local time.  This is the exact seam used by an endpoint band. -/
theorem pathPhasedExternalLocalTime_eq_source_of_compatible
    (t : DominoTiling) (o : Orientation) (s : WalkPath) (n : ℕ)
    (b : Point)
    (hvalid : s ∈ (VariableStoppedTracePartition.validStepWalk : Set WalkPath))
    (hcompatible : OrientationCompatible o b) :
    pathPhasedExternalLocalTime t o s n b =
      tilingSourceExternalBaseLocalTime t o s n b := by
  exact pathPhasedExternalLocalTime_eq_endpoint_of_compatible
    t o s n b hvalid hcompatible

/-- Symmetric form convenient when rewriting a source predicate. -/
theorem tilingSourceExternalBaseLocalTime_eq_pathPhased_of_compatible
    (t : DominoTiling) (o : Orientation) (s : WalkPath) (n : ℕ)
    (b : Point)
    (hvalid : s ∈ (VariableStoppedTracePartition.validStepWalk : Set WalkPath))
    (hcompatible : OrientationCompatible o b) :
    tilingSourceExternalBaseLocalTime t o s n b =
      pathPhasedExternalLocalTime t o s n b :=
  (pathPhasedExternalLocalTime_eq_source_of_compatible
    t o s n b hvalid hcompatible).symm

/-- Endpoint sites of one source pairing, restricted to the pairing's
checkerboard class.  The filter makes the intended support explicit even on
arbitrary (not necessarily nearest-neighbor) paths. -/
def tilingSourceExternalVisitedSites
    (t : DominoTiling) (o : Orientation) (s : WalkPath) (n : ℕ) :
    Finset Point := by
  classical
  exact (phasedExternalVertexVisitedSites t o .endpoint
      (finitePathList (pathPrefix s n))).filter (OrientationCompatible o)

theorem mem_tilingSourceExternalVisitedSites_iff
    (t : DominoTiling) (o : Orientation) (s : WalkPath) (n : ℕ)
    (b : Point) :
    b ∈ tilingSourceExternalVisitedSites t o s n ↔
      OrientationCompatible o b ∧
        0 < tilingSourceExternalBaseLocalTime t o s n b := by
  rw [tilingSourceExternalVisitedSites, Finset.mem_filter]
  unfold phasedExternalVertexVisitedSites
  rw [mem_tilingExternalPhaseVisitedSites_iff]
  change
    (0 < tilingExternalPhaseLocalTime t .endpoint
        (phasedInput o (finitePathList (pathPrefix s n))) b ∧
      OrientationCompatible o b) ↔
    OrientationCompatible o b ∧
      0 < tilingExternalPhaseLocalTime t .endpoint
        (phasedInput o (finitePathList (pathPrefix s n))) b
  tauto

/-- Literal all-six, orientation-indexed version of the relevant-site family
used in Proposition 4.4.  Its probability transport to the canonical
external chain is separate; this definition records the exact pathwise
support needed by the source `Theta` screen. -/
def tilingSourceExternalCandidateSites
    (t : DominoTiling) (o : Orientation) (cutoff externalThreshold : ℕ)
    (distinguished : WalkPath → Finset Point) (s : WalkPath) : Finset Point :=
  (tilingSourceExternalVisitedSites t o s
      cutoff).filter fun b ↦
    externalThreshold ≤
        tilingSourceExternalBaseLocalTime t o s
          cutoff b ∧
      b ∉ distinguished s

theorem mem_tilingSourceExternalCandidateSites_iff
    (t : DominoTiling) (o : Orientation)
    (cutoff externalThreshold : ℕ)
    (distinguished : WalkPath → Finset Point) (s : WalkPath) (b : Point) :
    b ∈ tilingSourceExternalCandidateSites t o cutoff externalThreshold
        distinguished s ↔
      OrientationCompatible o b ∧
      0 < tilingSourceExternalBaseLocalTime t o s
        cutoff b ∧
      externalThreshold ≤
        tilingSourceExternalBaseLocalTime t o s
          cutoff b ∧
      b ∉ distinguished s := by
  rw [tilingSourceExternalCandidateSites, Finset.mem_filter,
    mem_tilingSourceExternalVisitedSites_iff]
  tauto

/-- The deterministic Proposition 4.4 support implication.  Positivity of
the thick level is stated explicitly because it is a numerical fact used only
at sufficiently large source levels. -/
theorem mem_tilingSourceExternalCandidateSites_of_thick
    {t : DominoTiling} {o : Orientation} {cutoff externalThreshold : ℕ}
    {distinguished : WalkPath → Finset Point} {s : WalkPath} {b : Point}
    (hpositive : 0 < externalThreshold)
    (hcompatible : OrientationCompatible o b)
    (hthick : externalThreshold ≤
      tilingSourceExternalBaseLocalTime t o s
        cutoff b)
    (hout : b ∉ distinguished s) :
    b ∈ tilingSourceExternalCandidateSites t o cutoff externalThreshold
      distinguished s := by
  rw [mem_tilingSourceExternalCandidateSites_iff]
  exact ⟨hcompatible, hpositive.trans_le hthick, hthick, hout⟩

/-- The exact overflow event to which the all-six normalization transport
must be applied. -/
def tilingSourceExternalCandidateOverflow
    (t : DominoTiling) (o : Orientation)
    (cutoff externalThreshold budget : ℕ)
    (distinguished : WalkPath → Finset Point) : Set WalkPath :=
  {s | budget <
    (tilingSourceExternalCandidateSites t o cutoff externalThreshold
      distinguished s).card}

theorem tilingSourceExternalCandidateSites_card_le_of_not_overflow
    {t : DominoTiling} {o : Orientation}
    {cutoff externalThreshold budget : ℕ}
    {distinguished : WalkPath → Finset Point} {s : WalkPath}
    (hs : s ∉ tilingSourceExternalCandidateOverflow
      t o cutoff externalThreshold budget distinguished) :
    (tilingSourceExternalCandidateSites t o cutoff externalThreshold
      distinguished s).card ≤ budget := by
  exact Nat.le_of_not_gt hs

end

end Erdos1165.HLOZSourceOrientedExternalLocalTime
