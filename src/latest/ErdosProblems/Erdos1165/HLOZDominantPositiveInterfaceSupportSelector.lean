/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairSupportSelector
import ErdosProblems.Erdos1165.TilingPrefixedFavoriteTraceSupport

/-!
# Dominant exact-pair support for the positive shell recurrence

The raw random-clock candidate is an endpoint.  The insertion product is
instead applied after replacing its domino by the endpoint with larger
stopped local time and then choosing the temporal orientation of that
endpoint.  This file records the corresponding prefix-local support
selector.  It is kept separate from the older raw-orientation selector so
that the cardinal normalization in the recurrence remains explicit.
-/

open Set

namespace Erdos1165.HLOZDominantPositiveInterfaceSupportSelector

open HLOZPositiveInterfacePairSupportSelector
open HLOZPositiveInterfaceSupportSelector
open LazyDecomposition
open NearFavoriteShells
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedRetainedDominoEndpoint
open TilingOrientedShellZeroSourcePartition
open TilingLazyDecomposition
open TilingPrefixedInsertedLocalTime
open TilingPrefixedFavoriteTraceSupport
open TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

attribute [local instance] Classical.propDecidable

/-- The orientation-selected endpoint of `b` is dominant at the stopped
physical prefix.  Inserted domino excursions add the same amount to both
endpoints, so this is exactly the dominance condition needed in every
stopped fibre. -/
def orientedEndpointDominantAt
    (t : DominoTiling) (o : Orientation) (s : WalkPath) (n : ℕ)
    (b : Point) : Prop :=
  let z := fixedOrientedTypedExternalWordCode t o n s
  let terminal := prefixedTilingInsertionTerminal z.initial t z.start
    z.retained (fun _ ↦ 0) z.tail
  prefixedTilingFixedBoundaryLocalTime z.initial.1 z.start z.retained terminal
      (tilingPartner t (orientedDominoEndpoint t o b)) ≤
    prefixedTilingFixedBoundaryLocalTime z.initial.1 z.start z.retained terminal
      (orientedDominoEndpoint t o b)

/-- Tie-consistent dominant selection.  In a strict comparison the larger
endpoint is selected; on equality only the canonical tiling base is kept.
This makes the selector single-valued on every domino while retaining the
fixed-boundary formulation needed by the stopped product. -/
def orientedEndpointCanonicallyDominantAt
    (t : DominoTiling) (o : Orientation) (s : WalkPath) (n : ℕ)
    (b : Point) : Prop :=
  let z := fixedOrientedTypedExternalWordCode t o n s
  let terminal := prefixedTilingInsertionTerminal z.initial t z.start
    z.retained (fun _ ↦ 0) z.tail
  let partnerCount := prefixedTilingFixedBoundaryLocalTime z.initial.1
    z.start z.retained terminal (tilingPartner t (orientedDominoEndpoint t o b))
  let endpointCount := prefixedTilingFixedBoundaryLocalTime z.initial.1
    z.start z.retained terminal (orientedDominoEndpoint t o b)
  partnerCount < endpointCount ∨
    (partnerCount = endpointCount ∧ orientedDominoEndpoint t o b = b)

theorem orientedEndpointDominantAt_of_canonical
    {t : DominoTiling} {o : Orientation} {s : WalkPath} {n : ℕ} {b : Point}
    (h : orientedEndpointCanonicallyDominantAt t o s n b) :
    orientedEndpointDominantAt t o s n b := by
  unfold orientedEndpointCanonicallyDominantAt at h
  unfold orientedEndpointDominantAt
  rcases h with h | h
  · exact h.le
  · exact h.1.le

/-- Canonical retained bases in one orientation whose selected endpoint is
thick, below the current favorite level, outside the distinguished dominoes,
and dominant in its domino. -/
def orientedDominantPositiveInterfaceSupportAt
    (t : DominoTiling) (o : Orientation) (m externalThreshold : ℕ)
    (s : WalkPath) (n : ℕ) : Finset Point :=
  (orientedPositiveInterfaceSupportAt t o m externalThreshold s n).filter
    (orientedEndpointCanonicallyDominantAt t o s n)

/-- The two adjacent deficit rows of the dominant support. -/
def orientedDominantPositiveInterfacePairSupportAt
    (t : DominoTiling) (o : Orientation)
    (m externalThreshold width shell : ℕ)
    (s : WalkPath) (n : ℕ) : Finset Point :=
  (orientedDominantPositiveInterfaceSupportAt t o m externalThreshold s n).filter
    fun b ↦
      (m - localTime s n (orientedDominoEndpoint t o b)) / width = shell ∨
        (m - localTime s n (orientedDominoEndpoint t o b)) / width = shell + 1

/-- Physical dominant endpoints represented by the normalized broad
positive-interface support. -/
noncomputable def orientedDominantPositiveInterfacePhysicalSites
    (t : DominoTiling) (o : Orientation) (m externalThreshold : ℕ)
    (s : WalkPath) (n : ℕ) : Finset Point :=
  (orientedDominantPositiveInterfaceSupportAt t o m externalThreshold s n).image
    (orientedDominoEndpoint t o)

/-- Physical dominant endpoints in two adjacent deficit rows. -/
noncomputable def orientedDominantPositiveInterfacePhysicalPairSites
    (t : DominoTiling) (o : Orientation)
    (m externalThreshold width shell : ℕ)
    (s : WalkPath) (n : ℕ) : Finset Point :=
  (orientedDominantPositiveInterfacePairSupportAt t o m externalThreshold
    width shell s n).image (orientedDominoEndpoint t o)

theorem shellCandidates_dominantPairSites_eq
    (t : DominoTiling) (o : Orientation)
    (m externalThreshold width shell : ℕ) (s : WalkPath) (n j : ℕ)
    (hj : j = shell ∨ j = shell + 1) :
    shellCandidates
        (orientedDominantPositiveInterfacePhysicalPairSites t o m
          externalThreshold width shell s n)
        (fun x ↦ (m - localTime s n x) / width) j =
      shellCandidates
        (orientedDominantPositiveInterfacePhysicalSites t o m
          externalThreshold s n)
        (fun x ↦ (m - localTime s n x) / width) j := by
  classical
  rcases hj with rfl | rfl <;>
    ext x <;>
    simp only [mem_shellCandidates,
      orientedDominantPositiveInterfacePhysicalPairSites,
      orientedDominantPositiveInterfacePhysicalSites, Finset.mem_image,
      orientedDominantPositiveInterfacePairSupportAt, Finset.mem_filter] <;>
    aesop

theorem orientedDominantPositiveInterfaceSupportAt_subset
    (t : DominoTiling) (o : Orientation) (m externalThreshold : ℕ)
    (s : WalkPath) (n : ℕ) :
    orientedDominantPositiveInterfaceSupportAt t o m externalThreshold s n ⊆
      orientedPositiveInterfaceSupportAt t o m externalThreshold s n :=
  Finset.filter_subset _ _

theorem orientedDominantPositiveInterfacePairSupportAt_subset
    (t : DominoTiling) (o : Orientation)
    (m externalThreshold width shell : ℕ)
    (s : WalkPath) (n : ℕ) :
    orientedDominantPositiveInterfacePairSupportAt t o m externalThreshold
        width shell s n ⊆
      orientedDominantPositiveInterfaceSupportAt t o m externalThreshold s n :=
  Finset.filter_subset _ _

theorem orientedDominantPositiveInterfacePairSupportAt_subset_raw
    (t : DominoTiling) (o : Orientation)
    (m externalThreshold width shell : ℕ)
    (s : WalkPath) (n : ℕ) :
    orientedDominantPositiveInterfacePairSupportAt t o m externalThreshold
        width shell s n ⊆
      orientedPositiveInterfacePairSupportAt t o m externalThreshold width
        shell s n := by
  intro b hb
  rw [orientedDominantPositiveInterfacePairSupportAt, Finset.mem_filter] at hb
  rw [orientedPositiveInterfacePairSupportAt, Finset.mem_filter]
  exact ⟨orientedDominantPositiveInterfaceSupportAt_subset
    t o m externalThreshold s n hb.1, hb.2⟩

theorem mem_orientedDominantPositiveInterfacePairSupportAt_iff
    (t : DominoTiling) (o : Orientation)
    (m externalThreshold width shell : ℕ)
    (s : WalkPath) (n : ℕ) (b : Point) :
    b ∈ orientedDominantPositiveInterfacePairSupportAt t o m
        externalThreshold width shell s n ↔
      b ∈ orientedPositiveInterfacePairSupportAt t o m externalThreshold
          width shell s n ∧
        orientedEndpointCanonicallyDominantAt t o s n b := by
  simp only [orientedDominantPositiveInterfacePairSupportAt,
    orientedDominantPositiveInterfaceSupportAt,
    orientedPositiveInterfacePairSupportAt, Finset.mem_filter]
  tauto

theorem orientedEndpointCanonicallyDominantAt_prefix_invariant
    (t : DominoTiling) (o : Orientation) {s s' : WalkPath} {n : ℕ}
    (hp : pathPrefix s n = pathPrefix s' n) (b : Point) :
    orientedEndpointCanonicallyDominantAt t o s n b ↔
      orientedEndpointCanonicallyDominantAt t o s' n b := by
  unfold orientedEndpointCanonicallyDominantAt
  rw [fixedOrientedTypedExternalWordCode_eq_of_pathPrefix_eq t o hp]

theorem orientedDominantPositiveInterfaceSupportAt_prefix_invariant
    (t : DominoTiling) (o : Orientation) (m externalThreshold : ℕ)
    {s s' : WalkPath} {n : ℕ} (hp : pathPrefix s n = pathPrefix s' n) :
    orientedDominantPositiveInterfaceSupportAt t o m externalThreshold s n =
      orientedDominantPositiveInterfaceSupportAt t o m externalThreshold s' n := by
  classical
  unfold orientedDominantPositiveInterfaceSupportAt
  rw [orientedPositiveInterfaceSupportAt_prefix_invariant
    t o m externalThreshold hp]
  apply Finset.filter_congr
  intro b _hb
  exact orientedEndpointCanonicallyDominantAt_prefix_invariant t o hp b

theorem orientedDominantPositiveInterfacePairSupportAt_prefix_invariant
    (t : DominoTiling) (o : Orientation)
    (m externalThreshold width shell : ℕ)
    {s s' : WalkPath} {n : ℕ} (hp : pathPrefix s n = pathPrefix s' n) :
    orientedDominantPositiveInterfacePairSupportAt t o m externalThreshold
        width shell s n =
      orientedDominantPositiveInterfacePairSupportAt t o m externalThreshold
        width shell s' n := by
  classical
  have hsupport :=
    orientedDominantPositiveInterfaceSupportAt_prefix_invariant
      t o m externalThreshold hp
  have hlocal : ∀ x, localTime s n x = localTime s' n x := by
    intro x
    unfold localTime
    rw [hp]
  unfold orientedDominantPositiveInterfacePairSupportAt
  rw [hsupport]
  apply Finset.filter_congr
  intro b _hb
  rw [hlocal]

theorem measurable_orientedDominantPositiveInterfacePairSupportAt
    (t : DominoTiling) (o : Orientation)
    (m externalThreshold width shell n : ℕ) :
    Measurable fun s ↦
      orientedDominantPositiveInterfacePairSupportAt t o m externalThreshold
        width shell s n := by
  apply measurable_of_pathPrefix_invariant n
  exact orientedDominantPositiveInterfacePairSupportAt_prefix_invariant
    t o m externalThreshold width shell

/-- The dominant adjacent-pair support is a concrete all-creation selector.
The represented condition follows from the older raw pair support. -/
theorem orientedDominantPositiveInterfacePairSupportSelectorData
    (t : DominoTiling) (o : Orientation)
    (m k externalThreshold width shell : ℕ) :
    OrientedAllCreationSupportSelectorData t o m k
      (orientedDominantPositiveInterfacePairSupportAt t o m
        externalThreshold width shell) := by
  constructor
  · exact measurable_natIndexed (creationTimeNat m k)
      (measurable_creationTimeNat m k)
      (fun n s ↦ orientedDominantPositiveInterfacePairSupportAt t o m
        externalThreshold width shell s n)
      (measurable_orientedDominantPositiveInterfacePairSupportAt t o m
        externalThreshold width shell)
  · intro s s' n hp
    exact orientedDominantPositiveInterfacePairSupportAt_prefix_invariant
      t o m externalThreshold width shell hp
  · intro s n hvalid
    exact (orientedDominantPositiveInterfacePairSupportAt_subset_raw t o m
      externalThreshold width shell s n).trans
        ((orientedPositiveInterfacePairSupportSelectorData t o m k
          externalThreshold width shell).represented s n hvalid)

/-- Every member carries the dominance inequality definitionally. -/
theorem orientedEndpointDominantAt_of_mem_pairSupport
    {t : DominoTiling} {o : Orientation}
    {m externalThreshold width shell n : ℕ} {s : WalkPath} {b : Point}
    (hb : b ∈ orientedDominantPositiveInterfacePairSupportAt t o m
      externalThreshold width shell s n) :
    orientedEndpointDominantAt t o s n b := by
  rw [orientedDominantPositiveInterfacePairSupportAt,
    Finset.mem_filter] at hb
  rw [orientedDominantPositiveInterfaceSupportAt,
    Finset.mem_filter] at hb
  exact orientedEndpointDominantAt_of_canonical hb.1.2

end

end Erdos1165.HLOZDominantPositiveInterfaceSupportSelector
