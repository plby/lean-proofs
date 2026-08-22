/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfacePhysicalCoordinateRecovery

/-!
# Exact adjacent-pair support for the positive interface

The broad positive-interface support contains every thick below-level
domino.  It is too large for an actual-rank comparison: an unrestricted
replacement on that whole support may create two new level sites at every
coordinate.  The thresholded interface, however, only uses the two physical
rows `shell` and `shell + 1`.

This file isolates exactly those rows as a stopped support selector.  The
selector is prefix-local and measurable, and its orientation-selected image
is literally the physical adjacent-pair site set.  Consequently a later
actual-delta product can expose only the genuinely random pair total, rather
than paying a cutoff-sized rank multiplicity.
-/

open Set

namespace Erdos1165.HLOZPositiveInterfacePairSupportSelector

open HLOZPositiveInterfacePhysicalCoordinateRecovery
open HLOZPositiveInterfaceSupportSelector
open LazyDecomposition
open NearFavoriteShells
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedRetainedDominoEndpoint
open TilingLazyDecomposition
open TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

attribute [local instance] Classical.propDecidable

/-- Canonical retained bases whose orientation-selected physical endpoint
lies in one of the two adjacent deficit rows. -/
def orientedPositiveInterfacePairSupportAt
    (t : DominoTiling) (o : Orientation) (m externalThreshold width shell : ℕ)
    (s : WalkPath) (n : ℕ) : Finset Point :=
  (orientedPositiveInterfaceSupportAt t o m externalThreshold s n).filter
    fun b ↦
      (m - localTime s n (orientedDominoEndpoint t o b)) / width = shell ∨
        (m - localTime s n (orientedDominoEndpoint t o b)) / width = shell + 1

theorem orientedPositiveInterfacePairSupportAt_subset
    (t : DominoTiling) (o : Orientation) (m externalThreshold width shell : ℕ)
    (s : WalkPath) (n : ℕ) :
    orientedPositiveInterfacePairSupportAt t o m externalThreshold width
        shell s n ⊆
      orientedPositiveInterfaceSupportAt t o m externalThreshold s n :=
  Finset.filter_subset _ _

/-- The pair support depends only on the physical stopped prefix. -/
theorem orientedPositiveInterfacePairSupportAt_prefix_invariant
    (t : DominoTiling) (o : Orientation) (m externalThreshold width shell : ℕ)
    {s s' : WalkPath} {n : ℕ} (hp : pathPrefix s n = pathPrefix s' n) :
    orientedPositiveInterfacePairSupportAt t o m externalThreshold width
        shell s n =
      orientedPositiveInterfacePairSupportAt t o m externalThreshold width
        shell s' n := by
  classical
  have hsupport := orientedPositiveInterfaceSupportAt_prefix_invariant
    t o m externalThreshold hp
  have hlocal : ∀ x, localTime s n x = localTime s' n x := by
    intro x
    unfold localTime
    rw [hp]
  unfold orientedPositiveInterfacePairSupportAt
  rw [hsupport]
  apply Finset.filter_congr
  intro b _hb
  rw [hlocal]

theorem measurable_orientedPositiveInterfacePairSupportAt
    (t : DominoTiling) (o : Orientation)
    (m externalThreshold width shell n : ℕ) :
    Measurable fun s ↦
      orientedPositiveInterfacePairSupportAt t o m externalThreshold width
        shell s n := by
  apply measurable_of_pathPrefix_invariant n
  exact orientedPositiveInterfacePairSupportAt_prefix_invariant
    t o m externalThreshold width shell

/-- The exact adjacent-pair support is a concrete all-creation support
selector at every creation rank. -/
theorem orientedPositiveInterfacePairSupportSelectorData
    (t : DominoTiling) (o : Orientation)
    (m k externalThreshold width shell : ℕ) :
    OrientedAllCreationSupportSelectorData t o m k
      (orientedPositiveInterfacePairSupportAt t o m externalThreshold width
        shell) := by
  constructor
  · exact measurable_natIndexed (creationTimeNat m k)
      (measurable_creationTimeNat m k)
      (fun n s ↦ orientedPositiveInterfacePairSupportAt t o m
        externalThreshold width shell s n)
      (measurable_orientedPositiveInterfacePairSupportAt t o m
        externalThreshold width shell)
  · intro s s' n hp
    exact orientedPositiveInterfacePairSupportAt_prefix_invariant
      t o m externalThreshold width shell hp
  · intro s n hvalid
    exact (orientedPositiveInterfacePairSupportAt_subset t o m
      externalThreshold width shell s n).trans
        ((orientedPositiveInterfaceSupportSelectorData t o m k
          externalThreshold).represented s n hvalid)

/-- Physical thick endpoint sites in the two adjacent deficit rows. -/
def positiveInterfacePhysicalPairSites
    (t : DominoTiling) (o : Orientation)
    (m externalThreshold width shell : ℕ) (s : WalkPath) (n : ℕ) :
    Finset Point :=
  (positiveInterfacePhysicalSites t o externalThreshold s n).filter fun x ↦
    (m - localTime s n x) / width = shell ∨
      (m - localTime s n x) / width = shell + 1

/-- On a genuine positive-rank prefix, the exact physical adjacent-pair set
is the orientation-selected image of the pair support. -/
theorem positiveInterfacePhysicalPairSites_eq_support_image
    (t : DominoTiling) (o : Orientation) (m externalThreshold width shell : ℕ)
    (s : WalkPath) (n : ℕ) (hvalid : s ∈ validStepWalk) (hn : 0 < n)
    (hfavorite : thresholdSites s n m = favoriteSites s n)
    (hthreshold : 0 < externalThreshold) :
    positiveInterfacePhysicalPairSites t o m externalThreshold width shell
        s n =
      (orientedPositiveInterfacePairSupportAt t o m externalThreshold width
        shell s n).image (orientedDominoEndpoint t o) := by
  classical
  have hsites := positiveInterfacePhysicalSites_eq_support_image
    t o m externalThreshold s n hvalid hn hfavorite hthreshold
  ext x
  constructor
  · intro hx
    rw [positiveInterfacePhysicalPairSites, Finset.mem_filter] at hx
    rcases hx with ⟨hxsites, hrow⟩
    rw [hsites, Finset.mem_image] at hxsites
    rcases hxsites with ⟨b, hb, rfl⟩
    rw [Finset.mem_image]
    refine ⟨b, ?_, rfl⟩
    rw [orientedPositiveInterfacePairSupportAt, Finset.mem_filter]
    exact ⟨hb, hrow⟩
  · intro hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨b, hb, rfl⟩
    rw [orientedPositiveInterfacePairSupportAt, Finset.mem_filter] at hb
    rw [positiveInterfacePhysicalPairSites, Finset.mem_filter, hsites]
    exact ⟨Finset.mem_image.mpr ⟨b, hb.1, rfl⟩, hb.2⟩

end

end Erdos1165.HLOZPositiveInterfacePairSupportSelector
