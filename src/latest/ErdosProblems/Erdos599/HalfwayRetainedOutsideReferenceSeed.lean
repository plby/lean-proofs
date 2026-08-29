/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayRetainedLaterLinkage
import ErdosProblems.Erdos599.HalfwayMarkerAbsorbedMacroRequest

/-!
# A deletion-safe retained row supplies the outside-reference seed

This is the end-to-end positive replacement for selecting an unrelated
later linkage.  The input row is the family certified safe for deletion by
Assertion 9.23.  The current extension clause solves the deleted residual;
the lifted residual linkage is united with the retained row, and first-hit
truncation leaves that row literally unchanged because it is tight at the
selected later frontier.

The resulting later row therefore satisfies the literal inclusion required
by the pruned-reference Theorem 4.12 construction.  Running the ordinary
omega closure then produces the actual closed set, split outside warp,
full-reference bracket assignment, and Claim 2 context.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath
open CardinalInduction
open CardinalInduction.ControlledSlices
open CardinalInduction.SliceCandidate
open _root_.Erdos599.Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa theta : Cardinal.{u}}

/-- All genuinely local hypotheses needed to turn the deletion-safe
reference row into the exact linkage-first outside-reference seed.

The two location fields are stated at row level.  The constructor derives
the seed's corresponding facts using the exact initial set and terminal
frontier of the first-hit linkage; neither field mentions the subsequently
constructed closed set. -/
structure RetainedOutsideReferenceSeedInput
    (C : ClubStageGeometry Gamma Y kappa theta) where
  retainedTarget : Set Gamma.DPath
  retainedInitials : Set V
  retained_initials_source : retainedInitials ⊆ Gamma.source
  retained_linkage :
    IsLinkageBetween Gamma retainedInitials Gamma.target retainedTarget
  residual_unhindered :
    (Gamma.delete (Gamma.vertexSet retainedTarget)).IsUnhindered
  residual_source_card :
    #(Gamma.delete (Gamma.vertexSet retainedTarget)).source = kappa
  source_reference_prefixes :
    {p | p ∈ Y ∧ p.initial ∈ Gamma.source} ⊆
      firstHitPrefixFamily retained_linkage
        (separates_target_of_subset_roof
          (retained_initials_source.trans C.source_subset_outerRoof))
  reference_isWarp : Gamma.IsWarp Y
  reference_finite : Gamma.HasFiniteCharacter Y
  reference_in_roof : ∀ p ∈ Y, p.support ⊆ C.outerRoof
  source_location :
    Gamma.source \ Gamma.initialSet Y ⊆ C.before ∩ C.innerRoof
  terminal_location :
    C.newSlice \ Gamma.vertexSet Y ⊆ C.before ∩ C.outerRoof
  Preserves : FinitePath Gamma.graph → Prop
  target_paths : ∀ v ∈ C.oldSlice ∩ C.outerRoof,
    ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ C.newSlice ∧
        p.support ⊆ C.outerRoof ∧ Preserves p
  safe_in_roof : EligibleHammocksContainedInRoof Gamma Y
    C.before C.innerRoof C.outerRoof
  initialSeed : Set V
  initial_card : #initialSeed ≤ kappa
  initial_in_roof : initialSeed ⊆ C.outerRoof
  marker_initials_seed :
    Gamma.initialSet {p | p ∈ Y ∧ p.initial ∉ Gamma.source} ⊆
      initialSeed

namespace RetainedOutsideReferenceSeedInput

variable {C : ClubStageGeometry Gamma Y kappa theta}

/-- Install a particular retained current-later linkage into the exact
marker-absorbed seed.  Keeping this as a named construction (rather than a
local `let`) lets downstream accounting retain the ambient source--target
linkage which owns all first-hit prefixes. -/
noncomputable def markerSeedOfCurrent
    (I : RetainedOutsideReferenceSeedInput C)
    (D : CurrentLaterLinkage C Gamma.source)
    (hsourceD : {p | p ∈ Y ∧ p.initial ∈ Gamma.source} ⊆ D.later) :
    MarkerAbsorbedMacroSeed
      (Gamma := Gamma) (Y := Y) (kappa := kappa) where
  before := C.before
  innerRoof := C.innerRoof
  outerRoof := C.outerRoof
  targetSlice := C.oldSlice
  targetSide := C.newSlice
  initialSeed := I.initialSeed
  later := D.later
  Preserves := I.Preserves
  target_paths := I.target_paths
  reference_isWarp := I.reference_isWarp
  reference_finite := I.reference_finite
  reference_in_roof := I.reference_in_roof
  later_isWarp := D.later_isWarp
  later_finite := D.later_finite
  later_in_roof := D.later_in_outerRoof
  safe_in_roof := I.safe_in_roof
  kappa_infinite := C.capacity_infinite
  before_card := C.before_card
  initial_card := I.initial_card
  initial_in_roof := I.initial_in_roof
  sourceReferenceRetained := hsourceD
  markerInitialsSeed := I.marker_initials_seed
  source_location := by
    simpa only [D.initialSet_later] using I.source_location
  terminal_location := by
    intro x hx
    exact I.terminal_location
      ⟨D.terminalFrontier_later_subset hx.1, hx.2⟩

/-- The dependency-preserving output of the retained linkage construction.
Unlike `exists_seed`, this record does not discard the ambient target
linkage after forming its first-hit row. -/
structure CurrentResult
    (I : RetainedOutsideReferenceSeedInput C) where
  current : CurrentLaterLinkage C Gamma.source
  sourceReferenceRetained :
    {p | p ∈ Y ∧ p.initial ∈ Gamma.source} ⊆ current.later

namespace CurrentResult

variable {I : RetainedOutsideReferenceSeedInput C}

/-- The marker-absorbed seed installed on the retained current-later row. -/
noncomputable def seed (O : CurrentResult I) :
    MarkerAbsorbedMacroSeed
      (Gamma := Gamma) (Y := Y) (kappa := kappa) :=
  I.markerSeedOfCurrent O.current O.sourceReferenceRetained

@[simp] theorem seed_later (O : CurrentResult I) :
    O.seed.later = O.current.later := rfl

@[simp] theorem seed_initialSeed (O : CurrentResult I) :
    O.seed.initialSeed = I.initialSeed := rfl

/-- Every member of the installed later row retains its actual ambient
source--target owner. -/
theorem seed_later_is_ambient_fragment (O : CurrentResult I)
    {p : Gamma.DPath} (hp : p ∈ O.seed.later) :
    IsLadderFragment Gamma O.current.ambient p :=
  O.current.later_is_ambient_fragment p hp

/-- Concrete ambient target suffix recovered without pretending that it
lies in the first-hit row. -/
theorem exists_ambientTargetSuffix_of_mem_seedVertex
    (O : CurrentResult I) {x : V}
    (hx : x ∈ Gamma.vertexSet O.seed.later) :
    ∃ p : FinitePath Gamma.graph,
      p.start = x ∧ p.finish ∈ Gamma.target ∧
        p.support ⊆ Gamma.vertexSet O.current.ambient ∧
        p.edgeSet ⊆ familyEdges O.current.ambient :=
  O.current.exists_ambientTargetSuffix_of_mem_laterVertex hx

end CurrentResult

/-- Construct the retained current-later linkage while preserving its
ambient target linkage in the result. -/
theorem exists_currentResult
    (I : RetainedOutsideReferenceSeedInput C)
    (hext : UniversalExtensionClauseAt V kappa) :
    Nonempty (CurrentResult I) := by
  obtain ⟨D, hsourceD⟩ := C.exists_currentLaterLinkage_containing_prefixes
    hext C.normalized I.retained_initials_source I.retained_linkage
      I.residual_unhindered I.residual_source_card
      (separates_target_of_subset_roof
        (I.retained_initials_source.trans C.source_subset_outerRoof))
      I.source_reference_prefixes
  exact ⟨⟨D, hsourceD⟩⟩

/-- Construct the exact later row and the outside-reference seed.  The
returned linkage witness records that this is a genuine source-to-later-
frontier linkage, while the equality exposes the chosen row used by the
seed. -/
theorem exists_seed
    (I : RetainedOutsideReferenceSeedInput C)
    (hext : UniversalExtensionClauseAt V kappa) :
    ∃ S : MarkerAbsorbedMacroSeed
        (Gamma := Gamma) (Y := Y) (kappa := kappa),
      IsLinkageBetween Gamma Gamma.source C.newSlice S.later := by
  obtain ⟨O⟩ := I.exists_currentResult hext
  exact ⟨O.seed, O.current.later_linkage⟩

/-- Dependency-preserving request constructor.  Its output retains the
ambient target linkage alongside the closed marker-absorbed request. -/
theorem exists_currentRequest
    (I : RetainedOutsideReferenceSeedInput C)
    (hext : UniversalExtensionClauseAt V kappa) :
    ∃ O : CurrentResult I,
      Nonempty (MarkerAbsorbedMacroRequest O.seed) := by
  obtain ⟨O⟩ := I.exists_currentResult hext
  exact ⟨O, O.seed.exists_request⟩

/-- End-to-end repaired Assertion 9.31 Claim 2 stage.  The output includes
the exact seed so the dependent request retains the chosen later row; the
request itself contains the closed set, literal split fracture,
outside-reference boundary, full-reference bracket assignment, and Claim 2
closure context. -/
theorem exists_request
    (I : RetainedOutsideReferenceSeedInput C)
    (hext : UniversalExtensionClauseAt V kappa) :
    ∃ S : MarkerAbsorbedMacroSeed
        (Gamma := Gamma) (Y := Y) (kappa := kappa),
      IsLinkageBetween Gamma Gamma.source C.newSlice S.later ∧
        Nonempty (MarkerAbsorbedMacroRequest S) := by
  obtain ⟨S, hS⟩ := I.exists_seed hext
  exact ⟨S, hS, S.exists_request⟩

/-- Expanded output exposing both halves of the repaired retention
argument: the source-starting reference family is literally retained, and
after marker absorption the full selected reference survives outside the
cut only as a subwarp of the honest outside later row. -/
theorem exists_request_with_pruned_inclusion
    (I : RetainedOutsideReferenceSeedInput C)
    (hext : UniversalExtensionClauseAt V kappa) :
    ∃ S : MarkerAbsorbedMacroSeed
        (Gamma := Gamma) (Y := Y) (kappa := kappa),
      IsLinkageBetween Gamma Gamma.source C.newSlice S.later ∧
      {p | p ∈ Y ∧ p.initial ∈ Gamma.source} ⊆ S.later ∧
      ∃ R : MarkerAbsorbedMacroRequest S,
        outsideReference Y R.closureSet ⊆
          outsideReference S.later R.closureSet := by
  obtain ⟨S, hS, hrequest⟩ := I.exists_request hext
  exact ⟨S, hS, S.sourceReferenceRetained,
    hrequest.some, hrequest.some.outside_subset⟩

end RetainedOutsideReferenceSeedInput

end LinkageBlueprint
end Blueprint
end Erdos599
