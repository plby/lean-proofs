/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularPendingReentry
import ErdosProblems.Erdos599.ExtensionClause

/-!
# Safe lower-cardinal batches for the singular construction

The pointwise safe-link theorem is not by itself enough for a singular
successor: a column may contain an uncountable (but smaller-cardinal) set of
requests.  At such a request web the lower *extension* clause is the correct
batch replacement.  Apply it with the entire source as the exceptional set;
the complementary linkage is empty, so the request web is linkable.  The
resulting full linkage contains every source vertex.  Deleting its whole
vertex set therefore leaves a web with empty source, which is automatically
unhindered.

The source-empty conclusion is intentionally local to the request web.  It
does **not** say that deleting the chosen paths from a larger ambient web is
safe: other ambient sources may be hindered by that deletion.

The second half of this file records two sound replacements.  A protected
batch runs the lower half-way clause on current requests together with a
reserve that is already known.  A full-source batch avoids preselecting a
reserve by carrying every source to the new stop-over.  Neither construction
by itself proves that deleting the components completed by the chosen family
preserves the requests computed from that same family; that additional joint
selection invariant is deliberately not claimed here.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularSafeBatch

universe u

variable {V : Type u}

/-- A web with no distinguished sources is unhindered. -/
theorem isUnhindered_of_source_eq_empty
    (G : DWeb V) (hsource : G.source = ∅) : G.IsUnhindered := by
  rintro ⟨W, hW, hne⟩
  apply hne
  apply Set.Subset.antisymm
  · simpa only [hsource] using hW.2.1
  · rw [hsource]
    exact Set.empty_subset _

/-- Every source of a full linkage lies in the total vertex set of that
linkage. -/
theorem source_subset_vertexSet_of_fullLinkage
    {G : DWeb V} {P : Set G.DPath}
    (hP : IsLinkageBetween G G.source G.target P) :
    G.source ⊆ G.vertexSet P := by
  intro a ha
  have haInitial : a ∈ G.initialSet P := hP.initialSet_eq.symm ▸ ha
  obtain ⟨p, hpP, hpa⟩ := haInitial
  exact ⟨p, hpP, hpa.symm ▸ p.initial_mem_support⟩

/-- Deleting the complete carrier of a full linkage leaves an unhindered
web.  No compactness or limit argument is involved: all distinguished
sources have literally been deleted. -/
theorem delete_vertexSet_fullLinkage_isUnhindered
    {G : DWeb V} {P : Set G.DPath}
    (hP : IsLinkageBetween G G.source G.target P) :
    (G.delete (G.vertexSet P)).IsUnhindered := by
  apply isUnhindered_of_source_eq_empty
  ext a
  constructor
  · intro ha
    exact (ha.2 (source_subset_vertexSet_of_fullLinkage hP ha.1)).elim
  · intro ha
    exact ha.elim

/-- The lower-cardinal extension clause chooses a whole request batch whose
carrier may be deleted *inside that request web*: every distinguished source
is then absent, so unhinderedness is vacuous.  This is not the ambient
post-deletion conclusion of the one-point safe-link theorem. -/
theorem exists_fullLinkage_delete_isUnhindered_of_lower
    {kappa mu : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hmu : mu < kappa)
    (G : DWeb V) (hG : G.IsUnhindered)
    (hsource : #G.source = mu) :
    ∃ P : Set G.DPath,
      IsLinkageBetween G G.source G.target P ∧
        (G.delete (G.vertexSet P)).IsUnhindered := by
  have hCI : CardinalInductionAt G mu := hlower mu hmu G hG
  have hext : ExtensionClauseAt G #G.source := by
    rw [hsource]
    exact hCI.extension
  obtain ⟨P, hP⟩ := linkable_of_extension_at_source_card G hext
  exact ⟨P, hP, delete_vertexSet_fullLinkage_isUnhindered hP⟩

open SingularPendingDecomposition SingularPendingReentry

/-- Concrete specialization to the request subweb at a split stop-over.
The lower extension clause, not the half-way clause, supplies a completed
batch, so this theorem also applies when the request cardinal is finite. -/
theorem exists_fullPendingBatch_delete_sourceEmpty_of_lower
    {kappa mu : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hmu : mu < kappa)
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {C : Set V}
    (hquotient : (G.quotient C).IsUnhindered)
    (hrequest : pendingRequests G W C ⊆ (G.quotient C).source)
    (hcard : #(pendingRequests G W C) = mu) :
    let H := pendingAuxiliaryWeb G W C
    ∃ P : Set H.DPath,
      IsLinkageBetween H H.source H.target P ∧
        (H.delete (H.vertexSet P)).IsUnhindered := by
  dsimp only
  let H := pendingAuxiliaryWeb G W C
  have hH : H.IsUnhindered :=
    pendingAuxiliaryWeb_isUnhindered hNorm hquotient hrequest
  have hsource : #H.source = mu := by
    simpa only [H, pendingAuxiliaryWeb_source] using hcard
  exact exists_fullLinkage_delete_isUnhindered_of_lower
    hlower hmu H hH hsource

/-- Version consuming the split certificate directly. -/
theorem exists_fullPendingBatch_delete_sourceEmpty_of_split
    {kappa mu : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hmu : mu < kappa)
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} (S : SingularTargetRowMachine.SplitStopover G W)
    (hcard : #(pendingRequests G W S.boundary) = mu) :
    let H := pendingAuxiliaryWeb G W S.boundary
    ∃ P : Set H.DPath,
      IsLinkageBetween H H.source H.target P ∧
        (H.delete (H.vertexSet P)).IsUnhindered := by
  apply exists_fullPendingBatch_delete_sourceEmpty_of_lower
    hlower hmu hNorm
  · exact S.quotient_unhindered
  · rw [S.quotient_source_eq]
    unfold pendingRequests
    apply Set.union_subset
    · rintro x ⟨p, hp, hpx⟩
      exact S.terminal_subset ⟨p, hp.1.1, hpx⟩
    · exact initialSet_boundaryPendingPart_subset G W S.boundary
  · exact hcard

/-! ## A protected batch for a reserve known in advance -/

open SingularQuotientReentry

/-- Restrict a web to the union of the requests which must be completed now
and the requests which must remain available at the next stop-over. -/
def protectedRequestWeb (H : DWeb V) (current reserve : Set V) : DWeb V :=
  H.sourceSubweb (current ∪ reserve)

@[simp] theorem protectedRequestWeb_source
    (H : DWeb V) (current reserve : Set V) :
    (protectedRequestWeb H current reserve).source = current ∪ reserve :=
  rfl

@[simp] theorem protectedRequestWeb_target
    (H : DWeb V) (current reserve : Set V) :
    (protectedRequestWeb H current reserve).target = H.target :=
  rfl

/-- A no-incoming-source certificate restricts to a source subweb. -/
theorem noEdgeEnters_protectedRequestWeb
    {H : DWeb V} (hNoEnter : H.NoEdgeEnters H.source)
    {current reserve : Set V}
    (hcurrent : current ⊆ H.source)
    (hreserve : reserve ⊆ H.source) :
    (protectedRequestWeb H current reserve).NoEdgeEnters
      (protectedRequestWeb H current reserve).source := by
  intro x y hxy hy
  apply hNoEnter hxy
  exact Set.union_subset hcurrent hreserve hy

/-- The complete state produced by one protected lower-cardinal batch.
`paths` is a full linkage from `current ∪ reserve` to `boundary`, while the
half-way field additionally says that the `current` initials already have
target suffixes.  The `reserve` initials therefore have an exact terminal
coordinate at the new unhindered quotient and can be used as the next
request row. -/
structure ProtectedBatch
    (H : DWeb V) (current reserve : Set V) (mu : Cardinal.{u}) where
  paths : Set (protectedRequestWeb H current reserve).DPath
  boundary : Set V
  halfway : IsHalfwayLinkageOfAltitude
    (protectedRequestWeb H current reserve) current mu paths
  separating : IsSeparatingHalfwayStopover
    (protectedRequestWeb H current reserve) paths boundary
  height : HeightAtMost
    (protectedRequestWeb H current reserve) boundary mu

namespace ProtectedBatch

variable {H : DWeb V} {current reserve : Set V} {mu : Cardinal.{u}}

theorem initialSet_eq (B : ProtectedBatch H current reserve mu) :
    (protectedRequestWeb H current reserve).initialSet B.paths =
      current ∪ reserve :=
  B.separating.linkage.initialSet_eq

theorem links_current (B : ProtectedBatch H current reserve mu) :
    LinksToTarget (protectedRequestWeb H current reserve) B.paths current :=
  B.halfway.2.1

theorem terminalFrontier_subset
    (B : ProtectedBatch H current reserve mu) :
    (protectedRequestWeb H current reserve).terminalFrontier B.paths ⊆
      B.boundary :=
  B.separating.linkage.terminalFrontier_subset

theorem quotient_unhindered
    (B : ProtectedBatch H current reserve mu) :
    ((protectedRequestWeb H current reserve).quotient
      B.boundary).IsUnhindered :=
  B.separating.quotient_unhindered

/-- The exact terminal-coordinate request carried into the next quotient. -/
def reserveFrontier (B : ProtectedBatch H current reserve mu) : Set V :=
  SingularBoundarySplit.requestedFrontier
    (protectedRequestWeb H current reserve) B.paths reserve

theorem reserveFrontier_subset_quotientSource
    (B : ProtectedBatch H current reserve mu) :
    B.reserveFrontier ⊆
      ((protectedRequestWeb H current reserve).quotient
        B.boundary).source := by
  exact SingularTargetRowMachine.requestedFrontier_subset_quotientSource
    B.separating

/-- No cardinal is lost when the protected initials are changed to their
terminal coordinates at the new stop-over. -/
theorem mk_reserveFrontier_eq
    (B : ProtectedBatch H current reserve mu) :
    #B.reserveFrontier = #reserve := by
  apply SingularBoundarySplit.mk_requestedFrontier_eq
    B.separating.linkage
  exact Set.subset_union_right

end ProtectedBatch

/-! ## Full-source batches with post-choice reserve coordinates -/

/-- A lower half-way batch which carries every source of the ambient web.
Only `current` is required to have target suffixes, but every other source is
transported to the new separating stop-over.  Consequently a future reserve
may be chosen *after* the paths have been chosen. -/
structure FullSourceBatch
    (H : DWeb V) (current : Set V) (mu : Cardinal.{u}) where
  paths : Set H.DPath
  boundary : Set V
  halfway : IsHalfwayLinkageOfAltitude H current mu paths
  separating : IsSeparatingHalfwayStopover H paths boundary
  height : HeightAtMost H boundary mu

namespace FullSourceBatch

variable {H : DWeb V} {current : Set V} {mu : Cardinal.{u}}

theorem initialSet_eq (B : FullSourceBatch H current mu) :
    H.initialSet B.paths = H.source :=
  B.separating.linkage.initialSet_eq

theorem links_current (B : FullSourceBatch H current mu) :
    LinksToTarget H B.paths current :=
  B.halfway.2.1

theorem quotient_unhindered (B : FullSourceBatch H current mu) :
    (H.quotient B.boundary).IsUnhindered :=
  B.separating.quotient_unhindered

/-- The terminal coordinates of an arbitrary reserve, named only after the
full-source batch has been selected. -/
def reserveFrontier (B : FullSourceBatch H current mu)
    (reserve : Set V) : Set V :=
  SingularBoundarySplit.requestedFrontier H B.paths reserve

theorem reserveFrontier_subset_quotientSource
    (B : FullSourceBatch H current mu) (reserve : Set V) :
    B.reserveFrontier reserve ⊆
      (H.quotient B.boundary).source := by
  exact SingularTargetRowMachine.requestedFrontier_subset_quotientSource
    B.separating

/-- Full source coverage gives an exact, lossless coordinate change for any
future reserve contained in the ambient source. -/
theorem mk_reserveFrontier_eq
    (B : FullSourceBatch H current mu) {reserve : Set V}
    (hreserve : reserve ⊆ H.source) :
    #(B.reserveFrontier reserve) = #reserve := by
  exact SingularBoundarySplit.mk_requestedFrontier_eq
    B.separating.linkage hreserve

end FullSourceBatch

/-- Shrinking the designated request set preserves target links. -/
theorem linksToTarget_mono_sources
    (H : DWeb V) (W : Set H.DPath) {A B : Set V}
    (hAB : A ⊆ B) (hlinks : LinksToTarget H W B) :
    LinksToTarget H W A := by
  intro a ha
  obtain ⟨p, hpW, q, rfl, hpure, hsuffix⟩ := hlinks a (hAB ha)
  refine ⟨Sum.inl q, hpW, q, rfl, ?_, hsuffix⟩
  apply Set.Subset.antisymm
  · rintro x ⟨hxq, hxA⟩
    have hxB : x ∈ q.support ∩ B := ⟨hxq, hAB hxA⟩
    have hxa : x = a := Set.mem_singleton_iff.1 (hpure ▸ hxB)
    exact hxa ▸ Set.mem_singleton a
  · intro x hx
    have hxa : x = a := Set.mem_singleton_iff.1 hx
    subst x
    have haB : a ∈ ({a} : Set V) := Set.mem_singleton a
    have haq : a ∈ q.support := (hpure.symm ▸ haB).1
    exact ⟨haq, ha⟩

/-- Enlarge a set to an exact infinite cardinal inside a prescribed ambient
set. -/
theorem exists_superset_mk_eq_of_mk_le
    {S A : Set V} {rho : Cardinal.{u}}
    (hAS : A ⊆ S) (hA : #A ≤ rho) (hrhoS : rho ≤ #S)
    (hrhoInfinite : aleph0 ≤ rho) :
    ∃ B : Set V, A ⊆ B ∧ B ⊆ S ∧ #B = rho := by
  obtain ⟨R₀, hR₀⟩ := Cardinal.le_mk_iff_exists_set.mp hrhoS
  let R : Set V := Subtype.val '' R₀
  have hRsub : R ⊆ S := by
    rintro _ ⟨x, _hx, rfl⟩
    exact x.2
  have hRcard : #R = rho := by
    calc
      #R = #R₀ := Cardinal.mk_image_eq Subtype.val_injective
      _ = rho := hR₀
  refine ⟨A ∪ R, Set.subset_union_left, Set.union_subset hAS hRsub, ?_⟩
  apply le_antisymm
  · refine (Cardinal.mk_union_le A R).trans ?_
    exact Cardinal.add_le_of_le hrhoInfinite hA hRcard.le
  · rw [← hRcard]
    exact Cardinal.mk_le_mk_of_subset Set.subset_union_right

/-- The common geometric data produced whether the designated set is large
enough for the lower half-way clause or the whole ambient source is already
smaller than the requested scale.  The latter branch has no reason to satisfy
the scale altitude bound, so this honest common interface retains only the
geometry consumed by continuation.  Despite the historical name, no
post-deletion safety assertion is a field of this structure. -/
structure FullSourceSafeBatch
    (H : DWeb V) (current : Set V) where
  paths : Set H.DPath
  boundary : Set V
  separating : IsSeparatingHalfwayStopover H paths boundary
  links : LinksToTarget H paths current

namespace FullSourceSafeBatch

variable {H : DWeb V} {current : Set V}

theorem initialSet_eq (B : FullSourceSafeBatch H current) :
    H.initialSet B.paths = H.source :=
  B.separating.linkage.initialSet_eq

theorem quotient_unhindered (B : FullSourceSafeBatch H current) :
    (H.quotient B.boundary).IsUnhindered :=
  B.separating.quotient_unhindered

def reserveFrontier (B : FullSourceSafeBatch H current)
    (reserve : Set V) : Set V :=
  SingularBoundarySplit.requestedFrontier H B.paths reserve

theorem reserveFrontier_subset_quotientSource
    (B : FullSourceSafeBatch H current) (reserve : Set V) :
    B.reserveFrontier reserve ⊆
      (H.quotient B.boundary).source := by
  exact SingularTargetRowMachine.requestedFrontier_subset_quotientSource
    B.separating

theorem mk_reserveFrontier_eq
    (B : FullSourceSafeBatch H current) {reserve : Set V}
    (hreserve : reserve ⊆ H.source) :
    #(B.reserveFrontier reserve) = #reserve := by
  exact SingularBoundarySplit.mk_requestedFrontier_eq
    B.separating.linkage hreserve

end FullSourceSafeBatch

/-- A full-source batch furnished directly by the lower half-way clause.
Unlike `exists_protectedBatch_of_lower`, it does not take a lookahead reserve:
the returned family is full on `H.source`, so any reserve can be selected
afterward and transported by `FullSourceBatch.reserveFrontier`.  This
coordinate transport is not a claim that deleting completed components is
safe for that reserve. -/
theorem exists_fullSourceBatch_of_lower
    {kappa mu : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hmu : mu < kappa) (hmuInfinite : aleph0 ≤ mu)
    (H : DWeb V) (hH : H.IsUnhindered)
    (hNoEnter : H.NoEdgeEnters H.source)
    {current : Set V}
    (hcurrent : current ⊆ H.source)
    (hcard : #current = mu) :
    Nonempty (FullSourceBatch H current mu) := by
  obtain ⟨U, hU⟩ :=
    (hlower mu hmu H hH).halfway hmuInfinite current hcurrent hcard
  obtain ⟨C, hC, hheightC⟩ := hU.exists_stopover
  obtain ⟨D, hD, hheightD, _hDsub⟩ :=
    SingularQuotientReentry.exists_separatingStopover_of_stopover
      hNoEnter hC hheightC
  exact ⟨⟨U, D, hU, hD, hheightD⟩⟩

/-- Sound dichotomy constructor for a current set of size at most the
singular scale.  If the ambient source contains `rho` vertices, first pad
`current` and apply the lower half-way clause at `rho`.  Otherwise the whole
source has cardinal below `rho`; the lower extension clause gives a full
target linkage, whose target stop-over is separating and has unhindered
quotient. -/
theorem exists_fullSourceSafeBatch_of_lower
    {kappa rho : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hrhoKappa : rho < kappa) (hrhoInfinite : aleph0 ≤ rho)
    (H : DWeb V) (hH : H.IsUnhindered)
    (hNoEnter : H.NoEdgeEnters H.source)
    {current : Set V} (hcurrent : current ⊆ H.source)
    (hcurrentCard : #current ≤ rho) :
    Nonempty (FullSourceSafeBatch H current) := by
  by_cases hrhoSource : rho ≤ #H.source
  · obtain ⟨padded, hcurrentPadded, hpaddedSource, hpaddedCard⟩ :=
      exists_superset_mk_eq_of_mk_le hcurrent hcurrentCard
        hrhoSource hrhoInfinite
    obtain ⟨B⟩ := exists_fullSourceBatch_of_lower
      hlower hrhoKappa hrhoInfinite H hH hNoEnter
        hpaddedSource hpaddedCard
    refine ⟨⟨B.paths, B.boundary, B.separating, ?_⟩⟩
    exact linksToTarget_mono_sources H B.paths
      hcurrentPadded B.links_current
  · have hsourceRho : #H.source < rho := lt_of_not_ge hrhoSource
    have hsourceKappa : #H.source < kappa :=
      hsourceRho.trans hrhoKappa
    have hext : ExtensionClauseAt H #H.source :=
      (hlower #H.source hsourceKappa H hH).extension
    obtain ⟨P, hP⟩ := linkable_of_extension_at_source_card H hext
    have hseparating :
        IsSeparatingHalfwayStopover H P H.target := by
      refine ⟨⟨hP,
        target_subset_isTrimmedSeparator Set.Subset.rfl,
        quotient_target_isUnhindered H⟩, ?_⟩
      intro a _ha
      rw [roof_target]
      exact Set.mem_univ a
    exact ⟨⟨P, H.target, hseparating,
      fullLinkage_linksToTarget hP hcurrent⟩⟩

/-- Quotient specialization used at a singular stop-over.  The output is
full on the quotient source, while only `current` has prescribed target
links. -/
theorem exists_fullSourceQuotientBatch_of_lower
    {kappa mu : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hmu : mu < kappa) (hmuInfinite : aleph0 ≤ mu)
    {G : DWeb V} (hNorm : G.IsNormalized)
    {C current : Set V}
    (hquotient : (G.quotient C).IsUnhindered)
    (hcurrent : current ⊆ (G.quotient C).source)
    (hcard : #current = mu) :
    Nonempty (FullSourceBatch (G.quotient C) current mu) := by
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  exact exists_fullSourceBatch_of_lower hlower hmu hmuInfinite
    (G.quotient C) hquotient
    (DWeb.NoEdgeEnters.quotient G hNoEnter) hcurrent hcard

/-- The lower half-way clause chooses a batch which is full on
`current ∪ protected`, but is required to reach the target only for
`current`.  The protected components therefore remain available at the new
stop-over, whose quotient is unhindered by the half-way certificate.

This is the protected-batch interface for a singular row machine once a
one-step lookahead reserve has already been fixed.  If the reserve itself
depends on the output family, a separate joint-selection argument is needed.
The theorem neither deletes the current paths nor claims that an arbitrary
completed family is safe. -/
theorem exists_protectedHalfwayBatch_of_lower
    {kappa mu : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hmu : mu < kappa) (hmuInfinite : aleph0 ≤ mu)
    (H : DWeb V) (hH : H.IsUnhindered)
    (hNoEnter : H.NoEdgeEnters H.source)
    {current reserve : Set V}
    (hcurrent : current ⊆ H.source)
    (hreserve : reserve ⊆ H.source)
    (hcard : #current = mu) :
    ∃ (U : Set (protectedRequestWeb H current reserve).DPath)
        (D : Set V),
      IsHalfwayLinkageOfAltitude
          (protectedRequestWeb H current reserve) current mu U ∧
        IsSeparatingHalfwayStopover
          (protectedRequestWeb H current reserve) U D ∧
        HeightAtMost (protectedRequestWeb H current reserve) D mu := by
  let K := protectedRequestWeb H current reserve
  have hcombined : current ∪ reserve ⊆ H.source :=
    Set.union_subset hcurrent hreserve
  have hK : K.IsUnhindered := by
    exact hH.sourceSubweb H hNoEnter hcombined
  have hcurrentK : current ⊆ K.source := by
    intro x hx
    exact Or.inl hx
  obtain ⟨U, hU⟩ :=
    (hlower mu hmu K hK).halfway hmuInfinite current hcurrentK hcard
  obtain ⟨C, hC, hheightC⟩ := hU.exists_stopover
  have hNoEnterK : K.NoEdgeEnters K.source := by
    exact noEdgeEnters_protectedRequestWeb hNoEnter hcurrent hreserve
  obtain ⟨D, hD, hheightD, _hDsub⟩ :=
    SingularQuotientReentry.exists_separatingStopover_of_stopover
      hNoEnterK hC hheightC
  exact ⟨U, D, hU, hD, hheightD⟩

/-- Structure-valued form of `exists_protectedHalfwayBatch_of_lower`, with
the exact next-request source and cardinal equations available through the
`ProtectedBatch` namespace. -/
theorem exists_protectedBatch_of_lower
    {kappa mu : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hmu : mu < kappa) (hmuInfinite : aleph0 ≤ mu)
    (H : DWeb V) (hH : H.IsUnhindered)
    (hNoEnter : H.NoEdgeEnters H.source)
    {current reserve : Set V}
    (hcurrent : current ⊆ H.source)
    (hreserve : reserve ⊆ H.source)
    (hcard : #current = mu) :
    Nonempty (ProtectedBatch H current reserve mu) := by
  obtain ⟨U, D, hU, hD, hheight⟩ :=
    exists_protectedHalfwayBatch_of_lower hlower hmu hmuInfinite H hH
      hNoEnter hcurrent hreserve hcard
  exact ⟨⟨U, D, hU, hD, hheight⟩⟩

/-- Specialization to a quotient pending row.  `protected` is the exact
lookahead request set; both the current and protected requests must be
sources of the current quotient, but only the current cardinal is used by
the lower induction hypothesis. -/
theorem exists_protectedPendingBatch_of_lower
    {kappa mu : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hmu : mu < kappa) (hmuInfinite : aleph0 ≤ mu)
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {C reserve : Set V}
    (hquotient : (G.quotient C).IsUnhindered)
    (hcurrent : pendingRequests G W C ⊆ (G.quotient C).source)
    (hreserve : reserve ⊆ (G.quotient C).source)
    (hcard : #(pendingRequests G W C) = mu) :
    ∃ (U : Set
          (protectedRequestWeb (G.quotient C)
            (pendingRequests G W C) reserve).DPath)
        (D : Set V),
      IsHalfwayLinkageOfAltitude
          (protectedRequestWeb (G.quotient C)
            (pendingRequests G W C) reserve)
          (pendingRequests G W C) mu U ∧
        IsSeparatingHalfwayStopover
          (protectedRequestWeb (G.quotient C)
            (pendingRequests G W C) reserve) U D ∧
        HeightAtMost
          (protectedRequestWeb (G.quotient C)
            (pendingRequests G W C) reserve) D mu := by
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  obtain ⟨U, D, hU, hD, hheight⟩ :=
    exists_protectedHalfwayBatch_of_lower hlower hmu hmuInfinite
      (G.quotient C) hquotient
      (DWeb.NoEdgeEnters.quotient G hNoEnter)
      hcurrent hreserve hcard
  exact ⟨U, D, hU, hD, hheight⟩

end SingularSafeBatch
end CardinalInduction
end Erdos599
