/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularProtectedSplitSplice
import ErdosProblems.Erdos599.SingularProtectedSmallBoundary
import ErdosProblems.Erdos599.SingularBoundarySplit

/-!
# The corrected lower-cardinal singular successor

The lower half-way input is the actual protected split output, not an
exact-frontier linkage or a safely deletable full ambient batch. All lower
calls are restricted to edge subwebs of the original graph. A large pending
boundary uses the split source-star construction; a small boundary uses
only the lower extension clause and finishes every remaining source.
-/

noncomputable section

open Set Cardinal

namespace Erdos599.CardinalInduction.SingularProtectedLowerSelection

open Blueprint.LinkageBlueprint.CardinalInduction
open SingularProtectedCompletedState SingularProtectedCompletedAdvance
  SingularProtectedCompletedRecursion SingularProtectedSplitSplice
  SingularProtectedSmallBoundary RegularProtectedAmbientRebuild

universe u

variable {V : Type u}

/-- The half-way fragment of the corrected lower induction. It requires
only the construction's actual protected output and preserves original-edge
provenance for the hereditary subdivision argument. -/
def ProtectedHalfwayBelowFor (Base : DWeb V) (kappa : Cardinal.{u}) : Prop :=
  ∀ rho, rho < kappa → aleph0 ≤ rho → ∀ H : DWeb V,
    (∀ {x y : V}, H.graph.Adj x y → Base.graph.Adj x y) →
    H.IsNormalized → H.IsUnhindered →
    ∀ A0 : Set V, A0 ⊆ H.source → #A0 = rho →
      Nonempty (LocalizedProtectedHalfwayGeometry H A0 rho)

/-- Forget only the redundant whole-union and cardinal certificates when
installing the concrete splice in a protected state. -/
def ProtectedSplitSpliceResult.toResidualBatch
    {H : DWeb V} {rho : Cardinal.{u}} (Q : ProtectedSplitSpliceResult H rho) :
    ResidualProtectedBatch H where
  sources := Q.sources
  sources_subset := Q.sources_subset
  targetPaths := Q.targetPaths
  target_linkage := Q.target_linkage
  boundary := Q.boundary
  pending := Q.pending
  pending_linkage := Q.pending_linkage
  pending_clean := Q.pending_clean
  families_disjoint := Q.families_disjoint
  boundary_separator := Q.boundary_separator
  boundary_trimmed := Q.boundary_trimmed
  quotient_unhindered := Q.quotient_unhindered
  target_carrier_roof := Q.target_carrier_roof

/-- The explicit terminal request and the existing restricted-frontier
cardinality interface describe exactly the same set. -/
theorem requestedTerminalSet_eq_requestedFrontier
    (H : DWeb V) (R : Set H.DPath) (requested : Set V) :
    requestedTerminalSet H R requested =
      SingularBoundarySplit.requestedFrontier H R requested := by
  ext c
  constructor
  · rintro ⟨p, hp, hprequest, hpc⟩
    exact ⟨p, ⟨hp, hprequest⟩, hpc⟩
  · rintro ⟨p, ⟨hp, hprequest⟩, hpc⟩
    exact ⟨p, hp, hprequest, hpc⟩

/-- The large-boundary branch, with lower target paths attached only at
actual old terminals and all newly completed owners admitted. -/
theorem exists_boundedSuccessor_of_largeBoundary
    {G : DWeb V} {kappa rho : Cardinal.{u}} (hNorm : G.IsNormalized)
    (hhalf : ProtectedHalfwayBelowFor G kappa) (S : ProtectedCompletedState G)
    {requested : Set V} (hrhoKappa : rho < kappa) (hrho : aleph0 ≤ rho)
    (hcurrent : S.sources ⊆ requested) (hrequest : requested ⊆ G.source)
    (hrequestCard : #requested ≤ rho) (hC : rho ≤ #S.boundary) :
    Nonempty (BoundedProtectedSuccessor G rho S requested) := by
  let H := S.residual
  let K := H.quotient S.boundary
  let remaining := requested \ S.sources
  let terminals := requestedTerminalSet H S.pending remaining
  have hremaining : remaining ⊆ H.source := by
    rw [S.residual_source hNorm]
    exact fun _ hx ↦ ⟨hrequest hx.1, hx.2⟩
  have hterminals : terminals ⊆ K.source := by
    rw [S.quotient_source]
    rintro c ⟨p, hp, _hprequest, hpc⟩
    exact S.pending_linkage.terminalFrontier_subset ⟨p, hp, hpc⟩
  have hterminalCard : #terminals ≤ rho := by
    dsimp only [terminals]
    rw [requestedTerminalSet_eq_requestedFrontier]
    exact (SingularBoundarySplit.mk_requestedFrontier_le
      S.pending_linkage.isWarp).trans
        ((Cardinal.mk_subtype_mono Set.sdiff_subset).trans hrequestCard)
  have hKcard : rho ≤ #K.source := by
    rw [S.quotient_source]
    exact hC
  obtain ⟨A0, htermA0, hA0, hA0card⟩ :=
    SingularExtension.exists_enlargement_of_mk_le
      hterminals hterminalCard hrho hKcard
  have hHNorm : H.IsNormalized := S.residual_normalized hNorm
  have hKNorm : K.IsNormalized :=
    SingularExtension.DWeb.IsNormalized.quotient hHNorm _
  obtain ⟨D⟩ := hhalf rho hrhoKappa hrho K
    (fun {_ _} hxy ↦ S.residual_adj_imp hxy.1) hKNorm
    S.quotient_unhindered A0 hA0 hA0card
  let Q := protectedSplitSplice hHNorm S.pending_linkage
    S.boundary_separator S.boundary_trimmed S.pending_clean D
  have howners : remaining ⊆ Q.sources :=
    requested_subset_protectedSplitSplice_sources hHNorm S.pending_linkage
      S.boundary_separator S.boundary_trimmed S.pending_clean D hremaining htermA0
  have hQcard : #Q.sources ≤ rho := Q.sources_card.trans D.targetPaths_card
  obtain ⟨T, hTsource, hTcompleted⟩ := exists_advance hNorm S
    (ProtectedSplitSpliceResult.toResidualBatch Q)
  have hnewRequest : requested ⊆ T.sources := by
    rw [hTsource]
    intro a ha
    by_cases haOld : a ∈ S.sources
    · exact Or.inl haOld
    · exact Or.inr (howners ⟨ha, haOld⟩)
  have hTcard : #T.sources ≤ rho := by
    rw [hTsource]
    exact (Cardinal.mk_union_le S.sources Q.sources).trans
      (Cardinal.add_le_of_le hrho
        ((Cardinal.mk_subtype_mono hcurrent).trans hrequestCard) hQcard)
  exact ⟨{
    state := T
    requested_subset := hnewRequest
    sources_le := hTcard
    completed_subset := by rw [hTcompleted]; exact Set.subset_union_left }⟩

/-- The actual selector required by the completed-only countable matrix.
The two lower clauses have their true, separately stated interfaces. -/
theorem boundedProtectedSelection_of_lower
    {G : DWeb V} {kappa : Cardinal.{u}} (hNorm : G.IsNormalized)
    (hext : ExtensionBelowFor G kappa)
    (hhalf : ProtectedHalfwayBelowFor G kappa) :
    BoundedProtectedSelection G kappa := by
  intro rho S requested hrhoKappa hrho hcurrent hrequest hrequestCard
  by_cases hC : rho ≤ #S.boundary
  · exact exists_boundedSuccessor_of_largeBoundary hNorm hhalf S
      hrhoKappa hrho hcurrent hrequest hrequestCard hC
  · have hCrho : #S.boundary < rho := lt_of_not_ge hC
    exact exists_boundedSuccessor_of_smallBoundary hNorm hext S hrequest hrho
      ((Cardinal.mk_subtype_mono hcurrent).trans hrequestCard)
      hCrho.le (hCrho.trans hrhoKappa)

/-- The singular extension step under the corrected protected lower
induction, with no exact-frontier or ambient-deletion-safety assumption. -/
theorem extensionClauseAt_of_protectedLower
    (kappa : Cardinal.{u}) (hkappa : aleph0 < kappa) (hsingular : kappa.IsSingular)
    (G : DWeb V) (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    (hext : ExtensionBelowFor G kappa)
    (hhalf : ProtectedHalfwayBelowFor G kappa) : ExtensionClauseAt G kappa := by
  exact extensionClauseAt_of_boundedProtectedSelection kappa hkappa hsingular
    G hNorm hG (boundedProtectedSelection_of_lower hNorm hext hhalf)

#print axioms exists_boundedSuccessor_of_largeBoundary
#print axioms boundedProtectedSelection_of_lower
#print axioms extensionClauseAt_of_protectedLower

end Erdos599.CardinalInduction.SingularProtectedLowerSelection
