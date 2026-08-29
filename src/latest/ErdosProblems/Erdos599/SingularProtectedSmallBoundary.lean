/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularProtectedCompletedAdvance
import ErdosProblems.Erdos599.SingularProtectedCompletedRecursion

/-!
# Completing a singular column whose pending boundary is small

The lower extension clause links the whole source of the unhindered boundary
quotient. A clean source star then finishes every remaining ambient source.
This case uses no half-way clause and no assumption that the deleted ambient
web itself is unhindered.
-/

noncomputable section

open Set Cardinal

namespace Erdos599.CardinalInduction.SingularProtectedSmallBoundary

open SingularProtectedCompletedState SingularProtectedCompletedAdvance
  SingularProtectedCompletedRecursion SingularContinuation
  RegularProtectedAmbientRebuild

universe u

variable {V : Type u}

/-- A full target linkage is a residual protected batch with no pending
paths. The ambient target itself is a trimmed separating boundary. -/
def batchOfFullLinkage (H : DWeb V) {P : Set H.DPath}
    (hP : IsLinkageBetween H H.source H.target P) : ResidualProtectedBatch H where
  sources := H.source
  sources_subset := Set.Subset.rfl
  targetPaths := P
  target_linkage := hP
  boundary := H.target
  pending := ∅
  pending_linkage := by simpa only [Set.sdiff_self] using empty_linkage H
  pending_clean := by intro p hp; exact hp.elim
  families_disjoint := by
    apply Set.disjoint_left.2
    rintro x ⟨p, hp, _⟩ _
    exact hp.elim
  boundary_separator := by
    rw [IsSeparatorFrom, roof_target]
    exact Set.subset_univ _
  boundary_trimmed := target_subset_isTrimmedSeparator Set.Subset.rfl
  quotient_unhindered := quotient_target_isUnhindered H
  target_carrier_roof := by rw [roof_target]; exact Set.subset_univ _

/-- Every full-source finite linkage injects its sources into the endpoint
boundary, regardless of the cardinality of the ambient vertex type. -/
theorem source_card_le_boundary
    {H : DWeb V} {R : Set H.DPath} {C : Set V}
    (hR : IsLinkageBetween H H.source C R) : #H.source ≤ #C := by
  have hRcard : #R ≤ #C := by
    apply FamilyTools.mk_le_of_pairwiseDisjoint_of_meets hR.isWarp
    intro p hp
    obtain ⟨f, rfl⟩ := hR.finiteCharacter hp
    exact ⟨f.finish, hR.terminalFrontier_subset ⟨.inl f, hp, rfl⟩,
      f.finish_mem_support⟩
  rw [← hR.initialSet_eq]
  exact (mk_initialSet_le_family H R).trans hRcard

/-- Full linkability above the clean boundary lifts to full linkability of
the pending ambient web, even when that ambient web may be hindered. -/
theorem isLinkable_of_quotient_linkable
    {H : DWeb V} (hNorm : H.IsNormalized) {C : Set V} {R : Set H.DPath}
    (hR : IsLinkageBetween H H.source C R)
    (hsep : IsSeparatorFrom H H.source C) (htrim : IsTrimmedSeparator H C)
    (hclean : TerminalCleanAt H R C)
    (hQ : IsLinkable (H.quotient C)) : IsLinkable H := by
  obtain ⟨U, hU⟩ := hQ
  let P := continuation H hR hsep htrim hclean U hU.initialSet_eq
  have hPwarp : H.IsWarp P := continuation_isWarp H hR hsep htrim hclean
    hU.isWarp hU.initialSet_eq
  have hPfinite : H.HasFiniteCharacter P :=
    continuation_finiteCharacter H hR hsep htrim hclean hU.finiteCharacter
      hU.initialSet_eq
  have hPinitial : H.initialSet P = H.source :=
    initialSet_continuation H hR hsep htrim hclean U hU.initialSet_eq
  have hPterminal : H.terminalFrontier P ⊆ H.target := by
    have h := terminalFrontier_continuation_subset H hR hsep htrim hclean
      hU.initialSet_eq
    rw [H.terminalFrontier_liftQuotientFamily] at h
    exact h.trans hU.terminalFrontier_subset
  exact ⟨P, targetLinkage_of_structure hNorm Set.Subset.rfl hPwarp hPfinite
    hPinitial hPterminal⟩

/-- If the boundary is below the induction cardinal, the lower extension
clause supplies the full quotient linkage required by the preceding lemma. -/
theorem residual_isLinkable_of_boundary_below
    {G : DWeb V} {kappa : Cardinal.{u}} (hNorm : G.IsNormalized)
    (hlower : ExtensionBelowFor G kappa) (S : ProtectedCompletedState G)
    (hC : #S.boundary < kappa) : IsLinkable S.residual := by
  let K := S.residual.quotient S.boundary
  have hKcard : #K.source < kappa := by
    change #(S.residual.quotient S.boundary).source < kappa
    rw [S.quotient_source]
    exact hC
  have hext : ExtensionClauseAt K #K.source :=
    hlower #K.source hKcard K
      (fun {_ _} hxy ↦ S.residual_adj_imp hxy.1) S.quotient_unhindered
  have hKlink := linkable_of_extension_at_source_card K hext
  exact isLinkable_of_quotient_linkable (S.residual_normalized hNorm)
    S.pending_linkage S.boundary_separator S.boundary_trimmed S.pending_clean hKlink

/-- The small-boundary branch of the actual bounded successor. It finishes
all remaining sources while retaining every old completed target path. -/
theorem exists_boundedSuccessor_of_smallBoundary
    {G : DWeb V} {kappa rho : Cardinal.{u}} (hNorm : G.IsNormalized)
    (hlower : ExtensionBelowFor G kappa) (S : ProtectedCompletedState G)
    {requested : Set V} (hrequest : requested ⊆ G.source)
    (hrho : aleph0 ≤ rho) (hS : #S.sources ≤ rho)
    (hCsmall : #S.boundary ≤ rho) (hCbelow : #S.boundary < kappa) :
    Nonempty (BoundedProtectedSuccessor G rho S requested) := by
  obtain ⟨P, hP⟩ := residual_isLinkable_of_boundary_below hNorm hlower S hCbelow
  let Q := batchOfFullLinkage S.residual hP
  obtain ⟨T, hTsource, hTcompleted⟩ := exists_advance hNorm S Q
  have hunion : S.sources ∪ S.residual.source = G.source := by
    rw [S.residual_source hNorm, Set.union_comm,
      Set.sdiff_union_of_subset S.sources_subset]
  have hTfull : T.sources = G.source := hTsource.trans hunion
  have hTcard : #T.sources ≤ rho := by
    rw [hTsource]
    exact (Cardinal.mk_union_le S.sources S.residual.source).trans
      (Cardinal.add_le_of_le hrho hS
        ((source_card_le_boundary S.pending_linkage).trans hCsmall))
  exact ⟨{
    state := T
    requested_subset := hTfull.symm ▸ hrequest
    sources_le := hTcard
    completed_subset := by rw [hTcompleted]; exact Set.subset_union_left }⟩

#print axioms isLinkable_of_quotient_linkable
#print axioms exists_boundedSuccessor_of_smallBoundary

end Erdos599.CardinalInduction.SingularProtectedSmallBoundary
