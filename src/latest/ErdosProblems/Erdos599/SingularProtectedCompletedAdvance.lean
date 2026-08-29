/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularProtectedCompletedState
import ErdosProblems.Erdos599.RegularProtectedAmbientRebuild
import ErdosProblems.Erdos599.SafeLinkGroundFinal

/-!
# Installing one protected batch without ambient deletion safety

The source-star construction returns two disjoint residual families: new
target paths and a clean complementary linkage to a trimmed separator.
The new target carrier is roofed by that separator. We delete that carrier,
restrict the pending family, and lift the completed paths into the original
web. Only quotient unhinderedness is used or retained.
-/

noncomputable section

open Set Cardinal

namespace Erdos599.CardinalInduction.SingularProtectedCompletedAdvance

open SingularCompletedDisplayEventualRows SingularProtectedCompletedState
  SingularContinuation RegularProtectedDeltaLift

universe u

variable {V : Type u}

/-- Normalization upgrades finite source-rooted target-ending paths to
endpoint-pure linkage paths. -/
theorem targetLinkage_of_structure
    {G : DWeb V} (hNorm : G.IsNormalized) {A : Set V} {P : Set G.DPath}
    (hAsub : A ⊆ G.source) (hPwarp : G.IsWarp P)
    (hPfinite : G.HasFiniteCharacter P) (hPinitial : G.initialSet P = A)
    (hPterminal : G.terminalFrontier P ⊆ G.target) :
    IsLinkageBetween G A G.target P := by
  refine ⟨hPwarp, hPfinite, hPinitial, hPterminal, ?_⟩
  intro p hp
  obtain ⟨f, rfl⟩ := hPfinite hp
  have hstart : f.start ∈ A := by
    rw [← hPinitial]
    exact ⟨.inl f, hp, rfl⟩
  have hfinish : f.finish ∈ G.target := hPterminal ⟨.inl f, hp, rfl⟩
  have hsource : f.support ∩ A = {f.start} := by
    ext x
    constructor
    · rintro ⟨hxf, hxA⟩
      exact Set.mem_singleton_iff.2
        (hNorm.eq_initial_of_mem_path (.inl f) hxf (hAsub hxA))
    · intro hx
      have hxa := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨f.start_mem_support, hstart⟩
  have htarget : f.support ∩ G.target = {f.finish} := by
    ext x
    constructor
    · rintro ⟨hxf, hxTarget⟩
      exact Set.mem_singleton_iff.2
        (Option.some.inj (hNorm.terminal?_eq_of_mem_path (.inl f) hxf hxTarget)).symm
    · intro hx
      have hxf := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨f.finish_mem_support, hfinish⟩
  refine ⟨f, rfl, ?_, hsource⟩
  rw [Set.inter_union_distrib_left, hsource, htarget]
  ext x
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]

/-- Concrete output of the residual source-star split, before installing
its new completed carrier in the original ambient web. -/
structure ResidualProtectedBatch (H : DWeb V) where
  sources : Set V
  sources_subset : sources ⊆ H.source
  targetPaths : Set H.DPath
  target_linkage : IsLinkageBetween H sources H.target targetPaths
  boundary : Set V
  pending : Set H.DPath
  pending_linkage : IsLinkageBetween H (H.source \ sources) boundary pending
  pending_clean : TerminalCleanAt H pending boundary
  families_disjoint : Disjoint (H.vertexSet pending) (H.vertexSet targetPaths)
  boundary_separator : IsSeparatorFrom H H.source boundary
  boundary_trimmed : IsTrimmedSeparator H boundary
  quotient_unhindered : (H.quotient boundary).IsUnhindered
  target_carrier_roof : H.vertexSet targetPaths ⊆ H.roof boundary

namespace ResidualProtectedBatch

variable {H : DWeb V}

/-- Source purity identifies the source after deleting the new target
carrier. No unhinderedness premise is involved. -/
theorem deleted_source (Q : ResidualProtectedBatch H) (hNorm : H.IsNormalized) :
    (H.delete (H.vertexSet Q.targetPaths)).source = H.source \ Q.sources := by
  ext a
  change (a ∈ H.source ∧ a ∉ H.vertexSet Q.targetPaths) ↔
    a ∈ H.source ∧ a ∉ Q.sources
  constructor
  · rintro ⟨ha, haCarrier⟩
    refine ⟨ha, ?_⟩
    intro haQ
    rw [← Q.target_linkage.initialSet_eq] at haQ
    obtain ⟨p, hp, hpa⟩ := haQ
    exact haCarrier ⟨p, hp, hpa ▸ p.initial_mem_support⟩
  · rintro ⟨ha, haQ⟩
    refine ⟨ha, ?_⟩
    rintro ⟨p, hp, hap⟩
    apply haQ
    rw [← Q.target_linkage.initialSet_eq]
    exact ⟨p, hp, (hNorm.eq_initial_of_mem_path p hap ha).symm⟩

/-- The pending complementary linkage retypes to the new deletion. -/
theorem restricted_pending_linkage (Q : ResidualProtectedBatch H)
    (hNorm : H.IsNormalized) :
    IsLinkageBetween (H.delete (H.vertexSet Q.targetPaths))
      (H.delete (H.vertexSet Q.targetPaths)).source
      (Q.boundary \ H.vertexSet Q.targetPaths)
      (H.restrictDeleteFamily (H.vertexSet Q.targetPaths) Q.pending
        Q.families_disjoint) := by
  rw [Q.deleted_source hNorm]
  exact RegularProtectedAmbientRebuild.IsLinkageBetween.restrictDeleteFamily
    H _ Q.pending_linkage Q.families_disjoint

/-- All three new boundary facts follow from a roofed deletion. -/
theorem deleted_boundary (Q : ResidualProtectedBatch H) :
    IsSeparatorFrom (H.delete (H.vertexSet Q.targetPaths))
        (H.delete (H.vertexSet Q.targetPaths)).source
        (Q.boundary \ H.vertexSet Q.targetPaths) ∧
      IsTrimmedSeparator (H.delete (H.vertexSet Q.targetPaths))
        (Q.boundary \ H.vertexSet Q.targetPaths) ∧
      ((H.delete (H.vertexSet Q.targetPaths)).quotient
        (Q.boundary \ H.vertexSet Q.targetPaths)).IsUnhindered := by
  refine ⟨?_, H.delete_essential_sdiff_eq_of_subset_roof
    Q.target_carrier_roof Q.boundary_trimmed, ?_⟩
  · change (H.delete (H.vertexSet Q.targetPaths)).source ⊆
      (H.delete (H.vertexSet Q.targetPaths)).roof
        (Q.boundary \ H.vertexSet Q.targetPaths)
    rw [H.delete_roof_sdiff_eq_of_subset_roof
      Q.target_carrier_roof Q.boundary_trimmed]
    exact Set.sdiff_subset.trans Q.boundary_separator
  · have h := H.delete_quotient_isUnhindered_of_subset_roof
      Q.target_carrier_roof Q.boundary_trimmed Q.boundary_separator
      Q.quotient_unhindered
    rw [H.delete_quotient_eq_quotient_delete_inter_of_subset_roof
      Q.target_carrier_roof Q.boundary_trimmed Q.boundary_separator] at h
    rw [H.delete_quotient_sdiff_eq_quotient_delete_inter_of_subset_roof
      Q.target_carrier_roof Q.boundary_trimmed Q.boundary_separator]
    exact h

end ResidualProtectedBatch

/-- Install the residual batch. The old completed paths are literally
retained, and the new source set is exactly their union with the batch's
owners, which may include more than the originally requested sources. -/
theorem exists_advance
    {G : DWeb V} (hNorm : G.IsNormalized) (S : ProtectedCompletedState G)
    (Q : ResidualProtectedBatch S.residual) :
    ∃ T : ProtectedCompletedState G,
      T.sources = S.sources ∪ Q.sources ∧
      T.completed = S.completed ∪
        G.liftDeleteFamily (G.vertexSet S.completed) Q.targetPaths := by
  let X := G.vertexSet S.completed
  let H := S.residual
  let R : Set G.DPath := G.liftDeleteFamily X Q.targetPaths
  let A : Set V := S.sources ∪ Q.sources
  let P : Set G.DPath := S.completed ∪ R
  have hAsub : A ⊆ G.source :=
    Set.union_subset S.sources_subset (Q.sources_subset.trans Set.sdiff_subset)
  have hQR : IsLinkageBetween G Q.sources H.target R :=
    IsLinkageBetween.liftDeleteFamily G X Q.target_linkage
  have hRavoid : Disjoint (G.vertexSet R) X := by
    apply G.vertexSet_liftDeleteFamily_disjoint
    rw [Q.target_linkage.initialSet_eq]
    exact Q.sources_subset
  have hPwarp : G.IsWarp P := by
    apply Set.PairwiseDisjoint.union S.linkage.isWarp hQR.isWarp
    intro p hp q hq _hpq
    apply Set.disjoint_left.2
    intro x hxp hxq
    exact Set.disjoint_left.1 hRavoid ⟨q, hq, hxq⟩ ⟨p, hp, hxp⟩
  have hPfinite : G.HasFiniteCharacter P :=
    finiteCharacter_union G S.linkage.finiteCharacter hQR.finiteCharacter
  have hPinitial : G.initialSet P = A := by
    rw [G.initialSet_union, S.linkage.initialSet_eq, hQR.initialSet_eq]
  have hPterminal : G.terminalFrontier P ⊆ G.target := by
    rw [G.terminalFrontier_union]
    exact Set.union_subset S.linkage.terminalFrontier_subset
      (hQR.terminalFrontier_subset.trans Set.sdiff_subset)
  have hPlink : IsLinkageBetween G A G.target P := by
    exact targetLinkage_of_structure hNorm hAsub hPwarp hPfinite hPinitial hPterminal
  let Y := H.vertexSet Q.targetPaths
  let D := Q.boundary \ Y
  have hvertex : G.vertexSet P = X ∪ Y := by
    dsimp only [P, R, X, Y, H, ProtectedCompletedState.residual]
    rw [G.vertexSet_union, SafeLinkGroundFinal.DWeb.vertexSet_liftDeleteFamily]
  have hres : G.delete (G.vertexSet P) = H.delete Y := by
    rw [hvertex, ← G.delete_delete]
  have hHNorm : H.IsNormalized := S.residual_normalized hNorm
  have hdata : ∃ W : Set (G.delete (G.vertexSet P)).DPath,
      IsLinkageBetween (G.delete (G.vertexSet P))
        (G.delete (G.vertexSet P)).source D W ∧
      TerminalCleanAt (G.delete (G.vertexSet P)) W D := by
    rw [hres]
    refine ⟨H.restrictDeleteFamily Y Q.pending Q.families_disjoint,
      Q.restricted_pending_linkage hHNorm, ?_⟩
    exact RegularProtectedAmbientRebuild.terminalCleanAt_restrictDeleteFamily
      H Y Q.boundary Q.families_disjoint Q.pending_clean
  obtain ⟨W, hW, hWclean⟩ := hdata
  have hgeometry : IsSeparatorFrom (G.delete (G.vertexSet P))
        (G.delete (G.vertexSet P)).source D ∧
      IsTrimmedSeparator (G.delete (G.vertexSet P)) D ∧
      ((G.delete (G.vertexSet P)).quotient D).IsUnhindered := by
    rw [hres]
    exact Q.deleted_boundary
  exact ⟨{
    sources := A
    sources_subset := hAsub
    completed := P
    linkage := hPlink
    boundary := D
    pending := W
    pending_linkage := hW
    pending_clean := hWclean
    boundary_separator := hgeometry.1
    boundary_trimmed := hgeometry.2.1
    quotient_unhindered := hgeometry.2.2 }, rfl, rfl⟩

#print axioms ResidualProtectedBatch.deleted_boundary
#print axioms exists_advance

end Erdos599.CardinalInduction.SingularProtectedCompletedAdvance
