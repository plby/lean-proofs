/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularPendingReentry
import ErdosProblems.Erdos599.SingularBoundarySplit

/-!
# Roofed frozen components need no deletion certificate

In a singular successor, a quotient path can meet the old roof only at its
initial vertex.  If its initial vertex is the terminal of a continued pending
component, warp disjointness rules out that vertex on every other frozen old
component.  Consequently a frozen family which is already roofed at the old
boundary is automatically disjoint from the new frontier continuation.

This is sharper than the deleted-carrier interface: only the non-roofed part
of the frozen carrier has to be protected by a safe deletion.  No terminal-
clean hypothesis on the frozen family is needed.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularRoofedFrozenAvoidance

open SingularContinuation SingularPendingReentry SliceSpliceSource
  SingularBoundarySplit SingularPendingDecomposition SingularExtension

universe u

variable {V : Type u}

/-- A lifted quotient family whose initials are terminals of `P` is disjoint
from every old family `F` which is both disjoint from `P` and roofed by the
old boundary.  Terminal cleanliness of `F` is unnecessary. -/
theorem disjoint_roofed_frontierContinuation
    (G : DWeb V) {F P : Set G.DPath} {C : Set V}
    (hFP : Disjoint (G.vertexSet F) (G.vertexSet P))
    (hFroof : G.vertexSet F ⊆ G.roof C)
    (hPwarp : G.IsWarp P)
    (hProof : G.vertexSet P ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    {U : Set (G.quotient C).DPath}
    (hUstart : (G.quotient C).initialSet U ⊆
      G.terminalFrontier P) :
    Disjoint (G.vertexSet F)
      (G.vertexSet (frontierContinuation G hPwarp hProof htrim
        U hUstart)) := by
  let L := liftedQuotientFamily G C U
  let hc : G.StarCompatible P L :=
    starCompatible_liftQuotientFamily_of_frontier
      G hPwarp hProof htrim hUstart
  apply Set.disjoint_left.2
  intro x hxF hxContinuation
  have hxStar : x ∈ G.vertexSet (G.star hc) := hxContinuation
  rcases vertexSet_star_subset_union hc hxStar with hxP | hxL
  · exact Set.disjoint_left.1 hFP hxF hxP
  · obtain ⟨q, hqL, hxq⟩ := hxL
    obtain ⟨q₀, hq₀U, rfl⟩ := hqL
    have hxClass := G.quotientPath_support_initial_or_avoids C q₀ (by
      simpa only [G.support_liftQuotientPath] using hxq)
    have hxInitial : x = q₀.initial := by
      rcases hxClass with hx | hxAvoid
      · exact hx
      · exfalso
        have hxRoof : x ∈ G.roof C := hFroof hxF
        by_cases hxEssential : x ∈ G.essential C
        · exact hxAvoid.2 (htrim ▸ hxEssential)
        · exact hxAvoid.1 ⟨hxRoof, hxEssential⟩
    have hqInitial : q₀.initial ∈ (G.quotient C).initialSet U :=
      ⟨q₀, hq₀U, rfl⟩
    obtain ⟨p, hpP, hpTerminal⟩ := hUstart hqInitial
    apply Set.disjoint_left.1 hFP hxF
    refine ⟨p, hpP, ?_⟩
    exact hxInitial ▸ G.terminal_mem_support hpTerminal

/-- Structural frozen continuation without a deletion step when the frozen
family is roofed.  This is the direct consumer form of
`disjoint_roofed_frontierContinuation`. -/
theorem frozenFrontierContinuation_structural_of_roofed
    (G : DWeb V) {F P : Set G.DPath} {C : Set V}
    (hF : G.IsWarp F) (hP : G.IsWarp P)
    (hFfinite : G.HasFiniteCharacter F)
    (hPfinite : G.HasFiniteCharacter P)
    (hFP : Disjoint (G.vertexSet F) (G.vertexSet P))
    (hFroof : G.vertexSet F ⊆ G.roof C)
    (hProof : G.vertexSet P ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    {U : Set (G.quotient C).DPath}
    (hU : (G.quotient C).IsWarp U)
    (hUfinite : (G.quotient C).HasFiniteCharacter U)
    (hUinitial : (G.quotient C).initialSet U =
      G.terminalFrontier P) :
    G.IsWarp
        (frozenFrontierContinuation G F hP hProof htrim U hUinitial.le) ∧
      G.HasFiniteCharacter
        (frozenFrontierContinuation G F hP hProof htrim U hUinitial.le) ∧
      G.ForwardExtension (F ∪ P)
        (frozenFrontierContinuation G F hP hProof htrim U hUinitial.le) ∧
      G.initialSet
        (frozenFrontierContinuation G F hP hProof htrim U hUinitial.le) =
        G.initialSet (F ∪ P) := by
  apply frozenFrontierContinuation_structural G hF hP hFfinite hPfinite
    hProof htrim hU hUfinite hUinitial
  exact disjoint_roofed_frontierContinuation G hFP hFroof hP hProof
    htrim hUinitial.le

/-! ## Mixed frozen families

Only the genuinely non-roofed part of a frozen family must be put into the
deleted set.  The roofed remainder is protected by the preceding theorem.
-/

/-- Split the frozen family into a protected part `D` whose carrier is in
the deleted set and an automatically safe roofed part `R`. -/
theorem disjoint_protected_union_roofed_frontierContinuation
    (G : DWeb V) {D R P : Set G.DPath} {C Q : Set V}
    (hDP : Disjoint (G.vertexSet D) (G.vertexSet P))
    (hDQ : G.vertexSet D ⊆ Q)
    (hRP : Disjoint (G.vertexSet R) (G.vertexSet P))
    (hRroof : G.vertexSet R ⊆ G.roof C)
    (hPwarp : G.IsWarp P)
    (hProof : G.vertexSet P ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    {U : Set ((G.delete Q).quotient C).DPath}
    (hstart : ((G.delete Q).quotient C).initialSet U ⊆
      ((G.delete Q).quotient C).source)
    (hLiftStart : (G.quotient C).initialSet
        (SingularExtension.deletedQuotientFamily G C Q U) ⊆
      G.terminalFrontier P) :
    Disjoint (G.vertexSet (D ∪ R))
      (G.vertexSet (frontierContinuation G hPwarp hProof htrim
        (SingularExtension.deletedQuotientFamily G C Q U)
        hLiftStart)) := by
  rw [G.vertexSet_union]
  apply Set.disjoint_union_left.mpr
  refine ⟨?_, ?_⟩
  · exact
      disjoint_frozen_frontierContinuation_deletedQuotientFamily
        G hDP hDQ hPwarp hProof htrim hstart hLiftStart
  · exact disjoint_roofed_frontierContinuation G hRP hRroof hPwarp
      hProof htrim hLiftStart

/-- Structural form of the mixed protected/roofed decomposition. -/
theorem frozenFrontierContinuation_structural_of_protected_union_roofed
    (G : DWeb V) {D R P : Set G.DPath} {C Q : Set V}
    (hFrozen : G.IsWarp (D ∪ R)) (hP : G.IsWarp P)
    (hFrozenFinite : G.HasFiniteCharacter (D ∪ R))
    (hPfinite : G.HasFiniteCharacter P)
    (hDP : Disjoint (G.vertexSet D) (G.vertexSet P))
    (hDQ : G.vertexSet D ⊆ Q)
    (hRP : Disjoint (G.vertexSet R) (G.vertexSet P))
    (hRroof : G.vertexSet R ⊆ G.roof C)
    (hProof : G.vertexSet P ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    {U : Set ((G.delete Q).quotient C).DPath}
    (hU : ((G.delete Q).quotient C).IsWarp U)
    (hUfinite : ((G.delete Q).quotient C).HasFiniteCharacter U)
    (hstart : ((G.delete Q).quotient C).initialSet U ⊆
      ((G.delete Q).quotient C).source)
    (hLiftInitial : (G.quotient C).initialSet
        (SingularExtension.deletedQuotientFamily G C Q U) =
      G.terminalFrontier P) :
    let L := SingularExtension.deletedQuotientFamily G C Q U
    G.IsWarp
        (frozenFrontierContinuation G (D ∪ R) hP hProof htrim L
          hLiftInitial.le) ∧
      G.HasFiniteCharacter
        (frozenFrontierContinuation G (D ∪ R) hP hProof htrim L
          hLiftInitial.le) ∧
      G.ForwardExtension ((D ∪ R) ∪ P)
        (frozenFrontierContinuation G (D ∪ R) hP hProof htrim L
          hLiftInitial.le) ∧
      G.initialSet
        (frozenFrontierContinuation G (D ∪ R) hP hProof htrim L
          hLiftInitial.le) = G.initialSet ((D ∪ R) ∪ P) := by
  dsimp only
  let L := SingularExtension.deletedQuotientFamily G C Q U
  have hLwarp : (G.quotient C).IsWarp L :=
    SingularExtension.deletedQuotientFamily_isWarp hU
  have hLfinite : (G.quotient C).HasFiniteCharacter L :=
    SingularExtension.deletedQuotientFamily_hasFiniteCharacter hUfinite
  apply frozenFrontierContinuation_structural G hFrozen hP
    hFrozenFinite hPfinite hProof htrim hLwarp hLfinite hLiftInitial
  exact disjoint_protected_union_roofed_frontierContinuation G hDP hDQ
    hRP hRroof hP hProof htrim hstart hLiftInitial.le

/-! ## The canonical boundary-start decomposition

For a subfamily of a genuine source row, every component starts either
strictly outside the boundary or on the boundary.  The former part is
automatically roofed.  Thus a safe-deletion certificate is required only
for the boundary-starting part of a frozen family.
-/

/-- A subfamily of a full source row is the union of its outside-starting
and boundary-starting pieces. -/
theorem outsidePart_union_boundaryPart_of_subset
    (G : DWeb V) {W F : Set G.DPath} {C : Set V}
    (hWinitial : G.initialSet W = G.source) (hFsub : F ⊆ W) :
    outsidePart G F C ∪
        initialRestriction G F (G.source ∩ C) = F := by
  apply Set.Subset.antisymm
  · exact Set.union_subset (fun _ h ↦ h.1) (fun _ h ↦ h.1)
  · intro p hpF
    have hpSource : p.initial ∈ G.source := by
      rw [← hWinitial]
      exact ⟨p, hFsub hpF, rfl⟩
    by_cases hpC : p.initial ∈ C
    · exact Or.inr ⟨hpF, hpSource, hpC⟩
    · exact Or.inl ⟨hpF, hpSource, hpC⟩

/-- The outside-starting part of a subfamily of a separating source row is
roofed, even though the subfamily need not itself cover the whole source. -/
theorem outsidePart_subfamily_vertexSet_subset_roof
    {G : DWeb V} {W F : Set G.DPath} {C : Set V}
    (hW : IsLinkageBetween G G.source C W)
    (hsep : IsSeparatorFrom G G.source C) (hFsub : F ⊆ W) :
    G.vertexSet (outsidePart G F C) ⊆ G.roof C := by
  intro x hx
  apply outsidePart_vertexSet_subset_roof hW hsep
  obtain ⟨p, hp, hxp⟩ := hx
  exact ⟨p, ⟨hFsub hp.1, hp.2⟩, hxp⟩

/-- Canonical mixed frozen continuation.  For a frozen subfamily `F` of an
actual source-to-`C` linkage, only the components whose initial vertices lie
in `C` have to be included in the protected deletion `Q`; all other frozen
components are automatically invisible to the quotient continuation.

This is the construction-facing sharpening of the arbitrary-row successor:
the safety obligation is concentrated exactly on the boundary-starting
components which survive the roof argument. -/
theorem frozenFrontierContinuation_structural_protect_boundaryStarts
    (G : DWeb V) {W F P : Set G.DPath} {C Q : Set V}
    (hW : IsLinkageBetween G G.source C W)
    (hsep : IsSeparatorFrom G G.source C)
    (hFsub : F ⊆ W)
    (hF : G.IsWarp F) (hP : G.IsWarp P)
    (hFfinite : G.HasFiniteCharacter F)
    (hPfinite : G.HasFiniteCharacter P)
    (hFP : Disjoint (G.vertexSet F) (G.vertexSet P))
    (hBoundaryQ :
      G.vertexSet (initialRestriction G F (G.source ∩ C)) ⊆ Q)
    (hProof : G.vertexSet P ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    {U : Set ((G.delete Q).quotient C).DPath}
    (hU : ((G.delete Q).quotient C).IsWarp U)
    (hUfinite : ((G.delete Q).quotient C).HasFiniteCharacter U)
    (hstart : ((G.delete Q).quotient C).initialSet U ⊆
      ((G.delete Q).quotient C).source)
    (hLiftInitial : (G.quotient C).initialSet
        (SingularExtension.deletedQuotientFamily G C Q U) =
      G.terminalFrontier P) :
    let L := SingularExtension.deletedQuotientFamily G C Q U
    G.IsWarp
        (frozenFrontierContinuation G F hP hProof htrim L
          hLiftInitial.le) ∧
      G.HasFiniteCharacter
        (frozenFrontierContinuation G F hP hProof htrim L
          hLiftInitial.le) ∧
      G.ForwardExtension (F ∪ P)
        (frozenFrontierContinuation G F hP hProof htrim L
          hLiftInitial.le) ∧
      G.initialSet
        (frozenFrontierContinuation G F hP hProof htrim L
          hLiftInitial.le) = G.initialSet (F ∪ P) := by
  dsimp only
  let D := initialRestriction G F (G.source ∩ C)
  let R := outsidePart G F C
  have hsplit : R ∪ D = F := by
    exact outsidePart_union_boundaryPart_of_subset G
      hW.initialSet_eq hFsub
  have hFrozen : G.IsWarp (D ∪ R) := by
    rw [Set.union_comm, hsplit]
    exact hF
  have hFrozenFinite : G.HasFiniteCharacter (D ∪ R) := by
    rw [Set.union_comm, hsplit]
    exact hFfinite
  have hDcarrier : G.vertexSet D ⊆ G.vertexSet F := by
    rintro x ⟨p, hp, hxp⟩
    exact ⟨p, hp.1, hxp⟩
  have hRcarrier : G.vertexSet R ⊆ G.vertexSet F := by
    rintro x ⟨p, hp, hxp⟩
    exact ⟨p, hp.1, hxp⟩
  have hDP : Disjoint (G.vertexSet D) (G.vertexSet P) :=
    hFP.mono_left hDcarrier
  have hRP : Disjoint (G.vertexSet R) (G.vertexSet P) :=
    hFP.mono_left hRcarrier
  have hRroof : G.vertexSet R ⊆ G.roof C :=
    outsidePart_subfamily_vertexSet_subset_roof hW hsep hFsub
  have hresult :=
    frozenFrontierContinuation_structural_of_protected_union_roofed
      G hFrozen hP hFrozenFinite hPfinite hDP hBoundaryQ hRP hRroof
        hProof htrim hU hUfinite hstart hLiftInitial
  simpa only [Set.union_comm D R, hsplit] using hresult

/-! ## Only completed boundary starts need protection

In the split row used by the singular construction, every boundary-starting
pending component is normalized to a trivial path.  Such a component is
supported in `C`, hence is roofed by `C`.  Consequently the protected part
of the preceding theorem can be reduced once more, to the *completed* part
of the boundary-starting frozen family.
-/

/-- The pending part of a boundary-starting restriction is roofed whenever
all boundary-starting pending members of the ambient row are trivial. -/
theorem pending_boundaryRestriction_vertexSet_subset_roof
    (G : DWeb V) {W F : Set G.DPath} {C : Set V}
    (hFsub : F ⊆ W)
    (htrivial : ∀ p ∈ boundaryPendingPart G W C,
      p = G.trivialPath p.initial) :
    G.vertexSet
        (pendingPart G (initialRestriction G F (G.source ∩ C))) ⊆
      G.roof C := by
  rintro x ⟨p, hpPending, hxp⟩
  have hpPendingW : p ∈ pendingPart G W := by
    refine ⟨hFsub hpPending.1.1, ?_⟩
    intro hpCompletedW
    exact hpPending.2 ⟨hpPending.1, hpCompletedW.2⟩
  have hpBoundary : p ∈ boundaryPendingPart G W C :=
    ⟨hpPendingW, hpPending.1.2⟩
  have hpEq := htrivial p hpBoundary
  rw [hpEq, G.support_trivialPath] at hxp
  apply G.subset_roof C
  exact hxp ▸ hpPending.1.2.2

/-- Canonical frozen continuation in a split row: among components starting
on the old boundary, only those already completed at the ambient target
must lie in the protected deletion.  Boundary-starting pending components
are trivial and join the automatically roofed part. -/
theorem frozenFrontierContinuation_structural_protect_completedBoundaryStarts
    (G : DWeb V) {W F P : Set G.DPath} {C Q : Set V}
    (hW : IsLinkageBetween G G.source C W)
    (hsep : IsSeparatorFrom G G.source C)
    (hFsub : F ⊆ W)
    (hF : G.IsWarp F) (hP : G.IsWarp P)
    (hFfinite : G.HasFiniteCharacter F)
    (hPfinite : G.HasFiniteCharacter P)
    (hFP : Disjoint (G.vertexSet F) (G.vertexSet P))
    (htrivial : ∀ p ∈ boundaryPendingPart G W C,
      p = G.trivialPath p.initial)
    (hCompletedBoundaryQ :
      G.vertexSet (completedPart G
        (initialRestriction G F (G.source ∩ C))) ⊆ Q)
    (hProof : G.vertexSet P ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    {U : Set ((G.delete Q).quotient C).DPath}
    (hU : ((G.delete Q).quotient C).IsWarp U)
    (hUfinite : ((G.delete Q).quotient C).HasFiniteCharacter U)
    (hstart : ((G.delete Q).quotient C).initialSet U ⊆
      ((G.delete Q).quotient C).source)
    (hLiftInitial : (G.quotient C).initialSet
        (SingularExtension.deletedQuotientFamily G C Q U) =
      G.terminalFrontier P) :
    let L := SingularExtension.deletedQuotientFamily G C Q U
    G.IsWarp
        (frozenFrontierContinuation G F hP hProof htrim L
          hLiftInitial.le) ∧
      G.HasFiniteCharacter
        (frozenFrontierContinuation G F hP hProof htrim L
          hLiftInitial.le) ∧
      G.ForwardExtension (F ∪ P)
        (frozenFrontierContinuation G F hP hProof htrim L
          hLiftInitial.le) ∧
      G.initialSet
        (frozenFrontierContinuation G F hP hProof htrim L
          hLiftInitial.le) = G.initialSet (F ∪ P) := by
  dsimp only
  let D := initialRestriction G F (G.source ∩ C)
  let E := completedPart G D
  let B := pendingPart G D
  let R := outsidePart G F C
  let R₀ := R ∪ B
  have hRD : R ∪ D = F := by
    exact outsidePart_union_boundaryPart_of_subset G
      hW.initialSet_eq hFsub
  have hEB : E ∪ B = D := by
    exact completedPart_union_pendingPart G D
  have hsplit : E ∪ R₀ = F := by
    dsimp only [R₀]
    rw [Set.union_left_comm E R B, hEB, hRD]
  have hFrozen : G.IsWarp (E ∪ R₀) := by
    rw [hsplit]
    exact hF
  have hFrozenFinite : G.HasFiniteCharacter (E ∪ R₀) := by
    rw [hsplit]
    exact hFfinite
  have hEcarrier : G.vertexSet E ⊆ G.vertexSet F := by
    rintro x ⟨p, hp, hxp⟩
    exact ⟨p, hp.1.1, hxp⟩
  have hRcarrier : G.vertexSet R ⊆ G.vertexSet F := by
    rintro x ⟨p, hp, hxp⟩
    exact ⟨p, hp.1, hxp⟩
  have hBcarrier : G.vertexSet B ⊆ G.vertexSet F := by
    rintro x ⟨p, hp, hxp⟩
    exact ⟨p, hp.1.1, hxp⟩
  have hR₀carrier : G.vertexSet R₀ ⊆ G.vertexSet F := by
    rw [G.vertexSet_union]
    exact Set.union_subset hRcarrier hBcarrier
  have hEP : Disjoint (G.vertexSet E) (G.vertexSet P) :=
    hFP.mono_left hEcarrier
  have hR₀P : Disjoint (G.vertexSet R₀) (G.vertexSet P) :=
    hFP.mono_left hR₀carrier
  have hRroof : G.vertexSet R ⊆ G.roof C :=
    outsidePart_subfamily_vertexSet_subset_roof hW hsep hFsub
  have hBroof : G.vertexSet B ⊆ G.roof C := by
    exact pending_boundaryRestriction_vertexSet_subset_roof
      G hFsub htrivial
  have hR₀roof : G.vertexSet R₀ ⊆ G.roof C := by
    rw [G.vertexSet_union]
    exact Set.union_subset hRroof hBroof
  have hresult :=
    frozenFrontierContinuation_structural_of_protected_union_roofed
      G hFrozen hP hFrozenFinite hPfinite hEP hCompletedBoundaryQ
        hR₀P hR₀roof hProof htrim hU hUfinite hstart hLiftInitial
  simpa only [hsplit] using hresult

end SingularRoofedFrozenAvoidance
end CardinalInduction
end Erdos599
