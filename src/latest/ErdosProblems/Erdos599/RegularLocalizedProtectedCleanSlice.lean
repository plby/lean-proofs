/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayLocalizedProtectedGeometry
import ErdosProblems.Erdos599.RegularProtectedAmbientRebuild
import ErdosProblems.Erdos599.RegularWeakProtectedSelectedClean
import ErdosProblems.Erdos599.SingularSafeCarrierCardinal

/-!
# Installing the localized protected half-way output

The fair half-way construction returns a completed source-root track `P`
and a terminal-clean complementary track `R`.  This file uses the *whole*
initial set of `P` as the selected coordinate, deletes the whole carrier of
`P`, invokes the protected ambient rebuild on `R`, and installs the result as
a genuine `CleanTargetSlice`.

No exact-frontier half-way assertion and no abstract provider is used.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace CardinalInduction
namespace RegularLocalizedProtectedCleanSlice

open DirectedPath
open SliceSpliceSource
open Blueprint.LinkageBlueprint.CardinalInduction

universe u
variable {V : Type u}

/-- The completed source-root family is an exact linkage from all of its
actual initials to the ambient target. -/
theorem LocalizedProtectedHalfwayGeometry.targetPaths_isLinkageBetween
    {Gamma : DWeb V} {A₀ : Set V} {rho : Cardinal.{u}}
    (D : LocalizedProtectedHalfwayGeometry Gamma A₀ rho)
    (hNorm : Gamma.IsNormalized) :
    IsLinkageBetween Gamma (Gamma.initialSet D.targetPaths)
      Gamma.target D.targetPaths := by
  refine ⟨D.targetPaths_isWarp, D.targetPaths_finite, rfl,
    D.targetPaths_terminal_target, ?_⟩
  intro p hp
  obtain ⟨f, rfl⟩ := D.targetPaths_finite hp
  have hstartSelected : f.start ∈ Gamma.initialSet D.targetPaths :=
    ⟨Sum.inl f, hp, rfl⟩
  have hstartSource : f.start ∈ Gamma.source :=
    D.targetPaths_initial_subset_source hstartSelected
  have hfinishTarget : f.finish ∈ Gamma.target :=
    D.targetPaths_terminal_target ⟨Sum.inl f, hp, rfl⟩
  have hsource : f.support ∩ Gamma.initialSet D.targetPaths = {f.start} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxf, hxInitial⟩
      exact Set.mem_singleton_iff.2
        (hNorm.eq_initial_of_mem_path (Sum.inl f) hxf
          (D.targetPaths_initial_subset_source hxInitial))
    · rintro x hx
      have hxeq : x = f.start := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨f.start_mem_support, hstartSelected⟩
  have htarget : f.support ∩ Gamma.target = {f.finish} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxf, hxTarget⟩
      have hterminal :=
        hNorm.terminal?_eq_of_mem_path (Sum.inl f) hxf hxTarget
      exact Set.mem_singleton_iff.2 (Option.some.inj hterminal).symm
    · rintro x hx
      have hxeq : x = f.finish := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨f.finish_mem_support, hfinishTarget⟩
  refine ⟨f, rfl, ?_, hsource⟩
  rw [Set.inter_union_distrib_left, hsource, htarget]
  ext x
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]

/-- The two localized families split the source exactly at the actual
initial set of the completed track. -/
theorem LocalizedProtectedHalfwayGeometry.remainder_initialSet_eq_sdiff
    {Gamma : DWeb V} {A₀ : Set V} {rho : Cardinal.{u}}
    (D : LocalizedProtectedHalfwayGeometry Gamma A₀ rho) :
    Gamma.initialSet D.remainder =
      Gamma.source \ Gamma.initialSet D.targetPaths := by
  have hdisjoint : Disjoint (Gamma.initialSet D.targetPaths)
      (Gamma.initialSet D.remainder) := by
    apply Set.disjoint_left.2
    intro x hxP hxR
    obtain ⟨p, hpP, hpInitial⟩ := hxP
    obtain ⟨q, hqR, hqInitial⟩ := hxR
    exact Set.disjoint_left.1 (D.families_disjoint p hpP q hqR)
      (hpInitial ▸ p.initial_mem_support)
      (hqInitial ▸ q.initial_mem_support)
  apply Set.Subset.antisymm
  · intro x hxR
    exact ⟨D.remainder_initial_subset_source hxR,
      fun hxP ↦ Set.disjoint_left.1 hdisjoint hxP hxR⟩
  · rintro x ⟨hxSource, hxNotP⟩
    have hxCover : x ∈ Gamma.initialSet D.targetPaths ∪
        Gamma.initialSet D.remainder := by
      rw [D.source_cover]
      exact hxSource
    exact hxCover.resolve_left hxNotP

/-- The terminal-clean remainder is an exact linkage from the complementary
source set to the stopover. -/
theorem LocalizedProtectedHalfwayGeometry.remainder_isLinkageBetween
    {Gamma : DWeb V} {A₀ : Set V} {rho : Cardinal.{u}}
    (D : LocalizedProtectedHalfwayGeometry Gamma A₀ rho) :
    IsLinkageBetween Gamma
      (Gamma.source \ Gamma.initialSet D.targetPaths)
      D.stopover D.remainder := by
  have hinitial := remainder_initialSet_eq_sdiff D
  refine ⟨D.remainder_isWarp, D.remainder_finite, hinitial,
    D.remainder_terminal_stopover, ?_⟩
  intro p hp
  obtain ⟨f, hpf, hends, hsource⟩ := D.remainder_endpointPure p hp
  have hstartComplement : f.start ∈
      Gamma.source \ Gamma.initialSet D.targetPaths := by
    have hstartR : f.start ∈ Gamma.initialSet D.remainder := by
      exact ⟨p, hp, by
        rw [hpf]
        change f.start = f.start
        rfl⟩
    rwa [hinitial] at hstartR
  have hsource' : f.support ∩
      (Gamma.source \ Gamma.initialSet D.targetPaths) = {f.start} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxf, hxSource, _hxNotSelected⟩
      exact hsource ▸ ⟨hxf, hxSource⟩
    · rintro x hx
      have hxeq : x = f.start := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨f.start_mem_support, hstartComplement⟩
  have hfinishC : f.finish ∈ D.stopover := by
    apply D.remainder_terminal_stopover
    exact ⟨p, hp, by
      rw [hpf]
      exact Gamma.terminal?_finite f⟩
  refine ⟨f, hpf, ?_, hsource'⟩
  apply Set.Subset.antisymm
  · rintro x ⟨hxf, hxSource | hxC⟩
    · have hx : x ∈ ({f.start} : Set V) := by
        rw [← hsource']
        exact ⟨hxf, hxSource⟩
      exact Set.mem_insert_iff.2 (Or.inl (Set.mem_singleton_iff.1 hx))
    · have hxOld : x ∈ f.support ∩ (Gamma.source ∪ D.stopover) :=
        ⟨hxf, Or.inr hxC⟩
      rw [hends] at hxOld
      exact hxOld
  · rintro x (hxStart | hxFinish)
    · subst x
      exact ⟨f.start_mem_support, Or.inl hstartComplement⟩
    · have hxeq : x = f.finish := Set.mem_singleton_iff.1 hxFinish
      subst x
      exact ⟨f.finish_mem_support, Or.inr hfinishC⟩

/-- The localized protected output itself is already the initial
selected/clean slice at its stopover, with `selected` equal to *all* actual
initials of the completed track. -/
noncomputable def LocalizedProtectedHalfwayGeometry.toCleanTargetSlice
    {Gamma : DWeb V} {A₀ : Set V} {rho : Cardinal.{u}}
    (D : LocalizedProtectedHalfwayGeometry Gamma A₀ rho)
    (hNorm : Gamma.IsNormalized) :
    RegularCompletedPendingSplice.CleanTargetSlice Gamma Gamma.source
      D.stopover (Gamma.initialSet D.targetPaths) := by
  have hvertexDisjoint : Disjoint (Gamma.vertexSet D.targetPaths)
      (Gamma.vertexSet D.remainder) := by
    apply Set.disjoint_left.2
    rintro x ⟨p, hpP, hxp⟩ ⟨q, hqR, hxq⟩
    exact Set.disjoint_left.1 (D.families_disjoint p hpP q hqR) hxp hxq
  have hunionWarp : Gamma.IsWarp (D.targetPaths ∪ D.remainder) :=
    SingularContinuation.isWarp_union_of_disjoint_vertexSet Gamma
      D.targetPaths_isWarp D.remainder_isWarp hvertexDisjoint
  have hunionFinite : Gamma.HasFiniteCharacter
      (D.targetPaths ∪ D.remainder) :=
    SingularContinuation.finiteCharacter_union Gamma
      D.targetPaths_finite D.remainder_finite
  refine
    { target := D.targetPaths
      clean := D.remainder
      union_warp := hunionWarp
      finiteCharacter := hunionFinite
      target_initial := rfl
      clean_initial := remainder_initialSet_eq_sdiff D
      initial_cover := D.targetPaths_initial_subset_source
      target_links := D.targetPaths_link_initial
      clean_terminal := D.remainder_terminal_stopover
      clean_terminal_only := D.remainder_terminalClean
      source_pure := ?_ }
  intro p hp
  rcases hp with hpP | hpR
  · apply Set.Subset.antisymm
    · rintro x ⟨hxp, hxSource⟩
      exact Set.mem_singleton_iff.2
        (hNorm.eq_initial_of_mem_path p hxp hxSource)
    · rintro x hx
      have hxeq : x = p.initial := Set.mem_singleton_iff.1 hx
      subst x
      refine ⟨p.initial_mem_support, ?_⟩
      apply D.targetPaths_initial_subset_source
      exact ⟨p, hpP, rfl⟩
  · obtain ⟨f, hpf, _hends, hsource⟩ := D.remainder_endpointPure p hpR
    rw [hpf]
    change f.support ∩ Gamma.source = {f.start}
    exact hsource

/-- Exact source complement after deleting the whole completed carrier. -/
theorem LocalizedProtectedHalfwayGeometry.delete_targetCarrier_source
    {Gamma : DWeb V} {A₀ : Set V} {rho : Cardinal.{u}}
    (D : LocalizedProtectedHalfwayGeometry Gamma A₀ rho)
    (hNorm : Gamma.IsNormalized) :
    (Gamma.delete (Gamma.vertexSet D.targetPaths)).source =
      Gamma.source \ Gamma.initialSet D.targetPaths := by
  have hinter : Gamma.vertexSet D.targetPaths ∩ Gamma.source =
      Gamma.initialSet D.targetPaths := by
    apply Set.Subset.antisymm
    · rintro x ⟨⟨p, hpP, hxp⟩, hxSource⟩
      have hxInitial : x = p.initial :=
        hNorm.eq_initial_of_mem_path p hxp hxSource
      exact ⟨p, hpP, hxInitial.symm⟩
    · intro x hxInitial
      obtain ⟨p, hpP, hpInitial⟩ := hxInitial
      refine ⟨⟨p, hpP, hpInitial ▸ p.initial_mem_support⟩, ?_⟩
      apply D.targetPaths_initial_subset_source
      exact ⟨p, hpP, hpInitial⟩
  ext x
  constructor
  · rintro ⟨hxSource, hxCarrier⟩
    refine ⟨hxSource, ?_⟩
    intro hxInitial
    have hxInter : x ∈ Gamma.vertexSet D.targetPaths ∩ Gamma.source := by
      rw [hinter]
      exact hxInitial
    exact hxCarrier hxInter.1
  · rintro ⟨hxSource, hxInitial⟩
    refine ⟨hxSource, ?_⟩
    intro hxCarrier
    apply hxInitial
    have hxInter : x ∈ Gamma.vertexSet D.targetPaths ∩ Gamma.source :=
      ⟨hxCarrier, hxSource⟩
    rwa [hinter] at hxInter

/-- The whole completed carrier remains below the current regular cardinal
when the fair output has lower-cardinal path budget. -/
theorem LocalizedProtectedHalfwayGeometry.targetCarrier_small
    {Gamma : DWeb V} {A₀ : Set V} {rho kappa : Cardinal.{u}}
    (D : LocalizedProtectedHalfwayGeometry Gamma A₀ rho)
    (hNorm : Gamma.IsNormalized) (huncountable : aleph0 < kappa)
    (hrho : rho < kappa) :
    #(Gamma.vertexSet D.targetPaths) < kappa := by
  have hP := targetPaths_isLinkageBetween D hNorm
  have hselected : #(Gamma.initialSet D.targetPaths) < kappa :=
    (RegularProtectedAmbientRebuild.mk_initialSet_le_family
      Gamma D.targetPaths).trans_lt (D.targetPaths_card.trans_lt hrho)
  exact SingularSafeCarrierCardinal.mk_vertexSet_lt_of_mk_initial_lt
    huncountable hP hselected

/-- End-to-end protected installation of the actual localized `P/R` split.
The returned slice keeps `P` literally as its target track and uses the
protected ambient rebuild as its clean track. -/
theorem LocalizedProtectedHalfwayGeometry.exists_advancedCleanTargetSlice
    {Gamma : DWeb V} {A₀ : Set V} {rho kappa : Cardinal.{u}}
    (D : LocalizedProtectedHalfwayGeometry Gamma A₀ rho)
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hrho : rho < kappa)
    (hlower : RegularProtectedAmbientRebuild.ExtensionBelowFor Gamma kappa)
    (hNorm : Gamma.IsNormalized)
    {T E₀ : Set V} {Y₀ : Set Gamma.DPath}
    (hCroof : D.stopover ⊆ Gamma.roof T)
    (hTessential : Gamma.essential T = T)
    (hE₀small : #E₀ < kappa)
    (hY₀ : IsLinkageBetween Gamma (Gamma.source \ E₀) T Y₀)
    (hY₀tight : MeetsOnlyAtTerminal Gamma Y₀ T) :
    ∃ K : RegularProtectedAmbientRebuild.ProtectedAmbientCompletion
        Gamma (Gamma.vertexSet D.targetPaths) D.stopover T kappa,
      ∃ S : RegularCompletedPendingSplice.CleanTargetSlice
          Gamma Gamma.source T (Gamma.initialSet D.targetPaths),
        S.target = D.targetPaths ∧ S.clean = K.lifted := by
  let X := Gamma.vertexSet D.targetPaths
  let selected := Gamma.initialSet D.targetPaths
  let S₀ := toCleanTargetSlice D hNorm
  have hsource : (Gamma.delete X).source = Gamma.source \ selected :=
    delete_targetCarrier_source D hNorm
  have hR : IsLinkageBetween Gamma (Gamma.delete X).source
      D.stopover D.remainder := by
    rw [hsource]
    exact remainder_isLinkageBetween D
  have hRavoid : Disjoint (Gamma.vertexSet D.remainder) X := by
    apply Set.disjoint_left.2
    rintro x hxR hxP
    obtain ⟨r, hr, hxr⟩ := hxR
    obtain ⟨p, hp, hxp⟩ := hxP
    exact Set.disjoint_left.1 (D.families_disjoint p hp r hr) hxp hxr
  obtain ⟨K⟩ :=
    RegularProtectedAmbientRebuild.exists_protectedAmbientCompletion_of_ambientRemainder
      hregular huncountable Gamma hlower hNorm
        (targetCarrier_small D hNorm huncountable hrho)
        D.targetPaths_carrier_roof D.stopover_trimmed D.stopover_separator
        D.original_quotient_unhindered hCroof hTessential
        hR D.remainder_terminalClean hRavoid hE₀small hY₀ hY₀tight
  have hclean : TightLinkageBetween Gamma
      (Gamma.source \ selected) T K.lifted := by
    rw [← hsource]
    exact K.liftedTight
  have hdisjoint : Disjoint (Gamma.vertexSet S₀.target)
      (Gamma.vertexSet K.lifted) := by
    change Disjoint X (Gamma.vertexSet K.lifted)
    exact K.liftedAvoids.symm
  obtain ⟨S, hStarget, hSclean⟩ :=
    RegularWeakProtectedSelectedClean.CleanTargetSlice.advanceClean_of_vertexDisjoint
      S₀ hclean hdisjoint
  exact ⟨K, S, hStarget, hSclean⟩

#print axioms LocalizedProtectedHalfwayGeometry.exists_advancedCleanTargetSlice

end RegularLocalizedProtectedCleanSlice
end CardinalInduction
end Erdos599
