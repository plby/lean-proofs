/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularTargetLinkTransfer

/-!
# Exact-frontier singular continuation

The half-way rows occurring in the construction of Assertion 9.17 have a
stronger property than the public `IsHalfwayStopover` interface currently
records: their terminal frontier is *equal* to the stop-over.  This exactness
is the source-faithful invariant needed for literal quotient iteration.

Indeed, every member of a warp meets its terminal frontier only at its own
terminal.  Thus an exact-frontier half-way row is automatically
terminal-clean, and a finite member starting on the boundary is necessarily
trivial.  More importantly, exactness is preserved by the ordinary quotient
continuation.  Consequently the same literal continuation both carries the
next target links and is the clean row used for the following quotient step.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularExactFrontierContinuation

open SingularContinuation SingularQuotientReentry SingularTargetLinkTransfer

universe u

variable {V : Type u}

/-- A separating half-way stop-over whose boundary is exactly the exposed
terminal frontier of its linkage. -/
structure ExactFrontierStopover (G : DWeb V) (W : Set G.DPath)
    (C : Set V) : Prop where
  separating : IsSeparatingHalfwayStopover G W C
  terminalFrontier_eq : G.terminalFrontier W = C

namespace ExactFrontierStopover

theorem terminalCleanAt {G : DWeb V} {W : Set G.DPath} {C : Set V}
    (h : ExactFrontierStopover G W C) :
    TerminalCleanAt G W C := by
  intro p hp x hxp hxC
  apply DWeb.IsWarp.terminal_eq_of_mem_support_mem_terminalFrontier
    G h.separating.linkage.isWarp hp hxp
  rw [h.terminalFrontier_eq]
  exact hxC

theorem linkage {G : DWeb V} {W : Set G.DPath} {C : Set V}
    (h : ExactFrontierStopover G W C) :
    IsLinkageBetween G G.source C W :=
  h.separating.linkage

theorem quotient_unhindered {G : DWeb V} {W : Set G.DPath} {C : Set V}
    (h : ExactFrontierStopover G W C) :
    (G.quotient C).IsUnhindered :=
  h.separating.quotient_unhindered

end ExactFrontierStopover

/-- If every right-hand initial is an exposed left-hand terminal, every
right-hand terminal remains exposed after source-star composition. -/
theorem terminalFrontier_subset_terminalFrontier_star
    {G : DWeb V} {W T : Set G.DPath}
    (hWfinite : G.HasFiniteCharacter W)
    (hTwarp : G.IsWarp T)
    (hcompat : G.StarCompatible W T)
    (hcover : G.initialSet T ⊆ G.terminalFrontier W) :
    G.terminalFrontier T ⊆ G.terminalFrontier (G.star hcompat) := by
  rintro x ⟨q, hqT, hqx⟩
  have hqInitial : q.initial ∈ G.initialSet T := ⟨q, hqT, rfl⟩
  obtain ⟨p, hpW, hpterm⟩ := hcover hqInitial
  obtain ⟨f, rfl⟩ := hWfinite hpW
  have hqStart : q.initial = f.finish :=
    (Option.some.inj hpterm).symm
  have hmatch : ∃ r ∈ T, r.initial = f.finish :=
    ⟨q, hqT, hqStart⟩
  let chosen : G.DPath := Classical.choose hmatch
  have hchosenT : chosen ∈ T := (Classical.choose_spec hmatch).1
  have hchosenInitial : chosen.initial = f.finish :=
    (Classical.choose_spec hmatch).2
  have hchosenEq : chosen = q :=
    DWeb.IsWarp.eq_of_initial_eq G hTwarp hchosenT hqT
      (hchosenInitial.trans hqStart.symm)
  let old : W := ⟨(.inl f : G.DPath), hpW⟩
  refine ⟨G.starPath hcompat old, ⟨old, rfl⟩, ?_⟩
  dsimp only [old, DWeb.starPath]
  rw [dif_pos hmatch]
  have hinter : f.support ∩ chosen.support ⊆ {f.finish} := by
    intro y hy
    have hy' := hcompat (.inl f) hpW chosen hchosenT y hy.1 hy.2
    exact Set.mem_singleton_iff.2 (Option.some.inj hy'.1).symm
  exact (DirectedPath.Path.terminal?_appendFinite
    f chosen hchosenInitial hinter).trans (hchosenEq ▸ hqx)

/-- Exact terminal frontiers are preserved by the literal quotient
continuation. -/
theorem terminalFrontier_continuation_eq
    (G : DWeb V) {D E : Set V} {W : Set G.DPath}
    (hW : IsLinkageBetween G G.source D W)
    (hsep : IsSeparatorFrom G G.source D)
    (htrim : IsTrimmedSeparator G D)
    (hWfrontier : G.terminalFrontier W = D)
    {U : Set (G.quotient D).DPath}
    (hUwarp : (G.quotient D).IsWarp U)
    (hUinitial : (G.quotient D).initialSet U =
      (G.quotient D).source)
    (hUfrontier : (G.quotient D).terminalFrontier U = E) :
    G.terminalFrontier
        (continuation G hW hsep htrim
          (by
            intro p hp x hxp hxD
            apply DWeb.IsWarp.terminal_eq_of_mem_support_mem_terminalFrontier
              G hW.isWarp hp hxp
            rw [hWfrontier]
            exact hxD)
          U hUinitial) = E := by
  let hclean : TerminalCleanAt G W D := by
    intro p hp x hxp hxD
    apply DWeb.IsWarp.terminal_eq_of_mem_support_mem_terminalFrontier
      G hW.isWarp hp hxp
    rw [hWfrontier]
    exact hxD
  let L : Set G.DPath := liftedQuotientFamily G D U
  let hcompat : G.StarCompatible W L :=
    starCompatible_liftQuotientFamily_of_linkage
      G hW hsep htrim hclean hUinitial
  have hLwarp : G.IsWarp L :=
    DWeb.IsWarp.liftQuotientFamily G hUwarp
  have hcover : G.initialSet L ⊆ G.terminalFrontier W := by
    intro x hx
    have hx' : x ∈ (G.quotient D).initialSet U := by
      simpa only [L, G.initialSet_liftQuotientFamily] using hx
    rw [hUinitial, quotient_source_eq_stopover G hsep htrim,
      ← hWfrontier] at hx'
    exact hx'
  have hlower : G.terminalFrontier L ⊆
      G.terminalFrontier (G.star hcompat) :=
    terminalFrontier_subset_terminalFrontier_star
      hW.finiteCharacter hLwarp hcompat hcover
  have hupper : G.terminalFrontier (G.star hcompat) ⊆
      G.terminalFrontier L :=
    terminalFrontier_continuation_subset
      G hW hsep htrim hclean hUinitial
  have hstar : G.star hcompat =
      continuation G hW hsep htrim hclean U hUinitial := rfl
  apply Set.Subset.antisymm
  · intro x hx
    have hxL : x ∈ G.terminalFrontier L := hupper hx
    change x ∈
      G.terminalFrontier (G.liftQuotientFamily D U) at hxL
    rw [G.terminalFrontier_liftQuotientFamily, hUfrontier] at hxL
    exact hxL
  · intro x hxE
    have hxL : x ∈ G.terminalFrontier L := by
      change x ∈ G.terminalFrontier (G.liftQuotientFamily D U)
      rw [G.terminalFrontier_liftQuotientFamily, hUfrontier]
      exact hxE
    have hxStar := hlower hxL
    simpa only [hstar] using hxStar

/-- The source-faithful form of the successor step in Assertion 9.17.
Exact old and quotient frontiers make the *ordinary* continuation into the
next exact-frontier half-way row. -/
theorem continuation_exactFrontierStopover
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {D E : Set V}
    (hD : ExactFrontierStopover G W D)
    {U : Set (G.quotient D).DPath}
    (hE : ExactFrontierStopover (G.quotient D) U E) :
    let P := continuation G hD.linkage hD.separating.separator
      hD.separating.stopover.minimal hD.terminalCleanAt U
      hE.linkage.initialSet_eq
    ExactFrontierStopover G P E ∧ G.ForwardExtension W P := by
  dsimp only
  let P := continuation G hD.linkage hD.separating.separator
    hD.separating.stopover.minimal hD.terminalCleanAt U
    hE.linkage.initialSet_eq
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  have hPwarp : G.IsWarp P :=
    continuation_isWarp G hD.linkage hD.separating.separator
      hD.separating.stopover.minimal hD.terminalCleanAt
      hE.linkage.isWarp hE.linkage.initialSet_eq
  have hPfinite : G.HasFiniteCharacter P :=
    continuation_finiteCharacter G hD.linkage hD.separating.separator
      hD.separating.stopover.minimal hD.terminalCleanAt
      hE.linkage.finiteCharacter hE.linkage.initialSet_eq
  have hPinitial : G.initialSet P = G.source :=
    initialSet_continuation G hD.linkage hD.separating.separator
      hD.separating.stopover.minimal hD.terminalCleanAt U
      hE.linkage.initialSet_eq
  have hPfrontier : G.terminalFrontier P = E := by
    exact terminalFrontier_continuation_eq
      G hD.linkage hD.separating.separator
        hD.separating.stopover.minimal hD.terminalFrontier_eq
        hE.linkage.isWarp hE.linkage.initialSet_eq
        hE.terminalFrontier_eq
  have hPclean : TerminalCleanAt G P E := by
    intro p hp x hxp hxE
    apply DWeb.IsWarp.terminal_eq_of_mem_support_mem_terminalFrontier
      G hPwarp hp hxp
    rw [hPfrontier]
    exact hxE
  have hPlinkage : IsLinkageBetween G G.source E P :=
    (SliceSpliceSource.tightLinkageBetween_of_structural
      hNorm Set.Subset.rfl hPwarp hPfinite hPinitial
        hPfrontier.le hPclean).1
  have hPseparator : IsSeparatorFrom G G.source E :=
    newStopover_isSeparator hD.separating hE.separating.separator
  have hPseparating : IsSeparatingHalfwayStopover G P E := by
    refine ⟨⟨hPlinkage, hPseparator,
      newStopover_isTrimmed hNoEnter hD.separating hE.separating,
      quotient_new_isUnhindered hNoEnter hD.separating hE.separating⟩,
      hPseparator⟩
  have hPforward : G.ForwardExtension W P :=
    forwardExtension_continuation G hD.linkage
      hD.separating.separator hD.separating.stopover.minimal
      hD.terminalCleanAt U hE.linkage.initialSet_eq
  exact ⟨⟨hPseparating, hPfrontier⟩, hPforward⟩

/-- The same exact-frontier successor also transports a designated set of
original sources to the ambient target. -/
theorem continuation_exactFrontierStopover_linksToTarget
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {D E A B : Set V}
    (hD : ExactFrontierStopover G W D)
    (hA : A ⊆ (G.quotient D).source)
    (hB : B ⊆ G.source)
    (hroute : RoutesTerminals G W B A)
    {U : Set (G.quotient D).DPath}
    (hE : ExactFrontierStopover (G.quotient D) U E)
    (hlinks : LinksToTarget (G.quotient D) U A) :
    let P := continuation G hD.linkage hD.separating.separator
      hD.separating.stopover.minimal hD.terminalCleanAt U
      hE.linkage.initialSet_eq
    ExactFrontierStopover G P E ∧ G.ForwardExtension W P ∧
      LinksToTarget G P B := by
  dsimp only
  have hstruct := continuation_exactFrontierStopover hNorm hD hE
  refine ⟨hstruct.1, hstruct.2, ?_⟩
  exact linksToTarget_continuation hNorm hD.separating
    hD.terminalCleanAt hE.linkage.isWarp hE.linkage.finiteCharacter
      hE.linkage.initialSet_eq hA hB hroute hlinks

#print axioms terminalFrontier_subset_terminalFrontier_star
#print axioms terminalFrontier_continuation_eq
#print axioms continuation_exactFrontierStopover
#print axioms continuation_exactFrontierStopover_linksToTarget

end SingularExactFrontierContinuation
end CardinalInduction
end Erdos599
