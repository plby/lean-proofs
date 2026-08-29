/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularQuotientLower
import ErdosProblems.Erdos599.SliceSpliceSource

/-!
# Selected-component continuation for the singular target matrix

At a singular successor stage only the components whose initial vertices
belong to the newly closed source set have to be continued.  The other
components are frozen.  This file supplies the source-star compatibility
lemma in the form needed for that split: quotient paths start at the actual
frontier of the selected subwarp.  Consequently an intersection with an old
selected path is forced, by warp disjointness, to be that path's terminal.
This avoids the unnecessarily strong assertion that the old linkage meets
its entire stop-over only at its terminal (which can fail when a source is
itself in the stop-over).
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularExtension

universe u

variable {V : Type u}

/-- Quotient paths starting at the actual frontier of a roofed warp are
source-star compatible with it.  The old warp condition identifies the
unique member ending at the quotient initial vertex. -/
theorem starCompatible_liftQuotientFamily_of_frontier
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hW : G.IsWarp W)
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    {U : Set (G.quotient C).DPath}
    (hUstart : (G.quotient C).initialSet U ⊆ G.terminalFrontier W) :
    G.StarCompatible W
      (SingularContinuation.liftedQuotientFamily G C U) := by
  intro p hpW q hqU x hxp hxq
  obtain ⟨q₀, hq₀U, rfl⟩ := hqU
  have hq₀frontier : q₀.initial ∈ G.terminalFrontier W :=
    hUstart ⟨q₀, hq₀U, rfl⟩
  have hxRoof : x ∈ G.roof C := hroof ⟨p, hpW, hxp⟩
  have hxClass := G.quotientPath_support_initial_or_avoids C q₀ (by
    simpa only [G.support_liftQuotientPath] using hxq)
  have hxInitial : x = q₀.initial := by
    rcases hxClass with hx | hxAvoid
    · exact hx
    · exfalso
      by_cases hxEssential : x ∈ G.essential C
      · exact hxAvoid.2 (htrim ▸ hxEssential)
      · exact hxAvoid.1 ⟨hxRoof, hxEssential⟩
  obtain ⟨r, hrW, hrterminal⟩ := hq₀frontier
  have hpr : p = r := by
    by_contra hne
    exact Set.disjoint_left.1 (hW hpW hrW hne) hxp
      (G.terminal_mem_support
        (hrterminal.trans (congrArg some hxInitial.symm)))
  subst r
  exact ⟨hrterminal.trans (congrArg some hxInitial.symm), by
    simpa only [G.initial_liftQuotientPath] using hxInitial.symm⟩

/-- Continue a selected subwarp through quotient paths beginning at every
selected terminal. -/
noncomputable def selectedContinuation
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hW : G.IsWarp W)
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    (U : Set (G.quotient C).DPath)
    (hUstart : (G.quotient C).initialSet U ⊆ G.terminalFrontier W) :
    Set G.DPath :=
  G.star (starCompatible_liftQuotientFamily_of_frontier
    G hW hroof htrim hUstart)

theorem selectedContinuation_isWarp
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hW : G.IsWarp W)
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    {U : Set (G.quotient C).DPath}
    (hU : (G.quotient C).IsWarp U)
    (hUstart : (G.quotient C).initialSet U ⊆ G.terminalFrontier W) :
    G.IsWarp (selectedContinuation G hW hroof htrim U hUstart) := by
  exact G.isWarp_star hW (DWeb.IsWarp.liftQuotientFamily G hU)
    (starCompatible_liftQuotientFamily_of_frontier
      G hW hroof htrim hUstart)

theorem forwardExtension_selectedContinuation
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hW : G.IsWarp W)
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    (U : Set (G.quotient C).DPath)
    (hUstart : (G.quotient C).initialSet U ⊆ G.terminalFrontier W) :
    G.ForwardExtension W
      (selectedContinuation G hW hroof htrim U hUstart) := by
  exact G.forwardExtension_star
    (starCompatible_liftQuotientFamily_of_frontier
      G hW hroof htrim hUstart)

theorem initialSet_selectedContinuation
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hW : G.IsWarp W)
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    (U : Set (G.quotient C).DPath)
    (hUstart : (G.quotient C).initialSet U ⊆ G.terminalFrontier W) :
    G.initialSet (selectedContinuation G hW hroof htrim U hUstart) =
      G.initialSet W := by
  exact (G.initialSet_eq_of_forwardExtension
    (forwardExtension_selectedContinuation
      G hW hroof htrim U hUstart)).symm

/-! ## Residual-interior-safe continuation

The roof hypothesis above is convenient but is not available when an old
path starts in the stop-over and then leaves its roof.  The construction
actually needs less: a proposed quotient continuation must avoid the
nonterminal vertices of the old warp.  This is the invariant obtained by
choosing the quotient family after deleting that residual interior.
-/

/-- The old vertices which a future continuation is not allowed to use.
Old terminal vertices are omitted because they are precisely the legal
source-star attachment points. -/
def residualInterior (G : DWeb V) (W : Set G.DPath) : Set V :=
  G.vertexSet W \ G.terminalFrontier W

/-- Residual-interior avoidance replaces both roof containment and
terminal-cleanliness in the source-overlap case.  A meeting point is an old
terminal by avoidance.  It is also the initial point of the quotient path,
because quotient paths cannot enter the commitment set after their initial
vertex.  Finally, pairwise disjointness of the old warp identifies the old
member which has that terminal.

Unlike `starCompatible_liftQuotientFamily_of_frontier`, this lemma permits
old paths to have arbitrary internal vertices outside `roof C`. -/
theorem starCompatible_liftQuotientFamily_of_residualInterior
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hW : G.IsWarp W)
    (hfrontier : G.terminalFrontier W ⊆ C)
    {U : Set (G.quotient C).DPath}
    (hUavoid : Disjoint
      (G.vertexSet (SingularContinuation.liftedQuotientFamily G C U))
      (residualInterior G W)) :
    G.StarCompatible W
      (SingularContinuation.liftedQuotientFamily G C U) := by
  intro p hpW q hqU x hxp hxq
  obtain ⟨q₀, hq₀U, rfl⟩ := hqU
  have hxOld : x ∈ G.vertexSet W := ⟨p, hpW, hxp⟩
  have hxFrontier : x ∈ G.terminalFrontier W := by
    by_contra hxNotFrontier
    exact Set.disjoint_left.1 hUavoid
      ⟨G.liftQuotientPath C q₀, ⟨q₀, hq₀U, rfl⟩, hxq⟩
      ⟨hxOld, hxNotFrontier⟩
  have hxC : x ∈ C := hfrontier hxFrontier
  have hxInitial : x = q₀.initial := by
    rcases G.quotientPath_support_initial_or_avoids C q₀ (by
        simpa only [G.support_liftQuotientPath] using hxq) with hx | hxAvoid
    · exact hx
    · exact False.elim (hxAvoid.2 hxC)
  obtain ⟨r, hrW, hrterminal⟩ := hxFrontier
  have hpr : p = r := by
    by_contra hne
    exact Set.disjoint_left.1 (hW hpW hrW hne) hxp
      (G.terminal_mem_support hrterminal)
  subst r
  exact ⟨hrterminal, by
    simpa only [G.initial_liftQuotientPath] using hxInitial.symm⟩

/-- Source-star based on residual-interior avoidance.  This is the robust
continuation operation for stop-overs which meet the ambient source. -/
noncomputable def residualSafeContinuation
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hW : G.IsWarp W)
    (hfrontier : G.terminalFrontier W ⊆ C)
    (U : Set (G.quotient C).DPath)
    (hUavoid : Disjoint
      (G.vertexSet (SingularContinuation.liftedQuotientFamily G C U))
      (residualInterior G W)) : Set G.DPath :=
  G.star (starCompatible_liftQuotientFamily_of_residualInterior
    G hW hfrontier hUavoid)

/-- The residual-safe continuation is a warp. -/
theorem residualSafeContinuation_isWarp
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hW : G.IsWarp W)
    (hfrontier : G.terminalFrontier W ⊆ C)
    {U : Set (G.quotient C).DPath}
    (hU : (G.quotient C).IsWarp U)
    (hUavoid : Disjoint
      (G.vertexSet (SingularContinuation.liftedQuotientFamily G C U))
      (residualInterior G W)) :
    G.IsWarp (residualSafeContinuation G hW hfrontier U hUavoid) := by
  exact G.isWarp_star hW (DWeb.IsWarp.liftQuotientFamily G hU)
    (starCompatible_liftQuotientFamily_of_residualInterior
      G hW hfrontier hUavoid)

/-- The residual-safe continuation is a genuine forward extension, with no
source/stop-over disjointness assumption. -/
theorem forwardExtension_residualSafeContinuation
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hW : G.IsWarp W)
    (hfrontier : G.terminalFrontier W ⊆ C)
    (U : Set (G.quotient C).DPath)
    (hUavoid : Disjoint
      (G.vertexSet (SingularContinuation.liftedQuotientFamily G C U))
      (residualInterior G W)) :
    G.ForwardExtension W
      (residualSafeContinuation G hW hfrontier U hUavoid) := by
  exact G.forwardExtension_star
    (starCompatible_liftQuotientFamily_of_residualInterior
      G hW hfrontier hUavoid)

/-- Residual-safe continuation preserves the exact old initial set. -/
theorem initialSet_residualSafeContinuation
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hW : G.IsWarp W)
    (hfrontier : G.terminalFrontier W ⊆ C)
    (U : Set (G.quotient C).DPath)
    (hUavoid : Disjoint
      (G.vertexSet (SingularContinuation.liftedQuotientFamily G C U))
      (residualInterior G W)) :
    G.initialSet (residualSafeContinuation G hW hfrontier U hUavoid) =
      G.initialSet W := by
  exact CardinalInduction.SliceSpliceSource.initialSet_star_eq
    (starCompatible_liftQuotientFamily_of_residualInterior
      G hW hfrontier hUavoid)

/-- Finite character is preserved by residual-safe continuation. -/
theorem residualSafeContinuation_finiteCharacter
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hW : G.IsWarp W)
    (hWfinite : G.HasFiniteCharacter W)
    (hfrontier : G.terminalFrontier W ⊆ C)
    {U : Set (G.quotient C).DPath}
    (hUfinite : (G.quotient C).HasFiniteCharacter U)
    (hUavoid : Disjoint
      (G.vertexSet (SingularContinuation.liftedQuotientFamily G C U))
      (residualInterior G W)) :
    G.HasFiniteCharacter
      (residualSafeContinuation G hW hfrontier U hUavoid) := by
  have hLiftFinite : G.HasFiniteCharacter
      (SingularContinuation.liftedQuotientFamily G C U) := by
    rintro q ⟨q₀, hq₀U, rfl⟩
    obtain ⟨f, rfl⟩ := hUfinite hq₀U
    exact ⟨f.lift (fun {_ _} h ↦ G.quotient_adj_imp h), rfl⟩
  unfold residualSafeContinuation
  intro p hp
  exact CardinalInduction.SliceSpliceSource.hasFiniteCharacter_star
    hWfinite hLiftFinite
    (starCompatible_liftQuotientFamily_of_residualInterior
      G hW hfrontier hUavoid) hp

/-- If the quotient family covers every old terminal, all new terminals
come from that quotient family. -/
theorem terminalFrontier_residualSafeContinuation_subset
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hW : G.IsWarp W)
    (hWfinite : G.HasFiniteCharacter W)
    (hfrontier : G.terminalFrontier W ⊆ C)
    {U : Set (G.quotient C).DPath}
    (hcover : G.terminalFrontier W ⊆ (G.quotient C).initialSet U)
    (hUavoid : Disjoint
      (G.vertexSet (SingularContinuation.liftedQuotientFamily G C U))
      (residualInterior G W)) :
    G.terminalFrontier
        (residualSafeContinuation G hW hfrontier U hUavoid) ⊆
      (G.quotient C).terminalFrontier U := by
  rw [← G.terminalFrontier_liftQuotientFamily C U]
  apply CardinalInduction.SliceSpliceSource.terminalFrontier_star_subset
    hWfinite
    (starCompatible_liftQuotientFamily_of_residualInterior
      G hW hfrontier hUavoid)
  simpa only [G.initialSet_liftQuotientFamily] using hcover

/-- A quotient family chosen after deleting the old residual interior has
the exact avoidance certificate required above. -/
theorem disjoint_liftQuotient_liftDeleteFamily_residualInterior
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    {U : Set ((G.quotient C).delete (residualInterior G W)).DPath}
    (hUsource :
      ((G.quotient C).delete (residualInterior G W)).initialSet U ⊆
        ((G.quotient C).delete (residualInterior G W)).source) :
    Disjoint
      (G.vertexSet (G.liftQuotientFamily C
        ((G.quotient C).liftDeleteFamily (residualInterior G W) U)))
      (residualInterior G W) := by
  have hq : Disjoint
      ((G.quotient C).vertexSet
        ((G.quotient C).liftDeleteFamily (residualInterior G W) U))
      (residualInterior G W) :=
    (G.quotient C).vertexSet_liftDeleteFamily_disjoint hUsource
  apply Set.disjoint_left.2
  intro x hx hxInterior
  obtain ⟨p, ⟨q, hqU, rfl⟩, hxp⟩ := hx
  exact Set.disjoint_left.1 hq
    ⟨q, hqU, by simpa using hxp⟩ hxInterior

/-- Concrete residual-safe successor package.  It has no `TerminalCleanAt`
or roof-containment premise: source-overlapping old paths are handled by
deleting precisely their nonterminal support in the quotient before the
new family is chosen. -/
theorem exists_residualSafeContinuation_of_quotientDeleteFamily
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hW : G.IsWarp W)
    (hWfinite : G.HasFiniteCharacter W)
    (hfrontier : G.terminalFrontier W ⊆ C)
    {U : Set ((G.quotient C).delete (residualInterior G W)).DPath}
    (hU : ((G.quotient C).delete (residualInterior G W)).IsWarp U)
    (hUfinite :
      ((G.quotient C).delete (residualInterior G W)).HasFiniteCharacter U)
    (hUsource :
      ((G.quotient C).delete (residualInterior G W)).initialSet U ⊆
        ((G.quotient C).delete (residualInterior G W)).source)
    (hcover : G.terminalFrontier W ⊆
      ((G.quotient C).delete (residualInterior G W)).initialSet U) :
    ∃ W' : Set G.DPath,
      G.IsWarp W' ∧ G.HasFiniteCharacter W' ∧
      G.ForwardExtension W W' ∧
      G.initialSet W' = G.initialSet W ∧
      G.terminalFrontier W' ⊆
        (G.quotient C).terminalFrontier
          ((G.quotient C).liftDeleteFamily (residualInterior G W) U) := by
  let U' : Set (G.quotient C).DPath :=
    (G.quotient C).liftDeleteFamily (residualInterior G W) U
  have hU' : (G.quotient C).IsWarp U' := hU.liftDeleteFamily
  have hU'finite : (G.quotient C).HasFiniteCharacter U' :=
    (G.quotient C).fd_hasFiniteCharacter_liftDeleteFamily hUfinite
  have hU'initial : (G.quotient C).initialSet U' =
      ((G.quotient C).delete (residualInterior G W)).initialSet U :=
    (G.quotient C).initialSet_liftDeleteFamily (residualInterior G W) U
  have hcover' : G.terminalFrontier W ⊆
      (G.quotient C).initialSet U' := by
    rw [hU'initial]
    exact hcover
  have havoid : Disjoint
      (G.vertexSet (SingularContinuation.liftedQuotientFamily G C U'))
      (residualInterior G W) :=
    disjoint_liftQuotient_liftDeleteFamily_residualInterior
      G hUsource
  let W' := residualSafeContinuation G hW hfrontier U' havoid
  refine ⟨W', ?_, ?_, ?_, ?_, ?_⟩
  · exact residualSafeContinuation_isWarp G hW hfrontier hU' havoid
  · exact residualSafeContinuation_finiteCharacter
      G hW hWfinite hfrontier hU'finite havoid
  · exact forwardExtension_residualSafeContinuation
      G hW hfrontier U' havoid
  · exact initialSet_residualSafeContinuation
      G hW hfrontier U' havoid
  · exact terminalFrontier_residualSafeContinuation_subset
      G hW hWfinite hfrontier hcover' havoid

end SingularExtension
end CardinalInduction
end Erdos599
