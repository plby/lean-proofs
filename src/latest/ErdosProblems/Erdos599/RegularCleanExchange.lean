/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SliceCandidate
import ErdosProblems.Erdos599.SingularContinuation

/-!
# Terminal-clean whole-component exchange

After completed target components are split off, Assertion 9.10 applies its
component exchange only to the complementary clean row.  This file records
that the whole-component replacement stays terminal-clean at the stop-over.
It also packages the clean version of the exchange, with no dummy target-link
predicate on the geometric row.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularCleanExchange

open SliceCandidate

universe u

variable {V : Type u}

/-- First-hit prefixes meet the cut only at their terminal. -/
theorem firstHitPrefixFamily_terminalClean
    {Q : DWeb V} {A C T : Set V} {Y : Set Q.DPath}
    (hY : IsLinkageBetween Q A T Y)
    (hsep : RelationalRoof.Separates Q.graph.Adj A T C) :
    SingularContinuation.TerminalCleanAt Q
      (firstHitPrefixFamily hY hsep) C := by
  rintro _ ⟨a, rfl⟩ x hx hxC
  have hx' : x ∈ (linkageFirstHitAt hY hsep a).support ∩ C :=
    ⟨hx, hxC⟩
  rw [linkageFirstHitAt_targetPure hY hsep a] at hx'
  have hxeq : x = (linkageFirstHitAt hY hsep a).finish :=
    Set.mem_singleton_iff.mp hx'
  exact congrArg some hxeq.symm

/-- Replacing whole alternating components by first-hit prefixes preserves
terminal cleanliness at the common cut. -/
theorem wholeComponentMixedFamily_terminalClean
    {Q : DWeb V} {A C T E : Set V} {W Y : Set Q.DPath}
    (hWclean : SingularContinuation.TerminalCleanAt Q W C)
    (hY : IsLinkageBetween Q (A \ E) T Y)
    (hsep : RelationalRoof.Separates Q.graph.Adj (A \ E) T C) :
    SingularContinuation.TerminalCleanAt Q
      (wholeComponentMixedFamily Q W
        (firstHitPrefixFamily hY hsep) Y E) C := by
  intro p hp x hxp hxC
  rcases hp with hpW | hpP
  · exact hWclean p hpW.1 x hxp hxC
  · exact firstHitPrefixFamily_terminalClean hY hsep
      p hpP.1 x hxp hxC

/-- Clean geometric form of the whole-terminal exchange.  The old row has
no target-link obligation: completed requested components have already been
removed into the separate target track. -/
theorem exists_cleanWholeTerminalExchange_of_componentReplacement
    {kappa : Cardinal.{u}} (Q : DWeb V) {A C T E : Set V}
    {W : Set Q.DPath} (hW : IsLinkageBetween Q A C W)
    (hWclean : SingularContinuation.TerminalCleanAt Q W C)
    {Y : Set Q.DPath} (hY : IsLinkageBetween Q (A \ E) T Y)
    (hYtight : SliceSpliceSource.MeetsOnlyAtTerminal Q Y T)
    (hsep : RelationalRoof.Separates Q.graph.Adj (A \ E) T C)
    (hEsub : E ⊆ A) (hregular : kappa.IsRegular)
    (huncountable : aleph0 < kappa) (hEsmall : #E < kappa) :
    ∃ (W' : Set Q.DPath) (E' : Set V) (F : Set Q.DPath),
      IsLinkageBetween Q A C W' ∧
      SingularContinuation.TerminalCleanAt Q W' C ∧
      E' ⊆ Q.terminalFrontier W' ∧ #E' < kappa ∧
      IsLinkageBetween Q (Q.terminalFrontier W' \ E') T F ∧
      Q.StarCompatible W' F ∧
      SliceSpliceSource.MeetsOnlyAtTerminal Q F T := by
  let P := firstHitPrefixFamily hY hsep
  let W' := wholeComponentMixedFamily Q W P Y E
  let E' := wholeExchangeExceptionalTerminals Q W Y E
  let S := wholeNonexceptionalPrefixSources hY hsep W
  let F := selectedSuffixFamily hY hsep S
  have hW' : IsLinkageBetween Q A C W' :=
    wholeComponentMixedFamily_isLinkageBetween Q hW hY hsep hEsub
  have hW'clean : SingularContinuation.TerminalCleanAt Q W' C :=
    wholeComponentMixedFamily_terminalClean hWclean hY hsep
  have hE'sub : E' ⊆ Q.terminalFrontier W' := by
    intro x hx
    change x ∈ Q.terminalFrontier
      (initialPart Q W (exceptionalComponentVertices Q W Y E)) at hx
    change x ∈ Q.terminalFrontier
      (initialPart Q W (exceptionalComponentVertices Q W Y E) ∪
        initialPart Q P (exceptionalComponentVertices Q W Y E)ᶜ)
    rw [DWeb.terminalFrontier_union]
    exact Or.inl hx
  have hE'small : #E' < kappa :=
    wholeExchangeExceptionalTerminals_small Q hregular huncountable
      hW.isWarp hY.isWarp hW.finiteCharacter hY.finiteCharacter hEsmall
  have hsource : Q.terminalFrontier W' \ E' =
      selectedSuffixStartSet hY hsep S := by
    rw [terminalFrontier_wholeMixed_sdiff_exceptional_eq Q hW hY hsep]
    exact terminalFrontier_wholeNonexceptionalPrefix_eq_suffixStartSet hY hsep
  have hF : IsLinkageBetween Q
      (selectedSuffixStartSet hY hsep S) T F :=
    selectedSuffixFamily_isLinkageBetween hY hsep S
  have hFtight : SliceSpliceSource.MeetsOnlyAtTerminal Q F T :=
    selectedSuffixFamily_meetsOnlyAtTerminal hY hYtight hsep S
  exact ⟨W', E', F, hW', hW'clean, hE'sub, hE'small,
    hsource.symm ▸ hF,
    wholeComponentExchange_starCompatible Q hW hY hsep, hFtight⟩

end RegularCleanExchange
end CardinalInduction
end Erdos599
