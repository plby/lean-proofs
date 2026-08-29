/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingTerminalFragment
import ErdosProblems.Erdos599.GroundingFragmentPartition
import ErdosProblems.Erdos599.GroundingEscapeSuffix
import ErdosProblems.Erdos599.GroundingFiniteDescent
import ErdosProblems.Erdos599.HindranceGrounding

/-!
# The terminal seed in Assertion 8.18

This file constructs the first state of the finite last-contact descent.
The terminal component is a surviving fragment of a finite essential
limiting-ladder path.  It is therefore blockable by the finite branch of
`GroundingCut.IsBlockable`, and hence belongs to the exact family `G0`.

If the terminal component did not meet the escape region, its blocking
point would be its terminal.  That terminal would then belong to `BL` and
therefore to `BB`, contradicting avoidance by the ambient finite path.
Thus the component has a genuine escape.  Reversing it to its first escape
and appending the escape gives the initial `EscapeSuffixState`.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace GroundingAssertion818Seed

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

abbrev Aux (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal) :=
  L.popularAuxiliaryInput hlegal

abbrev LV (L : Gamma.KappaLadder kappa) (_hlegal : L.IsLegal) :=
  PopularAuxiliary.Input.LambdaVertex V L.groundedInfiniteRecords

/-- The terminal component of an essential limiting-ladder parent is a
finite member of the exact `G'`, has the ambient terminal as its own
terminal, and genuinely meets the escape region.

The last conclusion is the seed argument of Assertion 8.18: without an
escape, `bl(P)=ter(P)`, so the ambient path would meet `BL ⊆ BB`. -/
theorem exists_terminal_G0_fragment_meeting_escape
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (C : Set (LV L hlegal))
    (R : FinitePath Gamma.graph)
    (hterminal : R.finish ∈ (Aux L hlegal).terminalCut)
    (havoid : Gamma.Avoids R (GroundingCut.BB (Aux L hlegal) C)) :
    ∃ P : (Aux L hlegal).Fragment,
      P ∈ GroundingCut.G0 (Aux L hlegal) C ∧
        P ∈ GroundingCut.fragments (Aux L hlegal) C ∧
        P.path.terminal? = some R.finish ∧
        R.finish ∈ P.path.support ∧
        PopularAuxiliary.Input.Fragment.MeetsEscape
          (Aux L hlegal) C P ∧
        P.parent ∈ (Aux L hlegal).essentialLadder := by
  obtain ⟨parent, hpEssential, hpTerminal⟩ := hterminal
  cases parent with
  | inl p =>
      have hpFinish : p.finish = R.finish := by
        exact Option.some.inj hpTerminal
      have hfinishParent : R.finish ∈ p.support := by
        rw [← hpFinish]
        exact p.finish_mem_support
      obtain ⟨P, hparent, hPfragment, hfinishP⟩ :=
        GroundingFragmentPartition.exists_fragment_containing
          (Aux L hlegal) C hpEssential.1 hfinishParent
      obtain ⟨hPfinite, hterminalP⟩ :=
        GroundingTerminalFragment.finite_and_terminal_eq_parent_finish
          (Aux L hlegal) C p P hPfragment hparent
            (by simpa only [hpFinish] using hfinishP)
      have hPterminal : P.path.terminal? = some R.finish := by
        simpa only [hpFinish] using hterminalP
      have hparentEssential :
          P.parent ∈ (Aux L hlegal).essentialLadder := by
        simpa only [hparent] using hpEssential
      have hPG0 : P ∈ GroundingCut.G0 (Aux L hlegal) C :=
        ⟨hPfragment, Or.inr hPfinite⟩
      have hescape :
          PopularAuxiliary.Input.Fragment.MeetsEscape
            (Aux L hlegal) C P := by
        by_contra hnoEscape
        have hblock :
            GroundingCut.blockingPoint (Aux L hlegal) C P = R.finish :=
          GroundingCut.blockingPoint_eq_terminal_of_not_meetsEscape
            (Aux L hlegal) C P hnoEscape hPterminal
        have hBL : R.finish ∈ GroundingCut.BL (Aux L hlegal) C :=
          ⟨P, hPG0, hblock⟩
        have hBB : R.finish ∈ GroundingCut.BB (Aux L hlegal) C :=
          GroundingCut.BL_subset_BB (Aux L hlegal) C hBL
        exact Set.disjoint_left.1 havoid R.finish_mem_support hBB
      exact ⟨P, hPG0, hPfragment, hPterminal,
        by simpa only [hpFinish] using hfinishP,
        hescape, hparentEssential⟩
  | inr r =>
      change (none : Option V) = some R.finish at hpTerminal
      cases hpTerminal

/-- The concrete terminal fragment and its escape compile to the initial
escape-suffix state used by the finite descent.  The position is literally
the final position of the ambient finite path. -/
theorem exists_initialEscapeSuffixState
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (C : Set (LV L hlegal))
    (R : FinitePath Gamma.graph)
    (hterminal : R.finish ∈ (Aux L hlegal).terminalCut)
    (havoid : Gamma.Avoids R (GroundingCut.BB (Aux L hlegal) C)) :
    ∃ S : GroundingFiniteDescent.EscapeSuffixState
        (Aux L hlegal) C R,
      ¬ S.position.1 + 1 < R.walk.support.length := by
  obtain ⟨P, hPG0, hPfragment, hPterminal, hfinishP,
      hPescape, _hparent⟩ :=
    exists_terminal_G0_fragment_meeting_escape
      L hlegal C R hterminal havoid
  have hfinishNotBB :
      R.finish ∉ GroundingCut.BB (Aux L hlegal) C := by
    intro hfinishBB
    exact Set.disjoint_left.1 havoid R.finish_mem_support hfinishBB
  obtain ⟨q, hqstart, hqtarget, hqavoid⟩ :=
    GroundingEscapeSuffix.exists_avoiding_terminal_escape_of_not_mem_BB
      (Aux L hlegal) C P ⟨hPfragment, hPG0⟩ hPterminal
        hPescape hfinishNotBB
  let n := R.walk.support.length - 1
  have hn : n < R.walk.support.length := by
    have hpos := R.support_length_pos
    dsimp only [n]
    omega
  let i : Fin R.walk.support.length := ⟨n, hn⟩
  have hilast : ¬ n + 1 < R.walk.support.length := by
    dsimp only [n]
    omega
  have hiFinish : R.walk.support[i] = R.finish :=
    Alternating.RelationComponents.getElem_last_support_eq_finish
      R n hn hilast
  refine ⟨{
    position := i
    fragment := P
    fragment_mem := hPG0
    fragment_escape := hPescape
    contact_mem := by simpa only [hiFinish] using hfinishP
    suffix := q
    suffix_start := hqstart.trans
      (congrArg PopularAuxiliary.Input.LambdaVertex.old hiFinish.symm)
    suffix_target := hqtarget
    suffix_avoids := hqavoid }, ?_⟩
  exact hilast

end GroundingAssertion818Seed
end Erdos599
