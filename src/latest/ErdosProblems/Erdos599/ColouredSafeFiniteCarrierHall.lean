/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeFiniteFeedbackFamily
import ErdosProblems.Erdos599.ColouredSafeGraphLift

/-!
# Fixed-original safe Hall inequality for finite carriers

The ambient digraph and vertex type need not be finite. Only the two
specified path-family carriers are finite. The proof introduces auxiliary
matching paths in a larger graph and then lowers all safe-word data back
to the original fixed families. No auxiliary adjacency assumption remains.
The infinite-carrier case is a separate obligation.
-/

namespace Erdos599.Alternating.ColouredSafeFiniteCarrierHall

open Set DirectedPath ColouredSafeReverseReachability FiniteColouredOccurrenceWord
open ColouredSafeGraphLift

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

def completeWeb (Gamma : DWeb V) : DWeb V where
  graph := ⟨fun _ _ ↦ True⟩
  source := Gamma.source
  target := Gamma.target

theorem hall_nonterminal_of_finite_carriers
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hWV : (Gamma.vertexSet W).Finite) (hYV : (Gamma.vertexSet Y).Finite)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    {J : Set (ExposedInitial W Y)} (hJ : J.Finite)
    (hnonterminal : ∀ s ∈ J, s.1 ∉ Gamma.terminalFrontier W) :
    J.ncard ≤ (safeTerminalUnion J).ncard := by
  let h : ∀ {x y}, Gamma.graph.Adj x y → (completeWeb Gamma).graph.Adj x y :=
    fun _ ↦ True.intro
  have hsource' : (completeWeb Gamma).initialSet (liftFamily h Y) ⊆
      (completeWeb Gamma).initialSet (liftFamily h W) := by
    simpa only [liftFamily_initialSet] using hsource
  have hterminal' : (completeWeb Gamma).terminalFrontier (liftFamily h W) ∩
      (completeWeb Gamma).vertexSet (liftFamily h Y) ⊆
      (completeWeb Gamma).terminalFrontier (liftFamily h Y) := by
    simpa only [liftFamily_terminalFrontier, liftFamily_vertexSet] using hterminal
  have hnonterminal' : ∀ s ∈ liftSource h '' J,
      s.1 ∉ (completeWeb Gamma).terminalFrontier (liftFamily h W) := by
    rintro _ ⟨s, hs, rfl⟩
    simpa only [liftSource, liftFamily_terminalFrontier] using hnonterminal s hs
  have hresult := ColouredSafeFiniteFeedbackFamily.hall_nonterminal_of_auxiliaryAdj
    (liftFamily_isWarp h hW) (liftFamily_isWarp h hY)
    (liftFamily_finiteCharacter h hWfin) (liftFamily_finiteCharacter h hYfin)
    (by simpa only [liftFamily_vertexSet] using hWV)
    (by simpa only [liftFamily_vertexSet] using hYV)
    hsource' hterminal' (hJ.image (liftSource h)) hnonterminal'
    (fun _ _ _ _ ↦ True.intro)
  simpa only [safeTerminalUnion_liftSource,
    Set.ncard_image_of_injective J (liftSource_injective h)] using hresult

/-- Exact finite Hall inequality for the original safe-terminal rows.
Exposed vertices which are also terminals are handled by singleton-row
cancellation, not by adding a nonterminal assumption to the conclusion. -/
theorem hall_of_finite_carriers
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hWV : (Gamma.vertexSet W).Finite) (hYV : (Gamma.vertexSet Y).Finite)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    {J : Set (ExposedInitial W Y)} (hJ : J.Finite) :
    J.ncard ≤ (safeTerminalUnion J).ncard := by
  have hno : ∀ s ∈ J, ¬ ∃ Q : InfiniteColouredOccurrenceWord W Y,
      Q.IsIntervalSafe ∧ Q.vertex 0 = s.1 := by
    rintro s _ ⟨Q, _hQ, _hs⟩
    exact ColouredSafeFiniteDuality.not_infiniteWord_of_finite_carriers hWV hYV ⟨Q⟩
  apply (hall_iff_nonterminalSources hW hY hWfin hYfin hJ hno).mpr
  exact hall_nonterminal_of_finite_carriers hW hY hWfin hYfin hWV hYV hsource hterminal
    (hJ.subset (nonterminalSources_subset J)) (fun _ hs ↦ hs.2)

#print axioms hall_nonterminal_of_finite_carriers
#print axioms hall_of_finite_carriers

end Erdos599.Alternating.ColouredSafeFiniteCarrierHall
