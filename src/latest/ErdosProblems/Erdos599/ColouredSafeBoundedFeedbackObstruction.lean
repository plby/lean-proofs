/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeBoundedAuxiliarySuccessor

/-!
# Excluding an uncovered source by bounded actual auxiliary continuation

Absence of an original infinite safe word makes the original saturation
carrier finite. The auxiliary successor stays in that carrier under the
internal-reference-edge property, so it cannot iterate indefinitely.
The ambient path-family carriers themselves may be infinite.
-/

noncomputable section

namespace Erdos599.Alternating.ColouredSafeBoundedFeedbackObstruction

open Set DirectedPath FiniteColouredOccurrenceWord ColouredSafeReverseReachability
open ColouredSafeAuxiliaryForwardContainment ColouredSafeBoundedAuxiliarySuccessor

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y C : Set Gamma.DPath}

theorem no_uncoveredSource_of_no_original_safeInfinite
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hYC : Gamma.IsWarp (Y ∪ C)) (hYCfin : Gamma.HasFiniteCharacter (Y ∪ C))
    (hdisjoint : Disjoint (Gamma.vertexSet Y) (Gamma.vertexSet C))
    (hsource : Gamma.initialSet (Y ∪ C) ⊆ Gamma.initialSet W)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet (Y ∪ C) ⊆
      Gamma.terminalFrontier (Y ∪ C))
    {J : Set (ExposedInitial W Y)} (hJ : J.Finite)
    (hno : ∀ s ∈ J, ¬ ∃ Q : InfiniteColouredOccurrenceWord W Y,
      Q.IsIntervalSafe ∧ Q.vertex 0 = s.1)
    (hnonterminal : ∀ s ∈ J, s.1 ∉ Gamma.terminalFrontier W)
    (hCtails : ∀ {x y}, (x, y) ∈ familyEdges C → x ∈ Subtype.val '' J)
    (hCV : Gamma.vertexSet C ⊆ Subtype.val '' J ∪ safeTerminalUnion J)
    (hcover : safeTerminalUnion J ⊆ Gamma.vertexSet C)
    (hinternal : ∀ {a b}, (a, b) ∈ familyEdges W → a ∈ Gamma.vertexSet Y →
      b ∈ Gamma.vertexSet Y → b ∉ Gamma.initialSet Y →
      a ∉ Gamma.terminalFrontier Y → (a, b) ∈ familyEdges Y) :
    Subtype.val '' J ⊆ Gamma.vertexSet (Y ∪ C) := by
  rintro _ ⟨s, hsJ, rfl⟩
  by_contra hsOff
  have hsW := initialSet_subset_vertexSet W s.2.1
  have hsOutside := ColouredSafeFiniteAuxiliaryRemoval.not_reverseReachable_of_auxiliary_cover
    hW hY hWfin hYfin hYC hdisjoint hnonterminal hCtails hcover hsJ hsOff
  let H := finiteSaturationCarrier hW hY J
  have hH : H.Finite := finiteSaturationCarrier_finite hW hY hWfin hYfin hJ hno
  let initial : SafePrefixState W (Y ∪ C) s.1 := SafePrefixState.initial hsW hsOutside
  have hInitial : initial.word.vertexSet ⊆ H := by
    rintro x ⟨i, hi⟩
    have hx : s.1 = x := hi
    exact hx ▸ source_or_safeTerminal_mem_saturation hW hY hWfin hYfin
      (J := J) (Or.inl ⟨s, hsJ, rfl⟩)
  let State := {S : SafePrefixState W (Y ∪ C) s.1 // S.word.vertexSet ⊆ H}
  have hstep (S : State) : ∃ T : State,
      S.1.word.Prefix T.1.word ∧ S.1.word.length < T.1.word.length := by
    obtain ⟨T, hp, hl, hTH⟩ := exists_successor_in_saturation
      hW hY hWfin hYfin hYC hYCfin hdisjoint hsource hterminal hCtails hCV hinternal
      ⟨s, hsJ, rfl⟩ hsOff S.1 S.2
    exact ⟨⟨T, hTH⟩, hp, hl⟩
  let next (S : State) : State := Classical.choose (hstep S)
  let stages : ℕ → State := Nat.rec ⟨initial, hInitial⟩ (fun _ S ↦ next S)
  let chain : FiniteColouredOccurrencePrefixChain W (Y ∪ C) := {
    stage := fun n ↦ (stages n).1.word
    grows := fun n ↦ (Classical.choose_spec (hstep (stages n))).1
    length_strict := fun n ↦ (Classical.choose_spec (hstep (stages n))).2 }
  have hlimit : chain.limit.vertexSet ⊆ H := by
    rw [chain.limit_vertexSet_eq_iUnion]
    intro x hx
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
    exact (stages n).2 hxn
  exact ColouredSafeForwardStopping.infiniteWord_vertexSet_infinite chain.limit
    (hH.subset hlimit)

#print axioms no_uncoveredSource_of_no_original_safeInfinite

end Erdos599.Alternating.ColouredSafeBoundedFeedbackObstruction
