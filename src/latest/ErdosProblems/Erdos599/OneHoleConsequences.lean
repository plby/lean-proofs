/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.OneHoleBoundary

/-!
# Consequences of the one-hole marked augmentation theorem

This file joins the two exhaustive branches of the contact-marked residual
search.  A reached uncovered target gives an augmentation; otherwise the
last-hit boundary from `OneHoleBoundary` gives a hindrance.  The remaining
theorems transport this one-hole dichotomy through the deletion constructions
already verified in `OneHoleReroute`.
-/

namespace Erdos599
namespace DWeb

open Set
open Alternating

universe u

variable {V : Type u}

/-- Contact-normalized marked augmentation implies the complete residual
search statement. -/
theorem oneHoleSearch_of_markedAugmentation
    (haugment : OneHoleMarkedAugmentation V) :
    OneHoleSearchStatement V := by
  intro G J hJ hsourceGap
  by_cases htarget : ∃ b ∈ G.target \ G.terminalFrontier J,
      b ∈ G.OneHoleMarkedReachable J
  · obtain ⟨b, hb, hbreach⟩ := htarget
    exact Or.inl (G.oneHole_augmentation_of_marked_target
      haugment hJ hb hbreach)
  · apply Or.inr
    refine ⟨G.OneHoleMarkedReachable J, ?_⟩
    apply G.isOneHoleBlockingSet_oneHoleMarkedReachable_of_no_targetGap
      J hJ
    rw [Set.disjoint_left]
    intro b hb hbreach
    exact htarget ⟨b, hb, hbreach⟩

/-- The contact-normalized marked augmentation implies the exact corrected
one-hole principle (with a genuine uncovered source). -/
theorem oneHolePrinciple_of_markedAugmentation
    (haugment : OneHoleMarkedAugmentation V) :
    OneHolePrinciple V :=
  oneHolePrinciple_of_search
    (oneHoleSearch_of_markedAugmentation haugment)

/-- Central one-hole dichotomy, parameterized only by the finite-chain
extraction theorem. -/
theorem oneHoleDichotomy_of_cleanFiniteWarp_of_markedAugmentation
    (haugment : OneHoleMarkedAugmentation V) (G : DWeb V)
    {J : Set G.DPath} (hJ : G.IsCleanFiniteWarp J)
    (hsourceGap : (G.source \ G.initialSet J).Nonempty) :
    G.OneHoleDichotomy J :=
  oneHolePrinciple_of_markedAugmentation haugment G J hJ hsourceGap

/-- Singleton deletion, with all transport bookkeeping discharged. -/
theorem isHindered_delete_singleton_of_markedAugmentation
    (haugment : OneHoleMarkedAugmentation V) (G : DWeb V) {v : V}
    (hG : G.IsHindered) (hvA : v ∉ G.source) :
    (G.delete {v}).IsHindered :=
  isHindered_delete_singleton_of_oneHolePrinciple
    (oneHolePrinciple_of_markedAugmentation haugment) G hG hvA

/-- Finite deletion (Aharoni--Berger Lemma 3.31), with all transport
bookkeeping discharged. -/
theorem isHindered_delete_finite_of_markedAugmentation
    (haugment : OneHoleMarkedAugmentation V) (G : DWeb V) {F : Set V}
    (hG : G.IsHindered) (hF : F.Finite) (hFA : F ⊆ G.sourceᶜ) :
    (G.delete F).IsHindered :=
  isHindered_delete_finite_of_oneHolePrinciple
    (oneHolePrinciple_of_markedAugmentation haugment) G hG hF hFA

/-- The one-vertex converse (Aharoni--Berger Lemma 3.32), with all transport
bookkeeping discharged. -/
theorem exists_wave_terminalFrontier_of_delete_isHindered_of_markedAugmentation
    (haugment : OneHoleMarkedAugmentation V) (G : DWeb V) {v : V}
    (hG : G.IsUnhindered) (hvA : v ∉ G.source)
    (hdel : (G.delete {v}).IsHindered) :
    ∃ W : Set G.DPath, G.IsWave W ∧ v ∈ G.terminalFrontier W :=
  exists_wave_terminalFrontier_of_delete_isHindered_of_oneHolePrinciple
    (oneHolePrinciple_of_markedAugmentation haugment) G hG hvA hdel

end DWeb
end Erdos599
