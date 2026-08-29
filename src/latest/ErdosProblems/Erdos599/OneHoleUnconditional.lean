/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.OneHoleRouteBalance
import ErdosProblems.Erdos599.OneHoleConsequences

/-!
# Unconditional one-hole and finite-deletion theorems

This module closes the marked residual search with the finite route-balance
calculation and exports the source Lemmas 3.31 and 3.32 without any auxiliary
principle assumptions.
-/

namespace Erdos599
namespace DWeb

open Set

universe u

variable {V : Type u}

/-- Unconditional corrected one-hole dichotomy for a clean finite-character
warp with a genuinely uncovered source. -/
theorem oneHoleDichotomy_of_cleanFiniteWarp
    (G : DWeb V) {J : Set G.DPath} (hJ : G.IsCleanFiniteWarp J)
    (hsourceGap : (G.source \ G.initialSet J).Nonempty) :
    G.OneHoleDichotomy J :=
  oneHoleDichotomy_of_cleanFiniteWarp_of_markedAugmentation
    oneHoleMarkedAugmentation G hJ hsourceGap

/-- Singleton case of the finite-deletion lemma. -/
theorem isHindered_delete_singleton
    (G : DWeb V) {v : V} (hG : G.IsHindered)
    (hvA : v ∉ G.source) :
    (G.delete {v}).IsHindered :=
  isHindered_delete_singleton_of_markedAugmentation
    oneHoleMarkedAugmentation G hG hvA

/-- Aharoni--Berger Lemma 3.31: deleting a finite set disjoint from the
source of a hindered web leaves a hindered web. -/
theorem isHindered_delete_finite
    (G : DWeb V) {F : Set V} (hG : G.IsHindered)
    (hF : F.Finite) (hFA : F ⊆ G.sourceᶜ) :
    (G.delete F).IsHindered :=
  isHindered_delete_finite_of_markedAugmentation
    oneHoleMarkedAugmentation G hG hF hFA

/-- Aharoni--Berger Lemma 3.32: if deleting a non-source vertex hinders an
unhindered web, that vertex lies on the terminal frontier of a wave. -/
theorem exists_wave_terminalFrontier_of_delete_isHindered
    (G : DWeb V) {v : V} (hG : G.IsUnhindered)
    (hvA : v ∉ G.source) (hdel : (G.delete {v}).IsHindered) :
    ∃ W : Set G.DPath, G.IsWave W ∧ v ∈ G.terminalFrontier W :=
  exists_wave_terminalFrontier_of_delete_isHindered_of_markedAugmentation
    oneHoleMarkedAugmentation G hG hvA hdel

end DWeb
end Erdos599
