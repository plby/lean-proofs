/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.AlternatingLiteralEdgeWalk
import ErdosProblems.Erdos599.AlternatingMacroProvenance
import ErdosProblems.Erdos599.SafeSwitchingAssembly

/-!
# Final safeness assembly for the literal macro compiler

Once run compression has produced a literal bracket-alternating trace and
unique backward-link provenance, the interval clause follows from provenance.
Every remaining edge is carried by the finite-character forward warp, whose
edge union contains neither a directed ray nor a directed cycle.
-/

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u

variable {V : Type u} {Γ : DWeb V}

theorem IsBracketAlternating.outside_subset_familyEdges_literal
    {Z Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (hQ : IsBracketAlternating Z Y Q) :
    Q.edgeSet \ familyEdges Y ⊆ familyEdges Z := by
  rintro e ⟨heQ, heY⟩
  rw [Q.edgeSet_eq_iUnion_links] at heQ
  simp only [Set.mem_iUnion] at heQ
  rcases heQ with ⟨l, hlQ, hel⟩
  cases hdir : l.direction with
  | forward =>
      rcases hQ.2 l hlQ hdir with ⟨p, hpZ, hsub⟩
      simp only [familyEdges, Set.mem_iUnion]
      exact ⟨p, hpZ, hsub.2 hel⟩
  | backward =>
      exfalso
      apply heY
      rcases hQ.1.2.1 l hlQ hdir with ⟨p, hpY, hsub⟩
      simp only [familyEdges, Set.mem_iUnion]
      exact ⟨p, hpY, hsub.2 hel⟩

/-- The precise final assembly theorem consumed by both the finite and the
infinite macro compilers. -/
theorem IsBracketAlternating.isBracketSafe_of_backwardProvenance
    {Z Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z)
    (hQ : IsBracketAlternating Z Y Q)
    (P : Q.BackwardLinkProvenance Y) :
    IsBracketSafe Z Y Q := by
  have houtside := hQ.outside_subset_familyEdges_literal
  refine ⟨⟨hQ.1, P.intervals hY, ?_, ?_⟩, hQ⟩
  · rintro ⟨R, hR⟩
    exact SwitchingCore.familyEdges_not_containsDirectedRay hZ hZfin
      ⟨R, hR.trans houtside⟩
  · rintro ⟨C, hC⟩
    exact SwitchingCore.familyEdges_not_containsDirectedCycle hZ hZfin
      ⟨C, hC.trans houtside⟩

end Alternating
end Erdos599
