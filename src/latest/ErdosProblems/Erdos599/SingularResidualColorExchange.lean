/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.BoundarySimultaneousAssignment
import ErdosProblems.Erdos599.SingularResidualWaveExchange

/-!
# The alternating colour route in a residual one-point augmentation

A one-point augmentation may globally reroute the old finite warp, so its
members cannot simply be restricted by their former colours.  Nevertheless
the two warps are aligned at their endpoint boundary.  The boundary form of
the simultaneous-assignment theorem therefore extracts an honest safe
bracket alternating route.  Since only one initial and one terminal were
added, the route starts at the new initial and either is infinite or ends at
the new terminal.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularResidualColorExchange

open Alternating

universe u

variable {V : Type u}

/-- The old warp and a one-point augmentation are aligned at both endpoint
boundaries.  This uses the full carrier equalities in `IsCleanFiniteWarp`,
not ambient normalization. -/
theorem boundaryAligned_of_onePointAugmentation
    {G : DWeb V} {J Jplus : Set G.DPath}
    (hJ : G.IsCleanFiniteWarp J)
    (hplus : G.IsOnePointAugmentation J Jplus) :
    BoundaryAligned Jplus J := by
  obtain ⟨a, ha, b, hb, _hwarp, _hfinite, hinitial, hterminal⟩ := hplus
  constructor
  · intro x hx
    rw [hinitial] at hx
    rcases hx.1 with hxa | hxInitial
    · subst x
      exact False.elim (ha.2 (by
        rw [← hJ.2.2.1]
        exact ⟨hx.2, ha.1⟩))
    · exact hxInitial
  · intro x hx
    rw [hterminal] at hx
    rcases hx.1 with hxb | hxTerminal
    · subst x
      exact False.elim (hb.2 (by
        rw [← hJ.2.2.2]
        exact ⟨hx.2, hb.1⟩))
    · exact hxTerminal

/-- Boundary alignment also holds against every old subwarp.  This is the
two-colour form used by the residual exchange: one may take the subwarp to be
either the designated target colour or the residual-wave colour. -/
theorem boundaryAligned_subwarp_of_onePointAugmentation
    {G : DWeb V} {J Jplus Y : Set G.DPath}
    (hJ : G.IsCleanFiniteWarp J) (hY : Y ⊆ J)
    (hplus : G.IsOnePointAugmentation J Jplus) :
    BoundaryAligned Jplus Y := by
  obtain ⟨a, ha, b, hb, _hwarp, _hfinite, hinitial, hterminal⟩ := hplus
  constructor
  · rintro x ⟨hxPlus, q, hqY, hxq⟩
    rw [hinitial] at hxPlus
    rcases hxPlus with hxa | hxInitial
    · subst x
      exact False.elim (ha.2 (by
        rw [← hJ.2.2.1]
        exact ⟨⟨q, hY hqY, hxq⟩, ha.1⟩))
    · obtain ⟨p, hpJ, hpx⟩ := hxInitial
      have hpq : p = q := by
        apply DWeb.IsWarp.eq_of_mem_support hJ.isWarp hpJ (hY hqY)
        · exact hpx ▸ p.initial_mem_support
        · exact hxq
      subst q
      exact ⟨p, hqY, hpx⟩
  · rintro x ⟨hxPlus, q, hqY, hxq⟩
    rw [hterminal] at hxPlus
    rcases hxPlus with hxb | hxTerminal
    · subst x
      exact False.elim (hb.2 (by
        rw [← hJ.2.2.2]
        exact ⟨⟨q, hY hqY, hxq⟩, hb.1⟩))
    · obtain ⟨p, hpJ, hpx⟩ := hxTerminal
      have hpq : p = q := by
        apply DWeb.IsWarp.eq_of_mem_support hJ.isWarp hpJ (hY hqY)
        · exact G.terminal_mem_support hpx
        · exact hxq
      subst q
      exact ⟨p, hqY, hpx⟩

/-- Starting at the new source, boundary simultaneous assignment may be run
against either colour of the old combined warp.  Its finite terminal is an
augmented terminal not covered by that chosen colour. -/
theorem exists_safeBracketRoute_against_subwarp
    {G : DWeb V} {J Jplus Y : Set G.DPath}
    (hJ : G.IsCleanFiniteWarp J) (hYsub : Y ⊆ J)
    (hYwarp : G.IsWarp Y) (hYfinite : G.HasFiniteCharacter Y)
    (hplus : G.IsOnePointAugmentation J Jplus) :
    ∃ a : V, a ∈ G.source \ G.initialSet J ∧
      ∃ Q : AltPath G.graph,
        IsBracketSafe Jplus Y Q ∧ Q.initial = a ∧
          (Q.IsInfinite ∨ ∃ v,
            v ∈ G.terminalFrontier Jplus \ G.vertexSet Y ∧
              Q.terminal? = some v) := by
  obtain ⟨a, ha, b, hb, hplusWarp, hplusFinite, hinitial, hterminal⟩ := hplus
  have hinitSub : G.initialSet Y ⊆ G.initialSet Jplus := by
    rw [hinitial]
    intro x hx
    apply Set.mem_insert_of_mem
    obtain ⟨p, hpY, hpx⟩ := hx
    exact ⟨p, hYsub hpY, hpx⟩
  obtain ⟨B⟩ := boundaryBracketSimultaneousAssignment G Jplus Y
    (boundaryAligned_subwarp_of_onePointAugmentation hJ hYsub
      ⟨a, ha, b, hb, hplusWarp, hplusFinite, hinitial, hterminal⟩)
    hplusWarp hYwarp hplusFinite hYfinite hinitSub
  have haPlus : a ∈ G.initialSet Jplus \ G.initialSet Y := by
    constructor
    · rw [hinitial]
      exact Set.mem_insert a _
    · intro haY
      obtain ⟨p, hpY, hpa⟩ := haY
      exact ha.2 ⟨p, hYsub hpY, hpa⟩
  let z : {x : V // x ∈ G.initialSet Jplus \ G.initialSet Y} := ⟨a, haPlus⟩
  let Q := B.assigned z
  refine ⟨a, ha, Q, B.bracket_safe z, B.starts_at z, ?_⟩
  rcases B.maximal z with hinfinite | hfinite
  · exact Or.inl hinfinite
  · exact Or.inr hfinite

/-- The safe bracket route exposed by a one-point augmentation.  Its finite
alternative necessarily reaches the unique new terminal. -/
theorem exists_safeBracketRoute_of_onePointAugmentation
    {G : DWeb V} {J Jplus : Set G.DPath}
    (hJ : G.IsCleanFiniteWarp J)
    (hplus : G.IsOnePointAugmentation J Jplus) :
    ∃ a b : V, a ∈ G.source \ G.initialSet J ∧
      b ∈ G.target \ G.terminalFrontier J ∧
      ∃ Q : AltPath G.graph,
        IsBracketSafe Jplus J Q ∧ Q.initial = a ∧
          (Q.IsInfinite ∨ Q.terminal? = some b) := by
  obtain ⟨a, ha, b, hb, hplusWarp, hplusFinite, hinitial, hterminal⟩ := hplus
  have hinitSub : G.initialSet J ⊆ G.initialSet Jplus := by
    rw [hinitial]
    exact Set.subset_insert a _
  obtain ⟨B⟩ := boundaryBracketSimultaneousAssignment G Jplus J
    (boundaryAligned_of_onePointAugmentation hJ
      ⟨a, ha, b, hb, hplusWarp, hplusFinite, hinitial, hterminal⟩)
    hplusWarp hJ.isWarp hplusFinite hJ.hasFiniteCharacter hinitSub
  have haPlus : a ∈ G.initialSet Jplus \ G.initialSet J := by
    constructor
    · rw [hinitial]
      exact Set.mem_insert a _
    · exact ha.2
  let z : {x : V // x ∈ G.initialSet Jplus \ G.initialSet J} := ⟨a, haPlus⟩
  let Q := B.assigned z
  have hQend : Q.IsInfinite ∨ Q.terminal? = some b := by
    rcases B.maximal z with hinfinite | ⟨v, hv, hQv⟩
    · exact Or.inl hinfinite
    · apply Or.inr
      have hvb : v = b := by
        rw [hterminal] at hv
        rcases hv.1 with hvb | hvOld
        · exact hvb
        · exact False.elim (hv.2 (by
            obtain ⟨p, hpJ, hpv⟩ := hvOld
            exact ⟨p, hpJ, G.terminal_mem_support hpv⟩))
      exact hvb ▸ hQv
  refine ⟨a, b, ha, hb, Q, ?_, ?_, hQend⟩
  · exact B.bracket_safe z
  · exact B.starts_at z

#print axioms boundaryAligned_of_onePointAugmentation
#print axioms boundaryAligned_subwarp_of_onePointAugmentation
#print axioms exists_safeBracketRoute_against_subwarp
#print axioms exists_safeBracketRoute_of_onePointAugmentation

end SingularResidualColorExchange
end CardinalInduction
end Erdos599
