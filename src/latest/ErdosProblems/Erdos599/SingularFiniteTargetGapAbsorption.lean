/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import Mathlib.Data.Set.Card
import ErdosProblems.Erdos599.AlternativeMaximalLinkage

/-!
# Absorbing a finite target deficit

The one-hole search has a stronger consequence than its usual disjunctive
statement.  In a normalized web, a clean finite warp whose uncovered target
set is finite can be completed to a wave without losing any of its initial
vertices.

Indeed, an augmenting outcome removes one point from the finite target
deficit.  A blocking outcome produces a last-hit prefix wave, whose initial
set is literally unchanged.  If no source is left uncovered, cutting every
member at its initial vertex gives the required wave directly.  Thus strong
induction on the finite target deficit terminates and retains the whole
initial profile throughout.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularFiniteTargetGapAbsorption

open DWeb
open AlternativeMaximalLinkage

universe u

variable {V : Type u}

/-- The range of the initial-vertex map on a path family is its initial
set.  This is the endpoint identity used in the full-source base case. -/
theorem range_initial_eq_initialSet
    (G : DWeb V) (W : Set G.DPath) :
    Set.range (fun p : W ↦ p.1.initial) = G.initialSet W := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.1, p.2, rfl⟩
  · rintro ⟨p, hp, hpx⟩
    exact ⟨⟨p, hp⟩, hpx⟩

/-- A clean finite warp in a normalized web with only finitely many
uncovered target vertices is dominated, at the level of initial vertices,
by an actual wave.

The proof uses the full residual-search statement rather than the weaker
one-hole dichotomy: its blocking certificate constructs a last-hit prefix
wave with exactly the old initial set. -/
theorem exists_wave_initialSet_superset_of_finite_target_gap
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} (hW : G.IsCleanFiniteWarp W)
    (hgapFinite : (G.target \ G.terminalFrontier W).Finite) :
    ∃ U : Set G.DPath, G.IsWave U ∧
      G.initialSet W ⊆ G.initialSet U := by
  generalize hn : Set.ncard (G.target \ G.terminalFrontier W) = n
  induction n using Nat.strong_induction_on generalizing W with
  | h n ih =>
      by_cases hsourceGap : (G.source \ G.initialSet W).Nonempty
      · rcases G.oneHoleSearch W hW hsourceGap with
          haugment | ⟨reachable, hblocking⟩
        · obtain ⟨Wplus, hplus⟩ := haugment
          have hplusCopy := hplus
          obtain ⟨a, ha, b, hb, _hwarp, _hcharacter,
            hinitial, hterminal⟩ := hplusCopy
          have hWplus : G.IsCleanFiniteWarp Wplus :=
            IsOnePointAugmentation.cleanFiniteWarp_of_normalized
              hNorm hW hplus
          have hgapEq :
              G.target \ G.terminalFrontier Wplus =
                (G.target \ G.terminalFrontier W) \ {b} := by
            rw [hterminal]
            ext x
            simp only [Set.mem_sdiff, Set.mem_insert_iff,
              Set.mem_singleton_iff]
            tauto
          have hgapPlusFinite :
              (G.target \ G.terminalFrontier Wplus).Finite := by
            rw [hgapEq]
            exact hgapFinite.sdiff
          have hdecrease :
              Set.ncard (G.target \ G.terminalFrontier Wplus) < n := by
            rw [hgapEq, ← hn]
            exact Set.ncard_sdiff_singleton_lt_of_mem hb hgapFinite
          obtain ⟨U, hU, hWplusU⟩ :=
            ih _ hdecrease (W := Wplus) hWplus hgapPlusFinite rfl
          refine ⟨U, hU, ?_⟩
          intro x hx
          apply hWplusU
          rw [hinitial]
          exact Set.mem_insert_of_mem a hx
        · let R := G.lastHitPrefixFamily W hW.hasFiniteCharacter reachable
          have hproper : G.initialSet W ≠ G.source :=
            DWeb.IsCleanFiniteWarp.initialSet_ne_source_of_gap_nonempty
              G hW hsourceGap
          have hroof : G.source ⊆ G.roof
              (Set.range (G.lastHitCut W hW.hasFiniteCharacter reachable)) :=
            G.roof_of_forwardBoundary
              hblocking.1 hblocking.2.1 hblocking.2.2
          have hR : G.IsHindrance R :=
            DWeb.IsWarp.isHindrance_lastHitPrefixFamily G hW.isWarp
              hW.hasFiniteCharacter hW.initialSet_subset_source hproper
                reachable hroof
          refine ⟨R, hR.1, ?_⟩
          simpa only [R, DWeb.lastHitPrefixFamily,
            G.initialSet_prefixFamily] using
              (Set.Subset.rfl : G.initialSet W ⊆ G.initialSet W)
      · have hfull : G.initialSet W = G.source := by
          apply Set.Subset.antisymm hW.initialSet_subset_source
          intro x hxSource
          by_contra hxInitial
          exact hsourceGap ⟨x, hxSource, hxInitial⟩
        let cut : W → V := fun p ↦ p.1.initial
        have hcut : ∀ p : W, cut p ∈ p.1.support :=
          fun p ↦ p.1.initial_mem_support
        let U := G.prefixFamily W hW.hasFiniteCharacter cut hcut
        have hseparator : G.source ⊆ G.roof (Set.range cut) := by
          rw [range_initial_eq_initialSet G W, hfull]
          exact G.subset_roof G.source
        have hU : G.IsWave U :=
          DWeb.IsWarp.isWave_prefixFamily G hW.isWarp
            hW.hasFiniteCharacter hW.initialSet_subset_source
              cut hcut hseparator
        refine ⟨U, hU, ?_⟩
        simpa only [U, G.initialSet_prefixFamily] using
          (Set.Subset.rfl : G.initialSet W ⊆ G.initialSet W)

#print axioms exists_wave_initialSet_superset_of_finite_target_gap

end SingularFiniteTargetGapAbsorption
end CardinalInduction
end Erdos599
