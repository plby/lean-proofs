/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularFiniteTargetGapAbsorption

/-!
# Finite-character strengthening of finite target-gap absorption

The recursive construction in `SingularFiniteTargetGapAbsorption` always
returns a prefix family of a finite-character warp.  This module records the
finite-character field explicitly, so the result can itself be used as the
next state of a residual-profile recursion without maximalizing and thereby
introducing rays.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularFiniteTargetGapAbsorptionStrong

open DWeb
open AlternativeMaximalLinkage
open SingularFiniteTargetGapAbsorption

universe u

variable {V : Type u}

/-- Prefixing a finite-character family retains finite character. -/
theorem hasFiniteCharacter_prefixFamily
    (G : DWeb V) {J : Set G.DPath}
    (hfin : G.HasFiniteCharacter J) (cut : J → V)
    (hcut : ∀ p, cut p ∈ p.1.support) :
    G.HasFiniteCharacter (G.prefixFamily J hfin cut hcut) := by
  rintro p ⟨q, _hq, rfl⟩
  unfold DWeb.prefixAtMember
  exact ⟨_, rfl⟩

/-- Finite target-gap absorption with the finite-character output retained. -/
theorem exists_finiteCharacter_wave_initialSet_superset_of_finite_target_gap
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} (hW : G.IsCleanFiniteWarp W)
    (hgapFinite : (G.target \ G.terminalFrontier W).Finite) :
    ∃ U : Set G.DPath, G.IsWave U ∧ G.HasFiniteCharacter U ∧
      G.initialSet W ⊆ G.initialSet U := by
  generalize hn : Set.ncard (G.target \ G.terminalFrontier W) = n
  induction n using Nat.strong_induction_on generalizing W with
  | h n ih =>
      by_cases hsourceGap : (G.source \ G.initialSet W).Nonempty
      · rcases G.oneHoleSearch W hW hsourceGap with
          haugment | ⟨reachable, hblocking⟩
        · obtain ⟨Wplus, hplus⟩ := haugment
          have hplusCopy := hplus
          obtain ⟨a, _ha, b, hb, _hwarp, _hcharacter,
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
          obtain ⟨U, hU, hUfinite, hWplusU⟩ :=
            ih _ hdecrease (W := Wplus) hWplus hgapPlusFinite rfl
          refine ⟨U, hU, hUfinite, ?_⟩
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
          refine ⟨R, hR.1, ?_, ?_⟩
          · exact hasFiniteCharacter_prefixFamily G hW.hasFiniteCharacter
              (G.lastHitCut W hW.hasFiniteCharacter reachable)
              (G.lastHitCut_mem_support W hW.hasFiniteCharacter reachable)
          · simpa only [R, DWeb.lastHitPrefixFamily,
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
        refine ⟨U, hU, ?_, ?_⟩
        · exact hasFiniteCharacter_prefixFamily G hW.hasFiniteCharacter
            cut hcut
        · simpa only [U, G.initialSet_prefixFamily] using
            (Set.Subset.rfl : G.initialSet W ⊆ G.initialSet W)

#print axioms hasFiniteCharacter_prefixFamily
#print axioms exists_finiteCharacter_wave_initialSet_superset_of_finite_target_gap

end SingularFiniteTargetGapAbsorptionStrong
end CardinalInduction
end Erdos599
