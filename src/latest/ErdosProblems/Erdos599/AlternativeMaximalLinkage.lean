/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CardinalInduction
import ErdosProblems.Erdos599.OneHoleUnconditional

/-!
# A maximal-linkage reduction for Erdős Problem 599

This file records precisely what a direct Zorn proof using the unconditional
one-hole augmentation theorem would still have to establish.  In a normalized
unhindered web every clean finite warp with an uncovered source has a
one-point augmentation.  Thus linkability follows as soon as the source sets
covered by clean finite warps have upper bounds for inclusion chains.

The chain-upper-bound premise is deliberately explicit.  One-point
augmentation can reroute old paths, so the families themselves do not form an
inclusion chain, and taking their union is not a sound proof of this premise.
-/

noncomputable section

namespace Erdos599
namespace AlternativeMaximalLinkage

open Set DirectedPath

universe u

variable {V : Type u}

/-- The source set covered by some clean finite warp. -/
def CleanlyCoverable (G : DWeb V) (S : Set V) : Prop :=
  ∃ W : Set G.DPath, G.IsCleanFiniteWarp W ∧ G.initialSet W = S

/-- The exact compactness assertion needed by the maximal clean-warp route.
It concerns the covered source sets, not inclusion of path families: a
one-point augmentation is allowed to reroute all old members. -/
def CleanCoverChainUpperBounds (G : DWeb V) : Prop :=
  ∀ c : Set (Set V),
    c ⊆ {S | CleanlyCoverable G S} → IsChain (· ⊆ ·) c →
      ∃ U, CleanlyCoverable G U ∧ ∀ S ∈ c, S ⊆ U

/-- In a normalized web, warp endpoints lying in the distinguished sides
force full endpoint cleanliness. -/
theorem cleanFiniteWarp_of_normalized
    {G : DWeb V} (hG : G.IsNormalized) {W : Set G.DPath}
    (hwarp : G.IsWarp W) (hfinite : G.HasFiniteCharacter W)
    (hinitial : G.initialSet W ⊆ G.source)
    (hterminal : G.terminalFrontier W ⊆ G.target) :
    G.IsCleanFiniteWarp W := by
  refine ⟨hwarp, hfinite, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨⟨p, hpW, hxp⟩, hxSource⟩
      exact ⟨p, hpW, (hG.eq_initial_of_mem_path p hxp hxSource).symm⟩
    · rintro x ⟨p, hpW, hpx⟩
      refine ⟨⟨p, hpW, hpx ▸ p.initial_mem_support⟩, ?_⟩
      exact hinitial ⟨p, hpW, hpx⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨⟨p, hpW, hxp⟩, hxTarget⟩
      exact ⟨p, hpW, hG.terminal?_eq_of_mem_path p hxp hxTarget⟩
    · rintro x ⟨p, hpW, hpx⟩
      refine ⟨⟨p, hpW, G.terminal_mem_support hpx⟩, ?_⟩
      exact hterminal ⟨p, hpW, hpx⟩

/-- A clean finite warp in a normalized web is the linkage between its
initial set and the ambient target that its endpoint sets suggest. -/
theorem isLinkageBetween_of_cleanFiniteWarp_of_normalized
    {G : DWeb V} (hG : G.IsNormalized) {W : Set G.DPath}
    (hW : G.IsCleanFiniteWarp W) :
    CardinalInduction.IsLinkageBetween
      G (G.initialSet W) G.target W := by
  refine ⟨hW.isWarp, hW.hasFiniteCharacter, rfl,
    hW.terminalFrontier_subset_target, ?_⟩
  intro p hpW
  obtain ⟨q, rfl⟩ := hW.2.1 hpW
  have hsource : q.support ∩ G.initialSet W = {q.start} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxq, hxInitial⟩
      have hxSource : x ∈ G.source :=
        DWeb.IsCleanFiniteWarp.initialSet_subset_source G hW hxInitial
      have hxStart : x = q.start :=
        hG.eq_start_of_mem_walk q.walk hxq hxSource
      simpa [hxStart]
    · rintro x hx
      have hxStart : x = q.start := Set.mem_singleton_iff.mp hx
      subst x
      refine ⟨q.start_mem_support, ?_⟩
      exact ⟨Sum.inl q, hpW, rfl⟩
  have htarget : q.support ∩ G.target = {q.finish} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxq, hxTarget⟩
      have hxFinish : x = q.finish :=
        hG.eq_finish_of_mem_walk q.walk hxq hxTarget
      simpa [hxFinish]
    · rintro x hx
      have hxFinish : x = q.finish := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨q.finish_mem_support,
        DWeb.IsCleanFiniteWarp.terminalFrontier_subset_target G hW
          ⟨(Sum.inl q : G.DPath), hpW, rfl⟩⟩
  refine ⟨q, rfl, ?_, hsource⟩
  rw [Set.inter_union_distrib_left, hsource, htarget]
  ext x
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]

/-- One-point augmentation preserves cleanliness in a normalized web.
The point is that the augmentation record gives only endpoint sets and
finite character; normalization upgrades those data to cleanliness. -/
theorem IsOnePointAugmentation.cleanFiniteWarp_of_normalized
    {G : DWeb V} (hG : G.IsNormalized) {W Wplus : Set G.DPath}
    (hW : G.IsCleanFiniteWarp W)
    (hplus : G.IsOnePointAugmentation W Wplus) :
    G.IsCleanFiniteWarp Wplus := by
  rcases hplus with
    ⟨a, ha, b, hb, hwarp, hfinite, hinitial, hterminal⟩
  apply AlternativeMaximalLinkage.cleanFiniteWarp_of_normalized
    hG hwarp hfinite
  · rw [hinitial]
    exact Set.insert_subset ha.1 hW.initialSet_subset_source
  · rw [hterminal]
    exact Set.insert_subset hb.1 hW.terminalFrontier_subset_target

/-- The direct maximal-linkage route, reduced to its genuine compactness
obligation.  The unconditional one-hole theorem supplies the strict
successor step; `CleanCoverChainUpperBounds` supplies precisely the missing
limit step. -/
theorem isLinkable_of_unhindered_of_cleanCoverChainUpperBounds
    (G : DWeb V) (hGnorm : G.IsNormalized) (hGunhindered : G.IsUnhindered)
    (hchain : CleanCoverChainUpperBounds G) :
    CardinalInduction.IsLinkable G := by
  let Good : Set (Set V) := {S | CleanlyCoverable G S}
  have hempty : CleanlyCoverable G ∅ := by
    refine ⟨∅, ?_, by simp [DWeb.initialSet]⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro p hp
      exact hp.elim
    · intro p hp
      exact hp.elim
    · simp [DWeb.vertexSet, DWeb.initialSet]
    · simp [DWeb.vertexSet, DWeb.terminalFrontier]
  have hzorn : ∀ c ⊆ Good, IsChain (· ⊆ ·) c →
      ∃ U ∈ Good, ∀ S ∈ c, S ⊆ U := by
    intro c hc hcc
    exact hchain c hc hcc
  obtain ⟨S, hSgood, hSmax⟩ := zorn_subset Good hzorn
  obtain ⟨W, hWclean, hWinitial⟩ := hSgood
  have hSsource : S ⊆ G.source := by
    rw [← hWinitial]
    exact hWclean.initialSet_subset_source
  by_cases hS : S = G.source
  · refine ⟨W, ?_⟩
    rw [← hS, ← hWinitial]
    exact isLinkageBetween_of_cleanFiniteWarp_of_normalized hGnorm hWclean
  · have hgap : (G.source \ G.initialSet W).Nonempty := by
      rw [hWinitial]
      by_contra hempty
      have hsourceSub : G.source ⊆ S := by
        intro a ha
        by_contra haS
        exact hempty ⟨a, ha, haS⟩
      exact hS (Set.Subset.antisymm hSsource hsourceSub)
    rcases G.oneHoleDichotomy_of_cleanFiniteWarp hWclean hgap with
      ⟨Wplus, hplus⟩ | hhindered
    · have hWplusClean : G.IsCleanFiniteWarp Wplus :=
        IsOnePointAugmentation.cleanFiniteWarp_of_normalized
          hGnorm hWclean hplus
      rcases hplus with
        ⟨a, ha, b, hb, _hwarp, _hfinite, hplusInitial, _hplusTerminal⟩
      have hplusGood : CleanlyCoverable G (insert a S) := by
        refine ⟨Wplus, hWplusClean, ?_⟩
        rw [hplusInitial, hWinitial]
      have hSsub : S ⊆ insert a S := Set.subset_insert a S
      have hmaxEq : insert a S = S :=
        Set.Subset.antisymm (hSmax hplusGood hSsub) hSsub
      exact False.elim (ha.2 (by rw [hWinitial, ← hmaxEq]; exact Set.mem_insert a S))
    · exact False.elim (hGunhindered hhindered)

/-- A full linkage is a greatest cleanly coverable source set, hence gives
all chain upper bounds at once.  This converse shows that the apparent
compactness premise above is not a cheap set-theoretic lemma. -/
theorem cleanCoverChainUpperBounds_of_isLinkable
    (G : DWeb V) (hGnorm : G.IsNormalized)
    (hlinkable : CardinalInduction.IsLinkable G) :
    CleanCoverChainUpperBounds G := by
  obtain ⟨L, hL⟩ := hlinkable
  have hLclean : G.IsCleanFiniteWarp L :=
    cleanFiniteWarp_of_normalized hGnorm hL.isWarp hL.finiteCharacter
      (hL.initialSet_eq ▸ Set.Subset.rfl)
      hL.terminalFrontier_subset
  have hsourceGood : CleanlyCoverable G G.source :=
    ⟨L, hLclean, hL.initialSet_eq⟩
  intro c hc _hchain
  refine ⟨G.source, hsourceGood, ?_⟩
  intro S hSc
  obtain ⟨W, hWclean, hWinitial⟩ := hc hSc
  rw [← hWinitial]
  exact hWclean.initialSet_subset_source

/-- On normalized unhindered webs, the chain-upper-bound assertion needed
by the naive Zorn route is equivalent to the theorem it was meant to prove.
Thus a proof of those upper bounds would already contain the deep infinite
Menger argument. -/
theorem cleanCoverChainUpperBounds_iff_isLinkable
    (G : DWeb V) (hGnorm : G.IsNormalized) (hGunhindered : G.IsUnhindered) :
    CleanCoverChainUpperBounds G ↔ CardinalInduction.IsLinkable G := by
  constructor
  · exact isLinkable_of_unhindered_of_cleanCoverChainUpperBounds
      G hGnorm hGunhindered
  · exact cleanCoverChainUpperBounds_of_isLinkable G hGnorm

end AlternativeMaximalLinkage
end Erdos599
