/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.AlternativeMaximalLinkage
import ErdosProblems.Erdos599.SingularRetargetedRow

/-!
# Alternating exchange against a hindered residual

This file is the finite alternating-path core needed by a singular safe-batch
construction.  If deleting the carrier of a target linkage leaves a
hindrance, normalize that hindrance and put it beside the retained linkage.
After retargeting at the two terminal frontiers this is a clean finite warp.
The unconditional one-hole theorem therefore augments it.  Moreover, the
new terminal produced by the augmentation lies in the *original* target:
all terminals contributed by the residual hindrance were already occupied.

The theorem permits global rerouting of both colours.  Subsequent switching
arguments may use its exact endpoint equations; no literal preservation of
the input linkage is asserted.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularResidualWaveExchange

open AlternativeMaximalLinkage
open SingularRetargetedRow

universe u

variable {V : Type u}

/-- The union of a retained target linkage and a finite, source-normalized
residual hindrance is clean after retargeting at the original target together
with the residual frontier. -/
theorem combinedWarp_isCleanFiniteWarp
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source)
    {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    {U : Set ((G.delete (G.vertexSet P)).DPath)}
    (hU : (G.delete (G.vertexSet P)).IsHindrance U)
    (hUfin : (G.delete (G.vertexSet P)).HasFiniteCharacter U) :
    let X := G.vertexSet P
    let H := G.delete X
    let L := G.liftDeleteFamily X U
    let C := G.target ∪ H.terminalFrontier U
    (G.retarget C).IsCleanFiniteWarp (P ∪ L) := by
  let X := G.vertexSet P
  let H := G.delete X
  let L := G.liftDeleteFamily X U
  let C := G.target ∪ H.terminalFrontier U
  let K := G.retarget C
  have hLavoid : Disjoint (G.vertexSet L) X := by
    exact G.vertexSet_liftDeleteFamily_disjoint hU.1.2.1
  have hwarpG : G.IsWarp (P ∪ L) := by
    apply Set.PairwiseDisjoint.union hP.isWarp hU.1.1.liftDeleteFamily
    intro p hp q hq _hpq
    apply Set.disjoint_left.2
    intro x hxp hxq
    exact Set.disjoint_left.1 hLavoid
      ⟨q, hq, hxq⟩ ⟨p, hp, hxp⟩
  have hfinG : G.HasFiniteCharacter (P ∪ L) := by
    intro p hp
    rcases hp with hp | hp
    · exact hP.finiteCharacter hp
    · exact G.fd_hasFiniteCharacter_liftDeleteFamily hUfin hp
  have hinit : K.initialSet (P ∪ L) ⊆ K.source := by
    change G.initialSet (P ∪ L) ⊆ G.source
    rw [G.initialSet_union, hP.initialSet_eq,
      G.initialSet_liftDeleteFamily]
    exact Set.union_subset hA (hU.1.2.1.trans Set.sdiff_subset)
  have hsource : ∀ p ∈ (P ∪ L),
      p.support ∩ K.source ⊆ {p.initial} := by
    intro p hp x hx
    change x ∈ p.support ∩ G.source at hx
    exact Set.mem_singleton_iff.2
      (hNorm.eq_initial_of_mem_path p hx.1 hx.2)
  have hterminal : K.terminalFrontier (P ∪ L) ⊆ K.target := by
    change G.terminalFrontier (P ∪ L) ⊆ C
    rw [G.terminalFrontier_union, G.terminalFrontier_liftDeleteFamily]
    exact Set.union_subset
      (hP.terminalFrontier_subset.trans (Set.subset_union_left))
      Set.subset_union_right
  have htarget : ∀ p ∈ (P ∪ L), ∀ {x : V},
      x ∈ p.support → x ∈ K.target → K.terminal? p = some x := by
    intro p hp x hxp hxTarget
    change x ∈ C at hxTarget
    rcases hxTarget with hxTarget | hxFrontier
    · exact hNorm.terminal?_eq_of_mem_path p hxp hxTarget
    · change G.terminal? p = some x
      apply G.fd_terminal_eq_of_mem_support_frontier hwarpG hfinG hp hxp
      rw [G.terminalFrontier_union, G.terminalFrontier_liftDeleteFamily]
      exact Or.inr hxFrontier
  change K.IsCleanFiniteWarp (P ∪ L)
  apply K.fd_isCleanFiniteWarp_of_endpoint_clean
  · exact hwarpG
  · exact hfinG
  · exact hinit
  · exact hsource
  · exact hterminal
  · exact htarget

/-- If the carrier deletion of a target linkage is hindered, the finite
alternating-trail theorem produces a global rerouting which adds one source
and whose new terminal belongs to the original target. -/
theorem exists_onePointAugmentation_of_residual_hindered
    {G : DWeb V} (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    {A : Set V} (hA : A ⊆ G.source)
    {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hresidual : (G.delete (G.vertexSet P)).IsHindered) :
    ∃ U : Set ((G.delete (G.vertexSet P)).DPath),
      (G.delete (G.vertexSet P)).IsHindrance U ∧
      (G.delete (G.vertexSet P)).HasFiniteCharacter U ∧
      ∃ Jplus : Set G.DPath,
        ∃ a b : V,
          a ∈ G.source \ G.initialSet
            (P ∪ G.liftDeleteFamily (G.vertexSet P) U) ∧
          b ∈ G.target ∧
          DWeb.IsOnePointAugmentation
            (G.retarget
              (G.target ∪
                (G.delete (G.vertexSet P)).terminalFrontier U))
            (P ∪ G.liftDeleteFamily (G.vertexSet P) U) Jplus := by
  let X := G.vertexSet P
  let H := G.delete X
  obtain ⟨U, hU, hUfin, _hUsource⟩ :=
    H.exists_source_normalized_hindrance hresidual
  let L := G.liftDeleteFamily X U
  let C := G.target ∪ H.terminalFrontier U
  let K := G.retarget C
  let J := P ∪ L
  have hclean : K.IsCleanFiniteWarp J := by
    exact combinedWarp_isCleanFiniteWarp hNorm hA hP hU hUfin
  have hgapH : (H.source \ H.initialSet U).Nonempty := by
    rw [Set.nonempty_def]
    by_contra hempty
    apply hU.2
    apply Set.Subset.antisymm hU.1.2.1
    intro x hx
    by_contra hxU
    exact hempty ⟨x, hx, hxU⟩
  obtain ⟨a, haH⟩ := hgapH
  have hAsubX : A ⊆ X := by
    intro x hxA
    have hxInitial : x ∈ G.initialSet P := hP.initialSet_eq.symm ▸ hxA
    obtain ⟨p, hpP, rfl⟩ := hxInitial
    exact ⟨p, hpP, p.initial_mem_support⟩
  have haGap : a ∈ K.source \ K.initialSet J := by
    constructor
    · exact haH.1.1
    · change a ∉ G.initialSet (P ∪ L)
      rw [G.initialSet_union, hP.initialSet_eq,
        G.initialSet_liftDeleteFamily]
      intro ha
      rcases ha with haA | haU
      · exact haH.1.2 (hAsubX haA)
      · exact haH.2 haU
  have hKunhindered : K.IsUnhindered := by
    exact retarget_union_isUnhindered hG (H.terminalFrontier U)
  rcases K.oneHoleDichotomy_of_cleanFiniteWarp hclean ⟨a, haGap⟩ with
    haug | hhindered
  · obtain ⟨Jplus, hJplus⟩ := haug
    have hJplus' := hJplus
    obtain ⟨a', ha', b, hb, _hwarp, _hfinite, _hinit, _hterm⟩ := hJplus'
    have hbTarget : b ∈ G.target := by
      change b ∈ C \ G.terminalFrontier J at hb
      rcases hb.1 with hbG | hbU
      · exact hbG
      · exact False.elim (hb.2 (by
          change b ∈ G.terminalFrontier (P ∪ L)
          rw [G.terminalFrontier_union,
            G.terminalFrontier_liftDeleteFamily]
          exact Or.inr hbU))
    refine ⟨U, hU, hUfin, Jplus, a', b, ?_, hbTarget, ?_⟩
    · exact ha'
    · exact hJplus
  · exact False.elim (hKunhindered hhindered)

#print axioms combinedWarp_isCleanFiniteWarp
#print axioms exists_onePointAugmentation_of_residual_hindered

end SingularResidualWaveExchange
end CardinalInduction
end Erdos599
