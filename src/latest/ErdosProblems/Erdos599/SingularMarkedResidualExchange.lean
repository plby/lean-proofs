/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.OneHoleRouteBalance
import ErdosProblems.Erdos599.SingularResidualWaveExchange

/-!
# A marked-route witness for residual exchange

The endpoint equations of an arbitrary one-point augmentation forget which
old terminal belonged to the designated linkage and which belonged to the
residual wave.  The marked one-hole search contains strictly more useful
information: in an unhindered web its reachable set must meet the uncovered
target, and hence there is a reduced, contact-normalized marked route from an
uncovered source to that target.

This file exposes that route before the finite-component decomposition erases
its history.  The residual specialization starts outside the carrier of the
designated linkage and ends in the original target, not merely in the
retargeted residual frontier.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularMarkedResidualExchange

open DWeb
open AlternativeMaximalLinkage SingularRetargetedRow
  SingularResidualWaveExchange

universe u

variable {V : Type u}

/-- In an unhindered web, a clean finite warp with a source gap has an
uncovered target reachable by the contact-marked residual search.  The
result retains the reduced marked route, rather than only its decomposed
one-point-augmentation warp. -/
theorem exists_reducedMarkedRoute_to_target_of_unhindered
    (G : DWeb V) (hG : G.IsUnhindered)
    {J : Set G.DPath} (hJ : G.IsCleanFiniteWarp J)
    (hgap : (G.source \ G.initialSet J).Nonempty) :
    ∃ a b : V, ∃ l : List (OneHoleResidualState V),
      a ∈ G.source \ G.initialSet J ∧
      b ∈ G.target \ G.terminalFrontier J ∧
      IsReducedMarkedRoute G J a b l := by
  have htarget : ∃ b ∈ G.target \ G.terminalFrontier J,
      b ∈ G.OneHoleMarkedReachable J := by
    by_contra hnone
    have hdisjoint : Disjoint
        (G.target \ G.terminalFrontier J)
        (G.OneHoleMarkedReachable J) := by
      rw [Set.disjoint_left]
      intro b hb hbreach
      exact hnone ⟨b, hb, hbreach⟩
    have hblock : G.IsOneHoleBlockingSet J hJ.hasFiniteCharacter
        (G.OneHoleMarkedReachable J) :=
      G.isOneHoleBlockingSet_oneHoleMarkedReachable_of_no_targetGap
        J hJ hdisjoint
    let W := G.lastHitPrefixFamily J hJ.hasFiniteCharacter
      (G.OneHoleMarkedReachable J)
    have hW : G.IsHindrance W := by
      apply DWeb.IsWarp.isHindrance_lastHitPrefixFamily G hJ.isWarp
        hJ.hasFiniteCharacter hJ.initialSet_subset_source
        (DWeb.IsCleanFiniteWarp.initialSet_ne_source_of_gap_nonempty
          G hJ hgap)
        (G.OneHoleMarkedReachable J)
      exact G.roof_of_forwardBoundary hblock.1 hblock.2.1 hblock.2.2
    exact hG ⟨W, hW⟩
  obtain ⟨b, hb, hbreach⟩ := htarget
  have hbReady : b ∈ G.OneHoleReadyReachable J :=
    (G.oneHole_targetGap_marked_iff_ready hJ hb).1 hbreach
  rcases hbReady with ⟨a, ha, hab⟩
  obtain ⟨l, hl⟩ := exists_reduced_markedRoute G J hab
  exact ⟨a, b, l, ha, hb, hl⟩

/-- The reduced route has the canonical toggle certificate whenever its two
ends are distinct.  Thus downstream color-exchange arguments can reason
about the exact toggled edge relation before cyclowarp components are
decomposed. -/
theorem exists_toggleCertificate_to_target_of_unhindered
    (G : DWeb V) (hG : G.IsUnhindered)
    {J : Set G.DPath} (hJ : G.IsCleanFiniteWarp J)
    (hgap : (G.source \ G.initialSet J).Nonempty) :
    ∃ a b : V, a ∈ G.source \ G.initialSet J ∧
      b ∈ G.target \ G.terminalFrontier J ∧
      (a = b ∨ ∃ l : List (OneHoleResidualState V),
        IsReducedMarkedRoute G J a b l ∧
        ∃ T : OneHoleToggleCertificate G J a b,
          T.edges = oneHoleRouteToggledEdges G J l) := by
  obtain ⟨a, b, l, ha, hb, hl⟩ :=
    exists_reducedMarkedRoute_to_target_of_unhindered G hG hJ hgap
  refine ⟨a, b, ha, hb, ?_⟩
  by_cases hab : a = b
  · exact Or.inl hab
  · apply Or.inr
    let T : OneHoleToggleCertificate G J a b :=
      oneHoleToggleCertificateOfReducedRoute hJ ha hl
        (oneHoleRouteBalance G J a b l hJ ha hl)
    exact ⟨l, hl, T, rfl⟩

/-- Color-sensitive form of the residual one-point producer.  The marked
route starts at a source of the deleted residual which the hindrance misses,
and it ends at an uncovered vertex of the *original* target. -/
theorem exists_markedRoute_of_residual_hindered
    {G : DWeb V} (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    {A : Set V} (hA : A ⊆ G.source)
    {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hresidual : (G.delete (G.vertexSet P)).IsHindered) :
    ∃ U : Set ((G.delete (G.vertexSet P)).DPath),
      (G.delete (G.vertexSet P)).IsHindrance U ∧
      (G.delete (G.vertexSet P)).HasFiniteCharacter U ∧
      ∃ a b : V, ∃ l : List (OneHoleResidualState V),
        a ∈ (G.delete (G.vertexSet P)).source \
          (G.delete (G.vertexSet P)).initialSet U ∧
        b ∈ G.target ∧
        IsReducedMarkedRoute
          (G.retarget
            (G.target ∪
              (G.delete (G.vertexSet P)).terminalFrontier U))
          (P ∪ G.liftDeleteFamily (G.vertexSet P) U) a b l := by
  let X := G.vertexSet P
  let H := G.delete X
  obtain ⟨U, hU, hUfin, _hUsource⟩ :=
    H.exists_source_normalized_hindrance hresidual
  let L := G.liftDeleteFamily X U
  let C := G.target ∪ H.terminalFrontier U
  let K := G.retarget C
  let J := P ∪ L
  have hclean : K.IsCleanFiniteWarp J :=
    combinedWarp_isCleanFiniteWarp hNorm hA hP hU hUfin
  have hgapH : (H.source \ H.initialSet U).Nonempty := by
    rw [Set.nonempty_def]
    by_contra hempty
    apply hU.2
    apply Set.Subset.antisymm hU.1.2.1
    intro x hx
    by_contra hxU
    exact hempty ⟨x, hx, hxU⟩
  obtain ⟨a₀, ha₀⟩ := hgapH
  have hAsubX : A ⊆ X := by
    intro x hxA
    have hxInitial : x ∈ G.initialSet P := hP.initialSet_eq.symm ▸ hxA
    obtain ⟨p, hpP, rfl⟩ := hxInitial
    exact ⟨p, hpP, p.initial_mem_support⟩
  have ha₀Gap : a₀ ∈ K.source \ K.initialSet J := by
    constructor
    · exact ha₀.1.1
    · change a₀ ∉ G.initialSet (P ∪ L)
      rw [G.initialSet_union, hP.initialSet_eq,
        G.initialSet_liftDeleteFamily]
      intro ha
      rcases ha with haA | haU
      · exact ha₀.1.2 (hAsubX haA)
      · exact ha₀.2 haU
  have hKunhindered : K.IsUnhindered :=
    retarget_union_isUnhindered hG (H.terminalFrontier U)
  obtain ⟨a, b, l, ha, hb, hl⟩ :=
    exists_reducedMarkedRoute_to_target_of_unhindered
      K hKunhindered hclean ⟨a₀, ha₀Gap⟩
  have haNotX : a ∉ X := by
    rintro ⟨p, hpP, hap⟩
    have haSource : a ∈ G.source := ha.1
    have hae : a = p.initial := hNorm.eq_initial_of_mem_path p hap haSource
    have haA : a ∈ A := by
      rw [hae]
      rw [← hP.initialSet_eq]
      exact ⟨p, hpP, rfl⟩
    exact ha.2 (by
      change a ∈ G.initialSet (P ∪ L)
      rw [G.initialSet_union, hP.initialSet_eq]
      exact Or.inl haA)
  have haH : a ∈ H.source \ H.initialSet U := by
    refine ⟨⟨ha.1, haNotX⟩, ?_⟩
    intro haU
    apply ha.2
    change a ∈ G.initialSet (P ∪ L)
    rw [G.initialSet_union, G.initialSet_liftDeleteFamily]
    exact Or.inr haU
  have hbTarget : b ∈ G.target := by
    change b ∈ C \ G.terminalFrontier J at hb
    rcases hb.1 with hbG | hbU
    · exact hbG
    · exact False.elim (hb.2 (by
        change b ∈ G.terminalFrontier (P ∪ L)
        rw [G.terminalFrontier_union,
          G.terminalFrontier_liftDeleteFamily]
        exact Or.inr hbU))
  exact ⟨U, hU, hUfin, a, b, l, haH, hbTarget, hl⟩

#print axioms exists_reducedMarkedRoute_to_target_of_unhindered
#print axioms exists_toggleCertificate_to_target_of_unhindered
#print axioms exists_markedRoute_of_residual_hindered

end SingularMarkedResidualExchange
end CardinalInduction
end Erdos599
