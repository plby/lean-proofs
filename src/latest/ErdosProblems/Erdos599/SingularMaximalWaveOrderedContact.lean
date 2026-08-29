/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularMarkedResidualDesignatedContact

/-!
# Pointwise maximal-wave contact and its canonical order block

The maximal residual producer chooses one marked route.  Selective
switching also needs a pointwise theorem: any marked route against the
finite essential part of a fixed maximal residual hindrance has to use the
designated colour.  This file exposes that fact without repeating the
existential selection interface.

Together with `exists_orderedDesignatedContactBlock`, a target-fresh route
therefore has canonical first and last designated cancellations, a pending
state at the first one, and a forward transition immediately after the last
one.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularMaximalWaveOrderedContact

open DWeb Alternating
open SingularMarkedResidualColorIsolation
  SingularMarkedResidualColorOrder
  SingularMarkedResidualDesignatedContact
  SingularMaximalWaveTargetAbsorption
  SingularResidualWaveExchange

universe u

variable {V : Type u}

/-- Pointwise form of maximal-wave colour forcing.  No existential choice
of the route remains in the interface. -/
theorem markedRoute_not_disjoint_designatedBackward_of_maximalHindrance
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source)
    {P : Set G.DPath} (hP : IsLinkageBetween G A G.target P)
    (M : (G.delete (G.vertexSet P)).Wave) (hMmax : IsMax M)
    (hMh : (G.delete (G.vertexSet P)).IsHindrance M.1)
    {a b : V} {l : List (OneHoleResidualState V)}
    (ha : a ∈ (G.delete (G.vertexSet P)).source \
      (G.delete (G.vertexSet P)).initialSet
        ((G.delete (G.vertexSet P)).essentialWarpPart M.1))
    (hb : b ∈ G.target \
      (G.delete (G.vertexSet P)).terminalFrontier
        ((G.delete (G.vertexSet P)).essentialWarpPart M.1))
    (hl : IsReducedMarkedRoute
      (G.retarget
        (G.target ∪
          (G.delete (G.vertexSet P)).terminalFrontier
            ((G.delete (G.vertexSet P)).essentialWarpPart M.1)))
      (P ∪ G.liftDeleteFamily (G.vertexSet P)
        ((G.delete (G.vertexSet P)).essentialWarpPart M.1)) a b l) :
    ¬ Disjoint
      (oneHoleRouteBackwardEdges
        (G.retarget
          (G.target ∪
            (G.delete (G.vertexSet P)).terminalFrontier
              ((G.delete (G.vertexSet P)).essentialWarpPart M.1)))
        (P ∪ G.liftDeleteFamily (G.vertexSet P)
          ((G.delete (G.vertexSet P)).essentialWarpPart M.1)) l)
      (familyEdges P) := by
  let X : Set V := G.vertexSet P
  let H : DWeb V := G.delete X
  let U : Set H.DPath := H.essentialWarpPart M.1
  let L : Set G.DPath := G.liftDeleteFamily X U
  let C : Set V := G.target ∪ H.terminalFrontier U
  let K : DWeb V := G.retarget C
  have hUh : H.IsHindrance U :=
    (essentialWarpPart_isHindrance_hasFiniteCharacter M hMh).1
  have hUfin : H.HasFiniteCharacter U :=
    (essentialWarpPart_isHindrance_hasFiniteCharacter M hMh).2
  have hclean : K.IsCleanFiniteWarp (P ∪ L) :=
    combinedWarp_isCleanFiniteWarp hNorm hA hP hUh hUfin
  have hLclean : K.IsCleanFiniteWarp L :=
    DWeb.IsCleanFiniteWarp.subfamily hclean Set.subset_union_right
  have hPL : Disjoint (K.vertexSet P) (K.vertexSet L) := by
    change Disjoint X (G.vertexSet L)
    exact (G.vertexSet_liftDeleteFamily_disjoint hUh.1.2.1).symm
  have haP : a ∉ K.vertexSet P := ha.1.2
  have haL : a ∈ K.source \ K.initialSet L := by
    refine ⟨ha.1.1, ?_⟩
    change a ∉ G.initialSet L
    rw [G.initialSet_liftDeleteFamily]
    exact ha.2
  have hbL : b ∈ K.target \ K.terminalFrontier L := by
    refine ⟨Or.inl hb.1, ?_⟩
    change b ∉ G.terminalFrontier L
    rw [G.terminalFrontier_liftDeleteFamily]
    exact hb.2
  intro hnoP
  obtain ⟨Lplus, hplus, havoid, hbLplus⟩ :=
    exists_residual_onePointAugmentation_avoiding_with_terminal
      hPL hLclean hl haP hnoP haL hbL
  change Set G.DPath at Lplus
  change (G.retarget C).IsOnePointAugmentation L Lplus at hplus
  change Disjoint X (G.vertexSet Lplus) at havoid
  change b ∈ G.terminalFrontier Lplus at hbLplus
  have hW : H.IsWave
      (G.restrictDeleteFamily X Lplus havoid.symm) :=
    residualWave_of_avoiding_onePointAugmentation
      G X hUh.1 hplus havoid
  have hbW : b ∈ H.terminalFrontier
      (G.restrictDeleteFamily X Lplus havoid.symm) := by
    rw [G.terminalFrontier_restrictDeleteFamily]
    exact hbLplus
  have hbNotX : b ∉ X := by
    intro hbX
    obtain ⟨p, hp, hpterm⟩ := hbLplus
    exact Set.disjoint_left.1 havoid hbX
      ⟨p, hp, G.terminal_mem_support hpterm⟩
  have hbHTarget : b ∈ H.target := ⟨hb.1, hbNotX⟩
  exact hb.2
    (target_mem_terminalFrontier_essentialWarpPart_of_isMax
      M hMmax hW hbHTarget hbW)

/-- The existential maximal-residual route can be chosen with a fresh target
and its complete first/last designated-contact order data.  This is the
direct input expected by the finite selective switching step. -/
theorem exists_maximalResidualRoute_with_orderedDesignatedContactBlock
    {G : DWeb V} (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    {A : Set V} (hA : A ⊆ G.source)
    {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hresidual : (G.delete (G.vertexSet P)).IsHindered) :
    ∃ M : (G.delete (G.vertexSet P)).Wave,
      IsMax M ∧ (G.delete (G.vertexSet P)).IsHindrance M.1 ∧
      let U := (G.delete (G.vertexSet P)).essentialWarpPart M.1
      (G.delete (G.vertexSet P)).IsHindrance U ∧
      (G.delete (G.vertexSet P)).HasFiniteCharacter U ∧
      ∃ a b : V, ∃ l : List (OneHoleResidualState V),
        a ∈ (G.delete (G.vertexSet P)).source \
          (G.delete (G.vertexSet P)).initialSet U ∧
        b ∈ G.target \
          (G.delete (G.vertexSet P)).terminalFrontier U ∧
        b ∉ G.vertexSet P ∧
        IsReducedMarkedRoute
          (G.retarget
            (G.target ∪
              (G.delete (G.vertexSet P)).terminalFrontier U))
          (P ∪ G.liftDeleteFamily (G.vertexSet P) U) a b l ∧
        ∃ i j k : Fin (l.length - 1), ∃ x : V,
          IsDesignatedBackwardContact
            (G.retarget
              (G.target ∪
                (G.delete (G.vertexSet P)).terminalFrontier U))
            P (G.liftDeleteFamily (G.vertexSet P) U) l i ∧
          (∀ i', i' < i → ¬ IsDesignatedBackwardContact
            (G.retarget
              (G.target ∪
                (G.delete (G.vertexSet P)).terminalFrontier U))
            P (G.liftDeleteFamily (G.vertexSet P) U) l i') ∧
          oneHoleRouteSource l i = .pending x ∧
          IsDesignatedBackwardContact
            (G.retarget
              (G.target ∪
                (G.delete (G.vertexSet P)).terminalFrontier U))
            P (G.liftDeleteFamily (G.vertexSet P) U) l j ∧
          (∀ j', j < j' → ¬ IsDesignatedBackwardContact
            (G.retarget
              (G.target ∪
                (G.delete (G.vertexSet P)).terminalFrontier U))
            P (G.liftDeleteFamily (G.vertexSet P) U) l j') ∧
          i ≤ j ∧ j < k ∧
          oneHoleRouteSource l k = oneHoleRouteTarget l j ∧
          OneHoleChosenForwardStep
            (G.retarget
              (G.target ∪
                (G.delete (G.vertexSet P)).terminalFrontier U))
            (P ∪ G.liftDeleteFamily (G.vertexSet P) U)
            (oneHoleRouteSource l k) (oneHoleRouteTarget l k) := by
  obtain ⟨M, hMmax, hMh, hUh, hUfin, a, b, l, ha, hb, hbP, hl⟩ :=
    exists_maximalHindrance_markedRoute_targetFresh_of_residual_hindered
      hNorm hG hA hP hresidual
  let U := (G.delete (G.vertexSet P)).essentialWarpPart M.1
  let L := G.liftDeleteFamily (G.vertexSet P) U
  let K := G.retarget
    (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
  have hnot : ¬ Disjoint
      (oneHoleRouteBackwardEdges K (P ∪ L) l) (familyEdges P) := by
    exact markedRoute_not_disjoint_designatedBackward_of_maximalHindrance
      hNorm hA hP M hMmax hMh ha hb hl
  have hPL : Disjoint (K.vertexSet P) (K.vertexSet L) := by
    change Disjoint (G.vertexSet P)
      (G.vertexSet (G.liftDeleteFamily (G.vertexSet P) U))
    exact (G.vertexSet_liftDeleteFamily_disjoint hUh.1.2.1).symm
  have haP : a ∉ K.vertexSet P := ha.1.2
  obtain ⟨i, j, k, x, hi, hfirst, hsource, hj, hlast,
      hij, hjk, hsourceK, hforwardK⟩ :=
    exists_orderedDesignatedContactBlock hPL hl haP hbP hnot
  exact ⟨M, hMmax, hMh, hUh, hUfin, a, b, l, ha, hb, hbP, hl,
    i, j, k, x, hi, hfirst, hsource, hj, hlast,
    hij, hjk, hsourceK, hforwardK⟩

#print axioms markedRoute_not_disjoint_designatedBackward_of_maximalHindrance
#print axioms exists_maximalResidualRoute_with_orderedDesignatedContactBlock

end SingularMaximalWaveOrderedContact
end CardinalInduction
end Erdos599
