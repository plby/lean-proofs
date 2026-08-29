/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularMaximalWaveFiniteExchange
import ErdosProblems.Erdos599.SingularMarkedResidualTotalFiniteFactor
import ErdosProblems.Erdos599.SingularMarkedResidualContactBlocks

/-!
# A totally finite mixed block at a maximal residual hindrance

The marked route forced by a maximal residual hindrance has a canonical
first/last designated-contact window.  Factoring the *whole* old family
(designated plus lifted residual) along this finite route makes both the
changed old family and its replacement finite.  Everything outside the
finite block is retained literally.

This is stronger than merely knowing that finitely many designated paths
are touched: it reduces the remaining colour-sensitive repair to a finite
two-colour linkage while retaining the exact incoming and outgoing carrier
crossings of the mixed window.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularMaximalWaveTotalFiniteExchange

open DWeb Alternating
open SingularMarkedResidualColorOrder
  SingularMarkedResidualTouchedPaths
  SingularMarkedResidualFiniteFactor
  SingularMarkedResidualTotalFiniteFactor
  SingularMarkedResidualContactBlocks
  SingularMaximalWaveFiniteExchange
  SingularResidualWaveExchange

universe u

variable {V : Type u}

/-- If a designated target linkage has a hindered carrier deletion, then a
maximal residual hindrance exposes a finite mixed exchange block.  The
changed old block and its replacement are both finite, the untouched part
of the entire old family is fixed literally, and the canonical two-sided
designated-contact window is recorded. -/
theorem exists_totalFiniteWindowExchangeExactRelation_of_residual_hindered
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
        let L := G.liftDeleteFamily (G.vertexSet P) U
        let K := G.retarget
          (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
        IsReducedMarkedRoute K (P ∪ L) a b l ∧
        ¬ Disjoint
          (oneHoleRouteBackwardEdges K (P ∪ L) l) (familyEdges P) ∧
        (∃ r i j k : Fin (l.length - 1), ∃ x : V,
          r < i ∧ i ≤ j ∧ j < k ∧
          oneHoleRouteTarget l r = oneHoleRouteSource l i ∧
          oneHoleRouteSource l i = .pending x ∧
          OneHoleChosenForwardStep K (P ∪ L)
            (oneHoleRouteSource l r) (oneHoleRouteTarget l r) ∧
          IsDesignatedBackwardContact K P L l i ∧
          IsDesignatedBackwardContact K P L l j ∧
          oneHoleRouteSource l k = oneHoleRouteTarget l j ∧
          OneHoleChosenForwardStep K (P ∪ L)
            (oneHoleRouteSource l k) (oneHoleRouteTarget l k) ∧
          (oneHoleRouteSource l r).vertex ∉ K.vertexSet P ∧
          (oneHoleRouteTarget l r).vertex ∈ K.vertexSet P ∧
          (oneHoleRouteSource l k).vertex ∈ K.vertexSet P ∧
          (oneHoleRouteTarget l k).vertex ∉ K.vertexSet P) ∧
        let T := touchedDesignatedPaths K (P ∪ L) l
        let R := untouchedDesignatedPaths K (P ∪ L) l
        T.Finite ∧
          (touchedDesignatedPaths K P l).Nonempty ∧
          ∃ Qplus : Set K.DPath,
            Qplus.Finite ∧
            K.IsOnePointAugmentation T Qplus ∧
            (K.vertexSet (T ∪ Qplus)).Finite ∧
            Disjoint (K.vertexSet R) (K.vertexSet Qplus) ∧
            K.IsOnePointAugmentation (P ∪ L) (R ∪ Qplus) ∧
            K.initialSet Qplus = insert a (K.initialSet T) ∧
            K.terminalFrontier Qplus = insert b (K.terminalFrontier T) ∧
            ∃ C : Cyclowarp K,
              Qplus = C.pathPart ∧
              C.edges = oneHoleRouteToggledEdges K T l ∧
              C.isolated = isolatedVertices T := by
  obtain ⟨M, hMmax, hMh, hUh, hUfin, a, b, l, ha, hb, hbP,
      hl, hcontact, _hTfiniteP, hTnonemptyP, _Qold, _hlocalOld,
      _havoidOld, _hglobalOld⟩ :=
    exists_finiteSupportedOnePointAugmentation_of_residual_hindered
      hNorm hG hA hP hresidual
  let U := (G.delete (G.vertexSet P)).essentialWarpPart M.1
  let L := G.liftDeleteFamily (G.vertexSet P) U
  let K := G.retarget
    (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
  have hclean : K.IsCleanFiniteWarp (P ∪ L) :=
    combinedWarp_isCleanFiniteWarp hNorm hA hP hUh hUfin
  have hPL : Disjoint (K.vertexSet P) (K.vertexSet L) := by
    change Disjoint (G.vertexSet P)
      (G.vertexSet (G.liftDeleteFamily (G.vertexSet P) U))
    exact (G.vertexSet_liftDeleteFamily_disjoint hUh.1.2.1).symm
  have haP : a ∉ K.vertexSet P := ha.1.2
  obtain ⟨r, i, j, k, x, hri, hij, hjk, htargetR, hsourceI,
      hforwardR, hi, hj, hsourceK, hforwardK, hsourceRAvoid,
      htargetRMem, hsourceKMem, htargetKAvoid⟩ :=
    exists_orderedDesignatedContactWindow hPL hl haP hbP hcontact
  have haGap : a ∈ K.source \ K.initialSet (P ∪ L) := by
    refine ⟨ha.1.1, ?_⟩
    change a ∉ G.initialSet (P ∪ L)
    rw [G.initialSet_union, G.initialSet_liftDeleteFamily]
    rintro (haPinitial | haU)
    · obtain ⟨p, hpP, rfl⟩ := haPinitial
      exact ha.1.2 ⟨p, hpP, p.initial_mem_support⟩
    · exact ha.2 haU
  have hbGap : b ∈ K.target \ K.terminalFrontier (P ∪ L) := by
    refine ⟨Or.inl hb.1, ?_⟩
    change b ∉ G.terminalFrontier (P ∪ L)
    rw [G.terminalFrontier_union, G.terminalFrontier_liftDeleteFamily]
    rintro (hbPfrontier | hbU)
    · obtain ⟨p, hpP, hpterm⟩ := hbPfrontier
      exact hbP ⟨p, hpP, G.terminal_mem_support hpterm⟩
    · exact hb.2 hbU
  have hab : a ≠ b := by
    intro hab
    subst b
    have hlong : 1 < l.length := by
      have hiLt := i.isLt
      omega
    have hfirst := oneHoleRoute_first hl
    have hlast := oneHoleRoute_last hl
    have heq :
        l[0]'(by omega) = l[l.length - 1]'(by omega) := by
      exact hfirst.trans hlast.symm
    have hindices : 0 = l.length - 1 :=
      (hl.2.1.getElem_inj_iff).1 heq
    omega
  obtain ⟨hTfinite, Qplus, hQfinite, hlocal, hcarrierFinite,
      havoid, hglobal, hinitExact, htermExact,
      C, hCpath, hCedges, hCisolated⟩ :=
    exists_totalFiniteSupportedOnePointAugmentation_exactRelation
      hclean hl haGap hbGap hab
  exact ⟨M, hMmax, hMh, hUh, hUfin, a, b, l, ha, hb, hbP,
    hl, hcontact,
    ⟨r, i, j, k, x, hri, hij, hjk, htargetR, hsourceI,
      hforwardR, hi, hj, hsourceK, hforwardK, hsourceRAvoid,
      htargetRMem, hsourceKMem, htargetKAvoid⟩,
    hTfinite, hTnonemptyP, Qplus, hQfinite, hlocal, hcarrierFinite,
    havoid, hglobal, hinitExact, htermExact,
    C, hCpath, hCedges, hCisolated⟩

/-- Backward-compatible exact-endpoint projection, forgetting the cyclowarp
which realizes the finite toggled relation. -/
theorem exists_totalFiniteWindowExchangeExact_of_residual_hindered
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
        let L := G.liftDeleteFamily (G.vertexSet P) U
        let K := G.retarget
          (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
        IsReducedMarkedRoute K (P ∪ L) a b l ∧
        ¬ Disjoint
          (oneHoleRouteBackwardEdges K (P ∪ L) l) (familyEdges P) ∧
        (∃ r i j k : Fin (l.length - 1), ∃ x : V,
          r < i ∧ i ≤ j ∧ j < k ∧
          oneHoleRouteTarget l r = oneHoleRouteSource l i ∧
          oneHoleRouteSource l i = .pending x ∧
          OneHoleChosenForwardStep K (P ∪ L)
            (oneHoleRouteSource l r) (oneHoleRouteTarget l r) ∧
          IsDesignatedBackwardContact K P L l i ∧
          IsDesignatedBackwardContact K P L l j ∧
          oneHoleRouteSource l k = oneHoleRouteTarget l j ∧
          OneHoleChosenForwardStep K (P ∪ L)
            (oneHoleRouteSource l k) (oneHoleRouteTarget l k) ∧
          (oneHoleRouteSource l r).vertex ∉ K.vertexSet P ∧
          (oneHoleRouteTarget l r).vertex ∈ K.vertexSet P ∧
          (oneHoleRouteSource l k).vertex ∈ K.vertexSet P ∧
          (oneHoleRouteTarget l k).vertex ∉ K.vertexSet P) ∧
        let T := touchedDesignatedPaths K (P ∪ L) l
        let R := untouchedDesignatedPaths K (P ∪ L) l
        T.Finite ∧
          (touchedDesignatedPaths K P l).Nonempty ∧
          ∃ Qplus : Set K.DPath,
            Qplus.Finite ∧
            K.IsOnePointAugmentation T Qplus ∧
            (K.vertexSet (T ∪ Qplus)).Finite ∧
            Disjoint (K.vertexSet R) (K.vertexSet Qplus) ∧
            K.IsOnePointAugmentation (P ∪ L) (R ∪ Qplus) ∧
            K.initialSet Qplus = insert a (K.initialSet T) ∧
            K.terminalFrontier Qplus = insert b (K.terminalFrontier T) := by
  obtain ⟨M, hMmax, hMh, hUh, hUfin, a, b, l, ha, hb, hbP,
      hl, hcontact, hwindow, hTfinite, hTnonemptyP, Qplus, hQfinite,
      hlocal, hcarrierFinite, havoid, hglobal, hinitExact, htermExact,
      _C, _hCpath, _hCedges, _hCisolated⟩ :=
    exists_totalFiniteWindowExchangeExactRelation_of_residual_hindered
      hNorm hG hA hP hresidual
  exact ⟨M, hMmax, hMh, hUh, hUfin, a, b, l, ha, hb, hbP,
    hl, hcontact, hwindow, hTfinite, hTnonemptyP, Qplus, hQfinite,
    hlocal, hcarrierFinite, havoid, hglobal, hinitExact, htermExact⟩

/-- Backward-compatible projection of
`exists_totalFiniteWindowExchangeExact_of_residual_hindered` which forgets
the identities of the two fresh endpoints of the finite exchange. -/
theorem exists_totalFiniteWindowExchange_of_residual_hindered
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
        let L := G.liftDeleteFamily (G.vertexSet P) U
        let K := G.retarget
          (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
        IsReducedMarkedRoute K (P ∪ L) a b l ∧
        ¬ Disjoint
          (oneHoleRouteBackwardEdges K (P ∪ L) l) (familyEdges P) ∧
        (∃ r i j k : Fin (l.length - 1), ∃ x : V,
          r < i ∧ i ≤ j ∧ j < k ∧
          oneHoleRouteTarget l r = oneHoleRouteSource l i ∧
          oneHoleRouteSource l i = .pending x ∧
          OneHoleChosenForwardStep K (P ∪ L)
            (oneHoleRouteSource l r) (oneHoleRouteTarget l r) ∧
          IsDesignatedBackwardContact K P L l i ∧
          IsDesignatedBackwardContact K P L l j ∧
          oneHoleRouteSource l k = oneHoleRouteTarget l j ∧
          OneHoleChosenForwardStep K (P ∪ L)
            (oneHoleRouteSource l k) (oneHoleRouteTarget l k) ∧
          (oneHoleRouteSource l r).vertex ∉ K.vertexSet P ∧
          (oneHoleRouteTarget l r).vertex ∈ K.vertexSet P ∧
          (oneHoleRouteSource l k).vertex ∈ K.vertexSet P ∧
          (oneHoleRouteTarget l k).vertex ∉ K.vertexSet P) ∧
        let T := touchedDesignatedPaths K (P ∪ L) l
        let R := untouchedDesignatedPaths K (P ∪ L) l
        T.Finite ∧
          (touchedDesignatedPaths K P l).Nonempty ∧
          ∃ Qplus : Set K.DPath,
            Qplus.Finite ∧
            K.IsOnePointAugmentation T Qplus ∧
            (K.vertexSet (T ∪ Qplus)).Finite ∧
            Disjoint (K.vertexSet R) (K.vertexSet Qplus) ∧
            K.IsOnePointAugmentation (P ∪ L) (R ∪ Qplus) := by
  obtain ⟨M, hMmax, hMh, hUh, hUfin, a, b, l, ha, hb, hbP,
      hl, hcontact, hwindow, hTfinite, hTnonemptyP, Qplus, hQfinite,
      hlocal, hcarrierFinite, havoid, hglobal, _hinitExact, _htermExact⟩ :=
    exists_totalFiniteWindowExchangeExact_of_residual_hindered
      hNorm hG hA hP hresidual
  exact ⟨M, hMmax, hMh, hUh, hUfin, a, b, l, ha, hb, hbP,
    hl, hcontact, hwindow, hTfinite, hTnonemptyP, Qplus, hQfinite,
    hlocal, hcarrierFinite, havoid, hglobal⟩

#print axioms exists_totalFiniteWindowExchangeExactRelation_of_residual_hindered
#print axioms exists_totalFiniteWindowExchangeExact_of_residual_hindered
#print axioms exists_totalFiniteWindowExchange_of_residual_hindered

end SingularMaximalWaveTotalFiniteExchange
end CardinalInduction
end Erdos599
