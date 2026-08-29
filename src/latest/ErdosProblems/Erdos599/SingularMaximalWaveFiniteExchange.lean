/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularMaximalWaveOrderedContact
import ErdosProblems.Erdos599.SingularMarkedResidualLocalizedRealization

/-!
# Finite-support exchange against a maximal residual hindrance

The marked route forced by a maximal residual hindrance meets only finitely
many members of the designated linkage.  Factoring the untouched designated
members out before realizing the toggle therefore gives a genuine one-point
augmentation which changes only a finite, nonempty designated subfamily.
Every untouched designated path occurs literally in the global output.

This is the local exchange datum needed by a cofinal diagonal construction:
the carrier of the provisional linkage may be singular, but each individual
maximal-wave repair has finite designated support.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularMaximalWaveFiniteExchange

open DWeb Alternating
open SingularMarkedResidualColorOrder
  SingularMarkedResidualTouchedPaths
  SingularMarkedResidualFiniteFactor
  SingularMarkedResidualLocalizedRealization
  SingularMaximalWaveOrderedContact
  SingularResidualWaveExchange

universe u

variable {V : Type u}

/-- If deleting a designated target linkage is hindered, a maximal residual
hindrance produces a one-point exchange supported on finitely many (and at
least one) designated paths.  The complement of that finite subfamily is
fixed literally in the resulting global one-point augmentation. -/
theorem exists_finiteSupportedOnePointAugmentation_of_residual_hindered
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
        let T := touchedDesignatedPaths K P l
        let R := untouchedDesignatedPaths K P l
        T.Finite ∧ T.Nonempty ∧
          ∃ Qplus : Set K.DPath,
            K.IsOnePointAugmentation (T ∪ L) Qplus ∧
            Disjoint (K.vertexSet R) (K.vertexSet Qplus) ∧
            K.IsOnePointAugmentation (P ∪ L) (R ∪ Qplus) := by
  obtain ⟨M, hMmax, hMh, hUh, hUfin, a, b, l, ha, hb, hbP, hl,
      i, _j, _k, _x, hi, _hfirst, _hsource, _hj, _hlast,
      _hij, _hjk, _hsourceK, _hforwardK⟩ :=
    exists_maximalResidualRoute_with_orderedDesignatedContactBlock
      hNorm hG hA hP hresidual
  let U := (G.delete (G.vertexSet P)).essentialWarpPart M.1
  let L := G.liftDeleteFamily (G.vertexSet P) U
  let K := G.retarget
    (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
  let T := touchedDesignatedPaths K P l
  let R := untouchedDesignatedPaths K P l
  have hcontact : ¬ Disjoint
      (oneHoleRouteBackwardEdges K (P ∪ L) l) (familyEdges P) :=
    (exists_designatedBackwardContact_iff K P L l).1 ⟨i, hi⟩
  have hclean : K.IsCleanFiniteWarp (P ∪ L) :=
    combinedWarp_isCleanFiniteWarp hNorm hA hP hUh hUfin
  have hPL : Disjoint (K.vertexSet P) (K.vertexSet L) := by
    change Disjoint (G.vertexSet P)
      (G.vertexSet (G.liftDeleteFamily (G.vertexSet P) U))
    exact (G.vertexSet_liftDeleteFamily_disjoint hUh.1.2.1).symm
  have hPK : K.IsWarp P := hP.isWarp
  have haGap : a ∈ K.source \ K.initialSet (P ∪ L) := by
    refine ⟨ha.1.1, ?_⟩
    change a ∉ G.initialSet (P ∪ L)
    rw [G.initialSet_union, G.initialSet_liftDeleteFamily]
    rintro (haP | haU)
    · obtain ⟨p, hpP, rfl⟩ := haP
      exact ha.1.2 ⟨p, hpP, p.initial_mem_support⟩
    · exact ha.2 haU
  have hbGap : b ∈ K.target \ K.terminalFrontier (P ∪ L) := by
    refine ⟨Or.inl hb.1, ?_⟩
    change b ∉ G.terminalFrontier (P ∪ L)
    rw [G.terminalFrontier_union, G.terminalFrontier_liftDeleteFamily]
    rintro (hbFrontierP | hbFrontierU)
    · obtain ⟨p, hpP, hpterm⟩ := hbFrontierP
      exact hbP ⟨p, hpP, G.terminal_mem_support hpterm⟩
    · exact hb.2 hbFrontierU
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
  have hTfinite : T.Finite :=
    touchedDesignatedPaths_finite hPK l
  have hTnonempty : T.Nonempty := by
    have heT :
        ((oneHoleRouteTarget l i).vertex,
          (oneHoleRouteSource l i).vertex) ∈ familyEdges T := by
      apply familyEdge_mem_touched_of_left_route_vertex
        (hxy := hi.2)
      apply state_vertex_mem_routeVertexSet
      exact List.getElem_mem (show i.1 + 1 < l.length by omega)
    simp only [familyEdges, Set.mem_iUnion] at heT
    obtain ⟨p, hpT, _he⟩ := heT
    exact ⟨p, hpT⟩
  obtain ⟨Qplus, hlocalPlus, hRplus, hglobalPlus⟩ :=
    exists_onePointAugmentation_fixing_untouched
      hPK hPL hclean hl haGap hbGap hab
  exact ⟨M, hMmax, hMh, hUh, hUfin, a, b, l, ha, hb, hbP,
    hl, hcontact, hTfinite, hTnonempty, Qplus,
    hlocalPlus, hRplus, hglobalPlus⟩

#print axioms exists_finiteSupportedOnePointAugmentation_of_residual_hindered

end SingularMaximalWaveFiniteExchange
end CardinalInduction
end Erdos599
