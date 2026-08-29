/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularMarkedResidualLocalizedRealization
import ErdosProblems.Erdos599.UndirectedFiniteEndpoint

/-!
# Total finite support of a marked residual exchange

A finite marked route meets only finitely many members of the *whole* old
warp, not merely finitely many members of one distinguished colour.  Applying
the localized realization theorem with the whole old warp as the designated
family therefore factors every untouched old path literally out of the
switch.  Both the old family that is changed and its replacement are finite.

This reduces the remaining colour-sensitive repair to a genuinely finite
two-colour problem even when the residual wave itself has infinitely many
members.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularMarkedResidualTotalFiniteFactor

open DWeb Alternating
open SingularMarkedResidualTouchedPaths
open SingularMarkedResidualFiniteFactor
open SingularMarkedResidualLocalizedRealization

universe u

variable {V : Type u}

/-- The initial set of a finite path family is finite. -/
private theorem initialSet_finite_of_family_finite
    (G : DWeb V) {W : Set G.DPath} (hW : W.Finite) :
    (G.initialSet W).Finite := by
  have himage : ((fun p : G.DPath ↦ p.initial) '' W).Finite :=
    hW.image fun p : G.DPath ↦ p.initial
  simpa only [DWeb.initialSet] using himage

/-- The carrier of a finite family of finite paths is finite. -/
private theorem vertexSet_finite_of_family_finite
    (G : DWeb V) {W : Set G.DPath} (hW : W.Finite)
    (hcharacter : G.HasFiniteCharacter W) :
    (G.vertexSet W).Finite := by
  have hunion : G.vertexSet W = ⋃ p ∈ W, p.support := by
    ext x
    simp [DWeb.vertexSet]
  rw [hunion]
  exact hW.biUnion fun p hp ↦ by
    obtain ⟨q, rfl⟩ := hcharacter hp
    exact q.support_finite

/-- A marked one-point augmentation changes only finitely many members of
the entire old clean finite warp.  The untouched complement is retained
literally, and the local replacement family is finite as well. -/
theorem exists_totalFiniteSupportedOnePointAugmentation_exactRelation
    {G : DWeb V} {J : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hJ : G.IsCleanFiniteWarp J)
    (hl : IsReducedMarkedRoute G J a b l)
    (ha : a ∈ G.source \ G.initialSet J)
    (hb : b ∈ G.target \ G.terminalFrontier J)
    (hab : a ≠ b) :
    let T := touchedDesignatedPaths G J l
    let R := untouchedDesignatedPaths G J l
    T.Finite ∧
      ∃ Qplus : Set G.DPath,
        Qplus.Finite ∧
        G.IsOnePointAugmentation T Qplus ∧
        (G.vertexSet (T ∪ Qplus)).Finite ∧
        Disjoint (G.vertexSet R) (G.vertexSet Qplus) ∧
        G.IsOnePointAugmentation J (R ∪ Qplus) ∧
        G.initialSet Qplus = insert a (G.initialSet T) ∧
        G.terminalFrontier Qplus = insert b (G.terminalFrontier T) ∧
        ∃ C : Cyclowarp G,
          Qplus = C.pathPart ∧
          C.edges = oneHoleRouteToggledEdges G T l ∧
          C.isolated = isolatedVertices T := by
  let T := touchedDesignatedPaths G J l
  let R := untouchedDesignatedPaths G J l
  have hJwarp : G.IsWarp J := hJ.1
  have hTfinite : T.Finite := touchedDesignatedPaths_finite hJwarp l
  have hdisEmpty : Disjoint (G.vertexSet J)
      (G.vertexSet (∅ : Set G.DPath)) := by
    rw [Set.disjoint_right]
    rintro x ⟨p, hp, _hxp⟩
    exact hp.elim
  obtain ⟨Qplus, hplus, hRplus, hglobal, hinitExact, htermExact,
      C, hCpath, hCedges, hCisolated⟩ :=
    exists_onePointAugmentation_fixing_untouched_exactRelation
      (P := J) (L := ∅) hJwarp hdisEmpty (by simpa using hJ)
        (by simpa using hl) (by simpa using ha) (by simpa using hb) hab
  have hplusT : G.IsOnePointAugmentation T Qplus := by
    simpa only [Set.union_empty] using hplus
  have hplusT' := hplusT
  obtain ⟨a', _ha', b', _hb', hQwarp, hQcharacter,
      hQinitial, _hQterminal⟩ := hplusT'
  have hTinitialFinite : (G.initialSet T).Finite :=
    initialSet_finite_of_family_finite G hTfinite
  have hQinitialFinite : (G.initialSet Qplus).Finite := by
    rw [hQinitial]
    exact hTinitialFinite.insert a'
  have hQfinite : Qplus.Finite :=
    AharoniBerger.finite_of_isWarp_of_initialSet_finite
      G hQwarp hQinitialFinite
  have hTcharacter : G.HasFiniteCharacter T := by
    intro p hp
    exact hJ.2.1 (touchedDesignatedPaths_subset G J l hp)
  have hcarrierFinite : (G.vertexSet (T ∪ Qplus)).Finite := by
    rw [G.vertexSet_union]
    exact (vertexSet_finite_of_family_finite G hTfinite hTcharacter).union
      (vertexSet_finite_of_family_finite G hQfinite hQcharacter)
  have hglobalJ : G.IsOnePointAugmentation J (R ∪ Qplus) := by
    simpa only [Set.union_empty] using hglobal
  exact ⟨hTfinite, Qplus, hQfinite, hplusT, hcarrierFinite,
    hRplus, hglobalJ, by simpa only [Set.union_empty] using hinitExact,
    by simpa only [Set.union_empty] using htermExact,
    C, hCpath, by simpa only [Set.union_empty] using hCedges,
    by simpa only [Set.union_empty] using hCisolated⟩

/-- Backward-compatible exact-endpoint total finite factor, forgetting the
cyclowarp which realizes the exact toggled relation. -/
theorem exists_totalFiniteSupportedOnePointAugmentation_exact
    {G : DWeb V} {J : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hJ : G.IsCleanFiniteWarp J)
    (hl : IsReducedMarkedRoute G J a b l)
    (ha : a ∈ G.source \ G.initialSet J)
    (hb : b ∈ G.target \ G.terminalFrontier J)
    (hab : a ≠ b) :
    let T := touchedDesignatedPaths G J l
    let R := untouchedDesignatedPaths G J l
    T.Finite ∧
      ∃ Qplus : Set G.DPath,
        Qplus.Finite ∧
        G.IsOnePointAugmentation T Qplus ∧
        (G.vertexSet (T ∪ Qplus)).Finite ∧
        Disjoint (G.vertexSet R) (G.vertexSet Qplus) ∧
        G.IsOnePointAugmentation J (R ∪ Qplus) ∧
        G.initialSet Qplus = insert a (G.initialSet T) ∧
        G.terminalFrontier Qplus = insert b (G.terminalFrontier T) := by
  obtain ⟨hTfinite, Qplus, hQfinite, hplus, hcarrierFinite,
      hdisjoint, hglobal, hinitial, hterminal,
      _C, _hCpath, _hCedges, _hCisolated⟩ :=
    exists_totalFiniteSupportedOnePointAugmentation_exactRelation
      hJ hl ha hb hab
  exact ⟨hTfinite, Qplus, hQfinite, hplus, hcarrierFinite,
    hdisjoint, hglobal, hinitial, hterminal⟩

/-- Endpoint-erased compatibility wrapper for the total finite factor. -/
theorem exists_totalFiniteSupportedOnePointAugmentation
    {G : DWeb V} {J : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hJ : G.IsCleanFiniteWarp J)
    (hl : IsReducedMarkedRoute G J a b l)
    (ha : a ∈ G.source \ G.initialSet J)
    (hb : b ∈ G.target \ G.terminalFrontier J)
    (hab : a ≠ b) :
    let T := touchedDesignatedPaths G J l
    let R := untouchedDesignatedPaths G J l
    T.Finite ∧
      ∃ Qplus : Set G.DPath,
        Qplus.Finite ∧
        G.IsOnePointAugmentation T Qplus ∧
        (G.vertexSet (T ∪ Qplus)).Finite ∧
        Disjoint (G.vertexSet R) (G.vertexSet Qplus) ∧
        G.IsOnePointAugmentation J (R ∪ Qplus) := by
  obtain ⟨hTfinite, Qplus, hQfinite, hplus, hcarrierFinite,
      hdisjoint, hglobal, _hinit, _hterminal⟩ :=
    exists_totalFiniteSupportedOnePointAugmentation_exact
      hJ hl ha hb hab
  exact ⟨hTfinite, Qplus, hQfinite, hplus, hcarrierFinite,
    hdisjoint, hglobal⟩

/-- At every infinite induction cardinal, the whole region modified by a
marked exchange is a strictly lower-cardinality auxiliary carrier.  This is
the cardinal form consumed by a subsequent local colour-repair call to the
lower induction hypothesis. -/
theorem exists_totalSmallSupportedOnePointAugmentation
    {G : DWeb V} {J : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hJ : G.IsCleanFiniteWarp J)
    (hl : IsReducedMarkedRoute G J a b l)
    (ha : a ∈ G.source \ G.initialSet J)
    (hb : b ∈ G.target \ G.terminalFrontier J)
    (hab : a ≠ b) {kappa : Cardinal.{u}}
    (hkappa : Cardinal.aleph0.{u} ≤ kappa) :
    let T := touchedDesignatedPaths G J l
    let R := untouchedDesignatedPaths G J l
    T.Finite ∧
      ∃ Qplus : Set G.DPath,
        Qplus.Finite ∧
        G.IsOnePointAugmentation T Qplus ∧
        Cardinal.mk (G.vertexSet (T ∪ Qplus)) < kappa ∧
        Disjoint (G.vertexSet R) (G.vertexSet Qplus) ∧
        G.IsOnePointAugmentation J (R ∪ Qplus) := by
  obtain ⟨hTfinite, Qplus, hQfinite, hplus, hcarrierFinite,
      hdisjoint, hglobal⟩ :=
    exists_totalFiniteSupportedOnePointAugmentation hJ hl ha hb hab
  have hcarrierSmall :
      Cardinal.mk (G.vertexSet
        (touchedDesignatedPaths G J l ∪ Qplus)) < kappa := by
    letI : Finite (G.vertexSet
        (touchedDesignatedPaths G J l ∪ Qplus)) :=
      Set.finite_coe_iff.mpr hcarrierFinite
    exact Cardinal.mk_lt_aleph0.trans_le hkappa
  exact ⟨hTfinite, Qplus, hQfinite, hplus, hcarrierSmall,
    hdisjoint, hglobal⟩

#print axioms exists_totalFiniteSupportedOnePointAugmentation_exactRelation
#print axioms exists_totalFiniteSupportedOnePointAugmentation_exact
#print axioms exists_totalFiniteSupportedOnePointAugmentation
#print axioms exists_totalSmallSupportedOnePointAugmentation

end SingularMarkedResidualTotalFiniteFactor
end CardinalInduction
end Erdos599
