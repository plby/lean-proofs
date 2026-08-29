/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteDeletion
import ErdosProblems.Erdos599.RoofQuotient

/-!
# Removing a target sublinkage from a combined wave

If a wave is split into a retained path subfamily and its complementary
members, deleting the carrier of the retained family leaves the complement
as a wave.  The roof argument is elementary but useful in finite colour
exchange: a target path in the deleted web cannot meet a terminal belonging
to the deleted subfamily, so the terminal supplied by the combined wave must
belong to the complementary family.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularCombinedWaveResidualExtraction

open DWeb

universe u

variable {V : Type u}

/-- Distinct subfamilies of a warp have disjoint carriers when one is the
set-theoretic complement of the other. -/
theorem vertexSet_diff_disjoint
    (G : DWeb V) {J P : Set G.DPath}
    (hJ : G.IsWarp J) (hPJ : P ⊆ J) :
    Disjoint (G.vertexSet (J \ P)) (G.vertexSet P) := by
  apply Set.disjoint_left.2
  rintro x ⟨p, hp, hxp⟩ ⟨q, hqP, hxq⟩
  have hpq : p ≠ q := by
    intro hpq
    subst q
    exact hp.2 hqP
  exact Set.disjoint_left.1 (hJ hp.1 (hPJ hqP) hpq) hxp hxq

/-- If two path families have disjoint carriers, removing the left family
from their union leaves the right family literally. -/
theorem union_diff_left_eq_right_of_vertexSet_disjoint
    (G : DWeb V) {P L : Set G.DPath}
    (hPL : Disjoint (G.vertexSet P) (G.vertexSet L)) :
    (P ∪ L) \ P = L := by
  have hfamilies : Disjoint P L := by
    apply Set.disjoint_left.2
    intro p hpP hpL
    exact Set.disjoint_left.1 hPL
      ⟨p, hpP, p.initial_mem_support⟩
      ⟨p, hpL, p.initial_mem_support⟩
  ext p
  constructor
  · rintro ⟨hpP | hpL, hpNotP⟩
    · exact False.elim (hpNotP hpP)
    · exact hpL
  · intro hpL
    exact ⟨Or.inr hpL,
      fun hpP ↦ Set.disjoint_left.1 hfamilies hpP hpL⟩

/-- Initial vertices subtract exactly when a subfamily is removed from a
warp. -/
theorem initialSet_diff_of_subfamily
    (G : DWeb V) {J P : Set G.DPath}
    (hJ : G.IsWarp J) (hPJ : P ⊆ J) :
    G.initialSet (J \ P) = G.initialSet J \ G.initialSet P := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨⟨p, hp.1, rfl⟩, ?_⟩
    rintro ⟨q, hqP, hqinitial⟩
    have hpq : p = q :=
      DWeb.IsWarp.eq_of_initial_eq G hJ hp.1 (hPJ hqP) hqinitial.symm
    exact hp.2 (hpq ▸ hqP)
  · rintro ⟨⟨p, hpJ, rfl⟩, hpInitial⟩
    refine ⟨p, ⟨hpJ, ?_⟩, rfl⟩
    intro hpP
    exact hpInitial ⟨p, hpP, rfl⟩

/-- Terminal vertices subtract exactly when a subfamily is removed from a
warp. -/
theorem terminalFrontier_diff_of_subfamily
    (G : DWeb V) {J P : Set G.DPath}
    (hJ : G.IsWarp J) (hPJ : P ⊆ J) :
    G.terminalFrontier (J \ P) =
      G.terminalFrontier J \ G.terminalFrontier P := by
  ext x
  constructor
  · rintro ⟨p, hp, hpx⟩
    refine ⟨⟨p, hp.1, hpx⟩, ?_⟩
    rintro ⟨q, hqP, hqx⟩
    have hpq : p = q := by
      by_contra hpq
      exact Set.disjoint_left.1 (hJ hp.1 (hPJ hqP) hpq)
        (G.terminal_mem_support hpx)
        (G.terminal_mem_support hqx)
    exact hp.2 (hpq ▸ hqP)
  · rintro ⟨⟨p, hpJ, hpx⟩, hpFrontier⟩
    refine ⟨p, ⟨hpJ, ?_⟩, hpx⟩
    intro hpP
    exact hpFrontier ⟨p, hpP, hpx⟩

/-- Subtracting a subwarp with the same old and new endpoint boundary from
a one-point augmentation leaves a one-point augmentation on the
complementary colour.  This is the algebraic core of simultaneous colour
repair: once the designated colour is repaired without changing its exact
initial and terminal frontiers, the fresh source and target necessarily
remain in the residual colour. -/
theorem onePointAugmentation_diff_of_exact_boundary
    (G : DWeb V) {J Jplus P Pplus : Set G.DPath}
    (hJ : G.IsWarp J) (hPJ : P ⊆ J) (hPplusJplus : Pplus ⊆ Jplus)
    (hplus : G.IsOnePointAugmentation J Jplus)
    (hPinitial : G.initialSet Pplus = G.initialSet P)
    (hPterminal : G.terminalFrontier Pplus = G.terminalFrontier P) :
    G.IsOnePointAugmentation (J \ P) (Jplus \ Pplus) := by
  obtain ⟨a, ha, b, hb, hJplus, hJplusFinite, hInitial, hTerminal⟩ := hplus
  have haP : a ∉ G.initialSet P := by
    rintro ⟨p, hpP, hpa⟩
    exact ha.2 ⟨p, hPJ hpP, hpa⟩
  have hbP : b ∉ G.terminalFrontier P := by
    rintro ⟨p, hpP, hpb⟩
    exact hb.2 ⟨p, hPJ hpP, hpb⟩
  refine ⟨a, ⟨ha.1, ?_⟩, b, ⟨hb.1, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro haDiff
    rw [initialSet_diff_of_subfamily G hJ hPJ] at haDiff
    exact ha.2 haDiff.1
  · intro hbDiff
    rw [terminalFrontier_diff_of_subfamily G hJ hPJ] at hbDiff
    exact hb.2 hbDiff.1
  · exact fun p hp q hq hpq ↦ hJplus hp.1 hq.1 hpq
  · exact fun {_p} hp ↦ hJplusFinite hp.1
  · rw [initialSet_diff_of_subfamily G hJplus hPplusJplus,
      initialSet_diff_of_subfamily G hJ hPJ, hInitial, hPinitial]
    exact Set.insert_sdiff_of_notMem _ haP
  · rw [terminalFrontier_diff_of_subfamily G hJplus hPplusJplus,
      terminalFrontier_diff_of_subfamily G hJ hPJ,
      hTerminal, hPterminal]
    exact Set.insert_sdiff_of_notMem _ hbP

/-- Packaged complementary-colour output.  Besides inheriting the exact
one-point boundary, the new complementary family is carrier-disjoint from
the repaired designated subfamily simply because both are subfamilies of
the new warp. -/
theorem complementary_onePointAugmentation_of_exact_boundary
    (G : DWeb V) {J Jplus P Pplus : Set G.DPath}
    (hJ : G.IsWarp J) (hPJ : P ⊆ J) (hPplusJplus : Pplus ⊆ Jplus)
    (hplus : G.IsOnePointAugmentation J Jplus)
    (hPinitial : G.initialSet Pplus = G.initialSet P)
    (hPterminal : G.terminalFrontier Pplus = G.terminalFrontier P) :
    G.IsOnePointAugmentation (J \ P) (Jplus \ Pplus) ∧
      Disjoint (G.vertexSet Pplus) (G.vertexSet (Jplus \ Pplus)) := by
  have hJplus := hplus
  obtain ⟨_a, _ha, _b, _hb, hJplusWarp, _hfinite,
      _hinitial, _hterminal⟩ := hJplus
  exact ⟨onePointAugmentation_diff_of_exact_boundary G hJ hPJ
      hPplusJplus hplus hPinitial hPterminal,
    (vertexSet_diff_disjoint G hJplusWarp hPplusJplus).symm⟩

/-- Delete a retained subfamily from a combined wave and restrict every
complementary member to the deleted web. -/
theorem residualWave_of_combinedWave_subfamily
    (G : DWeb V) {J P : Set G.DPath}
    (hJ : G.IsWave J) (hPJ : P ⊆ J) :
    let R := J \ P
    let havoid : Disjoint (G.vertexSet R) (G.vertexSet P) :=
      vertexSet_diff_disjoint G hJ.1 hPJ
    (G.delete (G.vertexSet P)).IsWave
      (G.restrictDeleteFamily (G.vertexSet P) R havoid) := by
  let R := J \ P
  let X := G.vertexSet P
  have havoid : Disjoint (G.vertexSet R) X :=
    vertexSet_diff_disjoint G hJ.1 hPJ
  have hsplit : P ∪ R = J := by
    ext p
    constructor
    · rintro (hpP | hpR)
      · exact hPJ hpP
      · exact hpR.1
    · intro hpJ
      by_cases hpP : p ∈ P
      · exact Or.inl hpP
      · exact Or.inr ⟨hpJ, hpP⟩
  refine ⟨DWeb.IsWarp.restrictDeleteFamily G
      (fun p hp q hq hpq ↦ hJ.1 hp.1 hq.1 hpq) havoid, ?_, ?_⟩
  · rw [G.initialSet_restrictDeleteFamily]
    intro a ha
    obtain ⟨r, hrR, rfl⟩ := ha
    refine ⟨hJ.2.1 ⟨r, hrR.1, rfl⟩, ?_⟩
    exact Set.disjoint_left.1 havoid
      ⟨r, hrR, r.initial_mem_support⟩
  · intro a ha p hp
    let q : DirectedPath.FinitePath G.graph :=
      p.lift G.delete_adj_imp
    have hq : G.IsTargetPathFrom a q := ⟨hp.1, hp.2.1⟩
    obtain ⟨x, hxq, hxfrontier⟩ := hJ.2.2 ha.1 q hq
    have hqAvoid : Disjoint q.support X := by
      have hpInitial :
          DirectedPath.Path.initial
            (Sum.inl p : (G.delete X).DPath) ∉ X := by
        rw [show DirectedPath.Path.initial
            (Sum.inl p : (G.delete X).DPath) = p.start by rfl,
          hp.1]
        exact ha.2
      have h := G.liftDeletePath_avoids X
        (Sum.inl p : (G.delete X).DPath) hpInitial
      change Disjoint q.support X at h
      exact h
    have hxNotX : x ∉ X :=
      fun hxX ↦ Set.disjoint_left.1 hqAvoid hxq hxX
    rw [← hsplit, G.terminalFrontier_union] at hxfrontier
    rcases hxfrontier with hxP | hxR
    · obtain ⟨r, hrP, hrx⟩ := hxP
      exact False.elim (hxNotX
        ⟨r, hrP, G.terminal_mem_support hrx⟩)
    · refine ⟨x, ?_, ?_⟩
      · simpa only [q,
          DirectedPath.FinitePath.support_lift] using hxq
      · rw [G.terminalFrontier_restrictDeleteFamily]
        exact hxR

/-- Initial-profile form of `residualWave_of_combinedWave_subfamily`.  The
new residual profile is literally the combined initial profile with the
retained subfamily's initials removed. -/
theorem residualWave_of_combinedWave_subfamily_with_initialSet
    (G : DWeb V) {J P : Set G.DPath}
    (hJ : G.IsWave J) (hPJ : P ⊆ J) :
    let R := J \ P
    let havoid : Disjoint (G.vertexSet R) (G.vertexSet P) :=
      vertexSet_diff_disjoint G hJ.1 hPJ
    (G.delete (G.vertexSet P)).IsWave
        (G.restrictDeleteFamily (G.vertexSet P) R havoid) ∧
      (G.delete (G.vertexSet P)).initialSet
        (G.restrictDeleteFamily (G.vertexSet P) R havoid) =
          G.initialSet J \ G.initialSet P := by
  let R := J \ P
  let havoid : Disjoint (G.vertexSet R) (G.vertexSet P) :=
    vertexSet_diff_disjoint G hJ.1 hPJ
  refine ⟨residualWave_of_combinedWave_subfamily G hJ hPJ, ?_⟩
  rw [G.initialSet_restrictDeleteFamily]
  exact initialSet_diff_of_subfamily G hJ.1 hPJ

#print axioms vertexSet_diff_disjoint
#print axioms union_diff_left_eq_right_of_vertexSet_disjoint
#print axioms initialSet_diff_of_subfamily
#print axioms terminalFrontier_diff_of_subfamily
#print axioms onePointAugmentation_diff_of_exact_boundary
#print axioms complementary_onePointAugmentation_of_exact_boundary
#print axioms residualWave_of_combinedWave_subfamily
#print axioms residualWave_of_combinedWave_subfamily_with_initialSet

end SingularCombinedWaveResidualExtraction
end CardinalInduction
end Erdos599
