/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeLinkCorollary69
import ErdosProblems.Erdos599.SafeLinkClosureFinal
import ErdosProblems.Erdos599.OneHoleUnconditional

/-!
# Final assembly of Proposition 6.3

This module connects the four concrete closing-up invariants with the
finite-deletion extraction, the countable ground wave, Corollary 6.9, and
the deletion--quotient arrow.
-/

noncomputable section

namespace Erdos599

open Set DirectedPath

universe u

namespace SafeLink

variable {V : Type u}

/-- The pointwise conclusion of Proposition 6.3 from the four Section 6
closing-up invariants.  The only functional inputs are exactly source
Lemmas 3.31 and 3.32. -/
theorem boundaryWave_of_sectionSixData
    (finiteDeletion : ∀ (H : DWeb V) (S : Set V), H.IsHindered →
      S.Finite → S ⊆ H.sourceᶜ → (H.delete S).IsHindered)
    (waveExtraction : ∀ (H : DWeb V) (v : V), H.IsUnhindered →
      v ∉ H.source → (H.delete {v}).IsHindered →
        ∃ W : Set H.DPath, H.IsWave W ∧ v ∈ H.terminalFrontier W)
    (G : DWeb V) (hG : G.IsNormalized) {a : V} (ha : a ∈ G.source)
    {T : Set V} (hT : Maximal (G.IsTreeSet a) T)
    {y : V} (hy : y ∈ G.outerBoundary T)
    (X : Set V) (M : ((G.delete {a}).quotient X).Wave)
    (hXcount : X.Countable) (hXT : X ⊆ T \ {a})
    (hFyX : boundaryObstruction G hG hT y ⊆ X)
    (hclosed : ((G.delete {a}).quotient X).vertexSet
      (((G.delete {a}).quotient X).essentialMeetingPaths M.1 X) ∩ T ⊆ X)
    (hboundaryClosed : ∀ z ∈ G.outerBoundary T,
      z ∈ ((G.delete {a}).quotient X).vertexSet
        (((G.delete {a}).quotient X).essentialMeetingPaths M.1 X) →
      boundaryObstruction G hG hT z ⊆ X)
    (hground : X \ nonBoundedTreeVertices G a T ⊆
      G.strictRoof (G.terminalFrontier
        (liftDeleteQuotientFamily G a X M.1))) :
    let Q := nonBoundedTreeVertices G a T
    ∃ U : Set ((G.delete (insert a Q)).DPath),
      (G.delete (insert a Q)).IsWave U ∧
        y ∈ (G.delete (insert a Q)).roof
          ((G.delete (insert a Q)).terminalFrontier U) := by
  dsimp only
  let base := G.delete {a}
  let H := base.quotient X
  let Q := nonBoundedTreeVertices G a T
  have h64 := assertion6_4_quotient G hG ha hT.1 hXcount hXT
    M.2 hclosed hground
  obtain ⟨U, Wraw, hU, hWrawDef, hWraw, _hfinite,
      hInitial, _hrawAncestry, hAncestry⟩ :=
    exists_reducedQuotientWave_with_ancestry G hG ha hT.1
      hXcount hXT M.2 hclosed hground
  let Wess : Set ((base.delete Q).quotient X).DPath :=
    ((base.delete Q).quotient X).essentialWarpPart Wraw
  have hWess : ((base.delete Q).quotient X).IsWave Wess := by
    exact hWraw.essentialWarpPart
  have hInitialEss : ∀ p ∈ Wess,
      p.initial ∈ (base.delete Q).source ∪ X := by
    intro p hp
    exact hInitial ⟨p, hp.1, rfl⟩

  letI : Nonempty V := ⟨a⟩
  obtain ⟨e, henum⟩ := Set.countable_iff_exists_subset_range.mp hXcount
  let R := SafeLinkGroundFinal.DWeb.groundRemoved G a X e
  let ground : (base.delete R).Wave :=
    SafeLinkGroundFinal.DWeb.groundWave G a X e
  have hRX : R ⊆ X :=
    SafeLinkGroundFinal.DWeb.groundRemoved_subset G X e
  have hgroundQ : Disjoint ((base.delete R).vertexSet ground.1) Q := by
    exact SafeLinkGroundFinal.DWeb.groundWave_vertexSet_disjoint_nonBounded
      G hG ha hT.1 hXT e
  let groundQ : ((base.delete Q).delete R).Wave :=
    restrictGroundWave base R Q ground hgroundQ

  have hboundaryGround : ∀ z ∈ G.outerBoundary T,
      z ∈ H.vertexSet (H.essentialMeetingPaths M.1 X) →
      z ∈ ((base.delete Q).delete R).roof
        (((base.delete Q).delete R).terminalFrontier groundQ.1) := by
    intro z hz hzM
    apply roof_restrictGroundWave base R Q ground hgroundQ
    exact boundary_roof_groundWave finiteDeletion waveExtraction
      G hG hT hXT e henum hz (hboundaryClosed z hz hzM)

  have hmeet : ∀ p ∈ Wess, ∃ u ∈ p.support, u ∉ R ∧
      u ∈ ((base.delete Q).delete R).roof
        (((base.delete Q).delete R).terminalFrontier groundQ.1) := by
    apply corollary69_of_reducedAncestry G hT.1 hXT hRX
      hInitialEss hAncestry h64.1 groundQ
    exact hboundaryGround

  have hyground : y ∈ (base.delete R).roof
      ((base.delete R).terminalFrontier ground.1) := by
    exact boundary_roof_groundWave finiteDeletion waveExtraction
      G hG hT hXT e henum hy hFyX

  exact finalBoundaryWave_of_ground_and_quotient
    G hG hT.1 hXT hRX ground hgroundQ ⟨Wess, hWess⟩ hmeet hyground

/-- Unconditional form of the pointwise assembler, instantiating source
Lemmas 3.31 and 3.32 by their proved finite-deletion implementations. -/
theorem boundaryWave_of_sectionSixData_unconditional
    (G : DWeb V) (hG : G.IsNormalized) {a : V} (ha : a ∈ G.source)
    {T : Set V} (hT : Maximal (G.IsTreeSet a) T)
    {y : V} (hy : y ∈ G.outerBoundary T)
    (X : Set V) (M : ((G.delete {a}).quotient X).Wave)
    (hXcount : X.Countable) (hXT : X ⊆ T \ {a})
    (hFyX : boundaryObstruction G hG hT y ⊆ X)
    (hclosed : ((G.delete {a}).quotient X).vertexSet
      (((G.delete {a}).quotient X).essentialMeetingPaths M.1 X) ∩ T ⊆ X)
    (hboundaryClosed : ∀ z ∈ G.outerBoundary T,
      z ∈ ((G.delete {a}).quotient X).vertexSet
        (((G.delete {a}).quotient X).essentialMeetingPaths M.1 X) →
      boundaryObstruction G hG hT z ⊆ X)
    (hground : X \ nonBoundedTreeVertices G a T ⊆
      G.strictRoof (G.terminalFrontier
        (liftDeleteQuotientFamily G a X M.1))) :
    let Q := nonBoundedTreeVertices G a T
    ∃ U : Set ((G.delete (insert a Q)).DPath),
      (G.delete (insert a Q)).IsWave U ∧
        y ∈ (G.delete (insert a Q)).roof
          ((G.delete (insert a Q)).terminalFrontier U) := by
  exact boundaryWave_of_sectionSixData
    (fun H S hH hS hSA ↦ H.isHindered_delete_finite hH hS hSA)
    (fun H v hH hvA hdel ↦
      H.exists_wave_terminalFrontier_of_delete_isHindered hH hvA hdel)
    G hG ha hT hy X M hXcount hXT hFyX hclosed
      hboundaryClosed hground

end SafeLink

end Erdos599
