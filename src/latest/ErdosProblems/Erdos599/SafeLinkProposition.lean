/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.OneHoleUnconditional
import ErdosProblems.Erdos599.SafeLinkClosureFinal
import ErdosProblems.Erdos599.SafeLinkCorollary69

/-!
# Proposition 6.3 and the safe-link theorem

This module assembles the countable closing-up argument in Section 6 of
Aharoni--Berger.  The first lemma records the initial finite-obstruction
step separately, so that the use of their Lemma 3.32 is explicit.
-/

noncomputable section

namespace Erdos599

open Set DirectedPath

universe u

namespace SafeLink

variable {V : Type u}

/-- The exact pointwise statement of Aharoni--Berger Proposition 6.3 used
in the proof of the safe-link theorem. -/
def Proposition63 (V : Type u) : Prop :=
  ∀ (G : DWeb V), G.IsNormalized →
    ∀ {a : V} {T : Set V}, a ∈ G.source →
      Maximal (G.IsTreeSet a) T → Disjoint T G.target →
      ∀ y ∈ G.outerBoundary T,
        ∃ U : Set ((G.delete
            (insert a (nonBoundedTreeVertices G a T))).DPath),
          (G.delete (insert a (nonBoundedTreeVertices G a T))).IsWave U ∧
            y ∈ (G.delete
              (insert a (nonBoundedTreeVertices G a T))).roof
                ((G.delete
                  (insert a (nonBoundedTreeVertices G a T))).terminalFrontier U)

/-- The first stage of the Proposition 6.3 construction.  A finite
obstruction at a boundary vertex produces a maximal quotient wave whose
terminal frontier roofs that vertex in the root-deleted web.

The functional premise is exactly Lemma 3.32.  It is kept abstract in this
local bookkeeping lemma so the proof remains independent of the module in
which Lemma 3.32 is established; the production corollary below instantiates
it with the theorem itself. -/
theorem initialBoundaryRoof_of_waveExtraction
    (waveExtraction :
      ∀ (H : DWeb V) (v : V), H.IsUnhindered → v ∉ H.source →
        (H.delete {v}).IsHindered →
          ∃ U : Set H.DPath, H.IsWave U ∧ v ∈ H.terminalFrontier U)
    (G : DWeb V) (hG : G.IsNormalized) {a : V} (ha : a ∈ G.source)
    {T : Set V} (hT : Maximal (G.IsTreeSet a) T)
    {y : V} (hy : y ∈ G.outerBoundary T) :
    let H := G.delete {a}
    let F := boundaryObstruction G hG hT y
    y ∈ H.roof
      ((H.quotient F).terminalFrontier (maximalQuotientWave H F).1) := by
  let H := G.delete {a}
  let F := boundaryObstruction G hG hT y
  have hFfinite : F.Finite := boundaryObstruction_finite G hG hT y
  have hFT : F ⊆ T \ {a} := boundaryObstruction_subset G hG hT y
  have hHunhindered : (H.delete F).IsUnhindered := by
    have hsafe := hT.1.2.2.2 F hFfinite hFT
    simpa [H, DWeb.SafeAfterRootDeletion, DWeb.SafeDeletion] using hsafe
  have hySource : y ∉ (H.delete F).source := by
    intro hySource
    have hyGSource : y ∈ G.source := hySource.1.1
    exact (outerBoundary_subset_source_compl G hG T hy) hyGSource
  have hyHindered : ((H.delete F).delete {y}).IsHindered := by
    have hunsafe := boundaryObstruction_isUnsafe G hG hT hy
    rw [DWeb.SafeAfterRootDeletion, DWeb.SafeDeletion] at hunsafe
    rw [DWeb.isUnhindered_iff_not_isHindered, not_not] at hunsafe
    have hsets : ({a} : Set V) ∪ (F ∪ {y}) = insert a (insert y F) := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
      tauto
    change (((G.delete {a}).delete F).delete {y}).IsHindered
    rw [DWeb.delete_delete, DWeb.delete_delete, hsets]
    exact hunsafe
  obtain ⟨U, hU, hyU⟩ :=
    waveExtraction (H.delete F) y hHunhindered hySource hyHindered
  have hNoEnter : H.NoEdgeEnters H.source :=
    delete_root_noEdgeEnters_source G hG a
  have hSourceF : Disjoint H.source F :=
    tree_offRoot_disjoint_delete_source G hT.1 hFT
  have hroof := (H.maximalQuotientWave_roofs_deleteWave
    hNoEnter hSourceF hU (maximalQuotientWave H F)
      (maximalQuotientWave_isMax H F)).1
  exact hroof ((H.delete F).subset_roof _ hyU)

/-- Consequently the raw countable commitment set is off the root as well. -/
theorem sectionSixAccumClosure_subset_offRoot
    (G : DWeb V) (hG : G.IsNormalized) {a : V} {T : Set V}
    (hT : Maximal (G.IsTreeSet a) T) (y : V) :
    (G.delete {a}).sectionSixAccumClosure
      (delete_root_noEdgeEnters_source G hG a)
      (fun z ↦ boundaryObstruction G hG hT z)
      (groundingSet G a T) (G.outerBoundary T)
      (nonBoundedTreeVertices G a T) T y ⊆ T \ {a} := by
  intro x hx
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
  exact (G.sectionSixAccumStage_carrier_subset_offRoot a
    (delete_root_noEdgeEnters_source G hG a)
    (fun z ↦ boundaryObstruction G hG hT z)
    (groundingSet G a T) (G.outerBoundary T)
    (nonBoundedTreeVertices G a T) T y
    (boundaryObstruction_subset G hG hT)
    (groundingSet_subset_offRoot G a T) n) hxn

/-- The one provenance statement needed to close the dependent Section 6
construction.  Every vertex on a final essential path which meets the raw
commitment set already occurs on a genuine dependent-stage path meeting that
stage's carrier.  The same witness supplies both clauses (b) and (d) of
Proposition 6.3. -/
def SectionSixAccumProvenance (V : Type u) : Prop :=
  ∀ (G : DWeb V) (hG : G.IsNormalized) {a : V}, a ∈ G.source →
    ∀ {T : Set V} (hT : Maximal (G.IsTreeSet a) T) (y : V),
      let base := G.delete {a}
      let hNoEnter : base.NoEdgeEnters base.source :=
        delete_root_noEdgeEnters_source G hG a
      let F := fun z ↦ boundaryObstruction G hG hT z
      let K := groundingSet G a T
      let Y := G.outerBoundary T
      let Q := nonBoundedTreeVertices G a T
      let X := base.sectionSixAccumClosure hNoEnter F K Y Q T y
      let M := base.sectionSixAccumCommonWave hNoEnter F K Y Q T y
      ∀ z ∈ (base.quotient X).vertexSet
          ((base.quotient X).essentialMeetingPaths M.1 X),
        ∃ n, z ∈ base.meetingVertexSet
          (base.sectionSixAccumStageLift
            (base.sectionSixAccumStage hNoEnter F K Y Q T y n))
          (base.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier

/-- All of Proposition 6.3 after the single dependent-stage provenance
statement.  This theorem contains the complete countable assembly: closure,
grounding, bring-down, essential reduction, Assertion 6.8, Corollary 6.9,
and the final general arrow. -/
theorem proposition63_of_sectionSixAccumProvenance
    (provenance : SectionSixAccumProvenance V) : Proposition63 V := by
  intro G hG a T ha hT hTtarget y hy
  let base := G.delete {a}
  let hNoEnter : base.NoEdgeEnters base.source :=
    delete_root_noEdgeEnters_source G hG a
  let F := fun z ↦ boundaryObstruction G hG hT z
  let K := groundingSet G a T
  let Y := G.outerBoundary T
  let Q := nonBoundedTreeVertices G a T
  let X := base.sectionSixAccumClosure hNoEnter F K Y Q T y
  let M := base.sectionSixAccumCommonWave hNoEnter F K Y Q T y
  let H := base.quotient X

  have hprov : ∀ z ∈ H.vertexSet (H.essentialMeetingPaths M.1 X),
      ∃ n, z ∈ base.meetingVertexSet
        (base.sectionSixAccumStageLift
          (base.sectionSixAccumStage hNoEnter F K Y Q T y n))
        (base.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier := by
    simpa only [base, hNoEnter, F, K, Y, Q, X, M, H] using
      provenance G hG ha hT y

  have hXcount : X.Countable := by
    exact base.sectionSixAccumClosure_countable hNoEnter
      (fun z ↦ boundaryObstruction_finite G hG hT z)
      (fun t ↦ groundingSet_countable G a T t)
  have hXT : X ⊆ T \ {a} := by
    exact sectionSixAccumClosure_subset_offRoot G hG hT y
  have hclosed : H.vertexSet (H.essentialMeetingPaths M.1 X) ∩ T ⊆ X := by
    intro z hz
    obtain ⟨n, hzn⟩ := hprov z hz.1
    exact base.sectionSixAccum_meetingTree_subset_closure
      hNoEnter F K Y Q T y n ⟨hzn, hz.2⟩
  have hground : X \ Q ⊆
      G.strictRoof (G.terminalFrontier
        (liftDeleteQuotientFamily G a X M.1)) := by
    intro t ht
    exact (sectionSixAccumClosure_grounding G hG ha hT y t ht).2

  let : Nonempty V := ⟨a⟩
  obtain ⟨e, henum⟩ := Set.countable_iff_exists_subset_range.mp hXcount
  let R := SafeLinkGroundFinal.DWeb.groundRemoved G a X e
  let ground : (base.delete R).Wave :=
    SafeLinkGroundFinal.DWeb.groundWave G a X e
  have hRX : R ⊆ X := by
    exact SafeLinkGroundFinal.DWeb.groundRemoved_subset G X e
  have hgroundQ : Disjoint ((base.delete R).vertexSet ground.1) Q := by
    exact SafeLinkGroundFinal.DWeb.groundWave_vertexSet_disjoint_nonBounded
      G hG ha hT.1 hXT e

  have h64 := assertion6_4_quotient G hG ha hT.1 hXcount hXT
    M.2 hclosed hground
  obtain ⟨U, W, hU, hWdef, hW, hWfinite, hWinitial,
      _hWancestryOr, hWancestry⟩ :=
    exists_reducedQuotientWave_with_ancestry G hG ha hT.1
      hXcount hXT M.2 hclosed hground
  let Wessential : ((base.delete Q).quotient X).Wave :=
    ⟨((base.delete Q).quotient X).essentialWarpPart W,
      hW.essentialWarpPart⟩
  let groundQ : ((base.delete Q).delete R).Wave :=
    restrictGroundWave base R Q ground hgroundQ

  have hboundaryGround : ∀ z ∈ G.outerBoundary T,
      z ∈ H.vertexSet (H.essentialMeetingPaths M.1 X) →
      z ∈ (base.delete R).roof
        ((base.delete R).terminalFrontier ground.1) := by
    intro z hz hzM
    obtain ⟨n, hzn⟩ := hprov z hzM
    have hFX : F z ⊆ X := by
      exact base.sectionSixAccum_F_subset_closure
        hNoEnter F K Y Q T y n ⟨hz, hzn⟩
    exact boundary_roof_groundWave
      (fun J S hJ hS hSSource ↦ DWeb.isHindered_delete_finite J hJ hS hSSource)
      (fun J v hJ hv hdel ↦
        DWeb.exists_wave_terminalFrontier_of_delete_isHindered J hJ hv hdel)
      G hG hT hXT e henum hz (by simpa only [F] using hFX)
  have hboundaryGroundQ : ∀ z ∈ G.outerBoundary T,
      z ∈ H.vertexSet (H.essentialMeetingPaths M.1 X) →
      z ∈ ((base.delete Q).delete R).roof
        (((base.delete Q).delete R).terminalFrontier groundQ.1) := by
    intro z hz hzM
    exact roof_restrictGroundWave base R Q ground hgroundQ
      (hboundaryGround z hz hzM)

  have hmeet : ∀ p ∈ Wessential.1, ∃ u ∈ p.support, u ∉ R ∧
      u ∈ ((base.delete Q).delete R).roof
        (((base.delete Q).delete R).terminalFrontier groundQ.1) := by
    apply corollary69_of_reducedAncestry G hT.1 hXT hRX
      (M := M.1) (W := Wessential.1) (ground := groundQ)
    · intro p hp
      exact hWinitial ⟨p, hp.1, rfl⟩
    · exact hWancestry
    · exact h64.1
    · exact hboundaryGroundQ

  have hFyX : F y ⊆ X := by
    intro x hx
    apply base.sectionSixAccumStage_carrier_subset_closure
      hNoEnter F K Y Q T y 0
    simpa only [base.sectionSixAccumStage_zero_carrier] using hx
  have hyground : y ∈ (base.delete R).roof
      ((base.delete R).terminalFrontier ground.1) := by
    exact boundary_roof_groundWave
      (fun J S hJ hS hSSource ↦ DWeb.isHindered_delete_finite J hJ hS hSSource)
      (fun J v hJ hv hdel ↦
        DWeb.exists_wave_terminalFrontier_of_delete_isHindered J hJ hv hdel)
      G hG hT hXT e henum hy (by simpa only [F] using hFyX)

  simpa only [Q, base] using
    (finalBoundaryWave_of_ground_and_quotient G hG hT.1 hXT hRX
      ground hgroundQ Wessential hmeet hyground)

/-- The contradiction step of Theorem 6.1, factored through the pointwise
conclusion of Proposition 6.3. -/
theorem exists_safeTargetPath_normalized_of_boundaryWaves
    (boundaryWaves : Proposition63 V)
    (G : DWeb V) (hGnormalized : G.IsNormalized)
    (hG : G.IsUnhindered) {a : V} (ha : a ∈ G.source) :
    G.HasSafeTargetPath a := by
  by_contra hnone
  obtain ⟨T, hTmax, hTtarget⟩ :=
    exists_maximalTreeSet_disjoint_target G hG ha hnone
  have hhindered : G.IsHindered :=
    isHindered_of_individual_boundary_waves G
      (insert_root_nonBounded_subset_tree G hTmax.1) hTtarget ha
      (fun y hy ↦ boundaryWaves G hGnormalized ha hTmax hTtarget y hy)
  exact hG hhindered

/-- Normalization transports the factored safe-link conclusion back to an
arbitrary web. -/
theorem exists_safeTargetPath_of_boundaryWaves
    (boundaryWaves : Proposition63 V)
    (G : DWeb V) (hG : G.IsUnhindered) {a : V} (ha : a ∈ G.source) :
    G.HasSafeTargetPath a := by
  apply DWeb.HasSafeTargetPath.of_normalized
  exact exists_safeTargetPath_normalized_of_boundaryWaves boundaryWaves
    G.normalized G.normalized_isNormalized hG.normalized ha

end SafeLink

end Erdos599
