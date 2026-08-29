/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeLinkProposition
import ErdosProblems.Erdos599.SafeLinkPropositionFinal
import ErdosProblems.Erdos599.SafeLinkFullGrounding
import ErdosProblems.Erdos599.SafeLinkFullClosure

/-!
# Completion of Proposition 6.3 and the safe-link theorem

This module installs the concrete dependent closing-up construction in the
pointwise Section 6 assembler, and then discharges Theorem 6.1 through the
already factored normalization argument.
-/

noncomputable section

namespace Erdos599

open Set DirectedPath

universe u

namespace SafeLink

variable {V : Type u}

/-- The outer Proposition 6.3 adapter.  Its two premises are precisely the
boundary and tree closure conclusions for the concrete dependent common
wave; all other Section 6 inputs are already unconditional. -/
theorem proposition63_of_dependentClosure
    (hboundary :
      ∀ (G : DWeb V) (hG : G.IsNormalized) {a : V}
        (ha : a ∈ G.source) {T : Set V}
        (hT : Maximal (G.IsTreeSet a) T) (y : V),
        let base := G.delete {a}
        let hNoEnter : base.NoEdgeEnters base.source :=
          delete_root_noEdgeEnters_source G hG a
        let F := fun z ↦ boundaryObstruction G hG hT z
        let K := groundingSet G a T
        let Y := G.outerBoundary T
        let Q := nonBoundedTreeVertices G a T
        let X := base.sectionSixAccumClosure hNoEnter F K Y Q T y
        let M := base.sectionSixAccumCommonWave hNoEnter F K Y Q T y
        ∀ z ∈ Y,
          z ∈ (base.quotient X).vertexSet
            ((base.quotient X).essentialMeetingPaths M.1 X) →
          F z ⊆ X)
    (htree :
      ∀ (G : DWeb V) (hG : G.IsNormalized) {a : V}
        (ha : a ∈ G.source) {T : Set V}
        (hT : Maximal (G.IsTreeSet a) T) (y : V),
        let base := G.delete {a}
        let hNoEnter : base.NoEdgeEnters base.source :=
          delete_root_noEdgeEnters_source G hG a
        let F := fun z ↦ boundaryObstruction G hG hT z
        let K := groundingSet G a T
        let Y := G.outerBoundary T
        let Q := nonBoundedTreeVertices G a T
        let X := base.sectionSixAccumClosure hNoEnter F K Y Q T y
        let M := base.sectionSixAccumCommonWave hNoEnter F K Y Q T y
        (base.quotient X).vertexSet
            ((base.quotient X).essentialMeetingPaths M.1 X) ∩ T ⊆ X) :
    Proposition63 V := by
  intro G hG a T ha hT _hTtarget y hy
  let base := G.delete {a}
  let hNoEnter : base.NoEdgeEnters base.source :=
    delete_root_noEdgeEnters_source G hG a
  let F := fun z ↦ boundaryObstruction G hG hT z
  let K := groundingSet G a T
  let Y := G.outerBoundary T
  let Q := nonBoundedTreeVertices G a T
  let X := base.sectionSixAccumClosure hNoEnter F K Y Q T y
  let M := base.sectionSixAccumCommonWave hNoEnter F K Y Q T y

  apply boundaryWave_of_sectionSixData_unconditional
    G hG ha hT hy X M
  · exact base.sectionSixAccumClosure_countable hNoEnter
      (fun z ↦ boundaryObstruction_finite G hG hT z)
      (fun t ↦ groundingSet_countable G a T t)
  · exact sectionSixAccumClosure_subset_offRoot G hG hT y
  · change F y ⊆ X
    simpa only [base.sectionSixAccumStage_zero_carrier] using
      (base.sectionSixAccumStage_carrier_subset_closure
        hNoEnter F K Y Q T y 0)
  · exact htree G hG ha hT y
  · exact hboundary G hG ha hT y
  · intro t ht
    exact (sectionSixAccumClosure_grounding G hG ha hT y t ht).2

/-- Proposition 6.3 for the source-faithful full quotient closure. -/
theorem proposition63 : Proposition63 V := by
  intro G hG a T ha hT _hTtarget y hy
  let base := G.delete {a}
  let hNoEnter : base.NoEdgeEnters base.source :=
    delete_root_noEdgeEnters_source G hG a
  let F := fun z ↦ boundaryObstruction G hG hT z
  let K := groundingSet G a T
  let Y := G.outerBoundary T
  let Q := nonBoundedTreeVertices G a T
  let X := base.sectionSixFullAccumClosure hNoEnter F K Y Q T y
  let M := base.sectionSixFullAccumCommonWave hNoEnter F K Y Q T y
  apply boundaryWave_of_sectionSixData_unconditional
    G hG ha hT hy X M
  · exact base.sectionSixFullAccumClosure_countable hNoEnter
      (fun z ↦ boundaryObstruction_finite G hG hT z)
      (fun t ↦ groundingSet_countable G a T t)
  · exact G.sectionSixFullAccumClosure_subset_offRoot a hNoEnter
      F K Y Q T y (boundaryObstruction_subset G hG hT)
      (groundingSet_subset_offRoot G a T)
  · change F y ⊆ X
    simpa only [base.sectionSixFullAccumStage_zero_carrier] using
      (base.sectionSixFullAccumStage_carrier_subset_closure
        hNoEnter F K Y Q T y 0)
  · exact base.sectionSixFullAccum_meeting_tree_closed
      hNoEnter F K Y Q T y
  · exact base.sectionSixFullAccum_boundary_closed
      hNoEnter F K Y Q T y
  · intro t ht
    exact (sectionSixFullAccumClosure_grounding G hG ha hT y t ht).2

/-- Aharoni--Berger Theorem 6.1: every source of an unhindered web has a
safe target path. -/
theorem exists_safeTargetPath
    (G : DWeb V) (hG : G.IsUnhindered) {a : V} (ha : a ∈ G.source) :
    G.HasSafeTargetPath a :=
  exists_safeTargetPath_of_boundaryWaves proposition63 G hG ha

/-- The Proposition 6.3 adapter for the full quotient closure.  Keeping the
three closure conclusions explicit isolates the final dependent-closure
argument from the already unconditional pointwise Section 6 assembler. -/
theorem proposition63_of_fullDependentClosure
    (hboundary :
      ∀ (G : DWeb V) (hG : G.IsNormalized) {a : V}
        (ha : a ∈ G.source) {T : Set V}
        (hT : Maximal (G.IsTreeSet a) T) (y : V),
        let base := G.delete {a}
        let hNoEnter : base.NoEdgeEnters base.source :=
          delete_root_noEdgeEnters_source G hG a
        let F := fun z ↦ boundaryObstruction G hG hT z
        let K := groundingSet G a T
        let Y := G.outerBoundary T
        let Q := nonBoundedTreeVertices G a T
        let X := base.sectionSixFullAccumClosure hNoEnter F K Y Q T y
        let M := base.sectionSixFullAccumCommonWave hNoEnter F K Y Q T y
        ∀ z ∈ Y,
          z ∈ (base.quotient X).vertexSet
            ((base.quotient X).essentialMeetingPaths M.1 X) →
          F z ⊆ X)
    (htree :
      ∀ (G : DWeb V) (hG : G.IsNormalized) {a : V}
        (ha : a ∈ G.source) {T : Set V}
        (hT : Maximal (G.IsTreeSet a) T) (y : V),
        let base := G.delete {a}
        let hNoEnter : base.NoEdgeEnters base.source :=
          delete_root_noEdgeEnters_source G hG a
        let F := fun z ↦ boundaryObstruction G hG hT z
        let K := groundingSet G a T
        let Y := G.outerBoundary T
        let Q := nonBoundedTreeVertices G a T
        let X := base.sectionSixFullAccumClosure hNoEnter F K Y Q T y
        let M := base.sectionSixFullAccumCommonWave hNoEnter F K Y Q T y
        (base.quotient X).vertexSet
            ((base.quotient X).essentialMeetingPaths M.1 X) ∩ T ⊆ X)
    (hground :
      ∀ (G : DWeb V) (hG : G.IsNormalized) {a : V}
        (ha : a ∈ G.source) {T : Set V}
        (hT : Maximal (G.IsTreeSet a) T) (y : V),
        let base := G.delete {a}
        let hNoEnter : base.NoEdgeEnters base.source :=
          delete_root_noEdgeEnters_source G hG a
        let F := fun z ↦ boundaryObstruction G hG hT z
        let K := groundingSet G a T
        let Y := G.outerBoundary T
        let Q := nonBoundedTreeVertices G a T
        let X := base.sectionSixFullAccumClosure hNoEnter F K Y Q T y
        let M := base.sectionSixFullAccumCommonWave hNoEnter F K Y Q T y
        X \ Q ⊆ G.strictRoof (G.terminalFrontier
          (liftDeleteQuotientFamily G a X M.1))) :
    Proposition63 V := by
  intro G hG a T ha hT _hTtarget y hy
  let base := G.delete {a}
  let hNoEnter : base.NoEdgeEnters base.source :=
    delete_root_noEdgeEnters_source G hG a
  let F := fun z ↦ boundaryObstruction G hG hT z
  let K := groundingSet G a T
  let Y := G.outerBoundary T
  let Q := nonBoundedTreeVertices G a T
  let X := base.sectionSixFullAccumClosure hNoEnter F K Y Q T y
  let M := base.sectionSixFullAccumCommonWave hNoEnter F K Y Q T y

  apply boundaryWave_of_sectionSixData_unconditional
    G hG ha hT hy X M
  · exact base.sectionSixFullAccumClosure_countable hNoEnter
      (fun z ↦ boundaryObstruction_finite G hG hT z)
      (fun t ↦ groundingSet_countable G a T t)
  · exact G.sectionSixFullAccumClosure_subset_offRoot
      a hNoEnter F K Y Q T y
      (boundaryObstruction_subset G hG hT)
      (groundingSet_subset_offRoot G a T)
  · change F y ⊆ X
    simpa only [base.sectionSixFullAccumStage_zero_carrier] using
      (base.sectionSixFullAccumStage_carrier_subset_closure
        hNoEnter F K Y Q T y 0)
  · exact htree G hG ha hT y
  · exact hboundary G hG ha hT y
  · exact hground G hG ha hT y

end SafeLink

end Erdos599
