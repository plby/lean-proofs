/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeLinkFiniteArrowAncestry
import ErdosProblems.Erdos599.SafeLinkProposition

/-!
# Countable Section 6 ancestry assembly

This module specializes the generic finite-arrow ancestry invariant to the
root-deleted web used in Proposition 6.3.  The remaining construction theorem
is deliberately an argument, so the graph-specific source-disjointness
bookkeeping is independent of the finite-arrow induction.
-/

noncomputable section

namespace Erdos599

open Set DirectedPath

universe u

namespace SafeLink

variable {V : Type u}

/-- A uniform endpoint-free finite-arrow ancestry theorem implies the exact
provenance proposition used by the countable safe-link construction. -/
theorem sectionSixAccumProvenance_of_weakFinalSuffix
    (hWeak : ∀ (G : DWeb V) (hNoEnter : G.NoEdgeEnters G.source)
      (F K : V → Set V) (Y Q T : Set V) (y : V),
      G.HasSectionSixAccumFiniteArrowWeakFinalSuffix
        hNoEnter F K Y Q T y) :
    SectionSixAccumProvenance V := by
  intro G hG a ha T hT y
  let base := G.delete {a}
  let hNoEnter : base.NoEdgeEnters base.source :=
    delete_root_noEdgeEnters_source G hG a
  let F := fun z ↦ boundaryObstruction G hG hT z
  let K := groundingSet G a T
  let Y := G.outerBoundary T
  let Q := nonBoundedTreeVertices G a T
  let X := base.sectionSixAccumClosure hNoEnter F K Y Q T y
  let M := base.sectionSixAccumCommonWave hNoEnter F K Y Q T y
  dsimp only
  have hXT : X ⊆ T \ {a} := by
    exact sectionSixAccumClosure_subset_offRoot G hG hT y
  have hSourceX : Disjoint base.source X :=
    tree_offRoot_disjoint_delete_source G hT.1 hXT
  exact DWeb.HasSectionSixAccumFiniteArrowWeakFinalSuffix.provenance
    base hNoEnter F K Y Q T y
      (hWeak base hNoEnter F K Y Q T y) hSourceX

/-- Uniform weak finite-arrow ancestry is the only missing combinatorial
input to Proposition 6.3. -/
theorem proposition63_of_weakFinalSuffix
    (hWeak : ∀ (G : DWeb V) (hNoEnter : G.NoEdgeEnters G.source)
      (F K : V → Set V) (Y Q T : Set V) (y : V),
      G.HasSectionSixAccumFiniteArrowWeakFinalSuffix
        hNoEnter F K Y Q T y) :
    Proposition63 V :=
  proposition63_of_sectionSixAccumProvenance
    (sectionSixAccumProvenance_of_weakFinalSuffix hWeak)

end SafeLink

end Erdos599
