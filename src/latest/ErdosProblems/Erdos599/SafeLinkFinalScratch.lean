/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeLink

/-!
# Final assembly of the safe-link theorem (scratch interface)

This file isolates the one genuinely deep input still needed from the
Section 6 closing-up construction.  The input says that every vertex on the
outer boundary of the maximal rooted tree is roofed by a wave in one fixed
deleted web.  The already proved maximal-wave absorption and boundary
promotion lemmas then give Theorem 6.1.

The declaration is intentionally kept in a scratch namespace.  Once the
pointwise boundary-wave theorem has been proved in `SafeLink.lean`, its exact
statement can replace `IndividualBoundaryWavePrinciple` below.
-/

noncomputable section

namespace Erdos599.SafeLinkFinalScratch

open Set
open Erdos599.DirectedPath

universe u

open Erdos599.SafeLink

/-- The precise pointwise output required from Proposition 6.3.

For a maximal rooted tree `T`, delete the root together with all non-bounded
tree vertices.  Every outer-boundary vertex must be roofed by some wave in
that *same* deleted web.  This common ambient web is what permits the waves
to be combined by `exists_wave_roofing`.
-/
def IndividualBoundaryWavePrinciple (V : Type u) : Prop :=
  ∀ (G : DWeb V), G.IsNormalized →
    ∀ {a : V} {T : Set V}, a ∈ G.source →
      Maximal (G.IsTreeSet a) T → Disjoint T G.target →
      ∀ y, y ∈ Walk.outBoundary G.graph T →
        ∃ U : (G.delete
            (insert a (nonBoundedTreeVertices G a T))).Wave,
          y ∈ (G.delete
              (insert a (nonBoundedTreeVertices G a T))).roof
            ((G.delete
              (insert a (nonBoundedTreeVertices G a T))).terminalFrontier U.1)

/-- A normalized unhindered web has a safely deletable path from each
source, assuming the pointwise boundary-wave conclusion of Proposition 6.3.
-/
theorem exists_safeTargetPath_of_individualBoundaryWave_normalized
    (hboundaryWave : IndividualBoundaryWavePrinciple V)
    (G : DWeb V) (hGnormalized : G.IsNormalized)
    (hG : G.IsUnhindered) {a : V} (ha : a ∈ G.source) :
    G.HasSafeTargetPath a := by
  by_contra hnone
  obtain ⟨T, hTmax, hTtarget⟩ :=
    exists_maximalTreeSet_disjoint_target G hG ha hnone
  let Q : Set V := nonBoundedTreeVertices G a T
  let D : Set V := insert a Q
  have hDT : D ⊆ T := by
    intro x hx
    rcases hx with hxa | hxQ
    · exact hxa ▸ hTmax.1.1
    · exact hxQ.1
  have hcover : ∀ y, y ∈ Walk.outBoundary G.graph T →
      ∃ U : (G.delete D).Wave,
        y ∈ (G.delete D).roof ((G.delete D).terminalFrontier U.1) := by
    intro y hy
    simpa only [D, Q] using
      hboundaryWave G hGnormalized ha hTmax hTtarget y hy
  obtain ⟨M, hMroof⟩ := exists_wave_roofing (G.delete D) hcover
  have hMhindrance : G.IsHindrance (G.liftDeleteFamily D M.1) :=
    hindrance_of_tree_boundary_wave G hDT hTtarget M.2 hMroof ha
      (Set.mem_insert a Q)
  exact hG ⟨G.liftDeleteFamily D M.1, hMhindrance⟩

/-- The unrestricted safe-link theorem follows by normalizing the web and
lifting the resulting safe path back to the original graph.
-/
theorem exists_safeTargetPath_of_individualBoundaryWave
    (hboundaryWave : IndividualBoundaryWavePrinciple V)
    (G : DWeb V) (hG : G.IsUnhindered) {a : V} (ha : a ∈ G.source) :
    G.HasSafeTargetPath a := by
  apply DWeb.HasSafeTargetPath.of_normalized
  exact exists_safeTargetPath_of_individualBoundaryWave_normalized
    hboundaryWave G.normalized G.normalized_isNormalized hG.normalized ha

end Erdos599.SafeLinkFinalScratch
