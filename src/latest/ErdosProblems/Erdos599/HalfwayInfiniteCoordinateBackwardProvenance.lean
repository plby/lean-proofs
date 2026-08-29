/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayInfiniteCoordinateRunEmbedding
import ErdosProblems.Erdos599.HalfwayIndexedBackwardInternalSubtrace

/-!
# Backward provenance on a bounded interval of an infinite compressor

The actual infinite compressor's indexed reference owners restrict to every
finite coordinate interval.  Each recompressed child run is sent to its
literal parent infinite run; the injectivity proved for that map preserves
the unique-owner clause.
-/

noncomputable section

namespace Erdos599.Alternating.RunCompressor.InfiniteInput

open Set DirectedPath

universe u w

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {I : Type w}

def coordinateIntervalParentNativeRun (S : InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a b : Nat) (hab : a < b)
    (i : Fin ((S.coordinateInterval a b hab).runs.length - 1 + 1)) : Nat :=
  S.coordinateIntervalParentRun hchange a b hab
    ((S.coordinateInterval a b hab).runIndex i)

noncomputable def coordinateIntervalParentProvenanceIndex
    (S : InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a b : Nat) (hab : a < b)
    (P : (AltPath.infinite
      (S.toInfiniteRunWalk hchange).toInfiniteTrace
      ).IndexedBackwardProvenance Y I)
    (i : Fin ((S.coordinateInterval a b hab).runs.length - 1 + 1)) : I :=
  Classical.choose (by
    have hmem := (S.toInfiniteRunWalk hchange).run_link_mem
      (S.coordinateIntervalParentNativeRun hchange a b hab i)
    change ((S.toInfiniteRunWalk hchange).run
        (S.coordinateIntervalParentNativeRun hchange a b hab i)).link ∈
      (AltPath.infinite
        (S.toInfiniteRunWalk hchange).toInfiniteTrace).links at hmem
    rw [P.links_eq_range] at hmem
    exact hmem)

theorem link_coordinateIntervalParentProvenanceIndex
    (S : InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a b : Nat) (hab : a < b)
    (P : (AltPath.infinite
      (S.toInfiniteRunWalk hchange).toInfiniteTrace
      ).IndexedBackwardProvenance Y I)
    (i : Fin ((S.coordinateInterval a b hab).runs.length - 1 + 1)) :
    P.link (S.coordinateIntervalParentProvenanceIndex
      hchange a b hab P i) =
      ((S.toInfiniteRunWalk hchange).run
        (S.coordinateIntervalParentNativeRun hchange a b hab i)).link :=
  Classical.choose_spec (by
    have hmem := (S.toInfiniteRunWalk hchange).run_link_mem
      (S.coordinateIntervalParentNativeRun hchange a b hab i)
    change ((S.toInfiniteRunWalk hchange).run
        (S.coordinateIntervalParentNativeRun hchange a b hab i)).link ∈
      (AltPath.infinite
        (S.toInfiniteRunWalk hchange).toInfiniteTrace).links at hmem
    rw [P.links_eq_range] at hmem
    exact hmem)

private theorem parent_direction_eq_child
    (S : InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a b : Nat) (hab : a < b)
    (i : Fin ((S.coordinateInterval a b hab).runs.length - 1 + 1)) :
    ((S.toInfiniteRunWalk hchange).run
      (S.coordinateIntervalParentNativeRun hchange a b hab i)).link.direction =
      ((S.coordinateInterval a b hab).toFiniteRunWalk.run i).link.direction := by
  let T := S.coordinateInterval a b hab
  rw [S.toInfiniteRunWalk_run_direction,
    T.toFiniteRunWalk_run_direction]
  exact S.coordinateIntervalParentRun_direction hchange a b hab
    (T.runIndex i)

/-- Indexed backward-owner provenance inherited by a bounded coordinate
interval of the actual infinite compressor. -/
noncomputable def coordinateIntervalIndexedBackwardProvenance
    (S : InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a b : Nat) (hab : a < b)
    (P : (AltPath.infinite
      (S.toInfiniteRunWalk hchange).toInfiniteTrace
      ).IndexedBackwardProvenance Y I) :
    (AltPath.finite
      (S.coordinateInterval a b hab).toFiniteRunWalk.toFiniteTrace
      ).IndexedBackwardProvenance Y
        (Fin ((S.coordinateInterval a b hab).runs.length - 1 + 1)) where
  link i := ((S.coordinateInterval a b hab).toFiniteRunWalk.run i).link
  links_eq_range :=
    (S.coordinateInterval a b hab).toFiniteRunWalk.toFiniteTrace_links
  owner i hd :=
    P.owner (S.coordinateIntervalParentProvenanceIndex
      hchange a b hab P i) (by
        rw [S.link_coordinateIntervalParentProvenanceIndex
          hchange a b hab P i]
        exact (S.parent_direction_eq_child hchange a b hab i).trans hd)
  owner_mem i hd :=
    P.owner_mem (S.coordinateIntervalParentProvenanceIndex
      hchange a b hab P i) (by
        rw [S.link_coordinateIntervalParentProvenanceIndex
          hchange a b hab P i]
        exact (S.parent_direction_eq_child hchange a b hab i).trans hd)
  isSubpath i hd := by
    let pi := S.coordinateIntervalParentProvenanceIndex
      hchange a b hab P i
    have hpd : (P.link pi).direction = .backward := by
      dsimp [pi]
      rw [S.link_coordinateIntervalParentProvenanceIndex
        hchange a b hab P i]
      exact (S.parent_direction_eq_child hchange a b hab i).trans hd
    have hp0 := P.isSubpath pi hpd
    have hpath : (P.link pi).path =
        ((S.toInfiniteRunWalk hchange).run
          (S.coordinateIntervalParentNativeRun hchange a b hab i)).link.path :=
      congrArg Link.path
        (S.link_coordinateIntervalParentProvenanceIndex
          hchange a b hab P i)
    have hp : ((S.toInfiniteRunWalk hchange).run
        (S.coordinateIntervalParentNativeRun hchange a b hab i)).link.path.IsSubpathOf
        (P.owner pi hpd) := by
      rw [← hpath]
      exact hp0
    let T := S.coordinateInterval a b hab
    change (T.projectedRun (T.runIndex i)).link.path.IsSubpathOf
      (P.owner pi hpd)
    change (S.projectedRun hchange
      (S.coordinateIntervalParentRun hchange a b hab (T.runIndex i)
      )).link.path.IsSubpathOf (P.owner pi hpd) at hp
    have hchild := S.coordinateInterval_projectedRun_isSubpathOf_parent
      hchange a b hab (T.runIndex i)
    exact ⟨hchild.1.trans hp.1, hchild.2.trans hp.2⟩
  owner_unique := by
    intro i j hi hj howner
    let pi := S.coordinateIntervalParentProvenanceIndex
      hchange a b hab P i
    let pj := S.coordinateIntervalParentProvenanceIndex
      hchange a b hab P j
    have hpi : (P.link pi).direction = .backward := by
      dsimp [pi]
      rw [S.link_coordinateIntervalParentProvenanceIndex
        hchange a b hab P i]
      exact (S.parent_direction_eq_child hchange a b hab i).trans hi
    have hpj : (P.link pj).direction = .backward := by
      dsimp [pj]
      rw [S.link_coordinateIntervalParentProvenanceIndex
        hchange a b hab P j]
      exact (S.parent_direction_eq_child hchange a b hab j).trans hj
    have hparentLink := P.owner_unique pi pj hpi hpj howner
    rw [S.link_coordinateIntervalParentProvenanceIndex
      hchange a b hab P i,
      S.link_coordinateIntervalParentProvenanceIndex
        hchange a b hab P j] at hparentLink
    have hparent : S.coordinateIntervalParentNativeRun hchange a b hab i =
        S.coordinateIntervalParentNativeRun hchange a b hab j :=
      S.projectedRun_link_injective hchange hparentLink
    have hrun : (S.coordinateInterval a b hab).runIndex i =
        (S.coordinateInterval a b hab).runIndex j :=
      S.coordinateIntervalParentRun_injective hchange a b hab hparent
    have hij : i = j := by
      apply Fin.ext
      simpa only [FiniteInput.runIndex_val] using congrArg Fin.val hrun
    subst j
    rfl

#print axioms coordinateIntervalIndexedBackwardProvenance

end Erdos599.Alternating.RunCompressor.InfiniteInput
