/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayInfiniteSuffixRunEmbedding
import ErdosProblems.Erdos599.HalfwayIndexedBackwardInternalSubtrace

/-!
# Backward-owner provenance for an actual infinite suffix

Recompressing the raw suffix at coordinate `a` may truncate its first
maximal run, but each shifted backward link is a literal subpath of a unique
original run.  Hence the original indexed reference-owner certificate
restricts to the entire infinite tail.
-/

noncomputable section

namespace Erdos599.Alternating.RunCompressor.InfiniteInput

open Set DirectedPath

universe u w

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {I : Type w}

noncomputable def shiftParentProvenanceIndex
    (S : InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a : Nat)
    (P : (AltPath.infinite
      (S.toInfiniteRunWalk hchange).toInfiniteTrace
      ).IndexedBackwardProvenance Y I)
    (i : Nat) : I :=
  Classical.choose (by
    have hmem := (S.toInfiniteRunWalk hchange).run_link_mem
      (S.shiftParentRun hchange a i)
    change ((S.toInfiniteRunWalk hchange).run
        (S.shiftParentRun hchange a i)).link ∈
      (AltPath.infinite
        (S.toInfiniteRunWalk hchange).toInfiniteTrace).links at hmem
    rw [P.links_eq_range] at hmem
    exact hmem)

theorem link_shiftParentProvenanceIndex
    (S : InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a : Nat)
    (P : (AltPath.infinite
      (S.toInfiniteRunWalk hchange).toInfiniteTrace
      ).IndexedBackwardProvenance Y I)
    (i : Nat) :
    P.link (S.shiftParentProvenanceIndex hchange a P i) =
      ((S.toInfiniteRunWalk hchange).run
        (S.shiftParentRun hchange a i)).link :=
  Classical.choose_spec (by
    have hmem := (S.toInfiniteRunWalk hchange).run_link_mem
      (S.shiftParentRun hchange a i)
    change ((S.toInfiniteRunWalk hchange).run
        (S.shiftParentRun hchange a i)).link ∈
      (AltPath.infinite
        (S.toInfiniteRunWalk hchange).toInfiniteTrace).links at hmem
    rw [P.links_eq_range] at hmem
    exact hmem)

private theorem shift_parent_direction_eq_child
    (S : InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a i : Nat) :
    ((S.toInfiniteRunWalk hchange).run
      (S.shiftParentRun hchange a i)).link.direction =
      (((S.shift a).toInfiniteRunWalk
        (S.shift_changes hchange a)).run i).link.direction := by
  rw [S.toInfiniteRunWalk_run_direction,
    (S.shift a).toInfiniteRunWalk_run_direction]
  exact S.shiftParentRun_direction hchange a i

/-- The exact indexed backward-owner certificate inherited by the shifted
infinite tail. -/
noncomputable def shiftIndexedBackwardProvenance
    (S : InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a : Nat)
    (P : (AltPath.infinite
      (S.toInfiniteRunWalk hchange).toInfiniteTrace
      ).IndexedBackwardProvenance Y I) :
    (AltPath.infinite
      ((S.shift a).toInfiniteRunWalk
        (S.shift_changes hchange a)).toInfiniteTrace
      ).IndexedBackwardProvenance Y Nat where
  link i := (((S.shift a).toInfiniteRunWalk
    (S.shift_changes hchange a)).run i).link
  links_eq_range := ((S.shift a).toInfiniteRunWalk
    (S.shift_changes hchange a)).toInfiniteTrace_links
  owner i hd :=
    P.owner (S.shiftParentProvenanceIndex hchange a P i) (by
      rw [S.link_shiftParentProvenanceIndex hchange a P i]
      exact (S.shift_parent_direction_eq_child hchange a i).trans hd)
  owner_mem i hd :=
    P.owner_mem (S.shiftParentProvenanceIndex hchange a P i) (by
      rw [S.link_shiftParentProvenanceIndex hchange a P i]
      exact (S.shift_parent_direction_eq_child hchange a i).trans hd)
  isSubpath i hd := by
    let pi := S.shiftParentProvenanceIndex hchange a P i
    have hpd : (P.link pi).direction = .backward := by
      dsimp [pi]
      rw [S.link_shiftParentProvenanceIndex hchange a P i]
      exact (S.shift_parent_direction_eq_child hchange a i).trans hd
    have hp0 := P.isSubpath pi hpd
    have hpath : (P.link pi).path =
        ((S.toInfiniteRunWalk hchange).run
          (S.shiftParentRun hchange a i)).link.path :=
      congrArg Link.path (S.link_shiftParentProvenanceIndex hchange a P i)
    have hp : ((S.toInfiniteRunWalk hchange).run
        (S.shiftParentRun hchange a i)).link.path.IsSubpathOf
        (P.owner pi hpd) := by
      rw [← hpath]
      exact hp0
    change ((S.shift a).projectedRun
      (S.shift_changes hchange a) i).link.path.IsSubpathOf (P.owner pi hpd)
    change (S.projectedRun hchange
      (S.shiftParentRun hchange a i)).link.path.IsSubpathOf
        (P.owner pi hpd) at hp
    have hchild := S.shift_projectedRun_isSubpathOf_parent hchange a i
    exact ⟨hchild.1.trans hp.1, hchild.2.trans hp.2⟩
  owner_unique := by
    intro i j hi hj howner
    let pi := S.shiftParentProvenanceIndex hchange a P i
    let pj := S.shiftParentProvenanceIndex hchange a P j
    have hpi : (P.link pi).direction = .backward := by
      dsimp [pi]
      rw [S.link_shiftParentProvenanceIndex hchange a P i]
      exact (S.shift_parent_direction_eq_child hchange a i).trans hi
    have hpj : (P.link pj).direction = .backward := by
      dsimp [pj]
      rw [S.link_shiftParentProvenanceIndex hchange a P j]
      exact (S.shift_parent_direction_eq_child hchange a j).trans hj
    have hparentLink := P.owner_unique pi pj hpi hpj howner
    rw [S.link_shiftParentProvenanceIndex hchange a P i,
      S.link_shiftParentProvenanceIndex hchange a P j] at hparentLink
    have hparent : S.shiftParentRun hchange a i =
        S.shiftParentRun hchange a j :=
      S.projectedRun_link_injective hchange hparentLink
    have hij : i = j := S.shiftParentRun_injective hchange a hparent
    subst j
    rfl

#print axioms shiftIndexedBackwardProvenance

end Erdos599.Alternating.RunCompressor.InfiniteInput
