/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayFiniteCoordinateRunSubpath
import ErdosProblems.Erdos599.HalfwayIndexedBackwardInternalSubtrace

/-!
# Backward provenance for finite coordinate restrictions

The parent compressor's indexed reference owners restrict to every
coordinate interval.  Restricted backward runs embed into parent runs, and
injectivity of the parent-run map preserves the unique-owner clause.
-/

noncomputable section

open Set

namespace Erdos599.Alternating

open DirectedPath

universe u w

variable {V : Type u} {D : Digraph V}

namespace FiniteTrace

/-- Ordered compatibility makes the link map of every finite alternating
trace injective. -/
theorem link_injective_of_compatible (F : FiniteTrace D) :
    Function.Injective F.link := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hcompat := F.compatible i j hlt
    rw [hij] at hcompat
    cases hd : (F.link j).direction with
    | forward =>
        simp only [CompatibleInOrder, hd] at hcompat
        rcases hcompat (F.link j).entry_mem_support
            (F.link j).entry_mem_support with h | h
        · exact (F.link j).entry_ne_exit h.2
        · exact (F.link j).entry_ne_exit h.1
    | backward =>
        simp only [CompatibleInOrder, hd] at hcompat
        rcases hcompat (F.link j).entry_mem_support
            (F.link j).entry_mem_support with h | h
        · exact (F.link j).entry_ne_exit h.2
        · exact (F.link j).entry_ne_exit h.1
  · have hji : F.link j = F.link i := hij.symm
    have hcompat := F.compatible j i hlt
    rw [hji] at hcompat
    cases hd : (F.link i).direction with
    | forward =>
        simp only [CompatibleInOrder, hd] at hcompat
        rcases hcompat (F.link i).entry_mem_support
            (F.link i).entry_mem_support with h | h
        · exact (F.link i).entry_ne_exit h.2
        · exact (F.link i).entry_ne_exit h.1
    | backward =>
        simp only [CompatibleInOrder, hd] at hcompat
        rcases hcompat (F.link i).entry_mem_support
            (F.link i).entry_mem_support with h | h
        · exact (F.link i).entry_ne_exit h.2
        · exact (F.link i).entry_ne_exit h.1

end FiniteTrace

namespace RunCompressor.FiniteInput

variable {Gamma : DWeb V} {Y : Set Gamma.DPath} {I : Type w}

def coordinateIntervalParentNativeRun (S : FiniteInput Gamma.graph)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge)
    (i : Fin ((S.coordinateInterval a b hab hb).runs.length - 1 + 1)) :
    Fin (S.runs.length - 1 + 1) :=
  Fin.cast S.runCount_eq.symm
    (S.coordinateIntervalParentRun a b hab hb
      ((S.coordinateInterval a b hab hb).runIndex i))

@[simp] theorem coordinateIntervalParentNativeRun_val
    (S : FiniteInput Gamma.graph)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge)
    (i : Fin ((S.coordinateInterval a b hab hb).runs.length - 1 + 1)) :
    (S.coordinateIntervalParentNativeRun a b hab hb i).1 =
      (S.coordinateIntervalParentRun a b hab hb
        ((S.coordinateInterval a b hab hb).runIndex i)).1 := rfl

@[simp] theorem runIndex_coordinateIntervalParentNativeRun
    (S : FiniteInput Gamma.graph)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge)
    (i : Fin ((S.coordinateInterval a b hab hb).runs.length - 1 + 1)) :
    S.runIndex (S.coordinateIntervalParentNativeRun a b hab hb i) =
      S.coordinateIntervalParentRun a b hab hb
        ((S.coordinateInterval a b hab hb).runIndex i) := by
  apply Fin.ext
  rfl

noncomputable def coordinateIntervalParentProvenanceIndex
    (S : FiniteInput Gamma.graph)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge)
    (P : (AltPath.finite S.toFiniteRunWalk.toFiniteTrace
      ).IndexedBackwardProvenance Y I)
    (i : Fin ((S.coordinateInterval a b hab hb).runs.length - 1 + 1)) : I :=
  Classical.choose (by
    have hmem := S.toFiniteRunWalk.run_link_mem
      (S.coordinateIntervalParentNativeRun a b hab hb i)
    change (S.toFiniteRunWalk.run
      (S.coordinateIntervalParentNativeRun a b hab hb i)).link ∈
        (AltPath.finite S.toFiniteRunWalk.toFiniteTrace).links at hmem
    rw [P.links_eq_range] at hmem
    exact hmem)

theorem link_coordinateIntervalParentProvenanceIndex
    (S : FiniteInput Gamma.graph)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge)
    (P : (AltPath.finite S.toFiniteRunWalk.toFiniteTrace
      ).IndexedBackwardProvenance Y I)
    (i : Fin ((S.coordinateInterval a b hab hb).runs.length - 1 + 1)) :
    P.link (S.coordinateIntervalParentProvenanceIndex a b hab hb P i) =
      (S.toFiniteRunWalk.run
        (S.coordinateIntervalParentNativeRun a b hab hb i)).link :=
  Classical.choose_spec (by
    have hmem := S.toFiniteRunWalk.run_link_mem
      (S.coordinateIntervalParentNativeRun a b hab hb i)
    change (S.toFiniteRunWalk.run
      (S.coordinateIntervalParentNativeRun a b hab hb i)).link ∈
        (AltPath.finite S.toFiniteRunWalk.toFiniteTrace).links at hmem
    rw [P.links_eq_range] at hmem
    exact hmem)

/-- The exact indexed backward-owner certificate inherited by a restricted
finite compressor. -/
noncomputable def coordinateIntervalIndexedBackwardProvenance
    (S : FiniteInput Gamma.graph)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge)
    (P : (AltPath.finite S.toFiniteRunWalk.toFiniteTrace
      ).IndexedBackwardProvenance Y I) :
    (AltPath.finite
      (S.coordinateInterval a b hab hb).toFiniteRunWalk.toFiniteTrace
      ).IndexedBackwardProvenance Y
        (Fin ((S.coordinateInterval a b hab hb).runs.length - 1 + 1)) where
  link i := ((S.coordinateInterval a b hab hb).toFiniteRunWalk.run i).link
  links_eq_range :=
    (S.coordinateInterval a b hab hb).toFiniteRunWalk.toFiniteTrace_links
  owner i hd :=
    P.owner (S.coordinateIntervalParentProvenanceIndex a b hab hb P i) (by
      rw [S.link_coordinateIntervalParentProvenanceIndex a b hab hb P i]
      have hdir := S.coordinateIntervalParentRun_direction a b hab hb
        ((S.coordinateInterval a b hab hb).runIndex i)
      rw [S.toFiniteRunWalk_run_direction,
        S.runIndex_coordinateIntervalParentNativeRun a b hab hb i, hdir]
      exact ((S.coordinateInterval a b hab hb
        ).toFiniteRunWalk_run_direction i).symm.trans hd)
  owner_mem i hd := P.owner_mem
    (S.coordinateIntervalParentProvenanceIndex a b hab hb P i) (by
      rw [S.link_coordinateIntervalParentProvenanceIndex a b hab hb P i]
      have hdir := S.coordinateIntervalParentRun_direction a b hab hb
        ((S.coordinateInterval a b hab hb).runIndex i)
      rw [S.toFiniteRunWalk_run_direction,
        S.runIndex_coordinateIntervalParentNativeRun a b hab hb i, hdir]
      exact ((S.coordinateInterval a b hab hb
        ).toFiniteRunWalk_run_direction i).symm.trans hd)
  isSubpath i hd := by
    let pi := S.coordinateIntervalParentProvenanceIndex a b hab hb P i
    let hpd : (P.link pi).direction = .backward := by
      dsimp [pi]
      rw [S.link_coordinateIntervalParentProvenanceIndex a b hab hb P i]
      have hdir := S.coordinateIntervalParentRun_direction a b hab hb
        ((S.coordinateInterval a b hab hb).runIndex i)
      rw [S.toFiniteRunWalk_run_direction,
        S.runIndex_coordinateIntervalParentNativeRun a b hab hb i, hdir]
      exact ((S.coordinateInterval a b hab hb
        ).toFiniteRunWalk_run_direction i).symm.trans hd
    change ((S.coordinateInterval a b hab hb).projectedRun
        ((S.coordinateInterval a b hab hb).runIndex i)).link.path.IsSubpathOf
      (P.owner pi hpd)
    have hp0 := P.isSubpath pi hpd
    have hpath : (P.link pi).path =
        (S.toFiniteRunWalk.run
          (S.coordinateIntervalParentNativeRun a b hab hb i)).link.path :=
      congrArg Link.path
        (S.link_coordinateIntervalParentProvenanceIndex a b hab hb P i)
    have hp : (S.toFiniteRunWalk.run
        (S.coordinateIntervalParentNativeRun a b hab hb i)).link.path.IsSubpathOf
        (P.owner pi hpd) := by
      rw [← hpath]
      exact hp0
    change (S.projectedRun
        (S.coordinateIntervalParentRun a b hab hb
          ((S.coordinateInterval a b hab hb).runIndex i))).link.path.IsSubpathOf
      (P.owner pi _) at hp
    have hchild := S.coordinateInterval_projectedRun_isSubpathOf_parent
      a b hab hb ((S.coordinateInterval a b hab hb).runIndex i)
    constructor
    · exact hchild.1.trans hp.1
    · exact hchild.2.trans hp.2
  owner_unique := by
    intro i j hi hj howner
    let pi := S.coordinateIntervalParentProvenanceIndex a b hab hb P i
    let pj := S.coordinateIntervalParentProvenanceIndex a b hab hb P j
    have hpi : (P.link pi).direction = .backward := by
      dsimp [pi]
      rw [S.link_coordinateIntervalParentProvenanceIndex a b hab hb P i]
      have hdir := S.coordinateIntervalParentRun_direction a b hab hb
        ((S.coordinateInterval a b hab hb).runIndex i)
      rw [S.toFiniteRunWalk_run_direction,
        S.runIndex_coordinateIntervalParentNativeRun a b hab hb i, hdir]
      exact ((S.coordinateInterval a b hab hb
        ).toFiniteRunWalk_run_direction i).symm.trans hi
    have hpj : (P.link pj).direction = .backward := by
      dsimp [pj]
      rw [S.link_coordinateIntervalParentProvenanceIndex a b hab hb P j]
      have hdir := S.coordinateIntervalParentRun_direction a b hab hb
        ((S.coordinateInterval a b hab hb).runIndex j)
      rw [S.toFiniteRunWalk_run_direction,
        S.runIndex_coordinateIntervalParentNativeRun a b hab hb j, hdir]
      exact ((S.coordinateInterval a b hab hb
        ).toFiniteRunWalk_run_direction j).symm.trans hj
    have hparentLink : P.link pi = P.link pj :=
      P.owner_unique pi pj hpi hpj howner
    rw [S.link_coordinateIntervalParentProvenanceIndex a b hab hb P i,
      S.link_coordinateIntervalParentProvenanceIndex a b hab hb P j]
        at hparentLink
    have hparentNative :=
      S.toFiniteRunWalk.toFiniteTrace.link_injective_of_compatible hparentLink
    have hparentRun : S.coordinateIntervalParentRun a b hab hb
          ((S.coordinateInterval a b hab hb).runIndex i) =
        S.coordinateIntervalParentRun a b hab hb
          ((S.coordinateInterval a b hab hb).runIndex j) := by
      apply Fin.ext
      change (S.coordinateIntervalParentNativeRun a b hab hb i).1 =
        (S.coordinateIntervalParentNativeRun a b hab hb j).1
      exact congrArg Fin.val hparentNative
    have hiDir : (S.coordinateInterval a b hab hb).runDirection
        ((S.coordinateInterval a b hab hb).runIndex i) = .backward := by
      exact ((S.coordinateInterval a b hab hb).toFiniteRunWalk_run_direction i
        ).symm.trans hi
    have hjDir : (S.coordinateInterval a b hab hb).runDirection
        ((S.coordinateInterval a b hab hb).runIndex j) = .backward := by
      exact ((S.coordinateInterval a b hab hb).toFiniteRunWalk_run_direction j
        ).symm.trans hj
    have hrun := S.coordinateIntervalParentRun_eq_imp_eq_of_direction
      a b hab hb hparentRun (hiDir.trans hjDir.symm)
    have hij : i = j := by
      apply Fin.ext
      have hval := congrArg Fin.val hrun
      simpa only [(S.coordinateInterval a b hab hb).runIndex_val] using hval
    subst j
    rfl

end RunCompressor.FiniteInput
end Erdos599.Alternating

#print axioms Erdos599.Alternating.RunCompressor.FiniteInput.coordinateIntervalIndexedBackwardProvenance
