/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingCutDecoder
import ErdosProblems.Erdos599.GroundingFragmentRelation

/-!
# Uniqueness of surviving ladder fragments

The structure `PopularAuxiliary.Input.Fragment` is not itself canonical: it
retains a concrete finite path or ray representing a component.  Maximality
of a deleted fragment nevertheless determines its parent and support as soon
as it shares one vertex with another deleted fragment.  Moreover, directed
edge containment makes the traversal order of either representation agree
with the traversal order of the common parent.  Consequently the blocking
point is representation-independent.

The final result is the useful geometric form: the support of any surviving
fragment meets `BL` in at most its own blocking point.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingFragmentUniqueness

open DirectedPath

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

abbrev Input (Gamma : DWeb V) (I : Type v) : Type (max u v) :=
  PopularAuxiliary.Input Gamma I

abbrev LV (_L : Input Gamma I) : Type (max u v) :=
  PopularAuxiliary.Input.LambdaVertex V I

/-- Two surviving fragments which share a vertex have the same ladder
parent.  This is the parent-level part of fragment uniqueness. -/
theorem parent_eq_of_common
    {L : Input Gamma I} {P Q : L.Fragment} {x : V}
    (hxP : x ∈ P.path.support) (hxQ : x ∈ Q.path.support) :
    P.parent = Q.parent :=
  Alternating.DWeb.IsWarp.eq_of_mem_support L.ladder.disjoint
    P.parent_mem Q.parent_mem (P.support_subset hxP) (Q.support_subset hxQ)

/-- Two maximal surviving fragments which share a vertex have both the same
parent and the same support.  Equality of the `Fragment` structures is not
claimed, since their concrete path fields are not definitionally canonical. -/
theorem parent_eq_and_support_eq_of_common
    {L : Input Gamma I} {C : Set (LV L)} {P Q : L.Fragment}
    (hP : P ∈ GroundingCut.fragments L C)
    (hQ : Q ∈ GroundingCut.fragments L C) {x : V}
    (hxP : x ∈ P.path.support) (hxQ : x ∈ Q.path.support) :
    P.parent = Q.parent ∧ P.path.support = Q.path.support := by
  have hparent : P.parent = Q.parent := parent_eq_of_common hxP hxQ
  exact ⟨hparent,
    GroundingFragmentRelation.fragment_support_eq_of_parent_eq_of_common
      hP hQ hparent hxP hxQ⟩

/-- Every vertex of a directed finite path or ray occurs weakly after its
initial vertex. -/
private theorem initial_beforeEq_of_mem
    {P : Gamma.DPath} {x : V} (hx : x ∈ P.support) :
    GroundingCut.BeforeEq P P.initial x := by
  cases P with
  | inl p =>
      obtain ⟨n, hn⟩ :=
        (GroundingCut.mem_support_iff_exists_occursAt (.inl p) x).1 hx
      refine ⟨0, n, ?_, hn, Nat.zero_le _⟩
      exact ⟨p.support_length_pos, p.support_getElem_zero⟩
  | inr r =>
      obtain ⟨n, hn⟩ :=
        (GroundingCut.mem_support_iff_exists_occursAt (.inr r) x).1 hx
      exact ⟨0, n, rfl, hn, Nat.zero_le _⟩

/-- The order on a concrete fragment representation is the restriction of
the order on its parent ladder path.  The edge-containment field is essential
here: support containment alone would allow an ambient chord or a reversed
representation. -/
theorem beforeEq_parent
    {L : Input Gamma I} (P : L.Fragment) {x y : V}
    (hxy : GroundingCut.BeforeEq P.path x y) :
    GroundingCut.BeforeEq P.parent x y := by
  have hxPath : x ∈ P.path.support := by
    obtain ⟨m, _n, hmx, _hny, _hmn⟩ := hxy
    exact GroundingCut.occursAt_mem_support hmx
  have hyPath : y ∈ P.path.support := by
    obtain ⟨_m, n, _hmx, hny, _hmn⟩ := hxy
    exact GroundingCut.occursAt_mem_support hny
  have hxParent : x ∈ P.parent.support := P.support_subset hxPath
  have hyParent : y ∈ P.parent.support := P.support_subset hyPath
  by_cases hxeq : x = y
  · subst y
    exact GroundingCut.beforeEq_refl hxParent
  · obtain ⟨q, hqStart, hqFinish, hqEdges⟩ :=
      GroundingCutDecoder.exists_forward_segment_of_before
        (P := P.path) ⟨hxy, hxeq⟩
    have hqParent : q.edgeSet ⊆ P.parent.edgeSet :=
      hqEdges.trans P.edges_subset
    cases hparent : P.parent with
    | inl p =>
        obtain ⟨m, hm⟩ :=
          (GroundingCut.mem_support_iff_exists_occursAt (.inl p) x).1
            (by simpa only [hparent] using hxParent)
        obtain ⟨n, hn⟩ :=
          (GroundingCut.mem_support_iff_exists_occursAt (.inl p) y).1
            (by simpa only [hparent] using hyParent)
        rcases hm with ⟨hmLen, hm⟩
        rcases hn with ⟨hnLen, hn⟩
        refine ⟨m, n, ?_, ?_, ?_⟩
        · simpa only [hparent, GroundingCut.OccursAt] using (⟨hmLen, hm⟩ :
            GroundingCut.OccursAt (.inl p : Gamma.DPath) m x)
        · simpa only [hparent, GroundingCut.OccursAt] using (⟨hnLen, hn⟩ :
            GroundingCut.OccursAt (.inl p : Gamma.DPath) n y)
        · apply DirectedPath.Walk.position_mono_in_finitePath p q.walk
            (by simpa only [hparent, DirectedPath.Path.edgeSet,
              DirectedPath.FinitePath.edgeSet] using hqParent)
            ⟨m, hmLen⟩ ⟨n, hnLen⟩
          · exact hm.trans hqStart.symm
          · exact hn.trans hqFinish.symm
    | inr r =>
        obtain ⟨m, hm⟩ :=
          (GroundingCut.mem_support_iff_exists_occursAt (.inr r) x).1
            (by simpa only [hparent] using hxParent)
        obtain ⟨n, hn⟩ :=
          (GroundingCut.mem_support_iff_exists_occursAt (.inr r) y).1
            (by simpa only [hparent] using hyParent)
        refine ⟨m, n, ?_, ?_, ?_⟩
        · simpa only [hparent] using
            (hm : GroundingCut.OccursAt (.inr r : Gamma.DPath) m x)
        · simpa only [hparent] using
            (hn : GroundingCut.OccursAt (.inr r : Gamma.DPath) n y)
        · apply DirectedPath.Walk.position_mono_in_ray r q.walk
            (by simpa only [hparent, DirectedPath.Path.edgeSet,
              DirectedPath.FinitePath.edgeSet] using hqParent) m n
          · exact hm.trans hqStart.symm
          · exact hn.trans hqFinish.symm

/-- The blocking point is independent of the concrete representation of a
maximal surviving fragment.  This is stronger than the `G0`-only form: no
retention hypothesis is needed once both objects are deleted fragments. -/
theorem blockingPoint_eq_of_common
    {L : Input Gamma I} {C : Set (LV L)} {P Q : L.Fragment}
    (hP : P ∈ GroundingCut.fragments L C)
    (hQ : Q ∈ GroundingCut.fragments L C) {x : V}
    (hxP : x ∈ P.path.support) (hxQ : x ∈ Q.path.support) :
    GroundingCut.blockingPoint L C P =
      GroundingCut.blockingPoint L C Q := by
  obtain ⟨hparent, hsupport⟩ :=
    parent_eq_and_support_eq_of_common hP hQ hxP hxQ
  by_cases hPescape :
      PopularAuxiliary.Input.Fragment.MeetsEscape L C P
  · have hQescape :
        PopularAuxiliary.Input.Fragment.MeetsEscape L C Q := by
      rcases hPescape with ⟨z, hzP, hzEscape⟩
      exact ⟨z, hsupport ▸ hzP, hzEscape⟩
    have hbPQ : GroundingCut.BeforeEq P.parent
        (GroundingCut.blockingPoint L C P)
        (GroundingCut.blockingPoint L C Q) := by
      apply beforeEq_parent P
      exact GroundingCut.blockingPoint_beforeEq_escape L C P hPescape
        (hsupport.symm ▸ GroundingCut.blockingPoint_mem_support L C Q
          (Or.inl hQescape))
        (GroundingCut.blockingPoint_mem_escapeRegion_of_meetsEscape
          L C Q hQescape)
    have hbQP : GroundingCut.BeforeEq P.parent
        (GroundingCut.blockingPoint L C Q)
        (GroundingCut.blockingPoint L C P) := by
      have h := beforeEq_parent Q <|
        GroundingCut.blockingPoint_beforeEq_escape L C Q hQescape
          (hsupport ▸ GroundingCut.blockingPoint_mem_support L C P
            (Or.inl hPescape))
          (GroundingCut.blockingPoint_mem_escapeRegion_of_meetsEscape
            L C P hPescape)
      simpa only [hparent] using h
    exact GroundingCutDecoder.beforeEq_antisymm hbPQ hbQP
  · have hQescape :
        ¬ PopularAuxiliary.Input.Fragment.MeetsEscape L C Q := by
      intro h
      rcases h with ⟨z, hzQ, hzEscape⟩
      exact hPescape ⟨z, hsupport.symm ▸ hzQ, hzEscape⟩
    cases hPpath : P.path with
    | inl p =>
        cases hQpath : Q.path with
        | inl q =>
            have hpFinishQ : p.finish ∈ Q.path.support := by
              rw [← hsupport]
              simpa only [hPpath, DirectedPath.Path.support] using
                p.finish_mem_support
            have hqFinishP : q.finish ∈ P.path.support := by
              rw [hsupport]
              simpa only [hQpath, DirectedPath.Path.support] using
                q.finish_mem_support
            have hpq : GroundingCut.BeforeEq P.parent p.finish q.finish := by
              have h := beforeEq_parent Q <|
                GroundingCut.beforeEq_terminal
                  (P := Q.path) (t := q.finish) (x := p.finish)
                    (by simp [hQpath]) hpFinishQ
              simpa only [hparent] using h
            have hqp : GroundingCut.BeforeEq P.parent q.finish p.finish :=
              beforeEq_parent P <|
                GroundingCut.beforeEq_terminal
                  (P := P.path) (t := p.finish) (x := q.finish)
                    (by simp [hPpath]) hqFinishP
            have hfinish : p.finish = q.finish :=
              GroundingCutDecoder.beforeEq_antisymm hpq hqp
            have hbP : GroundingCut.blockingPoint L C P = p.finish :=
              GroundingCut.blockingPoint_eq_terminal_of_not_meetsEscape
                L C P hPescape (t := p.finish) (by simp [hPpath])
            have hbQ : GroundingCut.blockingPoint L C Q = q.finish :=
              GroundingCut.blockingPoint_eq_terminal_of_not_meetsEscape
                L C Q hQescape (t := q.finish) (by simp [hQpath])
            exact hbP.trans (hfinish.trans hbQ.symm)
        | inr q =>
            exfalso
            have hfiniteP : P.path.support.Finite := by
              simpa only [hPpath, DirectedPath.Path.support] using
                p.support_finite
            have hfinite : Q.path.support.Finite := by
              simpa only [hsupport] using hfiniteP
            exact (Set.infinite_range_of_injective q.injective)
              (by simpa only [hQpath, DirectedPath.Path.support,
                DirectedPath.Ray.support] using hfinite)
    | inr p =>
        cases hQpath : Q.path with
        | inl q =>
            exfalso
            have hfiniteQ : Q.path.support.Finite := by
              simpa only [hQpath, DirectedPath.Path.support] using
                q.support_finite
            have hfinite : P.path.support.Finite := by
              simpa only [hsupport] using hfiniteQ
            exact (Set.infinite_range_of_injective p.injective)
              (by simpa only [hPpath, DirectedPath.Path.support,
                DirectedPath.Ray.support] using hfinite)
        | inr q =>
            have hpInitialQ : p.initial ∈ Q.path.support := by
              rw [← hsupport]
              simpa only [hPpath, DirectedPath.Path.initial,
                DirectedPath.Path.support] using p.initial_mem_support
            have hqInitialP : q.initial ∈ P.path.support := by
              rw [hsupport]
              simpa only [hQpath, DirectedPath.Path.initial,
                DirectedPath.Path.support] using q.initial_mem_support
            have hpq : GroundingCut.BeforeEq P.parent p.initial q.initial :=
              by
                have h := beforeEq_parent P
                  (initial_beforeEq_of_mem hqInitialP)
                simpa only [hPpath, DirectedPath.Path.initial] using h
            have hqp : GroundingCut.BeforeEq P.parent q.initial p.initial := by
              have h := beforeEq_parent Q (initial_beforeEq_of_mem hpInitialQ)
              simpa only [hparent, hQpath, DirectedPath.Path.initial] using h
            have hinitial : p.initial = q.initial :=
              GroundingCutDecoder.beforeEq_antisymm hpq hqp
            simpa only [GroundingCut.blockingPoint, dif_neg hPescape,
              dif_neg hQescape, hPpath, hQpath,
              DirectedPath.Path.terminal?_ray, Option.getD_none,
              DirectedPath.Path.initial] using hinitial

/-- Requested convenience form for retained fragments. -/
theorem blockingPoint_eq_of_common_G0
    {L : Input Gamma I} {C : Set (LV L)} {P Q : L.Fragment}
    (hP : P ∈ GroundingCut.G0 L C)
    (hQ : Q ∈ GroundingCut.G0 L C) {x : V}
    (hxP : x ∈ P.path.support) (hxQ : x ∈ Q.path.support) :
    GroundingCut.blockingPoint L C P =
      GroundingCut.blockingPoint L C Q :=
  blockingPoint_eq_of_common hP.1 hQ.1 hxP hxQ

/-- A surviving fragment can contain no `BL` point other than its own
blocking point.  The fragment itself need not belong to `G0`. -/
theorem support_inter_BL_subset_blockingPoint
    {L : Input Gamma I} {C : Set (LV L)} {P : L.Fragment}
    (hP : P ∈ GroundingCut.fragments L C) :
    P.path.support ∩ GroundingCut.BL L C ⊆
      {GroundingCut.blockingPoint L C P} := by
  intro x hx
  obtain ⟨Q, hQ, hQx⟩ :=
    (GroundingCut.mem_BL_iff).1 hx.2
  have hxQ : x ∈ Q.path.support := by
    rw [← hQx]
    exact GroundingCut.blockingPoint_mem_support L C Q hQ.2
  have hblock := blockingPoint_eq_of_common hP hQ.1 hx.1 hxQ
  exact Set.mem_singleton_iff.mpr (hQx.symm.trans hblock.symm)

/-- In particular, the intersection of a surviving fragment support with
`BL` is subsingleton. -/
theorem support_inter_BL_subsingleton
    {L : Input Gamma I} {C : Set (LV L)} {P : L.Fragment}
    (hP : P ∈ GroundingCut.fragments L C) :
    (P.path.support ∩ GroundingCut.BL L C).Subsingleton := by
  intro x hx y hy
  have hx' := support_inter_BL_subset_blockingPoint hP hx
  have hy' := support_inter_BL_subset_blockingPoint hP hy
  exact Set.mem_singleton_iff.mp hx' |>.trans
    (Set.mem_singleton_iff.mp hy').symm

#print axioms blockingPoint_eq_of_common
#print axioms support_inter_BL_subsingleton

end GroundingFragmentUniqueness
end Erdos599
