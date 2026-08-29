/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LadderSuccessorBridge
import ErdosProblems.Erdos599.QuotientMaximal

/-!
# Collapse of arrows along genuine forward extensions

The concrete arrow operation normally splices a prefix from its left input
onto a suffix chosen from its right input.  When the right input already is a
forward extension of the left input, this splice reconstructs the right-hand
path literally.  Consequently the whole arrow family is the right-hand warp,
and an accumulated omega-arrow over a forward chain has no extra bookkeeping
paths at its finite stages.
-/

namespace Erdos599

open Set DirectedPath

universe u

namespace DirectedPath

variable {V : Type u} {D : Digraph V}

namespace Ray

/-- If a finite path is an initial segment of a ray, the suffix selected at
its final vertex starts at the final index of the finite path. -/
theorem suffixFrom_eq_tail_length_sub_one
    (p : FinitePath D) (r : Ray D) (hpr : p.IsInitialSegmentOf r)
    (hx : p.finish ∈ r.support) :
    r.suffixFrom p.finish hx = r.tail (p.walk.support.length - 1) := by
  unfold suffixFrom
  congr 1
  apply r.injective
  rw [Classical.choose_spec hx]
  have hpos : 0 < p.walk.support.length := p.support_length_pos
  calc
    p.finish = p.walk.support.getLast p.walk.support_ne_nil :=
      p.walk.getLast_support.symm
    _ = p.walk.support[p.walk.support.length - 1] := by
      rw [List.get_length_sub_one (by omega : p.walk.support.length - 1 <
        p.walk.support.length)]
    _ = r (p.walk.support.length - 1) :=
      hpr _ (by omega)

end Ray

namespace Path

/-- Splicing a finite prefix onto a path which genuinely extends that prefix
reconstructs the extending path, for both finite paths and rays. -/
theorem appendAt_eq_of_extends (p : FinitePath D) (q : Path D)
    (hx : p.finish ∈ q.support) (happend : Appendable p q hx)
    (hpq : Extends (.inl p) q) : appendAt p q hx happend = q := by
  rcases q with q | r
  · change Sum.inl (p.appendSuffix q hx _) = Sum.inl q
    apply congrArg Sum.inl
    apply FinitePath.eq_of_start_finish_edgeSet_eq
    · exact hpq.start_eq
    · rfl
    · apply congrArg Walk.edgeSet
      apply Walk.eq_of_support_eq
      obtain ⟨tail, htail⟩ := hpq
      have hsuffix : (q.suffixData p.finish hx).walk.support =
          p.finish :: tail := by
        have hdesired : p.finish :: tail <:+ q.walk.support := by
          refine ⟨p.walk.support.dropLast, ?_⟩
          calc
            p.walk.support.dropLast ++ p.finish :: tail =
                (p.walk.support.dropLast ++ [p.finish]) ++ tail := by simp
            _ = p.walk.support ++ tail := by
              rw [← p.walk.getLast_support, List.dropLast_append_getLast]
            _ = q.walk.support := htail
        have hselected : (q.suffixData p.finish hx).walk.support <:+
            q.walk.support := q.suffixData_support_suffix p.finish hx
        rcases List.suffix_total hselected hdesired with hsd | hds
        · apply List.Nodup.eq_of_head_mem_of_suffix
              (hne := by simp) hsd
          · change p.finish ∈ (q.suffixData p.finish hx).walk.support
            exact (q.suffixData p.finish hx).walk.start_mem_support
          · exact hdesired.nodup q.isPath
        · symm
          apply List.Nodup.eq_of_head_mem_of_suffix
              (hne := (q.suffixData p.finish hx).walk.support_ne_nil) hds
          · rw [(q.suffixData p.finish hx).walk.head_support]
            exact List.mem_cons_self
          · exact hselected.nodup q.isPath
      change (p.walk.append (q.suffixData p.finish hx).walk).support =
        q.walk.support
      rw [Walk.support_append, hsuffix, List.tail_cons]
      exact htail
  · change Sum.inr (p.appendRaySuffix r hx _) = Sum.inr r
    apply congrArg Sum.inr
    apply Ray.eq_of_initial_edgeSet_eq
    · exact (p.initial_appendRaySuffix r hx _).trans hpq.start_eq
    · change (appendAt p (Sum.inr r) hx happend).edgeSet = r.edgeSet
      rw [edgeSet_appendAt]
      apply Set.Subset.antisymm
      · exact Set.union_subset (FinitePath.edgeSet_subset_ray hpq)
          (by
            rw [r.suffixFrom_eq_tail_length_sub_one p hpq hx]
            intro e
            rintro ⟨n, rfl⟩
            exact ⟨p.walk.support.length - 1 + n, by simp [Nat.add_assoc]⟩)
      · rintro e ⟨n, rfl⟩
        by_cases hn : n + 1 < p.walk.support.length
        · apply Or.inl
          apply (p.walk.mem_edgeSet_iff_exists_getElem _).2
          refine ⟨n, hn, ?_⟩
          rw [hpq n (lt_trans (Nat.lt_succ_self n) hn), hpq (n + 1) hn]
        · apply Or.inr
          rw [r.suffixFrom_eq_tail_length_sub_one p hpq hx]
          refine ⟨n - (p.walk.support.length - 1), ?_⟩
          simp only [Ray.tail_apply]
          have hle : p.walk.support.length - 1 ≤ n := by omega
          rw [Nat.add_sub_of_le hle]
          have hle' : p.walk.support.length - 1 ≤ n + 1 :=
            hle.trans (Nat.le_succ n)
          rw [Nat.add_sub_of_le hle']

end Path
end DirectedPath

end Erdos599
