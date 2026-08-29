/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.MarkedRayFiniteEdgeStability

/-!
# Marks on rays contained in a warp's edge relation

Any such ray is a suffix of one ray owner. This transfers infinitely many
marks without assuming the tested ray is literally a member of the warp.
-/

namespace Erdos599.DWeb

open Set _root_.Erdos599.DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {G : DWeb V} {D : Digraph V}

theorem IsWarp.markedIndices_infinite_of_edgeSet_subset
    {W : Set G.DPath} (hW : G.IsWarp W) {marked : V → V → Prop}
    (hmarked : G.InfinitelyManyMarkedEdges W marked)
    (r : Ray D) (hr : r.edgeSet ⊆ familyEdges W) :
    {n : Nat | marked (r n) (r (n + 1))}.Infinite := by
  have hfirst := hr ⟨0, rfl⟩
  simp only [familyEdges, Set.mem_iUnion] at hfirst
  obtain ⟨p, hpW, hp0⟩ := hfirst
  have hpedge : ∀ n : Nat, (r n, r (n + 1)) ∈ p.edgeSet := by
    intro n
    induction n with
    | zero => exact hp0
    | succ n ih =>
        have hn := hr ⟨n + 1, rfl⟩
        simp only [familyEdges, Set.mem_iUnion] at hn
        obtain ⟨q, hqW, hqn⟩ := hn
        have hqp : q = p := DWeb.IsWarp.eq_of_mem_support hW hqW hpW
          (q.edgeSet_subset_support_prod hqn).1 (p.edgeSet_subset_support_prod ih).2
        exact hqp ▸ hqn
  rcases p with p | s
  · have hall : ∀ n : Nat, r n ∈ p.support :=
      fun n ↦ (p.edgeSet_subset_support_prod (hpedge n)).1
    exact False.elim (p.support_finite.not_infinite
      (Set.infinite_of_injective_forall_mem r.injective hall))
  · obtain ⟨m, hm⟩ := (s.edgeSet_subset_support_prod (hpedge 0)).1
    have hrs : ∀ n : Nat, r n = s (m + n) := by
      intro n
      induction n with
      | zero => simpa using hm.symm
      | succ n ih =>
          obtain ⟨j, hj⟩ := hpedge n
          have hjm : j = m + n :=
            s.injective ((congrArg Prod.fst hj).symm.trans ih)
          simpa [hjm, Nat.add_assoc] using congrArg Prod.snd hj
    have hmark := hmarked s hpW
    have htail : {n : Nat | marked (s (m + n)) (s (m + n + 1))}.Infinite := by
      by_contra hfinite
      have hsubset : {n : Nat | marked (s n) (s (n + 1))} ⊆
          Set.Iio m ∪ (fun n : Nat ↦ m + n) ''
            {n : Nat | marked (s (m + n)) (s (m + n + 1))} := by
        intro n hn
        by_cases hnm : n < m
        · exact Or.inl hnm
        · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hnm)
          exact Or.inr ⟨j, hn, rfl⟩
      exact hmark (((Set.finite_Iio m).union
        ((Set.not_infinite.mp hfinite).image (fun n : Nat ↦ m + n))).subset hsubset)
    apply htail.mono
    intro n hn
    simpa only [hrs, Nat.add_assoc] using hn

#print axioms IsWarp.markedIndices_infinite_of_edgeSet_subset

end Erdos599.DWeb
