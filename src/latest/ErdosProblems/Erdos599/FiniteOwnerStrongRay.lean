/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Blueprint

/-!
# Finite-row trapping of a ray after its last strong edge

Once every weak edge has a proved common finite-row owner, disjointness of
the row forces an entire weak ray tail into one finite member. This is the
last combinatorial step of the strong-ray argument, separate from the
still-required degeneracy certificate for each actual shortcut.
-/

noncomputable section

open Cardinal Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

theorem edgePredicateIndices_infinite_of_complement_common_finite_owner
    {D : Digraph V}
    (marked : V → V → Prop)
    {W : Set Gamma.DPath} {E : Set (V × V)}
    (hW : Gamma.IsWarp W) (hfinite : Gamma.HasFiniteCharacter W)
    (howner : ∀ {x y}, (x, y) ∈ E →
      ¬marked x y →
      ∃ p ∈ W, x ∈ p.support ∧ y ∈ p.support)
    (r : Ray D) (hr : r.edgeSet ⊆ E) :
    {n : ℕ | marked (r n) (r (n + 1))}.Infinite := by
  by_contra hnot
  have hfin : {n : ℕ | marked (r n) (r (n + 1))}.Finite :=
    Set.not_infinite.mp hnot
  obtain ⟨N, hN⟩ := hfin.bddAbove
  have hweak : ∀ n : ℕ,
      ¬marked (r (N + 1 + n)) (r (N + 1 + (n + 1))) := by
    intro n hn
    have hnStrong : N + 1 + n ∈ {i : ℕ | marked (r i) (r (i + 1))} := by
      simpa only [Set.mem_ofPred_eq, Nat.add_assoc] using hn
    have hle := hN hnStrong
    omega
  have hedge : ∀ n : ℕ,
      (r (N + 1 + n), r (N + 1 + (n + 1))) ∈ E := by
    intro n
    apply hr
    exact ⟨N + 1 + n, by simp only [Nat.add_assoc]⟩
  obtain ⟨p, hpW, hp0, _hp1⟩ := howner (hedge 0) (hweak 0)
  have hall : ∀ n : ℕ, r (N + 1 + n) ∈ p.support := by
    intro n
    induction n with
    | zero => exact hp0
    | succ n ih =>
        obtain ⟨q, hqW, hqn, hqnext⟩ := howner (hedge n) (hweak n)
        have hpq : p = q := DWeb.IsWarp.eq_of_mem_support hW hpW hqW ih hqn
        exact hpq ▸ hqnext
  have hinj : Function.Injective (fun n : ℕ ↦ r (N + 1 + n)) := by
    intro n m hnm
    exact Nat.add_left_cancel (r.injective hnm)
  obtain ⟨pf, rfl⟩ := hfinite hpW
  exact pf.support_finite.not_infinite
    (Set.infinite_of_injective_forall_mem hinj hall)

theorem strongEdgeIndices_infinite_of_nonstrong_common_finite_owner
    {W : Set Gamma.DPath} {E : Set (V × V)}
    (hW : Gamma.IsWarp W) (hfinite : Gamma.HasFiniteCharacter W)
    (howner : ∀ {x y}, (x, y) ∈ E →
      ¬IsStrongImaginaryEdge Gamma Y kappa x y →
      ∃ p ∈ W, x ∈ p.support ∧ y ∈ p.support)
    (r : Ray (imaginaryGraph Gamma Y kappa)) (hr : r.edgeSet ⊆ E) :
    (strongEdgeIndices r).Infinite :=
  edgePredicateIndices_infinite_of_complement_common_finite_owner
    (IsStrongImaginaryEdge Gamma Y kappa) hW hfinite howner r hr

#print axioms edgePredicateIndices_infinite_of_complement_common_finite_owner
#print axioms strongEdgeIndices_infinite_of_nonstrong_common_finite_owner

end Erdos599.Blueprint.LinkageBlueprint
