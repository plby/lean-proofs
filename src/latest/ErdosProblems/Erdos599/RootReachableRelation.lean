/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GenericSimultaneousSwitchRank

/-!
# Restricting a relation to its root-reachable components

In a relation with unique predecessors, finite reachability from genuine
roots has a unique length.  This length supplies a natural-number rank for
the reachable subrelation, without a global acyclicity or reverse-ray
assumption on the original relation.
-/

noncomputable section

open Set

namespace Erdos599.RootReachableRelation

universe u

variable {V : Type u} (E : Set (V × V)) (R : Set V)

/-- Exact finite distance from a chosen set of roots. -/
def AtLevel : Nat → V → Prop
  | 0, x => x ∈ R
  | n + 1, y => ∃ x, AtLevel n x ∧ (x, y) ∈ E

/-- Vertices at some finite distance from a chosen root. -/
def carrier : Set V := {x | ∃ n, AtLevel E R n x}

/-- Keep exactly edges leaving reachable vertices. -/
def edges : Set (V × V) := {e | e ∈ E ∧ e.1 ∈ carrier E R}

theorem roots_subset_carrier : R ⊆ carrier E R :=
  fun _ hx => ⟨0, hx⟩

theorem successor_mem_carrier {x y : V}
    (hx : x ∈ carrier E R) (hxy : (x, y) ∈ E) :
    y ∈ carrier E R := by
  obtain ⟨n, hn⟩ := hx
  exact ⟨n + 1, x, hn, hxy⟩

theorem endpoints_mem {e : V × V} (he : e ∈ edges E R) :
    e.1 ∈ carrier E R ∧ e.2 ∈ carrier E R :=
  ⟨he.2, successor_mem_carrier E R he.2 he.1⟩

theorem edges_subset : edges E R ⊆ E := fun _ he => he.1

theorem carrier_subset {C : Set V} (hR : R ⊆ C)
    (hE : ∀ e ∈ E, e.1 ∈ C ∧ e.2 ∈ C) : carrier E R ⊆ C := by
  rintro x ⟨n, hn⟩
  cases n with
  | zero => exact hR hn
  | succ n =>
      obtain ⟨y, _hy, hyx⟩ := hn
      exact (hE (y, x) hyx).2

theorem biUnique (hE : Relator.BiUnique fun x y ↦ (x, y) ∈ E) :
    Relator.BiUnique fun x y ↦ (x, y) ∈ edges E R := by
  exact ⟨fun _ _ _ h₁ h₂ => hE.1 h₁.1 h₂.1,
    fun _ _ _ h₁ h₂ => hE.2 h₁.1 h₂.1⟩

theorem level_unique
    (hin : Relator.LeftUnique fun x y ↦ (x, y) ∈ E)
    (hroots : ∀ x ∈ R, ¬ ∃ y, (y, x) ∈ E)
    {n m : Nat} {x : V}
    (hn : AtLevel E R n x) (hm : AtLevel E R m x) : n = m := by
  induction n generalizing m x with
  | zero =>
      cases m with
      | zero => rfl
      | succ m =>
          obtain ⟨y, _hy, hyx⟩ := hm
          exact False.elim (hroots x hn ⟨y, hyx⟩)
  | succ n ih =>
      obtain ⟨y, hy, hyx⟩ := hn
      cases m with
      | zero => exact False.elim (hroots x hm ⟨y, hyx⟩)
      | succ m =>
          obtain ⟨z, hz, hzx⟩ := hm
          have hyz : y = z := hin hyx hzx
          subst z
          exact congrArg Nat.succ (ih hy hz)

/-- The unique finite level, extended by zero outside the reachable carrier. -/
def rank (x : V) : Nat := by
  classical
  exact if h : x ∈ carrier E R then Nat.find h else 0

theorem rank_eq_of_level
    (hin : Relator.LeftUnique fun x y ↦ (x, y) ∈ E)
    (hroots : ∀ x ∈ R, ¬ ∃ y, (y, x) ∈ E)
    {n : Nat} {x : V} (hn : AtLevel E R n x) :
    rank E R x = n := by
  classical
  have hx : x ∈ carrier E R := ⟨n, hn⟩
  rw [rank, dif_pos hx]
  exact level_unique E R hin hroots (Nat.find_spec hx) hn

theorem rank_step
    (hin : Relator.LeftUnique fun x y ↦ (x, y) ∈ E)
    (hroots : ∀ x ∈ R, ¬ ∃ y, (y, x) ∈ E)
    {x y : V} (hxy : (x, y) ∈ edges E R) :
    rank E R x < rank E R y := by
  obtain ⟨n, hn⟩ := hxy.2
  have hy : AtLevel E R (n + 1) y := ⟨x, hn, hxy.1⟩
  rw [rank_eq_of_level E R hin hroots hn,
    rank_eq_of_level E R hin hroots hy]
  exact Nat.lt_succ_self n

theorem no_directed_cycle
    (hin : Relator.LeftUnique fun x y ↦ (x, y) ∈ E)
    (hroots : ∀ x ∈ R, ¬ ∃ y, (y, x) ∈ E) :
    ¬ Alternating.ContainsDirectedCycle (edges E R) :=
  Alternating.GenericSimultaneousSwitch.not_containsDirectedCycle_of_wellFoundedRank
    (edges E R) (rank E R) (rank_step E R hin hroots)

theorem no_reverse_ray
    (hin : Relator.LeftUnique fun x y ↦ (x, y) ∈ E)
    (hroots : ∀ x ∈ R, ¬ ∃ y, (y, x) ∈ E) :
    ¬ Alternating.ContainsReverseDirectedRay (edges E R) :=
  Alternating.GenericSimultaneousSwitch.not_containsReverseDirectedRay_of_wellFoundedRank
    (edges E R) (rank E R) (rank_step E R hin hroots)

/-- Restriction removes no outgoing edge at a reachable vertex. -/
theorem hasOutgoing_iff {x : V} (hx : x ∈ carrier E R) :
    (∃ y, (x, y) ∈ edges E R) ↔ ∃ y, (x, y) ∈ E :=
  ⟨fun ⟨y, hy⟩ => ⟨y, hy.1⟩, fun ⟨y, hy⟩ => ⟨y, hy, hx⟩⟩

theorem root_iff
    (hroots : ∀ x ∈ R, ¬ ∃ y, (y, x) ∈ E) {x : V} :
    (x ∈ carrier E R ∧ ¬ ∃ y, (y, x) ∈ edges E R) ↔ x ∈ R := by
  constructor
  · rintro ⟨⟨n, hn⟩, hno⟩
    cases n with
    | zero => exact hn
    | succ n =>
        obtain ⟨y, hy, hyx⟩ := hn
        exact False.elim (hno ⟨y, hyx, n, hy⟩)
  · intro hx
    refine ⟨roots_subset_carrier E R hx, ?_⟩
    rintro ⟨y, hyx⟩
    exact hroots x hx ⟨y, hyx.1⟩

theorem carrier_of_reflTransGen {a x : V} (ha : a ∈ R)
    (hax : Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) a x) :
    x ∈ carrier E R := by
  induction hax with
  | refl => exact roots_subset_carrier E R ha
  | tail _h hxy ih => exact successor_mem_carrier E R ih hxy

theorem carrier_of_reflTransGen_of_mem {a x : V} (ha : a ∈ carrier E R)
    (hax : Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) a x) :
    x ∈ carrier E R := by
  induction hax with
  | refl => exact ha
  | tail _h hxy ih => exact successor_mem_carrier E R ih hxy

#print axioms no_directed_cycle
#print axioms no_reverse_ray
#print axioms root_iff

end Erdos599.RootReachableRelation
