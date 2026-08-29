/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularResidualWaveExchange

/-!
# A one-point rerouting does not preserve the two endpoint colours

The one-point augmentation produced after adjoining a residual wave retains
only the *union* of the two old terminal frontiers.  Its paths need not retain
which part of that union came from the designated target linkage.

This six-vertex example makes the loss precise.  The old warp consists of
`a -> t` (the designated colour) and `r -> s` (the residual-frontier colour).
There is a one-point augmentation

`a -> s`, `r -> t`, `c -> b`.

Thus the old colours have been transposed.  Although the augmentation has all
the required endpoint equations, no subfamily of it is a linkage from `{a}`
to the original target `{t,b}`.  Consequently the output of
`exists_onePointAugmentation_of_residual_hindered` cannot be split merely by
restricting the rerouted family to designated initial vertices.  A genuine
colour-preserving simultaneous exchange is required.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularResidualWaveColorCounterexample

open DirectedPath

inductive Vertex
  | a | r | c | t | s | b
  deriving DecidableEq

open Vertex

def graph : Digraph Vertex where
  Adj x y :=
    (x = a ∧ y = t) ∨ (x = r ∧ y = s) ∨
      (x = a ∧ y = s) ∨ (x = r ∧ y = t) ∨
        (x = c ∧ y = b)

@[simp] theorem graph_adj (x y : Vertex) :
    graph.Adj x y ↔
      (x = a ∧ y = t) ∨ (x = r ∧ y = s) ∨
        (x = a ∧ y = s) ∨ (x = r ∧ y = t) ∨
          (x = c ∧ y = b) :=
  Iff.rfl

private def edgePath (x y : Vertex) (hxy : graph.Adj x y) :
    FinitePath graph where
  start := x
  finish := y
  walk := .cons hxy .nil
  isPath := by
    change [x, y].Nodup
    rw [List.nodup_cons]
    constructor
    · simp only [List.mem_singleton]
      intro h
      subst y
      cases x <;> simp [graph] at hxy
    · simp

def atp : FinitePath graph := edgePath a t (by simp [graph])
def rs : FinitePath graph := edgePath r s (by simp [graph])
def asp : FinitePath graph := edgePath a s (by simp [graph])
def rt : FinitePath graph := edgePath r t (by simp [graph])
def cb : FinitePath graph := edgePath c b (by simp [graph])

@[simp] theorem atp_start : atp.start = a := rfl
@[simp] theorem atp_finish : atp.finish = t := rfl
@[simp] theorem rs_start : rs.start = r := rfl
@[simp] theorem rs_finish : rs.finish = s := rfl
@[simp] theorem asp_start : asp.start = a := rfl
@[simp] theorem asp_finish : asp.finish = s := rfl
@[simp] theorem rt_start : rt.start = r := rfl
@[simp] theorem rt_finish : rt.finish = t := rfl
@[simp] theorem cb_start : cb.start = c := rfl
@[simp] theorem cb_finish : cb.finish = b := rfl

@[simp] theorem atp_support : atp.support = ({a, t} : Set Vertex) := by
  ext x
  change x ∈ [a, t] ↔ _
  simp

@[simp] theorem rs_support : rs.support = ({r, s} : Set Vertex) := by
  ext x
  change x ∈ [r, s] ↔ _
  simp

@[simp] theorem asp_support : asp.support = ({a, s} : Set Vertex) := by
  ext x
  change x ∈ [a, s] ↔ _
  simp

@[simp] theorem rt_support : rt.support = ({r, t} : Set Vertex) := by
  ext x
  change x ∈ [r, t] ↔ _
  simp

@[simp] theorem cb_support : cb.support = ({c, b} : Set Vertex) := by
  ext x
  change x ∈ [c, b] ↔ _
  simp

/-- The original target side does not contain the residual frontier `s`. -/
abbrev base : DWeb Vertex where
  graph := graph
  source := {a, r, c}
  target := {t, b}

/-- The retargeted web used by the residual-wave augmentation. -/
abbrev augmentedWeb : DWeb Vertex := base.retarget (base.target ∪ {s})

def old : Set augmentedWeb.DPath := {(.inl atp : augmentedWeb.DPath), .inl rs}
def plus : Set augmentedWeb.DPath :=
  {(.inl asp : augmentedWeb.DPath), .inl rt, .inl cb}

theorem augmentedWeb_normalized : augmentedWeb.IsNormalized := by
  intro x y hxy
  change graph.Adj x y at hxy
  simp only [graph_adj] at hxy
  rcases hxy with hxy | hxy | hxy | hxy | hxy
  all_goals rcases hxy with ⟨rfl, rfl⟩ <;> simp [base]

private theorem old_isWarp : augmentedWeb.IsWarp old := by
  intro p hp q hq hpq
  simp only [old, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact (hpq rfl).elim
  · change Disjoint atp.support rs.support
    rw [atp_support, rs_support]
    exact Set.disjoint_left.2 (by intro x hx hy; cases x <;> simp_all)
  · change Disjoint rs.support atp.support
    rw [rs_support, atp_support]
    exact Set.disjoint_left.2 (by intro x hx hy; cases x <;> simp_all)
  · exact (hpq rfl).elim

private theorem old_finiteCharacter : augmentedWeb.HasFiniteCharacter old := by
  intro p hp
  simp only [old, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact ⟨atp, rfl⟩
  · exact ⟨rs, rfl⟩

@[simp] theorem old_initialSet :
    augmentedWeb.initialSet old = ({a, r} : Set Vertex) := by
  ext x
  constructor
  · rintro ⟨p, hp, hpx⟩
    simp only [old, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · left
      exact hpx.symm
    · right
      exact hpx.symm
  · intro hx
    rcases hx with rfl | hx
    · exact ⟨.inl atp, Or.inl rfl, rfl⟩
    · have hxr : x = r := by simpa using hx
      subst x
      exact ⟨.inl rs, Or.inr rfl, rfl⟩

@[simp] theorem old_terminalFrontier :
    augmentedWeb.terminalFrontier old = ({t, s} : Set Vertex) := by
  ext x
  constructor
  · rintro ⟨p, hp, hpx⟩
    simp only [old, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · left
      exact (Option.some.inj hpx).symm
    · right
      exact (Option.some.inj hpx).symm
  · intro hx
    rcases hx with rfl | hx
    · exact ⟨.inl atp, Or.inl rfl, rfl⟩
    · have hxs : x = s := by simpa using hx
      subst x
      exact ⟨.inl rs, Or.inr rfl, rfl⟩

@[simp] theorem old_vertexSet :
    augmentedWeb.vertexSet old = ({a, t, r, s} : Set Vertex) := by
  ext x
  constructor
  · rintro ⟨p, hp, hxp⟩
    simp only [old, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · change x ∈ atp.support at hxp
      rw [atp_support] at hxp
      rcases hxp with hxa | hxt
      · exact Or.inl hxa
      · exact Or.inr (Or.inl hxt)
    · change x ∈ rs.support at hxp
      rw [rs_support] at hxp
      rcases hxp with hxr | hxs
      · exact Or.inr (Or.inr (Or.inl hxr))
      · exact Or.inr (Or.inr (Or.inr hxs))
  · intro hx
    rcases hx with hxa | hxt | hxr | hxs
    · subst x
      exact ⟨.inl atp, Or.inl rfl, atp.start_mem_support⟩
    · subst x
      exact ⟨.inl atp, Or.inl rfl, atp.finish_mem_support⟩
    · subst x
      exact ⟨.inl rs, Or.inr rfl, rs.start_mem_support⟩
    · subst x
      exact ⟨.inl rs, Or.inr rfl, rs.finish_mem_support⟩

private theorem plus_isWarp : augmentedWeb.IsWarp plus := by
  intro p hp q hq hpq
  simp only [plus, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
  · exact (hpq rfl).elim
  · change Disjoint asp.support rt.support
    rw [asp_support, rt_support]
    exact Set.disjoint_left.2 (by intro x hx hy; cases x <;> simp_all)
  · change Disjoint asp.support cb.support
    rw [asp_support, cb_support]
    exact Set.disjoint_left.2 (by intro x hx hy; cases x <;> simp_all)
  · change Disjoint rt.support asp.support
    rw [rt_support, asp_support]
    exact Set.disjoint_left.2 (by intro x hx hy; cases x <;> simp_all)
  · exact (hpq rfl).elim
  · change Disjoint rt.support cb.support
    rw [rt_support, cb_support]
    exact Set.disjoint_left.2 (by intro x hx hy; cases x <;> simp_all)
  · change Disjoint cb.support asp.support
    rw [cb_support, asp_support]
    exact Set.disjoint_left.2 (by intro x hx hy; cases x <;> simp_all)
  · change Disjoint cb.support rt.support
    rw [cb_support, rt_support]
    exact Set.disjoint_left.2 (by intro x hx hy; cases x <;> simp_all)
  · exact (hpq rfl).elim

private theorem plus_finiteCharacter : augmentedWeb.HasFiniteCharacter plus := by
  intro p hp
  simp only [plus, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨asp, rfl⟩
  · exact ⟨rt, rfl⟩
  · exact ⟨cb, rfl⟩

@[simp] theorem plus_initialSet :
    augmentedWeb.initialSet plus = ({a, r, c} : Set Vertex) := by
  ext x
  constructor
  · rintro ⟨p, hp, hpx⟩
    simp only [plus, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact Or.inl hpx.symm
    · exact Or.inr (Or.inl hpx.symm)
    · exact Or.inr (Or.inr hpx.symm)
  · intro hx
    rcases hx with rfl | rfl | hx
    · exact ⟨.inl asp, Or.inl rfl, rfl⟩
    · exact ⟨.inl rt, Or.inr (Or.inl rfl), rfl⟩
    · have hxc : x = c := by simpa using hx
      subst x
      exact ⟨.inl cb, Or.inr (Or.inr rfl), rfl⟩

@[simp] theorem plus_terminalFrontier :
    augmentedWeb.terminalFrontier plus = ({s, t, b} : Set Vertex) := by
  ext x
  constructor
  · rintro ⟨p, hp, hpx⟩
    simp only [plus, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact Or.inl (Option.some.inj hpx).symm
    · exact Or.inr (Or.inl (Option.some.inj hpx).symm)
    · exact Or.inr (Or.inr (Option.some.inj hpx).symm)
  · intro hx
    rcases hx with rfl | rfl | hx
    · exact ⟨.inl asp, Or.inl rfl, rfl⟩
    · exact ⟨.inl rt, Or.inr (Or.inl rfl), rfl⟩
    · have hxb : x = b := by simpa using hx
      subst x
      exact ⟨.inl cb, Or.inr (Or.inr rfl), rfl⟩

/-- The crossed family has exactly the one-point-augmentation endpoint
equations: the new initial is `c` and the new retargeted terminal is `b`. -/
theorem plus_isOnePointAugmentation :
    augmentedWeb.IsOnePointAugmentation old plus := by
  refine ⟨c, ?_, b, ?_, plus_isWarp, plus_finiteCharacter, ?_, ?_⟩
  · rw [old_initialSet]
    simp [base]
  · rw [old_terminalFrontier]
    simp [base]
  · rw [plus_initialSet, old_initialSet]
    ext x
    cases x <;> simp
  · rw [plus_terminalFrontier, old_terminalFrontier]
    ext x
    cases x <;> simp

private theorem plus_member_starting_a_eq_as
    {p : augmentedWeb.DPath} (hp : p ∈ plus) (hpa : p.initial = a) :
    p = .inl asp := by
  simp only [plus, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · rfl
  · change r = a at hpa
    nomatch hpa
  · change c = a at hpa
    nomatch hpa

/-- No subfamily of the globally rerouted augmentation has the designated
colour: its unique member starting at `a` ends at the residual frontier
`s`, not at the original target `{t,b}`. -/
theorem no_designated_target_subfamily :
    ¬ ∃ Q : Set augmentedWeb.DPath,
      Q ⊆ plus ∧
        IsLinkageBetween augmentedWeb ({a} : Set Vertex) base.target Q := by
  rintro ⟨Q, hQplus, hQ⟩
  have haInit : a ∈ augmentedWeb.initialSet Q := by
    rw [hQ.initialSet_eq]
    simp
  obtain ⟨p, hpQ, hpa⟩ := haInit
  have hpAs : p = .inl asp :=
    plus_member_starting_a_eq_as (hQplus hpQ) hpa
  have hsFrontier : s ∈ augmentedWeb.terminalFrontier Q := by
    refine ⟨p, hpQ, ?_⟩
    rw [hpAs]
    rfl
  have hsTarget : s ∈ base.target := hQ.terminalFrontier_subset hsFrontier
  simp [base] at hsTarget

/-- Exact failure of restriction-by-initial-colour, packaged with all the
structural facts available from the one-point producer. -/
theorem onePointAugmentation_does_not_split_by_old_colour :
    augmentedWeb.IsNormalized ∧
      augmentedWeb.IsCleanFiniteWarp old ∧
      augmentedWeb.IsOnePointAugmentation old plus ∧
      ¬ ∃ Q : Set augmentedWeb.DPath,
        Q ⊆ plus ∧
          IsLinkageBetween augmentedWeb ({a} : Set Vertex) base.target Q := by
  refine ⟨augmentedWeb_normalized, ?_, plus_isOnePointAugmentation,
    no_designated_target_subfamily⟩
  refine ⟨old_isWarp, old_finiteCharacter, ?_, ?_⟩
  · rw [old_vertexSet, old_initialSet]
    ext x
    cases x <;> simp [base]
  · rw [old_vertexSet, old_terminalFrontier]
    ext x
    cases x <;> simp [base]

#print axioms onePointAugmentation_does_not_split_by_old_colour

end SingularResidualWaveColorCounterexample
end CardinalInduction
end Erdos599
