/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingCut
import ErdosProblems.Erdos599.AlternatingTraceOps

/-!
# The terminal fragment of a finite ladder parent

A deleted-edge fragment records both support and edge containment in its
ladder parent.  If a maximal surviving component of a finite parent contains
the parent's terminal, then the fragment is finite and has exactly that
terminal.  Support containment rules out a ray; edge containment rules out
continuing past the parent terminal.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingTerminalFragment

open DirectedPath

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

abbrev Input (Gamma : DWeb V) (I : Type v) : Type (max u v) :=
  PopularAuxiliary.Input Gamma I

abbrev LV (_L : Input Gamma I) : Type (max u v) :=
  PopularAuxiliary.Input.LambdaVertex V I

/-- A path contained in the support of a finite parent cannot be a ray. -/
private theorem isFinite_of_parent_eq_finite
    {L : Input Gamma I} (P : L.Fragment)
    (p : FinitePath Gamma.graph)
    (hparent : P.parent = (.inl p : Gamma.DPath)) :
    P.path.IsFinite := by
  cases hpath : P.path with
  | inl q =>
      exact ⟨q.finish, rfl⟩
  | inr r =>
      exfalso
      have hrsub : r.support ⊆ p.support := by
        simpa only [hpath, hparent, Path.support] using P.support_subset
      have hrfinite : r.support.Finite := p.support_finite.subset hrsub
      exact (Set.infinite_range_of_injective r.injective) hrfinite

/-- If a fragment path contains its finite parent's terminal, edge
containment forces that vertex to be the fragment terminal as well. -/
private theorem terminal_eq_parent_finish_of_mem
    {L : Input Gamma I} (P : L.Fragment)
    (p : FinitePath Gamma.graph)
    (hparent : P.parent = (.inl p : Gamma.DPath))
    (hfinish : p.finish ∈ P.path.support) :
    P.path.terminal? = some p.finish := by
  cases hpath : P.path with
  | inl q =>
      change some q.finish = some p.finish
      congr 1
      by_contra hne
      have hfinishq : p.finish ∈ q.support := by
        simpa only [hpath, Path.support] using hfinish
      obtain ⟨y, hyq⟩ :=
        q.walk.exists_outgoing_edge_of_mem_of_ne_finish hfinishq
          (fun h ↦ hne h.symm)
      have hyp : (p.finish, y) ∈ p.edgeSet := by
        have hyP : (p.finish, y) ∈ P.path.edgeSet := by
          simpa only [hpath, Path.edgeSet, FinitePath.edgeSet] using hyq
        have hyParent := P.edges_subset hyP
        simpa only [hparent, Path.edgeSet] using hyParent
      exact (p.fst_ne_finish_of_mem_edge hyp) rfl
  | inr r =>
      have hrsub : r.support ⊆ p.support := by
        simpa only [hpath, hparent, Path.support] using P.support_subset
      have hrfinite : r.support.Finite := p.support_finite.subset hrsub
      exact False.elim
        ((Set.infinite_range_of_injective r.injective) hrfinite)

/-- Strong component form: maximality turns surviving connectivity to the
finite parent's terminal into membership of that terminal in the fragment;
the fragment's edge containment then fixes its orientation. -/
theorem finite_and_terminal_eq_parent_finish_of_survivingConnected
    (L : Input Gamma I) (C : Set (LV L))
    (p : FinitePath Gamma.graph) (P : L.Fragment)
    (hP : P ∈ GroundingCut.fragments L C)
    (hparent : P.parent = (.inl p : Gamma.DPath))
    (hconnected : GroundingCut.SurvivingConnected L C P.parent
      P.path.initial p.finish) :
    P.path.IsFinite ∧ P.path.terminal? = some p.finish := by
  have hpParent : p.finish ∈ P.parent.support := by
    simpa only [hparent, Path.support] using p.finish_mem_support
  have hpPath : p.finish ∈ P.path.support := by
    rw [hP.2]
    exact ⟨hpParent, hconnected⟩
  exact ⟨isFinite_of_parent_eq_finite P p hparent,
    terminal_eq_parent_finish_of_mem P p hparent hpPath⟩

/-- A maximal deleted-edge fragment containing the terminal of its finite
parent is finite and is oriented toward that same terminal. -/
theorem finite_and_terminal_eq_parent_finish
    (L : Input Gamma I) (C : Set (LV L))
    (p : FinitePath Gamma.graph) (P : L.Fragment)
    (hP : P ∈ GroundingCut.fragments L C)
    (hparent : P.parent = (.inl p : Gamma.DPath))
    (hfinish : p.finish ∈ P.path.support) :
    P.path.IsFinite ∧ P.path.terminal? = some p.finish := by
  have hclass : p.finish ∈
      {x | x ∈ P.parent.support ∧
        GroundingCut.SurvivingConnected L C P.parent P.path.initial x} := by
    rw [← hP.2]
    exact hfinish
  exact finite_and_terminal_eq_parent_finish_of_survivingConnected
    L C p P hP hparent hclass.2

end GroundingTerminalFragment
end Erdos599
