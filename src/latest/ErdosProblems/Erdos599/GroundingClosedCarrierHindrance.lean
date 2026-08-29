/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingRootedReachabilityWarp

/-!
# A closed source component disjoint from a rooted separating boundary

A bi-unique relation with a rooted sink separator yields a finite wave.
If one original source lies in a forward-closed carrier disjoint from the
separator, no path of that wave starts there. Thus the wave is already a
hindrance, without retaining or identifying the omitted component as a ray
or finite path of a larger decomposition.
-/

noncomputable section

open Set

namespace Erdos599.GroundingClosedCarrierHindrance

open DirectedPath Alternating GroundingRootedReachabilityWarp

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Reachability preserves any forward-closed carrier. -/
theorem mem_of_reaches_of_closed
    {E : Set (V × V)} {C : Set V}
    (hclosed : ∀ {x y}, (x, y) ∈ E → x ∈ C → y ∈ C)
    {a b : V} (ha : a ∈ C)
    (hab : Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b) :
    b ∈ C := by
  induction hab with
  | refl => exact ha
  | tail _ hxy ih => exact hclosed hxy ih

/-- A source in a closed carrier disjoint from the rooted sink separator
is absent from the finite separating warp produced by reachability. -/
theorem exists_hindrance_of_closed_source
    (E : Set (V × V)) (T C : Set V)
    (hEadj : E ⊆ {e | Gamma.graph.Adj e.1 e.2})
    (hbi : Relator.BiUnique fun x y ↦ (x, y) ∈ E)
    (hsink : ∀ t ∈ T, ¬ HasOutgoing E t)
    (hsep : Popular.IsSeparator Gamma T)
    (hroot : ∀ t ∈ T, ∃ a ∈ Gamma.source,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a t)
    (hclosed : ∀ {x y}, (x, y) ∈ E → x ∈ C → y ∈ C)
    (hdisj : Disjoint C T)
    (a : V) (haSource : a ∈ Gamma.source) (haC : a ∈ C) :
    ∃ W : Set Gamma.DPath,
      Gamma.IsHindrance W ∧ Gamma.terminalFrontier W = T ∧
        a ∉ Gamma.initialSet W := by
  have hanti : IsReachabilityAntichain E T := by
    intro x hx y _hy hxy
    rcases hxy.cases_head with h | ⟨z, hxz, _hzy⟩
    · exact h
    · exact (hsink x hx ⟨z, hxz⟩).elim
  obtain ⟨P, hcover, hpaths⟩ :=
    exists_rootedReachabilityWarp hEadj hbi Set.Subset.rfl hanti hroot
  let W : Set Gamma.DPath := PopularSwitching.pathFamily P
  have hfrontier : Gamma.terminalFrontier W = T :=
    PopularSwitching.pathFamily_terminalFrontier_eq P hcover
  have hmissing : a ∉ Gamma.initialSet W := by
    rintro ⟨p, hp, hpInitial⟩
    obtain ⟨q, hq, hqp⟩ := hp
    subst p
    have hqStart : q.start = a := hpInitial
    have hfinishC : q.finish ∈ C := by
      apply mem_of_reaches_of_closed hclosed (hqStart ▸ haC)
      exact finitePath_start_reaches_of_mem_support q (hpaths q hq).1
        q.finish_mem_support
    exact Set.disjoint_left.mp hdisj hfinishC (P.ends_in_target hq)
  have hwave : Gamma.IsWave W :=
    PopularSwitching.pathFamily_isWave P hcover hsep
  refine ⟨W, ⟨hwave, ?_⟩, hfrontier, hmissing⟩
  intro heq
  exact hmissing (heq ▸ haSource)

#print axioms exists_hindrance_of_closed_source

end Erdos599.GroundingClosedCarrierHindrance
