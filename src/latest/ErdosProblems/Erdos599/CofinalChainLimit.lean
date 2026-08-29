/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LadderConstantLimit
import ErdosProblems.Erdos599.SafeLinkGround

/-!
# Cofinal reindexing of genuine path limits

The direct limit of a growing warp chain is defined thread by thread.  This
file proves that passing to a cofinal family does not change the chosen
concrete path limit.
-/

noncomputable section

open Set

namespace Erdos599

universe u

open SafeLinkGround.DirectedPath.FinitePath

namespace DirectedPath.Path

variable {V : Type u} {D : Digraph V}

/-- A concrete chain limit extends into every path upper bound of the chain. -/
theorem chainLimit_extends_upper
    (C : Set (Path D)) (hCne : C.Nonempty)
    (hC : IsChain Extends C) {q : Path D}
    (hq : ∀ p ∈ C, Extends p q) :
    Extends (chainLimit C hCne hC) q := by
  let l := chainLimit C hCne hC
  have hlSupport : l.support = ⋃ p ∈ C, p.support :=
    support_chainLimit C hCne hC
  have hlUpper : ∀ p ∈ C, Extends p l := by
    intro p hp
    exact extends_chainLimit C hCne hC hp
  rcases hl : l with f | r
  · have hfinishUnion : f.finish ∈ ⋃ p ∈ C, p.support := by
      rw [← hlSupport, hl]
      exact f.finish_mem_support
    simp only [Set.mem_iUnion] at hfinishUnion
    obtain ⟨p, hpC, hfinishp⟩ := hfinishUnion
    have hpl : Extends p (.inl f) := by simpa only [← hl] using hlUpper p hpC
    have hfl : Path.support (.inl f : Path D) ⊆ p.support := by
      rcases p with p | s
      · change f.finish ∈ p.walk.support at hfinishp
        have hsupp : p.walk.support = f.walk.support :=
          support_eq_of_isPrefixOf_of_finish_mem hpl hfinishp
        intro x hx
        change x ∈ f.walk.support at hx
        change x ∈ p.walk.support
        rwa [hsupp]
      · exact False.elim hpl
    have hpeq : p = (.inl f : Path D) :=
      eq_of_extends_of_support_subset hpl hfl
    change Extends l q
    rw [hl, ← hpeq]
    exact hq p hpC
  · rcases q with f | s
    · exfalso
      have hrsupport : r.support ⊆ f.support := by
        intro x hx
        have hxUnion : x ∈ ⋃ p ∈ C, p.support := by
          rw [← hlSupport, hl]
          exact hx
        simp only [Set.mem_iUnion] at hxUnion
        obtain ⟨p, hpC, hxp⟩ := hxUnion
        exact support_mono_of_extends (hq p hpC) hxp
      exact (Set.infinite_range_of_injective r.injective)
        (f.support_finite.subset hrsupport)
    · change Extends l (.inr s)
      rw [hl]
      apply Ray.ext
      funext n
      have hrnUnion : r n ∈ ⋃ p ∈ C, p.support := by
        rw [← hlSupport, hl]
        exact r.apply_mem_support n
      simp only [Set.mem_iUnion] at hrnUnion
      obtain ⟨p, hpC, hrnp⟩ := hrnUnion
      have hpr : Extends p (.inr r) := by
        simpa only [← hl] using hlUpper p hpC
      have hps : Extends p (.inr s) := hq p hpC
      rcases p with p | t
      · change r n ∈ p.walk.support at hrnp
        obtain ⟨m, hm, hpm⟩ := List.mem_iff_getElem.mp hrnp
        have hmr : p.walk.support[m] = r m := hpr m hm
        have hmn : m = n := r.injective (hmr.symm.trans hpm)
        subst m
        exact (hpr n hm).symm.trans (hps n hm)
      · exact congrArg (fun z : Ray D ↦ z n) (hpr.symm.trans hps)

/-- Passing from a nonempty path-extension chain to a nonempty cofinal
subchain does not change the chosen concrete chain limit. -/
theorem chainLimit_eq_of_subset_of_cofinal
    (C E : Set (Path D))
    (hCne : C.Nonempty) (hEne : E.Nonempty)
    (hC : IsChain Extends C) (hE : IsChain Extends E)
    (hCE : C ⊆ E)
    (hcofinal : ∀ q ∈ E, ∃ p ∈ C, Extends q p) :
    chainLimit C hCne hC = chainLimit E hEne hE := by
  apply (eq_of_extends_of_support_subset ?_ ?_).symm
  · apply chainLimit_extends_upper E hEne hE
    intro q hqE
    obtain ⟨p, hpC, hqp⟩ := hcofinal q hqE
    exact extends_trans hqp (extends_chainLimit C hCne hC hpC)
  · rw [support_chainLimit, support_chainLimit]
    intro x hx
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨p, hpC, hxp⟩ := hx
    exact ⟨p, hCE hpC, hxp⟩

end DirectedPath.Path

end Erdos599
