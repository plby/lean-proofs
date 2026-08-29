/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeSubwarpRestriction

/-!
# Native linking after discarding a small exceptional reference carrier

The global reference need not have finite character. A large native hammock
avoids any prescribed small discarded-reference carrier. Its chosen member
then restricts honestly to the finite-character remaining subwarp, where
the native source-linking theorem applies. Smallness of the discarded
carrier is explicit; it is not inferred from an arbitrary limiting warp.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeHammock

open Set Cardinal Order DirectedPath Alternating
open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence

universe u

variable {V : Type u} {Gamma : DWeb V} {Y Local : Set Gamma.DPath} {s : V}

theorem HasCard.exists_referenceTerminal_path_avoiding_of_small_discard
    {e : Option V} {extra : Occurrence Y s → Prop} {rho : Cardinal.{u}}
    (h : HasCard Y s e extra (succ rho))
    (hY : Gamma.IsWarp Y) (hsub : Local ⊆ Y)
    (hfinite : Gamma.HasFiniteCharacter Local) (hrho : aleph0 ≤ rho)
    (hbad : #(Gamma.vertexSet (Y \ Local)) ≤ rho)
    (hnondeg : ∀ A, extra A → ∀ t, e = some t → ¬A.HasFiniteSwitchedPathTo t)
    {X : Set V} (hX : #X ≤ rho) :
    ∃ (A : Occurrence Y s) (p : FinitePath Gamma.graph),
      A ∈ goodRoutes Y s e extra ∧ p.start = s ∧
      p.finish ∈ Gamma.terminalFrontier Local ∧
      p.edgeSet ⊆ A.switchedEdges ∧ p.support ∩ X ⊆ endpoints s e := by
  let reserve := X ∪ Gamma.vertexSet (Y \ Local)
  have hreserve : #reserve ≤ rho :=
    (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le hrho hX hbad)
  obtain ⟨A, hA, havoid⟩ := h.exists_goodRoute_avoiding_referenceClosure hY hrho hreserve
  have hendsOff : Disjoint (endpoints s e) (Gamma.vertexSet Y) := by
    apply Set.disjoint_left.mpr
    intro x hx hxY
    rcases hx with hxs | hxt
    · exact hA.2.2.1 (Set.mem_singleton_iff.mp hxs ▸ hxY)
    · exact hA.2.2.2.1 x hxt hxY
  have hdiscard : Disjoint A.vertexSet (Gamma.vertexSet (Y \ Local)) := by
    apply Set.disjoint_left.mpr
    intro x hxA hxBad
    have hxEnd : x ∈ endpoints s e := havoid ⟨Or.inl hxA, Or.inr hxBad⟩
    obtain ⟨p, hp, hxp⟩ := hxBad
    exact Set.disjoint_left.mp hendsOff hxEnd ⟨p, hp.1, hxp⟩
  let hback := A.backwardEdges_subset_of_avoids_discardedReference hdiscard
  let B : Occurrence Local s := A.restrictReference hsub hback
  have hBvalid : Valid B := hA.1.restrictReference hsub hback
  have hBterminal : B.terminal? = e := by simpa [B] using hA.2.1
  have hBsource : s ∉ Gamma.vertexSet Local := by
    rintro ⟨p, hp, hsp⟩
    exact hA.2.2.1 ⟨p, hsub hp, hsp⟩
  have hBterminalOff : ∀ t, e = some t → t ∉ Gamma.vertexSet Local := by
    rintro t ht ⟨p, hp, htp⟩
    exact hA.2.2.2.1 t ht ⟨p, hsub hp, htp⟩
  have hBnondeg : ∀ t, e = some t → ¬B.HasFiniteSwitchedPathTo t := by
    intro t ht hp
    obtain ⟨p, hps, hpt, hpe⟩ := hp
    exact hnondeg A hA.2.2.2.2 t ht
      ⟨p, hps, hpt, hpe.trans (A.restrictReference_switchedEdges_subset hsub hback)⟩
  have hLocal : Gamma.IsWarp Local := hY.subset hsub
  have hpath : ∃ p : FinitePath Gamma.graph, p.start = s ∧
      p.finish ∈ Gamma.terminalFrontier Local ∧
      p.edgeSet ⊆ B.switchedEdges ∧ p.support ⊆ B.referenceClosure := by
    cases he : e with
    | none =>
        exact hBvalid.exists_referenceTerminal_path_of_infinite hLocal hfinite
          (hBterminal.trans he) hBsource
    | some t =>
        exact hBvalid.exists_referenceTerminal_path_of_nondegenerate hLocal hfinite
          (hBterminal.trans he) hBsource (hBterminalOff t he) (hBnondeg t he)
  obtain ⟨p, hps, hpt, hpB, _hpSupportB⟩ := hpath
  have hpA : p.edgeSet ⊆ A.switchedEdges :=
    hpB.trans (A.restrictReference_switchedEdges_subset hsub hback)
  have hpSupport : p.support ⊆ A.referenceClosure :=
    A.finitePath_support_subset_referenceClosure hY p hps hpA
  exact ⟨A, p, hA, hps, hpt, hpA,
    fun _ hx ↦ havoid ⟨hpSupport hx.1, Or.inl hx.2⟩⟩

#print axioms HasCard.exists_referenceTerminal_path_avoiding_of_small_discard

end Erdos599.Blueprint.ColouredSafeHammock
