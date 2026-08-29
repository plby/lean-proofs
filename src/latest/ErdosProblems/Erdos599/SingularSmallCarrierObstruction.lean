/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularSafeCarrierCardinal
import ErdosProblems.Erdos599.SingularSafeDesignatedLimit

/-!
# Localizing a residual-wave obstruction at a small deleted carrier

Let `M` be a wave after deleting a vertex set `X`.  Every ambient
source--target path either enters `X`, or restricts to a source--target path
in the deleted web and hence meets the terminal frontier of `M`.  Thus the
union of `X` and that frontier roofs the whole ambient source.

For a linkage on fewer than an uncountable cardinal `kappa` many initial
vertices, `X` may be taken to be the linkage carrier and is itself smaller
than `kappa`.  This is the precise small part of the rerouting problem: a
maximal residual wave handles all paths which avoid the carrier, while the
lower-cardinal exchange only has to handle paths entering the carrier.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularSmallCarrierObstruction

open DirectedPath

universe u

variable {V : Type u}

/-- A wave after deleting `X`, together with `X` itself, separates every
ambient source from the ambient target. -/
theorem source_subset_roof_terminalFrontier_union_deleted
    (G : DWeb V) (X : Set V)
    {W : Set (G.delete X).DPath}
    (hW : (G.delete X).IsWave W) :
    G.source ⊆ G.roof ((G.delete X).terminalFrontier W ∪ X) := by
  intro a ha p hp
  by_cases hmeet : G.Meets p X
  · obtain ⟨x, hxp, hxX⟩ := hmeet
    exact ⟨x, hxp, Or.inr hxX⟩
  · have hretain : p.support ⊆ Xᶜ := by
      intro x hxp hxX
      exact hmeet ⟨x, hxp, hxX⟩
    let q : DirectedPath.FinitePath (G.delete X).graph :=
      p.restrictGraphOnSupport fun e hu hv ↦
        ⟨e, hretain hu, hretain hv⟩
    have haDelete : a ∈ (G.delete X).source := by
      refine ⟨ha, ?_⟩
      intro haX
      exact hmeet ⟨a, hp.1 ▸ p.start_mem_support, haX⟩
    have hfinish : p.finish ∉ X := by
      intro hfinishX
      exact hmeet ⟨p.finish, p.finish_mem_support, hfinishX⟩
    have hq : (G.delete X).IsTargetPathFrom a q := by
      exact ⟨hp.1, hp.2, hfinish⟩
    obtain ⟨x, hxq, hxfrontier⟩ := hW.2.2 haDelete q hq
    refine ⟨x, ?_, Or.inl hxfrontier⟩
    have hsupport : q.support = p.support := by
      unfold q
      exact DirectedPath.FinitePath.support_restrictGraphOnSupport _ _
    rwa [hsupport] at hxq

/-- The same separator statement for a bundled residual wave. -/
theorem source_subset_roof_maximalWaveFrontier_union_deleted
    (G : DWeb V) (X : Set V)
    (M : (G.delete X).Wave) :
    G.source ⊆ G.roof
      ((G.delete X).terminalFrontier M.1 ∪ X) :=
  source_subset_roof_terminalFrontier_union_deleted G X M.2

/-- For a small designated linkage, the carrier part of the preceding
separator is strictly below `kappa`.  Maximality of `M` is not needed for
the localization; it is used only by the subsequent absorption/exchange
argument. -/
theorem smallCarrier_roof_with_residualWave
    {G : DWeb V} {A B : Set V} {P : Set G.DPath}
    {kappa : Cardinal.{u}}
    (hkappa : aleph0 < kappa)
    (hP : IsLinkageBetween G A B P)
    (hA : #A < kappa)
    (M : (G.delete (G.vertexSet P)).Wave) :
    #(G.vertexSet P) < kappa ∧
      G.source ⊆ G.roof
        ((G.delete (G.vertexSet P)).terminalFrontier M.1 ∪
          G.vertexSet P) := by
  exact ⟨SingularSafeCarrierCardinal.mk_vertexSet_lt_of_mk_initial_lt
      hkappa hP hA,
    source_subset_roof_maximalWaveFrontier_union_deleted
      G (G.vertexSet P) M⟩

#print axioms source_subset_roof_terminalFrontier_union_deleted
#print axioms smallCarrier_roof_with_residualWave

end SingularSmallCarrierObstruction
end CardinalInduction
end Erdos599
