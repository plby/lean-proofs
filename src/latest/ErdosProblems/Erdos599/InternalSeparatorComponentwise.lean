/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DirectedComponentwise
import ErdosProblems.Erdos599.MaximalWaveMengerLift
import ErdosProblems.Erdos599.UndirectedSingularMerge

/-!
# Componentwise solution behind an internal wave frontier

The quotient by a wave frontier is directed even when the original graph is
bidirected: incoming edges to the new source are deleted.  We therefore use
weak components of the quotient digraph, not connected components of the
original simple graph.

The first theorem below is the concrete countable-component criterion.  The
second is its cardinal-induction form: if every quotient component is
strictly smaller on at least one endpoint side, a source-oriented induction
hypothesis solves it, using directed transpose duality on the right-small
components.  The resulting quotient Menger pair lifts through the wave
frontier without having to cover every frontier vertex.
-/

noncomputable section

namespace Erdos599
namespace AharoniBerger
namespace InternalSeparatorComponentwise

open Cardinal Set DirectedPath

universe u

variable {V : Type u}

abbrev Separator (G : DWeb V) (M : G.Wave) : Set V :=
  MaximalWaveMengerLift.Separator G M

abbrev Quotient (G : DWeb V) (M : G.Wave) : DWeb V :=
  MaximalWaveMengerLift.Quotient G M

abbrev WeakComponent (G : DWeb V) (M : G.Wave) :=
  (DirectedComponentwise.WeakGraph (Quotient G M).graph).ConnectedComponent

/-- A wave frontier is a sound internal decomposition whenever each weak
component behind it has a countable slice on at least one endpoint side. -/
theorem directedMengerConclusion_of_componentwise_either_countable
    (G : DWeb V) (M : G.Wave)
    (hcount : ∀ c : WeakComponent G M,
      ((Quotient G M).source ∩ c.supp).Countable ∨
        ((Quotient G M).target ∩ c.supp).Countable) :
    Bridge.DirectedMengerConclusion G.graph G.source G.target := by
  apply MaximalWaveMengerLift.directedMengerConclusion_of_quotient G M
  exact DirectedComponentwise.directedMengerConclusion_of_componentwise_either_countable
      (Quotient G M).graph (Quotient G M).source (Quotient G M).target
      hcount

/-- Cardinal-induction version of the internal decomposition theorem.

`hsmaller` may choose a different endpoint side in every weak component.
The induction hypothesis itself is source-oriented; a right-small component
is transposed, solved by `hIH`, and transposed back. -/
theorem directedMengerConclusion_of_componentwise_either_mk_lt
    (G : DWeb V) (M : G.Wave) (kappa : Cardinal.{u})
    (hIH : ∀ (D : Digraph V) (A B : Set V), #A < kappa →
      Bridge.DirectedMengerConclusion D A B)
    (hsmaller : ∀ c : WeakComponent G M,
      #((Quotient G M).source ∩ c.supp : Set V) < kappa ∨
        #((Quotient G M).target ∩ c.supp : Set V) < kappa) :
    Bridge.DirectedMengerConclusion G.graph G.source G.target := by
  apply MaximalWaveMengerLift.directedMengerConclusion_of_quotient G M
  apply DirectedComponentwise.assemble
  intro c
  rcases hsmaller c with hsource | htarget
  · exact hIH (Quotient G M).graph
      ((Quotient G M).source ∩ c.supp)
      ((Quotient G M).target ∩ c.supp) hsource
  · have htransposed := hIH (transpose (Quotient G M).graph)
      ((Quotient G M).target ∩ c.supp)
      ((Quotient G M).source ∩ c.supp) htarget
    have hback :=
      DirectedEndpointDuality.directedMengerConclusion_transpose htransposed
    simpa using hback

/-- Supply the source-oriented hypothesis above from the existing lower
unhindered-linkability induction.  Thus the only new obligation in a
singular construction is the structural shrinking property of the chosen
wave quotient. -/
theorem directedMengerConclusion_of_lowerInduction_and_componentwise_shrink
    (G : DWeb V) (M : G.Wave) (kappa : Cardinal.{u})
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (hsmaller : ∀ c : WeakComponent G M,
      #((Quotient G M).source ∩ c.supp : Set V) < kappa ∨
        #((Quotient G M).target ∩ c.supp : Set V) < kappa) :
    Bridge.DirectedMengerConclusion G.graph G.source G.target := by
  apply directedMengerConclusion_of_componentwise_either_mk_lt
      G M kappa _ hsmaller
  intro D A B hA
  let H : DWeb V :=
    { graph := D
      source := A
      target := B }
  exact AharoniBerger.directedMengerConclusion_of_source_lt
    H hlower hA

/-- Assumption-free localization of the obstruction remaining behind any
chosen wave frontier.  Under lower induction, either the original web is
already solved or one weak quotient component is `kappa`-large on both
endpoint sides. -/
theorem directedMengerConclusion_or_exists_component_both_not_lt
    (G : DWeb V) (M : G.Wave) (kappa : Cardinal.{u})
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa) :
    Bridge.DirectedMengerConclusion G.graph G.source G.target ∨
      ∃ c : WeakComponent G M,
        ¬ #((Quotient G M).source ∩ c.supp : Set V) < kappa ∧
          ¬ #((Quotient G M).target ∩ c.supp : Set V) < kappa := by
  classical
  by_cases hbad : ∃ c : WeakComponent G M,
      ¬ #((Quotient G M).source ∩ c.supp : Set V) < kappa ∧
        ¬ #((Quotient G M).target ∩ c.supp : Set V) < kappa
  · exact Or.inr hbad
  · apply Or.inl
    apply directedMengerConclusion_of_lowerInduction_and_componentwise_shrink
      G M kappa hlower
    intro c
    by_cases hsource :
        #((Quotient G M).source ∩ c.supp : Set V) < kappa
    · exact Or.inl hsource
    · apply Or.inr
      by_contra htarget
      exact hbad ⟨c, hsource, htarget⟩

/-- Existential form: it is enough to construct one wave frontier whose
quotient weak components all satisfy the countable one-sided criterion. -/
theorem directedMengerConclusion_of_exists_decomposing_wave
    (G : DWeb V)
    (h : ∃ M : G.Wave, ∀ c : WeakComponent G M,
      ((Quotient G M).source ∩ c.supp).Countable ∨
        ((Quotient G M).target ∩ c.supp).Countable) :
    Bridge.DirectedMengerConclusion G.graph G.source G.target := by
  obtain ⟨M, hM⟩ := h
  exact directedMengerConclusion_of_componentwise_either_countable G M hM

#print axioms directedMengerConclusion_of_componentwise_either_countable
#print axioms directedMengerConclusion_of_componentwise_either_mk_lt
#print axioms directedMengerConclusion_of_lowerInduction_and_componentwise_shrink
#print axioms directedMengerConclusion_or_exists_component_both_not_lt
#print axioms directedMengerConclusion_of_exists_decomposing_wave

end InternalSeparatorComponentwise
end AharoniBerger
end Erdos599
