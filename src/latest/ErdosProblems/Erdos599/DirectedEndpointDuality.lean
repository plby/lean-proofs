/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UndirectedFiniteEndpoint

/-!
# Source--target duality for directed Menger pairs

Reversing a path in a digraph changes the graph to its transpose.  This file
records that precise duality for the exact directed Menger conclusion.  In
particular, the already proved countable-source theorem also yields a
countable-target theorem, after applying it to the transposed web.
-/

noncomputable section

namespace Erdos599
namespace DirectedEndpointDuality

open Set DirectedPath

universe u

variable {V : Type u} {D : Digraph V} {A B : Set V}

/-- Reverse a bundled directed path, simultaneously transposing its graph
and exchanging its endpoint sets. -/
def reversePath (p : Bridge.DirectedABPath D A B) :
    Bridge.DirectedABPath (transpose D) B A where
  path := p.path.reverse
  start_mem := p.finish_mem
  finish_mem := p.start_mem

@[simp]
theorem supportSet_reversePath (p : Bridge.DirectedABPath D A B) :
    (reversePath p).supportSet = p.supportSet := by
  exact FinitePath.support_reverse p.path

/-- Reverse every member of a directed path family. -/
def reverseFamily (P : Set (Bridge.DirectedABPath D A B)) :
    Set (Bridge.DirectedABPath (transpose D) B A) :=
  reversePath '' P

theorem reverseFamily_isPacking
    {P : Set (Bridge.DirectedABPath D A B)}
    (hP : Bridge.DirectedIsPathPacking P) :
    Bridge.DirectedIsPathPacking (reverseFamily P) := by
  rintro p ⟨q, hq, rfl⟩ r ⟨s, hs, rfl⟩ hne
  change Disjoint (reversePath q).supportSet (reversePath s).supportSet
  rw [supportSet_reversePath, supportSet_reversePath]
  apply hP hq hs
  intro hqs
  exact hne (congrArg reversePath hqs)

/-- A path in the transposed graph, reversed back and transported across
`transpose (transpose D) = D`. -/
def unreversePath
    (q : Bridge.DirectedABPath (transpose D) B A) :
    Bridge.DirectedABPath D A B :=
  cast (congrArg (fun F : Digraph V ↦
    Bridge.DirectedABPath F A B) (transpose_transpose D)) (reversePath q)

private theorem directedABPath_supportSet_cast
    {D E : Digraph V} {A B : Set V} (h : D = E)
    (p : Bridge.DirectedABPath D A B) :
    (cast (congrArg (fun F : Digraph V ↦
      Bridge.DirectedABPath F A B) h) p).supportSet = p.supportSet := by
  subst h
  rfl

@[simp]
theorem supportSet_unreversePath
    (q : Bridge.DirectedABPath (transpose D) B A) :
    (unreversePath (D := D) (A := A) (B := B) q).supportSet =
      q.supportSet := by
  exact (directedABPath_supportSet_cast (transpose_transpose D)
    (reversePath q)).trans (supportSet_reversePath q)

theorem transpose_isSeparator
    {S : Set V} (hS : Bridge.DirectedIsABSeparator D A B S) :
    Bridge.DirectedIsABSeparator (transpose D) B A S := by
  intro q
  obtain ⟨v, hvS, hvq⟩ := hS
    (unreversePath (D := D) (A := A) (B := B) q)
  exact ⟨v, hvS, by simpa using hvq⟩

theorem reverseFamily_isOrthogonal
    {P : Set (Bridge.DirectedABPath D A B)} {S : Set V}
    (horth : Bridge.DirectedIsOrthogonal P S) :
    Bridge.DirectedIsOrthogonal (reverseFamily P) S := by
  constructor
  · intro v hv
    have hv' := horth.1 hv
    simp only [Set.mem_iUnion] at hv' ⊢
    obtain ⟨p, hp, hvp⟩ := hv'
    exact ⟨reversePath p, ⟨p, hp, rfl⟩, by simpa using hvp⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := hp
    obtain ⟨v, hv, huniq⟩ := horth.2 q hq
    refine ⟨v, by simpa using hv, ?_⟩
    intro w hw
    apply huniq w
    simpa using hw

/-- The exact directed conclusion is invariant under simultaneously
transposing the graph and exchanging source and target. -/
theorem directedMengerConclusion_transpose
    (h : Bridge.DirectedMengerConclusion D A B) :
    Bridge.DirectedMengerConclusion (transpose D) B A := by
  obtain ⟨P, S, hP, hsep, horth⟩ := h
  exact ⟨reverseFamily P, S, reverseFamily_isPacking hP,
    transpose_isSeparator hsep, reverseFamily_isOrthogonal horth⟩

/-- Exchange the two endpoint sets of a web while transposing every edge. -/
def transposeWeb (G : DWeb V) : DWeb V where
  graph := transpose G.graph
  source := G.target
  target := G.source

/-- The countable-source directed theorem, applied after precise directed
duality, gives an unconditional countable-target theorem. -/
theorem directedMengerConclusion_of_target_countable
    (G : DWeb V) (htarget : G.target.Countable) :
    Bridge.DirectedMengerConclusion G.graph G.source G.target := by
  have htransposed :=
    AharoniBerger.directedMengerConclusion_of_source_countable
      (transposeWeb G) htarget
  have hback := directedMengerConclusion_transpose htransposed
  simpa [transposeWeb] using hback

#print axioms directedMengerConclusion_transpose
#print axioms directedMengerConclusion_of_target_countable

end DirectedEndpointDuality
end Erdos599
