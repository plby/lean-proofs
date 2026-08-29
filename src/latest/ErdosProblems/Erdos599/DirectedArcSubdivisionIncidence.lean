/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DirectedArcSubdivision
import ErdosProblems.Erdos599.ArcSubdivisionNoStrong

/-!
# Incidence of the directed-arc subdivision

The two private vertices inserted into every directed arc give each of the
three replacement edges the hereditary incidence pattern used to exclude
strong imaginary real edges.  Two private vertices are important here: the
argument remains valid when the original arc is a loop.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DirectedArcSubdivision

open Blueprint

universe u

variable {V : Type u}

/-- Every edge of the three-edge directed-arc subdivision has subdivision
incidence.  This includes subdivisions of loops in the original digraph. -/
theorem graph_hasHereditarySubdivisionIncidence (D : Digraph V) :
    HasHereditarySubdivisionIncidence (graph D) := by
  intro a b hab
  cases a with
  | original x =>
      cases b with
      | original y => simp [graph] at hab
      | first e =>
          have htail : x = e.1.1 := hab
          refine ⟨by simp, Or.inl ⟨.second e, by simp, by simp, ?_, ?_⟩⟩
          · intro z hz
            have hz' := (predecessor_first e z).1 hz
            simpa [htail] using hz'
          · intro z hz
            exact (successor_first e z).1 hz
      | second e => simp [graph] at hab
  | first e =>
      cases b with
      | original y => simp [graph] at hab
      | first f => simp [graph] at hab
      | second f =>
          have hef : e = f := hab
          subst f
          refine ⟨by simp, Or.inl ⟨.original e.1.2,
            by simp, by simp, ?_, ?_⟩⟩
          · intro z hz
            exact (predecessor_second e z).1 hz
          · intro z hz
            exact (successor_second e z).1 hz
  | second e =>
      cases b with
      | original y =>
          have hhead : e.1.2 = y := hab
          refine ⟨by simp, Or.inr ⟨.first e, by simp, by simp, ?_, ?_⟩⟩
          · intro z hz
            have hz' := (successor_second e z).1 hz
            simpa [hhead] using hz'
          · intro z hz
            exact (predecessor_second e z).1 hz
      | first f => simp [graph] at hab
      | second f => simp [graph] at hab

/-- Every real edge of a subdivided web is not a strong imaginary edge at
an infinite cardinal. -/
theorem web_edge_not_isStrongImaginaryEdge
    (G : DWeb V) {Y : Set (web G).DPath} {kappa : Cardinal.{u}}
    (hkappa : aleph0 ≤ kappa) {a b : Vertex G.graph}
    (hab : (web G).graph.Adj a b) :
    ¬ IsStrongImaginaryEdge (web G) Y kappa a b := by
  apply (graph_hasHereditarySubdivisionIncidence G.graph).no_strongImaginaryEdge
    hkappa
  exact hab

#print axioms graph_hasHereditarySubdivisionIncidence
#print axioms web_edge_not_isStrongImaginaryEdge

end DirectedArcSubdivision
end Erdos599

