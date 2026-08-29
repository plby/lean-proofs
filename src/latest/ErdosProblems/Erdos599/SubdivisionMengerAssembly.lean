/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DirectedArcSubdivisionMenger
import ErdosProblems.Erdos599.DirectedArcSubdivisionIncidence
import ErdosProblems.Erdos599.AharoniBerger

/-!
# Exact Menger reduction to hereditary subdivision-incidence webs

The incidence restriction is internal to the linkability theorem.  The
arbitrary input graph is subdivided, its maximal-wave quotient inherits the
incidence property, and the resulting full Menger pair is contracted back.
No incidence assumption is imposed on the original graph.
-/

namespace Erdos599
namespace SubdivisionMengerAssembly

open Set
open AharoniBerger Blueprint DirectedArcSubdivision

universe u

variable {V : Type u}

/-- Maximal-wave reduction for one web with hereditary incidence.  Only the
particular quotient used in the construction is passed to the deep theorem. -/
theorem menger_of_hereditary_unhindered_theorem
    (G : DWeb V) (hG : HasHereditarySubdivisionIncidence G.graph)
    (hunhindered : ∀ Q : DWeb V,
      HasHereditarySubdivisionIncidence Q.graph →
      Q.IsUnhindered → CardinalInduction.IsLinkable Q) :
    Bridge.DirectedMengerConclusion G.graph G.source G.target := by
  obtain ⟨M, hMmax⟩ := G.exists_maximal_wave
  let Q := G.quotient (concreteMaximalSeparator G M)
  have hQincidence : HasHereditarySubdivisionIncidence Q.graph :=
    hG.of_adj_imp (fun {_ _} h ↦ G.quotient_adj_imp h)
  have hQloose : Q.IsLoose := by
    dsimp only [Q]
    rw [concreteMaximalSeparator_eq_essential]
    exact G.quotient_essentialTerminalFrontier_isLoose_of_isMax
      M.property hMmax
  have hQunhindered : Q.IsUnhindered :=
    concrete_isUnhindered_of_isLoose Q hQloose
  obtain ⟨L, hL⟩ := hunhindered Q hQincidence hQunhindered
  exact (concreteSpliceWitnessOfLinkage G M hL).directedMengerConclusion

/-- The hereditary-incidence linkability theorem suffices for the exact
Menger conclusion on an arbitrary directed graph.  All new vertices remain
in the original vertex universe. -/
theorem directedMenger_of_subdivided_unhindered_theorem
    (D : Digraph V) (A B : Set V)
    (hunhindered : ∀ Q : DWeb (Vertex D),
      HasHereditarySubdivisionIncidence Q.graph →
      Q.IsUnhindered → CardinalInduction.IsLinkable Q) :
    Bridge.DirectedMengerConclusion D A B := by
  let G : DWeb V := { graph := D, source := A, target := B }
  apply directedMenger_of_subdivision
  exact menger_of_hereditary_unhindered_theorem (web G)
    (graph_hasHereditarySubdivisionIncidence D) hunhindered

#print axioms menger_of_hereditary_unhindered_theorem
#print axioms directedMenger_of_subdivided_unhindered_theorem

end SubdivisionMengerAssembly
end Erdos599

