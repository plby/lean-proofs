/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedRegularExtension
import ErdosProblems.Erdos599.HalfwayCausalProtectedEngine
import ErdosProblems.Erdos599.SubdivisionMengerAssembly

/-!
# Unconditional infinite directed Menger theorem

Both engines of the protected cardinal induction are supplied by actual
constructions. Hereditary subdivision incidence is needed only internally:
private arc subdivision supplies it, and exact contraction returns the
packing and orthogonal separator to the arbitrary original digraph.
-/

namespace Erdos599.UnroofedMengerAssembly

open Set CardinalInduction Blueprint

universe u

variable {V : Type u}

/-- Every unhindered web with hereditary subdivision incidence is linkable. -/
theorem unhindered_isLinkable_of_hereditarySubdivision
    (G : DWeb V) (hsub : HasHereditarySubdivisionIncidence G.graph)
    (hG : G.IsUnhindered) : IsLinkable G :=
  ProtectedCardinalAssembly.linkable_of_engines G hG
    (UnroofedRegularExtension.regularEngineFor G)
    (HalfwayCausalProtectedEngine.halfwayEngineFor G hsub)

/-- The exact infinite directed Menger conclusion, without auxiliary assumptions. -/
theorem directedMenger (D : Digraph V) (A B : Set V) :
    Bridge.DirectedMengerConclusion D A B :=
  SubdivisionMengerAssembly.directedMenger_of_subdivided_unhindered_theorem
    D A B unhindered_isLinkable_of_hereditarySubdivision

#print axioms unhindered_isLinkable_of_hereditarySubdivision
#print axioms directedMenger

end Erdos599.UnroofedMengerAssembly
