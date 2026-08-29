/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCausalInitialStableState
import ErdosProblems.Erdos599.HalfwayCausalClubGeometry

/-!
# The actual protected half-way engine

The repaired causal rows, their genuine avoiding club, the initial state
and the fair protected completion are all constructed. The only extension
input is through the current cardinal, exactly as required by the
simultaneous cardinal induction. There is no grounding premise.
-/

namespace Erdos599.CardinalInduction.HalfwayCausalProtectedEngine

open Set Cardinal Order
open Blueprint Blueprint.LinkageBlueprint
open Blueprint.LinkageBlueprint.CausalSection9Rows
open ProtectedCardinalAssembly

universe u

variable {V : Type u}

/-- The actual half-way engine on a hereditary subdivision ambient graph. -/
theorem halfwayEngineFor
    (Base : DWeb V) (hsub : HasHereditarySubdivisionIncidence Base.graph) :
    HalfwayEngineFor Base := by
  intro kappa hkappa hext H hHBase hNorm hH A0 hA0source hA0card
  have hseed : #A0 ≤ succ kappa := hA0card.le.trans (le_succ kappa)
  obtain ⟨C, hC, _hclosed⟩ := exists_clubStageGeometry_of_constantBase
    (Gamma := H) (Y := ∅) (seed := A0) (base := ∅)
    hkappa hNorm hH hseed (by simp)
  have hextH : ExtensionThroughFor H kappa := by
    intro rho hrho J hJH hJ
    exact hext rho hrho J (fun {_ _} hxy ↦ hHBase (hJH hxy)) hJ
  have hA0 : A0.Nonempty := Cardinal.mk_set_ne_zero_iff.mp (by
    rw [hA0card]
    exact (Cardinal.aleph0_pos.trans_le hkappa).ne')
  exact exists_endpointProtectedHalfway_of_nonempty hkappa hNorm hH hseed C hC
    hextH (hsub.of_adj_imp (fun {_ _} hxy ↦ hHBase hxy)) hA0source hA0card.le
    (seed_subset_globalCarrier hkappa hNorm hseed) hA0

#print axioms halfwayEngineFor

end Erdos599.CardinalInduction.HalfwayCausalProtectedEngine
