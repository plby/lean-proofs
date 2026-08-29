/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularFiniteFreedCarrierCorrection

/-!
# Endpoint purity of the carrier freed by an exact-boundary exchange

The finite marked exchange preserves the designated terminal frontier
literally.  In a normalized web this has a useful consequence which is
stronger than the usual source-purity statement: an old carrier vertex
which is absent from the replacement carrier is neither a source nor a
target.  Thus the remaining finite roof defect lies in the genuinely
internal colour of the old linkage and does not contain the target points
which obstruct an ordinary deletion--quotient arrow.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularExactBoundaryFreedCarrier

open DWeb
open SingularEndpointCarrierSplit

universe u

variable {V : Type u}

/-- Exact preservation of the terminal frontier prevents a replacement
target linkage from freeing any ambient target vertex. -/
theorem disjoint_target_freedCarrier_of_terminalFrontier_eq
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} {P Q : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hQ : IsLinkageBetween G A G.target Q)
    (hterminal : G.terminalFrontier Q = G.terminalFrontier P) :
    Disjoint G.target (G.vertexSet P \ G.vertexSet Q) := by
  rw [Set.disjoint_left]
  rintro x hxTarget ⟨hxP, hxNotQ⟩
  have hxTerminalP : x ∈ G.terminalFrontier P := by
    rw [← vertexSet_inter_target_eq_terminalFrontier hNorm hP]
    exact ⟨hxP, hxTarget⟩
  have hxTerminalQ : x ∈ G.terminalFrontier Q := by
    rw [hterminal]
    exact hxTerminalP
  apply hxNotQ
  obtain ⟨q, hqQ, hqx⟩ := hxTerminalQ
  exact ⟨q, hqQ, G.terminal_mem_support hqx⟩

/-- If the two exact-boundary linkages also have the same prescribed source
set, the entire freed carrier lies in the internal colour of the old
linkage. -/
theorem freedCarrier_subset_internalCarrier_of_exact_boundary
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source) {P Q : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hQ : IsLinkageBetween G A G.target Q)
    (hterminal : G.terminalFrontier Q = G.terminalFrontier P) :
    G.vertexSet P \ G.vertexSet Q ⊆ internalCarrier G P := by
  have hSource : Disjoint G.source (G.vertexSet P \ G.vertexSet Q) :=
    SingularFiniteFreedCarrierCorrection.disjoint_source_freedCarrier_of_targetLinkage_update
      hNorm hA hP hQ
  have hTarget : Disjoint G.target (G.vertexSet P \ G.vertexSet Q) :=
    disjoint_target_freedCarrier_of_terminalFrontier_eq
      hNorm hP hQ hterminal
  rintro x hxFreed
  refine ⟨hxFreed.1, ?_⟩
  rintro (hxSource | hxTarget)
  · exact Set.disjoint_left.1 hSource hxSource hxFreed
  · exact Set.disjoint_left.1 hTarget hxTarget hxFreed

#print axioms disjoint_target_freedCarrier_of_terminalFrontier_eq
#print axioms freedCarrier_subset_internalCarrier_of_exact_boundary

end SingularExactBoundaryFreedCarrier
end CardinalInduction
end Erdos599
