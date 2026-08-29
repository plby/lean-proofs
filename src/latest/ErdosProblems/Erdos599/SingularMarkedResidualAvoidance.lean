/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.OneHoleRouteBalance
import ErdosProblems.Erdos599.SingularMarkedResidualColorIsolation

/-!
# Carrier avoidance for a marked residual route

`SingularMarkedResidualColorIsolation` proves that the finite-component
decomposition of an avoiding toggle still avoids the forbidden carrier.
This file packages that result directly at the reduced-route interface used
by maximal-residual-wave arguments.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularMarkedResidualAvoidance

open DWeb Alternating
open SingularMarkedResidualColorIsolation

universe u

variable {V : Type u}

/-- A reduced marked route whose old family and every route state avoid
`X` produces an exact one-point augmentation whose whole carrier avoids
`X`.  The component decomposition is performed only after the avoidance
certificate has been attached to the toggled edge relation. -/
theorem exists_avoiding_onePointAugmentation_of_reducedRoute
    {G : DWeb V} {J : Set G.DPath} {X : Set V}
    {a b : V} {l : List (OneHoleResidualState V)}
    (hJ : G.IsCleanFiniteWarp J)
    (hJavoid : Disjoint X (G.vertexSet J))
    (ha : a ∈ G.source \ G.initialSet J)
    (hb : b ∈ G.target \ G.terminalFrontier J)
    (hab : a ≠ b)
    (hl : IsReducedMarkedRoute G J a b l)
    (hstates : ∀ n (hn : n < l.length), l[n].vertex ∉ X) :
    ∃ Jplus : Set G.DPath,
      G.IsOnePointAugmentation J Jplus ∧
        Disjoint X (G.vertexSet Jplus) := by
  let T : OneHoleToggleCertificate G J a b :=
    oneHoleToggleCertificateOfReducedRoute hJ ha hl
      (oneHoleRouteBalance G J a b l hJ ha hl)
  have hforwardAvoid : oneHoleRouteForwardEdges G J l ⊆ Xᶜ ×ˢ Xᶜ := by
    rintro e ⟨i, _hi, rfl⟩
    exact ⟨hstates i.1 (by omega), hstates (i.1 + 1) (by omega)⟩
  have holdEdgesAvoid : familyEdges J ⊆ Xᶜ ×ˢ Xᶜ := by
    rintro e he
    simp only [familyEdges, Set.mem_iUnion] at he
    obtain ⟨p, hpJ, hep⟩ := he
    have hs := p.edgeSet_subset_support_prod hep
    exact ⟨fun hx ↦ Set.disjoint_left.1 hJavoid hx ⟨p, hpJ, hs.1⟩,
      fun hx ↦ Set.disjoint_left.1 hJavoid hx ⟨p, hpJ, hs.2⟩⟩
  have htoggleAvoid : T.edges ⊆ Xᶜ ×ˢ Xᶜ := by
    change oneHoleRouteToggledEdges G J l ⊆ Xᶜ ×ˢ Xᶜ
    rintro e (he | he)
    · exact holdEdgesAvoid he.1
    · exact hforwardAvoid he
  exact exists_onePointAugmentation_of_toggleCertificate_avoiding
    G hJ ha hb hab T X htoggleAvoid hJavoid

#print axioms exists_avoiding_onePointAugmentation_of_reducedRoute

end SingularMarkedResidualAvoidance
end CardinalInduction
end Erdos599
