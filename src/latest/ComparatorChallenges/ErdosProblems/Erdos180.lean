/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Released under the Apache 2.0 license. This file has been modified. -/

import Mathlib

namespace Erdos180

structure FiniteGraph where
  order : ℕ
  graph : SimpleGraph (Fin order)

def FamilyFree (family : Finset FiniteGraph) {n : ℕ}
    (host : SimpleGraph (Fin n)) : Prop :=
  ∀ forbidden ∈ family, forbidden.graph.Free host

noncomputable def familyExtremal (family : Finset FiniteGraph)
    (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (FamilyFree family)).sup
    (fun host : SimpleGraph (Fin n) => host.edgeFinset.card)

theorem not_erdos_180 :
    ¬ (∀ family : Finset FiniteGraph,
      family.Nonempty → (∀ forbidden ∈ family, ¬ forbidden.graph.IsAcyclic) →
        ∃ forbidden ∈ family, ∃ C : ℝ, 0 < C ∧
          ∀ᶠ n : ℕ in Filter.atTop,
            (SimpleGraph.extremalNumber n forbidden.graph : ℝ) ≤
              C * (familyExtremal family n : ℝ)) := by
  sorry

end Erdos180
