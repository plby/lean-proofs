/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

noncomputable section

namespace Erdos622

variable {V : Type*} [Fintype V] [DecidableEq V]

open scoped Classical in
def IsSpannedByCycle (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ v : (S : Set V), ∃ p : (G.induce (S : Set V)).Walk v v,
    p.IsHamiltonianCycle

end Erdos622

namespace Erdos622

variable {V : Type*} [Fintype V] [DecidableEq V]

open scoped Classical in
noncomputable def cycleSpannedSubsets (G : SimpleGraph V) : Finset (Finset V) :=
  (Finset.univ : Finset V).powerset.filter (IsSpannedByCycle G)

end Erdos622

namespace Erdos622

open scoped Classical in
def Resolution : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    ∀ G : SimpleGraph (Fin (2 * n)),
      G.IsRegularOfDegree (n + 1) →
        ((1 / 2 : ℝ) - ε) * (2 : ℝ) ^ (2 * n) ≤
          ((cycleSpannedSubsets G).card : ℝ)

end Erdos622

namespace Erdos622

open scoped Classical in
theorem erdos_622 : Resolution := by
  sorry

end Erdos622

end
