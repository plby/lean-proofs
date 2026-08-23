/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped BigOperators

noncomputable section

namespace Erdos95

open scoped Classical in
abbrev Point := EuclideanSpace ℝ (Fin 2)

end Erdos95

namespace Erdos95

open scoped Classical in
noncomputable def pointPairs (P : Finset Point) : Finset (Sym2 Point) :=
  P.offDiag.image Sym2.mk.uncurry

end Erdos95

namespace Erdos95

open scoped Classical in
noncomputable def pairDistance : Sym2 Point → ℝ :=
  Sym2.lift ⟨fun p q ↦ dist p q, dist_comm⟩

end Erdos95

namespace Erdos95

open scoped Classical in
noncomputable def distances (P : Finset Point) : Finset ℝ :=
  (pointPairs P).image pairDistance

end Erdos95

namespace Erdos95

open scoped Classical in
noncomputable def distanceMultiplicity (P : Finset Point) (u : ℝ) : ℕ :=
  ((pointPairs P).filter fun e ↦ pairDistance e = u).card

end Erdos95

namespace Erdos95

open scoped Classical in
noncomputable def distanceEnergy (P : Finset Point) : ℕ :=
  ∑ u ∈ distances P, distanceMultiplicity P u ^ 2

end Erdos95

namespace Erdos95

open scoped Classical in
def Statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ P : Finset Point,
    (distanceEnergy P : ℝ) ≤ C * (P.card : ℝ) ^ (3 + ε)

end Erdos95

namespace Erdos95

open scoped Classical in
theorem erdos95 : Statement := by
  sorry

end Erdos95

end
