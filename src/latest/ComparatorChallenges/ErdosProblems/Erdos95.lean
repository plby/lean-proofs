import Mathlib

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos95

abbrev Point := EuclideanSpace ℝ (Fin 2)

end Erdos95

namespace Erdos95

noncomputable def pointPairs (P : Finset Point) : Finset (Sym2 Point) :=
  P.offDiag.image Sym2.mk.uncurry

end Erdos95

namespace Erdos95

noncomputable def pairDistance : Sym2 Point → ℝ :=
  Sym2.lift ⟨fun p q ↦ dist p q, dist_comm⟩

end Erdos95

namespace Erdos95

noncomputable def distances (P : Finset Point) : Finset ℝ :=
  (pointPairs P).image pairDistance

end Erdos95

namespace Erdos95

noncomputable def distanceMultiplicity (P : Finset Point) (u : ℝ) : ℕ :=
  ((pointPairs P).filter fun e ↦ pairDistance e = u).card

end Erdos95

namespace Erdos95

noncomputable def distanceEnergy (P : Finset Point) : ℕ :=
  ∑ u ∈ distances P, distanceMultiplicity P u ^ 2

end Erdos95

namespace Erdos95

def Statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ P : Finset Point,
    (distanceEnergy P : ℝ) ≤ C * (P.card : ℝ) ^ (3 + ε)

end Erdos95

namespace Erdos95

theorem erdos95 : Statement := by
  sorry

end Erdos95

end
