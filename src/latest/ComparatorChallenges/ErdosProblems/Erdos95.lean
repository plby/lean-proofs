/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos95

abbrev Point := EuclideanSpace ℝ (Fin 2)

noncomputable def pointPairs (P : Finset Point) : Finset (Sym2 Point) :=
  P.offDiag.image Sym2.mk.uncurry

noncomputable def pairDistance : Sym2 Point → ℝ :=
  Sym2.lift ⟨fun p q ↦ dist p q, dist_comm⟩

noncomputable def distances (P : Finset Point) : Finset ℝ :=
  (pointPairs P).image pairDistance

noncomputable def distanceMultiplicity (P : Finset Point) (u : ℝ) : ℕ :=
  ((pointPairs P).filter fun e ↦ pairDistance e = u).card

noncomputable def distanceEnergy (P : Finset Point) : ℕ :=
  ∑ u ∈ distances P, distanceMultiplicity P u ^ 2

theorem erdos_95 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ P : Finset Point,
      (distanceEnergy P : ℝ) ≤ C * (P.card : ℝ) ^ (3 + ε) := by
  sorry

end Erdos95
