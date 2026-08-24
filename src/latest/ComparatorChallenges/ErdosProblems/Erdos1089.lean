/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter
open scoped Topology

namespace Erdos1089

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable def distanceFinset {d : ℕ} (P : Finset (Point d)) : Finset ℝ :=
    P.offDiag.image fun xy => dist xy.1 xy.2

noncomputable def distanceCount {d : ℕ} (P : Finset (Point d)) : ℕ :=
  (distanceFinset P).card

def ForcesDistances (d n m : ℕ) : Prop :=
  ∀ P : Finset (Point d), P.card = m → n ≤ distanceCount P

noncomputable def g (d n : ℕ) : ℕ :=
  sInf {m : ℕ | ForcesDistances d n m}

theorem erdos_1089 (n : ℕ) (hn : 2 ≤ n) :
    (∀ d, (d + 1).choose (n - 1) + 1 ≤ g d n ∧
      g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
    Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1))
      atTop (𝓝 ((1 : ℝ) / (n - 1).factorial)) := by
  sorry

end Erdos1089
