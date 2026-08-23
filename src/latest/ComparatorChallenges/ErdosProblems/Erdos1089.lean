import Mathlib

open Asymptotics Filter Metric Set
open scoped BigOperators Topology RealInnerProductSpace

noncomputable section


namespace Erdos1089

open scoped Classical in
abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

end Erdos1089

namespace Erdos1089

open scoped Classical in
noncomputable def distanceFinset {d : ℕ} (P : Finset (Point d)) : Finset ℝ :=
  open scoped Classical in
  P.offDiag.image fun xy => dist xy.1 xy.2

end Erdos1089

namespace Erdos1089

open scoped Classical in
noncomputable def distanceCount {d : ℕ} (P : Finset (Point d)) : ℕ :=
  (distanceFinset P).card

end Erdos1089

namespace Erdos1089

open scoped Classical in
def ForcesDistances (d n m : ℕ) : Prop :=
  ∀ P : Finset (Point d), P.card = m → n ≤ distanceCount P

end Erdos1089

namespace Erdos1089

open scoped Classical in
noncomputable def g (d n : ℕ) : ℕ :=
  sInf {m : ℕ | ForcesDistances d n m}

end Erdos1089

namespace Erdos1089

open scoped Classical in
theorem erdos_1089 (n : ℕ) (hn : 2 ≤ n) :
    (∀ d, (d + 1).choose (n - 1) + 1 ≤ g d n ∧
      g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
    Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1))
      atTop (𝓝 ((1 : ℝ) / (n - 1).factorial)) := by
  sorry

end Erdos1089

end
