/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

noncomputable section


namespace Erdos223

open scoped Classical in
abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

end Erdos223

namespace Erdos223

open scoped Classical in
def IsDiameterOne {d : ℕ} (A : Finset (Point d)) : Prop :=
  Metric.diam (↑A : Set (Point d)) = 1

end Erdos223

namespace Erdos223

open scoped Classical in
noncomputable def diameterGraph {d : ℕ} (A : Finset (Point d)) :
    SimpleGraph {x // x ∈ A} where
  Adj x y := dist (x : Point d) (y : Point d) = 1
  symm.symm := by
    intro x y h
    simpa [dist_comm] using h
  loopless.irrefl := by
    intro x h
    simpa using h

end Erdos223

namespace Erdos223

open scoped Classical in
noncomputable instance diameterGraph.instDecidableRelAdj {d : ℕ}
    (A : Finset (Point d)) : DecidableRel (diameterGraph A).Adj :=
  Classical.decRel _

open scoped Classical in
noncomputable def diameterPairCount {d : ℕ} (A : Finset (Point d)) : ℕ :=
  (diameterGraph A).edgeFinset.card

end Erdos223

namespace Erdos223

open scoped Classical in
def attainableCounts (d n : ℕ) : Set ℕ :=
  {m | ∃ A : Finset (Point d),
    A.card = n ∧ IsDiameterOne A ∧ diameterPairCount A = m}

end Erdos223

namespace Erdos223

open scoped Classical in
noncomputable def f (d n : ℕ) : ℕ :=
  sSup (attainableCounts d n)

end Erdos223

namespace Erdos223

open scoped Classical in
def turanNumber (p n : ℕ) : ℕ :=
  (SimpleGraph.turanGraph n p).edgeFinset.card

end Erdos223

namespace Erdos223

open scoped Classical in
def ceilQuot (n p : ℕ) : ℕ := (n + p - 1) / p

end Erdos223

namespace Erdos223

open scoped Classical in
def fourCorrection (n : ℕ) : ℕ :=
  if n % 4 = 3 then 0 else 1

end Erdos223

namespace Erdos223

open scoped Classical in
def exactValue (d n : ℕ) : ℕ :=
  if d = 4 then
    turanNumber 2 n + ceilQuot n 2 + fourCorrection n
  else if d = 5 then
    turanNumber 2 n + n
  else if d % 2 = 0 then
    turanNumber (d / 2) n + d / 2
  else
    turanNumber (d / 2) n + ceilQuot n (d / 2) + (d / 2 - 1)

end Erdos223

namespace Erdos223

open scoped Classical in
def PublishedEventualExactClaim : Prop :=
  ∀ d, 4 ≤ d → ∃ N, ∀ n, N ≤ n → f d n = exactValue d n

end Erdos223

namespace Erdos223

open scoped Classical in
def Resolution : Prop :=
  f 2 2 = 1 ∧
  (∀ n, 3 ≤ n → f 2 n = n) ∧
  f 3 2 = 1 ∧
  f 3 3 = 3 ∧
  (∀ n, 4 ≤ n → f 3 n = 2 * n - 2) ∧
  (∀ d, 4 ≤ d →
    Tendsto (fun n : ℕ ↦ (f d n : ℝ) / (n : ℝ) ^ 2) atTop
      (nhds ((((d / 2 : ℕ) : ℝ) - 1) / (2 * (d / 2 : ℕ))))) ∧
  (∃ N, ∀ n, N ≤ n → f 4 n = exactValue 4 n) ∧
  (∀ d, 6 ≤ d → Even d →
    ∃ N, ∀ n, N ≤ n → f d n = exactValue d n) ∧
  ¬ PublishedEventualExactClaim ∧
  (∀ N, ∃ n, N ≤ n ∧ exactValue 7 n < f 7 n)

end Erdos223

namespace Erdos223

open scoped Classical in
theorem erdos_223 : Resolution := by
  sorry

end Erdos223

end
