/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Set.Card
import Mathlib.Topology.Instances.Real.Lemmas

open Filter Topology

namespace Erdos1005

/-- A rational `q` is a Farey fraction of order `n` if it lies in `[0,1]` and has
denominator at most `n`. Recall every `q : ℚ` is stored in lowest terms, so `q.den`
is the reduced denominator and `q.num` the reduced numerator. -/
def IsFarey (n : ℕ) (q : ℚ) : Prop := 0 ≤ q ∧ q ≤ 1 ∧ q.den ≤ n

/-- The number of Farey fractions of order `n` strictly between `x` and `y`. -/
noncomputable def betweenCount (n : ℕ) (x y : ℚ) : ℕ :=
  {q : ℚ | IsFarey n q ∧ x < q ∧ q < y}.ncard

/-- The largest safe separation of indices in the ordered Farey sequence is
one less than the smallest index difference of a badly ordered pair, hence
is the minimum number of Farey fractions strictly between such a pair.
Values at orders with no badly ordered pair do not affect the limit. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {k | ∃ x y : ℚ, IsFarey n x ∧ IsFarey n y ∧ x < y ∧
    (x.num - y.num) * ((x.den : ℤ) - y.den) < 0 ∧ betweenCount n x y = k}

theorem erdos_1005 :
    Tendsto (fun n : ℕ => (f n : ℝ) / n) atTop (𝓝 (1 / 4)) := by
  sorry

end Erdos1005
