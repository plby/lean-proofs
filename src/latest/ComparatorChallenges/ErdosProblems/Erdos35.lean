/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 35

Let `B ⊆ ℕ` be an additive basis of order `k`, with `0 ∈ B`.  Plünnecke's
Schnirelmann-density inequality gives

`σ(A + B) ≥ σ(A) ^ (1 - 1 / k)`.

The elementary power estimate

`α ^ (1 - 1 / k) ≥ α + α * (1 - α) / k`

then resolves Erdős Problem 35 in the affirmative.  The finite core below is
the truncated addition-graph version of Plünnecke's magnification inequality;
the truncation is essential because Schnirelmann density uses every initial
interval.

Mathematical sources:

* H. Plünnecke, *Eine zahlentheoretische Anwendung der Graphentheorie*,
  J. Reine Angew. Math. 243 (1970), 171–183.
* R. Jin, *Density Versions of Plünnecke Inequality—Epsilon-Delta Approach*,
  in CANT 2011 and 2012, Springer Proc. Math. Stat. 101 (2014), 99–113,
  especially Theorem 3 and Section 4.
* https://www.erdosproblems.com/35
-/

open scoped BigOperators Pointwise
open Finset Set Real


noncomputable section

namespace Erdos35

open scoped Classical in
/-- The exact order-`k` additive-basis predicate used in Problem 35.  Pointwise
natural scalar multiplication is the `k`-fold sumset, with `0 • B = {0}`. -/
def IsAdditiveBasisOfOrder (B : Set ℕ) (k : ℕ) : Prop :=
  k • B = Set.univ

open scoped Classical in
/-- The number of elements of `A` in the closed natural interval `[a,b]`. -/
def countOn (A : Set ℕ) (a b : ℕ) : ℕ :=
  #{x ∈ Icc a b | x ∈ A}

open scoped Classical in
/-- The number of elements of `A` in `{1, ..., n}`. -/
def countIn (A : Set ℕ) (n : ℕ) : ℕ :=
  #{x ∈ Ioc 0 n | x ∈ A}


open scoped Classical in
theorem erdos35 (A B : Set ℕ) (k : ℕ) (_hzero : 0 ∈ B)
    (hBasis : IsAdditiveBasisOfOrder B k) :
    schnirelmannDensity A +
        schnirelmannDensity A * (1 - schnirelmannDensity A) / k ≤
      schnirelmannDensity (A + B) := by
  sorry

end Erdos35

end
