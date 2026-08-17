import Mathlib

/-!
# Erdős Problem 440

For a strictly increasing sequence of positive natural numbers, let its
counting function be the number of indices whose adjacent least common
multiple is at most the threshold.

The file proves the square-root upper bound, the sharp universal limsup
constant of Erdős--Szemerédi, and that the largest possible liminf is one.

References:

* P. Erdős and E. Szemerédi, *Megjegyzések az American Mathematical
  Monthly egy problémájáról*, Matematikai Lapok 28 (1980), 121--124.
* W. van Doorn, *Sequences with bounded lcm for consecutive elements*.
-/

open scoped BigOperators NNReal Topology
open Filter Finset

namespace Erdos440SharpUpper.IncreasingSequence

noncomputable def sharpKernel (j : ℕ) : ℝ :=
  1 / (Real.sqrt j * (j + 1))

noncomputable def sharpConstant : ℝ := ∑' j : ℕ, sharpKernel j

end Erdos440SharpUpper.IncreasingSequence

namespace Erdos440

/-- The data of an infinite increasing sequence of positive integers. -/
structure IncreasingSequence where
  value : ℕ → ℕ
  positive : ∀ i, 0 < value i
  strictMono : StrictMono value

namespace IncreasingSequence

instance : CoeFun IncreasingSequence (fun _ => ℕ → ℕ) :=
  ⟨IncreasingSequence.value⟩

/-- The least common multiple attached to the edge from i to i + 1. -/
def edgeLcm (A : IncreasingSequence) (i : ℕ) : ℕ :=
  Nat.lcm (A i) (A (i + 1))

/-- The finite set of all good edges at threshold x.

The range x is exact: an edge with least common multiple at most x has
index strictly below x.
-/
def goodEdges (A : IncreasingSequence) (x : ℕ) : Finset ℕ :=
  (Finset.range x).filter fun i => edgeLcm A i ≤ x

/-- The counting function in Erdős Problem 440. -/
def count (A : IncreasingSequence) (x : ℕ) : ℕ :=
  (goodEdges A x).card

/-- The normalized counting function.  At x = 0 this is zero. -/
noncomputable def ratio (A : IncreasingSequence) (x : ℕ) : ℝ :=
  (count A x : ℝ) / Real.sqrt x

end IncreasingSequence

noncomputable abbrev sharpConstant : ℝ :=
  Erdos440SharpUpper.IncreasingSequence.sharpConstant

theorem erdos_440 :
    (∀ A : IncreasingSequence,
      (fun x : ℕ ↦ (A.count x : ℝ)) =O[atTop] (fun x : ℕ ↦ Real.sqrt x)) ∧
    (∀ A : IncreasingSequence, atTop.limsup A.ratio ≤ sharpConstant) ∧
    (∃ A : IncreasingSequence, atTop.limsup A.ratio = sharpConstant) ∧
    (∀ A : IncreasingSequence, atTop.liminf A.ratio ≤ 1) ∧
    (∃ A : IncreasingSequence, atTop.liminf A.ratio = 1) := by
  sorry

end Erdos440
