/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Finset

namespace Erdos692

def numDivisorsIn (x n m : ℕ) : ℕ :=
  ((Ioo n m).filter (· ∣ x)).card

def countWithOneDivisor (n m L : ℕ) : ℕ :=
  ((Icc 1 L).filter (numDivisorsIn · n m = 1)).card

noncomputable def delta1 (n m : ℕ) : ℚ :=
  countWithOneDivisor n m ((Ioo n m).lcm id) / ((Ioo n m).lcm id)

theorem not_erdos_692 :
    delta1 3 7 < delta1 3 6 ∧ delta1 3 7 < delta1 3 8 := by
  sorry

end Erdos692
