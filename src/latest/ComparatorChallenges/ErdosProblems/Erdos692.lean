import Mathlib

namespace Erdos692

open Finset

def numDivisorsIn (x n m : ℕ) : ℕ :=
  ((Ioo n m).filter (· ∣ x)).card

def countWithOneDivisor (n m L : ℕ) : ℕ :=
  ((Icc 1 L).filter (numDivisorsIn · n m = 1)).card

noncomputable def delta1 (n m : ℕ) : ℚ :=
  countWithOneDivisor n m ((Ioo n m).lcm id) / ((Ioo n m).lcm id)
end Erdos692

attribute [local instance] Classical.propDecidable

open Finset

namespace Erdos692

theorem delta1_not_unimodal :
    delta1 3 7 < delta1 3 6 ∧ delta1 3 7 < delta1 3 8 := by
  sorry

end Erdos692
