import Util.MaynardTao.BFT.Parameters

/-!
# Elementary parameters for the product sieve

The class packages only explicit real inequalities.  `parametersOfLength`
constructs it for every positive requested length, with decay proportional
to that length; it does not assume any prime-distribution conclusion.
-/

namespace MaynardBFT.Sieve

class Parameters where
  k : ℕ
  a : ℝ
  two_le_k : 2 ≤ k
  large_a : 1024 ≤ a
  upper_log : Real.log (1 + a * k) < 3 * a / 8
  lower_log : a / 3 < Real.log (1 + a * k * (1 / 8 : ℝ))

@[instance_reducible]
noncomputable def parametersOfLength (s : ℕ) (hs : 0 < s) : Parameters where
  k := dimension s
  a := decay s
  two_le_k := dimension_ge_two hs
  large_a := decay_ge_1024 hs
  upper_log := log_one_add_decay_dimension_lt hs
  lower_log := log_short_fiber_gt hs

end MaynardBFT.Sieve
