import Mathlib

open Filter Set Finset Function
open scoped Topology Polynomial
open scoped ArithmeticFunction.Moebius

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos977

noncomputable def greatestPrimeFactor (m : ℕ) : ℕ :=
  if h : m.primeFactors.Nonempty then m.primeFactors.max' h else 1

end Erdos977

namespace Erdos977

def mersenne (n : ℕ) : ℕ := 2 ^ n - 1

end Erdos977

namespace Erdos977

def Erdos977Statement : Prop :=
  Tendsto
    (fun n : ℕ => (greatestPrimeFactor (mersenne n) : ℝ) / (n : ℝ))
    atTop atTop

end Erdos977

namespace Erdos977

theorem erdos_977 : Erdos977Statement := by
  sorry

end Erdos977

end
