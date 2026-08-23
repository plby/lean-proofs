/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Asymptotics
open scoped Topology

noncomputable section

namespace Erdos446

open scoped Classical in
def intervalLcm (n : ℕ) : ℕ :=
  (Finset.Ioo n (2 * n)).lcm id

end Erdos446

namespace Erdos446

open scoped Classical in
def divisorCount (n m : ℕ) : ℕ :=
  ((Finset.Ioo n (2 * n)).filter fun d ↦ d ∣ m).card

end Erdos446

namespace Erdos446

open scoped Classical in
noncomputable def delta (n : ℕ) : ℝ :=
  (((((Finset.range (intervalLcm n)).filter
    (fun m ↦ 0 < divisorCount n m)).card : ℕ) : ℝ) /
      (intervalLcm n : ℝ))

end Erdos446

namespace Erdos446

open scoped Classical in
noncomputable def alpha446 : ℝ :=
  1 - (1 + Real.log (Real.log 2)) / Real.log 2

end Erdos446

namespace Erdos446

open scoped Classical in
noncomputable def growthDenominator446 (n : ℕ) : ℝ :=
  Real.log (n : ℝ) ^ alpha446 *
    Real.log (Real.log (n : ℝ)) ^ (3 / 2 : ℝ)

end Erdos446

namespace Erdos446

open scoped Classical in
noncomputable def growth446 (n : ℕ) : ℝ :=
  (growthDenominator446 n)⁻¹

end Erdos446

namespace Erdos446

open scoped Classical in
def GrowthResolution446 : Prop :=
  delta =Θ[atTop] growth446

end Erdos446

namespace Erdos446

open scoped Classical in
noncomputable def deltaR (r n : ℕ) : ℝ :=
  (((((Finset.range (intervalLcm n)).filter
    (fun m ↦ divisorCount n m = r)).card : ℕ) : ℝ) /
      (intervalLcm n : ℝ))

end Erdos446

namespace Erdos446

open scoped Classical in
def FixedMultiplicityResolution446 : Prop :=
  ∀ r : ℕ, 1 ≤ r → delta =O[atTop] (deltaR r)

end Erdos446

namespace Erdos446

open scoped Classical in
def Resolution446 : Prop :=
  GrowthResolution446 ∧
    FixedMultiplicityResolution446 ∧
      ¬ (deltaR 1 =o[atTop] delta)

end Erdos446

namespace Erdos446

open scoped Classical in
theorem erdos_446 : Resolution446 := by
  sorry

end Erdos446

end
