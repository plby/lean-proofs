import Mathlib

open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal Topology Pointwise InnerProductSpace

noncomputable section


namespace Erdos1118

open scoped Classical in
def IsEntire (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f

end Erdos1118

namespace Erdos1118

open scoped Classical in
def IsNonconstantEntire (f : ℂ → ℂ) : Prop :=
  IsEntire f ∧ ∃ x y, f x ≠ f y

end Erdos1118

namespace Erdos1118

open scoped Classical in
def exceptionalSet (f : ℂ → ℂ) (c : ℝ) : Set ℂ :=
  {z | c < ‖f z‖}

end Erdos1118

namespace Erdos1118

open scoped Classical in
def HasFiniteArea (f : ℂ → ℂ) (c : ℝ) : Prop :=
  volume (exceptionalSet f c) ≠ ∞

end Erdos1118

namespace Erdos1118

open scoped Classical in
noncomputable def maximumModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z : ℂ ↦ ‖f z‖) '' Metric.sphere (0 : ℂ) r)

end Erdos1118

namespace Erdos1118

open scoped Classical in
noncomputable def growthIntegrand (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  r / Real.log (Real.log (maximumModulus f r))

end Erdos1118

namespace Erdos1118

open scoped Classical in
def GrowthIntegralConverges (f : ℂ → ℂ) : Prop :=
  ∃ R > 0,
    (∀ r, R ≤ r → 0 < Real.log (Real.log (maximumModulus f r))) ∧
    IntegrableOn (growthIntegrand f) (Set.Ioi R)

end Erdos1118

namespace Erdos1118

open scoped Classical in
def DirectGrowthTheorem : Prop :=
  ∀ (f : ℂ → ℂ) (c : ℝ),
    IsNonconstantEntire f → HasFiniteArea f c → GrowthIntegralConverges f

end Erdos1118

namespace Erdos1118

open scoped Classical in
def SharpGrowthTheorem : Prop :=
  ∀ φ : ℝ → ℝ,
    Monotone φ → (∀ r, 0 ≤ r → 0 < φ r) →
    IntegrableOn (fun r : ℝ ↦ r / φ r) (Set.Ioi 0) →
    ∃ (f : ℂ → ℂ) (c C R : ℝ),
      IsNonconstantEntire f ∧ 0 < c ∧ HasFiniteArea f c ∧ 0 < C ∧ 0 < R ∧
        ∀ r, R ≤ r →
          Real.log (Real.log (maximumModulus f r)) ≤ C * φ r

end Erdos1118

namespace Erdos1118

open scoped Classical in
def thresholdSet (f : ℂ → ℂ) : Set ℝ :=
  {c | 0 < c ∧ HasFiniteArea f c}

end Erdos1118

namespace Erdos1118

open scoped Classical in
def ClosedThresholdWitness (m : ℝ) : Prop :=
  ∃ f : ℂ → ℂ, IsNonconstantEntire f ∧ thresholdSet f = Set.Ici m

end Erdos1118

namespace Erdos1118

open scoped Classical in
def OpenThresholdWitness (m : ℝ) : Prop :=
  ∃ f : ℂ → ℂ, IsNonconstantEntire f ∧ thresholdSet f = Set.Ioi m

end Erdos1118

namespace Erdos1118

open scoped Classical in
def PrescribedThresholdTheorem : Prop :=
  ∀ m : ℝ, 0 < m → ClosedThresholdWitness m ∧ OpenThresholdWitness m

end Erdos1118

namespace Erdos1118

open scoped Classical in
def Resolution : Prop :=
  DirectGrowthTheorem ∧ SharpGrowthTheorem ∧ PrescribedThresholdTheorem

end Erdos1118

namespace Erdos1118

open scoped Classical in
theorem erdos_1118 : Resolution := by
  sorry

end Erdos1118

end
