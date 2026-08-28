import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspRegularCoefficients

/-!
# Lemma 9.16(ii): cusp orders of genuine global holomorphic-form coefficients

The native regular-cover coefficients have the actual analytic vanishing
extensions constructed in the preceding file. Any scalar function on the
upper half-plane agreeing with one of these native coefficients therefore
has first analytic cusp order. The agreement premise only identifies a
chosen extension of the coefficient outside its original regular domain;
no cusp extension, factorization, growth, or vanishing is assumed.
-/

noncomputable section

open UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp

open Triangle HolomorphicDifferentialForms TriangleHolomorphicDifferentials

local notation "EL" => ℂ × ComplexPlane₂

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- The horizontal coefficient of any genuine global one-form has first cusp order. -/
theorem baseOne_hasCuspOrder_of_agree_regular (θ : Form EL Threefold.Space 1)
    (f : ℍ → ℂ) (hagree : ∀ z : TriangleRegularPoint, f (z : ℍ) = RegularCover.baseOne θ z) :
    HasCuspOrder 1 f := by
  apply hasCuspOrder_one_of_scaled_log_coordinate
    (Complex.ofReal_ne_zero.mpr width_ne_zero)
    (baseOneCuspCoefficient_analyticAt_zero θ) (baseOneCuspCoefficient_zero θ)
  intro s
  rw [hagree (cuspRegularBase s)]
  exact baseOne_cusp_expansion θ s

/-- Each original fibre coefficient of any genuine global one-form has first cusp order. -/
theorem fibreOne_hasCuspOrder_of_agree_regular (θ : Form EL Threefold.Space 1)
    (i : Fin 2) (f : ℍ → ℂ)
    (hagree : ∀ z : TriangleRegularPoint, f (z : ℍ) = RegularCover.fibreOne θ z i) :
    HasCuspOrder 1 f := by
  apply hasCuspOrder_one_of_log_coordinate
    (fibreOneCuspCoefficient_analyticAt_zero θ i) (fibreOneCuspCoefficient_zero θ i)
  intro s
  rw [hagree (cuspRegularBase s)]
  exact fibreOne_cusp_expansion θ s i

/-- Each original mixed two-form coefficient has first cusp order,
with the width removed exactly. -/
theorem mixedTwo_hasCuspOrder_of_agree_regular (θ : Form EL Threefold.Space 2)
    (i : Fin 2) (f : ℍ → ℂ)
    (hagree : ∀ z : TriangleRegularPoint, f (z : ℍ) = RegularCover.mixedTwo θ z i) :
    HasCuspOrder 1 f := by
  apply hasCuspOrder_one_of_scaled_log_coordinate
    (Complex.ofReal_ne_zero.mpr width_ne_zero)
    (mixedTwoCuspCoefficient_analyticAt_zero θ i) (mixedTwoCuspCoefficient_zero θ i)
  intro s
  rw [hagree (cuspRegularBase s)]
  exact mixedTwo_cusp_expansion θ s i

/-- The original top-form coefficient has the source's first analytic cusp order. -/
theorem top_hasCuspOrder_of_agree_regular (θ : Form EL Threefold.Space 3)
    (f : ℍ → ℂ) (hagree : ∀ z : TriangleRegularPoint, f (z : ℍ) = RegularCover.baseTop θ z) :
    HasCuspOrder 1 f := by
  apply hasCuspOrder_one_of_scaled_log_coordinate
    (Complex.ofReal_ne_zero.mpr width_ne_zero)
    (topCuspCoefficient_analyticAt_zero θ) (topCuspCoefficient_zero θ)
  intro s
  rw [hagree (cuspRegularBase s)]
  exact top_cusp_expansion θ s

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp
