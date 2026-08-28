import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorSourceOrdersCore

/-!
# Source orders forced by the normalized actual quotient map

For a supplied sphere identification taking the two elliptic quotient
points to zero and one, every zero of the finite projection has order
three and every zero of its difference from one has order four. Scaling
by 1728 yields the exact source orders required for the modular lifting
construction. None of these orders is an independent assumption.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor.SourceOrders

open Triangle

attribute [local instance] triangleCompactifiedChartedSpace

variable (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
  TriangleCompactifiedOrbitSpace RiemannSphere ω)

/-- The actual finite projection in the conventional modular normalization. -/
def sourceJ (z : ℍ) : ℂ := 1728 * BetaTorsor.finiteProjection π z

theorem sourceJ_invariant (g : TriangleGroup) (z : ℍ) :
    sourceJ π (triangleGeometricRepresentation g z) = sourceJ π z := by
  simp only [sourceJ, BetaTorsor.finiteProjection_invariant]

theorem sourceJ_eq_zero_iff_finiteProjection (z : ℍ) :
    sourceJ π z = 0 ↔ BetaTorsor.finiteProjection π z = 0 := by
  simp only [sourceJ, mul_eq_zero, show (1728 : ℂ) ≠ 0 by norm_num, false_or]

theorem sourceJ_eq_1728_iff_finiteProjection (z : ℍ) :
    sourceJ π z = 1728 ↔ BetaTorsor.finiteProjection π z = 1 := by
  constructor
  · intro h
    exact mul_left_cancel₀ (by norm_num : (1728 : ℂ) ≠ 0)
      (h.trans (mul_one (1728 : ℂ)).symm)
  · intro h
    simp only [sourceJ, h, mul_one]

variable (hπ : π triangleCuspPoint = (∞ : RiemannSphere))

include hπ

theorem sourceJ_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (sourceJ π) :=
  contMDiff_const.mul (BetaTorsor.finiteProjection_holomorphic π hπ)

theorem sourceJ_analyticAt (z : ℍ) :
    AnalyticAt ℂ (sourceJ π ∘ ofComplex) (z : ℂ) :=
  analyticAt_const.mul (finiteProjection_analyticAt π hπ z)

/-- The order-three source condition is proved at every point lying over
the normalized first elliptic value. -/
theorem finiteProjection_order_of_eq_zero
    (h₀ : π (triangleOpenInclusion triangleOrbitCenterOne) = ((0 : ℂ) : RiemannSphere))
    (z : ℍ) (hz : BetaTorsor.finiteProjection π z = 0) :
    analyticOrderAt (BetaTorsor.finiteProjection π ∘ ofComplex) (z : ℂ) = 3 := by
  have h := finiteProjection_centered_order_of_fibre π hπ .three z
    ((finiteProjection_eq_zero_iff π hπ h₀ z).mp hz)
  change analyticOrderAt (fun w : ℂ => BetaTorsor.finiteProjection π (ofComplex w) -
    BetaTorsor.finiteProjection π centerOne) (z : ℂ) = 3 at h
  simpa only [finiteProjection_centerOne π hπ h₀, sub_zero, Function.comp_def] using h

/-- The order-four source condition is proved throughout the entire fibre
over the normalized second elliptic value. -/
theorem finiteProjection_sub_one_order_of_eq_one
    (h₁ : π (triangleOpenInclusion triangleOrbitCenterTwo) = ((1 : ℂ) : RiemannSphere))
    (z : ℍ) (hz : BetaTorsor.finiteProjection π z = 1) :
    analyticOrderAt (fun w : ℂ => BetaTorsor.finiteProjection π (ofComplex w) - 1)
      (z : ℂ) = 4 := by
  have h := finiteProjection_centered_order_of_fibre π hπ .four z
    ((finiteProjection_eq_one_iff π hπ h₁ z).mp hz)
  change analyticOrderAt (fun w : ℂ => BetaTorsor.finiteProjection π (ofComplex w) -
    BetaTorsor.finiteProjection π centerTwo) (z : ℂ) = 4 at h
  simpa only [finiteProjection_centerTwo π hπ h₁] using h

theorem finiteProjection_order_centerOne
    (h₀ : π (triangleOpenInclusion triangleOrbitCenterOne) = ((0 : ℂ) : RiemannSphere)) :
    analyticOrderAt (BetaTorsor.finiteProjection π ∘ ofComplex) (centerOne : ℂ) = 3 :=
  finiteProjection_order_of_eq_zero π hπ h₀ centerOne (finiteProjection_centerOne π hπ h₀)

theorem finiteProjection_sub_one_order_centerTwo
    (h₁ : π (triangleOpenInclusion triangleOrbitCenterTwo) = ((1 : ℂ) : RiemannSphere)) :
    analyticOrderAt (fun w : ℂ => BetaTorsor.finiteProjection π (ofComplex w) - 1)
      (centerTwo : ℂ) = 4 :=
  finiteProjection_sub_one_order_of_eq_one π hπ h₁ centerTwo
    (finiteProjection_centerTwo π hπ h₁)

theorem sourceJ_centerOne
    (h₀ : π (triangleOpenInclusion triangleOrbitCenterOne) = ((0 : ℂ) : RiemannSphere)) :
    sourceJ π centerOne = 0 := by
  simp only [sourceJ, finiteProjection_centerOne π hπ h₀, mul_zero]

theorem sourceJ_centerTwo
    (h₁ : π (triangleOpenInclusion triangleOrbitCenterTwo) = ((1 : ℂ) : RiemannSphere)) :
    sourceJ π centerTwo = 1728 := by
  simp only [sourceJ, finiteProjection_centerTwo π hπ h₁, mul_one]

theorem sourceJ_eq_zero_iff
    (h₀ : π (triangleOpenInclusion triangleOrbitCenterOne) = ((0 : ℂ) : RiemannSphere))
    (z : ℍ) : sourceJ π z = 0 ↔ triangleOrbitProjection z = triangleOrbitCenterOne :=
  (sourceJ_eq_zero_iff_finiteProjection π z).trans (finiteProjection_eq_zero_iff π hπ h₀ z)

theorem sourceJ_eq_1728_iff
    (h₁ : π (triangleOpenInclusion triangleOrbitCenterTwo) = ((1 : ℂ) : RiemannSphere))
    (z : ℍ) : sourceJ π z = 1728 ↔ triangleOrbitProjection z = triangleOrbitCenterTwo :=
  (sourceJ_eq_1728_iff_finiteProjection π z).trans (finiteProjection_eq_one_iff π hπ h₁ z)

/-- Multiplication by the nonzero normalization constant leaves the actual
order-three branching unchanged. -/
theorem sourceJ_order_of_eq_zero
    (h₀ : π (triangleOpenInclusion triangleOrbitCenterOne) = ((0 : ℂ) : RiemannSphere))
    (z : ℍ) (hz : sourceJ π z = 0) :
    analyticOrderAt (sourceJ π ∘ ofComplex) (z : ℂ) = 3 := by
  have hc : AnalyticAt ℂ (fun _ : ℂ => (1728 : ℂ)) (z : ℂ) := analyticAt_const
  have hco : analyticOrderAt (fun _ : ℂ => (1728 : ℂ)) (z : ℂ) = 0 :=
    hc.analyticOrderAt_eq_zero.mpr (by norm_num)
  change analyticOrderAt
    ((fun _ : ℂ => (1728 : ℂ)) * (BetaTorsor.finiteProjection π ∘ ofComplex)) (z : ℂ) = 3
  rw [analyticOrderAt_mul hc (finiteProjection_analyticAt π hπ z), hco, zero_add]
  exact finiteProjection_order_of_eq_zero π hπ h₀ z
    ((sourceJ_eq_zero_iff_finiteProjection π z).mp hz)

/-- The second normalized modular source has exact order four at every
point over 1728. -/
theorem sourceJ_sub_1728_order_of_eq
    (h₁ : π (triangleOpenInclusion triangleOrbitCenterTwo) = ((1 : ℂ) : RiemannSphere))
    (z : ℍ) (hz : sourceJ π z = 1728) :
    analyticOrderAt (fun w : ℂ => sourceJ π (ofComplex w) - 1728) (z : ℂ) = 4 := by
  have hc : AnalyticAt ℂ (fun _ : ℂ => (1728 : ℂ)) (z : ℂ) := analyticAt_const
  have hco : analyticOrderAt (fun _ : ℂ => (1728 : ℂ)) (z : ℂ) = 0 :=
    hc.analyticOrderAt_eq_zero.mpr (by norm_num)
  have hp : AnalyticAt ℂ
      (fun w : ℂ => BetaTorsor.finiteProjection π (ofComplex w) - 1) (z : ℂ) :=
    (finiteProjection_analyticAt π hπ z).sub analyticAt_const
  have he : (fun w : ℂ => sourceJ π (ofComplex w) - 1728) =
      (fun _ : ℂ => (1728 : ℂ)) *
        (fun w : ℂ => BetaTorsor.finiteProjection π (ofComplex w) - 1) := by
    funext w
    simp only [sourceJ, Pi.mul_apply]
    ring
  rw [he, analyticOrderAt_mul hc hp, hco, zero_add]
  exact finiteProjection_sub_one_order_of_eq_one π hπ h₁ z
    ((sourceJ_eq_1728_iff_finiteProjection π z).mp hz)

theorem sourceJ_order_centerOne
    (h₀ : π (triangleOpenInclusion triangleOrbitCenterOne) = ((0 : ℂ) : RiemannSphere)) :
    analyticOrderAt (sourceJ π ∘ ofComplex) (centerOne : ℂ) = 3 :=
  sourceJ_order_of_eq_zero π hπ h₀ centerOne (sourceJ_centerOne π hπ h₀)

theorem sourceJ_sub_1728_order_centerTwo
    (h₁ : π (triangleOpenInclusion triangleOrbitCenterTwo) = ((1 : ℂ) : RiemannSphere)) :
    analyticOrderAt (fun w : ℂ => sourceJ π (ofComplex w) - 1728) (centerTwo : ℂ) = 4 :=
  sourceJ_sub_1728_order_of_eq π hπ h₁ centerTwo (sourceJ_centerTwo π hπ h₁)

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor.SourceOrders
