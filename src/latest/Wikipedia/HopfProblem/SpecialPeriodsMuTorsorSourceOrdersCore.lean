import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsorBase
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientOrdersTranslated
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientLocalBiholomorph
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorSourceOrdersLocal

/-!
# The finite coordinate preserves the actual elliptic branching orders

The supplied compact sphere identification restricts to the proved finite
orbit biholomorphism. Composing this with the actual inverse elliptic
quotient chart gives a genuine local biholomorphism of complex coordinates.
Its simple centered zero preserves the computed branching order. Actual
triangle invariance then transports the order to each whole elliptic fibre.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor.SourceOrders

open Triangle

attribute [local instance] triangleOrbitChartedSpace triangleCompactifiedChartedSpace

local instance : IsManifold 𝓘(ℂ) ω TriangleOrbitSpace := triangleOrbit_isManifold

variable (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
  TriangleCompactifiedOrbitSpace RiemannSphere ω)

/-- The actual change from an elliptic quotient chart to the finite
coordinate provided by the supplied sphere map. -/
def chartToFinite (j : Elliptic.Kind) : ℂ → ℂ :=
  BetaTorsor.finiteOrbitCoordinate π ∘ (ellipticFullChart j).symm

theorem ellipticFullChart_symm_zero (j : Elliptic.Kind) :
    (ellipticFullChart j).symm 0 = ellipticOrbitCenter j := by
  simpa only [ellipticFullChart_center] using
    (ellipticFullChart j).left_inv (ellipticFullChart_center_mem_source j)

@[simp] theorem chartToFinite_zero (j : Elliptic.Kind) :
    chartToFinite π j 0 = BetaTorsor.finiteProjection π (ellipticCenter j) := by
  rw [chartToFinite, Function.comp_apply, ellipticFullChart_symm_zero]
  rfl

/-- The equality is obtained from the genuine inverse quotient chart on
an actual neighbourhood of the source point. -/
theorem finiteProjection_germ_eventuallyEq_chartToFinite (j : Elliptic.Kind) (z : ℍ)
    (hz : triangleOrbitProjection z ∈ (ellipticFullChart j).source) :
    (BetaTorsor.finiteProjection π ∘ ofComplex) =ᶠ[𝓝 (z : ℂ)]
      chartToFinite π j ∘ (ellipticFullChart j ∘ triangleOrbitProjection ∘ ofComplex) := by
  have hc : ContinuousAt (triangleOrbitProjection ∘ ofComplex) (z : ℂ) :=
    triangleOrbitProjection_continuous.continuousAt.comp
      (contMDiffAt_ofComplex (n := ω) z.im_pos).continuousAt
  have hz' : (triangleOrbitProjection ∘ ofComplex) (z : ℂ) ∈
      (ellipticFullChart j).source := by
    simpa only [Function.comp_apply, ofComplex_apply] using hz
  have hU : ∀ᶠ w in 𝓝 (z : ℂ),
      triangleOrbitProjection (ofComplex w) ∈ (ellipticFullChart j).source :=
    hc ((ellipticFullChart j).open_source.mem_nhds hz')
  filter_upwards [hU] with w hw
  exact congrArg (BetaTorsor.finiteOrbitCoordinate π)
    ((ellipticFullChart j).left_inv hw).symm

variable (hπ : π triangleCuspPoint = (∞ : RiemannSphere))

include hπ

/-- This is a genuine local biholomorphism, not a nonzero derivative
supplied as additional source data. -/
theorem chartToFinite_isLocalDiffeomorphAt_zero (j : Elliptic.Kind) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (chartToFinite π j) 0 := by
  have hzero : (0 : ℂ) ∈ (ellipticFullChart j).target := by
    simpa only [ellipticFullChart_center] using
      (ellipticFullChart j).map_source (ellipticFullChart_center_mem_source j)
  have hinv : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (ellipticFullChart j).symm 0 :=
    (triangleOrbitCoordinatePartial (.inr j)).symm.isLocalDiffeomorphAt _ _ _ hzero
  exact hinv.comp (K := 𝓘(ℂ)) (P := ℂ)
    ((BetaTorsor.finiteOrbitBiholomorph π hπ).isLocalDiffeomorph _)

theorem finiteProjection_analyticAt (z : ℍ) :
    AnalyticAt ℂ (BetaTorsor.finiteProjection π ∘ ofComplex) (z : ℂ) :=
  ((BetaTorsor.finiteProjection_holomorphic π hπ).contMDiffAt.comp (z : ℂ)
    (contMDiffAt_ofComplex z.im_pos)).contDiffAt.analyticAt

/-- Fibres of the finite coordinate are precisely the actual quotient
fibres, because the finite orbit coordinate is injective. -/
theorem finiteProjection_eq_center_iff (j : Elliptic.Kind) (z : ℍ) :
    BetaTorsor.finiteProjection π z = BetaTorsor.finiteProjection π (ellipticCenter j) ↔
      triangleOrbitProjection z = ellipticOrbitCenter j :=
  (BetaTorsor.finiteOrbitCoordinate_injective π hπ).eq_iff

theorem finiteProjection_eq_center_iff_exists_action (j : Elliptic.Kind) (z : ℍ) :
    BetaTorsor.finiteProjection π z = BetaTorsor.finiteProjection π (ellipticCenter j) ↔
      ∃ g : TriangleGroup, triangleGeometricRepresentation g (ellipticCenter j) = z :=
  (finiteProjection_eq_center_iff π hπ j z).trans
    (triangleOrbitProjection_eq_iff z (ellipticCenter j))

/-- The finite coordinate has the actual elliptic branching order at the
distinguished source centre, independently of its chosen finite value. -/
theorem finiteProjection_centered_order_center (j : Elliptic.Kind) :
    analyticOrderAt (fun w : ℂ => BetaTorsor.finiteProjection π (ofComplex w) -
      BetaTorsor.finiteProjection π (ellipticCenter j)) (ellipticCenter j : ℂ) =
        (j.order : ℕ∞) := by
  let F : ℂ → ℂ := ellipticFullChart j ∘ triangleOrbitProjection ∘ ofComplex
  have hF : AnalyticAt ℂ F (ellipticCenter j : ℂ) :=
    ellipticFullChart_complexGerm_analyticAt j
  have hF0 : F (ellipticCenter j : ℂ) = 0 := by
    simp only [F, Function.comp_apply, ofComplex_apply]
    exact ellipticFullChart_center j
  have hlocal : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (chartToFinite π j)
      (F (ellipticCenter j : ℂ)) := by
    rw [hF0]
    exact chartToFinite_isLocalDiffeomorphAt_zero π hπ j
  have horder := centered_order_comp hF hlocal
  have he : (fun w : ℂ => BetaTorsor.finiteProjection π (ofComplex w) -
      BetaTorsor.finiteProjection π (ellipticCenter j)) =ᶠ[𝓝 (ellipticCenter j : ℂ)]
      (fun w => chartToFinite π j (F w) - BetaTorsor.finiteProjection π (ellipticCenter j)) := by
    filter_upwards [finiteProjection_germ_eventuallyEq_chartToFinite π j (ellipticCenter j)
      (ellipticFullChart_center_mem_source j)] with w hw
    exact congrArg (fun a : ℂ => a - BetaTorsor.finiteProjection π (ellipticCenter j)) hw
  calc
    analyticOrderAt (fun w : ℂ => BetaTorsor.finiteProjection π (ofComplex w) -
        BetaTorsor.finiteProjection π (ellipticCenter j)) (ellipticCenter j : ℂ) =
        analyticOrderAt (fun w => chartToFinite π j (F w) -
          BetaTorsor.finiteProjection π (ellipticCenter j)) (ellipticCenter j : ℂ) :=
      analyticOrderAt_congr he
    _ = analyticOrderAt F (ellipticCenter j : ℂ) := by
      simpa only [hF0, chartToFinite_zero, sub_zero] using horder
    _ = (j.order : ℕ∞) := ellipticFullChart_order_center j

/-- The branching order holds at every point of the actual elliptic
fibre, not only at its distinguished representative. -/
theorem finiteProjection_centered_order_of_fibre (j : Elliptic.Kind) (z : ℍ)
    (hz : triangleOrbitProjection z = ellipticOrbitCenter j) :
    analyticOrderAt (fun w : ℂ => BetaTorsor.finiteProjection π (ofComplex w) -
      BetaTorsor.finiteProjection π (ellipticCenter j)) (z : ℂ) = (j.order : ℕ∞) := by
  obtain ⟨g, rfl⟩ := (triangleOrbitProjection_eq_iff z (ellipticCenter j)).mp hz
  have ht := triangle_invariant_analyticOrderAt
    (fun a : ℍ => BetaTorsor.finiteProjection π a -
      BetaTorsor.finiteProjection π (ellipticCenter j))
    (fun g a => by rw [BetaTorsor.finiteProjection_invariant]) g (ellipticCenter j)
  exact ht.trans (finiteProjection_centered_order_center π hπ j)

theorem finiteProjection_centerOne
    (h₀ : π (triangleOpenInclusion triangleOrbitCenterOne) = ((0 : ℂ) : RiemannSphere)) :
    BetaTorsor.finiteProjection π centerOne = 0 := by
  apply OnePoint.coe_injective
  exact (BetaTorsor.finiteOrbitCoordinate_coe π hπ triangleOrbitCenterOne).trans h₀

theorem finiteProjection_centerTwo
    (h₁ : π (triangleOpenInclusion triangleOrbitCenterTwo) = ((1 : ℂ) : RiemannSphere)) :
    BetaTorsor.finiteProjection π centerTwo = 1 := by
  apply OnePoint.coe_injective
  exact (BetaTorsor.finiteOrbitCoordinate_coe π hπ triangleOrbitCenterTwo).trans h₁

theorem finiteProjection_eq_zero_iff
    (h₀ : π (triangleOpenInclusion triangleOrbitCenterOne) = ((0 : ℂ) : RiemannSphere))
    (z : ℍ) : BetaTorsor.finiteProjection π z = 0 ↔
      triangleOrbitProjection z = triangleOrbitCenterOne := by
  rw [← finiteProjection_centerOne π hπ h₀]
  exact finiteProjection_eq_center_iff π hπ .three z

theorem finiteProjection_eq_one_iff
    (h₁ : π (triangleOpenInclusion triangleOrbitCenterTwo) = ((1 : ℂ) : RiemannSphere))
    (z : ℍ) : BetaTorsor.finiteProjection π z = 1 ↔
      triangleOrbitProjection z = triangleOrbitCenterTwo := by
  rw [← finiteProjection_centerTwo π hπ h₁]
  exact finiteProjection_eq_center_iff π hπ .four z

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor.SourceOrders
