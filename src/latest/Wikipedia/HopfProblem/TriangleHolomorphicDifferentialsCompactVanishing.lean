import Wikipedia.HopfProblem.SpecialPeriodsExistence
import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsorDescent
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorCompactExtension
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsCuspOrder

/-!
# Scalar vanishing on the actual compact triangle quotient

An entire function in the actual normalized source coordinate, with a zero
analytic cusp germ, vanishes by the proved compact-quotient extension theorem.
Invariant holomorphic functions upstairs descend through the actual quotient,
so a positive analytic cusp order also forces their global vanishing.
Neither statement assumes a degree calculation on the projective line.
-/

noncomputable section

open Filter Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentials

open SpecialPeriods SpecialPeriods.Triangle

attribute [local instance] triangleOrbitChartedSpace triangleCompactifiedChartedSpace

/-- The actual compact quotient forces an entire scalar coefficient with a
zero analytic cusp germ to vanish.  The compact extension is constructed by
the imported theorem, rather than supplied as a hypothesis. -/
theorem entire_eq_zero_of_eventually_cusp {F G : ℂ → ℂ}
    (hF : ∀ t, AnalyticAt ℂ F t) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (he : ∀ᶠ z in atImInfty, F (specialSourceCoordinate z) = G (cuspQ z)) :
    F = 0 := by
  let f : TriangleOrbitSpace → ℂ :=
    F ∘ BetaTorsor.finiteOrbitCoordinate triangleSphereUniformization
  have hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f := by
    intro q
    exact (hF _).contDiffAt.contMDiffAt.comp q
      (BetaTorsor.finiteOrbitCoordinate_holomorphic triangleSphereUniformization
        triangleSphereUniformization_cusp q)
  have hzero : f = 0 :=
    MuTorsor.eq_zero_of_eventually_cusp f G hf hG hG0 he
  funext t
  have ht := congrFun hzero
    (BetaTorsor.finiteOrbitInverse triangleSphereUniformization
      triangleSphereUniformization_cusp t)
  change F (BetaTorsor.finiteOrbitCoordinate triangleSphereUniformization
    (BetaTorsor.finiteOrbitInverse triangleSphereUniformization
      triangleSphereUniformization_cusp t)) = 0 at ht
  rwa [BetaTorsor.finiteOrbitCoordinate_inverse] at ht

/-- A globally invariant holomorphic scalar with positive analytic cusp
order vanishes.  Entire descent and compact extension are both proved from
the actual geometric quotient, not assumed as extra data. -/
theorem invariant_scalar_eq_zero_of_hasCuspOrder {f : ℍ → ℂ}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hInv : ∀ g : TriangleGroup, ∀ z : ℍ,
      f (triangleGeometricRepresentation g z) = f z)
    {n : ℕ} (hn : 0 < n) (hcusp : HasCuspOrder n f) : f = 0 := by
  obtain ⟨F, hF, hdesc⟩ := BetaTorsor.exists_entire_descent
    triangleSphereUniformization triangleSphereUniformization_cusp f hf hInv
  obtain ⟨G, hG, he⟩ := hcusp
  have hFzero : F = 0 := by
    apply entire_eq_zero_of_eventually_cusp hF ((analyticAt_id.pow n).mul hG)
      (by simp [hn.ne'])
    filter_upwards [he] with z hz
    exact (hdesc z).trans hz
  funext z
  exact (hdesc z).symm.trans (by rw [hFzero]; rfl)

/-- The first-order cusp vanishing case used for invariant scalar
coefficients of global holomorphic differentials. -/
theorem invariant_scalar_eq_zero_of_hasCuspOrder_one {f : ℍ → ℂ}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hInv : ∀ g : TriangleGroup, ∀ z : ℍ,
      f (triangleGeometricRepresentation g z) = f z)
    (hcusp : HasCuspOrder 1 f) : f = 0 :=
  invariant_scalar_eq_zero_of_hasCuspOrder hf hInv (by decide) hcusp

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentials
