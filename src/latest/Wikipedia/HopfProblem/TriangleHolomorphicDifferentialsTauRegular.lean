import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsGeometry
import Wikipedia.HopfProblem.SpecialPeriodsUniquenessTau
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorSourceOrdersLocal
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientLocalBiholomorph
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientDensity

/-!
# Nonvanishing of the actual first-period derivative on the regular locus

The actual source coordinate is a local biholomorphism at every regular
upper-half-plane point. Differentiating the proved identity between the
modular invariant of the actual first period and the actual source
coordinate forces the first-period derivative to be nonzero there.
No nonvanishing hypothesis on the derivative of the modular invariant
is used.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentials

open SpecialPeriods SpecialPeriods.Triangle

attribute [local instance] triangleOrbitChartedSpace triangleCompactifiedChartedSpace

local instance : IsManifold 𝓘(ℂ) ω TriangleOrbitSpace := triangleOrbit_isManifold

private theorem ofComplex_isLocalDiffeomorphAt (z : ℍ) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω ofComplex (z : ℂ) := by
  let Φ : PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ℂ ℍ ω :=
    { toPartialEquiv := ofComplex.toPartialEquiv
      open_source := ofComplex.open_source
      open_target := ofComplex.open_target
      contMDiffOn_toFun := by
        intro w hw
        have he : ((ofComplex w : ℍ) : ℂ) = w := ofComplex.left_inv hw
        have hwim : 0 < w.im := by
          rw [← he]
          exact (ofComplex w).im_pos
        exact (contMDiffAt_ofComplex hwim).contMDiffWithinAt
      contMDiffOn_invFun := contMDiff_coe.contMDiffOn }
  refine ⟨Φ, ?_, fun _ _ => rfl⟩
  exact ofComplex.symm.map_source (mem_univ z)

/-- An actual local biholomorphism has nonzero derivative in the literal
upper-half-plane coordinate. -/
theorem scalarDeriv_ne_zero_of_isLocalDiffeomorphAt {f : ℍ → ℂ} {z : ℍ}
    (hf : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω f z) : scalarDeriv f z ≠ 0 := by
  apply MuTorsor.SourceOrders.deriv_ne_zero_of_isLocalDiffeomorph
  have hf' : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω f (ofComplex (z : ℂ)) := by
    simpa only [ofComplex_apply] using hf
  exact (ofComplex_isLocalDiffeomorphAt z).comp (K := 𝓘(ℂ)) (P := ℂ) hf'

theorem specialSourceCoordinate_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω specialSourceCoordinate :=
  BetaTorsor.finiteProjection_holomorphic triangleSphereUniformization
    triangleSphereUniformization_cusp

/-- The actual finite uniformizing coordinate is locally biholomorphic
at every point where the orbit projection has trivial stabilizer. -/
theorem specialSourceCoordinate_isLocalDiffeomorphAt_of_regular {z : ℍ}
    (hz : z ∈ triangleRegularLocus) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω specialSourceCoordinate z :=
  (triangleOrbitProjection_isLocalDiffeomorphAt_of_regular hz).comp (K := 𝓘(ℂ)) (P := ℂ)
    ((BetaTorsor.finiteOrbitBiholomorph triangleSphereUniformization
      triangleSphereUniformization_cusp).isLocalDiffeomorph _)

theorem specialSourceCoordinate_scalarDeriv_ne_zero_of_regular {z : ℍ}
    (hz : z ∈ triangleRegularLocus) : scalarDeriv specialSourceCoordinate z ≠ 0 :=
  scalarDeriv_ne_zero_of_isLocalDiffeomorphAt
    (specialSourceCoordinate_isLocalDiffeomorphAt_of_regular hz)

/-- The differentiated identity for the actual modular invariant and periods. -/
theorem specialTau_scalarDeriv_modular (z : ℍ) :
    scalarDeriv modularJ (specialTauHalfPlane z) * scalarDeriv specialTau z =
      1728 * scalarDeriv specialSourceCoordinate z := by
  have hc := scalarDeriv_comp modularJ_holomorphic specialTauHalfPlane_holomorphic z
  have ht : (fun w : ℍ => (specialTauHalfPlane w : ℂ)) = specialTau :=
    funext specialTauHalfPlane_coe
  have hJ : modularJ ∘ specialTauHalfPlane =
      fun w : ℍ => 1728 * specialSourceCoordinate w :=
    funext specialTauHalfPlane_modular
  have hp : scalarDeriv (fun w : ℍ => 1728 * specialSourceCoordinate w) z =
      1728 * scalarDeriv specialSourceCoordinate z :=
    ((scalarHasDerivAt specialSourceCoordinate_holomorphic z).const_mul 1728).deriv
  rw [ht, hJ, hp] at hc
  exact hc.symm

/-- The actual first-period derivative cannot vanish over any regular base point. -/
theorem specialTau_scalarDeriv_ne_zero_of_regular {z : ℍ}
    (hz : z ∈ triangleRegularLocus) : scalarDeriv specialTau z ≠ 0 := by
  intro hzero
  have h := specialTau_scalarDeriv_modular z
  rw [hzero, mul_zero] at h
  exact (mul_ne_zero (by norm_num : (1728 : ℂ) ≠ 0)
    (specialSourceCoordinate_scalarDeriv_ne_zero_of_regular hz)) h.symm

theorem specialTau_scalarDeriv_ne_zero (z : TriangleRegularPoint) :
    scalarDeriv specialTau z.val ≠ 0 := specialTau_scalarDeriv_ne_zero_of_regular z.property

/-- Nonvanishing holds on a proved dense subset, not a supplied generic locus. -/
theorem specialTau_scalarDeriv_nonzero_dense :
    Dense {z : ℍ | scalarDeriv specialTau z ≠ 0} :=
  triangleRegularLocus_dense.mono fun _ hz => specialTau_scalarDeriv_ne_zero_of_regular hz

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentials
