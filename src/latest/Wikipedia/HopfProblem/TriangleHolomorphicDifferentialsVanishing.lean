import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsExtensions
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsWeights
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsCuspCoordinates
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsCompactVanishing
import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspRegular

/-!
# Scalar vanishing for the actual triangle action

These are the coefficient forms of the source's weight-zero and
weight-one vanishing lemmas. Actual regular descent, actual elliptic
removability, and the actual cusp-coordinate formulas construct entire
coefficients with zero analytic cusp germ. Compactness of the proved
triangle compactification then forces them to vanish. The weight-one
case uses the actual first-period derivative, not an assumed
nonvanishing auxiliary differential.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentials

open SpecialPeriods SpecialPeriods.Triangle

/-- The source's actual high horodiscs avoid the two elliptic fibres. -/
theorem eventually_regular_at_cusp :
    ∀ᶠ z in atImInfty, z ∈ triangleRegularLocus := by
  apply (atImInfty_mem triangleRegularLocus).mpr
  refine ⟨width + 1, fun z hz => ?_⟩
  apply horodisc_subset_triangleRegularLocus width le_rfl
  change width < z.im
  linarith

/-- The genuine entire coefficient constructed from an invariant
one-form is zero when the source cusp coefficient has first order. -/
theorem oneFormExtension_eq_zero {A : ℍ → ℂ}
    (hA : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω A) (hInv : IsInvariantDifferential 1 A)
    (hcusp : HasCuspOrder 1 A) : oneFormExtension A = 0 := by
  obtain ⟨G, hG, hG0, he⟩ := exists_cusp_germ_div_specialSource_deriv hcusp
  apply entire_eq_zero_of_eventually_cusp (oneFormExtension_entire hInv hA) hG hG0
  filter_upwards [he, eventually_regular_at_cusp] with z hz hreg
  exact (oneFormExtension_projection hInv hreg).trans hz

/-- Source Lemma 9.18: an invariant holomorphic one-form coefficient
with actual first-order cusp decay vanishes on the whole upper half-plane. -/
theorem invariant_oneForm_eq_zero {A : ℍ → ℂ}
    (hA : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω A) (hInv : IsInvariantDifferential 1 A)
    (hcusp : HasCuspOrder 1 A) : A = 0 := by
  have hzero := oneFormExtension_eq_zero hA hInv hcusp
  apply eq_zero_of_regular hA.continuous
  intro z hz
  have he := oneFormExtension_projection hInv hz
  rw [hzero] at he
  have hdiv : A z / scalarDeriv specialSourceCoordinate z = 0 := he.symm
  exact (div_eq_zero_iff.mp hdiv).resolve_right
    (specialSourceCoordinate_scalarDeriv_ne_zero_of_regular hz)

/-- The same statement with the literal first-derivative pullback law. -/
theorem invariant_oneForm_eq_zero_of_pullback {A : ℍ → ℂ}
    (hA : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω A)
    (hInv : ∀ (g : TriangleGroup) (z : ℍ),
      A (triangleGeometricRepresentation g z) * actionDerivative g z = A z)
    (hcusp : HasCuspOrder 1 A) : A = 0 :=
  invariant_oneForm_eq_zero hA (by simpa only [IsInvariantDifferential, pow_one] using hInv) hcusp

/-- Clearing the two finite double poles gives the actual entire cubic
coefficient. Its proved analytic cusp germ has zero value. -/
theorem clearedCubicExtension_eq_zero {C : ℍ → ℂ}
    (hC : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω C) (hInv : IsInvariantDifferential 3 C)
    (hcusp : HasCuspOrder 2 C) : clearedCubicExtension C = 0 := by
  obtain ⟨G, hG, hG0, he⟩ := exists_cusp_germ_cleared_specialSource_cube hcusp
  apply entire_eq_zero_of_eventually_cusp (clearedCubicExtension_entire hInv hC) hG hG0
  filter_upwards [he, eventually_regular_at_cusp] with z hz hreg
  exact (clearedCubicExtension_projection hInv hreg).trans hz

/-- The invariant cubic used in Lemma 9.19 vanishes. The proof constructs
and annihilates its cleared scalar coefficient, with no line-bundle
degree or cohomology premise. -/
theorem invariant_cubic_eq_zero {C : ℍ → ℂ}
    (hC : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω C) (hInv : IsInvariantDifferential 3 C)
    (hcusp : HasCuspOrder 2 C) : C = 0 := by
  have hzero := clearedCubicExtension_eq_zero hC hInv hcusp
  apply eq_zero_of_regular hC.continuous
  intro z hz
  have he := clearedCubicExtension_projection hInv hz
  rw [hzero] at he
  have hdiv : specialSourceCoordinate z ^ 2 * (specialSourceCoordinate z - 1) ^ 2 * C z /
      scalarDeriv specialSourceCoordinate z ^ 3 = 0 := he.symm
  have hnum : specialSourceCoordinate z ^ 2 * (specialSourceCoordinate z - 1) ^ 2 * C z = 0 :=
    (div_eq_zero_iff.mp hdiv).resolve_right
      (pow_ne_zero 3 (specialSourceCoordinate_scalarDeriv_ne_zero_of_regular hz))
  obtain ⟨hz0, hz1⟩ := (specialSourceCoordinate_regular_iff z).mp hz
  exact (mul_eq_zero.mp hnum).resolve_left
    (mul_ne_zero (pow_ne_zero 2 hz0) (pow_ne_zero 2 (sub_ne_zero.mpr hz1)))

/-- Source Lemma 9.19: the source weight-one holomorphic one-form
coefficient with actual first-order cusp decay vanishes. -/
theorem weight_oneForm_eq_zero {B : ℍ → ℂ}
    (hB : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω B) (hInv : IsWeightOneDifferential B)
    (hcusp : HasCuspOrder 1 B) : B = 0 :=
  weightOne_eq_zero_of_cubic_eq_zero hB.continuous
    (invariant_cubic_eq_zero (weightOneCubic_holomorphic hB)
      (weightOneCubic_invariant hInv) (weightOneCubic_hasCuspOrder hcusp))

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentials
