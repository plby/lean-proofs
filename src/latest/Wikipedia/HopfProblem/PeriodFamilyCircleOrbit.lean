import Wikipedia.HopfProblem.PeriodFamilyCircleOrbitHomeomorph
import Wikipedia.HopfProblem.PeriodFamilyCircleOrbitMappingTorus

/-!
# The original regular-fibre circle quotient is the marked elliptic mapping torus

For every actual admissible period point, quotienting the original complex
two-torus by its original delta circle gives the mapping torus of translation
by `-6μ` on `ℂ / (ℤτ + ℤ)`.  With the repository's mapping-torus convention,
its positive deck translation is exactly `(z,r) ↦ (z+6μ,r+1)`.

The comparison retains the original complex covering representatives, the
literal real-linear transverse coordinate, and the first real-period circle.
It does not identify the family over the regular base with a product, remove
its monodromy, or extend that circle coordinate across the cusp filling.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodFamilyCircleOrbit

/-- The native delta-orbit quotient of an original period torus, with its
explicit elliptic mapping-torus model and unchanged quotient topology. -/
def circleMappingTorusHomeomorph (p : PeriodDomain) : CircleOrbit p ≃ₜ MappingTorusModel p :=
  (orbitModelHomeomorph p).trans (orbitMappingTorusHomeomorph p)

/-- The map on the original complex covering vectors, including its exact real coordinate. -/
@[simp] theorem circleMappingTorusHomeomorph_mkQ (p : PeriodDomain) (z : ComplexPlane₂) :
    circleMappingTorusHomeomorph p (circleOrbitProjection p (p.lattice.mkQ z)) =
      MappingTorus.mk (returnTranslation p)
        (((z 1).im - (p.val.μ.im / p.val.τ.im) * (z 0).im) / p.val.discriminant,
          ellipticClass p (z 0)) := by
  rw [circleMappingTorusHomeomorph, Homeomorph.trans_apply, orbitModelHomeomorph_mkQ,
    orbitMappingTorusHomeomorph_apply]
  rfl

/-- The first three actual real-period coefficients remain visible in the model. -/
theorem circleMappingTorusHomeomorph_flatProjection (p : PeriodDomain)
    (x : Elliptic.RealCoordinates) :
    circleMappingTorusHomeomorph p (circleOrbitProjection p (Elliptic.flatProjection p x)) =
      MappingTorus.mk (returnTranslation p)
        (x 0, ellipticClass p
          (6 * p.val.μ * (x 0 : ℂ) + p.val.τ * (x 1 : ℂ) + (x 2 : ℂ))) := by
  change orbitMappingTorusHomeomorph p
    (orbitModelHomeomorph p
      (circleOrbitProjection p (p.lattice.mkQ (Elliptic.periodEquiv p x)))) = _
  rw [orbitModelHomeomorph_mkQ, linearProjection_periodEquiv,
    orbitMappingTorusHomeomorph_apply, projectedPeriods_apply]
  rfl

/-- Mapping-torus time is the original first real-period circle, not a new coordinate. -/
theorem circleMappingTorusHomeomorph_base (p : PeriodDomain) (x : Elliptic.RealCoordinates) :
    MappingTorus.base (returnTranslation p)
      (circleMappingTorusHomeomorph p
        (circleOrbitProjection p (Elliptic.flatProjection p x))) =
      (x 0 : AddCircle (1 : ℝ)) := by
  rw [circleMappingTorusHomeomorph_flatProjection, MappingTorus.base_mk]

end Wikipedia.HopfProblem.PeriodFamilyCircleOrbit
