import Wikipedia.HopfProblem.PeriodFamilyCircleOrbitMappingTorusProjection
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusQuotient

/-!
# The fixed-period circle-orbit lattice is an elliptic mapping torus

Both sides retain their native quotient topology.  The homeomorphism sends
the class of `(z,r)` to the mapping-torus class of `(r,[z])`.  The native
return map is translation by `-6μ`, equivalently its positive deck
transformation adds `(6μ,1)` on the covering space.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodFamilyCircleOrbit

/-- Comparison of the two genuine quotient spaces with identical fibres. -/
def orbitMappingTorusHomeomorph (p : PeriodDomain) :
    OrbitModel p ≃ₜ MappingTorusModel p :=
  ThreefoldOverlapMappingTorus.quotientHomeomorph (orbitClass p) (mappingTorusProjection p)
    (orbitClass_isQuotientMap p) (mappingTorusProjection_isQuotientMap p)
    (fun z w => (mappingTorusProjection_eq_iff_orbitClass p z w).symm)

/-- The comparison preserves every original complex and real representative. -/
@[simp] theorem orbitMappingTorusHomeomorph_apply (p : PeriodDomain) (z : ℂ × ℝ) :
    orbitMappingTorusHomeomorph p (orbitClass p z) =
      MappingTorus.mk (returnTranslation p) (z.2, ellipticClass p z.1) :=
  ThreefoldOverlapMappingTorus.quotientHomeomorph_apply _ _ _ _ _ z

@[simp] theorem orbitMappingTorusHomeomorph_symm_apply (p : PeriodDomain) (z : ℂ × ℝ) :
    (orbitMappingTorusHomeomorph p).symm
      (MappingTorus.mk (returnTranslation p) (z.2, ellipticClass p z.1)) =
        orbitClass p z :=
  ThreefoldOverlapMappingTorus.quotientHomeomorph_symm_apply _ _ _ _ _ z

/-- The real covering coordinate descends to the original additive circle. -/
def orbitTime (p : PeriodDomain) : C(OrbitModel p, AddCircle (1 : ℝ)) :=
  (MappingTorus.base (returnTranslation p)).comp
    ⟨orbitMappingTorusHomeomorph p, (orbitMappingTorusHomeomorph p).continuous⟩

@[simp] theorem orbitTime_class (p : PeriodDomain) (z : ℂ × ℝ) :
    orbitTime p (orbitClass p z) = (z.2 : AddCircle (1 : ℝ)) := by
  simp [orbitTime]

theorem orbitTime_surjective (p : PeriodDomain) : Function.Surjective (orbitTime p) := by
  intro t
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
  exact ⟨orbitClass p (0, r), orbitTime_class p (0, r)⟩

end Wikipedia.HopfProblem.PeriodFamilyCircleOrbit
