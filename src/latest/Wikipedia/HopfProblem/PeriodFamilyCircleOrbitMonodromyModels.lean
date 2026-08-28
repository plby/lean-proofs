import Wikipedia.HopfProblem.PeriodFamilyCircleOrbitMonodromyGenerators
import Wikipedia.HopfProblem.PeriodFamilyCircleOrbitMonodromyLinearBasic

/-!
# Exact period changes in the marked circle-orbit models

The homeomorphisms here come from the original period-change
biholomorphisms.  On the projected covering vectors their formulas are
`(z,r) ↦ (-z/τ,r)`, `(z,r) ↦ (z/τ,r)`, and `(z,r) ↦ (z,r)`.
The mapping-torus formulas retain the varying elliptic period lattices
and the original first real-period circle.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodFamilyCircleOrbit

@[simp] theorem step₁OrbitHomeomorph_class (p : PeriodDomain) (y : ℂ × ℝ) :
    step₁OrbitHomeomorph p (orbitClass p y) =
      orbitClass p.step₁ (step₁Projection p y) := by
  obtain ⟨z, rfl⟩ := linearProjection_surjective p y
  change step₁OrbitHomeomorph p (torusProjection p (p.lattice.mkQ z)) = _
  rw [step₁OrbitHomeomorph_projection, p.step₁Biholomorph_mkQ,
    torusProjection_mkQ, linearProjection_step₁]

@[simp] theorem step₂OrbitHomeomorph_class (p : PeriodDomain) (y : ℂ × ℝ) :
    step₂OrbitHomeomorph p (orbitClass p y) =
      orbitClass p.step₂ (step₂Projection p y) := by
  obtain ⟨z, rfl⟩ := linearProjection_surjective p y
  change step₂OrbitHomeomorph p (torusProjection p (p.lattice.mkQ z)) = _
  rw [step₂OrbitHomeomorph_projection, p.step₂Biholomorph_mkQ,
    torusProjection_mkQ, linearProjection_step₂]

@[simp] theorem step₀OrbitHomeomorph_class (p : PeriodDomain) (y : ℂ × ℝ) :
    step₀OrbitHomeomorph p (orbitClass p y) =
      orbitClass p.step₀ (step₀Projection p y) := by
  obtain ⟨z, rfl⟩ := linearProjection_surjective p y
  change step₀OrbitHomeomorph p (torusProjection p (p.lattice.mkQ z)) = _
  rw [step₀OrbitHomeomorph_projection, p.step₀Biholomorph_mkQ,
    torusProjection_mkQ, linearProjection_step₀]

theorem step₁OrbitHomeomorph_time (p : PeriodDomain) (x : OrbitModel p) :
    orbitTime p.step₁ (step₁OrbitHomeomorph p x) = orbitTime p x := by
  obtain ⟨y, rfl⟩ := orbitClass_surjective p x
  rw [step₁OrbitHomeomorph_class, orbitTime_class, orbitTime_class, step₁Projection_apply]

theorem step₂OrbitHomeomorph_time (p : PeriodDomain) (x : OrbitModel p) :
    orbitTime p.step₂ (step₂OrbitHomeomorph p x) = orbitTime p x := by
  obtain ⟨y, rfl⟩ := orbitClass_surjective p x
  rw [step₂OrbitHomeomorph_class, orbitTime_class, orbitTime_class, step₂Projection_apply]

theorem step₀OrbitHomeomorph_time (p : PeriodDomain) (x : OrbitModel p) :
    orbitTime p.step₀ (step₀OrbitHomeomorph p x) = orbitTime p x := by
  obtain ⟨y, rfl⟩ := orbitClass_surjective p x
  rw [step₀OrbitHomeomorph_class, orbitTime_class, orbitTime_class, step₀Projection_apply]

/-- The first original period change in the actual elliptic mapping-torus models. -/
def step₁MappingTorusHomeomorph (p : PeriodDomain) :
    MappingTorusModel p ≃ₜ MappingTorusModel p.step₁ :=
  ((orbitMappingTorusHomeomorph p).symm.trans (step₁OrbitHomeomorph p)).trans
    (orbitMappingTorusHomeomorph p.step₁)

/-- The second original period change in the actual elliptic mapping-torus models. -/
def step₂MappingTorusHomeomorph (p : PeriodDomain) :
    MappingTorusModel p ≃ₜ MappingTorusModel p.step₂ :=
  ((orbitMappingTorusHomeomorph p).symm.trans (step₂OrbitHomeomorph p)).trans
    (orbitMappingTorusHomeomorph p.step₂)

/-- The original cusp marking change in the actual elliptic mapping-torus models. -/
def step₀MappingTorusHomeomorph (p : PeriodDomain) :
    MappingTorusModel p ≃ₜ MappingTorusModel p.step₀ :=
  ((orbitMappingTorusHomeomorph p).symm.trans (step₀OrbitHomeomorph p)).trans
    (orbitMappingTorusHomeomorph p.step₀)

@[simp] theorem step₁MappingTorusHomeomorph_mk (p : PeriodDomain) (z : ℂ) (r : ℝ) :
    step₁MappingTorusHomeomorph p
      (MappingTorus.mk (returnTranslation p) (r, ellipticClass p z)) =
      MappingTorus.mk (returnTranslation p.step₁)
        (r, ellipticClass p.step₁ (-z / p.val.τ)) := by
  change orbitMappingTorusHomeomorph p.step₁ (step₁OrbitHomeomorph p
    ((orbitMappingTorusHomeomorph p).symm
      (MappingTorus.mk (returnTranslation p) (r, ellipticClass p z)))) = _
  rw [orbitMappingTorusHomeomorph_symm_apply p (z, r), step₁OrbitHomeomorph_class,
    orbitMappingTorusHomeomorph_apply, step₁Projection_apply]

@[simp] theorem step₂MappingTorusHomeomorph_mk (p : PeriodDomain) (z : ℂ) (r : ℝ) :
    step₂MappingTorusHomeomorph p
      (MappingTorus.mk (returnTranslation p) (r, ellipticClass p z)) =
      MappingTorus.mk (returnTranslation p.step₂)
        (r, ellipticClass p.step₂ (z / p.val.τ)) := by
  change orbitMappingTorusHomeomorph p.step₂ (step₂OrbitHomeomorph p
    ((orbitMappingTorusHomeomorph p).symm
      (MappingTorus.mk (returnTranslation p) (r, ellipticClass p z)))) = _
  rw [orbitMappingTorusHomeomorph_symm_apply p (z, r), step₂OrbitHomeomorph_class,
    orbitMappingTorusHomeomorph_apply, step₂Projection_apply]

@[simp] theorem step₀MappingTorusHomeomorph_mk (p : PeriodDomain) (z : ℂ) (r : ℝ) :
    step₀MappingTorusHomeomorph p
      (MappingTorus.mk (returnTranslation p) (r, ellipticClass p z)) =
      MappingTorus.mk (returnTranslation p.step₀) (r, ellipticClass p.step₀ z) := by
  change orbitMappingTorusHomeomorph p.step₀ (step₀OrbitHomeomorph p
    ((orbitMappingTorusHomeomorph p).symm
      (MappingTorus.mk (returnTranslation p) (r, ellipticClass p z)))) = _
  rw [orbitMappingTorusHomeomorph_symm_apply p (z, r), step₀OrbitHomeomorph_class,
    orbitMappingTorusHomeomorph_apply, step₀Projection_apply]

/-- The first mapping-torus formula is the original native biholomorphism. -/
theorem step₁MappingTorusHomeomorph_native (p : PeriodDomain) (x : p.Torus) :
    step₁MappingTorusHomeomorph p
      (circleMappingTorusHomeomorph p (circleOrbitProjection p x)) =
      circleMappingTorusHomeomorph p.step₁
        (circleOrbitProjection p.step₁ (p.step₁Biholomorph x)) := by
  change orbitMappingTorusHomeomorph p.step₁ (step₁OrbitHomeomorph p
    ((orbitMappingTorusHomeomorph p).symm
      (orbitMappingTorusHomeomorph p (orbitModelHomeomorph p (circleOrbitProjection p x))))) =
    orbitMappingTorusHomeomorph p.step₁
      (orbitModelHomeomorph p.step₁ (circleOrbitProjection p.step₁ (p.step₁Biholomorph x)))
  rw [Homeomorph.symm_apply_apply, orbitModelHomeomorph_projection,
    step₁OrbitHomeomorph_projection, orbitModelHomeomorph_projection]

/-- The second mapping-torus formula is the original native biholomorphism. -/
theorem step₂MappingTorusHomeomorph_native (p : PeriodDomain) (x : p.Torus) :
    step₂MappingTorusHomeomorph p
      (circleMappingTorusHomeomorph p (circleOrbitProjection p x)) =
      circleMappingTorusHomeomorph p.step₂
        (circleOrbitProjection p.step₂ (p.step₂Biholomorph x)) := by
  change orbitMappingTorusHomeomorph p.step₂ (step₂OrbitHomeomorph p
    ((orbitMappingTorusHomeomorph p).symm
      (orbitMappingTorusHomeomorph p (orbitModelHomeomorph p (circleOrbitProjection p x))))) =
    orbitMappingTorusHomeomorph p.step₂
      (orbitModelHomeomorph p.step₂ (circleOrbitProjection p.step₂ (p.step₂Biholomorph x)))
  rw [Homeomorph.symm_apply_apply, orbitModelHomeomorph_projection,
    step₂OrbitHomeomorph_projection, orbitModelHomeomorph_projection]

/-- The cusp mapping-torus formula is the original native marking change. -/
theorem step₀MappingTorusHomeomorph_native (p : PeriodDomain) (x : p.Torus) :
    step₀MappingTorusHomeomorph p
      (circleMappingTorusHomeomorph p (circleOrbitProjection p x)) =
      circleMappingTorusHomeomorph p.step₀
        (circleOrbitProjection p.step₀ (p.step₀Biholomorph x)) := by
  change orbitMappingTorusHomeomorph p.step₀ (step₀OrbitHomeomorph p
    ((orbitMappingTorusHomeomorph p).symm
      (orbitMappingTorusHomeomorph p (orbitModelHomeomorph p (circleOrbitProjection p x))))) =
    orbitMappingTorusHomeomorph p.step₀
      (orbitModelHomeomorph p.step₀ (circleOrbitProjection p.step₀ (p.step₀Biholomorph x)))
  rw [Homeomorph.symm_apply_apply, orbitModelHomeomorph_projection,
    step₀OrbitHomeomorph_projection, orbitModelHomeomorph_projection]

end Wikipedia.HopfProblem.PeriodFamilyCircleOrbit
