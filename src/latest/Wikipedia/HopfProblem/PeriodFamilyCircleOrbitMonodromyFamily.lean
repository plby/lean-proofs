import Wikipedia.HopfProblem.PeriodFamilyCircleOrbitMonodromyFamilyOrbit

/-!
# All-word transport in the actual family of elliptic mapping-torus models

Every word in the original triangle group transports the native period
torus, its original delta-circle quotient, and its marked elliptic
mapping-torus model.  The transport uses the actual right block on complex
covering vectors and the full original four-dimensional real monodromy.
Its base circle is the original first real-period circle.

No product decomposition of the varying family or extension across a
singular filling is asserted.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.PeriodFamilyCircleOrbit

open SpecialPeriods

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction TriangleGroup B]
    (D : TrianglePeriodFamily.Data V B)

/-- The native flat projection is transported by all four original real coordinates. -/
theorem familyDeckHomeomorph_flatProjection (g : TriangleGroup) (b : B)
    (x : RealPlane₄) :
    familyDeckHomeomorph D g b (Elliptic.flatProjection (D.periods.point b) x) =
      Elliptic.flatProjection (D.periods.point (g • b)) (triangleRealEquiv g x) := by
  change familyDeckHomeomorph D g b
      ((D.periods.point b).lattice.mkQ (Elliptic.periodEquiv (D.periods.point b) x)) = _
  rw [familyDeckHomeomorph_mkQ, familyPeriodEquiv_monodromy]
  rfl

/-- The original all-word transport in the genuine elliptic mapping-torus models. -/
def familyMappingTorusHomeomorph (g : TriangleGroup) (b : B) :
    MappingTorusModel (D.periods.point b) ≃ₜ MappingTorusModel (D.periods.point (g • b)) :=
  mappingTorusCongr (familyDeckHomeomorph D g b) (familyDeckHomeomorph_circleFlow D g b)

@[simp] theorem familyMappingTorusHomeomorph_projection (g : TriangleGroup) (b : B)
    (x : (D.periods.point b).Torus) :
    familyMappingTorusHomeomorph D g b
      (circleMappingTorusHomeomorph (D.periods.point b)
        (circleOrbitProjection (D.periods.point b) x)) =
      circleMappingTorusHomeomorph (D.periods.point (g • b))
        (circleOrbitProjection (D.periods.point (g • b)) (familyDeckHomeomorph D g b x)) :=
  mappingTorusCongr_projection _ _ x

/-- The actual complex covering map descends without changing its right block. -/
theorem familyMappingTorusHomeomorph_cover (g : TriangleGroup) (b : B)
    (z : ComplexPlane₂) :
    familyMappingTorusHomeomorph D g b
      (mappingTorusProjection (D.periods.point b) (linearProjection (D.periods.point b) z)) =
      mappingTorusProjection (D.periods.point (g • b))
        (linearProjection (D.periods.point (g • b)) (D.rightBlock g b *ᵥ z)) := by
  have h := familyMappingTorusHomeomorph_projection D g b ((D.periods.point b).lattice.mkQ z)
  rw [familyDeckHomeomorph_mkQ, circleMappingTorusHomeomorph_mkQ,
    circleMappingTorusHomeomorph_mkQ] at h
  exact h

/-- The literal mapping-torus representative, including its original real time. -/
theorem familyMappingTorusHomeomorph_representative (g : TriangleGroup) (b : B)
    (z : ComplexPlane₂) :
    familyMappingTorusHomeomorph D g b
      (MappingTorus.mk (returnTranslation (D.periods.point b))
        ((linearProjection (D.periods.point b) z).2,
          ellipticClass (D.periods.point b) (z 0))) =
      MappingTorus.mk (returnTranslation (D.periods.point (g • b)))
        ((linearProjection (D.periods.point (g • b)) (D.rightBlock g b *ᵥ z)).2,
          ellipticClass (D.periods.point (g • b)) ((D.rightBlock g b *ᵥ z) 0)) :=
  familyMappingTorusHomeomorph_cover D g b z

/-- The marked real-period formula keeps the full native monodromy before quotienting delta. -/
theorem familyMappingTorusHomeomorph_periodCoordinates (g : TriangleGroup) (b : B)
    (x : RealPlane₄) :
    familyMappingTorusHomeomorph D g b
      (MappingTorus.mk (returnTranslation (D.periods.point b))
        (x 0, ellipticClass (D.periods.point b)
          (6 * (D.periods.point b).val.μ * (x 0 : ℂ) +
            (D.periods.point b).val.τ * (x 1 : ℂ) + (x 2 : ℂ)))) =
      MappingTorus.mk (returnTranslation (D.periods.point (g • b)))
        ((triangleRealEquiv g x) 0, ellipticClass (D.periods.point (g • b))
          (6 * (D.periods.point (g • b)).val.μ * ((triangleRealEquiv g x) 0 : ℂ) +
            (D.periods.point (g • b)).val.τ * ((triangleRealEquiv g x) 1 : ℂ) +
              ((triangleRealEquiv g x) 2 : ℂ))) := by
  have h := familyMappingTorusHomeomorph_projection D g b
    (Elliptic.flatProjection (D.periods.point b) x)
  rw [familyDeckHomeomorph_flatProjection, circleMappingTorusHomeomorph_flatProjection,
    circleMappingTorusHomeomorph_flatProjection] at h
  exact h

/-- The two already-constructed quotient comparisons commute with actual family transport. -/
theorem familyMappingTorusHomeomorph_orbitModel (g : TriangleGroup) (b : B)
    (x : OrbitModel (D.periods.point b)) :
    familyMappingTorusHomeomorph D g b (orbitMappingTorusHomeomorph (D.periods.point b) x) =
      orbitMappingTorusHomeomorph (D.periods.point (g • b))
        (familyOrbitModelHomeomorph D g b x) := by
  obtain ⟨z, rfl⟩ := orbitClass_surjective (D.periods.point b) x
  obtain ⟨w, rfl⟩ := linearProjection_surjective (D.periods.point b) z
  rw [familyOrbitModelHomeomorph_cover, orbitMappingTorusHomeomorph_apply,
    orbitMappingTorusHomeomorph_apply]
  exact familyMappingTorusHomeomorph_cover D g b w

/-- The actual first real-period circle is invariant under every original triangle word. -/
theorem familyMappingTorusHomeomorph_time (g : TriangleGroup) (b : B)
    (x : MappingTorusModel (D.periods.point b)) :
    MappingTorus.base (returnTranslation (D.periods.point (g • b)))
      (familyMappingTorusHomeomorph D g b x) =
        MappingTorus.base (returnTranslation (D.periods.point b)) x := by
  obtain ⟨z, rfl⟩ := mappingTorusProjection_surjective (D.periods.point b) x
  obtain ⟨w, rfl⟩ := linearProjection_surjective (D.periods.point b) z
  rw [familyMappingTorusHomeomorph_cover, mappingTorusProjection_apply,
    mappingTorusProjection_apply, MappingTorus.base_mk, MappingTorus.base_mk,
    familyLinearProjection_time_monodromy]

end Wikipedia.HopfProblem.PeriodFamilyCircleOrbit
