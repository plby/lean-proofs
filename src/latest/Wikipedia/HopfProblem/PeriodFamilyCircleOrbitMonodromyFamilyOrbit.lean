import Wikipedia.HopfProblem.PeriodFamilyCircleOrbitMonodromyBasic
import Wikipedia.HopfProblem.PeriodFamilyCircleOrbitMonodromyFamilyBasic
import Wikipedia.HopfProblem.PeriodFamilyCircleOrbitMonodromyFamilyCoordinates

/-!
# The original all-word family action on the actual circle quotients

The native fibre homeomorphisms commute with the original circle flow.
They therefore induce genuine homeomorphisms of the circle-orbit spaces
and of the proved three-period lattice models.  Their representative
formulas use the original right block and the full real monodromy.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.PeriodFamilyCircleOrbit

open SpecialPeriods

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction TriangleGroup B]
    (D : TrianglePeriodFamily.Data V B)

/-- The all-word transport of the native delta-circle orbit quotients. -/
def familyCircleOrbitHomeomorph (g : TriangleGroup) (b : B) :
    CircleOrbit (D.periods.point b) ≃ₜ CircleOrbit (D.periods.point (g • b)) :=
  circleOrbitCongr (familyDeckHomeomorph D g b) (familyDeckHomeomorph_circleFlow D g b)

@[simp] theorem familyCircleOrbitHomeomorph_projection (g : TriangleGroup) (b : B)
    (x : (D.periods.point b).Torus) :
    familyCircleOrbitHomeomorph D g b (circleOrbitProjection (D.periods.point b) x) =
      circleOrbitProjection (D.periods.point (g • b)) (familyDeckHomeomorph D g b x) :=
  circleOrbitCongr_projection _ _ x

@[simp] theorem familyCircleOrbitHomeomorph_symm_projection (g : TriangleGroup) (b : B)
    (x : (D.periods.point (g • b)).Torus) :
    (familyCircleOrbitHomeomorph D g b).symm
      (circleOrbitProjection (D.periods.point (g • b)) x) =
        circleOrbitProjection (D.periods.point b) ((familyDeckHomeomorph D g b).symm x) :=
  circleOrbitCongr_symm_projection _ _ x

/-- The descended map retains the actual complex covering representative. -/
@[simp] theorem familyCircleOrbitHomeomorph_mkQ (g : TriangleGroup) (b : B)
    (z : ComplexPlane₂) :
    familyCircleOrbitHomeomorph D g b
      (circleOrbitProjection (D.periods.point b) ((D.periods.point b).lattice.mkQ z)) =
        circleOrbitProjection (D.periods.point (g • b))
          ((D.periods.point (g • b)).lattice.mkQ (D.rightBlock g b *ᵥ z)) := by
  rw [familyCircleOrbitHomeomorph_projection, familyDeckHomeomorph_mkQ]

/-- The same actual family transport on the marked three-period quotients. -/
def familyOrbitModelHomeomorph (g : TriangleGroup) (b : B) :
    OrbitModel (D.periods.point b) ≃ₜ OrbitModel (D.periods.point (g • b)) :=
  orbitModelCongr (familyDeckHomeomorph D g b) (familyDeckHomeomorph_circleFlow D g b)

@[simp] theorem familyOrbitModelHomeomorph_projection (g : TriangleGroup) (b : B)
    (x : (D.periods.point b).Torus) :
    familyOrbitModelHomeomorph D g b (torusProjection (D.periods.point b) x) =
      torusProjection (D.periods.point (g • b)) (familyDeckHomeomorph D g b x) :=
  orbitModelCongr_projection _ _ x

/-- The marked lattice map is the original right block followed by the literal projection. -/
theorem familyOrbitModelHomeomorph_cover (g : TriangleGroup) (b : B)
    (z : ComplexPlane₂) :
    familyOrbitModelHomeomorph D g b
      (orbitClass (D.periods.point b) (linearProjection (D.periods.point b) z)) =
        orbitClass (D.periods.point (g • b))
          (linearProjection (D.periods.point (g • b)) (D.rightBlock g b *ᵥ z)) := by
  change familyOrbitModelHomeomorph D g b
    (torusProjection (D.periods.point b) ((D.periods.point b).lattice.mkQ z)) = _
  rw [familyOrbitModelHomeomorph_projection, familyDeckHomeomorph_mkQ, torusProjection_mkQ]

/-- Apply all four original real monodromy coordinates before taking the quotient. -/
theorem familyOrbitModelHomeomorph_periodCoordinates (g : TriangleGroup) (b : B)
    (x : RealPlane₄) :
    familyOrbitModelHomeomorph D g b
      (orbitClass (D.periods.point b)
        (projectedPeriods (D.periods.point b) (fun i : Fin 3 => x i.castSucc))) =
      orbitClass (D.periods.point (g • b))
        (projectedPeriods (D.periods.point (g • b))
          (fun i : Fin 3 => (triangleRealEquiv g x) i.castSucc)) := by
  simpa only [familyLinearProjection_monodromy, linearProjection_periodEquiv] using
    familyOrbitModelHomeomorph_cover D g b (Elliptic.periodEquiv (D.periods.point b) x)

/-- Every original triangle word preserves the actual first real-period circle. -/
theorem familyOrbitModelHomeomorph_time (g : TriangleGroup) (b : B)
    (x : OrbitModel (D.periods.point b)) :
    orbitTime (D.periods.point (g • b)) (familyOrbitModelHomeomorph D g b x) =
      orbitTime (D.periods.point b) x := by
  obtain ⟨z, rfl⟩ := orbitClass_surjective (D.periods.point b) x
  obtain ⟨w, rfl⟩ := linearProjection_surjective (D.periods.point b) z
  rw [familyOrbitModelHomeomorph_cover, orbitTime_class, orbitTime_class,
    familyLinearProjection_time_monodromy]

end Wikipedia.HopfProblem.PeriodFamilyCircleOrbit
