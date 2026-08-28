import Wikipedia.HopfProblem.PeriodFamilyCircleOrbitLinear
import Wikipedia.HopfProblem.TrianglePeriodFamilyAction
import Wikipedia.HopfProblem.TrianglePeriodFamilyGammaZeroLinear

/-!
# Actual family monodromy in the transverse period coordinates

The varying family's period map agrees with the canonical period map on
every original four-dimensional real vector.  Its complex monodromy lift
therefore projects by applying the full four-dimensional real monodromy
first, and only then forgetting the delta coordinate.  The normalized real
time is the original gamma coordinate and is preserved on the entire
complex covering space.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.PeriodFamilyCircleOrbit

open SpecialPeriods

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B] [MulAction TriangleGroup B]
  (D : TrianglePeriodFamily.Data V B)

/-- Both native period maps have exactly the same original complex columns. -/
theorem familyPeriodEquiv_apply (b : B) (x : RealPlane₄) :
    D.periods.periodEquiv b x = Elliptic.periodEquiv (D.periods.point b) x :=
  (D.periodEquiv_matrix b x).trans (Elliptic.periodEquiv_matrix (D.periods.point b) x).symm

/-- The complex lift agrees with the entire original real monodromy map. -/
theorem familyPeriodEquiv_monodromy (g : TriangleGroup) (b : B) (x : RealPlane₄) :
    D.rightBlock g b *ᵥ Elliptic.periodEquiv (D.periods.point b) x =
      Elliptic.periodEquiv (D.periods.point (g • b)) (triangleRealEquiv g x) := by
  rw [← familyPeriodEquiv_apply D b x, ← D.periodEquiv_monodromy,
    familyPeriodEquiv_apply]

/-- Projection forgets delta only after applying the full native monodromy. -/
theorem familyLinearProjection_monodromy (g : TriangleGroup) (b : B) (x : RealPlane₄) :
    linearProjection (D.periods.point (g • b))
        (D.rightBlock g b *ᵥ Elliptic.periodEquiv (D.periods.point b) x) =
      projectedPeriods (D.periods.point (g • b))
        (fun i : Fin 3 => (triangleRealEquiv g x) i.castSucc) := by
  rw [familyPeriodEquiv_monodromy, linearProjection_periodEquiv]

/-- The actual covering-space time is invariant for every complex point. -/
theorem familyLinearProjection_time_monodromy (g : TriangleGroup) (b : B)
    (z : ComplexPlane₂) :
    (linearProjection (D.periods.point (g • b)) (D.rightBlock g b *ᵥ z)).2 =
      (linearProjection (D.periods.point b) z).2 := by
  obtain ⟨x, rfl⟩ := (Elliptic.periodEquiv (D.periods.point b)).surjective z
  rw [familyLinearProjection_monodromy, linearProjection_periodEquiv]
  exact TrianglePeriodFamily.GammaZero.triangleRealEquiv_gamma g x

end Wikipedia.HopfProblem.PeriodFamilyCircleOrbit
