import Wikipedia.HopfProblem.PeriodFamilyCircleOrbitAction
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionTriangleBasic

/-!
# All-word transport between the original period tori

The actual four-dimensional integral triangle action, conjugated by the
original period-coordinate homeomorphisms, gives homeomorphisms between
the native complex period quotients.  Their complex lifts are the original
right blocks, and they commute with the original delta-circle flow.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.PeriodFamilyCircleOrbit

open SpecialPeriods

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction TriangleGroup B]
    (D : TrianglePeriodFamily.Data V B)

/-- Transport by an actual triangle word through the full original real torus. -/
def familyDeckHomeomorph (g : TriangleGroup) (b : B) :
    (D.periods.point b).Torus ≃ₜ (D.periods.point (g • b)).Torus :=
  (D.periods.torusHomeomorph b).symm.trans
    ((triangleTorusHomeomorph g).trans (D.periods.torusHomeomorph (g • b)))

theorem familyDeckHomeomorph_torusHomeomorph (g : TriangleGroup) (b : B)
    (x : RealTorus₄) :
    familyDeckHomeomorph D g b (D.periods.torusHomeomorph b x) =
      D.periods.torusHomeomorph (g • b) (triangleTorusHomeomorph g x) := by
  simp only [familyDeckHomeomorph, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]

/-- The complex representative is transformed by the actual all-word right block. -/
@[simp] theorem familyDeckHomeomorph_mkQ (g : TriangleGroup) (b : B)
    (z : ComplexPlane₂) :
    familyDeckHomeomorph D g b ((D.periods.point b).lattice.mkQ z) =
      (D.periods.point (g • b)).lattice.mkQ (D.rightBlock g b *ᵥ z) := by
  apply (D.periods.torusHomeomorph (g • b)).symm.injective
  simp only [familyDeckHomeomorph, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
  change triangleTorusHomeomorph g
      (standardLattice.mkQ ((D.periods.periodEquiv b).symm z)) =
    standardLattice.mkQ
      ((D.periods.periodEquiv (g • b)).symm (D.rightBlock g b *ᵥ z))
  rw [triangleTorusHomeomorph_mkQ, D.periodEquiv_symm_monodromy]

@[simp] theorem familyDeckHomeomorph_symm_mkQ (g : TriangleGroup) (b : B)
    (z : ComplexPlane₂) :
    (familyDeckHomeomorph D g b).symm ((D.periods.point (g • b)).lattice.mkQ z) =
      (D.periods.point b).lattice.mkQ ((D.rightEquiv g b).symm z) := by
  apply (familyDeckHomeomorph D g b).injective
  rw [Homeomorph.apply_symm_apply, familyDeckHomeomorph_mkQ]
  apply congrArg (D.periods.point (g • b)).lattice.mkQ
  exact (D.rightEquiv g b).apply_symm_apply z |>.symm

/-- No real period coefficient, including the delta coefficient, is discarded. -/
theorem familyDeckHomeomorph_periodCoordinates (g : TriangleGroup) (b : B)
    (x : RealPlane₄) :
    familyDeckHomeomorph D g b
      ((D.periods.point b).lattice.mkQ (D.periods.periodEquiv b x)) =
        (D.periods.point (g • b)).lattice.mkQ
          (D.periods.periodEquiv (g • b) (triangleRealEquiv g x)) := by
  rw [familyDeckHomeomorph_mkQ, D.periodEquiv_monodromy]

/-- This fibre transport is exactly the original total-space triangle action. -/
theorem fibreInclusion_familyDeckHomeomorph (g : TriangleGroup) (b : B)
    (x : (D.periods.point b).Torus) :
    letI := D.totalAction
    D.periods.fibreInclusion (g • b) (familyDeckHomeomorph D g b x) =
      g • D.periods.fibreInclusion b x := by
  let := D.totalAction
  change (g • b, (D.periods.torusHomeomorph (g • b)).symm
      (familyDeckHomeomorph D g b x)) =
    (g • b, triangleTorusHomeomorph g ((D.periods.torusHomeomorph b).symm x))
  simp only [familyDeckHomeomorph, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]

/-- The original triangle quotient identifies the two transported fibre points. -/
theorem quotient_fibreInclusion_familyDeckHomeomorph (g : TriangleGroup) (b : B)
    (x : (D.periods.point b).Torus) :
    D.quotient (D.periods.fibreInclusion (g • b) (familyDeckHomeomorph D g b x)) =
      D.quotient (D.periods.fibreInclusion b x) := by
  let := D.totalAction
  rw [fibreInclusion_familyDeckHomeomorph, D.quotient_smul]

@[simp] theorem familyDeckHomeomorph_zero (g : TriangleGroup) (b : B) :
    familyDeckHomeomorph D g b 0 = 0 := by
  simpa using familyDeckHomeomorph_mkQ D g b 0

theorem familyDeckHomeomorph_add (g : TriangleGroup) (b : B)
    (x y : (D.periods.point b).Torus) :
    familyDeckHomeomorph D g b (x + y) =
      familyDeckHomeomorph D g b x + familyDeckHomeomorph D g b y := by
  obtain ⟨z, rfl⟩ := (D.periods.point b).lattice.mkQ_surjective x
  obtain ⟨w, rfl⟩ := (D.periods.point b).lattice.mkQ_surjective y
  rw [← map_add, familyDeckHomeomorph_mkQ, familyDeckHomeomorph_mkQ,
    familyDeckHomeomorph_mkQ, Matrix.mulVec_add, map_add]

/-- All original triangle words commute with the actual delta-circle action. -/
theorem familyDeckHomeomorph_circleFlow (g : TriangleGroup) (b : B)
    (t : AddCircle (1 : ℝ)) (x : (D.periods.point b).Torus) :
    familyDeckHomeomorph D g b (circleFlow (D.periods.point b) t x) =
      circleFlow (D.periods.point (g • b)) t (familyDeckHomeomorph D g b x) := by
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective t
  obtain ⟨z, rfl⟩ := (D.periods.point b).lattice.mkQ_surjective x
  simp only [circleFlow_coe_mkQ, familyDeckHomeomorph_mkQ, Matrix.mulVec_add,
    Threefold.VerticalAction.Triangle.rightBlock_vector]

end Wikipedia.HopfProblem.PeriodFamilyCircleOrbit
