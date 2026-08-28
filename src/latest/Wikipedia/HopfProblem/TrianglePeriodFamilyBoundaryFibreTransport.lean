import Wikipedia.HopfProblem.TrianglePeriodFamilyHomology

/-!
# Actual fibre inclusions at arbitrary regular boundary points

Keeping the original real period coordinates fixed along an actual path
in the regular covering base gives a continuous homotopy of the entire
marked torus into the actual regular family. Hence its singular-homology
map in every degree agrees with the already normalized fibre map. The
primitive integral rows and the exact monodromy-difference kernel therefore
apply to fibres at arbitrary regular points, not only the canonical one.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

open SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology

variable (D : Data ℂ TriangleRegularPoint)

/-- The actual marked torus inclusion over any point of the regular
covering base, with its original unchanged real coordinates. -/
def pointFamilyFibreInclusion (z : TriangleRegularPoint) : C(RealTorus₄, D.Space) :=
  ⟨fun f => D.quotient (z, f),
    D.quotient_continuous.comp (continuous_const.prodMk continuous_id)⟩

@[simp] theorem pointFamilyFibreInclusion_apply (z : TriangleRegularPoint)
    (f : RealTorus₄) : pointFamilyFibreInclusion D z f = D.quotient (z, f) := rfl

@[simp] theorem pointFamilyFibreInclusion_slit (b : SlitBaseLift) :
    pointFamilyFibreInclusion D b.val = familyFibreInclusion D b := rfl

/-- This homotopy moves every marked torus point along the same genuine
base path; it is jointly continuous in the interval and the torus. -/
def pointFamilyFibreHomotopy {z w : TriangleRegularPoint} (γ : Path z w) :
    (pointFamilyFibreInclusion D z).Homotopy (pointFamilyFibreInclusion D w) where
  toFun tf := D.quotient (γ tf.1, tf.2)
  continuous_toFun := D.quotient_continuous.comp
    ((γ.continuous.comp continuous_fst).prodMk continuous_snd)
  map_zero_left f := by
    change D.quotient (γ 0, f) = D.quotient (z, f)
    rw [γ.source]
  map_one_left f := by
    change D.quotient (γ 1, f) = D.quotient (w, f)
    rw [γ.target]

@[simp] theorem pointFamilyFibreHomotopy_apply {z w : TriangleRegularPoint}
    (γ : Path z w) (t : unitInterval) (f : RealTorus₄) :
    pointFamilyFibreHomotopy D γ (t, f) = D.quotient (γ t, f) := rfl

/-- The actual whole-torus homotopy gives equality of the genuine singular
homology maps in every degree, with no marking equality assumed. -/
theorem pointFamilyFibreInclusion_homology_eq_of_path {z w : TriangleRegularPoint}
    (γ : Path z w) (n : ℕ) :
    singularHomologyMap (pointFamilyFibreInclusion D z) n =
      singularHomologyMap (pointFamilyFibreInclusion D w) n :=
  homotopy_homologyMap (pointFamilyFibreHomotopy D γ) n

/-- The actual regular covering base is path connected, so the marked
fibre map is independent of its chosen regular point. -/
theorem pointFamilyFibreInclusion_homology_eq (z w : TriangleRegularPoint) (n : ℕ) :
    singularHomologyMap (pointFamilyFibreInclusion D z) n =
      singularHomologyMap (pointFamilyFibreInclusion D w) n :=
  pointFamilyFibreInclusion_homology_eq_of_path D (PathConnectedSpace.somePath z w) n

/-- Comparison with the original normalized fibre inclusion used in the
actual regular-family Mayer--Vietoris computation. -/
theorem pointFamilyFibreInclusion_homology_eq_normalized (z : TriangleRegularPoint) (n : ℕ) :
    singularHomologyMap (pointFamilyFibreInclusion D z) n =
      singularHomologyMap (familyFibreInclusion D normalizedSlitBaseLift) n :=
  pointFamilyFibreInclusion_homology_eq D z normalizedSlitBaseLift.val n

/-- At any actual regular point, the fibre map kills exactly the integral
source-monodromy differences, with no rationalization or rank comparison. -/
theorem pointFamilyFibreInclusion_kernel (z : TriangleRegularPoint) (n : ℕ) :
    LinearMap.ker (singularHomologyMap (pointFamilyFibreInclusion D z) n) =
      LinearMap.range (sourceDifference n) := by
  rw [pointFamilyFibreInclusion_homology_eq_normalized, familyFibreInclusion_kernel]

/-- The actual degree-one boundary-fibre map has the same primitive row
in the existing integral marking of the regular family. -/
theorem familyH1Equiv_pointFibre (z : TriangleRegularPoint)
    (a : SingularHomology RealTorus₄ 1) :
    familyH1Equiv D (singularHomologyMap (pointFamilyFibreInclusion D z) 1 a) =
      ![FlatTorus.singularH1Equiv a 0, 0, 0] := by
  rw [pointFamilyFibreInclusion_homology_eq_normalized, familyH1Equiv_fibre]

/-- The actual degree-two row remains the primitive expression
`6 * x₂ + x₃` in the original ordered exterior-square coordinates. -/
theorem familyH2Equiv_pointFibre (z : TriangleRegularPoint)
    (a : SingularHomology RealTorus₄ 2) :
    familyH2Equiv D (singularHomologyMap (pointFamilyFibreInclusion D z) 2 a) =
      ![6 * FlatTorus.singularH2Coordinates a 2 + FlatTorus.singularH2Coordinates a 3,
        0, 0, 0, 0, 0] := by
  rw [pointFamilyFibreInclusion_homology_eq_normalized, familyH2Equiv_fibre]

/-- The actual degree-three row keeps its original exterior-cube coordinate. -/
theorem familyH3Equiv_pointFibre (z : TriangleRegularPoint)
    (a : SingularHomology RealTorus₄ 3) :
    familyH3Equiv D (singularHomologyMap (pointFamilyFibreInclusion D z) 3 a) =
      ![FlatTorus.singularH3Coordinates a 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [pointFamilyFibreInclusion_homology_eq_normalized, familyH3Equiv_fibre]

/-- The actual positively marked top fibre class gives the first
degree-four coordinate at every regular boundary point. -/
theorem familyH4Equiv_pointFibre (z : TriangleRegularPoint)
    (a : SingularHomology RealTorus₄ 4) :
    familyH4Equiv D (singularHomologyMap (pointFamilyFibreInclusion D z) 4 a) =
      ![realTorusH4Equiv a, 0, 0, 0, 0, 0] := by
  rw [pointFamilyFibreInclusion_homology_eq_normalized, familyH4Equiv_fibre]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Homology
