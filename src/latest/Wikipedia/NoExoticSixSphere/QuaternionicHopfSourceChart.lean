import Wikipedia.NoExoticSixSphere.QuaternionicHopfTubeClass
import Wikipedia.NoExoticSixSphere.StereographicTargetDifferential

/-!
# The actual south Hopf fiber in the original source stereographic chart

The pole is the real first-quaternion axis. The entire south fiber is
orthogonal to it, and its chart image has the actual factor-two radius.
The original regular-fiber atlas and ambient chart inclusion are retained.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

open Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration

theorem first_sourcePole : first (spherePole 7).val = 1 := by
  rw [← fiberPoint_pole, first_fiberPoint]
  apply Quaternion.linearIsometryEquivTuple.injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [spherePole]

theorem second_sourcePole : second (spherePole 7).val = 0 :=
  (sphereMap_eq_pole_iff (spherePole 7)).mp sphereMap_pole

theorem sourcePole_inner (x : V 8) : inner ℝ (spherePole 7).val x = (first x).re := by
  rw [inner_quaternion_coordinates, first_sourcePole, second_sourcePole, inner_zero_left,
    add_zero, Quaternion.inner_def, one_mul]
  simp

theorem southFiber_orthogonal_sourcePole (q : Sphere 3) :
    inner ℝ (spherePole 7).val (southFiberPoint q).val = 0 := by
  rw [sourcePole_inner, first_southFiberPoint]
  rfl

def southChartUnit (q : Sphere 3) : V 7 :=
  StereographicEquator.project 7 (southFiberPoint q).val

theorem lift_southChartUnit (q : Sphere 3) :
    StereographicEquator.lift 7 (southChartUnit q) = (southFiberPoint q).val :=
  StereographicEquator.lift_project_of_orthogonal 7 _ (southFiber_orthogonal_sourcePole q)

theorem norm_southChartUnit (q : Sphere 3) : ‖southChartUnit q‖ = 1 := by
  rw [← StereographicEquator.norm_lift 7, lift_southChartUnit]
  exact mem_sphere_zero_iff_norm.mp (southFiberPoint q).property

theorem sourceChart_southFiber (q : Sphere 3) :
    sphereProjection 7 (southFiberPoint q) = (2 : ℝ) • southChartUnit q :=
  StereographicEquator.chart_equator 7 _ (southFiber_orthogonal_sourcePole q)

theorem southChartEmbedding_parametrized (q : Sphere 3) :
    letI := regularFiberAtlas sphereMap contMDiff_sphereMap south south_regular 3
      (by simp only [finrank_euclideanSpace_fin]);
    southChartEmbedding.toFun (southFiberDiffeomorph q) = (2 : ℝ) • southChartUnit q := by
  let := regularFiberAtlas sphereMap contMDiff_sphereMap south south_regular 3
    (by simp only [finrank_euclideanSpace_fin])
  change sphereProjection 7 (southFiberDiffeomorph q).val = _
  rw [southFiberDiffeomorph_val]
  exact sourceChart_southFiber q

theorem first_lift_re (v : V 7) : (first (StereographicEquator.lift 7 v)).re = 0 := by
  rw [← sourcePole_inner, real_inner_comm]
  exact StereographicEquator.inner_lift_pole 7 v

theorem finiteAmbient_southChartUnit (q : Sphere 3) :
    StereographicEquator.finiteAmbient 7 ((2 : ℝ) • southChartUnit q) =
      (southFiberPoint q).val := by
  have h := StereographicEquator.compactification_double_axis 7
    (⟨southChartUnit q, mem_sphere_zero_iff_norm.mpr (norm_southChartUnit q)⟩ : Sphere 6)
  have hh := congrArg Subtype.val h
  exact hh.trans (lift_southChartUnit q)

end NoExoticSixSphere.QuaternionicHopf
