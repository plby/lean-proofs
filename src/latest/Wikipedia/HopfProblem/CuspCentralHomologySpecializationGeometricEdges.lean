import Wikipedia.HopfProblem.CuspCentralHomologyBaseTorusTheta

/-!
# Marked displacements of the three actual theta edges

The first three dual hexagon sides, with the middle side reversed, are
the actual paths used by the theta base map.  Their displacement vectors
are computed in the original marked base coordinate `-B₀ y`.  The
integer differences and the zero-sum edge-cycle identities below concern
these literal paths; no cellular or singular-homology marking is assumed.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace ToricComponent CuspHoneycomb CuspHoneycombTiling CuspHoneycombHexagon
open PeriodTorusHigherHomology

local notation "Plane" => CuspHoneycombTiling.Plane
local notation "Lattice" => CuspHoneycombTiling.Lattice

/-- Exact affine coordinates of the three oriented paths in the literal
dual honeycomb plane. -/
theorem orientedEdgeBasePoint_formula (t : unitInterval) (j : Fin 3) :
    orientedEdgeBasePoint t j =
      ![![(2 - (t : ℝ)) / 3, (2 * (t : ℝ) - 1) / 3],
        ![(2 * (t : ℝ) - 1) / 3, (2 - (t : ℝ)) / 3],
        ![-(1 + (t : ℝ)) / 3, (2 - (t : ℝ)) / 3]] j := by
  fin_cases j
  · change dualSidePoint 0 t = ![(2 - (t : ℝ)) / 3, (2 * (t : ℝ) - 1) / 3]
    rw [dualSidePoint_apply, sideIntervalHomeomorph_apply]
    change dualStandardPlaneHomeomorph.symm
      ((1 - (t : ℝ)) • vertex 5 + (t : ℝ) • vertex 0) = _
    rw [vertex_five, vertex_zero, dualStandardPlaneHomeomorph_symm_apply]
    funext i
    fin_cases i <;> norm_num [Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring
  · change dualSidePoint 1 (unitInterval.symm t) =
      ![(2 * (t : ℝ) - 1) / 3, (2 - (t : ℝ)) / 3]
    rw [dualSidePoint_apply, sideIntervalHomeomorph_apply]
    change dualStandardPlaneHomeomorph.symm
      ((1 - ((unitInterval.symm t : unitInterval) : ℝ)) • vertex 0 +
        ((unitInterval.symm t : unitInterval) : ℝ) • vertex 1) = _
    rw [vertex_zero, vertex_one, dualStandardPlaneHomeomorph_symm_apply]
    funext i
    fin_cases i <;>
      norm_num [unitInterval.coe_symm_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring
  · change dualSidePoint 2 t = ![-(1 + (t : ℝ)) / 3, (2 - (t : ℝ)) / 3]
    rw [dualSidePoint_apply, sideIntervalHomeomorph_apply]
    change dualStandardPlaneHomeomorph.symm
      ((1 - (t : ℝ)) • vertex 1 + (t : ℝ) • vertex 2) = _
    rw [vertex_one, vertex_two, dualStandardPlaneHomeomorph_symm_apply]
    funext i
    fin_cases i <;> norm_num [Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring

theorem orientedEdgeBasePoint_start_values (j : Fin 3) :
    orientedEdgeBasePoint 0 j =
      ![![(2 : ℝ) / 3, -1 / 3], ![-1 / 3, 2 / 3], ![-1 / 3, 2 / 3]] j := by
  rw [orientedEdgeBasePoint_formula]
  norm_num

theorem orientedEdgeBasePoint_end_values (j : Fin 3) :
    orientedEdgeBasePoint 1 j =
      ![![(1 : ℝ) / 3, 1 / 3], ![1 / 3, 1 / 3], ![-2 / 3, 1 / 3]] j := by
  rw [orientedEdgeBasePoint_formula]
  norm_num

theorem orientedEdgeBasePoint_affine (t : unitInterval) (j : Fin 3) :
    orientedEdgeBasePoint t j = orientedEdgeBasePoint 0 j +
      (t : ℝ) • (orientedEdgeBasePoint 1 j - orientedEdgeBasePoint 0 j) := by
  rw [orientedEdgeBasePoint_formula, orientedEdgeBasePoint_start_values,
    orientedEdgeBasePoint_end_values]
  fin_cases j <;> funext i <;> fin_cases i <;>
    norm_num [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;> ring

/-- The starting lift of each edge in the actual marked `β` plane. -/
def thetaEdgeBaseStart (j : Fin 3) : Plane :=
  -realCuspVector (orientedEdgeBasePoint 0 j)

/-- The actual marked displacement of an oriented theta edge. -/
def thetaEdgeBaseDisplacement (j : Fin 3) : Plane :=
  -realCuspVector (orientedEdgeBasePoint 1 j - orientedEdgeBasePoint 0 j)

theorem thetaEdgeBaseStart_values (j : Fin 3) :
    thetaEdgeBaseStart j =
      ![![(1 : ℝ) / 3, 2 / 3], ![-2 / 3, -1 / 3], ![-2 / 3, -1 / 3]] j := by
  rw [thetaEdgeBaseStart, orientedEdgeBasePoint_start_values]
  fin_cases j <;> funext i <;> fin_cases i <;> norm_num [realCuspVector]

/-- The first and third paths are forward sides; the middle path is reversed. -/
theorem thetaEdgeBaseDisplacement_values (j : Fin 3) :
    thetaEdgeBaseDisplacement j =
      ![![(-2 : ℝ) / 3, -1 / 3], ![1 / 3, 2 / 3], ![1 / 3, -1 / 3]] j := by
  rw [thetaEdgeBaseDisplacement, orientedEdgeBasePoint_start_values,
    orientedEdgeBasePoint_end_values]
  fin_cases j <;> funext i <;> fin_cases i <;>
    norm_num [realCuspVector, Pi.sub_apply]

@[simp] theorem thetaEdgeBaseDisplacement_zero :
    thetaEdgeBaseDisplacement 0 = ![(-2 : ℝ) / 3, -1 / 3] :=
  thetaEdgeBaseDisplacement_values 0

@[simp] theorem thetaEdgeBaseDisplacement_one :
    thetaEdgeBaseDisplacement 1 = ![(1 : ℝ) / 3, 2 / 3] :=
  thetaEdgeBaseDisplacement_values 1

@[simp] theorem thetaEdgeBaseDisplacement_two :
    thetaEdgeBaseDisplacement 2 = ![(1 : ℝ) / 3, -1 / 3] :=
  thetaEdgeBaseDisplacement_values 2

theorem thetaEdgeBaseCoordinates_affine (t : unitInterval) (j : Fin 3) :
    -realCuspVector (orientedEdgeBasePoint t j) =
      thetaEdgeBaseStart j + (t : ℝ) • thetaEdgeBaseDisplacement j := by
  rw [orientedEdgeBasePoint_affine]
  simp only [map_add, map_smul, neg_add, thetaEdgeBaseStart, thetaEdgeBaseDisplacement,
    smul_neg]

/-- The original torus-valued edge path is exactly its affine marked lift. -/
theorem baseTorusPoint_orientedEdgeBasePoint_affine (t : unitInterval) (j : Fin 3) :
    baseTorusPoint (orientedEdgeBasePoint t j) =
      coordinateProjection 2 (thetaEdgeBaseStart j + (t : ℝ) • thetaEdgeBaseDisplacement j) := by
  rw [baseTorusPoint_apply, thetaEdgeBaseCoordinates_affine]

theorem thetaBaseCylinder_affine (t : unitInterval) (j : Fin 3) :
    thetaBaseCylinder (t, j) =
      coordinateProjection 2 (thetaEdgeBaseStart j + (t : ℝ) • thetaEdgeBaseDisplacement j) :=
  baseTorusPoint_orientedEdgeBasePoint_affine t j

theorem thetaBaseMap_mk_affine (t : unitInterval) (j : Fin 3) :
    thetaBaseMap (Suspension.mk t j) =
      coordinateProjection 2 (thetaEdgeBaseStart j + (t : ℝ) • thetaEdgeBaseDisplacement j) := by
  rw [thetaBaseMap_mk, thetaBaseCylinder_affine]

/-- All three affine lifts may use the same starting point after reduction
modulo the actual integer lattice. -/
theorem thetaBaseCylinder_affine_commonStart (t : unitInterval) (j : Fin 3) :
    thetaBaseCylinder (t, j) =
      coordinateProjection 2 (thetaEdgeBaseStart 0 + (t : ℝ) • thetaEdgeBaseDisplacement j) := by
  have hs : coordinateProjection 2 (thetaEdgeBaseStart j) =
      coordinateProjection 2 (thetaEdgeBaseStart 0) := thetaBaseCylinder_zero j
  rw [thetaBaseCylinder_affine, map_add, hs, ← map_add]

theorem thetaBaseMap_mk_affine_commonStart (t : unitInterval) (j : Fin 3) :
    thetaBaseMap (Suspension.mk t j) =
      coordinateProjection 2 (thetaEdgeBaseStart 0 + (t : ℝ) • thetaEdgeBaseDisplacement j) := by
  rw [thetaBaseMap_mk, thetaBaseCylinder_affine_commonStart]

/-- The edge differences are actual integral base displacements. -/
theorem thetaEdgeBaseDisplacement_sub_two (j : Fin 3) :
    thetaEdgeBaseDisplacement j - thetaEdgeBaseDisplacement 2 =
      latticePoint (![![-1, 0], ![0, 1], ![0, 0]] j) := by
  rw [thetaEdgeBaseDisplacement_values, thetaEdgeBaseDisplacement_two]
  fin_cases j <;> funext i <;> fin_cases i <;>
    norm_num [Pi.sub_apply, latticePoint]

theorem thetaEdgeBaseDisplacement_zero_sub_one :
    thetaEdgeBaseDisplacement 0 - thetaEdgeBaseDisplacement 1 = latticePoint ![-1, -1] := by
  rw [thetaEdgeBaseDisplacement_zero, thetaEdgeBaseDisplacement_one]
  funext i
  fin_cases i <;> norm_num [Pi.sub_apply, latticePoint]

/-- The marked displacement of a zero-sum real edge combination. -/
theorem thetaEdgeBaseDisplacement_sum_of_sum_zero (m : Fin 3 → ℝ)
    (hm : ∑ j, m j = 0) :
    (∑ j, m j • thetaEdgeBaseDisplacement j) = ![-m 0, m 1] := by
  have hm' : m 0 + m 1 + m 2 = 0 := by
    simpa only [Fin.sum_univ_three] using hm
  funext i
  fin_cases i <;>
    simp [Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul] <;> linarith

/-- In particular, a zero-sum integral edge combination has an actual
integral marked base displacement. -/
theorem thetaEdgeBaseDisplacement_sum_int (m : Fin 3 → ℤ)
    (hm : ∑ j, m j = 0) :
    (∑ j, (m j : ℝ) • thetaEdgeBaseDisplacement j) = latticePoint ![-m 0, m 1] := by
  have hm' : ∑ j, (m j : ℝ) = 0 := by exact_mod_cast hm
  rw [thetaEdgeBaseDisplacement_sum_of_sum_zero _ hm']
  funext i
  fin_cases i <;> simp [latticePoint]

/-- The marked base lattice vector of a zero-sum combination of the
three actual theta edges. -/
def thetaEdgeCycleLattice (m : Fin 3 → ℤ) : Lattice := ![-m 0, m 1]

/-- The unique zero-sum edge coefficients with a given marked base vector. -/
def thetaEdgeCycleCoefficients (β : Lattice) : Fin 3 → ℤ :=
  ![-β 0, β 1, β 0 - β 1]

@[simp] theorem thetaEdgeCycleCoefficients_sum (β : Lattice) :
    ∑ j, thetaEdgeCycleCoefficients β j = 0 := by
  rw [Fin.sum_univ_three]
  change -β 0 + β 1 + (β 0 - β 1) = 0
  omega

@[simp] theorem thetaEdgeCycleLattice_coefficients (β : Lattice) :
    thetaEdgeCycleLattice (thetaEdgeCycleCoefficients β) = β := by
  ext i
  fin_cases i <;> simp [thetaEdgeCycleLattice, thetaEdgeCycleCoefficients]

theorem thetaEdgeCycleCoefficients_lattice (m : Fin 3 → ℤ)
    (hm : ∑ j, m j = 0) :
    thetaEdgeCycleCoefficients (thetaEdgeCycleLattice m) = m := by
  have hm' : m 0 + m 1 + m 2 = 0 := by
    simpa only [Fin.sum_univ_three] using hm
  ext j
  fin_cases j
  · simp [thetaEdgeCycleLattice, thetaEdgeCycleCoefficients]
  · simp [thetaEdgeCycleLattice, thetaEdgeCycleCoefficients]
  · change -m 0 - m 1 = m 2
    omega

/-- The middle edge is reversed; the first and last edges retain their orientation. -/
def thetaEdgeOrientationSign (j : Fin 3) : ℤ := if j = 1 then -1 else 1

@[simp] theorem thetaEdgeOrientationSign_zero : thetaEdgeOrientationSign 0 = 1 := rfl
@[simp] theorem thetaEdgeOrientationSign_one : thetaEdgeOrientationSign 1 = -1 := rfl
@[simp] theorem thetaEdgeOrientationSign_two : thetaEdgeOrientationSign 2 = 1 := rfl

/-- Actual signed ray determinants give the edge-cycle coefficients. -/
theorem thetaEdgeCycleCoefficients_det (β : Lattice) (j : Fin 3) :
    thetaEdgeCycleCoefficients β j = thetaEdgeOrientationSign j *
      (hexagonRay (thetaEdgeIndex j) 0 * cuspVector β 1 -
        hexagonRay (thetaEdgeIndex j) 1 * cuspVector β 0) := by
  rw [thetaEdgeIndex_ray]
  fin_cases j <;>
    simp [thetaEdgeCycleCoefficients, thetaEdgeOrientationSign, cuspVector]

/-- The same determinant identity in the literal real lattice plane. -/
theorem thetaEdgeCycleCoefficients_det_real (β : Lattice) (j : Fin 3) :
    (thetaEdgeCycleCoefficients β j : ℝ) = (thetaEdgeOrientationSign j : ℝ) *
      (latticePoint (hexagonRay (thetaEdgeIndex j)) 0 *
          realCuspVector (latticePoint β) 1 -
        latticePoint (hexagonRay (thetaEdgeIndex j)) 1 *
          realCuspVector (latticePoint β) 0) := by
  have h := congrArg (fun z : ℤ => (z : ℝ)) (thetaEdgeCycleCoefficients_det β j)
  simpa only [Int.cast_mul, Int.cast_sub, latticePoint, realCuspVector,
    cuspVector, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Int.cast_neg] using h

/-- Matrix-determinant form, with the actual ray and cusp vectors as columns. -/
theorem thetaEdgeCycleCoefficients_matrix_det_real (β : Lattice) (j : Fin 3) :
    (thetaEdgeCycleCoefficients β j : ℝ) = (thetaEdgeOrientationSign j : ℝ) *
      Matrix.det !![latticePoint (hexagonRay (thetaEdgeIndex j)) 0,
          realCuspVector (latticePoint β) 0;
        latticePoint (hexagonRay (thetaEdgeIndex j)) 1,
          realCuspVector (latticePoint β) 1] := by
  rw [Matrix.det_fin_two]
  simpa only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, mul_comm] using
    thetaEdgeCycleCoefficients_det_real β j

/-- These coefficients realize the specified integral base displacement
using the three actual oriented edges. -/
theorem thetaEdgeCycleCoefficients_displacement (β : Lattice) :
    (∑ j, (thetaEdgeCycleCoefficients β j : ℝ) • thetaEdgeBaseDisplacement j) =
      latticePoint β := by
  calc
    _ = latticePoint (thetaEdgeCycleLattice (thetaEdgeCycleCoefficients β)) :=
      thetaEdgeBaseDisplacement_sum_int _ (thetaEdgeCycleCoefficients_sum β)
    _ = latticePoint β := congrArg latticePoint (thetaEdgeCycleLattice_coefficients β)

/-- Recovering the integral marking from actual edge displacements. -/
theorem thetaEdgeCycleLattice_eq_of_displacement (m : Fin 3 → ℤ)
    (hm : ∑ j, m j = 0) (β : Lattice)
    (hβ : (∑ j, (m j : ℝ) • thetaEdgeBaseDisplacement j) = latticePoint β) :
    thetaEdgeCycleLattice m = β := by
  have he : latticePoint (thetaEdgeCycleLattice m) = latticePoint β :=
    (thetaEdgeBaseDisplacement_sum_int m hm).symm.trans hβ
  funext i
  have hi := congrFun he i
  change ((thetaEdgeCycleLattice m i : ℤ) : ℝ) = (β i : ℝ) at hi
  exact_mod_cast hi

/-- Zero-sum edge coefficients are determined exactly by their actual
marked planar displacement. -/
theorem thetaEdgeCycle_displacement_eq_iff (m : Fin 3 → ℤ)
    (hm : ∑ j, m j = 0) (β : Lattice) :
    (∑ j, (m j : ℝ) • thetaEdgeBaseDisplacement j) = latticePoint β ↔
      m = thetaEdgeCycleCoefficients β := by
  constructor
  · intro hβ
    rw [← thetaEdgeCycleLattice_eq_of_displacement m hm β hβ]
    exact (thetaEdgeCycleCoefficients_lattice m hm).symm
  · rintro rfl
    exact thetaEdgeCycleCoefficients_displacement β

/-- The actual edge coefficients, with the verified orientation signs,
are the corresponding determinants of the ray and marked cusp vector. -/
theorem thetaEdgeCycle_coefficient_det_of_displacement (m : Fin 3 → ℤ)
    (hm : ∑ j, m j = 0) (β : Lattice)
    (hβ : (∑ j, (m j : ℝ) • thetaEdgeBaseDisplacement j) = latticePoint β) (j : Fin 3) :
    m j = thetaEdgeOrientationSign j *
      (hexagonRay (thetaEdgeIndex j) 0 * cuspVector β 1 -
        hexagonRay (thetaEdgeIndex j) 1 * cuspVector β 0) := by
  rw [(thetaEdgeCycle_displacement_eq_iff m hm β).mp hβ]
  exact thetaEdgeCycleCoefficients_det β j

theorem thetaEdgeCycle_coefficient_matrix_det_real_of_displacement (m : Fin 3 → ℤ)
    (hm : ∑ j, m j = 0) (β : Lattice)
    (hβ : (∑ j, (m j : ℝ) • thetaEdgeBaseDisplacement j) = latticePoint β) (j : Fin 3) :
    (m j : ℝ) = (thetaEdgeOrientationSign j : ℝ) *
      Matrix.det !![latticePoint (hexagonRay (thetaEdgeIndex j)) 0,
          realCuspVector (latticePoint β) 0;
        latticePoint (hexagonRay (thetaEdgeIndex j)) 1,
          realCuspVector (latticePoint β) 1] := by
  rw [(thetaEdgeCycle_displacement_eq_iff m hm β).mp hβ]
  exact thetaEdgeCycleCoefficients_matrix_det_real β j

end Wikipedia.HopfProblem.CuspCentralHomology
