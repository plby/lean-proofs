import Wikipedia.HopfProblem.ToricBlowupOpenSets
import Wikipedia.HopfProblem.ToricComponentGluing
import Wikipedia.HopfProblem.ProjectivePlaneManifold
import Wikipedia.HopfProblem.AffineBlowupTopology

/-!
# The global holomorphic blow-down to the projective plane

The six polynomial affine maps descend to a map from the actual compact
toric ray surface to the actual scalar-quotient complex projective plane.
On each of the three open affine blow-ups, it is precisely the incidence
model's blow-down followed by the corresponding projective affine chart.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.ToricComponent

open ToricCharts ToricFan ToricSpace Triangle

def blowdownIndex : Fin 6 → Fin 3 := ![0, 0, 1, 1, 2, 2]

def blowdownCoordinates (i : Fin 6) (z : CoordinateSpace 2) : CoordinateSpace 2 :=
  ![![z 0 * z 1, z 1], ![z 1, z 0 * z 1], ![z 0 * z 1, z 0],
    ![z 1, z 0 * z 1], ![z 0 * z 1, z 1], ![z 0, z 0 * z 1]] i

theorem blowdownCoordinates_holomorphic (i : Fin 6) :
    ContDiff ℂ ω (blowdownCoordinates i) := by
  have hp : ContDiff ℂ ω (fun z : CoordinateSpace 2 => z 0 * z 1) :=
    (contDiff_apply ℂ ℂ 0).mul (contDiff_apply ℂ ℂ 1)
  have h0 : ContDiff ℂ ω (fun z : CoordinateSpace 2 => ![z 0 * z 1, z 1]) := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j
    · exact hp
    · exact contDiff_apply ℂ ℂ 1
  have h1 : ContDiff ℂ ω (fun z : CoordinateSpace 2 => ![z 1, z 0 * z 1]) := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j
    · exact contDiff_apply ℂ ℂ 1
    · exact hp
  have h2 : ContDiff ℂ ω (fun z : CoordinateSpace 2 => ![z 0 * z 1, z 0]) := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j
    · exact hp
    · exact contDiff_apply ℂ ℂ 0
  have h3 : ContDiff ℂ ω (fun z : CoordinateSpace 2 => ![z 0, z 0 * z 1]) := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j
    · exact contDiff_apply ℂ ℂ 0
    · exact hp
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h1
  · exact h0
  · exact h3

def zeroChartBlowdown (i : Fin 6) : CoordinateSpace 2 → ProjectivePlane.Space :=
  ProjectivePlane.affineMap (blowdownIndex i) ∘ blowdownCoordinates i

theorem zeroChartBlowdown_holomorphic (i : Fin 6) :
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (zeroChartBlowdown i) :=
  (ProjectivePlane.affineMap_holomorphic _).comp (blowdownCoordinates_holomorphic i).contMDiff

def chartBlowdown (c : ChartIndex 0) : CoordinateSpace 2 → ProjectivePlane.Space :=
  zeroChartBlowdown (zeroChartEquiv.symm c)

@[simp] theorem chartBlowdown_zeroChart (i : Fin 6) (z : CoordinateSpace 2) :
    chartBlowdown (zeroChart i) z = zeroChartBlowdown i z := by
  change zeroChartBlowdown (zeroChartEquiv.symm (zeroChartEquiv i)) z = _
  rw [Equiv.symm_apply_apply]

theorem chartBlowdown_holomorphic (c : ChartIndex 0) :
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (chartBlowdown c) :=
  zeroChartBlowdown_holomorphic _

def referenceCoordinates (i : Fin 6) (z : CoordinateSpace 2) : CoordinateSpace 2 :=
  ![z, ![(z 0)⁻¹, z 0 * z 1], ![(z 0 * z 1)⁻¹, z 1],
    ![(z 1)⁻¹, (z 0)⁻¹], ![z 1, (z 0 * z 1)⁻¹], ![z 0 * z 1, (z 0)⁻¹]] i

def referenceTransitionMatrix : Fin 6 → Matrix (Fin 3) (Fin 3) ℤ :=
  ![1, !![1, 1, 0; 0, -1, 0; 0, 1, 1],
    !![2, 1, 1; -1, 0, -1; 0, 0, 1], !![2, 2, 1; 0, -1, 0; -1, 0, 0],
    !![2, 1, 1; 0, 1, 0; -1, -1, 0], !![1, 1, 0; 1, 0, 1; -1, 0, 0]]

theorem referenceTransition (i : Fin 6) :
    transition (zeroTriangle i) (zeroTriangle 0) = referenceTransitionMatrix i := by
  fin_cases i <;> decide

theorem zeroChartVector (i : Fin 6) (z : CoordinateSpace 2) :
    insertZero (zeroCoordinate i) z =
      ![![0, z 0, z 1], ![0, z 0, z 1], ![z 0, 0, z 1],
        ![z 0, z 1, 0], ![z 0, z 1, 0], ![z 0, 0, z 1]] i := by
  fin_cases i <;> ext j <;> fin_cases j <;> rfl

private theorem removeZero_monomial (A : Matrix (Fin 3) (Fin 3) ℤ)
    (z : CoordinateSpace 3) :
    removeCoordinate 0 (monomial A z) =
      ![z 0 ^ A 1 0 * z 1 ^ A 1 1 * z 2 ^ A 1 2,
        z 0 ^ A 2 0 * z 1 ^ A 2 1 * z 2 ^ A 2 2] := by
  ext j
  fin_cases j
  · change (∏ k, z k ^ A 1 k) = _
    simp [Fin.prod_univ_succ, mul_assoc]
  · change (∏ k, z k ^ A 2 k) = _
    simp [Fin.prod_univ_succ, mul_assoc]

theorem referenceCoordinates_change (i : Fin 6) (z : CoordinateSpace 2) :
    removeCoordinate 0 (chartChange (zeroTriangle i) (zeroTriangle 0)
      (insertZero (zeroCoordinate i) z)) = referenceCoordinates i z := by
  change removeCoordinate 0 (monomial (transition _ _) _) = _
  rw [referenceTransition, zeroChartVector, removeZero_monomial]
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [referenceTransitionMatrix, referenceCoordinates,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.vecHead, Matrix.vecTail, mul_comm, Fin.ext_iff]

theorem referenceCoordinates_chart (i : Fin 6) {z : CoordinateSpace 2} (hz : z ∈ torus) :
    (parametrization (zeroChart 0)).symm (affineInclusion (zeroChart i) z) =
      referenceCoordinates i z := by
  have h := parametrization_transition (zeroChart i) (zeroChart 0)
    (affineInclusion_torus_mem_range (zeroChart i) (zeroChart 0) hz)
  exact h.2.trans (referenceCoordinates_change i z)

def homogeneousMultiplier (i : Fin 6) (z : CoordinateSpace 2) : ℂ :=
  ![1, 1, z 0, z 0 * z 1, z 0 * z 1, z 0] i

theorem zeroChartBlowdown_reference (i : Fin 6) {z : CoordinateSpace 2} (hz : z ∈ torus) :
    zeroChartBlowdown i z = zeroChartBlowdown 0 (referenceCoordinates i z) := by
  apply (ProjectivePlane.quotientMap_eq_iff_scalar _ _).mpr
  refine ⟨homogeneousMultiplier i z, ?_⟩
  have h0 := hz 0
  have h1 := hz 1
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [ProjectivePlane.homogeneous, blowdownCoordinates, blowdownIndex,
      referenceCoordinates, homogeneousMultiplier, Matrix.cons_val, Pi.smul_apply,
      smul_eq_mul, h0, h1] <;> field_simp [h0, h1]

theorem chartBlowdown_compatible (c d : ChartIndex 0) (z w : CoordinateSpace 2)
    (he : affineInclusion c z = affineInclusion d w) : chartBlowdown c z = chartBlowdown d w := by
  apply compatible_of_reference_torus chartBlowdown (zeroChart 0)
    (fun c => (chartBlowdown_holomorphic c).continuous) ?_ c d z w he
  intro c z hz
  obtain ⟨i, rfl⟩ := zeroChart_surjective c
  rw [chartBlowdown_zeroChart, referenceCoordinates_chart i hz, chartBlowdown_zeroChart]
  exact zeroChartBlowdown_reference i hz

/-- The global map obtained by gluing the six polynomial blow-down charts. -/
def blowdown : rayDivisor 0 → ProjectivePlane.Space := descend chartBlowdown

@[simp] theorem blowdown_affineInclusion (c : ChartIndex 0) (z : CoordinateSpace 2) :
    blowdown (affineInclusion c z) = chartBlowdown c z :=
  descend_affineInclusion chartBlowdown chartBlowdown_compatible c z

@[simp] theorem blowdown_zeroChart (i : Fin 6) (z : CoordinateSpace 2) :
    blowdown (affineInclusion (zeroChart i) z) = zeroChartBlowdown i z := by
  rw [blowdown_affineInclusion, chartBlowdown_zeroChart]

theorem blowdown_holomorphic :
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω blowdown :=
  descend_holomorphic chartBlowdown chartBlowdown_compatible _ chartBlowdown_holomorphic

theorem blowdown_continuous : Continuous blowdown := blowdown_holomorphic.continuous

theorem blowdown_isProperMap : IsProperMap blowdown := blowdown_continuous.isProperMap

theorem blowdownIndex_blowupIndex (k : Fin 3) (b : Bool) :
    blowdownIndex (blowupIndex k b) = k := by
  fin_cases k <;> cases b <;> decide

theorem blowdownCoordinates_reorder (k : Fin 3) (b : Bool) (z : CoordinateSpace 2) :
    blowdownCoordinates (blowupIndex k b) (reorder k b z) =
      AffineBlowup.projection (AffineBlowup.affineMap b z) := by
  fin_cases k <;> cases b <;> ext i <;> fin_cases i <;>
    simp [blowdownCoordinates, blowupIndex, reorder, AffineBlowup.projection,
      AffineBlowup.affineMap, AffineBlowup.left, AffineBlowup.right, Matrix.cons_val,
      Fin.ext_iff, mul_comm]

@[simp] theorem blowdown_blowupAffine (k : Fin 3) (b : Bool) (z : CoordinateSpace 2) :
    blowdown (blowupAffine k b z) =
      ProjectivePlane.affineMap k (AffineBlowup.projection (AffineBlowup.affineMap b z)) := by
  change blowdown (affineInclusion (zeroChart (blowupIndex k b)) (reorder k b z)) = _
  rw [blowdown_zeroChart]
  change ProjectivePlane.affineMap _ (blowdownCoordinates _ _) = _
  rw [blowdownIndex_blowupIndex, blowdownCoordinates_reorder]

/-- On each open affine blow-up the global map is exactly its blow-down. -/
@[simp] theorem blowdown_blowupMap (k : Fin 3) (x : AffineBlowup.Space) :
    blowdown (blowupMap k x) = ProjectivePlane.affineMap k (AffineBlowup.projection x) := by
  obtain ⟨b, z, rfl⟩ := AffineBlowup.affineMap_jointly_surjective x
  rw [blowupMap_affineMap, blowdown_blowupAffine]

theorem blowdown_surjective : Function.Surjective blowdown := by
  intro x
  obtain ⟨k, z, rfl⟩ := ProjectivePlane.affineMap_jointly_surjective x
  obtain ⟨y, hy⟩ := AffineBlowup.projection_surjective z
  refine ⟨blowupMap k y, ?_⟩
  rw [blowdown_blowupMap, hy]

end Wikipedia.HopfProblem.ToricComponent
