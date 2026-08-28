import Wikipedia.HopfProblem.ToricBlowdown

/-!
# Exact local models for the global blow-down

The inverse image of each standard projective affine patch is exactly
one of the three open affine blow-ups constructed on the toric surface.
Thus the local blow-down descriptions are exhaustive, not merely maps
from some open subsets of those inverse images.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.ToricComponent

open ToricCharts ToricFan ToricSpace Triangle

theorem affineInclusion_mem_range_iff_changeSource {v : Fin 2 → ℤ}
    (c d : ChartIndex v) (z : CoordinateSpace 2) :
    affineInclusion c z ∈ range (affineInclusion d) ↔
      insertZero c.coordinate z ∈ (chartChange c.triangle d.triangle).source := by
  constructor
  · intro hz
    exact (parametrization_transition c d hz).1
  · intro hz
    rw [affineInclusion_mem_range_iff]
    refine ⟨chartChange c.triangle d.triangle (insertZero c.coordinate z), ?_⟩
    exact ((inclusion_eq_iff _ _ _ _).mpr ⟨hz, rfl⟩).symm

/-- A chart of the target blow-up that suffices for each source chart.
Where both affine coordinates are nonzero either choice would work. -/
def blowdownTargetSide (k : Fin 3) (i : Fin 6) : Bool :=
  ![![false, true, true, false, false, false],
    ![false, false, false, true, true, false],
    ![true, false, false, false, false, true]] k i

theorem blowdownTargetSide_source (k : Fin 3) (i : Fin 6) (z : CoordinateSpace 2)
    (hz : ProjectivePlane.homogeneous (blowdownIndex i) (blowdownCoordinates i z) k ≠ 0) :
    insertZero (zeroCoordinate i) z ∈
      (chartChange (zeroTriangle i)
        (zeroTriangle (blowupIndex k (blowdownTargetSide k i)))).source := by
  rw [chartChange_source, zeroChartVector]
  fin_cases k <;> fin_cases i <;>
    norm_num [ProjectivePlane.homogeneous, blowdownCoordinates, blowdownIndex,
      blowdownTargetSide, blowupIndex, zeroTriangle, domain, transition, dual, rays,
      Matrix.mul_apply, Fin.sum_univ_succ, Fin.forall_fin_succ, Matrix.cons_val,
      Fin.ext_iff] at hz ⊢ <;> simp_all [mul_eq_zero]

/-- Each projective affine patch has exactly the claimed affine blow-up as
its inverse image under the global map. -/
theorem blowdown_preimage_affineTarget (k : Fin 3) :
    blowdown ⁻¹' ProjectivePlane.affineTarget k = range (blowupMap k) := by
  ext x
  constructor
  · intro hx
    obtain ⟨c, z, rfl⟩ := affineInclusion_jointly_surjective x
    obtain ⟨i, rfl⟩ := zeroChart_surjective c
    have ht : zeroChartBlowdown i z ∈ ProjectivePlane.affineTarget k := by
      simpa only [mem_preimage, blowdown_zeroChart] using hx
    have hp : ProjectivePlane.homogeneous (blowdownIndex i) (blowdownCoordinates i z) k ≠ 0 :=
      (ProjectivePlane.quotientMap_mem_affineTarget_iff k _).mp ht
    let b := blowdownTargetSide k i
    have hmem : affineInclusion (zeroChart i) z ∈
        range (affineInclusion (zeroChart (blowupIndex k b))) :=
      (affineInclusion_mem_range_iff_changeSource _ _ z).mpr (blowdownTargetSide_source k i z hp)
    obtain ⟨w, hw⟩ := hmem
    refine ⟨AffineBlowup.affineMap b (reorder k b w), ?_⟩
    rw [blowupMap_affineMap]
    unfold blowupAffine
    rw [reorder_involutive]
    exact hw
  · rintro ⟨y, rfl⟩
    rw [mem_preimage, blowdown_blowupMap]
    exact ProjectivePlane.affineMap_mem_target k _

theorem blowdown_mem_affineTarget_iff (k : Fin 3) (x : rayDivisor 0) :
    blowdown x ∈ ProjectivePlane.affineTarget k ↔ x ∈ blowupOpenSet k := by
  change x ∈ blowdown ⁻¹' ProjectivePlane.affineTarget k ↔ x ∈ range (blowupMap k)
  rw [blowdown_preimage_affineTarget]

/-- The local coordinate of the global blow-down on a complete inverse
image of a standard projective affine chart. -/
theorem blowdown_affine_local_model (k : Fin 3) (x : AffineBlowup.Space) :
    ProjectivePlane.affineCoords k
      (blowdown (blowupBiholomorph k x : rayDivisor 0)) = AffineBlowup.projection x := by
  change ProjectivePlane.affineCoords k (blowdown (blowupMap k x)) = _
  rw [blowdown_blowupMap, ProjectivePlane.affineCoords_affineMap]

end Wikipedia.HopfProblem.ToricComponent
