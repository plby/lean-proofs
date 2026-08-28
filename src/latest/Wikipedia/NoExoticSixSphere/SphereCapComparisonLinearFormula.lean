import Wikipedia.NoExoticSixSphere.SphereAxisDilationFiniteCoordinates

/-!
# The fixed-scale cap comparison is an actual ambient linear map

The orthonormal basis in the reference stereographic chart is retained.
Mathlib's scale-two convention makes the comparison at scale two linear:
the source axis maps to minus the reference pole, and the tail maps by the
actual orthogonal-coordinate isometry used by that chart.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization Wikipedia.SmoothSixDPoincare.SphereCoordinates

abbrev capReferencePole : Sphere 3 := referencePole 3

def capTailIsometry : Vector 3 ≃ₗᵢ[ℝ] (ℝ ∙ (-(capReferencePole : Vector 4)))ᗮ := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  exact (referenceIsometry (Vector 3) 3 (by simp)).trans
    (OrthonormalBasis.fromOrthogonalSpanSingleton 3
      (ne_zero_of_mem_unit_sphere (-capReferencePole))).repr.symm

def capComparisonLinear : Vector 4 →ₗ[ℝ] Vector 4 where
  toFun x := (-x 0) • capReferencePole.val + (capTailIsometry (SphereCylinder.tail 2 x)).val
  map_add' x y := by
    simp only [PiLp.add_apply, map_add, Submodule.coe_add, neg_add, add_smul]
    abel
  map_smul' c x := by
    simp only [PiLp.smul_apply, smul_eq_mul, map_smul, Submodule.coe_smul,
      RingHom.id_apply, smul_add, smul_smul]
    rw [mul_neg]

theorem capComparisonLinear_apply (x : Vector 4) :
    capComparisonLinear x =
      (-x 0) • capReferencePole.val + (capTailIsometry (SphereCylinder.tail 2 x)).val := rfl

theorem sourceChart_val (v : Vector 3) :
    (sourceChart v).val = stereoInvFunAux (-capReferencePole.val) (capTailIsometry v).val := by
  rw [referenceChart_apply]
  rfl

theorem sourceComplementChart_val (v : Vector 3) :
    (sourceComplementChart v).val = (1 + 4 * ‖v‖ ^ 2)⁻¹ •
      ((4 * ‖v‖ ^ 2 - 1) • capReferencePole.val + (4 : ℝ) • (capTailIsometry v).val) := by
  change -(sourceChart ((-4 : ℝ) • v)).val = _
  rw [sourceChart_val, map_smul, Submodule.coe_smul, stereoInvFunAux_apply]
  have hu : ‖(capTailIsometry v).val‖ = ‖v‖ := capTailIsometry.norm_map v
  have hn : ‖(-4 : ℝ) • (capTailIsometry v).val‖ ^ 2 = 16 * ‖v‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, hu]
    norm_num
  rw [hn]
  have hd : 1 + 4 * ‖v‖ ^ 2 ≠ 0 := by positivity
  have hd' : 16 * ‖v‖ ^ 2 + 4 ≠ 0 := by positivity
  match_scalars <;> field_simp <;> ring

theorem capComparisonLinear_finite (v : Vector 3) :
    capComparisonLinear (pinchScaledChart 2 (by norm_num) v).val =
      (sourceComplementChart v).val := by
  have hn : ‖(2 : ℝ) • v‖ ^ 2 = 4 * ‖v‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow]
    norm_num
  change capComparisonLinear (pinchFiniteChart ((2 : ℝ) • v)).val = _
  rw [pinchFiniteChart_val, map_smul, capComparisonLinear_apply]
  simp only [SphereCylinder.join_head, SphereCylinder.tail_join, map_smul, Submodule.coe_smul]
  rw [hn, sourceComplementChart_val]
  match_scalars <;> ring

end NoExoticSixSphere.SphereSumNeck
