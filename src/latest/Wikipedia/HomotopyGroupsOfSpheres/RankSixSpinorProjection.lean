import Wikipedia.NoExoticSixSphere.RankSixPfaffianSign
import Wikipedia.NoExoticSixSphere.RankSixSpinorPhase
import Wikipedia.NoExoticSixSphere.RankSixSpinorNullhomotopy
import Wikipedia.NoExoticSixSphere.RankSixHemisphereSpinor
import Wikipedia.NoExoticSixSphere.Topology.SimplyConnectedSphere

/-!
# The unit-spinor map and its actual complex-line projection

The spinor map takes values in the negative-Pfaffian component. Its line
projection is the rank-one projection onto the original spinor. Consequently
circle phases preserve the map, and every unit vector in the projected line
recovers the corresponding complex structure in that component.
-/

noncomputable section

namespace NoExoticSixSphere.RankSixComplexProjection

open RankSixSkewMatrix

def axisSpinor : UnitSpinor :=
  ⟨EuclideanSpace.basisFun (Fin 4) ℂ 0, by
    simpa only [Metric.mem_sphere, dist_zero_right] using
      (EuclideanSpace.basisFun (Fin 4) ℂ).orthonormal.1 0⟩

private theorem vecCons_five {α : Type*} {n : ℕ} (a : α) (v : Fin (n + 5) → α) :
    Matrix.vecCons a v (5 : Fin (n + 6)) = v 4 := rfl

theorem pfaffian_fromSpinor_axis : pfaffian (matrix (fromSpinor axisSpinor)) = -1 := by
  rw [matrix_fromSpinor]
  have hq : (fun i : Fin 4 ↦ axisSpinor.val i) = ![1, 0, 0, 0] := by
    funext i
    fin_cases i <;> simp [axisSpinor, EuclideanSpace.basisFun_apply]
  rw [hq]
  norm_num [pfaffian, spinorMatrix, skew, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, vecCons_five]

theorem pfaffian_fromSpinor (q : UnitSpinor) : pfaffian (matrix (fromSpinor q)) = -1 := by
  let : PathConnectedSpace UnitSpinor :=
    unitSpinorHomeomorph.symm.surjective.pathConnectedSpace unitSpinorHomeomorph.symm.continuous
  exact (pfaffian_constant ⟨fromSpinor, continuous_fromSpinor⟩ q axisSpinor).trans
    pfaffian_fromSpinor_axis

theorem lineProjection_fromSpinor (q : UnitSpinor) :
    lineProjection (matrix (fromSpinor q)) = spinorOuter (fun i ↦ q.val i) := by
  rw [lineProjection, pfaffian_fromSpinor, matrix_fromSpinor, spinorMatrix_spin,
    unitSpinor_normSq]
  simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_one_smul, one_smul, sub_neg_eq_add]
  module

theorem projection_fromSpinor (q : UnitSpinor) :
    projection (fromSpinor q) = InnerProductSpace.rankOne ℂ (q : Spinor) (q : Spinor) := by
  apply ContinuousLinearMap.coe_injective
  change Matrix.toEuclideanLin (lineProjection (matrix (fromSpinor q))) =
    (InnerProductSpace.rankOne ℂ (q : Spinor) (q : Spinor)).toLinearMap
  apply Matrix.toEuclideanLin.symm.injective
  rw [LinearEquiv.symm_apply_apply, InnerProductSpace.symm_toEuclideanLin_rankOne,
    lineProjection_fromSpinor]
  rfl

theorem projection_fromSpinor_fixed (q : UnitSpinor) :
    projection (fromSpinor q) q = (q : Spinor) := by
  rw [projection_fromSpinor, InnerProductSpace.rankOne_apply, inner_self_eq_norm_sq_to_K,
    unitSpinor_norm]
  simp

theorem fromSpinor_eq_of_fixed (J : OrthogonalComplexStructures.Space 6)
    (hJ : pfaffian (matrix J) = -1) (q : UnitSpinor)
    (hq : projection J q = (q : Spinor)) : fromSpinor q = J := by
  apply matrix_injective
  rw [fromSpinor_recovers_of_fixed J q hq, hJ, neg_neg, one_smul]

theorem fromSpinor_phaseSmul (z : Circle) (q : UnitSpinor) :
    fromSpinor (phaseSmul z q) = fromSpinor q :=
  fromSpinor_eq_of_fixed _ (pfaffian_fromSpinor q) _
    (phaseSmul_fixed _ q (projection_fromSpinor_fixed q) z)

theorem exists_unit_fixed (J : OrthogonalComplexStructures.Space 6) :
    ∃ q : UnitSpinor, projection J q = (q : Spinor) := by
  obtain ⟨v, hv, hfix⟩ := exists_nonzero_fixed J
  let q : UnitSpinor := ⟨NormedSpace.normalize v, by
    simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hv⟩
  refine ⟨q, ?_⟩
  change realProjection J (‖v‖⁻¹ • v) = ‖v‖⁻¹ • v
  rw [map_smul]
  exact congrArg (fun w : Spinor ↦ ‖v‖⁻¹ • w) hfix

theorem range_fromSpinor :
    Set.range fromSpinor = {J | pfaffian (matrix J) = -1} := by
  ext J
  constructor
  · rintro ⟨q, rfl⟩
    exact pfaffian_fromSpinor q
  · intro hJ
    obtain ⟨q, hq⟩ := exists_unit_fixed J
    exact ⟨q, fromSpinor_eq_of_fixed J hJ q hq⟩

end NoExoticSixSphere.RankSixComplexProjection
