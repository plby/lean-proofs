import Wikipedia.NoExoticSixSphere.RankSixUnitSpinor

/-!
# Unit vectors in the projected complex line recover the complex structure

A unit vector fixed by the projection determines its rank-one formula.
Consequently every such vector is a spinor representative of the original
orthogonal complex structure, with the explicit Pfaffian sign.
-/

namespace NoExoticSixSphere.RankSixComplexProjection

open RankSixSkewMatrix LinearMap

theorem unitSpinor_ne_zero (q : UnitSpinor) : (q : Spinor) ≠ 0 := by
  intro h
  have hn := unitSpinor_norm q
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

theorem projection_range_eq_span (J : OrthogonalComplexStructures.Space 6)
    (q : UnitSpinor) (hq : projection J q = q) :
    LinearMap.range (projection J).toLinearMap = Submodule.span ℂ {(q : Spinor)} :=
  eq_span_singleton_of_mem_of_finrank_eq_one (projection_finrank J)
    ⟨q, hq⟩ (unitSpinor_ne_zero q)

theorem projection_apply_eq_inner (J : OrthogonalComplexStructures.Space 6)
    (q : UnitSpinor) (hq : projection J q = q) (x : Spinor) :
    projection J x = inner ℂ (q : Spinor) x • (q : Spinor) := by
  have hm : projection J x ∈ Submodule.span ℂ {(q : Spinor)} := by
    rw [← projection_range_eq_span J q hq]
    exact ⟨x, rfl⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
  have hi := congrArg (fun y : Spinor ↦ inner ℂ (q : Spinor) y) hc
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K, unitSpinor_norm,
    RCLike.ofReal_one, one_pow, mul_one] at hi
  rw [← (projection J).adjoint_inner_left x (q : Spinor),
    projection_selfAdjoint, hq] at hi
  exact (hi ▸ hc).symm

theorem projection_eq_rankOne (J : OrthogonalComplexStructures.Space 6)
    (q : UnitSpinor) (hq : projection J q = q) :
    projection J = InnerProductSpace.rankOne ℂ (q : Spinor) (q : Spinor) := by
  apply ContinuousLinearMap.ext
  intro x
  exact projection_apply_eq_inner J q hq x

theorem spinorOuter_eq_lineProjection (J : OrthogonalComplexStructures.Space 6)
    (q : UnitSpinor) (hq : projection J q = q) :
    spinorOuter (fun i ↦ q.1 i) = lineProjection (matrix J) := by
  have h := congrArg
    (fun T : Spinor →L[ℂ] Spinor ↦ Matrix.toEuclideanLin.symm T.toLinearMap)
    (projection_eq_rankOne J q hq)
  rw [InnerProductSpace.symm_toEuclideanLin_rankOne] at h
  change Matrix.toEuclideanLin.symm
    (Matrix.toEuclideanLin (lineProjection (matrix J))) = spinorOuter (fun i ↦ q.1 i) at h
  rw [LinearEquiv.symm_apply_apply] at h
  exact h.symm

theorem fromSpinor_recovers_of_fixed (J : OrthogonalComplexStructures.Space 6)
    (q : UnitSpinor) (hq : projection J q = q) :
    matrix (fromSpinor q) = (-pfaffian (matrix J)) • matrix J :=
  fromSpinor_recovers_signed_matrix J q (spinorOuter_eq_lineProjection J q hq)

end NoExoticSixSphere.RankSixComplexProjection
