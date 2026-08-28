import Wikipedia.SmoothSixDPoincare.ComplementCoefficientSigns

/-!
# Compare full intersection signs with a fixed normal detector

A surjective normal detector annihilating one sheet factors through the
quotient supplied by any actual complementary frame. Both the full splitting
and its normal coefficient are invertible along that sheet. Their endpoint
determinant products are positive, so they introduce no change in the
opposite-intersection-sign condition.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.FrameField

variable {D Z F : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A normal detector killing the first sheet factors through the actual complementary quotient. -/
theorem normalDetector_eq_comp_quotient (G : D →L[ℝ] F) (C : Z →L[ℝ] F) (Q : F →L[ℝ] Z)
    (hi : (G.coprod C).IsInvertible) (hQG : Q.comp G = 0) :
    Q = (Q.comp C).comp (complementQuotient G C) := by
  apply ContinuousLinearMap.ext
  intro v
  let w := (G.coprod C).inverse v
  have hv : G w.1 + C w.2 = v := hi.self_apply_inverse v
  have hzero : Q (G w.1) = 0 := congrArg (fun L : D →L[ℝ] Z => L w.1) hQG
  change Q v = Q (C w.2)
  rw [← hv, map_add, hzero, zero_add]

variable [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z]

/-- The tangent and normal determinants differ by the two actual frame factors. -/
theorem det_intersection_mul_normalComplement
    (j : (D × Z) ≃L[ℝ] F) (G : D →L[ℝ] F) (C L : Z →L[ℝ] F) (Q : F →L[ℝ] Z)
    (hi : (G.coprod C).IsInvertible) (hQG : Q.comp G = 0) :
    (j.symm.toContinuousLinearMap.comp (G.coprod L)).det * (Q.comp C).det =
      (j.symm.toContinuousLinearMap.comp (G.coprod C)).det * (Q.comp L).det := by
  have hnormal : Q.comp L = (Q.comp C).comp ((complementQuotient G C).comp L) := by
    have h := normalDetector_eq_comp_quotient G C Q hi hQG
    exact congrArg (fun R : F →L[ℝ] Z => R.comp L) h
  have hdet : (Q.comp L).det = (Q.comp C).det * ((complementQuotient G C).comp L).det := by
    rw [hnormal]
    exact LinearMap.det_comp _ _
  have hframe : (j.symm.toContinuousLinearMap.comp (G.coprod L)).det =
      (j.symm.toContinuousLinearMap.comp (G.coprod C)).det *
        ((complementQuotient G C).comp L).det :=
    det_frame_eq_det_split_mul_det_coefficient j G C L hi
  rw [hframe, hdet]
  ring

/-- A continuous actual normal detector and complement preserve the opposite-pair sign condition. -/
theorem opposite_intersectionDet_iff_normalDet
    (j : (D × Z) ≃L[ℝ] F) (G : ℝ → (D →L[ℝ] F)) (C L : ℝ → (Z →L[ℝ] F))
    (Q : ℝ → (F →L[ℝ] Z))
    (hG : ContDiffOn ℝ ∞ G (Icc (0 : ℝ) 1))
    (hC : ContDiffOn ℝ ∞ C (Icc (0 : ℝ) 1))
    (hQ : ContDiffOn ℝ ∞ Q (Icc (0 : ℝ) 1))
    (hi : ∀ t ∈ Icc (0 : ℝ) 1, ((G t).coprod (C t)).IsInvertible)
    (hQs : ∀ t ∈ Icc (0 : ℝ) 1, Surjective (Q t))
    (hQG : ∀ t ∈ Icc (0 : ℝ) 1, (Q t).comp (G t) = 0) :
    ((j.symm.toContinuousLinearMap.comp ((G 0).coprod (L 0))).det *
      (j.symm.toContinuousLinearMap.comp ((G 1).coprod (L 1))).det < 0) ↔
      ((Q 0).comp (L 0)).det * ((Q 1).comp (L 1)).det < 0 := by
  let T (t : ℝ) := j.symm.toContinuousLinearMap.comp ((G t).coprod (C t))
  let K (t : ℝ) := (Q t).comp (C t)
  have hT : ContDiffOn ℝ ∞ T (Icc (0 : ℝ) 1) :=
    contDiffOn_const.clm_comp (contDiffOn_coprod hG hC)
  have hK : ContDiffOn ℝ ∞ K (Icc (0 : ℝ) 1) := hQ.clm_comp hC
  have hTpos := det_mul_endpoints_pos hT.continuousOn
    (fun t ht => j.symm.bijective.comp (hi t ht).bijective)
  have hKpos := det_mul_endpoints_pos hK.continuousOn
    (fun t ht => TransverseCoordinates.bijective_normal_comp (Q t) (G t) (C t)
      (hQs t ht) (hi t ht).surjective (hQG t ht) rfl)
  have h₀ := det_intersection_mul_normalComplement j (G 0) (C 0) (L 0) (Q 0)
    (hi 0 (by simp)) (hQG 0 (by simp))
  have h₁ := det_intersection_mul_normalComplement j (G 1) (C 1) (L 1) (Q 1)
    (hi 1 (by simp)) (hQG 1 (by simp))
  let a := (j.symm.toContinuousLinearMap.comp ((G 0).coprod (L 0))).det *
    (j.symm.toContinuousLinearMap.comp ((G 1).coprod (L 1))).det
  let b := ((Q 0).comp (L 0)).det * ((Q 1).comp (L 1)).det
  have heq : a * ((K 0).det * (K 1).det) = ((T 0).det * (T 1).det) * b := by
    dsimp [a, b, T, K]
    calc
      _ = ((j.symm.toContinuousLinearMap.comp ((G 0).coprod (L 0))).det *
          ((Q 0).comp (C 0)).det) *
          ((j.symm.toContinuousLinearMap.comp ((G 1).coprod (L 1))).det *
          ((Q 1).comp (C 1)).det) := by ring
      _ = _ := by rw [h₀, h₁]; ring
  change a < 0 ↔ b < 0
  constructor
  · intro ha
    have hn : ((T 0).det * (T 1).det) * b < 0 :=
      heq ▸ mul_neg_of_neg_of_pos ha hKpos
    rcases mul_neg_iff.mp hn with ⟨_, hb⟩ | ⟨ht, _⟩
    · exact hb
    · exact (not_lt_of_gt hTpos ht).elim
  · intro hb
    have hn : a * ((K 0).det * (K 1).det) < 0 :=
      heq.symm ▸ mul_neg_of_pos_of_neg hTpos hb
    rcases mul_neg_iff.mp hn with ⟨_, hk⟩ | ⟨ha, _⟩
    · exact (not_lt_of_gt hKpos hk).elim
    · exact ha

end Wikipedia.SmoothSixDPoincare.FrameField
