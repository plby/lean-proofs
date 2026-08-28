import Wikipedia.HopfProblem.DegreeCollapseImmersedCornerCoordinates
import Wikipedia.HopfProblem.OrbitPairOrientationWeights

/-!
# The determinant comparison with the original source-coordinate factors

The original tangent maps factor through their induced sheet coordinates
and the actual forward tubular differential. Taking determinants retains
both source factors, the tubular factor, and the one fixed coordinate
factor. No derivative of an invented global inverse is used.
-/

noncomputable section

open Function

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedCorner

open Wikipedia.SmoothSixDPoincare WhitneyPairModel FrameField
open OrbitPair.MixedChartDeterminant

variable {G E : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  (J : Sheet ≃L[ℝ] G) (K : (G × G) ≃L[ℝ] E)

theorem det_original_sheet_comparison (T : NormalSpace →L[ℝ] E)
    (P Q : Sheet →L[ℝ] NormalSpace) (U V : G →L[ℝ] Sheet) (F H : G →L[ℝ] E)
    (hF : T.comp (P.comp U) = F) (hH : T.comp (Q.comp V) = H) :
    (IntersectionCoordinates.jointBlock normalPairCoordinates P Q).det *
        (T.comp (tubeCoordinates J K).toContinuousLinearMap).det * coordinateScale J K *
        (J.toContinuousLinearMap.comp U).det * (J.toContinuousLinearMap.comp V).det =
      (K.symm.toContinuousLinearMap.comp (F.coprod H)).det := by
  let M := IntersectionCoordinates.jointBlock normalPairCoordinates P Q
  let C := T.comp (tubeCoordinates J K).toContinuousLinearMap
  let A := J.toContinuousLinearMap.comp U
  let B := J.toContinuousLinearMap.comp V
  let D := K.symm.toContinuousLinearMap.comp (C.comp
    ((targetCoordinates J K).toContinuousLinearMap.comp
      (M.comp (sourceCoordinates J).toContinuousLinearMap)))
  have hc (z : Space) : C (targetCoordinates J K z) = T (normalCoordinates z) := by
    change T (tubeCoordinates J K (targetCoordinates J K z)) = _
    rw [tube_target_coordinates]
  have hcomp : D.comp (A.prodMap B) = K.symm.toContinuousLinearMap.comp (F.coprod H) := by
    apply ContinuousLinearMap.ext
    rintro ⟨u, v⟩
    change K.symm (C (targetCoordinates J K (M (sourceCoordinates J (A u, B v))))) =
      K.symm (F u + H v)
    rw [hc, normal_jointBlock_source]
    change K.symm (T (P (J.symm (J (U u))) + Q (J.symm (J (V v))))) = _
    rw [J.symm_apply_apply, J.symm_apply_apply, map_add]
    exact congrArg K.symm (congrArg₂ (· + ·)
      (congrArg (fun L : G →L[ℝ] E => L u) hF)
      (congrArg (fun L : G →L[ℝ] E => L v) hH))
  have hbase : M.det * C.det * coordinateScale J K = D.det :=
    det_of_comparison_square K (sourceCoordinates J) (targetCoordinates J K) C M D rfl
  have hdet : D.det * (A.det * B.det) =
      (K.symm.toContinuousLinearMap.comp (F.coprod H)).det := by
    have he := congrArg (fun L : (G × G) →L[ℝ] (G × G) => L.det) hcomp
    have hprod : (D.comp (A.prodMap B)).det = D.det * (A.det * B.det) := by
      change (D.toLinearMap.comp (A.toLinearMap.prodMap B.toLinearMap)).det = _
      rw [LinearMap.det_comp, LinearMap.det_prodMap]
    exact hprod.symm.trans he
  change M.det * C.det * coordinateScale J K * A.det * B.det = _
  rw [hbase]
  exact (mul_assoc _ _ _).trans hdet

theorem normalize_source_comparison {m c k a b d : ℝ} (u v w : Bool)
    (h : m * c * k * a * b = d) :
    m * (OrbitPair.OrientationWeights.weight w * c) *
        (OrbitPair.OrientationWeights.weight u * a) *
        (OrbitPair.OrientationWeights.weight v * b) * k =
      OrbitPair.OrientationWeights.weight (Bool.xor (Bool.xor u v) w) * d := by
  rw [OrbitPair.OrientationWeights.weight_xor, OrbitPair.OrientationWeights.weight_xor]
  calc
    _ = (OrbitPair.OrientationWeights.weight u * OrbitPair.OrientationWeights.weight v *
        OrbitPair.OrientationWeights.weight w) * (m * c * k * a * b) := by ring
    _ = _ := by rw [h]

theorem negative_product_of_source_comparison
    {m₀ m₁ c₀ c₁ a₀ a₁ b₀ b₁ d₀ d₁ k : ℝ}
    (h₀ : m₀ * c₀ * a₀ * b₀ * k = d₀) (h₁ : m₁ * c₁ * a₁ * b₁ * k = d₁)
    (hk : k ≠ 0) (hc : 0 < c₀ * c₁) (ha : 0 < a₀ * a₁) (hb : 0 < b₀ * b₁)
    (hd : d₀ * d₁ < 0) : m₀ * m₁ < 0 := by
  have heq : (m₀ * m₁) * ((c₀ * c₁) * (a₀ * a₁) * (b₀ * b₁) * k ^ 2) = d₀ * d₁ := by
    calc
      _ = (m₀ * c₀ * a₀ * b₀ * k) * (m₁ * c₁ * a₁ * b₁ * k) := by ring
      _ = _ := congrArg₂ (· * ·) h₀ h₁
  have hscale : 0 < (c₀ * c₁) * (a₀ * a₁) * (b₀ * b₁) * k ^ 2 :=
    mul_pos (mul_pos (mul_pos hc ha) hb) (sq_pos_of_ne_zero hk)
  have hneg : (m₀ * m₁) * ((c₀ * c₁) * (a₀ * a₁) * (b₀ * b₁) * k ^ 2) < 0 := heq ▸ hd
  by_contra hm
  exact (not_lt_of_ge (mul_nonneg (le_of_not_gt hm) hscale.le)) hneg

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedCorner
