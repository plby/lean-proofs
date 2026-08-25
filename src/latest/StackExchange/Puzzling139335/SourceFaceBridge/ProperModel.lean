import StackExchange.Puzzling139335.SourceFaceBridge.Defs

/-!
# Source containment implies the finite scalar model

Every point of the source belongs to the lower half-square and to both
inverse-image strips.  The second strip is the same for either parity of the
left placement.  Applying these bounds to the distinguished source points
produces `ProperRotation.Model` without any additional scalar hypotheses.
-/

open Set

namespace Puzzling139335.SourceFaceBridge

namespace SupportedSource

variable {d : FaceData} {reversed : Bool} {P : Set Plane}

/-- Source-box containment and the two square placements give all twelve
scalar inequalities for every actual source point, for either left parity. -/
theorem pointValid (h : SupportedSource d reversed P) {p : Plane} (hp : p ∈ P) :
    ProperRotation.PointValid d.scalarData (p 0) (p 1) := by
  have hsource := h.source_subset hp
  have hright := h.right_fits hp
  have hleft := h.left_fits hp
  change (p 0 ∈ Icc (0 : ℝ) 1) ∧ (p 1 ∈ Icc (0 : ℝ) (1 / 2)) at hsource
  change (1 + d.normal₁ p - d.normal₁ d.M₁ ∈ Icc (0 : ℝ) 1) ∧
    (1 / 2 + d.tangent₁ p - d.tangent₁ d.M₁ ∈ Icc (0 : ℝ) 1) at hright
  have hleftBounds :
      d.normal₂ d.M₂ - 1 ≤ d.normal₂ p ∧
      d.normal₂ p ≤ d.normal₂ d.M₂ ∧
      d.tangent₂ d.M₂ - 1 / 2 ≤ d.tangent₂ p ∧
      d.tangent₂ p ≤ d.tangent₂ d.M₂ + 1 / 2 := by
    cases reversed with
    | false =>
        change (d.normal₂ d.M₂ - d.normal₂ p ∈ Icc (0 : ℝ) 1) ∧
          (1 / 2 - d.tangent₂ p + d.tangent₂ d.M₂ ∈ Icc (0 : ℝ) 1) at hleft
        rcases hleft with ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    | true =>
        change (d.normal₂ d.M₂ - d.normal₂ p ∈ Icc (0 : ℝ) 1) ∧
          (1 / 2 + d.tangent₂ p - d.tangent₂ d.M₂ ∈ Icc (0 : ℝ) 1) at hleft
        rcases hleft with ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  refine
    { x_nonneg := hsource.1.1
      x_le_one := hsource.1.2
      y_nonneg := hsource.2.1
      y_le_half := hsource.2.2
      normal1_lower := ?_
      normal1_upper := ?_
      tangent1_lower := ?_
      tangent1_upper := ?_
      normal2_lower := hleftBounds.1
      normal2_upper := hleftBounds.2.1
      tangent2_lower := hleftBounds.2.2.1
      tangent2_upper := hleftBounds.2.2.2 }
  · change d.normal₁ d.M₁ - 1 ≤ d.normal₁ p
    linarith only [hright.1.1]
  · change d.normal₁ p ≤ d.normal₁ d.M₁
    linarith only [hright.1.2]
  · change d.tangent₁ d.M₁ - 1 / 2 ≤ d.tangent₁ p
    linarith only [hright.2.1]
  · change d.tangent₁ p ≤ d.tangent₁ d.M₁ + 1 / 2
    linarith only [hright.2.2]

/-- The finite scalar model follows from actual distinguished-point
membership and the two geometric square placements, for either parity. -/
theorem toProperModel (h : SupportedSource d reversed P) :
    ProperRotation.Model d.scalarData := by
  have hπ := Real.pi_pos
  refine
    { c_pos := ?_
      s_pos := ?_
      d_pos := ?_
      q_pos := ?_
      cs_circle := Real.cos_sq_add_sin_sq d.α
      dq_circle := Real.cos_sq_add_sin_sq d.β
      a_pos := h.a_pos
      a_lt_half := h.a_lt_half
      b_pos := h.b_pos
      b_lt_half := h.b_lt_half
      origin := ?_
      base_right := ?_
      left_top := ?_
      right_top := ?_
      face1_minus := ?_
      face1_plus := ?_
      face2_minus := ?_
      face2_plus := ?_ }
  · change 0 < Real.cos d.α
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [h.alpha_pos], h.alpha_lt_half_pi⟩
  · change 0 < Real.sin d.α
    exact Real.sin_pos_of_mem_Ioo ⟨h.alpha_pos, by linarith [h.alpha_lt_half_pi]⟩
  · change 0 < Real.cos d.β
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [h.beta_pos], h.beta_lt_half_pi⟩
  · change 0 < Real.sin d.β
    exact Real.sin_pos_of_mem_Ioo ⟨h.beta_pos, by linarith [h.beta_lt_half_pi]⟩
  · exact h.pointValid (h.base_mem 0 (by norm_num))
  · exact h.pointValid (h.base_mem 1 (by norm_num))
  · exact h.pointValid h.left_top_mem
  · exact h.pointValid h.right_top_mem
  · rw [FaceData.scalarData_x1, FaceData.scalarData_y1]
    exact h.pointValid h.face₁minus_mem
  · rw [FaceData.scalarData_x1, FaceData.scalarData_y1]
    exact h.pointValid h.face₁plus_mem
  · rw [FaceData.scalarData_x2, FaceData.scalarData_y2]
    exact h.pointValid h.face₂minus_mem
  · rw [FaceData.scalarData_x2, FaceData.scalarData_y2]
    exact h.pointValid h.face₂plus_mem

end SupportedSource

end Puzzling139335.SourceFaceBridge
