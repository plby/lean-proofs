import StackExchange.Puzzling139335.SourceFaceBridge.UpperDefs
import StackExchange.Puzzling139335.TwoSideFaces

/-!
# The natural upper-normal order is impossible for actual source data

Every endpoint, support, width, and tangent-strip hypothesis of the scalar
obstruction is derived here from the source memberships and square images.
Neither Jordan regularity nor a common-interface hypothesis is required.
-/

open Set

namespace Puzzling139335.SourceFaceBridge

namespace UpperSupportedSource

/-- Actual supported sources cannot have the first upper normal acute and
the second upper normal obtuse. The statement applies to either left parity. -/
theorem natural_straddle_false {d : UpperFaceData} {reversed : Bool} {P : Set Plane}
    (h : UpperSupportedSource d reversed P)
    (hphi : d.φ < Real.pi / 2) (hpsi : Real.pi / 2 < d.ψ) : False := by
  have hπ := Real.pi_pos
  have hc : 0 < Real.cos d.φ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [h.phi_pos], hphi⟩
  have hs : 0 < Real.sin d.φ :=
    Real.sin_pos_of_mem_Ioo ⟨h.phi_pos, h.phi_lt_pi⟩
  have hd : 0 < -Real.cos d.ψ :=
    neg_pos.mpr (Real.cos_neg_of_pi_div_two_lt_of_lt hpsi (by linarith [h.psi_lt_pi]))
  have hq : 0 < Real.sin d.ψ :=
    Real.sin_pos_of_mem_Ioo ⟨h.psi_pos, h.psi_lt_pi⟩
  have hYN : d.normal₁ d.face₁plus = d.normal₁ d.M₁ := by
    dsimp [UpperFaceData.normal₁, UpperFaceData.face₁plus, point]
    ring
  have hZN : d.normal₂ d.face₂minus = d.normal₂ d.M₂ := by
    dsimp [UpperFaceData.normal₂, UpperFaceData.face₂minus, point]
    ring
  apply TwoSideFaces.natural_straddle_false_of_endpoints
    (Real.cos d.φ) (Real.sin d.φ) (-Real.cos d.ψ) (Real.sin d.ψ)
    d.a d.b (d.face₁plus 0) (d.face₁plus 1) (d.face₂minus 0) (d.face₂minus 1)
    hc hs hd hq (Real.cos_sq_add_sin_sq d.φ)
    (by simpa only [neg_sq] using Real.cos_sq_add_sin_sq d.ψ)
    h.a_lt_half h.b_lt_half (h.source_subset h.face₁plus_mem).2.2
    (h.source_subset h.face₂minus_mem).2.2
  · have hrow := (h.source_subset h.face₁minus_mem).1.2
    dsimp [UpperFaceData.face₁minus, UpperFaceData.face₁plus, point] at hrow ⊢
    nlinarith only [hrow]
  · have hrow := (h.source_subset h.face₂plus_mem).1.1
    dsimp [UpperFaceData.face₂minus, UpperFaceData.face₂plus, point] at hrow ⊢
    nlinarith only [hrow]
  · have hrow := (h.source_supports h.right_top_mem).1
    rw [← hYN] at hrow
    change Real.cos d.φ * 1 + Real.sin d.φ * d.b ≤
      Real.cos d.φ * d.face₁plus 0 + Real.sin d.φ * d.face₁plus 1 at hrow
    nlinarith only [hrow]
  · have hrow := (h.source_supports h.left_top_mem).2
    rw [← hZN] at hrow
    change Real.cos d.ψ * 0 + Real.sin d.ψ * d.a ≤
      Real.cos d.ψ * d.face₂minus 0 + Real.sin d.ψ * d.face₂minus 1 at hrow
    nlinarith only [hrow]
  · have hrow := (h.source_supports h.face₂minus_mem).1
    rw [← hYN] at hrow
    change Real.cos d.φ * d.face₂minus 0 + Real.sin d.φ * d.face₂minus 1 ≤
      Real.cos d.φ * d.face₁plus 0 + Real.sin d.φ * d.face₁plus 1 at hrow
    nlinarith only [hrow]
  · have hrow := (h.source_supports h.face₁plus_mem).2
    rw [← hZN] at hrow
    change Real.cos d.ψ * d.face₁plus 0 + Real.sin d.ψ * d.face₁plus 1 ≤
      Real.cos d.ψ * d.face₂minus 0 + Real.sin d.ψ * d.face₂minus 1 at hrow
    nlinarith only [hrow]
  · have hleft := (h.right_inverse_box h.left_top_mem).2.2.2
    have hright := (h.right_inverse_box (h.base_mem 1 (by norm_num))).2.2.1
    change -Real.sin d.φ * 0 + Real.cos d.φ * d.a - d.tangent₁ d.M₁ ≤ 1 / 2 at hleft
    change -(1 / 2 : ℝ) ≤
      -Real.sin d.φ * 1 + Real.cos d.φ * 0 - d.tangent₁ d.M₁ at hright
    nlinarith only [hleft, hright]
  · have hleft := (h.left_inverse_box (h.base_mem 0 (by norm_num))).2.2.2
    have hright := (h.left_inverse_box h.right_top_mem).2.2.1
    change -Real.sin d.ψ * 0 + Real.cos d.ψ * 0 - d.tangent₂ d.M₂ ≤ 1 / 2 at hleft
    change -(1 / 2 : ℝ) ≤
      -Real.sin d.ψ * 1 + Real.cos d.ψ * d.b - d.tangent₂ d.M₂ at hright
    nlinarith only [hleft, hright]
  · have hrow := (h.right_inverse_box h.face₂plus_mem).2.2.2
    convert hrow using 1
    dsimp [UpperFaceData.tangent₁, UpperFaceData.face₁plus,
      UpperFaceData.face₂minus, UpperFaceData.face₂plus, point]
    ring
  · have hrow := (h.left_inverse_box h.face₁minus_mem).2.2.1
    convert hrow using 1
    dsimp [UpperFaceData.tangent₂, UpperFaceData.face₁minus,
      UpperFaceData.face₁plus, UpperFaceData.face₂minus, point]
    ring

end UpperSupportedSource

end Puzzling139335.SourceFaceBridge
