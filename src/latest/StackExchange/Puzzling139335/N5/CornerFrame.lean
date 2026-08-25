import StackExchange.Puzzling139335.PlaneIsometries

/-!
# The actual corner frame in the normalized five-incidence case

The source set contains the bottom side's endpoints and lies below the
diagonal.  If an actual Euclidean placement sends a third source point to
the top-right corner, its linear part has a nonnegative, ordered pair of
parameters.  Both possible orientations are retained.
-/

open Set

namespace Puzzling139335.N5

open PlaneIsometries

private theorem corner_zero_eq_origin : corner 0 = (0 : Plane) := by
  apply plane_ext <;> norm_num [corner, Fin.ext_iff]

/-- A scalar affine function bounded above by one at both ends of the unit
interval cannot reach one at a strict interior point unless it is constant. -/
private theorem base_slope_eq_zero {h a t : ℝ}
    (hh₀ : 0 < h) (hh₁ : h < 1)
    (hleft : t ≤ 1) (hright : a + t ≤ 1)
    (hmax : a * h + t = 1) : a = 0 := by
  have ha₀ : 0 ≤ a := by
    by_contra ha
    have hprod : a * h < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge ha) hh₀
    linarith
  have ha₁ : a ≤ 0 := by
    by_contra ha
    have hprod : 0 < a * (1 - h) :=
      mul_pos (lt_of_not_ge ha) (sub_pos.mpr hh₁)
    nlinarith
  exact le_antisymm ha₁ ha₀

/-- A supporting row that reaches its maximum at positive height must have
a nonnegative vertical coefficient. -/
private theorem vertical_coefficient_nonneg {h k a b t : ℝ}
    (hh₀ : 0 ≤ h) (hh₁ : h ≤ 1) (hk : 0 < k)
    (hleft : t ≤ 1) (hright : a + t ≤ 1)
    (hmax : a * h + b * k + t = 1) : 0 ≤ b := by
  have hw₀ := mul_nonneg (sub_nonneg.mpr hh₁) (sub_nonneg.mpr hleft)
  have hw₁ := mul_nonneg hh₀ (sub_nonneg.mpr hright)
  have hbk : 0 ≤ b * k := by nlinarith
  by_contra hb
  have hneg : b * k < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hb) hk
  linarith

/-- The lower-diagonal source constraint orders the two nonnegative frame
parameters, and their unit norm makes the larger parameter positive. -/
private theorem ordered_frame_parameters {c s h k : ℝ}
    (hnorm : c ^ 2 + s ^ 2 = 1) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hk : 0 < k) (hkh : k ≤ h) (hleft : s * h ≤ c * k) :
    s ≤ c ∧ 0 < c := by
  have hh : 0 < h := lt_of_lt_of_le hk hkh
  have hprod : s * h ≤ c * h :=
    hleft.trans (mul_le_mul_of_nonneg_left hkh hc)
  have hsc : s ≤ c := le_of_mul_le_mul_right hprod hh
  refine ⟨hsc, ?_⟩
  by_contra hpos
  have hcz : c = 0 := le_antisymm (le_of_not_gt hpos) hc
  have hsz : s = 0 := by linarith
  nlinarith

/-- A point distinct from the two bottom corners cannot be sent to the
top-right corner while the entire set remains inside the square unless the
point has positive height.  No convexity assumption is used. -/
theorem height_pos_of_corner_placement {P : Set Plane} {C : Plane}
    (hP : P ⊆ unitSquare) (hA : corner 0 ∈ P) (hB : corner 1 ∈ P)
    (hC : C ∈ P) (hCA : C ≠ corner 0) (hCB : C ≠ corner 1)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' P ⊆ unitSquare)
    (heC : e C = corner 2) : 0 < C 1 := by
  have hCfit := hP hC
  have hAfit : e 0 ∈ unitSquare := by
    simpa only [corner_zero_eq_origin] using he ⟨corner 0, hA, rfl⟩
  have hBfit := he ⟨corner 1, hB, rfl⟩
  by_contra hheight
  have hk : C 1 = 0 := le_antisymm (le_of_not_gt hheight) hCfit.2.1
  have hh₀ : 0 < C 0 := by
    by_contra h
    have hx : C 0 = 0 := le_antisymm (le_of_not_gt h) hCfit.1.1
    apply hCA
    apply plane_ext <;> norm_num [corner, Fin.ext_iff, hx, hk]
  have hh₁ : C 0 < 1 := by
    by_contra h
    have hx : C 0 = 1 := le_antisymm hCfit.1.2 (le_of_not_gt h)
    apply hCB
    apply plane_ext <;> norm_num [corner, Fin.ext_iff, hx, hk]
  obtain ⟨a, b, hnorm, hform⟩ := affine_coordinate_classification e
  have hBbounds : a + (e 0) 0 ≤ 1 ∧ b + (e 0) 1 ≤ 1 := by
    rcases hform with hform | hform
    · rw [hform (corner 1)] at hBfit
      norm_num [unitSquare, directCoordinates, corner, Fin.ext_iff] at hBfit
      exact ⟨hBfit.1.2, hBfit.2.2⟩
    · rw [hform (corner 1)] at hBfit
      norm_num [unitSquare, reversingCoordinates, corner, Fin.ext_iff] at hBfit
      exact ⟨hBfit.1.2, hBfit.2.2⟩
  have hCrows : a * C 0 + (e 0) 0 = 1 ∧ b * C 0 + (e 0) 1 = 1 := by
    rcases hform with hform | hform
    · have h₀ := congrArg (fun p : Plane => p 0) (hform C)
      have h₁ := congrArg (fun p : Plane => p 1) (hform C)
      rw [heC] at h₀ h₁
      norm_num [directCoordinates, corner, Fin.ext_iff, hk] at h₀ h₁
      exact ⟨h₀.symm, h₁.symm⟩
    · have h₀ := congrArg (fun p : Plane => p 0) (hform C)
      have h₁ := congrArg (fun p : Plane => p 1) (hform C)
      rw [heC] at h₀ h₁
      norm_num [reversingCoordinates, corner, Fin.ext_iff, hk] at h₀ h₁
      exact ⟨h₀.symm, h₁.symm⟩
  have ha : a = 0 := base_slope_eq_zero hh₀ hh₁ hAfit.1.2 hBbounds.1 hCrows.1
  have hb : b = 0 := base_slope_eq_zero hh₀ hh₁ hAfit.2.2 hBbounds.2 hCrows.2
  nlinarith

/-- The exact two possible affine coordinate frames of a placement taking
the third point to the top-right corner.  The inequalities are forced by the
actual images of the two source endpoints, not assumed supporting angles. -/
theorem cornerFrame_of_placement {P : Set Plane} {C : Plane}
    (hP : P ⊆ unitSquare) (hbelow : P ⊆ {p | p 1 ≤ p 0})
    (hA : corner 0 ∈ P) (hB : corner 1 ∈ P)
    (hC : C ∈ P) (hCA : C ≠ corner 0) (hCB : C ≠ corner 1)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' P ⊆ unitSquare)
    (heC : e C = corner 2) :
    0 < C 1 ∧ ∃ c s : ℝ,
      c ^ 2 + s ^ 2 = 1 ∧ 0 ≤ s ∧ s ≤ c ∧ 0 < c ∧
      s * C 0 ≤ c * C 1 ∧ c * (1 - C 0) ≤ s * C 1 ∧
      ((∀ p, e p =
          !₂[1 - c * C 0 - s * C 1 + c * p 0 + s * p 1,
             1 + s * C 0 - c * C 1 - s * p 0 + c * p 1]) ∨
       (∀ p, e p =
          !₂[1 + s * C 0 - c * C 1 - s * p 0 + c * p 1,
             1 - c * C 0 - s * C 1 + c * p 0 + s * p 1])) := by
  have hk := height_pos_of_corner_placement hP hA hB hC hCA hCB e he heC
  have hCfit := hP hC
  have hkh : C 1 ≤ C 0 := hbelow hC
  have hAfit : e 0 ∈ unitSquare := by
    simpa only [corner_zero_eq_origin] using he ⟨corner 0, hA, rfl⟩
  have hBfit := he ⟨corner 1, hB, rfl⟩
  obtain ⟨a, b, hnorm, hform | hform⟩ := affine_coordinate_classification e
  · rw [hform (corner 1)] at hBfit
    norm_num [unitSquare, directCoordinates, corner, Fin.ext_iff] at hBfit
    have h₀ := congrArg (fun p : Plane => p 0) (hform C)
    have h₁ := congrArg (fun p : Plane => p 1) (hform C)
    rw [heC] at h₀ h₁
    norm_num [directCoordinates, corner, Fin.ext_iff] at h₀ h₁
    have hs : 0 ≤ -b := vertical_coefficient_nonneg
      hCfit.1.1 hCfit.1.2 hk hAfit.1.2 hBfit.1.2 (by nlinarith [h₀])
    have hc : 0 ≤ a := vertical_coefficient_nonneg
      hCfit.1.1 hCfit.1.2 hk hAfit.2.2 hBfit.2.2 (by nlinarith [h₁])
    have hleft : (-b) * C 0 ≤ a * C 1 := by linarith [hAfit.2.2]
    have hright : a * (1 - C 0) ≤ (-b) * C 1 := by nlinarith [hBfit.1.2]
    have hnorm' : a ^ 2 + (-b) ^ 2 = 1 := by nlinarith [hnorm]
    obtain ⟨hsc, hcpos⟩ := ordered_frame_parameters hnorm' hc hs hk hkh hleft
    have ht₀ : (e 0) 0 = 1 - a * C 0 + b * C 1 := by linarith
    have ht₁ : (e 0) 1 = 1 - b * C 0 - a * C 1 := by linarith
    refine ⟨hk, a, -b, hnorm', hs, hsc, hcpos, hleft, hright, Or.inl ?_⟩
    intro p
    rw [hform p]
    apply plane_ext <;> simp [directCoordinates, ht₀, ht₁] <;> ring
  · rw [hform (corner 1)] at hBfit
    norm_num [unitSquare, reversingCoordinates, corner, Fin.ext_iff] at hBfit
    have h₀ := congrArg (fun p : Plane => p 0) (hform C)
    have h₁ := congrArg (fun p : Plane => p 1) (hform C)
    rw [heC] at h₀ h₁
    norm_num [reversingCoordinates, corner, Fin.ext_iff] at h₀ h₁
    have hc : 0 ≤ b := vertical_coefficient_nonneg
      hCfit.1.1 hCfit.1.2 hk hAfit.1.2 hBfit.1.2 (by nlinarith [h₀])
    have hs : 0 ≤ -a := vertical_coefficient_nonneg
      hCfit.1.1 hCfit.1.2 hk hAfit.2.2 hBfit.2.2 (by nlinarith [h₁])
    have hleft : (-a) * C 0 ≤ b * C 1 := by linarith [hAfit.1.2]
    have hright : b * (1 - C 0) ≤ (-a) * C 1 := by nlinarith [hBfit.2.2]
    have hnorm' : b ^ 2 + (-a) ^ 2 = 1 := by nlinarith [hnorm]
    obtain ⟨hsc, hcpos⟩ := ordered_frame_parameters hnorm' hc hs hk hkh hleft
    have ht₀ : (e 0) 0 = 1 - a * C 0 - b * C 1 := by linarith
    have ht₁ : (e 0) 1 = 1 - b * C 0 + a * C 1 := by linarith
    refine ⟨hk, b, -a, hnorm', hs, hsc, hcpos, hleft, hright, Or.inr ?_⟩
    intro p
    rw [hform p]
    apply plane_ext <;> simp [reversingCoordinates, ht₀, ht₁] <;> ring

end Puzzling139335.N5
