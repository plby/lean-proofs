import Wikipedia.SmoothSixDPoincare.BigonStripCoordinates

/-!
# Interior points have strict interior strip coordinates

The interpolated edge coordinates send every interior bigon point to a
positive transverse coordinate and a time strictly between zero and one.
Consequently neither the center contact nor either endpoint contact can
occur there. The argument uses an explicit convex-combination identity.
-/

noncomputable section

open Set Function

namespace Wikipedia.SmoothSixDPoincare.WhitneyPairModel

theorem interpolated_strip_time_mem_Ioo {h t β z J : ℝ}
    (hh : 0 < h) (ht : t ∈ Ioo (0 : ℝ) 1) (hβ : β ∈ Icc (0 : ℝ) 1)
    (hJ : 0 < J) (hJdef : J = (1 - β) * (1 - t) + β * t)
    (hz : 0 < z) (hzupper : z < 4 * h * t * (1 - t)) :
    t + (2 * β - 1) * (z / (4 * h * J)) ∈ Ioo (0 : ℝ) 1 := by
  let H := 4 * h * t * (1 - t)
  have hH : 0 < H :=
    mul_pos (mul_pos (mul_pos (by norm_num) hh) ht.1) (sub_pos.mpr ht.2)
  let θ := z / H
  let e := t * β / J
  have hθ0 : 0 < θ := div_pos hz hH
  have hθ1 : θ < 1 := (div_lt_one hH).mpr hzupper
  have he0 : 0 ≤ e := div_nonneg (mul_nonneg ht.1.le hβ.1) hJ.le
  have he1 : e ≤ 1 := by
    apply (div_le_one hJ).mpr
    rw [hJdef]
    have hr := mul_nonneg (sub_nonneg.mpr hβ.2) (sub_nonneg.mpr ht.2.le)
    nlinarith
  have hid : t + (2 * β - 1) * (z / (4 * h * J)) = (1 - θ) * t + θ * e := by
    dsimp [θ, e, H]
    field_simp [hh.ne', ht.1.ne', (sub_pos.mpr ht.2).ne', hJ.ne']
    rw [hJdef]
    ring
  rw [hid]
  constructor
  · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hθ1) ht.1)
      (mul_nonneg hθ0.le he0)
  · have hpos : 0 < (1 - θ) * (1 - t) + θ * (1 - e) :=
      add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hθ1) (sub_pos.mpr ht.2))
        (mul_nonneg hθ0.le (sub_nonneg.mpr he1))
    nlinarith

/-- Every interior point has positive normal coordinate and strictly interior lower-strip time. -/
theorem lowerStripCoordinates_interior {h : ℝ} (hh : 0 < h) {p : ℝ × ℝ}
    (hp : p ∈ interior (bigon h)) :
    (lowerStripCoordinates h p).1 ∈ Ioo (0 : ℝ) 1 ∧ 0 < (lowerStripCoordinates h p).2 := by
  obtain ⟨hp0, hphi⟩ := (mem_interior_bigon_iff h p).mp hp
  have hheight : 0 < h * (1 - p.1 ^ 2) := hp0.trans hphi
  have hsq : p.1 ^ 2 < 1 := by
    have hpos : 0 < 1 - p.1 ^ 2 := (mul_pos_iff_of_pos_left hh).mp hheight
    linarith
  have ht : arcTime p ∈ Ioo (0 : ℝ) 1 := by
    dsimp [arcTime]
    constructor <;> nlinarith [sq_nonneg (p.1 - 1), sq_nonneg (p.1 + 1)]
  have hβ : cornerTransition (arcTime p) ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hheight_eq : h * (1 - p.1 ^ 2) = 4 * h * arcTime p * (1 - arcTime p) := by
    dsimp [arcTime]
    ring
  have hzupper : p.2 < 4 * h * arcTime p * (1 - arcTime p) := hheight_eq ▸ hphi
  refine ⟨?_, ?_⟩
  · exact interpolated_strip_time_mem_Ioo hh ht hβ (cornerScale_pos _) rfl hp0 hzupper
  · exact div_pos hp0 (mul_pos (mul_pos (by norm_num) hh) (cornerScale_pos _))

theorem exchangeEdges_mem_interior {h : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ interior (bigon h)) : exchangeEdges h p ∈ interior (bigon h) := by
  obtain ⟨hp0, hphi⟩ := (mem_interior_bigon_iff h p).mp hp
  apply (mem_interior_bigon_iff h _).mpr
  change 0 < h * (1 - p.1 ^ 2) - p.2 ∧
    h * (1 - p.1 ^ 2) - p.2 < h * (1 - p.1 ^ 2)
  constructor <;> linarith

/-- The upper edge coordinates have the same strict interior-contact exclusion. -/
theorem upperStripCoordinates_interior {h : ℝ} (hh : 0 < h) {p : ℝ × ℝ}
    (hp : p ∈ interior (bigon h)) :
    (upperStripCoordinates h p).1 ∈ Ioo (0 : ℝ) 1 ∧ 0 < (upperStripCoordinates h p).2 :=
  lowerStripCoordinates_interior hh (exchangeEdges_mem_interior hp)

end Wikipedia.SmoothSixDPoincare.WhitneyPairModel
