import Wikipedia.NoExoticSixSphere.OrthogonalHomotopyLift

/-!
# Normalized coordinates on a closed time interval

The normalized parameter is clamped outside the interval. Affine interpolation
recovers the original clipped time, including when the interval degenerates.
This allows a local path replacement to be inserted into a larger path.
-/

open Set unitInterval

namespace NoExoticSixSphere.IntervalCoordinates

open OrthogonalPaths.ColumnLift

noncomputable def normalize (s u t : I) : I :=
  projIcc 0 1 zero_le_one (((t : ℝ) - (s : ℝ)) / ((u : ℝ) - (s : ℝ)))

theorem continuous_normalize (s u : I) : Continuous (normalize s u) :=
  continuous_projIcc.comp ((continuous_subtype_val.sub continuous_const).div_const _)

theorem normalize_before {s u t : I} (hsu : s ≤ u) (ht : t ≤ s) : normalize s u t = 0 :=
  projIcc_of_le_left zero_le_one
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_nonneg.mpr hsu))

theorem normalize_after {s u t : I} (hsu : s < u) (ht : u ≤ t) : normalize s u t = 1 := by
  apply projIcc_of_right_le zero_le_one
  apply (le_div_iff₀ (sub_pos.mpr (show (s : ℝ) < (u : ℝ) from hsu))).mpr
  simpa only [one_mul] using sub_le_sub_right (show (u : ℝ) ≤ (t : ℝ) from ht) (s : ℝ)

theorem coe_normalize_of_mem {s u t : I} (hsu : s < u) (ht : t ∈ Icc s u) :
    (normalize s u t : ℝ) = ((t : ℝ) - (s : ℝ)) / ((u : ℝ) - (s : ℝ)) := by
  have h0 : 0 ≤ ((t : ℝ) - (s : ℝ)) / ((u : ℝ) - (s : ℝ)) :=
    div_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr hsu.le)
  have h1 : ((t : ℝ) - (s : ℝ)) / ((u : ℝ) - (s : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ (sub_pos.mpr (show (s : ℝ) < (u : ℝ) from hsu))).mpr
    simpa only [one_mul] using sub_le_sub_right (show (t : ℝ) ≤ (u : ℝ) from ht.2) (s : ℝ)
  change max 0 (min 1 _) = _
  rw [min_eq_right h1, max_eq_right h0]

/-- The coordinate formula agrees with the actual clipped time even on degenerate intervals. -/
theorem convexComb_normalize {s u : I} (hsu : s ≤ u) (t : I) :
    Icc.convexComb s u (normalize s u t) = clip s u t := by
  by_cases heq : s = u
  · subst u
    rw [Icc.convexComb_eq, clip, min_eq_right (le_max_right _ _)]
  have hlt : s < u := lt_of_le_of_ne hsu heq
  by_cases hts : t ≤ s
  · rw [normalize_before hsu hts, Icc.convexComb_zero, clip_of_le hsu hts]
  have hst : s ≤ t := le_of_not_ge hts
  by_cases hut : u ≤ t
  · rw [normalize_after hlt hut, Icc.convexComb_one, clip_of_ge hst, min_eq_right hut]
  have htu : t ≤ u := le_of_not_ge hut
  rw [clip_of_ge hst, min_eq_left htu]
  apply Subtype.ext
  rw [Icc.coe_convexComb, coe_normalize_of_mem hlt ⟨hst, htu⟩]
  have hne : (u : ℝ) - (s : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr hlt)
  field_simp [hne]
  ring

end NoExoticSixSphere.IntervalCoordinates
