import ErdosProblems.Erdos633b.GroupOneMetric
import ErdosProblems.Erdos633b.CaseSixGeometry
import ErdosProblems.Erdos633b.RationalSides

/-! The existing geometric triquadratic construction as a comparison tiling. -/

namespace Erdos633b.TriquadraticCoordinates

theorem outer_side_one (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) :
    (outer c s d hc hs hs1 hd).side 1 = c ^ 2 * (1 - s ^ 2) := by
  have hp : 0 < c ^ 2 * (1 - s ^ 2) :=
    mul_pos (sq_pos_of_pos hc) (parameter_denominator_pos s hs hs1).1
  change dist (bigC c s) (0 : Plane) = _
  have hv : bigC c s = (c ^ 2 * (1 - s ^ 2)) • (!₂[1, 0] : Plane) := by
    ext i
    fin_cases i <;> simp [bigC]
  rw [hv, dist_zero_right, norm_smul, Real.norm_of_nonneg hp.le, norm_e, mul_one]

theorem reference_angles_of_groupOne (S : Triangle)
    (hrel : 3 * S.angle 0 + 2 * S.angle 1 = Real.pi)
    (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) (he : d ^ 2 = 4 - s ^ 2)
    (hparam : s = 2 * Real.sin (S.angle 0 / 2)) :
    ∀ i, (reference c s d hc hs hs1 hd).angle i = S.angle i := by
  let R := reference c s d hc hs hs1 hd
  have hrat := S.groupOne_side_ratios hrel
  rw [← hparam] at hrat
  have hside (i : Fin 3) : S.side i = (S.side 2 / c) * R.side i := by
    rw [reference_sides c s d hc hs hs1 hd he]
    fin_cases i
    · change S.side 0 = (S.side 2 / c) * (c * s)
      have hh := (div_eq_iff (S.side_pos 2).ne').mp hrat.1
      rw [hh]
      field_simp
    · change S.side 1 = (S.side 2 / c) * (c * (1 - s ^ 2))
      have hh := (div_eq_iff (S.side_pos 2).ne').mp hrat.2
      rw [hh]
      field_simp
    · change S.side 2 = (S.side 2 / c) * c
      field_simp
  intro i
  exact (R.angles_of_scaled_sides S (S.side 2 / c) (div_pos (S.side_pos 2) hc) hside i).symm

theorem outer_angles_of_groupOne (S T : Triangle)
    (h0 : T.angle 0 = 2 * S.angle 0) (h1 : T.angle 1 = S.angle 1)
    (h2 : T.angle 2 = S.angle 0 + S.angle 1)
    (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) (he : d ^ 2 = 4 - s ^ 2)
    (hparam : s = 2 * Real.sin (S.angle 0 / 2)) :
    ∀ i, (outer c s d hc hs hs1 hd).angle i = T.angle i := by
  let U := outer c s d hc hs hs1 hd
  obtain ⟨hUrel, hUs⟩ := outer_angle_relations c s d hc hs hs1 hd he
  have hTrel : T.angle 2 = T.angle 0 / 2 + T.angle 1 := by rw [h0, h1, h2]; ring
  have hTparam : 2 * Real.sin (T.angle 0 / 4) = s := by
    rw [h0, show 2 * S.angle 0 / 4 = S.angle 0 / 2 by ring, ← hparam]
  have hsin : Real.sin (U.angle 0 / 4) = Real.sin (T.angle 0 / 4) := by linarith
  have hzero : U.angle 0 = T.angle 0 := by
    have hh := Real.injOn_sin
      (show U.angle 0 / 4 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by linarith [Real.pi_pos, U.angle_pos 0], by linarith [Real.pi_pos, U.angle_lt_pi 0]⟩)
      (show T.angle 0 / 4 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by linarith [Real.pi_pos, T.angle_pos 0], by linarith [Real.pi_pos, T.angle_lt_pi 0]⟩)
      hsin
    linarith
  have hone : U.angle 1 = T.angle 1 := by linarith [U.angle_sum, T.angle_sum]
  have htwo : U.angle 2 = T.angle 2 := by linarith
  intro i
  fin_cases i
  · exact hzero
  · exact hone
  · exact htwo

end Erdos633b.TriquadraticCoordinates
