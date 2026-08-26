import ErdosProblems.Erdos1038.PlatformAdjointPartition

/-!
# Angular factorization of the platform block energy

The distance between two platform support points factors into the two
circle sine kernels with the exact capacity factor.  This is the pointwise
identity behind manuscript equation `(5.3)`.
-/

set_option warningAsError false

open Set

namespace Erdos1038

noncomputable section

local notation "AngleCircle" => AddCircle (2 * Real.pi)

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

lemma addCircle_dist_coe_coe_eq_abs_sub
    {theta phi : ℝ} (habs : |theta - phi| ≤ Real.pi) :
    dist (theta : AngleCircle) (phi : AngleCircle) = |theta - phi| := by
  rw [dist_eq_norm]
  change ‖((theta - phi : ℝ) : AngleCircle)‖ = |theta - phi|
  exact (AddCircle.norm_coe_eq_abs_iff
    (2 * Real.pi) (by positivity)).2 (by
      rw [abs_of_pos Real.two_pi_pos]
      linarith)

lemma sin_half_addCircle_dist_neg_coe_coe
    {theta phi : ℝ} (htheta : theta ∈ Icc (0 : ℝ) Real.pi)
    (hphi : phi ∈ Icc (0 : ℝ) Real.pi) :
    Real.sin
        (dist ((-theta : ℝ) : AngleCircle) (phi : AngleCircle) / 2) =
      Real.sin ((theta + phi) / 2) := by
  have hsum0 : 0 ≤ theta + phi := by linarith [htheta.1, hphi.1]
  have hsum2pi : theta + phi ≤ 2 * Real.pi := by
    linarith [htheta.2, hphi.2]
  have hnorm := addCircle_norm_coe_eq_min_wrap
    (theta + phi) hsum0 hsum2pi
  have hdist :
      dist ((-theta : ℝ) : AngleCircle) (phi : AngleCircle) =
        min (theta + phi) (2 * Real.pi - (theta + phi)) := by
    rw [dist_eq_norm]
    rw [← AddCircle.coe_sub]
    rw [show -theta - phi = -(theta + phi) by ring,
      AddCircle.coe_neg]
    rw [norm_neg]
    exact hnorm
  rw [hdist]
  rcases le_total (theta + phi) Real.pi with hle | hge
  · rw [min_eq_left (by linarith)]
  · rw [min_eq_right (by linarith)]
    rw [show (2 * Real.pi - (theta + phi)) / 2 =
        Real.pi - (theta + phi) / 2 by ring,
      Real.sin_pi_sub]

lemma circleLogDeficitAt_coe_coe
    {theta phi : ℝ} (htheta : theta ∈ Icc (0 : ℝ) Real.pi)
    (hphi : phi ∈ Icc (0 : ℝ) Real.pi) :
    circleLogDeficitAt (theta : AngleCircle) (phi : AngleCircle) =
      -Real.log (Real.sin (|theta - phi| / 2)) := by
  have habs : |theta - phi| ≤ Real.pi := by
    rw [abs_le]
    constructor <;> linarith [htheta.1, htheta.2, hphi.1, hphi.2]
  unfold circleLogDeficitAt
  rw [show dist (phi : AngleCircle) (theta : AngleCircle) =
      dist (theta : AngleCircle) (phi : AngleCircle) by exact dist_comm _ _,
    addCircle_dist_coe_coe_eq_abs_sub habs]

lemma circleLogDeficitAt_neg_coe_coe
    {theta phi : ℝ} (htheta : theta ∈ Icc (0 : ℝ) Real.pi)
    (hphi : phi ∈ Icc (0 : ℝ) Real.pi) :
    circleLogDeficitAt ((-theta : ℝ) : AngleCircle)
        (phi : AngleCircle) =
      -Real.log (Real.sin ((theta + phi) / 2)) := by
  unfold circleLogDeficitAt
  rw [show dist (phi : AngleCircle) ((-theta : ℝ) : AngleCircle) =
      dist ((-theta : ℝ) : AngleCircle) (phi : AngleCircle) by
        exact dist_comm _ _,
    sin_half_addCircle_dist_neg_coe_coe htheta hphi]

lemma platformAngularDistance_sub_factor
    (a theta phi : ℝ) :
    platformAngularDistance a theta - platformAngularDistance a phi =
      4 * platformCapacity a *
        Real.sin ((theta + phi) / 2) *
        Real.sin ((theta - phi) / 2) := by
  have hcos : Real.cos phi - Real.cos theta =
      2 * Real.sin ((theta + phi) / 2) *
        Real.sin ((theta - phi) / 2) := by
    rw [Real.cos_sub_cos]
    rw [show (phi + theta) / 2 = (theta + phi) / 2 by ring,
      show (phi - theta) / 2 = -((theta - phi) / 2) by ring,
      Real.sin_neg]
    ring
  calc
    platformAngularDistance a theta - platformAngularDistance a phi =
        platformRadius a * (Real.cos phi - Real.cos theta) := by
      unfold platformAngularDistance
      ring
    _ = 4 * platformCapacity a *
        Real.sin ((theta + phi) / 2) *
        Real.sin ((theta - phi) / 2) := by
      rw [hcos]
      unfold platformRadius platformCapacity
      ring

lemma abs_platformAngularDistance_sub_factor
    {a theta phi : ℝ} (ha2 : a < 2)
    (htheta : theta ∈ Icc (0 : ℝ) Real.pi)
    (hphi : phi ∈ Icc (0 : ℝ) Real.pi) :
    |platformAngularDistance a theta - platformAngularDistance a phi| =
      4 * platformCapacity a *
        Real.sin ((theta + phi) / 2) *
        Real.sin (|theta - phi| / 2) := by
  have hcap : 0 < platformCapacity a := platformCapacity_pos ha2
  have hsum0 : 0 ≤ (theta + phi) / 2 := by linarith [htheta.1, hphi.1]
  have hsumpi : (theta + phi) / 2 ≤ Real.pi := by
    linarith [htheta.2, hphi.2]
  have hsinSum : 0 ≤ Real.sin ((theta + phi) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hsum0 hsumpi
  have hdiff : |(theta - phi) / 2| ≤ Real.pi := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have habs : |theta - phi| ≤ Real.pi := by
      rw [abs_le]
      constructor <;> linarith [htheta.1, htheta.2, hphi.1, hphi.2]
    linarith [habs, Real.pi_pos]
  rw [platformAngularDistance_sub_factor, abs_mul, abs_mul,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos hcap,
    abs_of_nonneg hsinSum,
    Real.abs_sin_eq_sin_abs_of_abs_le_pi hdiff,
    abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

theorem log_abs_platformAngularDistance_sub
    {a theta phi : ℝ} (ha2 : a < 2)
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi)
    (hphi : phi ∈ Ioo (0 : ℝ) Real.pi) (hne : theta ≠ phi) :
    Real.log
        |platformAngularDistance a theta - platformAngularDistance a phi| =
      Real.log (platformCapacity a) + 2 * Real.log 2 +
        Real.log (Real.sin ((theta + phi) / 2)) +
        Real.log (Real.sin (|theta - phi| / 2)) := by
  have hcap : 0 < platformCapacity a := platformCapacity_pos ha2
  have hsum0 : 0 < (theta + phi) / 2 := by linarith [htheta.1, hphi.1]
  have hsumpi : (theta + phi) / 2 < Real.pi := by
    linarith [htheta.2, hphi.2]
  have hsinSum : 0 < Real.sin ((theta + phi) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hsum0 hsumpi
  have habsDiff : 0 < |theta - phi| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have habsDiffPi : |theta - phi| / 2 < Real.pi := by
    have habs : |theta - phi| < 2 * Real.pi := by
      rw [abs_lt]
      constructor <;> linarith [htheta.1, htheta.2, hphi.1, hphi.2,
        Real.pi_pos]
    linarith
  have hsinDiff : 0 < Real.sin (|theta - phi| / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) habsDiffPi
  rw [abs_platformAngularDistance_sub_factor ha2
      ⟨htheta.1.le, htheta.2.le⟩ ⟨hphi.1.le, hphi.2.le⟩,
    Real.log_mul
      (mul_ne_zero
        (mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) hcap.ne')
        hsinSum.ne')
      hsinDiff.ne',
    Real.log_mul
      (mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) hcap.ne')
      hsinSum.ne',
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hcap.ne',
    show Real.log (4 : ℝ) = 2 * Real.log 2 by
      rw [show (4 : ℝ) = 2 * 2 by norm_num,
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
          (by norm_num : (2 : ℝ) ≠ 0)]
      ring]
  ring

/-- Pointwise form of equation `(5.3)`, away from the diagonal null set.
The two circle deficits correspond to the same-sign and opposite-sign
copies of the even angular densities. -/
theorem log_abs_platformAngularDistance_sub_eq_circleDeficits
    {a theta phi : ℝ} (ha2 : a < 2)
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi)
    (hphi : phi ∈ Ioo (0 : ℝ) Real.pi) (hne : theta ≠ phi) :
    Real.log
        |platformAngularDistance a theta - platformAngularDistance a phi| =
      Real.log (platformCapacity a) + 2 * Real.log 2 -
        circleLogDeficitAt (theta : AngleCircle) (phi : AngleCircle) -
        circleLogDeficitAt ((-theta : ℝ) : AngleCircle)
          (phi : AngleCircle) := by
  rw [log_abs_platformAngularDistance_sub ha2 htheta hphi hne,
    circleLogDeficitAt_coe_coe
      ⟨htheta.1.le, htheta.2.le⟩ ⟨hphi.1.le, hphi.2.le⟩,
    circleLogDeficitAt_neg_coe_coe
      ⟨htheta.1.le, htheta.2.le⟩ ⟨hphi.1.le, hphi.2.le⟩]
  ring

end

end Erdos1038
