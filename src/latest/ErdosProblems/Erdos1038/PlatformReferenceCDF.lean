import ErdosProblems.Erdos1038.PlatformCircleBlock

/-!
# The cumulative mass coordinate of a constant-platform reference

The block comparison is indexed by consecutive intervals in reference
quantile space.  This file constructs the inverse of the physical angular
mass of the constant-platform probability.  In particular, every
`u ∈ [0,1]` has a unique angular cut, and differences of cumulative masses
are exactly the physical interval masses used by `PlatformCircleBlock`.
-/

set_option warningAsError false

open Set MeasureTheory

namespace Erdos1038

noncomputable section

/-- Physical reference mass accumulated from angle `0` through `theta`. -/
def platformReferenceCumulative (k a theta : ℝ) : ℝ :=
  (1 / Real.pi) *
    ∫ phi : ℝ in 0..theta, platformAngularDensity k a phi

lemma platformReferenceCumulative_eq_intervalMass (k a theta : ℝ) :
    platformReferenceCumulative k a theta =
      platformReferenceIntervalMass k a 0 theta := rfl

lemma platformReferenceCumulative_zero (k a : ℝ) :
    platformReferenceCumulative k a 0 = 0 := by
  simp [platformReferenceCumulative]

lemma platformReferenceCumulative_pi
    (k : ℝ) {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 2) :
    platformReferenceCumulative k a Real.pi = 1 := by
  exact normalized_integral_platformAngularDensity k ha ha2

lemma continuous_platformReferenceCumulative
    (k : ℝ) {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 2) :
    ContinuousOn (platformReferenceCumulative k a) (Icc 0 Real.pi) := by
  have hint := intervalIntegrable_platformAngularDensity k ha ha2
  have hprimitive : ContinuousOn
      (fun theta ↦ ∫ phi : ℝ in 0..theta,
        platformAngularDensity k a phi) (Icc 0 Real.pi) := by
    simpa only [uIcc_of_le Real.pi_pos.le] using!
      (intervalIntegral.continuousOn_primitive_interval' hint
        (show (0 : ℝ) ∈ Set.uIcc 0 Real.pi from left_mem_uIcc))
  unfold platformReferenceCumulative
  exact continuousOn_const.mul hprimitive

lemma platformReferenceCumulative_sub
    {k a left right : ℝ} (ha : 0 < a) (ha2 : a ≤ 2)
    (hleft : 0 ≤ left) (hle : left ≤ right)
    (hright : right ≤ Real.pi) :
    platformReferenceCumulative k a right -
        platformReferenceCumulative k a left =
      platformReferenceIntervalMass k a left right := by
  have hwhole := intervalIntegrable_platformAngularDensity k ha ha2
  have hleftInt : IntervalIntegrable (platformAngularDensity k a)
      volume 0 left := by
    apply hwhole.mono_set
    rw [uIcc_of_le Real.pi_pos.le, uIcc_of_le hleft]
    exact Icc_subset_Icc_right (hle.trans hright)
  have hrightInt : IntervalIntegrable (platformAngularDensity k a)
      volume left right := by
    apply hwhole.mono_set
    rw [uIcc_of_le Real.pi_pos.le, uIcc_of_le hle]
    exact Icc_subset_Icc hleft hright
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    hleftInt hrightInt
  have hdiff :
      (∫ phi : ℝ in 0..right, platformAngularDensity k a phi) -
          ∫ phi : ℝ in 0..left, platformAngularDensity k a phi =
        ∫ phi : ℝ in left..right, platformAngularDensity k a phi := by
    linarith
  unfold platformReferenceCumulative platformReferenceIntervalMass
  rw [← mul_sub, hdiff]

theorem platformReferenceCumulative_strictMonoOn
    {k a : ℝ} (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    StrictMonoOn (platformReferenceCumulative k a) (Icc 0 Real.pi) := by
  intro left hleft right hright hlr
  have hmass : 0 < platformReferenceIntervalMass k a left right := by
    rw [platformReferenceIntervalMass_eq_endpoint_mul_radius
      (le_trans (by norm_num) hk) ha ha2.le]
    exact div_pos
      (mul_pos (platformAPi_pos (le_trans (by norm_num) hk) ha ha2.le)
        (platformReferenceCircleRadius_pos hk ha ha2 hthreshold
          hleft.1 hlr hright.2))
      Real.pi_pos
  have hsub := platformReferenceCumulative_sub (k := k) ha ha2.le
    hleft.1 hlr.le hright.2
  linarith

theorem platformReferenceCumulative_mem_Icc
    {k a theta : ℝ} (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (htheta : theta ∈ Icc (0 : ℝ) Real.pi) :
    platformReferenceCumulative k a theta ∈ Icc (0 : ℝ) 1 := by
  have hmono :=
    (platformReferenceCumulative_strictMonoOn hk ha ha2 hthreshold).monotoneOn
  constructor
  · simpa [platformReferenceCumulative_zero] using!
      hmono (left_mem_Icc.2 Real.pi_pos.le) htheta htheta.1
  · simpa [platformReferenceCumulative_pi k ha ha2.le] using!
      hmono htheta (right_mem_Icc.2 Real.pi_pos.le) htheta.2

/-- Existence and uniqueness of a cut having prescribed physical reference
mass. -/
theorem existsUnique_platformReferenceCumulative_eq
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (u : Icc (0 : ℝ) 1) :
    ∃! theta : ℝ, theta ∈ Icc 0 Real.pi ∧
      platformReferenceCumulative k a theta = u := by
  have hcont := continuous_platformReferenceCumulative k ha ha2.le
  have hu : (u : ℝ) ∈ Icc
      (platformReferenceCumulative k a 0)
      (platformReferenceCumulative k a Real.pi) := by
    rw [platformReferenceCumulative_zero,
      platformReferenceCumulative_pi k ha ha2.le]
    exact u.property
  obtain ⟨theta, htheta, hvalue⟩ :=
    intermediate_value_Icc Real.pi_pos.le hcont hu
  refine ⟨theta, ⟨htheta, hvalue⟩, ?_⟩
  intro phi hphi
  exact (platformReferenceCumulative_strictMonoOn hk ha ha2 hthreshold).injOn
    hphi.1 htheta (hphi.2.trans hvalue.symm)

/-- The unique angular cut whose accumulated physical reference mass is
`u`. -/
def platformReferenceCut
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (u : Icc (0 : ℝ) 1) : ℝ :=
  Classical.choose
    (existsUnique_platformReferenceCumulative_eq
      k a hk ha ha2 hthreshold u)

lemma platformReferenceCut_spec
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (u : Icc (0 : ℝ) 1) :
    platformReferenceCut k a hk ha ha2 hthreshold u ∈ Icc 0 Real.pi ∧
      platformReferenceCumulative k a
          (platformReferenceCut k a hk ha ha2 hthreshold u) = u := by
  exact (Classical.choose_spec
    (existsUnique_platformReferenceCumulative_eq
      k a hk ha ha2 hthreshold u)).1

lemma platformReferenceCut_mem_Icc
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (u : Icc (0 : ℝ) 1) :
    platformReferenceCut k a hk ha ha2 hthreshold u ∈ Icc 0 Real.pi :=
  (platformReferenceCut_spec k a hk ha ha2 hthreshold u).1

@[simp]
lemma platformReferenceCumulative_cut
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (u : Icc (0 : ℝ) 1) :
    platformReferenceCumulative k a
        (platformReferenceCut k a hk ha ha2 hthreshold u) = u :=
  (platformReferenceCut_spec k a hk ha ha2 hthreshold u).2

theorem platformReferenceCut_strictMono
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    StrictMono (platformReferenceCut k a hk ha ha2 hthreshold) := by
  intro u v huv
  have hcu := platformReferenceCut_mem_Icc k a hk ha ha2 hthreshold u
  have hcv := platformReferenceCut_mem_Icc k a hk ha ha2 hthreshold v
  apply lt_of_not_ge
  intro hnot
  have hrev :=
    (platformReferenceCumulative_strictMonoOn hk ha ha2 hthreshold).monotoneOn
      hcv hcu hnot
  rw [platformReferenceCumulative_cut, platformReferenceCumulative_cut] at hrev
  exact (not_le_of_gt huv) hrev

@[simp]
theorem platformReferenceCut_zero
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    platformReferenceCut k a hk ha ha2 hthreshold
        ⟨0, by constructor <;> norm_num⟩ = 0 := by
  apply (platformReferenceCumulative_strictMonoOn
    hk ha ha2 hthreshold).injOn
  · exact platformReferenceCut_mem_Icc k a hk ha ha2 hthreshold _
  · exact left_mem_Icc.2 Real.pi_pos.le
  · rw [platformReferenceCumulative_cut,
      platformReferenceCumulative_zero]

@[simp]
theorem platformReferenceCut_one
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    platformReferenceCut k a hk ha ha2 hthreshold
        ⟨1, by constructor <;> norm_num⟩ = Real.pi := by
  apply (platformReferenceCumulative_strictMonoOn
    hk ha ha2 hthreshold).injOn
  · exact platformReferenceCut_mem_Icc k a hk ha ha2 hthreshold _
  · exact right_mem_Icc.2 Real.pi_pos.le
  · rw [platformReferenceCumulative_cut,
      platformReferenceCumulative_pi k ha ha2.le]

theorem platformReferenceIntervalMass_cut
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {u v : Icc (0 : ℝ) 1} (huv : u ≤ v) :
    platformReferenceIntervalMass k a
        (platformReferenceCut k a hk ha ha2 hthreshold u)
        (platformReferenceCut k a hk ha ha2 hthreshold v) =
      (v : ℝ) - u := by
  have hcu := platformReferenceCut_mem_Icc k a hk ha ha2 hthreshold u
  have hcv := platformReferenceCut_mem_Icc k a hk ha ha2 hthreshold v
  have hcuts : platformReferenceCut k a hk ha ha2 hthreshold u ≤
      platformReferenceCut k a hk ha ha2 hthreshold v :=
    (platformReferenceCut_strictMono k a hk ha ha2 hthreshold).monotone huv
  rw [← platformReferenceCumulative_sub ha ha2.le
    hcu.1 hcuts hcv.2,
    platformReferenceCumulative_cut,
    platformReferenceCumulative_cut]

end

end Erdos1038
