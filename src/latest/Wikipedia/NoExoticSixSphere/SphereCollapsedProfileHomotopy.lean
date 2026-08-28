import Wikipedia.NoExoticSixSphere.SphereSumCappedNeck

/-!
# Linearization of the collapsed radial profile

Interpolate between the flat zero-opening profile and the positive part of
the radial coordinate. Every interpolation is zero on the negative half-line
and exactly linear beyond time two. The same product-of-balls bound holds
throughout the actual unit parameter interval.
-/

noncomputable section

open Set Function Metric Topology

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

def linearizingProfile (b : unitInterval) (t : ℝ) : ℝ :=
  (1 - b.val) * capProfile 0 t + b.val * max t 0

theorem continuous_linearizingProfile :
    Continuous (fun p : unitInterval × ℝ ↦ linearizingProfile p.1 p.2) := by
  have hb : Continuous (fun p : unitInterval × ℝ ↦ p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  exact ((continuous_const.sub hb).mul
    ((contDiff_capProfile_slice 0).continuous.comp continuous_snd)).add
      (hb.mul (continuous_snd.max continuous_const))

theorem linearizingProfile_zero (t : ℝ) : linearizingProfile 0 t = capProfile 0 t := by
  simp [linearizingProfile]

theorem linearizingProfile_one (t : ℝ) : linearizingProfile 1 t = max t 0 := by
  simp [linearizingProfile]

theorem linearizingProfile_nonneg (b : unitInterval) (t : ℝ) : 0 ≤ linearizingProfile b t :=
  add_nonneg (mul_nonneg (sub_nonneg.mpr b.property.2) (capProfile_nonneg 0 t))
    (mul_nonneg b.property.1 (le_max_right _ _))

theorem linearizingProfile_of_nonpos (b : unitInterval) {t : ℝ} (ht : t ≤ 0) :
    linearizingProfile b t = 0 := by
  have hz : capProfile 0 t = 0 := (capProfile_zero_iff le_rfl t).mpr (by simpa using ht)
  simp [linearizingProfile, hz, max_eq_right ht]

theorem linearizingProfile_of_two_le (b : unitInterval) {t : ℝ} (ht : 2 ≤ t) :
    linearizingProfile b t = t := by
  rw [linearizingProfile, capProfile_eq_id 0 t ht, max_eq_left (by linarith)]
  ring

theorem linearizingProfile_le (b : unitInterval) {t R : ℝ} (hR : 1 ≤ R) (ht : t ≤ R) :
    linearizingProfile b t ≤ R := by
  have hp := mul_le_mul_of_nonneg_left (capProfile_le 0 hR ht)
    (sub_nonneg.mpr b.property.2)
  have hm : max t 0 ≤ R := max_le ht (by linarith)
  have hm' := mul_le_mul_of_nonneg_left hm b.property.1
  dsimp [linearizingProfile]
  nlinarith

def linearPair (q : Parameter) : Vector 3 × Vector 3 :=
  (max q.1 0 • q.2.val, max (-q.1) 0 • q.2.val)

def linearizingPair (p : unitInterval × Parameter) : Vector 3 × Vector 3 :=
  (linearizingProfile p.1 p.2.1 • p.2.2.val,
    linearizingProfile p.1 (-p.2.1) • p.2.2.val)

theorem continuous_linearizingPair : Continuous linearizingPair := by
  have ht : Continuous (fun p : unitInterval × Parameter ↦ p.2.1) :=
    continuous_fst.comp continuous_snd
  have hs : Continuous (fun p : unitInterval × Parameter ↦ p.2.2.val) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  exact ((continuous_linearizingProfile.comp (continuous_fst.prodMk ht)).smul hs).prodMk
    ((continuous_linearizingProfile.comp (continuous_fst.prodMk ht.neg)).smul hs)

theorem linearizingPair_zero (q : Parameter) : linearizingPair (0, q) = capPair 0 q := by
  simp only [linearizingPair, linearizingProfile_zero, capPair]

theorem linearizingPair_one (q : Parameter) : linearizingPair (1, q) = linearPair q := by
  simp only [linearizingPair, linearizingProfile_one, linearPair]

theorem linearizingPair_right (b : unitInterval) (q : Parameter) (ht : 2 ≤ q.1) :
    linearizingPair (b, q) = (q.1 • q.2.val, 0) := by
  simp only [linearizingPair, linearizingProfile_of_two_le b ht,
    linearizingProfile_of_nonpos b (show -q.1 ≤ 0 by linarith), zero_smul]

theorem linearizingPair_left (b : unitInterval) (q : Parameter) (ht : q.1 ≤ -2) :
    linearizingPair (b, q) = (0, (-q.1) • q.2.val) := by
  simp only [linearizingPair, linearizingProfile_of_two_le b (show 2 ≤ -q.1 by linarith),
    linearizingProfile_of_nonpos b (show q.1 ≤ 0 by linarith), zero_smul]

theorem scaled_linearizingPair_mem_product {ε R : ℝ} (hε : 0 < ε) (hR : 1 ≤ R)
    (b : unitInterval) (q : Parameter) (hq : q.1 ∈ Icc (-R) R) :
    ε • linearizingPair (b, q) ∈
      closedBall (0 : Vector 3) (ε * R) ×ˢ closedBall (0 : Vector 3) (ε * R) := by
  have hn (t : ℝ) (ht : t ≤ R) : ‖ε • (linearizingProfile b t • q.2.val)‖ ≤ ε * R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (linearizingProfile_nonneg b t), ClosedHemisphere.unit_norm, mul_one]
    exact mul_le_mul_of_nonneg_left (linearizingProfile_le b hR ht) hε.le
  exact ⟨by simpa [linearizingPair, mem_closedBall, dist_zero_right] using hn q.1 hq.2,
    by simpa [linearizingPair, mem_closedBall, dist_zero_right]
      using hn (-q.1) (by linarith [hq.1])⟩

end NoExoticSixSphere.SphereSumNeck
