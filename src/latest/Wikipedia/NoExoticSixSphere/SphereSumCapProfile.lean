import Wikipedia.NoExoticSixSphere.SphereSumNeckProfile
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# A flat neck profile with exact linear cap coordinates

The opening parameter moves the flat endpoint from zero to minus one.
For times at most one this is the original exponential profile; for times
at least two it is exactly the identity. A monotone smooth transition
preserves strictly positive speed on the positive region. Exact linearity
at infinity is needed for smooth extension across the source sphere poles.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff

namespace NoExoticSixSphere.SphereSumNeck

def capProfile (a t : ℝ) : ℝ :=
  profile (t + a - 1) + Real.smoothTransition (t - 1) * (t - profile (t + a - 1))

theorem contDiff_capProfile :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ capProfile p.1 p.2) := by
  have hp : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ profile (p.2 + p.1 - 1)) :=
    contDiff_profile.comp ((contDiff_snd.add contDiff_fst).sub contDiff_const)
  exact hp.add ((Real.smoothTransition.contDiff.comp
    (contDiff_snd.sub contDiff_const)).mul (contDiff_snd.sub hp))

theorem contDiff_capProfile_slice (a : ℝ) : ContDiff ℝ ∞ (capProfile a) :=
  contDiff_capProfile.comp (contDiff_const.prodMk contDiff_id)

theorem capProfile_eq_profile (a t : ℝ) (ht : t ≤ 1) :
    capProfile a t = profile (t + a - 1) := by
  have hz := Real.smoothTransition.zero_of_nonpos (show t - 1 ≤ 0 by linarith)
  simp only [capProfile, hz, zero_mul, add_zero]

theorem capProfile_eq_id (a t : ℝ) (ht : 2 ≤ t) : capProfile a t = t := by
  have ho := Real.smoothTransition.one_of_one_le (show 1 ≤ t - 1 by linarith)
  simp only [capProfile, ho, one_mul, add_sub_cancel]

theorem capProfile_weighted (a t : ℝ) : capProfile a t =
    (1 - Real.smoothTransition (t - 1)) * profile (t + a - 1) +
      Real.smoothTransition (t - 1) * t := by
  dsimp [capProfile]
  ring

theorem capProfile_nonneg (a t : ℝ) : 0 ≤ capProfile a t := by
  by_cases ht : t ≤ 1
  · rw [capProfile_eq_profile a t ht]
    exact profile_nonneg _
  · rw [capProfile_weighted]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr (Real.smoothTransition.le_one _))
      (profile_nonneg _)) (mul_nonneg (Real.smoothTransition.nonneg _) (by linarith))

theorem capProfile_pos {a t : ℝ} (ht : -a < t) : 0 < capProfile a t := by
  have hp : 0 < profile (t + a - 1) := (profile_pos_iff _).mpr (by linarith)
  by_cases hsmall : t ≤ 1
  · rw [capProfile_eq_profile a t hsmall]
    exact hp
  · have hb := Real.smoothTransition.nonneg (t - 1)
    have hb1 := Real.smoothTransition.le_one (t - 1)
    rw [capProfile_weighted]
    by_cases hlt : Real.smoothTransition (t - 1) < 1
    · exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) hp)
        (mul_nonneg hb (by linarith))
    · have he : Real.smoothTransition (t - 1) = 1 := by linarith
      simp only [he, sub_self, zero_mul, one_mul, zero_add]
      linarith

theorem capProfile_zero_iff {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    capProfile a t = 0 ↔ t ≤ -a := by
  constructor
  · intro hz
    by_contra ht
    exact (capProfile_pos (lt_of_not_ge ht)).ne' hz
  · intro ht
    rw [capProfile_eq_profile a t (by linarith), profile_zero_iff]
    linarith

theorem capProfile_pos_iff {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    0 < capProfile a t ↔ -a < t := by
  rw [lt_iff_le_and_ne]
  constructor
  · rintro ⟨_, hn⟩
    exact lt_of_not_ge (fun ht ↦ hn ((capProfile_zero_iff ha t).mpr ht).symm)
  · intro ht
    exact ⟨capProfile_nonneg a t, (capProfile_pos ht).ne⟩

theorem capProfile_le (a : ℝ) {t R : ℝ} (hR : 1 ≤ R) (ht : t ≤ R) :
    capProfile a t ≤ R := by
  by_cases hs : t ≤ 1
  · rw [capProfile_eq_profile a t hs]
    linarith [profile_lt_one (t + a - 1)]
  · have hb := Real.smoothTransition.nonneg (t - 1)
    have hb1 := Real.smoothTransition.le_one (t - 1)
    have hp : profile (t + a - 1) ≤ R := by linarith [profile_lt_one (t + a - 1)]
    have h1 := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr hb1)
    have h2 := mul_le_mul_of_nonneg_left ht hb
    rw [capProfile_weighted]
    nlinarith

theorem capProfile_le_two (a : ℝ) {t : ℝ} (ht : t ≤ 2) : capProfile a t ≤ 2 :=
  capProfile_le a (by norm_num) ht

def capSpeed (a t : ℝ) : ℝ :=
  (1 - Real.smoothTransition (t - 1)) * speed (t + a - 1) +
    Real.smoothTransition (t - 1) +
    deriv Real.smoothTransition (t - 1) * (t - profile (t + a - 1))

theorem hasDerivAt_capProfile (a t : ℝ) : HasDerivAt (capProfile a) (capSpeed a t) t := by
  have hp : HasDerivAt (fun s : ℝ ↦ profile (s + a - 1)) (speed (t + a - 1)) t := by
    simpa using! (hasDerivAt_profile (t + a - 1)).comp t
      (((hasDerivAt_id t).add_const a).sub_const 1)
  have hb : HasDerivAt (fun s : ℝ ↦ Real.smoothTransition (s - 1))
      (deriv Real.smoothTransition (t - 1)) t := by
    have hc : ContDiff ℝ 1 Real.smoothTransition := Real.smoothTransition.contDiff
    simpa using! ((hc.differentiable (by simp) (t - 1)).hasDerivAt).comp t
      ((hasDerivAt_id t).sub_const 1)
  have h := hp.add (hb.mul ((hasDerivAt_id t).sub hp))
  have he : capSpeed a t = speed (t + a - 1) +
      (deriv Real.smoothTransition (t - 1) * (t - profile (t + a - 1)) +
        Real.smoothTransition (t - 1) * (1 - speed (t + a - 1))) := by
    dsimp [capSpeed]
    ring
  rw [he]
  simpa [capProfile] using! h

theorem deriv_capProfile_pos {a t : ℝ} (ht : -a < t) :
    0 < deriv (capProfile a) t := by
  by_cases hs : t < 1
  · have he : capProfile a =ᶠ[𝓝 t] (fun s ↦ profile (s + a - 1)) := by
      filter_upwards [Iio_mem_nhds hs] with s hs
      exact capProfile_eq_profile a s hs.le
    have hp : HasDerivAt (fun s : ℝ ↦ profile (s + a - 1)) (speed (t + a - 1)) t := by
      simpa using! (hasDerivAt_profile (t + a - 1)).comp t
        (((hasDerivAt_id t).add_const a).sub_const 1)
    rw [he.deriv_eq, hp.deriv]
    simpa using speed_pos (show -1 < t + a - 1 by linarith)
  · rw [(hasDerivAt_capProfile a t).deriv, capSpeed]
    have hb := Real.smoothTransition.nonneg (t - 1)
    have hb1 := Real.smoothTransition.le_one (t - 1)
    have hd : 0 ≤ deriv Real.smoothTransition (t - 1) :=
      Real.smoothTransition.monotone.deriv_nonneg
    have hp := speed_pos (show -1 < t + a - 1 by linarith)
    have hlast : 0 ≤ deriv Real.smoothTransition (t - 1) * (t - profile (t + a - 1)) :=
      mul_nonneg hd (by linarith [profile_lt_one (t + a - 1)])
    apply add_pos_of_pos_of_nonneg _ hlast
    by_cases hlt : Real.smoothTransition (t - 1) < 1
    · exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) hp) hb
    · have he : Real.smoothTransition (t - 1) = 1 := by linarith
      simp only [he, sub_self, zero_mul, zero_add]
      norm_num

theorem capProfile_strictMonoOn (a : ℝ) :
    StrictMonoOn (capProfile a) (Ioi (-a)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi (-a))
    (contDiff_capProfile_slice a).continuous.continuousOn
  intro t ht
  exact deriv_capProfile_pos (interior_subset ht)

end NoExoticSixSphere.SphereSumNeck
