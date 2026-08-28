import Wikipedia.SmoothSixDPoincare.CompactSmoothCutoff
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Smooth cutoffs with arbitrarily small logarithmic derivative

A fixed compact bump is composed with a regularized logarithm. The
regularization makes the formula smooth even at zero; a large logarithmic
scale makes `abs (t * deriv χ t)` uniformly as small as required. This is
the derivative control needed to blend two descending heights which agree
on a level, without losing descent to the cutoff derivative.
-/

noncomputable section

open Set Function Filter
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

def logarithmicCoordinate (η L t : ℝ) : ℝ :=
  Real.log (1 + (t / η) ^ 2) / L

theorem contDiff_logarithmicCoordinate (η L : ℝ) :
    ContDiff ℝ ∞ (logarithmicCoordinate η L) := by
  apply ContDiff.div_const
  apply ContDiff.log
  · exact contDiff_const.add ((contDiff_id.div_const η).pow 2)
  · intro t
    positivity

theorem hasDerivAt_logarithmicCoordinate {η L : ℝ} (hη : 0 < η) (hL : 0 < L) (t : ℝ) :
    HasDerivAt (logarithmicCoordinate η L)
      (2 * t / (L * (η ^ 2 + t ^ 2))) t := by
  have hp : 1 + (t / η) ^ 2 ≠ 0 := by positivity
  have hh := (((((hasDerivAt_id t).div_const η).pow 2).const_add 1).log hp).div_const L
  convert hh using 1 <;> try rfl
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp

theorem logarithmicCoordinate_weighted_deriv_bound {η L : ℝ}
    (hη : 0 < η) (hL : 0 < L) (t : ℝ) :
    |t * deriv (logarithmicCoordinate η L) t| ≤ 2 / L := by
  rw [(hasDerivAt_logarithmicCoordinate hη hL t).deriv]
  have hden : 0 < η ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hη) (sq_nonneg t)
  have heq : t * (2 * t / (L * (η ^ 2 + t ^ 2))) =
      (2 / L) * (t ^ 2 / (η ^ 2 + t ^ 2)) := by
    field_simp
  rw [heq, abs_of_nonneg (by positivity)]
  exact mul_le_of_le_one_right (by positivity) ((div_le_one hden).mpr (by nlinarith))

/-- The cutoff is one on a genuine neighborhood of zero, vanishes outside
the prescribed radius, and has an arbitrarily small weighted derivative. -/
theorem exists_logarithmic_cutoff {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ᶠ t in 𝓝 0, χ t = 1) ∧
      (∀ t, ε ≤ |t| → χ t = 0) ∧
      (∀ t, χ t ∈ Icc (0 : ℝ) 1) ∧ ∀ t, |t * deriv χ t| < δ := by
  obtain ⟨β, hβ, hcompact, hsupp, hone, hrange⟩ :=
    Wikipedia.SmoothSixDPoincare.exists_compact_smooth_cutoff
      (K := {(0 : ℝ)}) (U := Metric.ball 0 1) isCompact_singleton Metric.isOpen_ball
      (by simp)
  obtain ⟨C, hC⟩ := hcompact.deriv.exists_bound_of_continuous
    (hβ.continuous_deriv (by simp))
  let B : ℝ := max C 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hbound (t : ℝ) : |deriv β t| ≤ B := by
    have hh := hC t
    rw [Real.norm_eq_abs] at hh
    exact hh.trans (by dsimp [B]; linarith [le_max_left C 0])
  let L : ℝ := 2 * B / δ + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hsmall : B * (2 / L) < δ := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hL).mpr
    dsimp [L]
    have hd : δ * (2 * B / δ) = 2 * B := by field_simp
    nlinarith
  let η : ℝ := ε / Real.exp L
  have hη : 0 < η := div_pos hε (Real.exp_pos L)
  let q := logarithmicCoordinate η L
  have hq : ContDiff ℝ ∞ q := contDiff_logarithmicCoordinate η L
  have hqzero : q 0 = 0 := by simp [q, logarithmicCoordinate]
  let χ : ℝ → ℝ := β ∘ q
  have hχ : ContDiff ℝ ∞ χ := hβ.comp hq
  have hout (t : ℝ) (ht : ε ≤ |t|) : χ t = 0 := by
    have hratio : Real.exp L ≤ |t / η| := by
      rw [abs_div, abs_of_pos hη, le_div_iff₀ hη]
      have he : Real.exp L * η = ε := by dsimp [η]; field_simp
      simpa only [he] using ht
    have heone : 1 ≤ Real.exp L := Real.one_le_exp_iff.mpr hL.le
    have hlower : L ≤ Real.log (1 + (t / η) ^ 2) := by
      apply (Real.le_log_iff_exp_le (by positivity)).mpr
      nlinarith [sq_abs (t / η)]
    have honeq : 1 ≤ q t := (le_div_iff₀ hL).mpr (by simpa using hlower)
    have hnotsupp : q t ∉ tsupport β := by
      intro hh
      have hball := hsupp hh
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] at hball
      linarith [hball.2]
    change β (q t) = 0
    exact image_eq_zero_of_notMem_tsupport hnotsupp
  have hcompactχ : HasCompactSupport χ := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-ε) ε))
    intro t ht
    apply hout
    by_contra h
    have hh := abs_lt.mp (lt_of_not_ge h)
    exact ht ⟨hh.1.le, hh.2.le⟩
  have hnear : ∀ᶠ t in 𝓝 0, χ t = 1 := by
    have hb : ∀ᶠ r in 𝓝 (0 : ℝ), β r = 1 := by simpa only [nhdsSet_singleton] using hone
    have ht : Tendsto q (𝓝 0) (𝓝 0) := by
      have hh : Tendsto q (𝓝 0) (𝓝 (q 0)) := hq.continuous.continuousAt
      simpa only [hqzero] using hh
    exact ht.eventually hb
  refine ⟨χ, hχ, hcompactχ, hnear, hout, fun t => hrange (q t), ?_⟩
  intro t
  have hder : deriv χ t = deriv β (q t) * deriv q t :=
    ((hβ.differentiable (by simp)).differentiableAt.hasDerivAt.comp t
      (hq.differentiable (by simp)).differentiableAt.hasDerivAt).deriv
  rw [hder]
  have he : |t * (deriv β (q t) * deriv q t)| =
      |deriv β (q t)| * |t * deriv q t| := by rw [← abs_mul]; congr 1; ring
  rw [he]
  exact lt_of_le_of_lt (mul_le_mul (hbound _) (logarithmicCoordinate_weighted_deriv_bound hη hL t)
    (abs_nonneg _) hB.le) hsmall

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation
