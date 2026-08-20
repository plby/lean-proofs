import ErdosProblems.Erdos515.Prawitz
import ErdosProblems.Erdos515.External.Ray.Koebe.Koebe
import ErdosProblems.Erdos515.External.Ray.Schwarz.Mobius
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The upper Koebe distortion estimate

This file derives the upper growth estimate for normalized univalent maps of the disk from the
Bieberbach coefficient inequality.  The latter is supplied by the fully proved `Ray` development,
pinned in this project's Lake manifest to its Mathlib-v4.33.0 revision.
-/

open Metric (ball isOpen_ball)
open Set
open scoped ComplexConjugate ContDiff RealInnerProductSpace

noncomputable section

namespace Erdos515
namespace KoebeDistortion

variable {G : ℂ → ℂ}

private lemma zero_mem_unitBall : (0 : ℂ) ∈ ball 0 1 := by simp

/-- Bieberbach applied after moving `a` to the origin.  This is the classical
pre-Schwarzian estimate from which Koebe distortion follows. -/
theorem preSchwarzian_bound
    (hG : AnalyticOnNhd ℂ G (ball 0 1)) (hinj : InjOn G (ball 0 1))
    {a : ℂ} (ha : ‖a‖ < 1) :
    ‖((‖a‖ ^ 2 - 1 : ℝ) : ℂ) * (deriv (deriv G) a / deriv G a) + 2 * conj a‖ ≤ 4 := by
  have hamem : a ∈ ball (0 : ℂ) 1 := by simpa using ha
  by_cases hdG : deriv G a = 0
  · simp only [hdG, div_zero, mul_zero, zero_add]
    simpa [norm_mul] using (show 2 * ‖a‖ ≤ 4 by nlinarith [norm_nonneg a])
  have hq : (((‖a‖ ^ 2 - 1 : ℝ) : ℂ)) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero, sub_eq_zero]
    nlinarith [sq_lt_sq₀ (norm_nonneg a) (by norm_num : (0 : ℝ) ≤ 1) |>.2 ha]
  have hqd : (((‖a‖ ^ 2 - 1 : ℝ) : ℂ)) * deriv G a ≠ 0 := mul_ne_zero hq hdG
  let K : ℂ → ℂ := fun z ↦
    (G (mobius a z) - G a) / ((((‖a‖ ^ 2 - 1 : ℝ) : ℂ)) * deriv G a)
  have hmob : AnalyticOnNhd ℂ (mobius a) (ball 0 1) :=
    (contDiffOn_mobius (n := ω) ha).analyticOnNhd isOpen_ball
  have hKa : AnalyticOnNhd ℂ K (ball 0 1) := by
    exact ((hG.comp hmob (mapsTo_mobius ha)).sub analyticOnNhd_const).div
      analyticOnNhd_const (fun _ _ ↦ hqd)
  have hKinj : InjOn K (ball 0 1) := by
    intro z hz w hw he
    simp only [K] at he
    have he' := (div_left_inj' hqd).mp he
    have hG_eq : G (mobius a z) = G (mobius a w) := by
      simpa only [sub_left_inj] using he'
    exact (injOn_mobius ha).eq_iff hz hw |>.1
      ((hinj.eq_iff (mapsTo_mobius ha hz) (mapsTo_mobius ha hw)).1 hG_eq)
  have hK0 : K 0 = 0 := by simp [K]
  have hKderiv : ∀ z ∈ ball (0 : ℂ) 1,
      deriv K z = deriv G (mobius a z) * deriv (mobius a) z /
        ((((‖a‖ ^ 2 - 1 : ℝ) : ℂ)) * deriv G a) := by
    intro z hz
    simp only [K, deriv_div_const, deriv_sub_const_fun]
    change deriv (G ∘ mobius a) z / _ = _
    rw [deriv_comp z (hG _ (mapsTo_mobius ha hz)).differentiableAt
      (hmob z hz).differentiableAt]
  have hKd0 : deriv K 0 = 1 := by
    rw [hKderiv 0 zero_mem_unitBall, mobius_zero, deriv_mobius_zero ha]
    rw [mul_comm]
    convert div_self hqd using 1 <;> push_cast <;> rfl
  have hKK : (fun z ↦ deriv K z) =ᶠ[nhds 0]
      (fun z ↦ deriv G (mobius a z) * deriv (mobius a) z /
        ((((‖a‖ ^ 2 - 1 : ℝ) : ℂ)) * deriv G a)) :=
    EqOn.eventuallyEq_of_mem hKderiv (isOpen_ball.mem_nhds zero_mem_unitBall)
  have hddK : deriv (deriv K) 0 =
      (((‖a‖ ^ 2 - 1 : ℝ) : ℂ) * (deriv (deriv G) a / deriv G a) +
        2 * conj a) := by
    rw [hKK.deriv_eq]
    have hGa : DifferentiableAt ℂ (deriv G) a := (hG a hamem).deriv.differentiableAt
    have hm0 : DifferentiableAt ℂ (mobius a) 0 :=
      (hmob 0 zero_mem_unitBall).differentiableAt
    have hGa0 : DifferentiableAt ℂ (deriv G) (mobius a 0) := by
      simpa only [mobius_zero] using hGa
    have hdm0 : DifferentiableAt ℂ (deriv (mobius a)) 0 :=
      (hmob 0 zero_mem_unitBall).deriv.differentiableAt
    rw [deriv_div_const]
    change deriv ((deriv G ∘ mobius a) * fun z ↦ deriv (mobius a) z) 0 / _ = _
    rw [deriv_mul (hGa0.comp 0 hm0) hdm0]
    rw [deriv_comp 0 hGa0 hm0]
    rw [deriv_mobius_zero ha]
    have hdm : deriv (deriv (mobius a)) 0 =
        2 * conj a * (((‖a‖ ^ 2 - 1 : ℝ) : ℂ)) := by
      have he : (fun z ↦ deriv (mobius a) z) =ᶠ[nhds 0]
          (fun z ↦ (((‖a‖ ^ 2 - 1 : ℝ) : ℂ)) /
            (1 - conj a * z) ^ 2) := by
        filter_upwards [isOpen_ball.mem_nhds zero_mem_unitBall] with z hz
        convert deriv_mobius ha (by simpa using hz) using 1 <;> push_cast <;> rfl
      rw [he.deriv_eq]
      have hinner := (hasDerivAt_const (x := (0 : ℂ)) (1 : ℂ)).sub
        ((hasDerivAt_id' (x := (0 : ℂ))).const_mul (conj a))
      have hpow := hinner.pow 2
      have hfrac := (hasDerivAt_const (x := (0 : ℂ))
        ((((‖a‖ ^ 2 - 1 : ℝ) : ℂ)))).div hpow (by simp)
      have hfd := hfrac.deriv
      simp only [Pi.pow_apply, zero_mul, zero_sub, Nat.cast_ofNat,
        Nat.add_one_sub_one, pow_one, mul_one] at hfd
      have heq : (fun z : ℂ => (((‖a‖ ^ 2 - 1 : ℝ) : ℂ)) /
          (1 - conj a * z) ^ 2) =
          ((fun _ : ℂ => (((‖a‖ ^ 2 - 1 : ℝ) : ℂ))) /
            ((fun _ : ℂ => 1) - fun z : ℂ => conj a * z) ^ 2) := by
        funext z
        rfl
      rw [heq, hfd]
      simp
      ring
    rw [hdm, mobius_zero]
    simp only [Function.comp_apply, mobius_zero]
    field_simp [hq, hdG]
    push_cast
    ring
  have hb := bieberbach hKa hKinj hK0 hKd0
  rw [hddK] at hb
  exact hb

/-- The real-part form of the pre-Schwarzian estimate along a radius. -/
theorem radial_logDeriv_re_le
    (hG : AnalyticOnNhd ℂ G (ball 0 1)) (hinj : InjOn G (ball 0 1))
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (hd : deriv G ((t : ℂ) * ζ) ≠ 0) :
    (ζ * (deriv (deriv G) ((t : ℂ) * ζ) / deriv G ((t : ℂ) * ζ))).re ≤
      (4 + 2 * t) / (1 - t ^ 2) := by
  let a : ℂ := (t : ℂ) * ζ
  have ha_norm : ‖a‖ = t := by
    simp only [a, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht, hζ, mul_one]
  have ha : ‖a‖ < 1 := ha_norm.trans_lt ht1
  have hb := preSchwarzian_bound hG hinj ha
  let Q : ℂ := deriv (deriv G) a / deriv G a
  have hb' : ‖ζ * ((((‖a‖ ^ 2 - 1 : ℝ) : ℂ) * Q + 2 * conj a))‖ ≤ 4 := by
    rw [norm_mul, hζ, one_mul]
    exact hb
  have hrewrite :
      ζ * ((((‖a‖ ^ 2 - 1 : ℝ) : ℂ) * Q + 2 * conj a)) =
        (((t ^ 2 - 1 : ℝ) : ℂ) * (ζ * Q) + ((2 * t : ℝ) : ℂ)) := by
    have hzc : ζ * conj ζ = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ]
      norm_num
    simp only [a, ha_norm, map_mul, Complex.conj_ofReal]
    push_cast
    calc
      ζ * (((t : ℂ) ^ 2 - 1) * Q + 2 * ((t : ℂ) * conj ζ)) =
          (((t : ℂ) ^ 2 - 1) * (ζ * Q) + (2 * (t : ℂ)) * (ζ * conj ζ)) := by ring
      _ = (((t : ℂ) ^ 2 - 1) * (ζ * Q) + 2 * (t : ℂ)) := by rw [hzc, mul_one]
  have hre : -4 ≤
      (ζ * ((((‖a‖ ^ 2 - 1 : ℝ) : ℂ) * Q + 2 * conj a))).re := by
    exact (neg_le_neg hb').trans
      ((neg_le_neg (Complex.abs_re_le_norm _)).trans (neg_abs_le _))
  rw [hrewrite] at hre
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero] at hre
  have hden : 0 < 1 - t ^ 2 := by nlinarith
  apply (le_div_iff₀ hden).2
  change (ζ.re * Q.re - ζ.im * Q.im) * (1 - t ^ 2) ≤ 4 + 2 * t
  nlinarith [hre]

/-- Differential inequality for the squared norm of the derivative along a radius. -/
theorem radial_deriv_normSq_slope_le
    (hG : AnalyticOnNhd ℂ G (ball 0 1)) (hinj : InjOn G (ball 0 1))
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    inner ℝ (deriv G ((t : ℂ) * ζ))
        (ζ * deriv (deriv G) ((t : ℂ) * ζ)) ≤
      ((4 + 2 * t) / (1 - t ^ 2)) * ‖deriv G ((t : ℂ) * ζ)‖ ^ 2 := by
  let p : ℂ := deriv G ((t : ℂ) * ζ)
  let q : ℂ := deriv (deriv G) ((t : ℂ) * ζ)
  by_cases hp : p = 0
  · simp [p, q, hp]
  have hlog := radial_logDeriv_re_le hG hinj ht ht1 hζ hp
  have hinner : inner ℝ p (ζ * q) = ‖p‖ ^ 2 * (ζ * (q / p)).re := by
    rw [Complex.inner]
    have heq : ζ * q * conj p = ((‖p‖ ^ 2 : ℝ) : ℂ) * (ζ * (q / p)) := by
      have hnorm : (((‖p‖ ^ 2 : ℝ) : ℂ)) = p * conj p := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self, mul_comm]
      rw [hnorm]
      field_simp [hp]
    rw [heq]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hinner]
  simpa only [p, q, mul_comm, mul_left_comm] using
    (mul_le_mul_of_nonneg_left hlog (sq_nonneg ‖p‖))

private def distortionWeight (t : ℝ) : ℝ :=
  (1 - t) ^ 6 / (1 + t) ^ 2

private def derivMajorant (t : ℝ) : ℝ :=
  (1 + t) / (1 - t) ^ 3

private lemma hasDerivAt_distortionWeight {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    HasDerivAt distortionWeight
      (-2 * ((4 + 2 * t) / (1 - t ^ 2)) * distortionWeight t) t := by
  have hden : (1 + t) ^ 2 ≠ 0 := by positivity
  have hraw := (((hasDerivAt_const t 1).sub (hasDerivAt_id t)).pow 6).div
    (((hasDerivAt_const t 1).add (hasDerivAt_id t)).pow 2) hden
  change HasDerivAt (((fun x : ℝ ↦ 1) - fun x ↦ x) ^ 6 /
    ((fun x : ℝ ↦ 1) + fun x ↦ x) ^ 2) _ t
  apply hraw.congr_deriv
  simp only [distortionWeight, Pi.div_apply, Pi.pow_apply, Pi.sub_apply, Pi.add_apply,
    id_eq, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one, zero_sub, zero_add]
  have hquad : 1 - t ^ 2 ≠ 0 := ne_of_gt (by nlinarith)
  have hplus : 1 + t ≠ 0 := ne_of_gt (by linarith)
  field_simp [hquad, hplus]
  ring

/-- The upper derivative distortion estimate on every radius. -/
theorem radial_deriv_norm_le
    (hG : AnalyticOnNhd ℂ G (ball 0 1)) (hinj : InjOn G (ball 0 1))
    (hG0' : deriv G 0 = 1) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ‖deriv G ((r : ℂ) * ζ)‖ ≤ derivMajorant r := by
  let p : ℝ → ℂ := fun t ↦ deriv G ((t : ℂ) * ζ)
  let V : ℝ → ℝ := fun t ↦ distortionWeight t * ‖p t‖ ^ 2
  have hpoint_mem : ∀ {t : ℝ}, t ∈ Icc 0 r → ((t : ℂ) * ζ) ∈ ball (0 : ℂ) 1 := by
    intro t ht
    simp only [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht.1, hζ, mul_one]
    exact ht.2.trans_lt hr1
  have hp_deriv : ∀ {t : ℝ}, t ∈ Icc 0 r →
      HasDerivAt p (ζ * deriv (deriv G) ((t : ℂ) * ζ)) t := by
    intro t ht
    have hcomplex : HasDerivAt (fun z : ℂ ↦ deriv G (z * ζ))
        (ζ * deriv (deriv G) ((t : ℂ) * ζ)) (t : ℂ) := by
      have hc := ((hG _ (hpoint_mem ht)).deriv.differentiableAt.hasDerivAt.comp (t : ℂ)
        (hasDerivAt_mul_const ζ))
      simpa only [mul_comm ζ] using! hc
    simpa only [p] using! hcomplex.comp_ofReal
  have hV_deriv : ∀ {t : ℝ}, t ∈ Icc 0 r →
      HasDerivAt V
        ((-2 * ((4 + 2 * t) / (1 - t ^ 2)) * distortionWeight t) * ‖p t‖ ^ 2 +
          distortionWeight t *
            (2 * inner ℝ (p t) (ζ * deriv (deriv G) ((t : ℂ) * ζ)))) t := by
    intro t ht
    exact (hasDerivAt_distortionWeight ht.1 (ht.2.trans_lt hr1)).mul ((hp_deriv ht).norm_sq)
  have hV_cont : ContinuousOn V (Icc 0 r) := by
    intro t ht
    exact (hV_deriv ht).continuousAt.continuousWithinAt
  have hV_anti : AntitoneOn V (Icc 0 r) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) r) hV_cont
    · intro t ht
      have ht' : t ∈ Icc 0 r := interior_subset ht
      exact (hV_deriv ht').differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Icc 0 r := interior_subset ht
      rw [(hV_deriv ht').deriv]
      have ht0 : 0 ≤ t := ht'.1
      have ht1 : t < 1 := ht'.2.trans_lt hr1
      have hslope := radial_deriv_normSq_slope_le hG hinj ht0 ht1 hζ
      have hw : 0 ≤ distortionWeight t := by
        simp only [distortionWeight]
        positivity
      nlinarith
  have hVle : V r ≤ V 0 := hV_anti (by exact ⟨le_rfl, hr⟩)
    (by exact ⟨hr, le_rfl⟩) hr
  have hp0 : p 0 = 1 := by simp [p, hG0']
  have hweighted : distortionWeight r * ‖p r‖ ^ 2 ≤ 1 := by
    simpa [V, hp0, distortionWeight] using hVle
  have hwpos : 0 < distortionWeight r := by
    exact div_pos (pow_pos (sub_pos.2 hr1) _) (pow_pos (by linarith : 0 < 1 + r) _)
  have hsquare : ‖p r‖ ^ 2 ≤ (derivMajorant r) ^ 2 := by
    have hdiv : ‖p r‖ ^ 2 ≤ 1 / distortionWeight r :=
      (le_div_iff₀ hwpos).2 (by simpa only [one_mul, mul_comm] using hweighted)
    calc
      ‖p r‖ ^ 2 ≤ 1 / distortionWeight r := hdiv
      _ = derivMajorant r ^ 2 := by
        simp only [distortionWeight, derivMajorant]
        field_simp
  have hmaj : 0 ≤ derivMajorant r := by
    exact div_nonneg (by linarith) (pow_nonneg (by linarith) _)
  exact (sq_le_sq₀ (norm_nonneg _) hmaj).mp (by simpa only [p] using hsquare)

private def growthPrimitive (t : ℝ) : ℝ :=
  t / (1 - t) ^ 2

private lemma hasDerivAt_growthPrimitive {t : ℝ} (ht : t < 1) :
    HasDerivAt growthPrimitive (derivMajorant t) t := by
  have hden : (1 - t) ^ 2 ≠ 0 := by positivity
  have hraw := (hasDerivAt_id t).div
    (((hasDerivAt_const t 1).sub (hasDerivAt_id t)).pow 2) hden
  change HasDerivAt ((fun x : ℝ ↦ x) /
    ((fun x : ℝ ↦ 1) - fun x ↦ x) ^ 2) _ t
  apply hraw.congr_deriv
  simp only [derivMajorant, Pi.div_apply, Pi.pow_apply, Pi.sub_apply, id_eq,
    Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one, zero_sub]
  have hminus : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht)
  field_simp [hminus]
  ring

/-- Koebe's upper growth estimate along a radius. -/
theorem radial_growth_le
    (hG : AnalyticOnNhd ℂ G (ball 0 1)) (hinj : InjOn G (ball 0 1))
    (hG0 : G 0 = 0) (hG0' : deriv G 0 = 1)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ‖G ((r : ℂ) * ζ)‖ ≤ growthPrimitive r := by
  let γ : ℝ → ℂ := fun t ↦ G ((t : ℂ) * ζ)
  let dγ : ℝ → ℂ := fun t ↦ ζ * deriv G ((t : ℂ) * ζ)
  have hpoint_mem : ∀ {t : ℝ}, t ∈ Icc 0 r → ((t : ℂ) * ζ) ∈ ball (0 : ℂ) 1 := by
    intro t ht
    simp only [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht.1, hζ, mul_one]
    exact ht.2.trans_lt hr1
  have hγderiv : ∀ {t : ℝ}, t ∈ Icc 0 r → HasDerivAt γ (dγ t) t := by
    intro t ht
    have hc := (hG _ (hpoint_mem ht)).differentiableAt.hasDerivAt.comp (t : ℂ)
      (hasDerivAt_mul_const ζ)
    have hr := hc.comp_ofReal
    simpa only [γ, dγ, mul_comm ζ] using! hr
  have hdγcont : ContinuousOn dγ (Icc 0 r) := by
    intro t ht
    have hinner : ContinuousAt (fun s : ℝ ↦ deriv G ((s : ℂ) * ζ)) t := by
      have hout : ContinuousAt (deriv G) ((t : ℂ) * ζ) :=
        (hG.deriv _ (hpoint_mem ht)).continuousAt
      have hin : ContinuousAt (fun s : ℝ ↦ (s : ℂ) * ζ) t :=
        Complex.continuous_ofReal.continuousAt.mul_const ζ
      exact ContinuousAt.comp (f := fun s : ℝ ↦ (s : ℂ) * ζ) hout hin
    exact (continuousAt_const.mul hinner).continuousWithinAt
  have hdγcont' : ContinuousOn dγ (uIcc 0 r) := by
    simpa [uIcc_of_le hr] using hdγcont
  have hγFTC : (∫ t in (0 : ℝ)..r, dγ t) = γ r - γ 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht ↦ hγderiv (by simpa [uIcc_of_le hr] using ht))
      hdγcont'.intervalIntegrable
  have hmajcont : ContinuousOn derivMajorant (Icc 0 r) := by
    intro t ht
    have hne : 1 - t ≠ 0 := by linarith [ht.2.trans_lt hr1]
    exact ((continuousAt_const.add continuousAt_id).div
      ((continuousAt_const.sub continuousAt_id).pow 3) (pow_ne_zero 3 hne)).continuousWithinAt
  have hmajcont' : ContinuousOn derivMajorant (uIcc 0 r) := by
    simpa [uIcc_of_le hr] using hmajcont
  have hprimFTC : (∫ t in (0 : ℝ)..r, derivMajorant t) =
      growthPrimitive r - growthPrimitive 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht ↦ by
        have ht' : t ∈ Icc 0 r := by simpa [uIcc_of_le hr] using ht
        exact hasDerivAt_growthPrimitive (ht'.2.trans_lt hr1))
      hmajcont'.intervalIntegrable
  have hnormInt : ‖∫ t in (0 : ℝ)..r, dγ t‖ ≤
      ∫ t in (0 : ℝ)..r, derivMajorant t := by
    apply intervalIntegral.norm_integral_le_of_norm_le hr
    · filter_upwards with t
      intro htr
      have hbound := radial_deriv_norm_le hG hinj hG0' htr.1.le
        (lt_of_le_of_lt htr.2 hr1) hζ
      simpa only [dγ, norm_mul, hζ, one_mul] using hbound
    · exact hmajcont'.intervalIntegrable
  rw [hγFTC, hprimFTC] at hnormInt
  simpa [γ, hG0, growthPrimitive] using hnormInt

/-- A coarse lower Koebe growth estimate. It follows directly from the Koebe-quarter theorem:
if the estimate failed, an intermediate disk would have an image containing `G z`, contradicting
injectivity. -/
theorem norm_div_four_le_norm
    (hG : AnalyticOnNhd ℂ G (ball 0 1)) (hinj : InjOn G (ball 0 1))
    (hG0 : G 0 = 0) (hG0' : deriv G 0 = 1)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ‖z‖ / 4 ≤ ‖G z‖ := by
  by_contra hnot
  have hlt : ‖G z‖ < ‖z‖ / 4 := lt_of_not_ge hnot
  let ρ : ℝ := (4 * ‖G z‖ + ‖z‖) / 2
  have hGρ : ‖G z‖ < ρ / 4 := by
    dsimp only [ρ]
    nlinarith
  have hρz : ρ < ‖z‖ := by
    dsimp only [ρ]
    nlinarith
  have hz1 : ‖z‖ < 1 := by simpa [Metric.mem_ball] using hz
  have hρ1 : ρ < 1 := hρz.trans hz1
  have hsub : ball (0 : ℂ) ρ ⊆ ball 0 1 := Metric.ball_subset_ball hρ1.le
  have hquarter := koebe_quarter' (c := (0 : ℂ)) (r := ρ)
    (hG.mono hsub) (hinj.mono hsub)
  have hmem : G z ∈ ball (G 0) (ρ * ‖deriv G 0‖ / 4) := by
    simpa only [hG0, hG0', norm_one, mul_one, Metric.mem_ball, dist_zero_right] using hGρ
  obtain ⟨w, hw, hwG⟩ := hquarter hmem
  have hw1 : w ∈ ball (0 : ℂ) 1 := hsub hw
  have hwz : w = z := hinj hw1 hz hwG
  have hwρ : ‖w‖ < ρ := by simpa [Metric.mem_ball] using hw
  rw [hwz] at hwρ
  exact (not_lt_of_ge hρz.le) hwρ

/-- The normalized univalent hypotheses imply the exact radial Koebe upper bound used in
`Prawitz.lean`. -/
theorem koebeUpperBound_of_normalized_univalent
    (hG : AnalyticOnNhd ℂ G (ball 0 1)) (hinj : InjOn G (ball 0 1))
    (hG0 : G 0 = 0) (hG0' : deriv G 0 = 1) :
    Prawitz.KoebeUpperBound G := by
  intro r hr hr1 θ
  let ζ : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  have hζ : ‖ζ‖ = 1 := by
    simp only [ζ, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero, Real.exp_zero]
  have hgrowth := radial_growth_le hG hinj hG0 hG0' hr.le hr1 hζ
  have hquot : Prawitz.radialQuotient G r θ ≤ 1 / (1 - r) ^ 2 := by
    rw [Prawitz.radialQuotient, Prawitz.circlePoint]
    change ‖G ((r : ℂ) * ζ)‖ / r ≤ _
    rw [div_le_iff₀ hr]
    simpa only [growthPrimitive, one_div, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm,
      one_mul]
      using hgrowth
  refine hquot.trans_eq ?_
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg (by linarith : 0 ≤ 1 - r)]
  norm_num [Real.rpow_two]

end KoebeDistortion
end Erdos515
