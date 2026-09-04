import ErdosProblems.Erdos515.Prawitz
import ErdosProblems.Erdos515.CircleCutoff
import ErdosProblems.Erdos515.PoissonKernelBounds
import ErdosProblems.Erdos515.PoissonMaximal
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Data.EReal.Basic

/-!
# The analytic radial-maximal estimate at exponent `1/4`

This file supplies the analytic bridge left open by `Prawitz.lean`.  The quotient of a normalized
univalent function by the coordinate is represented by `dslope`, so its removable singularity at
the origin is handled by Mathlib's removable-singularity theorem.  Since the quotient has no
zeros, it has a continuous fourth root on the disk.  The first lemma below records the elementary
fact that such a continuous root of a holomorphic function is holomorphic; this lets the ordinary
Poisson formula be applied to the fourth root.
-/

open Filter MeasureTheory Metric Set

open scoped ENNReal Real Topology

namespace Erdos515
namespace Prawitz
namespace RadialMaximal

/-- A continuous fourth root of a holomorphic nonvanishing function is holomorphic. -/
theorem differentiableOn_of_continuousOn_pow_four_eq
    {U : Set ℂ} {g q : ℂ → ℂ}
    (hU : IsOpen U) (hg : DifferentiableOn ℂ g U) (hq : ContinuousOn q U)
    (hq0 : ∀ z ∈ U, q z ≠ 0) (hpow : ∀ z ∈ U, q z ^ 4 = g z) :
    DifferentiableOn ℂ q U := by
  intro z hz
  have hzU : U ∈ nhds z := hU.mem_nhds hz
  have hgc : ContinuousAt g z := (hg.differentiableAt hzU).continuousAt
  have hqc : ContinuousAt q z := hq.continuousAt hzU
  let S : ℂ → ℂ := fun w ↦
    q w ^ 3 + q w ^ 2 * q z + q w * q z ^ 2 + q z ^ 3
  have hSc : Tendsto S (nhdsWithin z {z}ᶜ) (nhds (4 * q z ^ 3)) := by
    have hq' : Tendsto q (nhdsWithin z {z}ᶜ) (nhds (q z)) :=
      hqc.mono_left inf_le_left
    have hconst : Tendsto (fun _ : ℂ ↦ q z) (nhdsWithin z {z}ᶜ) (nhds (q z)) :=
      tendsto_const_nhds
    have ht := (((hq'.pow 3).add ((hq'.pow 2).mul hconst)).add
      (hq'.mul (hconst.pow 2))).add (hconst.pow 3)
    have heq : q z ^ 3 + q z ^ 2 * q z + q z * q z ^ 2 + q z ^ 3 =
        4 * q z ^ 3 := by ring
    simpa only [S, heq] using ht
  have hS0 : 4 * q z ^ 3 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ (hq0 z hz))
  have hslopeG : Tendsto (slope g z) (nhdsWithin z {z}ᶜ) (nhds (deriv g z)) :=
    (hg.differentiableAt hzU).hasDerivAt.tendsto_slope
  apply (show HasDerivWithinAt q (deriv g z / (4 * q z ^ 3)) U z from ?_).differentiableWithinAt
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hmemU : ∀ᶠ w in nhdsWithin z (U \ {z}), w ∈ U := by
    filter_upwards [eventually_mem_nhdsWithin] with w hw
    exact hw.1
  have hne : ∀ᶠ w in nhdsWithin z (U \ {z}), w ≠ z := by
    filter_upwards [eventually_mem_nhdsWithin] with w hw
    exact hw.2
  have hS_ne : ∀ᶠ w in nhdsWithin z (U \ {z}), S w ≠ 0 := by
    have hSne : ∀ᶠ w in nhdsWithin z {z}ᶜ, S w ≠ 0 :=
      hSc (isOpen_ne.mem_nhds hS0)
    exact hSne.filter_mono (nhdsWithin_mono z (diff_subset_compl U {z}))
  have hslopeEq : ∀ᶠ w in nhdsWithin z (U \ {z}),
      slope q z w = slope g z w / S w := by
    filter_upwards [hmemU, hne, hS_ne] with w hwU hwz hSw
    rw [slope_fun_def_field, slope_fun_def_field]
    have hfac : q w ^ 4 - q z ^ 4 = (q w - q z) * S w := by
      dsimp [S]
      ring
    change (q w - q z) / (w - z) = ((g w - g z) / (w - z)) / S w
    rw [← hpow w hwU, ← hpow z hz, hfac]
    field_simp [sub_ne_zero.mpr hwz, hSw]
  apply (tendsto_congr' hslopeEq).mpr
  have hmono : nhdsWithin z (U \ {z}) ≤ nhdsWithin z {z}ᶜ :=
    nhdsWithin_mono z (diff_subset_compl U {z})
  exact (hslopeG.mono_left hmono).div (hSc.mono_left hmono) hS0

/-- The holomorphic quotient `G(z)/z`, with its removable value at zero. -/
noncomputable def diskQuotient (G : ℂ → ℂ) : ℂ → ℂ :=
  dslope G 0

lemma diskQuotient_apply_of_ne {G : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0) :
    diskQuotient G z = G z / z - G 0 / z := by
  rw [diskQuotient, dslope_of_ne _ hz, slope_fun_def_field]
  simp only [sub_zero]
  ring

lemma diskQuotient_apply_of_eq_zero (G : ℂ → ℂ) :
    diskQuotient G 0 = deriv G 0 := by
  exact dslope_same G 0

theorem differentiableOn_diskQuotient {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G (ball 0 1)) :
    DifferentiableOn ℂ (diskQuotient G) (ball 0 1) := by
  exact (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (by simp))).2 hG

/-- A normalized injective map has a nonvanishing disk quotient. -/
theorem diskQuotient_ne_zero {G : ℂ → ℂ}
    (hG0 : G 0 = 0) (hGderiv : deriv G 0 ≠ 0)
    (hGinj : Set.InjOn G (ball 0 1)) :
    ∀ z ∈ ball (0 : ℂ) 1, diskQuotient G z ≠ 0 := by
  intro z hz
  rcases eq_or_ne z 0 with rfl | hz0
  · simpa [diskQuotient_apply_of_eq_zero] using hGderiv
  · rw [diskQuotient_apply_of_ne hz0, hG0, zero_div, sub_zero]
    exact div_ne_zero (fun hEq ↦ hz0 (hGinj hz (by simp) (by simpa [hG0] using hEq))) hz0

/-- The disk quotient of a normalized injective map has a holomorphic fourth root. -/
theorem exists_differentiableOn_fourthRoot {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G (ball 0 1))
    (hG0 : G 0 = 0) (hGderiv : deriv G 0 ≠ 0)
    (hGinj : Set.InjOn G (ball 0 1)) :
    ∃ q : ℂ → ℂ, DifferentiableOn ℂ q (ball 0 1) ∧
      ∀ z ∈ ball (0 : ℂ) 1, q z ^ 4 = diskQuotient G z := by
  have hnonzero := diskQuotient_ne_zero hG0 hGderiv hGinj
  have himage : 0 ∉ diskQuotient G '' ball (0 : ℂ) 1 := by
    rintro ⟨z, hz, hzeq⟩
    exact hnonzero z hz hzeq
  let : ContractibleSpace (ball (0 : ℂ) 1) := Metric.contractibleSpace_ball one_pos
  have hsimply : IsSimplyConnected (ball (0 : ℂ) 1) := by
    exact (inferInstance : SimplyConnectedSpace (ball (0 : ℂ) 1))
  obtain ⟨q, hqc, hqpow⟩ := Complex.exists_continuousOn_pow_eq
    hsimply isOpen_ball
    (differentiableOn_diskQuotient hG).continuousOn himage (by norm_num : (4 : ℕ) ≠ 0)
  have hq0 : ∀ z ∈ ball (0 : ℂ) 1, q z ≠ 0 := by
    intro z hz hqz
    exact hnonzero z hz (by rw [← hqpow z, hqz, zero_pow (by norm_num : (4 : ℕ) ≠ 0)])
  exact ⟨q, differentiableOn_of_continuousOn_pow_four_eq isOpen_ball
    (differentiableOn_diskQuotient hG) hqc hq0 (fun z _ ↦ hqpow z), fun z _ ↦ hqpow z⟩

lemma norm_circlePoint {r θ : ℝ} (hr : 0 ≤ r) :
    ‖circlePoint r θ‖ = r := by
  simp [circlePoint, Complex.norm_exp, hr]

/-- The norm of a fourth root of the disk quotient is exactly the quarter power occurring in
`HardyQuarterBound`. -/
theorem norm_fourthRoot_circlePoint {G q : ℂ → ℂ}
    (hG0 : G 0 = 0)
    (hqpow : ∀ z ∈ ball (0 : ℂ) 1, q z ^ 4 = diskQuotient G z)
    {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ‖q (circlePoint r θ)‖ = (radialQuotient G r θ) ^ quarter := by
  have hz0 : circlePoint r θ ≠ 0 := by
    rw [circlePoint]
    exact mul_ne_zero (by exact_mod_cast hr.ne') (Complex.exp_ne_zero _)
  have hzmem : circlePoint r θ ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_circlePoint hr.le]
    exact hr1
  have hp := congrArg norm (hqpow (circlePoint r θ) hzmem)
  have hquot : ‖diskQuotient G (circlePoint r θ)‖ = radialQuotient G r θ := by
    rw [diskQuotient_apply_of_ne hz0, hG0, zero_div, sub_zero, norm_div,
      norm_circlePoint hr.le]
    rfl
  have hpowNorm : ‖q (circlePoint r θ)‖ ^ 4 = radialQuotient G r θ := by
    simpa only [norm_pow, hquot] using hp
  calc
    ‖q (circlePoint r θ)‖ =
        (‖q (circlePoint r θ)‖ ^ 4) ^ ((4 : ℝ)⁻¹) := by
      symm
      exact Real.pow_rpow_inv_natCast (norm_nonneg _) (by norm_num : (4 : ℕ) ≠ 0)
    _ = (radialQuotient G r θ) ^ quarter := by
      rw [hpowNorm]
      congr 1
      norm_num [quarter]

/-- A `HardyQuarterBound` for `G` is an ordinary uniform `H¹` bound for the holomorphic fourth
root of `G(z)/z`. -/
theorem fourthRoot_integral_le_of_hardyQuarter {G q : ℂ → ℂ} {C : ℝ}
    (hG0 : G 0 = 0)
    (hqpow : ∀ z ∈ ball (0 : ℂ) 1, q z ^ 4 = diskQuotient G z)
    (hHardy : HardyQuarterBound G C) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (∫ θ in angularInterval, ‖q (circlePoint r θ)‖) ≤ C := by
  convert hHardy r hr hr1 using 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro θ _
  exact norm_fourthRoot_circlePoint hG0 hqpow hr hr1

lemma hardyQuarter_constant_nonneg {G : ℂ → ℂ} {C : ℝ}
    (hHardy : HardyQuarterBound G C) : 0 ≤ C := by
  have hnonneg : 0 ≤
      ∫ θ in angularInterval, (radialQuotient G (1 / 2 : ℝ) θ) ^ quarter :=
    integral_nonneg fun _ ↦ Real.rpow_nonneg (by
      exact div_nonneg (norm_nonneg _) (by norm_num)) _
  exact hnonneg.trans (hHardy (1 / 2) (by norm_num) (by norm_num))

/-- Boundary norms on every compactly contained circle are continuous. -/
theorem continuous_boundaryNorm_of_differentiableOn {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q (ball 0 1)) {R : ℝ}
    (hR : 0 ≤ R) (hR1 : R < 1) :
    Continuous (boundaryNorm q R) := by
  apply Continuous.norm
  apply hq.continuousOn.comp_continuous
  · unfold circlePoint
    fun_prop
  · intro θ
    rw [mem_ball_zero_iff]
    rw [show ‖circlePoint R θ‖ = |R| by simp [circlePoint, Complex.norm_exp]]
    rw [abs_of_nonneg hR]
    exact hR1

/-- Holomorphy on the unit disk gives the closed-disk regularity needed by the Poisson formula
at every smaller radius. -/
theorem diffContOnCl_ball_of_differentiableOn {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q (ball 0 1)) {R : ℝ} (hR1 : R < 1) :
    DiffContOnCl ℂ q (ball 0 R) := by
  exact hq.diffContOnCl_ball (closedBall_subset_ball hR1)

/-- The exact radial maximum, allowed to be `⊤` on exceptional directions.  The extended-real
codomain is essential: even a univalent Hardy-class function can diverge along a boundary ray. -/
noncomputable def radialMaxE (G : ℂ → ℂ) (θ : ℝ) : EReal :=
  ⨆ r : {r : ℝ // r ∈ Ioo (0 : ℝ) 1},
    (radialQuotient G r θ : EReal)

/-- A real compatibility projection.  At every finite direction this is the genuine radial
maximum.  The exact all-direction API is `radialMaxE`. -/
noncomputable def radialMax (G : ℂ → ℂ) (θ : ℝ) : ℝ :=
  (radialMaxE G θ).toReal

/-- Weak finite-threshold control for an exact extended-real radial maximum. -/
def WeakRadialMaxEBound (H : ℝ → EReal) (a A : ℝ) : Prop :=
  ∀ K : ℝ, 0 < K →
    volume (angularInterval ∩ {θ | ((K * a : ℝ) : EReal) < H θ}) ≤
      ENNReal.ofReal (A * K ^ (-quarter))

/-- Exact bad directions, stated without choosing any codomain for the radial supremum. -/
def radialQuotientBadDirections (G : ℂ → ℂ) (K : ℝ) : Set ℝ :=
  angularInterval ∩ {θ | ∃ r ∈ Ioo (0 : ℝ) 1, K < radialQuotient G r θ}

/-- The exact bad set for a physical radial quotient obtained by multiplying by a positive
conformal-radius scale. -/
def scaledRadialQuotientBadDirections (G : ℂ → ℂ) (a K : ℝ) : Set ℝ :=
  angularInterval ∩ {θ | ∃ r ∈ Ioo (0 : ℝ) 1,
    K * a < a * radialQuotient G r θ}

theorem radialQuotient_le_radialMaxE {G : ℂ → ℂ} {r θ : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    (radialQuotient G r θ : EReal) ≤ radialMaxE G θ := by
  exact le_iSup (fun s : {s : ℝ // s ∈ Ioo (0 : ℝ) 1} ↦
    (radialQuotient G s θ : EReal)) ⟨r, hr⟩

theorem radialMaxE_nonneg (G : ℂ → ℂ) (θ : ℝ) :
    (0 : EReal) ≤ radialMaxE G θ := by
  have hq : (0 : EReal) ≤
      (radialQuotient G (1 / 2 : ℝ) θ : EReal) := by
    exact EReal.coe_nonneg.mpr (div_nonneg (norm_nonneg _) (by norm_num))
  exact hq.trans (radialQuotient_le_radialMaxE (by norm_num))

theorem radialMax_nonneg (G : ℂ → ℂ) (θ : ℝ) :
    0 ≤ radialMax G θ := by
  exact EReal.toReal_nonneg (radialMaxE_nonneg G θ)

theorem radialQuotient_le_radialMax_of_ne_top {G : ℂ → ℂ} {r θ : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) (hfinite : radialMaxE G θ ≠ ⊤) :
    radialQuotient G r θ ≤ radialMax G θ := by
  apply EReal.coe_le_coe_iff.mp
  rw [radialMax, EReal.coe_toReal hfinite]
  · exact radialQuotient_le_radialMaxE hr
  · exact ne_of_gt ((by simp : (⊥ : EReal) < 0).trans_le (radialMaxE_nonneg G θ))

theorem exists_radialQuotient_gt_of_lt_radialMaxE {G : ℂ → ℂ} {K θ : ℝ}
    (hK : (K : EReal) < radialMaxE G θ) :
    ∃ r ∈ Ioo (0 : ℝ) 1, K < radialQuotient G r θ := by
  rw [radialMaxE, lt_iSup_iff] at hK
  rcases hK with ⟨r, hr⟩
  exact ⟨r, r.property, EReal.coe_lt_coe_iff.mp hr⟩

theorem exists_radialQuotient_gt_of_lt_radialMax {G : ℂ → ℂ} {K θ : ℝ}
    (hK0 : 0 < K) (hK : K < radialMax G θ) :
    ∃ r ∈ Ioo (0 : ℝ) 1, K < radialQuotient G r θ := by
  have hfinite : radialMaxE G θ ≠ ⊤ := by
    intro htop
    have : radialMax G θ = 0 := by simp [radialMax, htop]
    linarith
  apply exists_radialQuotient_gt_of_lt_radialMaxE
  rw [← EReal.coe_toReal hfinite]
  · exact EReal.coe_lt_coe_iff.mpr hK
  · exact ne_of_gt ((by simp : (⊥ : EReal) < 0).trans_le (radialMaxE_nonneg G θ))

theorem radialMaxE_superlevel_eq_radialQuotientBadDirections
    (G : ℂ → ℂ) (K : ℝ) :
    angularInterval ∩ {θ | (K : EReal) < radialMaxE G θ} =
      radialQuotientBadDirections G K := by
  ext θ
  simp only [radialQuotientBadDirections, mem_inter_iff, mem_setOf_eq,
    and_congr_right_iff]
  intro _
  constructor
  · exact exists_radialQuotient_gt_of_lt_radialMaxE
  · rintro ⟨r, hr, hKr⟩
    exact (EReal.coe_lt_coe_iff.mpr hKr).trans_le (radialQuotient_le_radialMaxE hr)

theorem scaledRadialQuotientBadDirections_eq
    (G : ℂ → ℂ) {a K : ℝ} (ha : 0 < a) :
    scaledRadialQuotientBadDirections G a K = radialQuotientBadDirections G K := by
  ext θ
  simp only [scaledRadialQuotientBadDirections, radialQuotientBadDirections,
    mem_inter_iff, mem_setOf_eq, and_congr_right_iff]
  intro _
  apply exists_congr
  intro r
  apply and_congr_right
  intro _
  simpa [mul_comm] using
    (mul_lt_mul_iff_of_pos_left ha : a * K < a * radialQuotient G r θ ↔
      K < radialQuotient G r θ)

/-- Avoiding the exact bad set controls every radius, including on maps with unbounded image. -/
theorem radialQuotient_le_of_not_mem_bad {G : ℂ → ℂ} {K θ r : ℝ}
    (hθ : θ ∈ angularInterval) (hbad : θ ∉ radialQuotientBadDirections G K)
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    radialQuotient G r θ ≤ K := by
  by_contra hnot
  exact hbad ⟨hθ, r, hr, lt_of_not_ge hnot⟩

/-- Scaled version of `radialQuotient_le_of_not_mem_bad`. -/
theorem scaledRadialQuotient_le_of_not_mem_bad {G : ℂ → ℂ} {a K θ r : ℝ}
    (hθ : θ ∈ angularInterval)
    (hbad : θ ∉ scaledRadialQuotientBadDirections G a K)
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    a * radialQuotient G r θ ≤ K * a := by
  by_contra hnot
  exact hbad ⟨hθ, r, hr, lt_of_not_ge hnot⟩

/-! ## Exhausting the disk by fixed radii -/

/-- A monotone sequence of positive radii increasing to one. -/
noncomputable def exhaustionRadius (n : ℕ) : ℝ :=
  1 - 1 / (n + 2 : ℝ)

lemma exhaustionRadius_pos (n : ℕ) : 0 < exhaustionRadius n := by
  rw [exhaustionRadius, sub_pos]
  rw [div_lt_one (by positivity : (0 : ℝ) < n + 2)]
  have hn : (0 : ℝ) ≤ n := by positivity
  linarith

lemma exhaustionRadius_lt_one (n : ℕ) : exhaustionRadius n < 1 := by
  rw [exhaustionRadius, sub_lt_self_iff]
  positivity

lemma exhaustionRadius_mono : Monotone exhaustionRadius := by
  intro n m hnm
  rw [exhaustionRadius, exhaustionRadius]
  gcongr

lemma exists_lt_exhaustionRadius {r : ℝ} (hr : r < 1) :
    ∃ n : ℕ, r < exhaustionRadius n := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hr)
  refine ⟨n, ?_⟩
  rw [exhaustionRadius]
  have hden : (1 / (n + 2 : ℝ)) ≤ 1 / (n + 1 : ℝ) := by
    gcongr <;> norm_num
  linarith

/-- Directions on which the fourth root exceeds `T` before radius `R`. -/
def truncatedRootBad (q : ℂ → ℂ) (T R : ℝ) : Set ℝ :=
  angularInterval ∩ {θ | ∃ r ∈ Ioo (0 : ℝ) R, T < ‖q (circlePoint r θ)‖}

/-- Directions on which the fourth root exceeds `T` somewhere in the unit disk. -/
def rootBad (q : ℂ → ℂ) (T : ℝ) : Set ℝ :=
  angularInterval ∩ {θ | ∃ r ∈ Ioo (0 : ℝ) 1, T < ‖q (circlePoint r θ)‖}

lemma truncatedRootBad_mono (q : ℂ → ℂ) (T : ℝ) :
    Monotone (fun n ↦ truncatedRootBad q T (exhaustionRadius n)) := by
  intro n m hnm θ hθ
  refine ⟨hθ.1, ?_⟩
  rcases hθ.2 with ⟨r, hr, hqr⟩
  exact ⟨r, ⟨hr.1, hr.2.trans_le (exhaustionRadius_mono hnm)⟩, hqr⟩

lemma rootBad_eq_iUnion (q : ℂ → ℂ) (T : ℝ) :
    rootBad q T = ⋃ n : ℕ, truncatedRootBad q T (exhaustionRadius n) := by
  ext θ
  constructor
  · rintro ⟨hθ, r, hr, hqr⟩
    obtain ⟨n, hn⟩ := exists_lt_exhaustionRadius hr.2
    exact mem_iUnion.mpr ⟨n, hθ, r, ⟨hr.1, hn⟩, hqr⟩
  · rw [mem_iUnion]
    rintro ⟨n, hθ, r, hr, hqr⟩
    exact ⟨hθ, r, ⟨hr.1, hr.2.trans (exhaustionRadius_lt_one n)⟩, hqr⟩

/-- A uniform estimate on all fixed-radius bad sets passes to the full radial bad set. -/
theorem measure_rootBad_le_of_truncated {q : ℂ → ℂ} {T : ℝ} {A : ℝ≥0∞}
    (h : ∀ n : ℕ, volume (truncatedRootBad q T (exhaustionRadius n)) ≤ A) :
    volume (rootBad q T) ≤ A := by
  rw [rootBad_eq_iUnion, (truncatedRootBad_mono q T).measure_iUnion]
  exact iSup_le h

/-- Taking fourth powers converts the radial quotient bad set into the fourth-root bad set. -/
theorem radialMax_bad_subset_rootBad {G q : ℂ → ℂ} {K : ℝ}
    (hG0 : G 0 = 0)
    (hqpow : ∀ z ∈ ball (0 : ℂ) 1, q z ^ 4 = diskQuotient G z)
    (hK : 0 < K) :
    angularInterval ∩ {θ | K < radialMax G θ} ⊆ rootBad q (K ^ quarter) := by
  rintro θ ⟨hθ, hmax⟩
  obtain ⟨r, hr, hquot⟩ :=
    exists_radialQuotient_gt_of_lt_radialMax hK hmax
  refine ⟨hθ, r, hr, ?_⟩
  rw [norm_fourthRoot_circlePoint hG0 hqpow hr.1 hr.2]
  exact Real.rpow_lt_rpow (le_of_lt hK) hquot quarter_pos

/-- Exact extended-real radial bad directions are carried into fourth-root bad directions. -/
theorem radialMaxE_bad_subset_rootBad {G q : ℂ → ℂ} {K : ℝ}
    (hG0 : G 0 = 0)
    (hqpow : ∀ z ∈ ball (0 : ℂ) 1, q z ^ 4 = diskQuotient G z)
    (hK : 0 < K) :
    angularInterval ∩ {θ | (K : EReal) < radialMaxE G θ} ⊆
      rootBad q (K ^ quarter) := by
  rintro θ ⟨hθ, hmax⟩
  obtain ⟨r, hr, hquot⟩ := exists_radialQuotient_gt_of_lt_radialMaxE hmax
  refine ⟨hθ, r, hr, ?_⟩
  rw [norm_fourthRoot_circlePoint hG0 hqpow hr.1 hr.2]
  exact Real.rpow_lt_rpow hK.le hquot quarter_pos

open HardyLittlewood in
/-- Weak `(1,1)` for any bad set pointwise dominated by the maximal function. -/
theorem weak_measure_of_maximal_bad
    {u : ℝ → ℝ≥0∞} {E : Set ℝ} {T C : ℝ}
    (hT : 0 < T) (hC : 0 ≤ C)
    (hu : ∫⁻ x, u x ∂volume ≤ 3 * ENNReal.ofReal C)
    (hbad : ∀ θ ∈ E,
      ENNReal.ofReal T < 4096 * globalMaximalFunction u θ) :
    volume E ≤ ENNReal.ofReal (49152 * C * T⁻¹) := by
  let t : ℝ≥0∞ := ENNReal.ofReal T / 4096
  have ht0 : t ≠ 0 := by
    dsimp [t]
    exact ENNReal.div_ne_zero.mpr ⟨(ENNReal.ofReal_pos.2 hT).ne', by norm_num⟩
  have httop : t ≠ ∞ := by
    dsimp [t]
    exact ENNReal.div_ne_top (by simp) (by norm_num)
  have hsubset : E ⊆ {θ | t < globalMaximalFunction u θ} := by
    intro θ hθ
    change t < globalMaximalFunction u θ
    apply (ENNReal.div_lt_iff (a := globalMaximalFunction u θ)
      (b := (4096 : ℝ≥0∞)) (c := ENNReal.ofReal T)
      (Or.inl (by norm_num)) (Or.inl (by norm_num))).2
    simpa [mul_comm] using hbad θ hθ
  have hweak : t * volume {θ | t < globalMaximalFunction u θ} ≤
      4 * ∫⁻ x, u x ∂volume := weak_type_globalMaximalFunction u t
  calc
    volume E ≤ volume {θ | t < globalMaximalFunction u θ} := measure_mono hsubset
    _ ≤ t⁻¹ * (4 * ∫⁻ x, u x ∂volume) := by
      exact (ENNReal.mul_le_iff_le_inv ht0 httop).1 hweak
    _ ≤ t⁻¹ * (4 * (3 * ENNReal.ofReal C)) := by gcongr
    _ = ENNReal.ofReal (49152 * C * T⁻¹) := by
      rw [show t⁻¹ = 4096 * (ENNReal.ofReal T)⁻¹ by
        change (ENNReal.ofReal T / 4096)⁻¹ = _
        rw [ENNReal.inv_div (by norm_num) (by simp), ENNReal.div_eq_inv_mul]
        ac_rfl]
      rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) hC),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 49152),
        ENNReal.ofReal_inv_of_pos hT]
      norm_num
      ring

open HardyLittlewood in
/-- Fixed-radius weak estimate for the fourth root. -/
theorem measure_truncatedRootBad_le_of_hardyQuarter
    {G q : ℂ → ℂ} {C T R : ℝ}
    (hq : DifferentiableOn ℂ q (ball 0 1))
    (hG0 : G 0 = 0)
    (hqpow : ∀ z ∈ ball (0 : ℂ) 1, q z ^ 4 = diskQuotient G z)
    (hHardy : HardyQuarterBound G C)
    (hT : 0 < T) (hR0 : 0 < R) (hR1 : R < 1) :
    volume (truncatedRootBad q T R) ≤
      ENNReal.ofReal (49152 * C * T⁻¹) := by
  have hboundary : Continuous (boundaryNorm q R) :=
    continuous_boundaryNorm_of_differentiableOn hq hR0.le hR1
  have hmass : (∫⁻ x, threePeriodCutoff q R x ∂volume) ≤
      3 * ENNReal.ofReal C := by
    apply lintegral_threePeriodCutoff_le hboundary
    simpa only [boundaryNorm] using
      fourthRoot_integral_le_of_hardyQuarter hG0 hqpow hHardy hR0 hR1
  apply weak_measure_of_maximal_bad hT (hardyQuarter_constant_nonneg hHardy) hmass
  intro θ hθ
  rcases hθ with ⟨hθang, r, hr, hbad⟩
  have hlt : ENNReal.ofReal T < ENNReal.ofReal ‖q (circlePoint r θ)‖ :=
    (ENNReal.ofReal_lt_ofReal_iff (hT.trans hbad)).2 hbad
  exact hlt.trans_le
    (circlePoint_enorm_le_globalMaximalFunction hq hR0 hR1 hr.1.le hr.2 hθang)

/-- The fixed-radius estimates pass to all radii by monotone exhaustion. -/
theorem measure_rootBad_le_of_hardyQuarter
    {G q : ℂ → ℂ} {C T : ℝ}
    (hq : DifferentiableOn ℂ q (ball 0 1))
    (hG0 : G 0 = 0)
    (hqpow : ∀ z ∈ ball (0 : ℂ) 1, q z ^ 4 = diskQuotient G z)
    (hHardy : HardyQuarterBound G C) (hT : 0 < T) :
    volume (rootBad q T) ≤ ENNReal.ofReal (49152 * C * T⁻¹) := by
  apply measure_rootBad_le_of_truncated
  intro n
  exact measure_truncatedRootBad_le_of_hardyQuarter hq hG0 hqpow hHardy hT
    (exhaustionRadius_pos n) (exhaustionRadius_lt_one n)

/-- The final quarter-power conversion, separated from the fixed-radius maximal theorem. -/
theorem weakRadialMax_of_rootBad {G q : ℂ → ℂ} {A : ℝ}
    (hG0 : G 0 = 0)
    (hqpow : ∀ z ∈ ball (0 : ℂ) 1, q z ^ 4 = diskQuotient G z)
    (hroot : ∀ T : ℝ, 0 < T →
      volume (rootBad q T) ≤ ENNReal.ofReal (A * T⁻¹)) :
    WeakRadialMaxBound (radialMax G) 1 A := by
  intro K hK
  simp only [mul_one]
  calc
    volume (angularInterval ∩ {θ | K < radialMax G θ}) ≤
        volume (rootBad q (K ^ quarter)) :=
      measure_mono (radialMax_bad_subset_rootBad hG0 hqpow hK)
    _ ≤ ENNReal.ofReal (A * (K ^ quarter)⁻¹) :=
      hroot _ (Real.rpow_pos_of_pos hK quarter)
    _ = ENNReal.ofReal (A * K ^ (-quarter)) := by
      congr 2
      rw [Real.rpow_neg hK.le]

/-- Exact extended-real quarter-power conversion.  Unlike the real compatibility projection,
this theorem includes directions on which the radial supremum is infinite. -/
theorem weakRadialMaxE_of_rootBad {G q : ℂ → ℂ} {A : ℝ}
    (hG0 : G 0 = 0)
    (hqpow : ∀ z ∈ ball (0 : ℂ) 1, q z ^ 4 = diskQuotient G z)
    (hroot : ∀ T : ℝ, 0 < T →
      volume (rootBad q T) ≤ ENNReal.ofReal (A * T⁻¹)) :
    WeakRadialMaxEBound (radialMaxE G) 1 A := by
  intro K hK
  simp only [mul_one]
  calc
    volume (angularInterval ∩ {θ | (K : EReal) < radialMaxE G θ}) ≤
        volume (rootBad q (K ^ quarter)) :=
      measure_mono (radialMaxE_bad_subset_rootBad hG0 hqpow hK)
    _ ≤ ENNReal.ofReal (A * (K ^ quarter)⁻¹) :=
      hroot _ (Real.rpow_pos_of_pos hK quarter)
    _ = ENNReal.ofReal (A * K ^ (-quarter)) := by
      congr 2
      rw [Real.rpow_neg hK.le]

/-- The complete Hardy--Littlewood radial-maximal consequence of the Hardy quarter bound. -/
theorem weakRadialMax_of_hardyQuarter_complete
    {G : ℂ → ℂ} {C : ℝ}
    (hG : DifferentiableOn ℂ G (ball 0 1))
    (hG0 : G 0 = 0) (hGderiv : deriv G 0 ≠ 0)
    (hGinj : Set.InjOn G (ball 0 1))
    (hHardy : HardyQuarterBound G C) :
    WeakRadialMaxBound (radialMax G) 1 (49152 * C) := by
  obtain ⟨q, hq, hqpow⟩ :=
    exists_differentiableOn_fourthRoot hG hG0 hGderiv hGinj
  apply weakRadialMax_of_rootBad hG0 hqpow
  intro T hT
  simpa only [mul_assoc] using
    measure_rootBad_le_of_hardyQuarter hq hG0 hqpow hHardy hT

/-- Exact extended-real Hardy--Littlewood radial-maximal theorem, with no bounded-image
assumption and with infinite exceptional rays retained. -/
theorem weakRadialMaxE_of_hardyQuarter_complete
    {G : ℂ → ℂ} {C : ℝ}
    (hG : DifferentiableOn ℂ G (ball 0 1))
    (hG0 : G 0 = 0) (hGderiv : deriv G 0 ≠ 0)
    (hGinj : Set.InjOn G (ball 0 1))
    (hHardy : HardyQuarterBound G C) :
    WeakRadialMaxEBound (radialMaxE G) 1 (49152 * C) := by
  obtain ⟨q, hq, hqpow⟩ :=
    exists_differentiableOn_fourthRoot hG hG0 hGderiv hGinj
  apply weakRadialMaxE_of_rootBad hG0 hqpow
  intro T hT
  simpa only [mul_assoc] using
    measure_rootBad_le_of_hardyQuarter hq hG0 hqpow hHardy hT

/-- Direct bad-set form of the radial maximal theorem.  This is often the most convenient exact
interface for path selection, since it includes infinite rays without any `toReal` projection. -/
theorem measure_radialQuotientBadDirections_le
    {G : ℂ → ℂ} {C K : ℝ}
    (hG : DifferentiableOn ℂ G (ball 0 1))
    (hG0 : G 0 = 0) (hGderiv : deriv G 0 ≠ 0)
    (hGinj : Set.InjOn G (ball 0 1))
    (hHardy : HardyQuarterBound G C) (hK : 0 < K) :
    volume (radialQuotientBadDirections G K) ≤
      ENNReal.ofReal ((49152 * C) * K ^ (-quarter)) := by
  rw [← radialMaxE_superlevel_eq_radialQuotientBadDirections]
  simpa only [mul_one] using
    weakRadialMaxE_of_hardyQuarter_complete hG hG0 hGderiv hGinj hHardy K hK

/-- Scaled direct bad-set form, matching an unnormalized Riemann map exactly. -/
theorem measure_scaledRadialQuotientBadDirections_le
    {G : ℂ → ℂ} {C K a : ℝ}
    (hG : DifferentiableOn ℂ G (ball 0 1))
    (hG0 : G 0 = 0) (hGderiv : deriv G 0 ≠ 0)
    (hGinj : Set.InjOn G (ball 0 1))
    (hHardy : HardyQuarterBound G C) (hK : 0 < K) (ha : 0 < a) :
    volume (scaledRadialQuotientBadDirections G a K) ≤
      ENNReal.ofReal ((49152 * C) * K ^ (-quarter)) := by
  rw [scaledRadialQuotientBadDirections_eq G ha]
  exact measure_radialQuotientBadDirections_le hG hG0 hGderiv hGinj hHardy hK

/-- Rescaling the radial maximum and its conformal-radius parameter by the same positive factor
does not change the exceptional directions. -/
theorem WeakRadialMaxBound.const_mul {H : ℝ → ℝ} {A a : ℝ}
    (hH : WeakRadialMaxBound H 1 A) (ha : 0 < a) :
    WeakRadialMaxBound (fun θ ↦ a * H θ) a A := by
  intro K hK
  have hsets : angularInterval ∩ {θ | K * a < a * H θ} =
      angularInterval ∩ {θ | K < H θ} := by
    ext θ
    simp only [mem_inter_iff, mem_setOf_eq, and_congr_right_iff]
    intro _
    simpa [mul_comm] using
      (mul_lt_mul_iff_of_pos_left ha : a * K < a * H θ ↔ K < H θ)
  rw [hsets]
  simpa only [mul_one] using hH K hK

/-- Scaled form of the complete radial-maximal theorem, matching the conformal-radius parameter
of a non-unit-normalized Riemann map. -/
theorem weakRadialMax_of_hardyQuarter_scaled
    {G : ℂ → ℂ} {C a : ℝ}
    (hG : DifferentiableOn ℂ G (ball 0 1))
    (hG0 : G 0 = 0) (hGderiv : deriv G 0 ≠ 0)
    (hGinj : Set.InjOn G (ball 0 1))
    (hHardy : HardyQuarterBound G C) (ha : 0 < a) :
    WeakRadialMaxBound (fun θ ↦ a * radialMax G θ) a (49152 * C) :=
  WeakRadialMaxBound.const_mul
    (weakRadialMax_of_hardyQuarter_complete hG hG0 hGderiv hGinj
      hHardy) ha

end RadialMaximal
end Prawitz
end Erdos515
