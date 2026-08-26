import ErdosProblems.Erdos1002.NearResonantPoleL2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Smoothness of the near-resonant pole profile

This file checks the point that is hidden by the totalized quotient in the
definition of `nearW`: the numerator vanishes on a whole neighbourhood of
the origin, so the quotient is genuinely smooth there.  Away from the
origin it is the ordinary quotient of smooth functions.

The quantitative Gevrey estimate is deliberately not asserted here; global
smoothness alone does not imply a bound uniform in a growing derivative
order.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace Erdos1002

noncomputable section

theorem scaledNearProfile_contDiff (s : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (scaledNearProfile s) := by
  unfold scaledNearProfile
  exact nearBaseProfile_contDiff.comp (contDiff_id.div_const s)

theorem nearRho_contDiff (a ε : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (nearRho a ε) := by
  unfold nearRho
  exact (scaledNearProfile_contDiff (ε / 2)).sub
    (scaledNearProfile_contDiff a)

private theorem nearW_eventuallyEq_zero_at_zero
    (a ε : ℝ) (ha : 0 < a) (haε : a ≤ ε / 4) :
    nearW a ε =ᶠ[𝓝 0] (fun _ : ℝ ↦ 0) := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) ha] with x hx
  have habs : |x| ≤ a := by
    have : |x| < a := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using! hx
    exact this.le
  unfold nearW
  rw [nearRho_eq_zero_of_abs_le a ε x ha haε habs, zero_div]

/-- The quotient cutoff is genuinely `C∞` on the whole real line.  At the
origin this uses its equality to zero on `(-a,a)`; away from the origin it
uses ordinary smooth division. -/
theorem nearW_contDiff
    (a ε : ℝ) (ha : 0 < a) (haε : a ≤ ε / 4) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (nearW a ε) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      (nearW_eventuallyEq_zero_at_zero a ε ha haε)
  · have hden :
        ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : ℝ ↦ (y : ℂ)) x :=
      (Complex.ofRealCLM.contDiff.comp contDiff_id).contDiffAt
    have hdenInv := hden.inv (by exact_mod_cast hx)
    have hprod := (nearRho_contDiff a ε).contDiffAt.mul hdenInv
    simpa only [nearW, div_eq_mul_inv] using! hprod

theorem nearW_iteratedDeriv_continuous
    (a ε : ℝ) (ha : 0 < a) (haε : a ≤ ε / 4) (j : ℕ) :
    Continuous (iteratedDeriv j (nearW a ε)) := by
  rw [iteratedDeriv_eq_iterate]
  exact (nearW_contDiff a ε ha haε).iterate_deriv j |>.continuous

/-- Exact affine scaling of every derivative on one reduced pole cell. -/
theorem iteratedDeriv_nearPoleCell
    (a ε : ℝ) (p q j : ℕ) (hp : 0 < p)
    (ha : 0 < a) (haε : a ≤ ε / 4) (alpha : ℝ) :
    iteratedDeriv j (nearPoleCell a ε p q) alpha =
      ((p : ℝ) ^ 2) ^ j •
        iteratedDeriv j (nearW a ε)
          ((p : ℝ) * ((p : ℝ) * alpha - (q : ℝ))) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hfun :
      nearPoleCell a ε p q =
        fun x : ℝ ↦ nearW a ε
          ((p : ℝ) ^ 2 * (x - (q : ℝ) / (p : ℝ))) := by
    funext x
    unfold nearPoleCell
    congr 1
    field_simp [hpR]
  rw [hfun]
  have hshift := congrFun
    (iteratedDeriv_comp_sub_const j
      (fun x : ℝ ↦ nearW a ε ((p : ℝ) ^ 2 * x))
      ((q : ℝ) / (p : ℝ))) alpha
  rw [hshift]
  have hsmooth : ContDiff ℝ j (nearW a ε) :=
    (nearW_contDiff a ε ha haε).of_le (by
      exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top))
  have hscale := congrFun
    (iteratedDeriv_comp_const_smul hsmooth ((p : ℝ) ^ 2))
    (alpha - (q : ℝ) / (p : ℝ))
  convert! hscale using 1
  field_simp [hpR]

theorem support_nearW_subset_Icc
    (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4) :
    Function.support (nearW a ε) ⊆ Icc (-ε) ε := by
  intro x hx
  constructor
  · by_contra hleft
    have hxlt : x < -ε := lt_of_not_ge hleft
    have hxneg : x < 0 := by linarith
    have habs : ε ≤ |x| := by
      rw [abs_of_neg hxneg]
      linarith
    exact hx (nearW_eq_zero_of_epsilon_le_abs a ε x ha hε haε habs)
  · by_contra hright
    have hxgt : ε < x := lt_of_not_ge hright
    have hxpos : 0 < x := hε.trans hxgt
    have habs : ε ≤ |x| := by
      rw [abs_of_pos hxpos]
      exact hxgt.le
    exact hx (nearW_eq_zero_of_epsilon_le_abs a ε x ha hε haε habs)

/-- Every classical derivative has support in the same closed cutoff
interval.  The closure in `support_deriv_subset` is harmless because the
interval is closed. -/
theorem support_iteratedDeriv_nearW_subset_Icc
    (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (j : ℕ) :
    Function.support (iteratedDeriv j (nearW a ε)) ⊆ Icc (-ε) ε := by
  rw [iteratedDeriv_eq_iterate]
  induction j with
  | zero =>
      simpa using! support_nearW_subset_Icc a ε ha hε haε
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact support_deriv_subset.trans (closure_minimal ih isClosed_Icc)

theorem integrable_norm_iteratedDeriv_nearW_sq
    (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (j : ℕ) :
    Integrable (fun x : ℝ ↦ ‖iteratedDeriv j (nearW a ε) x‖ ^ 2) := by
  have hcont : Continuous
      (fun x : ℝ ↦ ‖iteratedDeriv j (nearW a ε) x‖ ^ 2) :=
    (nearW_iteratedDeriv_continuous a ε ha haε j).norm.pow 2
  have hsupp : Function.support
      (fun x : ℝ ↦ ‖iteratedDeriv j (nearW a ε) x‖ ^ 2) ⊆ Icc (-ε) ε := by
    intro x hx
    apply support_iteratedDeriv_nearW_subset_Icc a ε ha hε haε j
    intro hzero
    apply hx
    change ‖iteratedDeriv j (nearW a ε) x‖ ^ 2 = 0
    rw [hzero, norm_zero, zero_pow (by omega : (2 : ℕ) ≠ 0)]
  exact hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp)

/-- Exact squared `L²` mass of the `j`-th pole-profile derivative. -/
def nearWDerivNormSqMass (a ε : ℝ) (j : ℕ) : ℝ :=
  ∫ x : ℝ, ‖iteratedDeriv j (nearW a ε) x‖ ^ 2

theorem nearWDerivNormSqMass_nonneg (a ε : ℝ) (j : ℕ) :
    0 ≤ nearWDerivNormSqMass a ε j := by
  unfold nearWDerivNormSqMass
  exact integral_nonneg fun _ ↦ sq_nonneg _

/-- Squared `L²` mass of the `j`-th derivative on one affine pole cell. -/
def nearPoleCellDerivNormSqIntegral
    (a ε : ℝ) (p q j : ℕ) : ℝ :=
  ∫ alpha in nearestCellLeft p q..nearestCellRight p q,
    ‖iteratedDeriv j (nearPoleCell a ε p q) alpha‖ ^ 2

/-- Exact `p^(4j-2)` scaling of one cell derivative.  The formula is kept
in a subtraction-free form so it also covers `j=0` literally. -/
theorem nearPoleCellDerivNormSqIntegral_eq
    (a ε : ℝ) (p q j : ℕ) (hp : 0 < p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) :
    nearPoleCellDerivNormSqIntegral a ε p q j =
      (1 / (p : ℝ) ^ 2) * (((p : ℝ) ^ 2) ^ j) ^ 2 *
        nearWDerivNormSqMass a ε j := by
  have hpRpos : 0 < (p : ℝ) := by exact_mod_cast hp
  have hpR : (p : ℝ) ≠ 0 := hpRpos.ne'
  let c : ℝ := (p : ℝ) ^ 2
  let d : ℝ := (p : ℝ) * (q : ℝ)
  let f : ℝ → ℝ := fun x ↦
    ‖(c ^ j) • iteratedDeriv j (nearW a ε) x‖ ^ 2
  have hpone : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hεp : ε < (p : ℝ) / 2 := by linarith
  have hsupport : Function.support f ⊆
      Ioc (-(p : ℝ) / 2) ((p : ℝ) / 2) := by
    intro x hx
    have hderiv : iteratedDeriv j (nearW a ε) x ≠ 0 := by
      intro hzero
      apply hx
      dsimp [f]
      simp [hzero]
    have hxcut :=
      support_iteratedDeriv_nearW_subset_Icc a ε ha hε haε j hderiv
    exact ⟨by linarith [hxcut.1], by linarith [hxcut.2]⟩
  have hpoint : f = fun x : ℝ ↦
      (c ^ j) ^ 2 * ‖iteratedDeriv j (nearW a ε) x‖ ^ 2 := by
    funext x
    dsimp [f]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (sq_nonneg (p : ℝ)) j)]
    ring
  have hfull :
      (∫ x in (-(p : ℝ) / 2)..((p : ℝ) / 2), f x) =
        (c ^ j) ^ 2 * nearWDerivNormSqMass a ε j := by
    calc
      (∫ x in (-(p : ℝ) / 2)..((p : ℝ) / 2), f x) =
          ∫ x : ℝ, f x :=
        intervalIntegral.integral_eq_integral_of_support_subset hsupport
      _ = ∫ x : ℝ,
          (c ^ j) ^ 2 * ‖iteratedDeriv j (nearW a ε) x‖ ^ 2 := by
        rw [hpoint]
      _ = (c ^ j) ^ 2 * nearWDerivNormSqMass a ε j := by
        rw [integral_const_mul]
        rfl
  have hintegrand :
      (fun alpha : ℝ ↦
        ‖iteratedDeriv j (nearPoleCell a ε p q) alpha‖ ^ 2) =
      (fun alpha : ℝ ↦ f (c * alpha - d)) := by
    funext alpha
    rw [iteratedDeriv_nearPoleCell a ε p q j hp ha haε alpha]
    dsimp [f, c, d]
    rw [show (p : ℝ) * ((p : ℝ) * alpha - (q : ℝ)) =
      (p : ℝ) ^ 2 * alpha - (p : ℝ) * (q : ℝ) by ring]
  unfold nearPoleCellDerivNormSqIntegral
  rw [hintegrand]
  rw [intervalIntegral.integral_comp_mul_sub f (pow_ne_zero 2 hpR)
    d, nearestCellLeft_sq_mul_sub p q hp,
    nearestCellRight_sq_mul_sub p q hp, hfull]
  simp only [smul_eq_mul]
  dsimp [c]
  field_simp [hpR]

end

end Erdos1002
