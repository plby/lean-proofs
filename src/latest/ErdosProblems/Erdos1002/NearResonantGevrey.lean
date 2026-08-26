import ErdosProblems.Erdos1002.NearResonantPoleDerivatives

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Quantitative Gevrey bounds for the near-resonant cutoff

The near-resonant profile is the explicit order-two Gevrey cutoff from
`GevreyCutoff`, rather than an abstract smooth bump.  This file transfers
the real derivative estimate to the complex profile, proves the exact
dilation formula, and obtains a bound for every derivative of the two-scale
cutoff with all dependence on the derivative order displayed.
-/

open Filter MeasureTheory Set
open scoped BigOperators
open scoped Topology

namespace Erdos1002

noncomputable section

/-- Fixed constant dominating the zero-order profile and every positive
order Gevrey estimate. -/
def nearGevreyProfileConstant : ℝ :=
  max 1 (2 * gevreyCompactBumpMass⁻¹)

theorem nearGevreyProfileConstant_one_le :
    1 ≤ nearGevreyProfileConstant :=
  le_max_left _ _

theorem nearGevreyProfileConstant_nonneg :
    0 ≤ nearGevreyProfileConstant :=
  zero_le_one.trans nearGevreyProfileConstant_one_le

theorem two_mul_gevreyMass_inv_le_nearGevreyProfileConstant :
    2 * gevreyCompactBumpMass⁻¹ ≤ nearGevreyProfileConstant :=
  le_max_right _ _

private theorem iteratedDeriv_complex_ofReal_eq
    (f : ℝ → ℝ) (j : ℕ) (x : ℝ) (hf : ContDiffAt ℝ j f x) :
    iteratedDeriv j (fun y : ℝ ↦ (f y : ℂ)) x =
      (iteratedDeriv (F := ℝ) j f x : ℂ) := by
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv]
  have h := Complex.ofRealCLM.iteratedFDeriv_comp_left hf (i := j) le_rfl
  change iteratedFDeriv ℝ j (Complex.ofRealCLM ∘ f) x = _ at h
  have hfun : (fun y : ℝ ↦ (f y : ℂ)) = Complex.ofRealCLM ∘ f := rfl
  rw [hfun, h]
  rfl

theorem iteratedDeriv_nearBaseProfile_eq
    (j : ℕ) (x : ℝ) :
    iteratedDeriv j nearBaseProfile x =
      (iteratedDeriv (F := ℝ) j (gevreyOuterCutoff 2) x : ℂ) := by
  have h := iteratedDeriv_complex_ofReal_eq (gevreyOuterCutoff 2) j x
    ((gevreyOuterCutoff_contDiff (m := (⊤ : ℕ∞)) 2).of_le (by
      exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top)) |>.contDiffAt)
  simpa only [nearBaseProfile] using! h

/-- Uniform Gevrey-order-two estimate for the fixed complex profile. -/
theorem norm_iteratedDeriv_nearBaseProfile_le
    (j : ℕ) (x : ℝ) :
    ‖iteratedDeriv j nearBaseProfile x‖ ≤
      nearGevreyProfileConstant * 96 ^ j *
        (j.factorial : ℝ) ^ 2 := by
  rw [iteratedDeriv_nearBaseProfile_eq,
    Complex.norm_real, Real.norm_eq_abs]
  cases j with
  | zero =>
      have hcut := gevreyOuterCutoff_mem_Icc
        (by norm_num : (0 : ℝ) < 2) x
      simp only [iteratedDeriv_zero, pow_zero, Nat.factorial_zero,
        Nat.cast_one, one_pow, mul_one]
      rw [abs_of_nonneg hcut.1]
      exact hcut.2.trans nearGevreyProfileConstant_one_le
  | succ n =>
      have hraw := abs_iteratedDeriv_gevreyOuterCutoff_succ_le n 2 x
      have hsimplified :
          |iteratedDeriv (n + 1) (gevreyOuterCutoff 2) x| ≤
            (2 * gevreyCompactBumpMass⁻¹) *
              (96 ^ n * (n.factorial : ℝ) ^ 2) := by
        norm_num at hraw
        simpa only [mul_assoc] using! hraw
      calc
        |iteratedDeriv (n + 1) (gevreyOuterCutoff 2) x| ≤
            (2 * gevreyCompactBumpMass⁻¹) *
              (96 ^ n * (n.factorial : ℝ) ^ 2) := hsimplified
        _ ≤ nearGevreyProfileConstant *
              96 ^ (n + 1) * ((n + 1).factorial : ℝ) ^ 2 := by
          have hconst :=
            two_mul_gevreyMass_inv_le_nearGevreyProfileConstant
          have horder :
              (96 : ℝ) ^ n * (n.factorial : ℝ) ^ 2 ≤
                96 ^ (n + 1) * ((n + 1).factorial : ℝ) ^ 2 := by
            have hp : (96 : ℝ) ^ n ≤ 96 ^ (n + 1) :=
              pow_le_pow_right₀ (by norm_num) n.le_succ
            have hfacNat : n.factorial ≤ (n + 1).factorial :=
              Nat.factorial_le (by omega)
            have hfac : (n.factorial : ℝ) ^ 2 ≤
                ((n + 1).factorial : ℝ) ^ 2 := by
              exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hfacNat) 2
            exact mul_le_mul hp hfac (by positivity) (by positivity)
          have hfirst := mul_le_mul_of_nonneg_right hconst (by positivity :
            0 ≤ (96 : ℝ) ^ n * (n.factorial : ℝ) ^ 2)
          have hsecond := mul_le_mul_of_nonneg_left horder
            nearGevreyProfileConstant_nonneg
          exact hfirst.trans (by
            simpa only [mul_assoc] using! hsecond)

/-- Exact derivative scaling for a dilated near profile. -/
theorem iteratedDeriv_scaledNearProfile
    (j : ℕ) (s x : ℝ) :
    iteratedDeriv j (scaledNearProfile s) x =
      (s⁻¹ ^ j) • iteratedDeriv j nearBaseProfile (x / s) := by
  have hfun : scaledNearProfile s =
      fun y : ℝ ↦ nearBaseProfile (s⁻¹ * y) := by
    funext y
    unfold scaledNearProfile
    congr 1
    rw [div_eq_mul_inv, mul_comm]
  rw [hfun]
  have h := congrFun
    (iteratedDeriv_comp_const_smul
      (nearBaseProfile_contDiff.of_le (by
        exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top))) s⁻¹) x
  simpa only [div_eq_mul_inv, mul_comm] using! h

/-- Quantitative derivative bound after a positive dilation. -/
theorem norm_iteratedDeriv_scaledNearProfile_le
    (j : ℕ) (s x : ℝ) (hs : 0 < s) :
    ‖iteratedDeriv j (scaledNearProfile s) x‖ ≤
      nearGevreyProfileConstant * 96 ^ j *
        (j.factorial : ℝ) ^ 2 * s⁻¹ ^ j := by
  rw [iteratedDeriv_scaledNearProfile, norm_smul, Real.norm_eq_abs,
    abs_pow, abs_of_pos (inv_pos.mpr hs)]
  have hmul := mul_le_mul_of_nonneg_left
    (norm_iteratedDeriv_nearBaseProfile_le j (x / s))
    (pow_nonneg (inv_pos.mpr hs).le j)
  simpa only [mul_assoc, mul_comm, mul_left_comm] using! hmul

/-- Exact derivative formula for the two-scale cutoff. -/
theorem iteratedDeriv_nearRho
    (j : ℕ) (a ε x : ℝ) :
    iteratedDeriv j (nearRho a ε) x =
      iteratedDeriv j (scaledNearProfile (ε / 2)) x -
        iteratedDeriv j (scaledNearProfile a) x := by
  unfold nearRho
  have houter : ContDiffAt ℝ j (scaledNearProfile (ε / 2)) x := by
    unfold scaledNearProfile
    exact (nearBaseProfile_contDiff.comp
      (contDiff_id.div_const (ε / 2))).of_le (by
        exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top)) |>.contDiffAt
  have hinner : ContDiffAt ℝ j (scaledNearProfile a) x := by
    unfold scaledNearProfile
    exact (nearBaseProfile_contDiff.comp
      (contDiff_id.div_const a)).of_le (by
        exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top)) |>.contDiffAt
  exact iteratedDeriv_fun_sub
    houter hinner

/-- Uniform derivative bound for `rho`; the shrinking inner scale is the
only scale retained in the right-hand side. -/
theorem norm_iteratedDeriv_nearRho_le
    (j : ℕ) (a ε x : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (haε : a ≤ ε / 4) :
    ‖iteratedDeriv j (nearRho a ε) x‖ ≤
      2 * nearGevreyProfileConstant * 96 ^ j *
        (j.factorial : ℝ) ^ 2 * a⁻¹ ^ j := by
  rw [iteratedDeriv_nearRho j a ε x]
  have hout := norm_iteratedDeriv_scaledNearProfile_le
    j (ε / 2) x (by positivity)
  have hin := norm_iteratedDeriv_scaledNearProfile_le j a x ha
  have hscale : (ε / 2)⁻¹ ^ j ≤ a⁻¹ ^ j := by
    have haHalf : a ≤ ε / 2 := by linarith
    exact pow_le_pow_left₀ (by positivity)
      ((inv_le_inv₀ (by positivity : 0 < ε / 2) ha).2 haHalf) j
  calc
    ‖iteratedDeriv j (scaledNearProfile (ε / 2)) x -
        iteratedDeriv j (scaledNearProfile a) x‖ ≤
      ‖iteratedDeriv j (scaledNearProfile (ε / 2)) x‖ +
        ‖iteratedDeriv j (scaledNearProfile a) x‖ := norm_sub_le _ _
    _ ≤ nearGevreyProfileConstant * 96 ^ j *
          (j.factorial : ℝ) ^ 2 * (ε / 2)⁻¹ ^ j +
        nearGevreyProfileConstant * 96 ^ j *
          (j.factorial : ℝ) ^ 2 * a⁻¹ ^ j := add_le_add hout hin
    _ ≤ nearGevreyProfileConstant * 96 ^ j *
          (j.factorial : ℝ) ^ 2 * a⁻¹ ^ j +
        nearGevreyProfileConstant * 96 ^ j *
          (j.factorial : ℝ) ^ 2 * a⁻¹ ^ j := by
      have hcoef : 0 ≤ nearGevreyProfileConstant * 96 ^ j *
          (j.factorial : ℝ) ^ 2 :=
        mul_nonneg
          (mul_nonneg nearGevreyProfileConstant_nonneg (by positivity))
          (sq_nonneg _)
      exact add_le_add
        (mul_le_mul_of_nonneg_left hscale hcoef) le_rfl
    _ = 2 * nearGevreyProfileConstant * 96 ^ j *
        (j.factorial : ℝ) ^ 2 * a⁻¹ ^ j := by ring

/-! ## The quotient profile -/

/-- Exact norm of the iterated derivative of the real-axis reciprocal,
viewed as a complex-valued function. -/
theorem norm_iteratedDeriv_complexInvId
    (j : ℕ) (x : ℝ) (hx : x ≠ 0) :
    ‖iteratedDeriv j (fun y : ℝ ↦ ((y : ℂ)⁻¹)) x‖ =
      (j.factorial : ℝ) / |x| ^ (j + 1) := by
  have hfun : (fun y : ℝ ↦ ((y : ℂ)⁻¹)) =
      fun y : ℝ ↦ ((y⁻¹ : ℝ) : ℂ) := by
    funext y
    push_cast
    rfl
  rw [hfun]
  have hcast := iteratedDeriv_complex_ofReal_eq
    (fun y : ℝ ↦ y⁻¹) j x (contDiffAt_inv ℝ hx)
  rw [hcast, iteratedDeriv_eq_iterate, iter_deriv_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [abs_zpow]
  have habs : |x| ≠ 0 := abs_ne_zero.mpr hx
  rw [show (-1 - (j : ℤ)) = -((j + 1 : ℕ) : ℤ) by push_cast; omega,
    zpow_neg, zpow_natCast]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (j.factorial : ℝ))]
  field_simp

/-- Away from the origin, Leibniz's rule for `W = rho / x` has every
binomial term displayed. -/
theorem iteratedDeriv_nearW_eq_sum
    (j : ℕ) (a ε x : ℝ) (hx : x ≠ 0) :
    iteratedDeriv j (nearW a ε) x =
      ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℂ) * iteratedDeriv i (nearRho a ε) x *
          iteratedDeriv (j - i) (fun y : ℝ ↦ ((y : ℂ)⁻¹)) x := by
  have hrho : ContDiffAt ℝ j (nearRho a ε) x :=
    (nearRho_contDiff a ε).of_le (by
      exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top)) |>.contDiffAt
  have hcastTop :
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : ℝ ↦ (y : ℂ)) x :=
    (Complex.ofRealCLM.contDiff.comp contDiff_id).contDiffAt
  have hcast : ContDiffAt ℝ j (fun y : ℝ ↦ (y : ℂ)) x :=
    hcastTop.of_le (by
      exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top))
  have hinv : ContDiffAt ℝ j (fun y : ℝ ↦ ((y : ℂ)⁻¹)) x :=
    hcast.inv (by exact_mod_cast hx)
  unfold nearW
  simpa only [div_eq_mul_inv, Complex.real_smul] using!
    (iteratedDeriv_fun_mul hrho hinv)

private theorem choose_mul_factorial_sq_mul_factorial_sub_le
    {j i : ℕ} (hi : i ≤ j) :
    (j.choose i : ℝ) * (i.factorial : ℝ) ^ 2 *
        ((j - i).factorial : ℝ) ≤ (j.factorial : ℝ) ^ 2 := by
  have hidNat := Nat.choose_mul_factorial_mul_factorial hi
  have hid : (j.choose i : ℝ) * (i.factorial : ℝ) *
      ((j - i).factorial : ℝ) = (j.factorial : ℝ) := by
    exact_mod_cast hidNat
  have hfacNat : i.factorial ≤ j.factorial := Nat.factorial_le hi
  have hfac : (i.factorial : ℝ) ≤ (j.factorial : ℝ) := by
    exact_mod_cast hfacNat
  calc
    (j.choose i : ℝ) * (i.factorial : ℝ) ^ 2 *
        ((j - i).factorial : ℝ) =
      ((j.choose i : ℝ) * (i.factorial : ℝ) *
        ((j - i).factorial : ℝ)) * (i.factorial : ℝ) := by ring
    _ = (j.factorial : ℝ) * (i.factorial : ℝ) := by rw [hid]
    _ ≤ (j.factorial : ℝ) * (j.factorial : ℝ) :=
      mul_le_mul_of_nonneg_left hfac (by positivity)
    _ = (j.factorial : ℝ) ^ 2 := by ring

private theorem inv_scale_mul_inv_abs_pow_le
    {a x : ℝ} {j i : ℕ} (ha : 0 < a) (hx : x ≠ 0)
    (hax : a ≤ |x|) (hi : i ≤ j) :
    a⁻¹ ^ i * |x|⁻¹ ^ (j - i + 1) ≤
      a⁻¹ ^ j * |x|⁻¹ := by
  have habs : 0 < |x| := abs_pos.mpr hx
  have hinv : |x|⁻¹ ≤ a⁻¹ :=
    (inv_le_inv₀ habs ha).2 hax
  have hp : |x|⁻¹ ^ (j - i) ≤ a⁻¹ ^ (j - i) :=
    pow_le_pow_left₀ (by positivity) hinv (j - i)
  have haInv : 0 ≤ a⁻¹ := (inv_pos.mpr ha).le
  have hxInv : 0 ≤ |x|⁻¹ := (inv_pos.mpr habs).le
  calc
    a⁻¹ ^ i * |x|⁻¹ ^ (j - i + 1) =
        (a⁻¹ ^ i * |x|⁻¹ ^ (j - i)) * |x|⁻¹ := by
      rw [pow_succ]
      ring
    _ ≤ (a⁻¹ ^ i * a⁻¹ ^ (j - i)) * |x|⁻¹ := by
      gcongr
    _ = a⁻¹ ^ j * |x|⁻¹ := by
      rw [← pow_add, Nat.add_sub_of_le hi]

private theorem nat_succ_le_two_pow : ∀ j : ℕ, j + 1 ≤ 2 ^ j
  | 0 => by simp
  | j + 1 => by
      calc
        j + 1 + 1 ≤ 2 * (j + 1) := by omega
        _ ≤ 2 * 2 ^ j := Nat.mul_le_mul_left 2 (nat_succ_le_two_pow j)
        _ = 2 ^ (j + 1) := by rw [pow_succ]; ring

/-- Pointwise Gevrey bound for the quotient profile on the retained
annulus.  The remaining factor `|x|⁻¹` is kept rather than replaced by
`a⁻¹`; its square integrates to the required extra factor `a⁻¹`. -/
theorem norm_iteratedDeriv_nearW_le
    (j : ℕ) (a ε x : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (haε : a ≤ ε / 4) (hax : a ≤ |x|) :
    ‖iteratedDeriv j (nearW a ε) x‖ ≤
      2 * nearGevreyProfileConstant * 192 ^ j *
        (j.factorial : ℝ) ^ 2 * a⁻¹ ^ j * |x|⁻¹ := by
  have hx : x ≠ 0 := by
    intro hzero
    subst x
    simp only [abs_zero] at hax
    linarith
  rw [iteratedDeriv_nearW_eq_sum j a ε x hx]
  calc
    ‖∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℂ) * iteratedDeriv i (nearRho a ε) x *
          iteratedDeriv (j - i) (fun y : ℝ ↦ ((y : ℂ)⁻¹)) x‖ ≤
      ∑ i ∈ Finset.range (j + 1),
        ‖(j.choose i : ℂ) * iteratedDeriv i (nearRho a ε) x *
          iteratedDeriv (j - i) (fun y : ℝ ↦ ((y : ℂ)⁻¹)) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (j + 1),
        2 * nearGevreyProfileConstant * 96 ^ j *
          (j.factorial : ℝ) ^ 2 * a⁻¹ ^ j * |x|⁻¹ := by
      apply Finset.sum_le_sum
      intro i hi
      have hij : i ≤ j := by
        have := Finset.mem_range.mp hi
        omega
      have hrho := norm_iteratedDeriv_nearRho_le
        i a ε x ha hε haε
      have hinv := norm_iteratedDeriv_complexInvId (j - i) x hx
      have hinv' :
          ‖iteratedDeriv (j - i) (fun y : ℝ ↦ ((y : ℂ)⁻¹)) x‖ =
            ((j - i).factorial : ℝ) * |x|⁻¹ ^ (j - i + 1) := by
        rw [hinv, div_eq_mul_inv, ← inv_pow]
      have hchoose := choose_mul_factorial_sq_mul_factorial_sub_le hij
      have h96 : (96 : ℝ) ^ i ≤ 96 ^ j :=
        pow_le_pow_right₀ (by norm_num) hij
      have hscale := inv_scale_mul_inv_abs_pow_le ha hx hax hij
      have hC := nearGevreyProfileConstant_nonneg
      rw [norm_mul, norm_mul, Complex.norm_natCast, hinv']
      calc
        (j.choose i : ℝ) *
            ‖iteratedDeriv i (nearRho a ε) x‖ *
              (((j - i).factorial : ℝ) * |x|⁻¹ ^ (j - i + 1)) ≤
          (j.choose i : ℝ) *
            (2 * nearGevreyProfileConstant * 96 ^ i *
              (i.factorial : ℝ) ^ 2 * a⁻¹ ^ i) *
              (((j - i).factorial : ℝ) * |x|⁻¹ ^ (j - i + 1)) := by
            gcongr
        _ = 2 * nearGevreyProfileConstant *
            ((j.choose i : ℝ) * (i.factorial : ℝ) ^ 2 *
              ((j - i).factorial : ℝ)) * 96 ^ i *
              (a⁻¹ ^ i * |x|⁻¹ ^ (j - i + 1)) := by ring
        _ ≤ 2 * nearGevreyProfileConstant *
            ((j.factorial : ℝ) ^ 2) * 96 ^ j *
              (a⁻¹ ^ j * |x|⁻¹) := by
            gcongr
        _ = 2 * nearGevreyProfileConstant * 96 ^ j *
            (j.factorial : ℝ) ^ 2 * a⁻¹ ^ j * |x|⁻¹ := by ring
    _ = ((j + 1 : ℕ) : ℝ) *
        (2 * nearGevreyProfileConstant * 96 ^ j *
          (j.factorial : ℝ) ^ 2 * a⁻¹ ^ j * |x|⁻¹) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ j *
        (2 * nearGevreyProfileConstant * 96 ^ j *
          (j.factorial : ℝ) ^ 2 * a⁻¹ ^ j * |x|⁻¹) := by
      have hcast : ((j + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ j := by
        exact_mod_cast nat_succ_le_two_pow j
      have hnonneg : 0 ≤
          2 * nearGevreyProfileConstant * 96 ^ j *
            (j.factorial : ℝ) ^ 2 * a⁻¹ ^ j * |x|⁻¹ := by
        have hC := nearGevreyProfileConstant_nonneg
        positivity
      exact mul_le_mul_of_nonneg_right hcast hnonneg
    _ = 2 * nearGevreyProfileConstant * 192 ^ j *
        (j.factorial : ℝ) ^ 2 * a⁻¹ ^ j * |x|⁻¹ := by
      rw [show (192 : ℝ) ^ j = 2 ^ j * 96 ^ j by
        rw [← mul_pow]
        norm_num]
      ring

/-- All derivatives of `W` vanish strictly inside the deleted interval. -/
theorem iteratedDeriv_nearW_eq_zero_of_abs_lt
    (j : ℕ) (a ε x : ℝ) (ha : 0 < a) (haε : a ≤ ε / 4)
    (hx : |x| < a) :
    iteratedDeriv j (nearW a ε) x = 0 := by
  have hopen : IsOpen {y : ℝ | |y| < a} :=
    isOpen_lt continuous_abs continuous_const
  have hnhds : {y : ℝ | |y| < a} ∈ 𝓝 x := hopen.mem_nhds hx
  have heq : nearW a ε =ᶠ[𝓝 x] (fun _ : ℝ ↦ 0) := by
    filter_upwards [hnhds] with y hy
    unfold nearW
    rw [nearRho_eq_zero_of_abs_le a ε y ha haε hy.le, zero_div]
  rw [heq.iteratedDeriv_eq j]
  simp [iteratedDeriv_const]

end

end Erdos1002
