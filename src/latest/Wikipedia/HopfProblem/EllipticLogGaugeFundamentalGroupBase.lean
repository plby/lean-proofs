import Wikipedia.HopfProblem.EllipticLogGaugeRotation
import Wikipedia.HopfProblem.SpecialPeriodsTauCuspDomain

/-!
# The logarithmic meridian in the elliptic base disc

The normalized logarithm moves from `s₀` to `s₀ - 1 / m`, at constant
imaginary part. Its exponential is a nonzero path in the actual unit
disc, from its initial point to the selected order-`m` base rotation.
Its radius, and hence the radius of its `m`-th power, remain constant.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HopfProblem.Elliptic.LogGauge

open SpecialPeriods CuspUniformization

/-- The negative primitive-angle meridian in normalized logarithmic coordinates. -/
def logMeridianParameter (j : Kind) (s₀ : ℂ) (t : I) : ℂ :=
  s₀ - ((t : ℝ) : ℂ) / (j.order : ℂ)

theorem logMeridianParameter_continuous (j : Kind) (s₀ : ℂ) :
    Continuous (logMeridianParameter j s₀) := by
  unfold logMeridianParameter
  fun_prop

@[simp] theorem logMeridianParameter_zero (j : Kind) (s₀ : ℂ) :
    logMeridianParameter j s₀ 0 = s₀ := by
  simp [logMeridianParameter]

@[simp] theorem logMeridianParameter_one (j : Kind) (s₀ : ℂ) :
    logMeridianParameter j s₀ 1 = s₀ - 1 / (j.order : ℂ) := by
  simp [logMeridianParameter]

@[simp] theorem logMeridianParameter_im (j : Kind) (s₀ : ℂ) (t : I) :
    (logMeridianParameter j s₀ t).im = s₀.im := by
  simp [logMeridianParameter, Complex.div_im]

theorem logMeridianParameter_exponential_norm (j : Kind) (s₀ : ℂ) (t : I) :
    ‖exponential (logMeridianParameter j s₀ t)‖ = ‖exponential s₀‖ := by
  simp [exponential, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- The root of the base meridian, as a point of the actual unit disc. -/
def logMeridianRoot (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im) (t : I) : Disc :=
  ⟨exponential (logMeridianParameter j s₀ t), by
    change dist (exponential (logMeridianParameter j s₀ t)) 0 < 1
    rw [dist_zero_right]
    apply TauCusp.exponential_norm_lt_one_of_upperHalfPlane
    simpa only [logMeridianParameter_im] using hs₀⟩

@[simp] theorem logMeridianRoot_coe (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im) (t : I) :
    (logMeridianRoot j s₀ hs₀ t : ℂ) = exponential (logMeridianParameter j s₀ t) := rfl

theorem logMeridianRoot_continuous (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    Continuous (logMeridianRoot j s₀ hs₀) :=
  (exponential_holomorphic.continuous.comp
    (logMeridianParameter_continuous j s₀)).subtype_mk _

@[simp] theorem logMeridianRoot_ne_zero (j : Kind) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im) (t : I) :
    (logMeridianRoot j s₀ hs₀ t : ℂ) ≠ 0 := exponential_ne_zero _

@[simp] theorem logMeridianRoot_zero (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    (logMeridianRoot j s₀ hs₀ 0 : ℂ) = exponential s₀ := by
  simp

@[simp] theorem logMeridianRoot_one (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    logMeridianRoot j s₀ hs₀ 1 = familyRotation j (logMeridianRoot j s₀ hs₀ 0) := by
  apply Subtype.ext
  rw [familyRotation_val_exponential, logMeridianRoot_zero, logMeridianRoot_coe,
    logMeridianParameter_one, sub_eq_add_neg, exponential_add]
  exact mul_comm _ _

theorem logMeridianRoot_norm (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im) (t : I) :
    ‖(logMeridianRoot j s₀ hs₀ t : ℂ)‖ = ‖exponential s₀‖ :=
  logMeridianParameter_exponential_norm j s₀ t

/-- Any power of the root path has constant norm. -/
theorem logMeridianRoot_pow_norm (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (n : ℕ) (t : I) :
    ‖(logMeridianRoot j s₀ hs₀ t : ℂ) ^ n‖ = ‖exponential s₀‖ ^ n := by
  rw [norm_pow, logMeridianRoot_norm]

/-- A radius bound at the initial point holds along the entire powered path. -/
theorem logMeridianRoot_pow_norm_lt (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (n : ℕ) {r : ℝ} (hr : ‖exponential s₀‖ ^ n < r) (t : I) :
    ‖(logMeridianRoot j s₀ hs₀ t : ℂ) ^ n‖ < r := by
  rw [logMeridianRoot_pow_norm]
  exact hr

/-- The literal root path, ending at the actual selected base rotation. -/
def logMeridianBasePath (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    Path (logMeridianRoot j s₀ hs₀ 0)
      (familyRotation j (logMeridianRoot j s₀ hs₀ 0)) where
  toFun := logMeridianRoot j s₀ hs₀
  continuous_toFun := logMeridianRoot_continuous j s₀ hs₀
  source' := rfl
  target' := logMeridianRoot_one j s₀ hs₀

@[simp] theorem logMeridianBasePath_apply (j : Kind) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im) (t : I) :
    logMeridianBasePath j s₀ hs₀ t = logMeridianRoot j s₀ hs₀ t := rfl

end Wikipedia.HopfProblem.Elliptic.LogGauge
