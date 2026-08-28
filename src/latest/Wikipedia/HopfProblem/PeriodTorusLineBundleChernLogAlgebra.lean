import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLogCocycle

/-!
# Algebra of the actual positive factor-log defect

The convention throughout is
`b(l+m,z) - b(l,z+m) - b(m,z) = 2πi κ(l,m)`.
Addition, negation, gauge logarithms, and integer branch changes are
computed with this sign.  In particular a branch change contributes the
negative of the standard group-cochain coboundary.  These are logarithmic
identities, not a definition or sign choice for a Chern class.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleChernLog

open PeriodTorusLineBundleClassification

/-- The actual exponential period used by the factor logarithms. -/
abbrev logPeriod : ℂ := 2 * (Real.pi : ℂ) * Complex.I

theorem logPeriod_ne_zero : logPeriod ≠ 0 :=
  mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero

/-- The integer correction for our positive logarithmic-defect convention. -/
def logCoboundary {A : Type*} [Add A] (t : A → ℤ) (l m : A) : ℤ :=
  t (l + m) - t l - t m

/-- This sign is opposite to the standard inhomogeneous group-cochain coboundary. -/
theorem logCoboundary_eq_neg_standard {A : Type*} [Add A]
    (t : A → ℤ) (l m : A) :
    logCoboundary t l m = -(t l + t m - t (l + m)) := by
  unfold logCoboundary
  ring

theorem logCoboundary_comm {A : Type*} [AddCommMonoid A]
    (t : A → ℤ) (l m : A) : logCoboundary t l m = logCoboundary t m l := by
  simp only [logCoboundary, add_comm l m]
  ring

theorem logCoboundary_zero_left {A : Type*} [AddMonoid A]
    (t : A → ℤ) (ht : t 0 = 0) (l : A) : logCoboundary t 0 l = 0 := by
  simp [logCoboundary, ht]

theorem logCoboundary_zero_right {A : Type*} [AddMonoid A]
    (t : A → ℤ) (ht : t 0 = 0) (l : A) : logCoboundary t l 0 = 0 := by
  simp [logCoboundary, ht]

variable {p : PeriodDomain}
  {b c : p.lattice → ComplexPlane₂ → ℂ} {n n' : p.lattice → p.lattice → ℤ}

/-- Addition of actual logarithms adds their integer defects. -/
theorem logDefect_add (hb : HasIntegerLogDefect p b n)
    (hc : HasIntegerLogDefect p c n') :
    HasIntegerLogDefect p (fun l z => b l z + c l z) (fun l m => n l m + n' l m) := by
  intro l m z
  push_cast
  linear_combination hb l m z + hc l m z

/-- Negating a logarithm negates its positive factor-log defect. -/
theorem logDefect_neg (hb : HasIntegerLogDefect p b n) :
    HasIntegerLogDefect p (fun l z => -b l z) (fun l m => -n l m) := by
  intro l m z
  push_cast
  linear_combination -hb l m z

theorem logDefect_sub (hb : HasIntegerLogDefect p b n)
    (hc : HasIntegerLogDefect p c n') :
    HasIntegerLogDefect p (fun l z => b l z - c l z) (fun l m => n l m - n' l m) := by
  simpa only [sub_eq_add_neg] using logDefect_add hb (logDefect_neg hc)

/-- Integer powers at the factor level correspond to integer multiples of logarithms. -/
theorem logDefect_intMul (hb : HasIntegerLogDefect p b n) (r : ℤ) :
    HasIntegerLogDefect p (fun l z => (r : ℂ) * b l z) (fun l m => r * n l m) := by
  intro l m z
  push_cast
  linear_combination (r : ℂ) * hb l m z

/-- A logarithmic gauge change for the positive-translation factor convention. -/
def logGauge (b : p.lattice → ComplexPlane₂ → ℂ) (u : ComplexPlane₂ → ℂ)
    (l : p.lattice) (z : ComplexPlane₂) : ℂ :=
  b l z + u (z + l) - u z

/-- A gauge logarithm cancels exactly in the integer factor-log defect. -/
theorem logDefect_gauge (hb : HasIntegerLogDefect p b n) (u : ComplexPlane₂ → ℂ) :
    HasIntegerLogDefect p (logGauge b u) n := by
  intro l m z
  simp only [logGauge, Submodule.coe_add, add_assoc,
    add_comm (m : ComplexPlane₂) (l : ComplexPlane₂)]
  linear_combination hb l m z

theorem logGauge_zero (hb : ∀ z, b 0 z = 0) (u : ComplexPlane₂ → ℂ)
    (z : ComplexPlane₂) : logGauge b u 0 z = 0 := by
  simp [logGauge, hb]

/-- Exponentiation gives the actual positive-translation gauge-factor formula. -/
theorem logGauge_exp (b : p.lattice → ComplexPlane₂ → ℂ) (u : ComplexPlane₂ → ℂ)
    (l : p.lattice) (z : ComplexPlane₂) :
    Complex.exp (logGauge b u l z) =
      Complex.exp (b l z) * Complex.exp (u (z + l)) / Complex.exp (u z) := by
  rw [logGauge, Complex.exp_sub, Complex.exp_add]

/-- Changing the branch by an actual integer multiple of the exponential period. -/
def logIntegerShift (b : p.lattice → ComplexPlane₂ → ℂ) (t : p.lattice → ℤ)
    (l : p.lattice) (z : ComplexPlane₂) : ℂ :=
  b l z + (t l : ℂ) * logPeriod

/-- The exact branch correction is `t(l+m)-t(l)-t(m)`, with the displayed positive sign. -/
theorem logDefect_integerShift (hb : HasIntegerLogDefect p b n) (t : p.lattice → ℤ) :
    HasIntegerLogDefect p (logIntegerShift b t) (fun l m => n l m + logCoboundary t l m) := by
  intro l m z
  dsimp only [logIntegerShift, logCoboundary, logPeriod]
  push_cast
  linear_combination hb l m z

theorem logIntegerShift_zero (hb : ∀ z, b 0 z = 0)
    (t : p.lattice → ℤ) (ht : t 0 = 0) (z : ComplexPlane₂) :
    logIntegerShift b t 0 z = 0 := by
  simp [logIntegerShift, hb, ht]

/-- An integer branch change does not change the actual exponential factor. -/
theorem logIntegerShift_exp (b : p.lattice → ComplexPlane₂ → ℂ)
    (t : p.lattice → ℤ) (l : p.lattice) (z : ComplexPlane₂) :
    Complex.exp (logIntegerShift b t l z) = Complex.exp (b l z) := by
  rw [logIntegerShift, Complex.exp_add,
    Complex.exp_eq_one_iff.mpr ⟨t l, rfl⟩, mul_one]

end Wikipedia.HopfProblem.PeriodTorusLineBundleChernLog
