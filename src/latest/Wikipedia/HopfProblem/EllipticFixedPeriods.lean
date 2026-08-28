import Wikipedia.HopfProblem.EllipticData
import Wikipedia.HopfProblem.PeriodMonodromy

/-!
# Explicit fixed periods for the elliptic transformations

The order-three and order-four period transformations have actual fixed
points in the admissible period domain.  The examples below fix `β = -I`
and verify both the period inequalities and all three fixed-point equations.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic

/-- The elliptic transformation corresponding to the chosen order. -/
def periodStep (j : Kind) (p : PeriodDomain) : PeriodDomain :=
  match j with
  | .three => p.step₁
  | .four => p.step₂

/-- Fixed points in the actual admissible period domain. -/
abbrev FixedPeriod (j : Kind) := {p : PeriodDomain // periodStep j p = p}

/-- Concrete order-three and order-four fixed period parameters. -/
def examplePeriodPoint : Kind → PeriodPoint
  | .three => ⟨(1 + Complex.I * (Real.sqrt 3 : ℂ)) / 2,
      (1 : ℂ) / 2 - Complex.I * (Real.sqrt 3 : ℂ) / 6, -Complex.I⟩
  | .four => ⟨Complex.I, (1 - Complex.I) / 2, -Complex.I⟩

theorem examplePeriodPoint_tau_im_pos (j : Kind) :
    0 < (examplePeriodPoint j).τ.im := by
  cases j
  · simp only [examplePeriodPoint, Complex.div_ofNat_im, Complex.add_im,
      Complex.one_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]
    positivity
  · norm_num [examplePeriodPoint]

@[simp] theorem examplePeriodPoint_beta_im (j : Kind) :
    (examplePeriodPoint j).β.im = -1 := by
  cases j <;> norm_num [examplePeriodPoint]

theorem examplePeriodPoint_admissible (j : Kind) : (examplePeriodPoint j).Admissible := by
  refine ⟨examplePeriodPoint_tau_im_pos j, ?_⟩
  have hn : 0 ≤ 6 * (examplePeriodPoint j).μ.im ^ 2 / (examplePeriodPoint j).τ.im :=
    div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (examplePeriodPoint_tau_im_pos j).le
  rw [PeriodPoint.discriminant, examplePeriodPoint_beta_im]
  linarith

/-- The explicit parameters lie in the genuine open period domain. -/
def examplePeriod (j : Kind) : PeriodDomain :=
  ⟨examplePeriodPoint j, examplePeriodPoint_admissible j⟩

theorem examplePeriodPoint_three_fixed :
    (examplePeriodPoint .three).step₁ = examplePeriodPoint .three := by
  have hs : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have ht : 1 + Complex.I * (Real.sqrt 3 : ℂ) ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    norm_num at h'
  apply PeriodPoint.ext <;>
    dsimp [examplePeriodPoint, PeriodPoint.step₁] <;>
    field_simp [ht] <;> ring_nf <;> simp [Complex.I_sq, hs] <;> ring

theorem examplePeriodPoint_four_fixed :
    (examplePeriodPoint .four).step₂ = examplePeriodPoint .four := by
  apply PeriodPoint.ext <;> apply Complex.ext <;>
    norm_num [examplePeriodPoint, PeriodPoint.step₂, Complex.div_re, Complex.div_im,
      Complex.mul_re, Complex.mul_im, Complex.normSq_apply, pow_two]

theorem examplePeriod_fixed (j : Kind) : periodStep j (examplePeriod j) = examplePeriod j := by
  cases j
  · exact Subtype.ext examplePeriodPoint_three_fixed
  · exact Subtype.ext examplePeriodPoint_four_fixed

/-- Explicit inhabitants of both elliptic fixed-period loci. -/
def exampleFixedPeriod (j : Kind) : FixedPeriod j :=
  ⟨examplePeriod j, examplePeriod_fixed j⟩

instance FixedPeriod.nonempty (j : Kind) : Nonempty (FixedPeriod j) :=
  ⟨exampleFixedPeriod j⟩

end Wikipedia.HopfProblem.Elliptic
