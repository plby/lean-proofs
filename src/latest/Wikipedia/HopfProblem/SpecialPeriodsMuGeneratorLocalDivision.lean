import Wikipedia.HopfProblem.SpecialPeriodsGlobalTauUniqueness
import Wikipedia.HopfProblem.HolomorphicCousinDivision
import Mathlib.Analysis.Analytic.Order

/-!
# Local division of homogeneous mu sections at the elliptic centres

The actual homogeneous generator laws force a zero of order at least two
at the order-three centre, and a zero of order at least one at the
order-four centre.  Dividing by an analytic denominator with these exact
orders therefore has a locally analytic extension, with a constructed
removable value.  No analyticity of the raw total quotient at `0 / 0` is
asserted, and no existence of a global special period map is assumed.
-/

noncomputable section

open Filter Set UpperHalfPlane
open scoped Topology ContDiff Manifold MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods.MuGenerator

/-- A scalar-valued holomorphic function on the actual upper half-plane
is analytic in the ambient complex coordinate at each interior point. -/
theorem scalar_analyticAt {f : ℍ → ℂ} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (a : ℍ) :
    AnalyticAt ℂ (f ∘ ofComplex) (a : ℂ) :=
  (UpperHalfPlane.mdifferentiable_iff.mp (hf.mdifferentiable (by simp))).analyticAt
    (isOpen_upperHalfPlaneSet.mem_nhds a.im_pos)

/-- The homogeneous first-generator law already forces the value zero;
only the upper-half-plane range of `τ` is needed for this value statement. -/
theorem homogeneous_centerOne_eq_zero {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hν₁ : ∀ z : ℍ, ν (Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ)) :
    ν Triangle.centerOne = 0 := by
  have he := hν₁ Triangle.centerOne
  rw [Triangle.generatorOne_fix] at he
  have hmul : ν Triangle.centerOne * (τ Triangle.centerOne : ℂ) = -ν Triangle.centerOne :=
    (eq_div_iff (τ Triangle.centerOne).ne_zero).mp he
  have hz : ν Triangle.centerOne * ((τ Triangle.centerOne : ℂ) + 1) = 0 := by
    calc
      _ = ν Triangle.centerOne * (τ Triangle.centerOne : ℂ) + ν Triangle.centerOne := by ring
      _ = 0 := by rw [hmul]; ring
  apply (mul_eq_zero.mp hz).resolve_right
  intro hc
  have hi := congrArg Complex.im hc
  simp only [Complex.add_im, Complex.one_im, add_zero, Complex.zero_im] at hi
  exact (τ Triangle.centerOne).im_ne_zero hi

/-- The homogeneous second-generator law forces the value zero at the
actual order-four centre, without any independent normalization assumption. -/
theorem homogeneous_centerTwo_eq_zero {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hν₂ : ∀ z : ℍ, ν (Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ)) :
    ν Triangle.centerTwo = 0 := by
  have he := hν₂ Triangle.centerTwo
  rw [Triangle.generatorTwo_fix] at he
  have hmul : ν Triangle.centerTwo * (τ Triangle.centerTwo : ℂ) = ν Triangle.centerTwo :=
    (eq_div_iff (τ Triangle.centerTwo).ne_zero).mp he
  have hz : ν Triangle.centerTwo * ((τ Triangle.centerTwo : ℂ) - 1) = 0 := by
    calc
      _ = ν Triangle.centerTwo * (τ Triangle.centerTwo : ℂ) - ν Triangle.centerTwo := by ring
      _ = 0 := by rw [hmul]; ring
  apply (mul_eq_zero.mp hz).resolve_right
  intro hc
  have hi := congrArg Complex.im hc
  simp only [Complex.sub_im, Complex.one_im, sub_zero, Complex.zero_im] at hi
  exact (τ Triangle.centerTwo).im_ne_zero hi

/-- Differentiate the actual homogeneous product law at a fixed point.
The term involving the derivative of `τ` disappears because `ν` vanishes. -/
theorem homogeneous_fixed_derivative_identity {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν)
    (g : SL(2, ℝ)) (a : ℍ) (c : ℂ) (hfix : g • a = a) (hzero : ν a = 0)
    (hlaw : ∀ z : ℍ, ν (g • z) * (τ z : ℂ) = c * ν z) :
    (deriv (ν ∘ ofComplex) (a : ℂ) * Triangle.slMultiplier g a) * (τ a : ℂ) =
      c * deriv (ν ∘ ofComplex) (a : ℂ) := by
  let V : ℂ → ℂ := ν ∘ ofComplex
  let T : ℂ → ℂ := fun z => (τ (ofComplex z) : ℂ)
  let A : ℂ → ℂ := fun z => ((g • ofComplex z : ℍ) : ℂ)
  have hV := (scalar_analyticAt hν a).differentiableAt.hasDerivAt
  have hTa := scalar_analyticAt (UpperHalfPlane.contMDiff_coe.comp hτ) a
  have hT := hTa.differentiableAt.hasDerivAt
  have hA : HasDerivAt A (Triangle.slMultiplier g a) (a : ℂ) :=
    (Triangle.sl_hasStrictDerivAt_smul g a).hasDerivAt
  have hAa : A (a : ℂ) = (a : ℂ) := by simp [A, hfix]
  have hVo : HasDerivAt V (deriv V (a : ℂ)) (A (a : ℂ)) := by
    rw [hAa]
    exact hV
  have hcomp : HasDerivAt (fun z : ℂ => ν (g • ofComplex z))
      (deriv V (a : ℂ) * Triangle.slMultiplier g a) (a : ℂ) := by
    simpa only [V, A, Function.comp_def, ofComplex_apply] using hVo.comp (a : ℂ) hA
  have hprod : HasDerivAt (fun z : ℂ => ν (g • ofComplex z) * T z)
      ((deriv V (a : ℂ) * Triangle.slMultiplier g a) * (τ a : ℂ)) (a : ℂ) := by
    simpa only [T, Function.comp_def, Pi.mul_def, ofComplex_apply, hfix, hzero,
      zero_mul, add_zero]
      using hcomp.mul hT
  have he : (fun z : ℂ => ν (g • ofComplex z) * T z) = fun z => c * V z := by
    funext z
    exact hlaw (ofComplex z)
  rw [he] at hprod
  exact hprod.unique (hV.const_mul c)

/-- The first derivative also vanishes at the order-three centre.
Its actual source multiplier is `-ρ`, whereas the homogeneous multiplier
is `-1 / ρ`; their inequality forces the derivative to be zero. -/
theorem homogeneous_centerOne_deriv_eq_zero {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : TauCovariant τ)
    (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν)
    (hν₁ : ∀ z : ℍ, ν (Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ)) :
    deriv (ν ∘ ofComplex) (Triangle.centerOne : ℂ) = 0 := by
  have hzero := homogeneous_centerOne_eq_zero hν₁
  have hprod : ∀ z : ℍ,
      ν (Triangle.generatorOneSL • z) * (τ z : ℂ) = (-1 : ℂ) * ν z := by
    intro z
    rw [hν₁, div_mul_cancel₀ _ (τ z).ne_zero, neg_one_mul]
  have hd := homogeneous_fixed_derivative_identity hτ hν Triangle.generatorOneSL
    Triangle.centerOne (-1) Triangle.generatorOne_fix hzero hprod
  rw [Triangle.generatorOne_multiplier, (tau_covariant_values hτc).1] at hd
  change (deriv (ν ∘ ofComplex) (Triangle.centerOne : ℂ) * -rho) * rho =
    -1 * deriv (ν ∘ ofComplex) (Triangle.centerOne : ℂ) at hd
  have hz : deriv (ν ∘ ofComplex) (Triangle.centerOne : ℂ) * (rho ^ 2 - 1) = 0 := by
    linear_combination -hd
  apply (mul_eq_zero.mp hz).resolve_right
  intro hc
  rw [rho_sq] at hc
  have hi := congrArg Complex.im hc
  simp only [Complex.sub_im, Complex.one_im, sub_zero, Complex.zero_im] at hi
  exact rho_im_pos.ne' hi

/-- Cancel a common analytic vanishing factor, including when the
numerator vanishes on a whole neighbourhood. -/
theorem exists_analytic_factor_of_order_le {ν f : ℂ → ℂ} {a : ℂ} {n : ℕ}
    (hν : AnalyticAt ℂ ν a) (hf : AnalyticAt ℂ f a)
    (hforder : analyticOrderAt f a = (n : ℕ∞))
    (hνorder : (n : ℕ∞) ≤ analyticOrderAt ν a) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h a ∧
      ν =ᶠ[𝓝 a] fun z => f z * h z := by
  obtain ⟨u, hu, hu0, hfu⟩ := hf.analyticOrderAt_eq_natCast.mp hforder
  obtain ⟨v, hv, hνv⟩ := (natCast_le_analyticOrderAt hν).mp hνorder
  refine ⟨fun z => v z / u z, hv.div hu hu0, ?_⟩
  filter_upwards [hfu, hνv, hu.continuousAt.eventually_ne hu0] with z hfz hνz huz
  simp only [smul_eq_mul] at hfz hνz
  rw [hfz, hνz]
  field_simp

/-- An analytic numerator vanishing at the centre is divisible by an
analytic denominator with an exact simple zero. -/
theorem exists_analytic_factor_of_simple_zero {ν f : ℂ → ℂ} {a : ℂ}
    (hν : AnalyticAt ℂ ν a) (hf : AnalyticAt ℂ f a)
    (hforder : analyticOrderAt f a = 1) (hν0 : ν a = 0) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h a ∧
      ν =ᶠ[𝓝 a] fun z => f z * h z := by
  apply exists_analytic_factor_of_order_le hν hf (n := 1) hforder
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hν]
  intro k hk
  have hk0 : k = 0 := by omega
  subst k
  simpa using hν0

/-- Vanishing of the numerator and its first derivative permits division
by an analytic denominator with an exact double zero. -/
theorem exists_analytic_factor_of_double_zero {ν f : ℂ → ℂ} {a : ℂ}
    (hν : AnalyticAt ℂ ν a) (hf : AnalyticAt ℂ f a)
    (hforder : analyticOrderAt f a = 2) (hν0 : ν a = 0) (hν1 : deriv ν a = 0) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h a ∧
      ν =ᶠ[𝓝 a] fun z => f z * h z := by
  apply exists_analytic_factor_of_order_le hν hf (n := 2) hforder
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hν]
  intro k hk
  have hk01 : k = 0 ∨ k = 1 := by omega
  rcases hk01 with rfl | rfl
  · simpa using hν0
  · simpa using hν1

/-- The actual homogeneous law forces ambient analytic order at least
two at the order-three centre.  The order is allowed to be infinite. -/
theorem homogeneous_centerOne_order_ge_two {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : TauCovariant τ)
    (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν)
    (hν₁ : ∀ z : ℍ, ν (Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ)) :
    (2 : ℕ∞) ≤ analyticOrderAt (ν ∘ ofComplex) (Triangle.centerOne : ℂ) := by
  rw [show (2 : ℕ∞) = (2 : ℕ) by rfl,
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (scalar_analyticAt hν _)]
  intro k hk
  have hk01 : k = 0 ∨ k = 1 := by omega
  rcases hk01 with rfl | rfl
  · simpa only [iteratedDeriv_zero, Function.comp_apply, ofComplex_apply] using
      homogeneous_centerOne_eq_zero hν₁
  · simpa only [iteratedDeriv_one] using homogeneous_centerOne_deriv_eq_zero hτ hτc hν hν₁

/-- The actual homogeneous second-generator law forces ambient analytic
order at least one at the order-four centre. -/
theorem homogeneous_centerTwo_order_ge_one {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν)
    (hν₂ : ∀ z : ℍ, ν (Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ)) :
    (1 : ℕ∞) ≤ analyticOrderAt (ν ∘ ofComplex) (Triangle.centerTwo : ℂ) := by
  rw [show (1 : ℕ∞) = (1 : ℕ) by rfl,
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (scalar_analyticAt hν _)]
  intro k hk
  have hk0 : k = 0 := by omega
  subst k
  simpa only [iteratedDeriv_zero, Function.comp_apply, ofComplex_apply] using
    homogeneous_centerTwo_eq_zero hν₂

/-- Division by an exact double zero at the first actual elliptic centre
has an analytic removable extension for every homogeneous section. -/
theorem exists_division_at_centerOne {τ : ℍ → ℍ} {ν f : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : TauCovariant τ)
    (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν)
    (hν₁ : ∀ z : ℍ, ν (Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ))
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hforder : analyticOrderAt (f ∘ ofComplex) (Triangle.centerOne : ℂ) = 2) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h (Triangle.centerOne : ℂ) ∧
      (ν ∘ ofComplex) =ᶠ[𝓝 (Triangle.centerOne : ℂ)]
        fun z => (f ∘ ofComplex) z * h z :=
  exists_analytic_factor_of_order_le (scalar_analyticAt hν _) (scalar_analyticAt hf _)
    (n := 2) hforder (homogeneous_centerOne_order_ge_two hτ hτc hν hν₁)

/-- Division by an exact simple zero at the second actual elliptic
centre has an analytic removable extension for every homogeneous section. -/
theorem exists_division_at_centerTwo {τ : ℍ → ℍ} {ν f : ℍ → ℂ}
    (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν)
    (hν₂ : ∀ z : ℍ, ν (Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ))
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hforder : analyticOrderAt (f ∘ ofComplex) (Triangle.centerTwo : ℂ) = 1) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h (Triangle.centerTwo : ℂ) ∧
      (ν ∘ ofComplex) =ᶠ[𝓝 (Triangle.centerTwo : ℂ)]
        fun z => (f ∘ ofComplex) z * h z :=
  exists_analytic_factor_of_order_le (scalar_analyticAt hν _) (scalar_analyticAt hf _)
    (n := 1) hforder (homogeneous_centerTwo_order_ge_one hν hν₂)

end Wikipedia.HopfProblem.SpecialPeriods.MuGenerator
