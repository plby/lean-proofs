import Wikipedia.HopfProblem.SpecialPeriodsMuGeneratorLocalDivision

/-!
# Germ-local division of homogeneous mu sections

These results require holomorphicity only at the actual elliptic centre
and require the homogeneous transformation law only as an equality of
germs there.  No local section is presumed to extend to a globally
holomorphic or globally homogeneous function.

The locally analytic quotient is constructed by cancelling the common
vanishing factor, so its value at the removable point is not the raw
total-field value `0 / 0`.
-/

noncomputable section

open Filter Set UpperHalfPlane
open scoped Topology ContDiff Manifold MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods.MuGenerator

/-- Holomorphicity at one upper-half-plane point gives analyticity of
its actual ambient complex germ, without a global holomorphicity hypothesis. -/
theorem scalar_analyticAt_of_contMDiffAt {f : ℍ → ℂ} {a : ℍ}
    (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f a) :
    AnalyticAt ℂ (f ∘ ofComplex) (a : ℂ) :=
  (UpperHalfPlane.contMDiffAt_iff.mp hf).analyticAt

/-- Pull a native upper-half-plane germ equality to the actual ambient
complex coordinate at an interior point. -/
theorem eventuallyEq_comp_ofComplex {Y : Type*} {f g : ℍ → Y} {a : ℍ}
    (hfg : f =ᶠ[𝓝 a] g) :
    (f ∘ ofComplex) =ᶠ[𝓝 (a : ℂ)] (g ∘ ofComplex) := by
  have hc : Tendsto ofComplex (𝓝 (a : ℂ)) (𝓝 a) := by
    simpa only [ContinuousAt, ofComplex_apply] using
      (UpperHalfPlane.contMDiffAt_ofComplex (n := ω) a.im_pos).continuousAt
  exact hfg.comp_tendsto hc

/-- A real scalar cannot be an upper-half-plane value; hence a
homogeneous fixed-point relation with such a scalar forces a zero. -/
theorem homogeneous_value_eq_zero_of_real_multiplier {t : ℍ} {v c : ℂ}
    (hc : c.im = 0) (hv : v * (t : ℂ) = c * v) : v = 0 := by
  have hzero : v * ((t : ℂ) - c) = 0 := by linear_combination hv
  apply (mul_eq_zero.mp hzero).resolve_right
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im, hc, sub_zero, Complex.zero_im] at hi
  exact t.im_ne_zero hi

/-- The first homogeneous law need hold only on a neighbourhood of the
actual order-three centre in order to force its central value to vanish. -/
theorem homogeneous_centerOne_eq_zero_germ {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hν₁ : (fun z : ℍ => ν (Triangle.generatorOneSL • z)) =ᶠ[𝓝 Triangle.centerOne]
      (fun z => -ν z / (τ z : ℂ))) : ν Triangle.centerOne = 0 := by
  have he := hν₁.self_of_nhds
  dsimp only at he
  rw [Triangle.generatorOne_fix] at he
  apply homogeneous_value_eq_zero_of_real_multiplier (c := (-1 : ℂ)) (by simp)
  simpa only [neg_one_mul] using (eq_div_iff (τ Triangle.centerOne).ne_zero).mp he

/-- The second homogeneous law need hold only as a germ at the actual
order-four centre in order to force its central value to vanish. -/
theorem homogeneous_centerTwo_eq_zero_germ {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hν₂ : (fun z : ℍ => ν (Triangle.generatorTwoSL • z)) =ᶠ[𝓝 Triangle.centerTwo]
      (fun z => ν z / (τ z : ℂ))) : ν Triangle.centerTwo = 0 := by
  have he := hν₂.self_of_nhds
  dsimp only at he
  rw [Triangle.generatorTwo_fix] at he
  apply homogeneous_value_eq_zero_of_real_multiplier (c := (1 : ℂ)) (by simp)
  simpa only [one_mul] using (eq_div_iff (τ Triangle.centerTwo).ne_zero).mp he

/-- Differentiate a genuine germ-local product law at an actual fixed
point.  Both functions need be holomorphic only at that point. -/
theorem homogeneous_fixed_derivative_identity_germ {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (g : SL(2, ℝ)) (a : ℍ) (c : ℂ)
    (hτ : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω τ a)
    (hν : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ν a)
    (hfix : g • a = a) (hzero : ν a = 0)
    (hlaw : (fun z : ℍ => ν (g • z) * (τ z : ℂ)) =ᶠ[𝓝 a] (fun z => c * ν z)) :
    (deriv (ν ∘ ofComplex) (a : ℂ) * Triangle.slMultiplier g a) * (τ a : ℂ) =
      c * deriv (ν ∘ ofComplex) (a : ℂ) := by
  let V : ℂ → ℂ := ν ∘ ofComplex
  let T : ℂ → ℂ := fun z => (τ (ofComplex z) : ℂ)
  let A : ℂ → ℂ := fun z => ((g • ofComplex z : ℍ) : ℂ)
  have hV := (scalar_analyticAt_of_contMDiffAt hν).differentiableAt.hasDerivAt
  have hTa := scalar_analyticAt_of_contMDiffAt
    ((UpperHalfPlane.contMDiff_coe (τ a)).comp a hτ)
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
      zero_mul, add_zero] using hcomp.mul hT
  have he : (fun z : ℂ => ν (g • ofComplex z) * T z) =ᶠ[𝓝 (a : ℂ)]
      (fun z => c * V z) := eventuallyEq_comp_ofComplex hlaw
  exact (hprod.congr_of_eventuallyEq he.symm).unique (hV.const_mul c)

/-- The first derivative vanishes even for a section given only as a
holomorphic germ satisfying the first homogeneous generator equation. -/
theorem homogeneous_centerOne_deriv_eq_zero_germ {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : TauCovariant τ)
    (hν : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ν Triangle.centerOne)
    (hν₁ : (fun z : ℍ => ν (Triangle.generatorOneSL • z)) =ᶠ[𝓝 Triangle.centerOne]
      (fun z => -ν z / (τ z : ℂ))) :
    deriv (ν ∘ ofComplex) (Triangle.centerOne : ℂ) = 0 := by
  have hzero := homogeneous_centerOne_eq_zero_germ hν₁
  have hprod : (fun z : ℍ => ν (Triangle.generatorOneSL • z) * (τ z : ℂ))
      =ᶠ[𝓝 Triangle.centerOne] (fun z => (-1 : ℂ) * ν z) := by
    filter_upwards [hν₁] with z hz
    rw [hz, div_mul_cancel₀ _ (τ z).ne_zero, neg_one_mul]
  have hd := homogeneous_fixed_derivative_identity_germ Triangle.generatorOneSL
    Triangle.centerOne (-1) (hτ _) hν Triangle.generatorOne_fix hzero hprod
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

/-- The genuine homogeneous germ has analytic order at least two at the
order-three centre, with infinite order allowed. -/
theorem homogeneous_centerOne_order_ge_two_germ {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : TauCovariant τ)
    (hν : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ν Triangle.centerOne)
    (hν₁ : (fun z : ℍ => ν (Triangle.generatorOneSL • z)) =ᶠ[𝓝 Triangle.centerOne]
      (fun z => -ν z / (τ z : ℂ))) :
    (2 : ℕ∞) ≤ analyticOrderAt (ν ∘ ofComplex) (Triangle.centerOne : ℂ) := by
  rw [show (2 : ℕ∞) = (2 : ℕ) by rfl,
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (scalar_analyticAt_of_contMDiffAt hν)]
  intro k hk
  have hk01 : k = 0 ∨ k = 1 := by omega
  rcases hk01 with rfl | rfl
  · simpa only [iteratedDeriv_zero, Function.comp_apply, ofComplex_apply] using
      homogeneous_centerOne_eq_zero_germ hν₁
  · simpa only [iteratedDeriv_one] using homogeneous_centerOne_deriv_eq_zero_germ hτ hτc hν hν₁

/-- The genuine homogeneous germ has analytic order at least one at the
order-four centre. -/
theorem homogeneous_centerTwo_order_ge_one_germ {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hν : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ν Triangle.centerTwo)
    (hν₂ : (fun z : ℍ => ν (Triangle.generatorTwoSL • z)) =ᶠ[𝓝 Triangle.centerTwo]
      (fun z => ν z / (τ z : ℂ))) :
    (1 : ℕ∞) ≤ analyticOrderAt (ν ∘ ofComplex) (Triangle.centerTwo : ℂ) := by
  rw [show (1 : ℕ∞) = (1 : ℕ) by rfl,
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (scalar_analyticAt_of_contMDiffAt hν)]
  intro k hk
  have hk0 : k = 0 := by omega
  subst k
  simpa only [iteratedDeriv_zero, Function.comp_apply, ofComplex_apply] using
    homogeneous_centerTwo_eq_zero_germ hν₂

/-- Local division at the first centre requires only holomorphic germs
of both the numerator and the exact-double-zero denominator. -/
theorem exists_division_at_centerOne_germ {τ : ℍ → ℍ} {ν f : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : TauCovariant τ)
    (hν : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ν Triangle.centerOne)
    (hν₁ : (fun z : ℍ => ν (Triangle.generatorOneSL • z)) =ᶠ[𝓝 Triangle.centerOne]
      (fun z => -ν z / (τ z : ℂ)))
    (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f Triangle.centerOne)
    (hforder : analyticOrderAt (f ∘ ofComplex) (Triangle.centerOne : ℂ) = 2) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h (Triangle.centerOne : ℂ) ∧
      (ν ∘ ofComplex) =ᶠ[𝓝 (Triangle.centerOne : ℂ)]
        fun z => (f ∘ ofComplex) z * h z :=
  exists_analytic_factor_of_order_le (scalar_analyticAt_of_contMDiffAt hν)
    (scalar_analyticAt_of_contMDiffAt hf) (n := 2) hforder
    (homogeneous_centerOne_order_ge_two_germ hτ hτc hν hν₁)

/-- Local division at the second centre requires only holomorphic germs
of both the numerator and the exact-simple-zero denominator. -/
theorem exists_division_at_centerTwo_germ {τ : ℍ → ℍ} {ν f : ℍ → ℂ}
    (hν : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ν Triangle.centerTwo)
    (hν₂ : (fun z : ℍ => ν (Triangle.generatorTwoSL • z)) =ᶠ[𝓝 Triangle.centerTwo]
      (fun z => ν z / (τ z : ℂ)))
    (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f Triangle.centerTwo)
    (hforder : analyticOrderAt (f ∘ ofComplex) (Triangle.centerTwo : ℂ) = 1) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h (Triangle.centerTwo : ℂ) ∧
      (ν ∘ ofComplex) =ᶠ[𝓝 (Triangle.centerTwo : ℂ)]
        fun z => (f ∘ ofComplex) z * h z :=
  exists_analytic_factor_of_order_le (scalar_analyticAt_of_contMDiffAt hν)
    (scalar_analyticAt_of_contMDiffAt hf) (n := 1) hforder
    (homogeneous_centerTwo_order_ge_one_germ hν hν₂)

/-- Turn an ambient analytic factor germ into a native holomorphic
factor germ on the actual upper half-plane. -/
theorem exists_native_factor_of_ambient_factor {ν f : ℍ → ℂ} {a : ℍ}
    (hfactor : ∃ h : ℂ → ℂ, AnalyticAt ℂ h (a : ℂ) ∧
      (ν ∘ ofComplex) =ᶠ[𝓝 (a : ℂ)] fun z => (f ∘ ofComplex) z * h z) :
    ∃ h : ℍ → ℂ, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω h a ∧
      ν =ᶠ[𝓝 a] fun z => f z * h z := by
  obtain ⟨h, hh, he⟩ := hfactor
  refine ⟨fun z => h z, ?_, ?_⟩
  · exact hh.contDiffAt.contMDiffAt.comp a (UpperHalfPlane.contMDiff_coe a)
  · simpa only [Function.comp_def, ofComplex_apply] using
      he.comp_tendsto (UpperHalfPlane.continuous_coe.continuousAt (x := a))

/-- Native holomorphic-germ division at the first actual centre. -/
theorem exists_native_division_at_centerOne_germ {τ : ℍ → ℍ} {ν f : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : TauCovariant τ)
    (hν : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ν Triangle.centerOne)
    (hν₁ : (fun z : ℍ => ν (Triangle.generatorOneSL • z)) =ᶠ[𝓝 Triangle.centerOne]
      (fun z => -ν z / (τ z : ℂ)))
    (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f Triangle.centerOne)
    (hforder : analyticOrderAt (f ∘ ofComplex) (Triangle.centerOne : ℂ) = 2) :
    ∃ h : ℍ → ℂ, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω h Triangle.centerOne ∧
      ν =ᶠ[𝓝 Triangle.centerOne] fun z => f z * h z :=
  exists_native_factor_of_ambient_factor
    (exists_division_at_centerOne_germ hτ hτc hν hν₁ hf hforder)

/-- Native holomorphic-germ division at the second actual centre. -/
theorem exists_native_division_at_centerTwo_germ {τ : ℍ → ℍ} {ν f : ℍ → ℂ}
    (hν : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ν Triangle.centerTwo)
    (hν₂ : (fun z : ℍ => ν (Triangle.generatorTwoSL • z)) =ᶠ[𝓝 Triangle.centerTwo]
      (fun z => ν z / (τ z : ℂ)))
    (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f Triangle.centerTwo)
    (hforder : analyticOrderAt (f ∘ ofComplex) (Triangle.centerTwo : ℂ) = 1) :
    ∃ h : ℍ → ℂ, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω h Triangle.centerTwo ∧
      ν =ᶠ[𝓝 Triangle.centerTwo] fun z => f z * h z :=
  exists_native_factor_of_ambient_factor
    (exists_division_at_centerTwo_germ hν hν₂ hf hforder)

end Wikipedia.HopfProblem.SpecialPeriods.MuGenerator
