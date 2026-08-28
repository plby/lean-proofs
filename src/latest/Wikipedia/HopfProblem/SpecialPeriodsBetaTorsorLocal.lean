import Wikipedia.HopfProblem.SpecialPeriodsCocycles
import Wikipedia.HopfProblem.SpecialPeriodsGlobalTauGroupAction

/-!
# The actual local beta cocycle and elliptic primitives

The two inhomogeneous terms are holomorphic functions on the actual upper
half-plane.  The tau and mu generator equations imply their finite cyclic
relations and their product relation.  The explicit finite-average primitives
solve the corresponding individual generator equations; no global beta
function or all-word cocycle is assumed.
-/

noncomputable section

open Set UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor

/-- The order-three generator's actual inhomogeneous beta term. -/
def phiOne (τ : ℍ → ℍ) (μ : ℍ → ℂ) (z : ℍ) : ℂ :=
  2 - 6 * (1 - μ z) ^ 2 / (τ z : ℂ)

/-- The order-four generator's actual inhomogeneous beta term. -/
def phiTwo (τ : ℍ → ℍ) (μ : ℍ → ℂ) (z : ℍ) : ℂ :=
  -3 - 6 * μ z ^ 2 / (τ z : ℂ)

/-- The explicit finite-average primitive for the order-three generator. -/
def primitiveOne (τ : ℍ → ℍ) (μ : ℍ → ℂ) (z : ℍ) : ℂ :=
  betaPrimitiveThree (τ z) (μ z)

/-- The explicit finite-average primitive for the order-four generator. -/
def primitiveTwo (τ : ℍ → ℍ) (μ : ℍ → ℂ) (z : ℍ) : ℂ :=
  betaPrimitiveFour (τ z) (μ z)

private theorem tau_sub_one_ne_zero (τ : ℍ → ℍ) (z : ℍ) :
    (τ z : ℂ) - 1 ≠ 0 :=
  sub_ne_zero.mpr (by simpa only [Complex.ofReal_one] using (τ z).ne_ofReal 1)

theorem phiOne_holomorphic {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hμ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (phiOne τ μ) := by
  have ht : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => (τ z : ℂ)) :=
    UpperHalfPlane.contMDiff_coe.comp hτ
  exact contMDiff_const.sub ((contMDiff_const.mul ((contMDiff_const.sub hμ).pow 2)).div₀
    ht (fun z => (τ z).ne_zero))

theorem phiTwo_holomorphic {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hμ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (phiTwo τ μ) := by
  have ht : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => (τ z : ℂ)) :=
    UpperHalfPlane.contMDiff_coe.comp hτ
  exact contMDiff_const.sub ((contMDiff_const.mul (hμ.pow 2)).div₀
    ht (fun z => (τ z).ne_zero))

theorem primitiveOne_holomorphic {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hμ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (primitiveOne τ μ) := by
  have ht : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => (τ z : ℂ)) :=
    UpperHalfPlane.contMDiff_coe.comp hτ
  have ha : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun z => 6 * ((τ z : ℂ) - 1 + μ z) ^ 2 /
        ((τ z : ℂ) * ((τ z : ℂ) - 1))) :=
    (contMDiff_const.mul (((ht.sub contMDiff_const).add hμ).pow 2)).div₀
      (ht.mul (ht.sub contMDiff_const))
      (fun z => mul_ne_zero (τ z).ne_zero (tau_sub_one_ne_zero τ z))
  have hb : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun z => 6 * μ z ^ 2 / ((τ z : ℂ) - 1)) :=
    (contMDiff_const.mul (hμ.pow 2)).div₀ (ht.sub contMDiff_const)
      (tau_sub_one_ne_zero τ)
  exact ((contMDiff_const.sub ha).add
    (contMDiff_const.mul (contMDiff_const.add hb))).div_const 3

theorem primitiveTwo_holomorphic {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hμ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (primitiveTwo τ μ) := by
  have ht : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => (τ z : ℂ)) :=
    UpperHalfPlane.contMDiff_coe.comp hτ
  have ha : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => 6 * ((τ z : ℂ) + μ z) ^ 2 / (τ z : ℂ)) :=
    (contMDiff_const.mul ((ht.add hμ).pow 2)).div₀ ht (fun z => (τ z).ne_zero)
  have hb : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun z => 6 * (1 - (τ z : ℂ) - μ z) ^ 2 / (τ z : ℂ)) :=
    (contMDiff_const.mul (((contMDiff_const.sub ht).sub hμ).pow 2)).div₀
      ht (fun z => (τ z).ne_zero)
  have hc : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => 6 * (1 - μ z) ^ 2 / (τ z : ℂ)) :=
    (contMDiff_const.mul ((contMDiff_const.sub hμ).pow 2)).div₀ ht (fun z => (τ z).ne_zero)
  exact (((contMDiff_const.add ha).add
    (contMDiff_const.mul (contMDiff_const.sub hb))).add
    (contMDiff_const.mul (contMDiff_const.add hc))).div_const 4

/-- The first primitive solves the actual first generator equation. -/
theorem primitiveOne_difference {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : TauCovariant τ)
    (hμ : ∀ z : ℍ, μ (Triangle.generatorOneSL • z) = (1 - μ z) / (τ z : ℂ))
    (z : ℍ) :
    primitiveOne τ μ (Triangle.generatorOneSL • z) - primitiveOne τ μ z = phiOne τ μ z := by
  simp only [primitiveOne, phiOne, hτ.1, hμ]
  exact betaPrimitiveThree_difference (τ z) (μ z) (τ z).ne_zero (tau_sub_one_ne_zero τ z)

/-- The second primitive solves the actual second generator equation. -/
theorem primitiveTwo_difference {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : TauCovariant τ)
    (hμ : ∀ z : ℍ, μ (Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ))
    (z : ℍ) :
    primitiveTwo τ μ (Triangle.generatorTwoSL • z) - primitiveTwo τ μ z = phiTwo τ μ z := by
  simp only [primitiveTwo, phiTwo, hτ.2, hμ]
  exact betaPrimitiveFour_difference (τ z) (μ z) (τ z).ne_zero

private theorem generatorOne_triple (z : ℍ) :
    Triangle.generatorOneSL • (Triangle.generatorOneSL • (Triangle.generatorOneSL • z)) = z := by
  have he := congrArg (fun g : Equiv.Perm ℍ => g z) Triangle.generatorOnePerm_cube
  simpa only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply,
    Equiv.Perm.one_apply, Triangle.generatorOnePerm, Triangle.realSLPermutation_apply] using he

private theorem generatorTwo_quadruple (z : ℍ) :
    Triangle.generatorTwoSL • (Triangle.generatorTwoSL •
      (Triangle.generatorTwoSL • (Triangle.generatorTwoSL • z))) = z := by
  have he := congrArg (fun g : Equiv.Perm ℍ => g z) Triangle.generatorTwoPerm_fourth
  simpa only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply,
    Equiv.Perm.one_apply, Triangle.generatorTwoPerm, Triangle.realSLPermutation_apply] using he

/-- The first cyclic obstruction vanishes on the actual order-three orbit. -/
theorem phiOne_cyclic_sum {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : TauCovariant τ)
    (hμ : ∀ z : ℍ, μ (Triangle.generatorOneSL • z) = (1 - μ z) / (τ z : ℂ))
    (z : ℍ) :
    phiOne τ μ z + phiOne τ μ (Triangle.generatorOneSL • z) +
      phiOne τ μ (Triangle.generatorOneSL • (Triangle.generatorOneSL • z)) = 0 := by
  have h₀ := primitiveOne_difference hτ hμ z
  have h₁ := primitiveOne_difference hτ hμ (Triangle.generatorOneSL • z)
  have h₂ := primitiveOne_difference hτ hμ
    (Triangle.generatorOneSL • (Triangle.generatorOneSL • z))
  rw [generatorOne_triple] at h₂
  linear_combination -h₀ - h₁ - h₂

/-- The second cyclic obstruction vanishes on the actual order-four orbit. -/
theorem phiTwo_cyclic_sum {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : TauCovariant τ)
    (hμ : ∀ z : ℍ, μ (Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ))
    (z : ℍ) :
    phiTwo τ μ z + phiTwo τ μ (Triangle.generatorTwoSL • z) +
      phiTwo τ μ (Triangle.generatorTwoSL • (Triangle.generatorTwoSL • z)) +
      phiTwo τ μ (Triangle.generatorTwoSL •
        (Triangle.generatorTwoSL • (Triangle.generatorTwoSL • z))) = 0 := by
  have h₀ := primitiveTwo_difference hτ hμ z
  have h₁ := primitiveTwo_difference hτ hμ (Triangle.generatorTwoSL • z)
  have h₂ := primitiveTwo_difference hτ hμ
    (Triangle.generatorTwoSL • (Triangle.generatorTwoSL • z))
  have h₃ := primitiveTwo_difference hτ hμ
    (Triangle.generatorTwoSL • (Triangle.generatorTwoSL • (Triangle.generatorTwoSL • z)))
  rw [generatorTwo_quadruple] at h₃
  linear_combination -h₀ - h₁ - h₂ - h₃

/-- Finite-range form of the first cyclic relation for extension to words. -/
theorem phiOne_sum_range {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : TauCovariant τ)
    (hμ : ∀ z : ℍ, μ (Triangle.generatorOneSL • z) = (1 - μ z) / (τ z : ℂ))
    (z : ℍ) :
    (∑ k ∈ Finset.range 3, phiOne τ μ ((Triangle.generatorOnePerm ^ k) z)) = 0 := by
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
    Triangle.generatorOnePerm, Triangle.realSLPermutation_apply] using phiOne_cyclic_sum hτ hμ z

/-- Finite-range form of the second cyclic relation for extension to words. -/
theorem phiTwo_sum_range {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : TauCovariant τ)
    (hμ : ∀ z : ℍ, μ (Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ))
    (z : ℍ) :
    (∑ k ∈ Finset.range 4, phiTwo τ μ ((Triangle.generatorTwoPerm ^ k) z)) = 0 := by
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
    Triangle.generatorTwoPerm, Triangle.realSLPermutation_apply] using phiTwo_cyclic_sum hτ hμ z

/-- The elliptic product has beta increment `-1`, the inverse cusp increment. -/
theorem phi_product_relation {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : TauCovariant τ)
    (hμ : ∀ z : ℍ, μ (Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ))
    (z : ℍ) : phiOne τ μ (Triangle.generatorTwoSL • z) + phiTwo τ μ z = -1 := by
  let p : PeriodPoint := ⟨τ z, μ z, 0⟩
  have hp : SpecialPeriods.phiThree p.step₂ + SpecialPeriods.phiFour p = -1 := by
    rw [phiThree_eq_beta_sub, phiFour_eq_beta_sub, p.step₁_step₂ (τ z).ne_zero]
    simp only
    ring
  simp only [phiOne, phiTwo, hτ.2, hμ]
  exact hp

end Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor
