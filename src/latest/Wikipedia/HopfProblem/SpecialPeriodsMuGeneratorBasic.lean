import Wikipedia.HopfProblem.AnalyticRootCoverUpperHalfPlane
import Wikipedia.HopfProblem.SpecialPeriodsModularGermLiftNativeOrders

/-!
# The actual Eisenstein-series generator for the homogeneous μ-law

For a supplied holomorphic map `τ : ℍ → ℍ`, finite even order at every
zero of the actual pullback `E₆ ∘ τ` constructs a global holomorphic square
root.  Multiplying this root by `E₄² / Δ` gives the source's function `F`.
The discriminant is Mathlib's genuine nowhere-zero modular discriminant.

No existence of the global special `τ`, or classification of its elliptic
fibres, is assumed as a theorem here.  The precise zero criterion is given
in terms of the actual Eisenstein pullbacks and the modular function.
-/

noncomputable section

open Set Filter UpperHalfPlane ModularForm ModularGroup
open scoped Topology Manifold ContDiff MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods.MuGenerator

/-- The genuine pullback has finite even order at each of its zeros. -/
def FiniteEvenZeros (τ : ℍ → ℍ) : Prop :=
  ∀ a : ℍ, E₆ (τ a) = 0 → ∃ n : ℕ,
    analyticOrderAt (fun z : ℂ => E₆ (τ (ofComplex z))) (a : ℂ) = (2 * n : ℕ)

/-- The even-zero condition follows from an actual modular equation and
orders divisible by four at the source's `1728`-points. -/
theorem finiteEvenZeros_of_modular_equation {τ : ℍ → ℍ} {J : ℍ → ℂ}
    (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ)
    (hJ : ∀ a : ℍ, modularJ (τ a) = J a)
    (hsource : ∀ a : ℍ, J a = 1728 → ∃ k : ℕ,
      analyticOrderAt (fun z : ℂ => J (ofComplex z) - 1728) (a : ℂ) = (4 * k : ℕ)) :
    FiniteEvenZeros τ :=
  ModularGermLift.native_E₆_finite_even_zeros hτ hJ hsource

/-- A global holomorphic square root of the actual `E₆` pullback. -/
structure Root (τ : ℍ → ℍ) where
  toFun : ℍ → ℂ
  holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω toFun
  square : ∀ a : ℍ, toFun a ^ 2 = E₆ (τ a)

instance {τ : ℍ → ℍ} : CoeFun (Root τ) (fun _ => ℍ → ℂ) := ⟨Root.toFun⟩

/-- The actual analytic-root covering constructs such a root on `ℍ`;
zeros are retained rather than deleted from the domain. -/
theorem nonempty_root {τ : ℍ → ℍ}
    (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ) (hzero : FiniteEvenZeros τ) :
    Nonempty (Root τ) := by
  obtain ⟨r, hr, hrsq, _⟩ :=
    AnalyticRootCover.exists_holomorphic_square_root_upperHalfPlane
      (fun a => E₆ (τ a)) (E₆.holo'.comp hτ) hzero
  exact ⟨⟨r, hr, hrsq⟩⟩

/-- A chosen root, whose existence has just been proved. -/
def root (τ : ℍ → ℍ) (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ)
    (hzero : FiniteEvenZeros τ) : Root τ :=
  Classical.choice (nonempty_root hτ hzero)

/-- A genuine modular form is analytic as a manifold map on `ℍ`. -/
theorem modularForm_holomorphic {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f := by
  intro a
  exact UpperHalfPlane.contMDiffAt_iff.mpr (modularForm_analyticAt f a).contDiffAt

namespace Root

variable {τ : ℍ → ℍ} (r : Root τ)

theorem analyticAt (a : ℍ) :
    AnalyticAt ℂ (r ∘ ofComplex) (a : ℂ) :=
  (UpperHalfPlane.contMDiffAt_iff.mp (r.holomorphic a)).analyticAt

@[simp] theorem eq_zero_iff (a : ℍ) : r a = 0 ↔ E₆ (τ a) = 0 := by
  rw [← r.square a]
  exact (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).symm

/-- Every root, not only the chosen one, has exactly half the finite even order. -/
theorem order_of_square_order (a : ℍ) (n : ℕ)
    (horder : analyticOrderAt (fun z : ℂ => E₆ (τ (ofComplex z))) (a : ℂ) =
      (2 * n : ℕ)) :
    analyticOrderAt (r ∘ ofComplex) (a : ℂ) = n := by
  apply AnalyticRootCover.square_root_order (r.analyticAt a) _ horder
  filter_upwards with z
  exact r.square (ofComplex z)

/-- The exact function from Lemma 3.10, using the genuine modular forms. -/
def generator : ℍ → ℂ :=
  fun a => E₄ (τ a) ^ 2 * r a / discriminant (τ a)

theorem generator_holomorphic (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω r.generator := by
  have h4 : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun a => E₄ (τ a)) :=
    (modularForm_holomorphic E₄).comp hτ
  have hD : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun a => discriminant (τ a)) :=
    (modularForm_holomorphic (CuspForm.discriminant : ModularForm 𝒮ℒ 12)).comp hτ
  exact ((h4.pow 2).mul r.holomorphic).div₀ hD (fun a => discriminant_ne_zero (τ a))

/-- The exact zero set, without presuming which triangle orbits map to it. -/
theorem generator_eq_zero_iff (a : ℍ) :
    r.generator a = 0 ↔ E₄ (τ a) = 0 ∨ E₆ (τ a) = 0 := by
  simp only [generator, div_eq_zero_iff, discriminant_ne_zero, or_false,
    mul_eq_zero, pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0), r.eq_zero_iff]

theorem generator_eq_zero_iff_modularJ (a : ℍ) :
    r.generator a = 0 ↔ modularJ (τ a) = 0 ∨ modularJ (τ a) = 1728 := by
  rw [r.generator_eq_zero_iff, modularJ_eq_zero_iff, modularJ_eq_1728_iff]

/-- An actual modular lifting equation transfers the zero criterion to its
source function.  Identification of source fibres is a separate assertion. -/
theorem generator_eq_zero_iff_source {J : ℍ → ℂ}
    (hJ : ∀ a : ℍ, modularJ (τ a) = J a) (a : ℍ) :
    r.generator a = 0 ↔ J a = 0 ∨ J a = 1728 := by
  rw [r.generator_eq_zero_iff_modularJ, hJ a]

theorem generator_square (a : ℍ) :
    r.generator a ^ 2 = E₄ (τ a) ^ 4 * E₆ (τ a) / discriminant (τ a) ^ 2 := by
  simp only [generator, div_pow, mul_pow, ← pow_mul, r.square]

end Root

end Wikipedia.HopfProblem.SpecialPeriods.MuGenerator
