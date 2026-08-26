import ErdosProblems.Erdos520.Equation16Helpers

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory Set
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# Caich's normalized Euler-product energy, on the Parseval side

Caich defines his energy from the vertical `L²` norm of the finite Euler
product.  His Dirichlet-series Parseval identity identifies that norm, up to
the factor `2 * π`, with the inverse-square smooth-sum energy below.  We use
the Parseval-side expression as the Lean definition.  This has two benefits:

* the exact comparison needed in equation (16) is elementary algebra;
* finite-coordinate measurability and integrability are immediate from the
  already formalized smooth Rademacher model.

The theorem `caichNormalizedEnergy_eq_rpow` records the paper's exact
power normalization.
-/

/-- The inverse-square `L²` energy of the smooth Rademacher partial sum. -/
noncomputable def smoothEnergy (omega : Omega) (y : ℕ) : ℝ :=
  ∫ z in Ioi (0 : ℝ), |ΨReal omega z y| ^ 2 / z ^ 2

/-- The integral defining `smoothEnergy` is genuinely integrable.  In
particular, the definition does not use the convention that a non-integrable
Bochner integral evaluates to zero. -/
theorem integrableOn_smoothEnergy_integrand (omega : Omega) (y : ℕ) :
    IntegrableOn (fun z : ℝ ↦ |ΨReal omega z y| ^ 2 / z ^ 2)
      (Ioi (0 : ℝ)) :=
  integrableOn_ΨReal_sq_div_sq omega y

/-- The smooth energy is pointwise nonnegative. -/
theorem smoothEnergy_nonneg (omega : Omega) (y : ℕ) :
    0 ≤ smoothEnergy omega y := by
  unfold smoothEnergy
  exact integral_nonneg fun z ↦ div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The smooth energy only depends on prime coordinates at most `y`. -/
theorem smoothEnergy_eq_of_eq_on_primesBelow
    {omega omega' : Omega} {y : ℕ}
    (h : ∀ p ∈ (y + 1).primesBelow, omega p = omega' p) :
    smoothEnergy omega y = smoothEnergy omega' y := by
  have hΨ (n : ℕ) : Ψ omega n y = Ψ omega' n y := by
    rw [Ψ_eq_sum_squarefreeSmoothSets, Ψ_eq_sum_squarefreeSmoothSets]
    apply Finset.sum_congr rfl
    intro S hS
    unfold freshCharacter
    apply Finset.prod_congr rfl
    intro p hp
    have hpold : p ∈ (y + 1).primesBelow :=
      (mem_squarefreeSmoothSets.mp hS).1 hp
    unfold ε
    rw [h p hpold]
  unfold smoothEnergy
  apply setIntegral_congr_fun measurableSet_Ioi
  intro z _hz
  change |Ψ omega ⌊z⌋₊ y| ^ 2 / z ^ 2 =
    |Ψ omega' ⌊z⌋₊ y| ^ 2 / z ^ 2
  rw [hΨ]

/-- Finite-coordinate strong measurability of the base smooth energy. -/
theorem stronglyMeasurable_smoothEnergy (y : ℕ) :
    StronglyMeasurable[Filtration.piFinset ((y + 1).primesBelow)]
      (fun omega : Omega ↦ smoothEnergy omega y) := by
  classical
  let s : Finset ℕ := (y + 1).primesBelow
  let base : Omega := fun _ ↦ false
  let G : (s → Bool) → ℝ := fun eta ↦
    smoothEnergy (Function.updateFinset base s eta) y
  have hG : StronglyMeasurable G :=
    (measurable_of_finite G).stronglyMeasurable
  have hcomp : StronglyMeasurable[Filtration.piFinset s]
      (fun omega : Omega ↦ G (s.restrict omega)) :=
    hG.comp_measurable (measurable_restrict_piFinset s)
  have heq : (fun omega : Omega ↦ smoothEnergy omega y) =
      fun omega : Omega ↦ G (s.restrict omega) := by
    funext omega
    change smoothEnergy omega y =
      smoothEnergy (Function.updateFinset base s (s.restrict omega)) y
    apply smoothEnergy_eq_of_eq_on_primesBelow
    intro p hp
    change p ∈ s at hp
    simp [Function.updateFinset, hp]
  change StronglyMeasurable[Filtration.piFinset s]
    (fun omega : Omega ↦ smoothEnergy omega y)
  rw [heq]
  exact hcomp

/-- The base smooth energy is integrable under the infinite product law. -/
theorem integrable_smoothEnergy (y : ℕ) :
    Integrable (fun omega : Omega ↦ smoothEnergy omega y) μ :=
  integrable_of_stronglyMeasurable_piFinset
    (stronglyMeasurable_smoothEnergy y)

/-- Caich's normalized Euler-product energy, written using his Parseval
identity.  The factor `2 * π` is present because

`smoothEnergy = (1 / (2 * π)) * verticalEulerProductEnergy`.

The exponential is exactly
`(log y / log y₀) ^ (-1 / ell ^ K)` when the logarithms are positive. -/
noncomputable def caichNormalizedEnergy
    (ell K y₀ y : ℕ) (omega : Omega) : ℝ :=
  (2 * Real.pi) *
    Real.exp
      (-Real.log (Real.log (y : ℝ) / Real.log (y₀ : ℝ)) /
        ((ell : ℝ) ^ K)) *
    (smoothEnergy omega y / Real.log (y : ℝ))

/-- The exponential normalization in `caichNormalizedEnergy` is the exact
real-power normalization appearing in Caich's definition. -/
theorem caichNormalization_eq_rpow
    {ell K y₀ y : ℕ} (hy₀ : 1 < y₀) (hy : 1 < y) :
    Real.exp
        (-Real.log (Real.log (y : ℝ) / Real.log (y₀ : ℝ)) /
          ((ell : ℝ) ^ K)) =
      (Real.log (y : ℝ) / Real.log (y₀ : ℝ)) ^
        (-1 / ((ell : ℝ) ^ K)) := by
  have hlogy₀ : 0 < Real.log (y₀ : ℝ) :=
    Real.log_pos (by exact_mod_cast hy₀)
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast hy)
  have hratio : 0 < Real.log (y : ℝ) / Real.log (y₀ : ℝ) :=
    div_pos hlogy hlogy₀
  rw [Real.rpow_def_of_pos hratio]
  congr 1
  ring

/-- Paper-form expansion of the normalized energy. -/
theorem caichNormalizedEnergy_eq_rpow
    {ell K y₀ y : ℕ} (hy₀ : 1 < y₀) (hy : 1 < y)
    (omega : Omega) :
    caichNormalizedEnergy ell K y₀ y omega =
      (Real.log (y : ℝ) / Real.log (y₀ : ℝ)) ^
          (-1 / ((ell : ℝ) ^ K)) *
        ((2 * Real.pi) * smoothEnergy omega y /
          Real.log (y : ℝ)) := by
  rw [caichNormalizedEnergy, caichNormalization_eq_rpow hy₀ hy]
  ring

/-- Caich's normalized energy is nonnegative. -/
theorem caichNormalizedEnergy_nonneg
    {ell K y₀ y : ℕ} (hy : 1 < y) (omega : Omega) :
    0 ≤ caichNormalizedEnergy ell K y₀ y omega := by
  unfold caichNormalizedEnergy
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast hy)
  exact mul_nonneg
    (mul_nonneg (by positivity) (Real.exp_pos _).le)
    (div_nonneg (smoothEnergy_nonneg omega y) hlogy.le)

/-- The normalized energy is measurable with respect to the prime coordinates
at most its endpoint. -/
theorem stronglyMeasurable_caichNormalizedEnergy
    (ell K y₀ y : ℕ) :
    StronglyMeasurable[Filtration.piFinset ((y + 1).primesBelow)]
      (fun omega : Omega ↦ caichNormalizedEnergy ell K y₀ y omega) := by
  unfold caichNormalizedEnergy
  have hdiv : StronglyMeasurable[Filtration.piFinset ((y + 1).primesBelow)]
      (fun omega : Omega ↦ smoothEnergy omega y / Real.log (y : ℝ)) :=
    (stronglyMeasurable_smoothEnergy y).div stronglyMeasurable_const
  simpa only [mul_assoc] using!
    ((hdiv.const_mul
      (Real.exp
        (-Real.log (Real.log (y : ℝ) / Real.log (y₀ : ℝ)) /
          ((ell : ℝ) ^ K)))).const_mul (2 * Real.pi))

/-- The normalized energy is integrable. -/
theorem integrable_caichNormalizedEnergy
    (ell K y₀ y : ℕ) :
    Integrable (fun omega : Omega ↦
      caichNormalizedEnergy ell K y₀ y omega) μ := by
  unfold caichNormalizedEnergy
  simpa only [mul_assoc] using!
    (((integrable_smoothEnergy y).div_const
      (Real.log (y : ℝ))).const_mul
        (Real.exp
          (-Real.log (Real.log (y : ℝ) / Real.log (y₀ : ℝ)) /
            ((ell : ℝ) ^ K)))).const_mul (2 * Real.pi)

/-- Removing Caich's damping factor recovers the unnormalized Parseval-side
energy exactly. -/
theorem caichEnergy_recovery
    (ell K y₀ y : ℕ) (omega : Omega) :
    Real.exp
        (Real.log (Real.log (y : ℝ) / Real.log (y₀ : ℝ)) /
          ((ell : ℝ) ^ K)) *
        caichNormalizedEnergy ell K y₀ y omega =
      (2 * Real.pi) * smoothEnergy omega y /
        Real.log (y : ℝ) := by
  unfold caichNormalizedEnergy
  calc
    Real.exp
          (Real.log (Real.log (y : ℝ) / Real.log (y₀ : ℝ)) /
            ((ell : ℝ) ^ K)) *
        ((2 * Real.pi) *
          Real.exp
            (-Real.log (Real.log (y : ℝ) / Real.log (y₀ : ℝ)) /
              ((ell : ℝ) ^ K)) *
          (smoothEnergy omega y / Real.log (y : ℝ))) =
        (2 * Real.pi) *
          (Real.exp
              (Real.log (Real.log (y : ℝ) / Real.log (y₀ : ℝ)) /
                ((ell : ℝ) ^ K)) *
            Real.exp
              (-Real.log (Real.log (y : ℝ) / Real.log (y₀ : ℝ)) /
                ((ell : ℝ) ^ K))) *
          (smoothEnergy omega y / Real.log (y : ℝ)) := by ring
    _ = (2 * Real.pi) * smoothEnergy omega y /
          Real.log (y : ℝ) := by
      rw [← Real.exp_add]
      have hcancel :
          Real.log (Real.log (y : ℝ) / Real.log (y₀ : ℝ)) /
                ((ell : ℝ) ^ K) +
              -Real.log (Real.log (y : ℝ) / Real.log (y₀ : ℝ)) /
                ((ell : ℝ) ^ K) = 0 := by ring
      rw [hcancel, Real.exp_zero]
      ring

/-- Exact Parseval-side comparison used by equation (16).  Its only
schedule-dependent input is a uniform bound for the harmless damping
recovery factor. -/
theorem smoothEnergy_div_log_le_caichNormalizedEnergy
    {ell K y₀ a b : ℕ} (ha : 1 < a) (hab : a ≤ b)
    {C : ℝ} (hC :
      Real.exp
          (Real.log (Real.log (a : ℝ) / Real.log (y₀ : ℝ)) /
            ((ell : ℝ) ^ K)) ≤
        (2 * Real.pi) * C)
    (omega : Omega) :
    smoothEnergy omega a / Real.log (b : ℝ) ≤
      C * caichNormalizedEnergy ell K y₀ a omega := by
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast ha)
  have hlogb : 0 < Real.log (b : ℝ) := by
    apply Real.log_pos
    exact_mod_cast lt_of_lt_of_le ha hab
  have hlogab : Real.log (a : ℝ) ≤ Real.log (b : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast (lt_trans Nat.zero_lt_one ha)
    · exact_mod_cast hab
  have hH : 0 ≤ smoothEnergy omega a := smoothEnergy_nonneg omega a
  have hfirst :
      smoothEnergy omega a / Real.log (b : ℝ) ≤
        smoothEnergy omega a / Real.log (a : ℝ) := by
    exact div_le_div_of_nonneg_left hH hloga hlogab
  have hrecovery := caichEnergy_recovery ell K y₀ a omega
  calc
    smoothEnergy omega a / Real.log (b : ℝ) ≤
        smoothEnergy omega a / Real.log (a : ℝ) := hfirst
    _ = (1 / (2 * Real.pi)) *
          (Real.exp
              (Real.log (Real.log (a : ℝ) / Real.log (y₀ : ℝ)) /
                ((ell : ℝ) ^ K)) *
            caichNormalizedEnergy ell K y₀ a omega) := by
      rw [hrecovery]
      have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      field_simp
    _ ≤ C * caichNormalizedEnergy ell K y₀ a omega := by
      have hI : 0 ≤ caichNormalizedEnergy ell K y₀ a omega :=
        caichNormalizedEnergy_nonneg ha omega
      have htwoPi : 0 < 2 * Real.pi := by positivity
      have hgrowth :
          (1 / (2 * Real.pi)) *
              Real.exp
                (Real.log (Real.log (a : ℝ) / Real.log (y₀ : ℝ)) /
                  ((ell : ℝ) ^ K)) ≤ C := by
        calc
          (1 / (2 * Real.pi)) *
              Real.exp
                (Real.log (Real.log (a : ℝ) / Real.log (y₀ : ℝ)) /
                  ((ell : ℝ) ^ K)) =
              Real.exp
                (Real.log (Real.log (a : ℝ) / Real.log (y₀ : ℝ)) /
                  ((ell : ℝ) ^ K)) / (2 * Real.pi) := by ring
          _ ≤ ((2 * Real.pi) * C) / (2 * Real.pi) :=
            div_le_div_of_nonneg_right hC htwoPi.le
          _ = C := by field_simp
      calc
        (1 / (2 * Real.pi)) *
            (Real.exp
                (Real.log (Real.log (a : ℝ) / Real.log (y₀ : ℝ)) /
                  ((ell : ℝ) ^ K)) *
              caichNormalizedEnergy ell K y₀ a omega) =
            ((1 / (2 * Real.pi)) *
              Real.exp
                (Real.log (Real.log (a : ℝ) / Real.log (y₀ : ℝ)) /
                  ((ell : ℝ) ^ K))) *
              caichNormalizedEnergy ell K y₀ a omega := by ring
        _ ≤ C * caichNormalizedEnergy ell K y₀ a omega :=
          mul_le_mul_of_nonneg_right hgrowth hI

end Problem520
end Erdos
