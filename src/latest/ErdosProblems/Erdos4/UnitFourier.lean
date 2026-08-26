import ErdosProblems.Erdos4.FourierDecay
import Mathlib.Data.Fintype.BigOperators

/-!
# Uniform unit-group normalization

The ordinary Fourier coefficient is the uniform average on the product of
unit groups. It differs from `ProductCharacterMatrix.fourierCoefficient`
by exactly the positive Euler factor `unitDensity`.
-/

open scoped BigOperators

namespace Erdos4.UnitFourier

open LocalOrthogonality DivisorCoefficients RestrictedProductNorm
  ProductCharacterMatrix

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}
    (ell : P → ℕ) [∀ p, Fact (ell p).Prime]

noncomputable def unitDensity : ℝ := ∏ p, ((ell p : ℝ) - 1) / ell p

omit [DecidableEq P] in
theorem unitDensity_pos : 0 < unitDensity ell := by
  apply Finset.prod_pos
  intro p _hp
  have hp : (1 : ℝ) < ell p := by exact_mod_cast (Fact.out : (ell p).Prime).one_lt
  exact div_pos (sub_pos.mpr hp) (by linarith)

omit [DecidableEq P] in
theorem unitDensity_eq_product : unitDensity ell = ∏ p, (1 - 1 / (ell p : ℝ)) := by
  apply Finset.prod_congr rfl
  intro p _hp
  have hp : (ell p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : (ell p).Prime).ne_zero
  field_simp

theorem card_unit_product :
    (Fintype.card (∀ p, (ZMod (ell p))ˣ) : ℂ) = ∏ p, ((ell p : ℂ) - 1) := by
  rw [Fintype.card_pi, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro p _hp
  rw [ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out : (ell p).Prime),
    Nat.cast_sub (Fact.out : (ell p).Prime).one_le, Nat.cast_one]

theorem density_div_card :
    (unitDensity ell : ℂ) / Fintype.card (∀ p, (ZMod (ell p))ˣ) =
      ∏ p, (ell p : ℂ)⁻¹ := by
  rw [card_unit_product, unitDensity]
  push_cast
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p _hp
  have hp : (ell p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : (ell p).Prime).ne_zero
  have hp1 : (ell p : ℂ) - 1 ≠ 0 := by
    have hn := (Fact.out : (ell p).Prime).ne_one
    exact sub_ne_zero.mpr (by exact_mod_cast hn)
  field_simp

noncomputable def coefficient (m : ℝ) (R : ℕ)
    (h : ∀ p, Fin k → ZMod (ell p)) (j : Fin k)
    (chi : ∀ p, DirichletCharacter ℂ (ell p)) : ℂ :=
  (Fintype.card (∀ p, (ZMod (ell p))ˣ) : ℂ)⁻¹ *
    ∑ u : ∀ p, (ZMod (ell p))ˣ,
      (∏ p, star (chi p (u p : ZMod (ell p)))) *
        TensorMoments.amplitude (fun a => (DivisorCoefficients.coefficient m R ell a : ℂ))
          (fun p a t => (extendedBasis (ell p : ℝ) a
            (RootStates.rootState (Finset.univ.erase j) (AnchorRoots.anchorRoot (h p) j) t) : ℂ)) u ^ 2

theorem raw_eq_density_mul_coefficient (m : ℝ) (R : ℕ)
    (h : ∀ p, Fin k → ZMod (ell p)) (j : Fin k)
    (chi : ∀ p, DirichletCharacter ℂ (ell p)) :
    fourierCoefficient ell m R h j chi = (unitDensity ell : ℂ) * coefficient ell m R h j chi := by
  unfold fourierCoefficient coefficient
  rw [← mul_assoc, ← div_eq_mul_inv, density_div_card]
  simp only [Finset.prod_mul_distrib, Finset.mul_sum, mul_assoc]

theorem coefficient_eq_raw_div_density (m : ℝ) (R : ℕ)
    (h : ∀ p, Fin k → ZMod (ell p)) (j : Fin k)
    (chi : ∀ p, DirichletCharacter ℂ (ell p)) :
    coefficient ell m R h j chi = fourierCoefficient ell m R h j chi / unitDensity ell := by
  have hd : (unitDensity ell : ℂ) ≠ 0 := by exact_mod_cast (unitDensity_pos ell).ne'
  rw [raw_eq_density_mul_coefficient, mul_div_cancel_left₀ _ hd]

/-- The principal coefficient is the exact restricted product norm divided
by the Euler density. It does not depend on the admissible shifts. -/
theorem principal_coefficient_eq_restrictedForm (m : ℝ) (R : ℕ)
    (h : ∀ p, Fin k → ZMod (ell p)) (hh : ∀ p, Function.Injective (h p)) (j : Fin k) :
    coefficient ell m R h j (fun _ => 1) =
      (restrictedForm (fun p => (ell p : ℝ))
        (fun s => ∏ p, LocalCharacterMatrix.deletionMask j (s p))
        (DivisorCoefficients.coefficient m R ell)
        (DivisorCoefficients.coefficient m R ell) : ℂ) / unitDensity ell := by
  rw [coefficient_eq_raw_div_density, fourierCoefficient_eq_tensor,
    RestrictedTensor.restrictedForm_productMask_eq]
  congr 1
  unfold ConductorSupport.tensorForm
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro b _hb
  congr 1
  apply Finset.prod_congr rfl
  intro p _hp
  exact LocalCharacterMatrix.principal_characterMatrix_eq_mean (h p) (hh p) j (a p) (b p)

/-- The exact-energy Fourier bound with the genuine uniform normalization. -/
theorem norm_coefficient_le {m : ℝ} (hm : 1 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (hell : ∀ p, k + 2 ≤ ell p)
    (h : ∀ p, Fin k → ZMod (ell p)) (hh : ∀ p, Function.Injective (h p)) (j : Fin k)
    (chi : ∀ p, DirichletCharacter ℂ (ell p)) (J : Finset P)
    (hchi : ∀ p ∈ J, chi p ≠ 1) (houtside : ∀ p, p ∉ J → chi p = 1) :
    ‖coefficient ell m R h j chi‖ ≤
      (energy (DivisorCoefficients.coefficient (k := k) m R ell) / unitDensity ell) *
        ∏ p : J, 20 * (k : ℝ) ^ 3 / ell p := by
  rw [coefficient_eq_raw_div_density, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (unitDensity_pos ell)]
  have hh' := div_le_div_of_nonneg_right
    (FourierDecay.norm_fourierCoefficient_le ell hm hR hell h hh j chi J hchi houtside)
    (unitDensity_pos ell).le
  exact hh'.trans_eq (by ring)

theorem coefficient_eq_zero_of_large_conductor (m : ℝ) (R : ℕ)
    (h : ∀ p, Fin k → ZMod (ell p)) (hh : ∀ p, Function.Injective (h p)) (j : Fin k)
    (chi : ∀ p, DirichletCharacter ℂ (ell p)) (J : Finset P)
    (hchi : ∀ p ∈ J, chi p ≠ 1) (hlarge : R ^ 2 < ∏ p ∈ J, ell p) :
    coefficient ell m R h j chi = 0 := by
  rw [coefficient_eq_raw_div_density,
    ProductCharacterMatrix.fourierCoefficient_eq_zero_of_large_conductor ell m R h hh j chi J hchi hlarge,
    zero_div]

end Erdos4.UnitFourier
