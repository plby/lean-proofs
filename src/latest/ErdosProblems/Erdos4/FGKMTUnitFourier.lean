import ErdosProblems.Erdos4.FGKMTRationalFourierDecay
import ErdosProblems.Erdos4.FGKMTProjectionComparison
import ErdosProblems.Erdos4.UnitFourier

/-! Exact uniform-unit normalization of the rational sieve transform. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open LocalOrthogonality RestrictedProductNorm LocalCharacterMatrix RestrictedTensor

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}
    (ell : P → ℕ) [∀ p, Fact (ell p).Prime]

noncomputable def rationalUnitFourier (b : ℝ) (R : ℕ)
    (h : ∀ p, Fin k → ZMod (ell p)) (j : Fin k)
    (χ : ∀ p, DirichletCharacter ℂ (ell p)) : ℂ :=
  (Fintype.card (∀ p, (ZMod (ell p))ˣ) : ℂ)⁻¹ *
    ∑ u : ∀ p, (ZMod (ell p))ˣ,
      (∏ p, star (χ p (u p : ZMod (ell p)))) *
        TensorMoments.amplitude (fun a => (rationalCoefficient b R ell a : ℂ))
          (fun p a t => (extendedBasis (ell p : ℝ) a
            (RootStates.rootState (Finset.univ.erase j) (AnchorRoots.anchorRoot (h p) j) t) : ℂ)) u ^ 2

theorem rational_raw_eq_density_mul_unit (b : ℝ) (R : ℕ)
    (h : ∀ p, Fin k → ZMod (ell p)) (j : Fin k)
    (χ : ∀ p, DirichletCharacter ℂ (ell p)) :
    rationalRawFourier ell b R h j χ = (sieveWindowDensity ell : ℂ) * rationalUnitFourier ell b R h j χ := by
  have hd : (sieveWindowDensity ell : ℂ) / (Fintype.card (∀ p, (ZMod (ell p))ˣ) : ℂ) =
      ∏ p, (ell p : ℂ)⁻¹ := UnitFourier.density_div_card ell
  unfold rationalRawFourier rationalUnitFourier
  rw [← mul_assoc, ← div_eq_mul_inv, hd]
  simp only [Finset.prod_mul_distrib, Finset.mul_sum, mul_assoc]

theorem rational_unit_eq_raw_div_density (b : ℝ) (R : ℕ)
    (h : ∀ p, Fin k → ZMod (ell p)) (j : Fin k)
    (χ : ∀ p, DirichletCharacter ℂ (ell p)) :
    rationalUnitFourier ell b R h j χ = rationalRawFourier ell b R h j χ / sieveWindowDensity ell := by
  have hd : (sieveWindowDensity ell : ℂ) ≠ 0 := by
    exact_mod_cast (UnitFourier.unitDensity_pos ell).ne'
  rw [rational_raw_eq_density_mul_unit, mul_div_cancel_left₀ _ hd]

theorem rational_unit_principal_eq_trueForm (b : ℝ) (R : ℕ)
    (h : ∀ p, Fin k → ZMod (ell p)) (hh : ∀ p, Function.Injective (h p)) (j : Fin k) :
    rationalUnitFourier ell b R h j (fun _ => 1) =
      (rationalTrueForm b R ell j : ℂ) / sieveWindowDensity ell := by
  rw [rational_unit_eq_raw_div_density, rationalRawFourier_eq_tensor]
  unfold rationalTrueForm
  rw [restrictedForm_productMask_eq]
  congr 1
  unfold ConductorSupport.tensorForm
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  apply Finset.prod_congr rfl
  intro p _
  exact principal_characterMatrix_eq_mean (h p) (hh p) j (a p) (c p)

theorem norm_rationalUnitFourier_le {b : ℝ} (hb : 0 ≤ b) (R : ℕ)
    (hell : ∀ p, k + 2 ≤ ell p)
    (h : ∀ p, Fin k → ZMod (ell p)) (hh : ∀ p, Function.Injective (h p)) (j : Fin k)
    (χ : ∀ p, DirichletCharacter ℂ (ell p)) (J : Finset P)
    (hχ : ∀ p ∈ J, χ p ≠ 1) (houtside : ∀ p, p ∉ J → χ p = 1) :
    ‖rationalUnitFourier ell b R h j χ‖ ≤
      (energy (rationalCoefficient (k := k) b R ell) / sieveWindowDensity ell) *
        ∏ p : J, 20 * (k : ℝ) ^ 3 / ell p := by
  have hd : 0 < sieveWindowDensity ell := UnitFourier.unitDensity_pos ell
  rw [rational_unit_eq_raw_div_density, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  have hh' := div_le_div_of_nonneg_right
    (norm_rationalRawFourier_le ell hb R hell h hh j χ J hχ houtside) hd.le
  exact hh'.trans_eq (by ring)

theorem norm_rationalUnitFourier_le_small {b : ℝ} (hb : 0 ≤ b) (R : ℕ)
    (hell : ∀ p, k + 2 ≤ ell p) {δ : ℝ} (hδ : δ ≤ 1)
    (hlocal : ∀ p, 20 * (k : ℝ) ^ 3 ≤ δ * ell p)
    (h : ∀ p, Fin k → ZMod (ell p)) (hh : ∀ p, Function.Injective (h p)) (j : Fin k)
    (χ : ∀ p, DirichletCharacter ℂ (ell p)) (J : Finset P) (hJ : J.Nonempty)
    (hχ : ∀ p ∈ J, χ p ≠ 1) (houtside : ∀ p, p ∉ J → χ p = 1) :
    ‖rationalUnitFourier ell b R h j χ‖ ≤
      (energy (rationalCoefficient (k := k) b R ell) / sieveWindowDensity ell) * δ := by
  have hd : 0 < sieveWindowDensity ell := UnitFourier.unitDensity_pos ell
  rw [rational_unit_eq_raw_div_density, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  have hh' := div_le_div_of_nonneg_right
    (norm_rationalRawFourier_le_small ell hb R hell hδ hlocal h hh j χ J hJ hχ houtside) hd.le
  exact hh'.trans_eq (by ring)

theorem rationalUnitFourier_eq_zero_of_large_conductor (b : ℝ) (R : ℕ)
    (h : ∀ p, Fin k → ZMod (ell p)) (j : Fin k)
    (χ : ∀ p, DirichletCharacter ℂ (ell p)) (J : Finset P)
    (hχ : ∀ p ∈ J, χ p ≠ 1) (hlarge : R ^ 2 < ∏ p ∈ J, ell p) :
    rationalUnitFourier ell b R h j χ = 0 := by
  rw [rational_unit_eq_raw_div_density,
    rationalRawFourier_eq_zero_of_large_conductor ell b R h j χ J hχ hlarge, zero_div]

end Erdos4.FGKMT
