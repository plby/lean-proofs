import ErdosProblems.Erdos4.FGKMTSmallPrimeMask

/-! Every small-mask Fourier coefficient is bounded by its positive principal mean. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical

variable {p k : ℕ} [Fact p.Prime]

noncomputable def smallMaskFourier (h : Fin k → ZMod p) (j : Fin k)
    (χ : DirichletCharacter ℂ p) : ℂ :=
  (∑ u ∈ smallAnchorGoodStates h j, star (χ (u : ZMod p))) /
    (Fintype.card ((ZMod p)ˣ) : ℂ)

theorem smallMaskFourier_principal (h : Fin k → ZMod p) (j : Fin k) :
    smallMaskFourier h j 1 = (smallAnchoredDensity h j : ℂ) := by
  unfold smallMaskFourier smallAnchoredDensity
  simp only [MulChar.one_apply_coe, star_one, Finset.sum_const, nsmul_eq_mul, mul_one,
    Complex.ofReal_div, Complex.ofReal_natCast]

theorem smallMaskFourier_norm_le (h : Fin k → ZMod p) (j : Fin k)
    (χ : DirichletCharacter ℂ p) : ‖smallMaskFourier h j χ‖ ≤ smallAnchoredDensity h j := by
  unfold smallMaskFourier smallAnchoredDensity
  rw [norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hh := norm_sum_le (smallAnchorGoodStates h j) (fun u => star (χ (u : ZMod p)))
  simpa only [norm_star, χ.unit_norm_eq_one, Finset.sum_const, nsmul_eq_mul, mul_one] using hh

theorem smallMaskFourier_norm_le_density_ratio (h : Fin k → ZMod p) (j : Fin k)
    (χ : DirichletCharacter ℂ p) :
    ‖smallMaskFourier h j χ‖ ≤ smallPresieveDensity h / (((p : ℝ) - 1) / p) := by
  rw [← smallAnchoredDensity_eq h j]
  exact smallMaskFourier_norm_le h j χ

theorem smallPresieveDensity_ge_inv (h : Fin k → ZMod p) (ha : ∃ x, SmallPrimeGood h x) :
    (p : ℝ)⁻¹ ≤ smallPresieveDensity h := by
  obtain ⟨x, hx⟩ := ha
  have hcard : 1 ≤ (smallPrimeGoodStates h).card :=
    Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
  have hcardR : (1 : ℝ) ≤ (smallPrimeGoodStates h).card := by exact_mod_cast hcard
  simpa only [one_div, smallPresieveDensity] using
    div_le_div_of_nonneg_right hcardR (Nat.cast_nonneg p : (0 : ℝ) ≤ p)

end Erdos4.FGKMT
