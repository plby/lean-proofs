import ErdosProblems.Erdos4.FGKMTMaskedAverage

/-! Low modes have conductor and family size controlled only by the small-prime modulus. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical FiniteCharacterSupport ProductCharacterEncoding

variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
    (ell₀ : P → ℕ) (ell₁ : Q → ℕ)
    [∀ p, Fact (ell₀ p).Prime] [∀ q, Fact (ell₁ q).Prime]

noncomputable def lowMaskedIndices (M : ℕ) : Finset (smallCharacters (Sum.elim ell₀ ell₁) M) :=
  Finset.univ.filter (fun chi => (fun q => chi.val (.inr q)) = (fun _ => 1))

theorem mem_lowMaskedIndices (M : ℕ) (chi : smallCharacters (Sum.elim ell₀ ell₁) M) :
    chi ∈ lowMaskedIndices ell₀ ell₁ M ↔ (fun q => chi.val (.inr q)) = (fun _ => 1) := by
  simp only [lowMaskedIndices, Finset.mem_filter, Finset.mem_univ, true_and]

theorem low_product_conductor_le
    (chi : ∀ s, DirichletCharacter ℂ (Sum.elim ell₀ ell₁ s))
    (hhigh : (fun q => chi (.inr q)) = (fun _ => 1)) :
    localConductorProduct (Sum.elim ell₀ ell₁) chi ≤ ∏ p, ell₀ p := by
  rw [localConductorProduct_sum]
  have hh : localConductorProduct ell₁ (fun q => chi (.inr q)) = 1 := by
    rw [hhigh]
    unfold localConductorProduct
    apply Finset.prod_eq_one
    intro q hq
    exact False.elim (((mem_support ell₁ (fun _ => 1) q).mp hq) rfl)
  rw [hh, mul_one]
  exact localConductorProduct_le_full ell₀ (fun p => chi (.inl p))

theorem low_primitive_conductor_le
    (chi : ∀ s, DirichletCharacter ℂ (Sum.elim ell₀ ell₁ s))
    (hhigh : (fun q => chi (.inr q)) = (fun _ => 1)) :
    (entry (Sum.elim ell₀ ell₁) chi).1 ≤ ∏ p, ell₀ p :=
  (conductor_le_support (Sum.elim ell₀ ell₁) chi (support (Sum.elim ell₀ ell₁) chi)
    (outside_support (Sum.elim ell₀ ell₁) chi)).trans
      (low_product_conductor_le ell₀ ell₁ chi hhigh)

theorem card_lowMaskedIndices_le (M : ℕ) (hinj : Function.Injective (Sum.elim ell₀ ell₁)) :
    (lowMaskedIndices ell₀ ell₁ M).card ≤ (∏ p, ell₀ p) ^ 2 := by
  let family : lowMaskedIndices ell₀ ell₁ M → PrimitiveCharacterFamily.Entry :=
    fun chi => entry (Sum.elim ell₀ ell₁) chi.val.val
  have hvalid : ∀ chi, PrimitiveCharacterFamily.Valid (family chi) :=
    fun chi => family_valid (Sum.elim ell₀ ell₁) chi.val
  have hfamily : Function.Injective family := by
    intro chi psi heq
    apply Subtype.ext
    exact family_injective (Sum.elim ell₀ ell₁) hinj heq
  have hbound : ∀ chi, (family chi).1 ≤ ∏ p, ell₀ p := by
    intro chi
    exact low_primitive_conductor_le ell₀ ell₁ chi.val.val
      ((mem_lowMaskedIndices ell₀ ell₁ M chi.val).mp chi.property)
  have hh := PrimitiveCharacterFamily.card_family_le_square family hvalid hfamily hbound
  simpa only [Fintype.card_coe] using hh

theorem primeProductValue_norm_le_one
    (chi : ∀ s, DirichletCharacter ℂ (Sum.elim ell₀ ell₁ s)) (n : ℕ) :
    ‖ProductPrimeMeanSquare.value (Sum.elim ell₀ ell₁) chi n‖ ≤ 1 := by
  unfold ProductPrimeMeanSquare.value
  rw [norm_prod]
  exact Finset.prod_le_one (fun s _ => norm_nonneg _)
    (fun s _ => (chi s).norm_le_one _)

theorem low_masked_source_error_le {k : ℕ} (b : ℝ) (R M : ℕ)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q))
    (hinj : Function.Injective (Sum.elim ell₀ ell₁))
    (sources : Finset ℕ) (a : sources → ℂ) (q : ℕ)
    {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hc : ∀ chi, ‖lowMaskedCoefficient ell₀ ell₁ b R M h₀ h₁ chi‖ ≤ K)
    (hs : ∀ chi ∈ lowMaskedIndices ell₀ ell₁ M,
      ‖∑ p : sources, a p * ProductPrimeMeanSquare.value (Sum.elim ell₀ ell₁) chi.val p‖ ≤ ε) :
    ‖ProductPrimeMeanSquare.weightedSourceError (Sum.elim ell₀ ell₁) M
      (lowMaskedCoefficient ell₀ ell₁ b R M h₀ h₁) sources a q‖ ≤
        ((∏ p, ell₀ p : ℕ) : ℝ) ^ 2 * K * ε := by
  let F : smallCharacters (Sum.elim ell₀ ell₁) M → ℂ := fun chi =>
    (lowMaskedCoefficient ell₀ ell₁ b R M h₀ h₁ chi *
      ∑ p : sources, a p * ProductPrimeMeanSquare.value (Sum.elim ell₀ ell₁) chi.val p) *
        star (ProductPrimeMeanSquare.value (Sum.elim ell₀ ell₁) chi.val q)
  have hzero : ∀ chi, chi ∉ lowMaskedIndices ell₀ ell₁ M → F chi = 0 := by
    intro chi hnot
    have hh : (fun q => chi.val (.inr q)) ≠ (fun _ => 1) :=
      fun heq => hnot ((mem_lowMaskedIndices ell₀ ell₁ M chi).mpr heq)
    simp only [F, lowMaskedCoefficient, if_neg hh, zero_mul]
  have hsum : (∑ chi ∈ lowMaskedIndices ell₀ ell₁ M, ‖F chi‖) = ∑ chi, ‖F chi‖ := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro chi _ hnot
    rw [hzero chi hnot, norm_zero]
  have hbound : ∀ chi ∈ lowMaskedIndices ell₀ ell₁ M, ‖F chi‖ ≤ K * ε := by
    intro chi hchi
    change ‖(lowMaskedCoefficient ell₀ ell₁ b R M h₀ h₁ chi *
      ∑ p : sources, a p * ProductPrimeMeanSquare.value (Sum.elim ell₀ ell₁) chi.val p) *
        star (ProductPrimeMeanSquare.value (Sum.elim ell₀ ell₁) chi.val q)‖ ≤ K * ε
    rw [norm_mul, norm_mul, norm_star]
    have hm := mul_le_mul (hc chi) (hs chi hchi) (norm_nonneg _) hK
    exact (mul_le_mul_of_nonneg_left (primeProductValue_norm_le_one ell₀ ell₁ chi.val q)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans (by simpa only [mul_one] using hm)
  calc
    _ = ‖∑ chi, F chi‖ := rfl
    _ ≤ ∑ chi, ‖F chi‖ := norm_sum_le _ _
    _ = ∑ chi ∈ lowMaskedIndices ell₀ ell₁ M, ‖F chi‖ := hsum.symm
    _ ≤ ∑ _chi ∈ lowMaskedIndices ell₀ ell₁ M, K * ε :=
      Finset.sum_le_sum hbound
    _ = ((lowMaskedIndices ell₀ ell₁ M).card : ℝ) * (K * ε) := by simp
    _ ≤ (((∏ p, ell₀ p) ^ 2 : ℕ) : ℝ) * (K * ε) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast card_lowMaskedIndices_le ell₀ ell₁ M hinj)
        (mul_nonneg hK hε)
    _ = _ := by push_cast; ring

end Erdos4.FGKMT
