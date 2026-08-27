import ErdosProblems.Erdos4.FGKMTPrimeExcision
import BoundedGaps.BombieriVinogradov.Analytic.DirichletExceptionalZeroKernel

/-! An explicit exceptional-kernel bound using the common real zero gap. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open BoundedGaps.Maynard

theorem exceptional_kernel_le_of_gap {M q : ℕ} [NeZero q] (hM : 2 ≤ M)
    (χ : DirichletCharacter ℂ q) {x w : ℝ} (hx : 1 ≤ x) (T : ℝ)
    (hgap : ∀ ρ : ℂ, IsDirichletExceptionalLFunctionZeroAtScale M χ ρ → ρ.re ≤ 1 - w) :
    ‖dirichletExceptionalZeroKernelSum M χ x T‖ ≤ 2 * x ^ (1 - w) := by
  classical
  let S := dirichletExceptionalLFunctionZerosFinset M χ T
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [dirichletExceptionalZeroKernelSum]
    change ‖∑ ρ ∈ S, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) *
      dirichletExplicitFormulaKernel x ρ‖ ≤ _
    rw [hS]
    simp only [Finset.sum_empty, norm_zero]
    positivity
  · obtain ⟨ρ, hρS⟩ := hS
    have hcard : S.card ≤ 1 := card_dirichletExceptionalLFunctionZerosFinset_le_one M χ T
    have hsingle : S = {ρ} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hρS, fun z hz => Finset.card_le_one.mp hcard z hz ρ hρS⟩
    have hex := (mem_dirichletExceptionalLFunctionZerosFinset_iff.mp hρS).2.2
    have hβ := hgap ρ hex
    obtain ⟨hnear, _, _, _, ψ, _, hχ, _, him, horder, _⟩ := hex
    have horderχ : analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ = 1 := by
      simpa [hχ] using horder
    have hhalf : (1 / 2 : ℝ) < ρ.re := half_lt_re_of_near_one_scale hM hnear
    have hρreal : ρ = (ρ.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him
    have hkernel : ‖dirichletExplicitFormulaKernel x ρ‖ ≤ 2 * x ^ (1 - w) := by
      rw [hρreal, norm_dirichletExplicitFormulaKernel_ofReal_eq_rpow_sub_one_div hx (by linarith)]
      calc
        _ ≤ x ^ ρ.re / ρ.re := div_le_div_of_nonneg_right (by linarith) (by linarith)
        _ ≤ x ^ ρ.re / (1 / 2) := div_le_div_of_nonneg_left
          (Real.rpow_nonneg (by linarith) _) (by norm_num) hhalf.le
        _ ≤ x ^ (1 - w) / (1 / 2) := div_le_div_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le hx hβ) (by norm_num)
        _ = _ := by ring
    rw [dirichletExceptionalZeroKernelSum]
    change ‖∑ z ∈ S, (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) *
      dirichletExplicitFormulaKernel x z‖ ≤ _
    rw [hsingle]
    simpa only [Finset.sum_singleton, horderχ, Nat.cast_one, one_mul] using hkernel

theorem exceptional_kernel_le_after_excision {U Q B M : ℕ} (hM : 2 ≤ M)
    (hexc : ∀ χ : PrimitiveCharacter, χ.modulus.Coprime B → ¬HasExceptionalRealZero U Q χ)
    (χ : PrimitiveCharacter) (hq : χ.modulus ≤ Q) (hcop : χ.modulus.Coprime B)
    {x : ℝ} (hx : 1 ≤ x) (T : ℝ) :
    ‖dirichletExceptionalZeroKernelSum M χ.character x T‖ ≤
      2 * x ^ (1 - exceptionalWidth U Q) := by
  apply exceptional_kernel_le_of_gap hM χ.character hx T
  intro ρ hρ
  obtain ⟨_, _, _, _, ψ, hψ, hχ, _, him, _, _⟩ := hρ
  subst ψ
  have hh := (isNonprincipalNontrivialLFunctionZero_iff χ.character ρ).mp hψ
  have hreal : (ρ.re : ℂ) = ρ := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using him.symm
  exact (real_zero_gap_of_prime_excision hexc χ hq hcop hh.2.2.1 hh.2.2.2
    (by rw [hreal]; exact hh.2.1)).le

end Erdos4.FGKMT
