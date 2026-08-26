/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPhysicalDensity
import ErdosProblems.Erdos4b.GeneralFourierSourceBounds

/-!
# Uniform normalization bounds for the CRT endpoint error

The affine normalization is bounded by four times the scale product
once the pre-sieve cutoff is large. In the endpoint bound, the physical
density cancels exactly, leaving only the primorial and coefficient
mass over the interval length.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem half_le_norm_affineAuxiliaryPrimeCorrection
    (H : Finset ℕ) {m q : ℕ} (hq : q.Prime) (hcard : 8 * (H.card : ℝ) ≤ q) :
    (1 : ℝ) / 2 ≤ ‖affineAuxiliaryPrimeCorrection H m q‖ := by
  have hbound := norm_affineAuxiliaryPrimeCorrection_sub_one_le (m := m) H hq (by linarith)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hfrac : 4 * (H.card : ℝ) / q ≤ 1 / 2 := (div_le_iff₀ hqR).mpr (by linarith)
  have hnorm := norm_sub_norm_le (1 : ℂ) (affineAuxiliaryPrimeCorrection H m q)
  rw [norm_one, norm_sub_rev] at hnorm
  linarith

theorem norm_actualAffineFourierNormalization_le_four_mul_prod
    {K w m q : ℕ} (L : (Fin K ⊕ Fin K) → ℝ) (hL : ∀ i, 0 ≤ L i)
    (hm : 0 < m) (hq : q.Prime) (hw : 14 * K + 1 ≤ w) (hwq : w < q)
    (hS : (1 : ℝ) / 2 ≤ ‖∏' p : Nat.Primes, roughDoubledFourierSingularFactor w
      (indexedPreSievedFourierEdges K w m q) (affineFourierCompanionSwitch m) p‖) :
    ‖actualAffineFourierNormalization K w m q L‖ ≤ 4 * ∏ i, L i := by
  have hqR : 8 * ((preSievedShifts K w).card : ℝ) ≤ q := by
    rw [card_preSievedShifts]
    exact_mod_cast (show 8 * K ≤ q by omega)
  rw [actualAffineFourierNormalization_eq_div_correction L hm hq hw hwq, norm_div]
  calc
    _ ≤ (2 * ∏ i, L i) / (1 / 2) := div_le_div₀
      (mul_nonneg (by norm_num) (Finset.prod_nonneg fun i hi ↦ hL i))
      (norm_doubledFourierNormalization_le w _ _ L hL hS) (by norm_num)
      (half_le_norm_affineAuxiliaryPrimeCorrection _ hq hqR)
    _ = _ := by ring

theorem exists_uniform_actualAffineFourierNormalization_bound (K : ℕ) :
    ∃ W : ℕ, ∀ {w m q : ℕ}, W ≤ w → 0 < m → q.Prime → w < q →
      ∀ (L : (Fin K ⊕ Fin K) → ℝ), (∀ i, 0 ≤ L i) →
      ‖actualAffineFourierNormalization K w m q L‖ ≤ 4 * ∏ i, L i := by
  obtain ⟨W, hW⟩ := exists_uniform_half_le_norm_tprod_roughDoubledFourierSingularFactor (Fin K)
  refine ⟨max W (14 * K + 1), fun {w m q} hw hm hq hwq L hL ↦ ?_⟩
  have hlarge : 14 * K + 1 ≤ w := (le_max_right _ _).trans hw
  apply norm_actualAffineFourierNormalization_le_four_mul_prod L hL hm hq hlarge hwq
  apply hW _ _ ((le_max_left _ _).trans hw)
    (Nat.mul_pos hm (crossExceptionalModulus_pos (H := preSievedShifts K w) hm hq))
  · intro p hwp
    simpa only [Fintype.card_fin] using
      card_indexedPreSievedFourierEdges_le (m := m) (q := q) p.property (by omega : K ≤ w) hwp
  · exact fun p hwp hnot ↦ indexedPreSievedFourierEdges_generic hnot

theorem norm_fullAffineFourierNormalization_mul_error_div_le
    {K w m q T : ℕ} (L : (Fin K ⊕ Fin K) → ℝ)
    (hK : 0 < K) (hw : 2 ≤ w) (hm : 0 < m) (hmeven : Even m) (hT : 0 < T)
    {N B E : ℝ} (hN : ‖actualAffineFourierNormalization K w m q L‖ ≤ N)
    (_hB : 0 ≤ B) (herror : |E| ≤ B * (allowedPreSieveResidues (primorial w) m).card) :
    ‖fullAffineFourierNormalization K w m q L * (E : ℂ) / (T : ℂ)‖ ≤
      N * B * (primorial w : ℝ) / T := by
  have hρ : 0 < preSieveDensity w m := preSieveDensity_pos_of_even hmeven
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hP : (0 : ℝ) < primorial w := by exact_mod_cast primorial_pos w
  have hN0 : 0 ≤ N := (norm_nonneg _).trans hN
  have hid := congrArg norm
    (fullAffineFourierNormalization_mul_preSieveDensity (w := w) (q := q) L hK hmeven)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ] at hid
  have hfull : ‖fullAffineFourierNormalization K w m q L‖ =
      ‖actualAffineFourierNormalization K w m q L‖ / preSieveDensity w m :=
    (eq_div_iff hρ.ne').mpr hid
  have hcard : ((allowedPreSieveResidues (primorial w) m).card : ℝ) =
      preSieveDensity w m * primorial w :=
    (div_eq_iff hP.ne').mp (card_allowedPreSieveResidues_div_primorial hw hm)
  rw [norm_div, norm_mul, show ‖(T : ℂ)‖ = (T : ℝ) by simp,
    Complex.norm_real, Real.norm_eq_abs, hfull]
  calc
    _ ≤ (N / preSieveDensity w m) *
        (B * (allowedPreSieveResidues (primorial w) m).card) / T := by
      apply div_le_div_of_nonneg_right _ hTR.le
      exact mul_le_mul (div_le_div_of_nonneg_right hN hρ.le) herror (abs_nonneg _)
        (div_nonneg hN0 hρ.le)
    _ = _ := by
      rw [hcard]
      field_simp

end

end Erdos4b
