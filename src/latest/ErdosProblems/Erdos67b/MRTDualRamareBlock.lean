import ErdosProblems.Erdos67b.MRTWindowRamare

/-! # Finite duality and the minor-arc saving for actual Ramaré prime blocks -/

open scoped BigOperators ComplexConjugate
open Finset

namespace Erdos67b

noncomputable section

def mrtDualPhase (z : ℂ) : ℂ := if z = 0 then 0 else conj z / (‖z‖ : ℂ)

theorem mrtNorm_dualPhase_le_one (z : ℂ) : ‖mrtDualPhase z‖ ≤ 1 := by
  unfold mrtDualPhase
  split_ifs with hz
  · simp
  · simp only [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    rw [div_self (norm_ne_zero_iff.2 hz)]

theorem mrtDualPhase_mul (z : ℂ) : mrtDualPhase z * z = (‖z‖ : ℂ) := by
  unfold mrtDualPhase
  split_ifs with hz
  · simp [hz]
  · have hnorm : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)
    have hsquare : conj z * z = (‖z‖ : ℂ) ^ 2 := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    calc
      _ = (conj z * z) / (‖z‖ : ℂ) := by ring
      _ = _ := by rw [hsquare]; field_simp

theorem mrtSum_norm_eq_norm_dual_sum {ι : Type*} (S : Finset ι) (F : ι → ℂ) :
    (∑ n ∈ S, ‖F n‖) = ‖∑ n ∈ S, mrtDualPhase (F n) * F n‖ := by
  simp_rw [mrtDualPhase_mul]
  rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]

theorem mrtTypical_firstMoment_le_dual_ramare
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} (hI : I ∈ blocks) (hL : 0 < I.1)
    (Z H Y : ℕ) (hHY : H ≤ Y) (f : ℕ → ℂ) (α : ℝ)
    (hmul : IsMultiplicativeOnPositiveNat f) (hf : ∀ r, 0 < r → ‖f r‖ ≤ 1) :
    ∃ θ : ℕ → ℂ, (∀ n, ‖θ n‖ ≤ 1) ∧
      (∑ n ∈ Finset.Ioc Y (2 * Y), ‖typicalModulatedShortSum blocks Z f n H α‖) ≤
        ‖∑ n ∈ Finset.Ioc Y (2 * Y),
          θ n * mrtRawRamarePrimeSum blocks I (primesInBlock I) Z f n H α‖ +
        12 * H * Y / I.1 := by
  let F : ℕ → ℂ := fun n ↦
    mrtRawShortSum (mrTypicalCommonCoefficient blocks Z (primesInBlock I) f) n H α
  refine ⟨fun n ↦ mrtDualPhase (F n), fun n ↦ mrtNorm_dualPhase_le_one (F n), ?_⟩
  have hdual := mrtSum_norm_eq_norm_dual_sum (Finset.Ioc Y (2 * Y)) F
  have herror := mrtSum_norm_primeSquare_short_error_le hI hL Z H Y hHY f α hmul hf
  calc
    _ ≤ ∑ n ∈ Finset.Ioc Y (2 * Y),
        (‖F n‖ + ‖mrtRawShortSum (mrTypicalValueCoefficient blocks Z f) n H α - F n‖) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [← mrtRawShortSum_typical_norm]
      calc
        _ ≤ ‖F n‖ + ‖F n - mrtRawShortSum (mrTypicalValueCoefficient blocks Z f) n H α‖ :=
          norm_le_norm_add_norm_sub _ _
        _ = _ := by rw [norm_sub_rev]
    _ = (∑ n ∈ Finset.Ioc Y (2 * Y), ‖F n‖) +
        ∑ n ∈ Finset.Ioc Y (2 * Y),
          ‖mrtRawShortSum (mrTypicalValueCoefficient blocks Z f) n H α - F n‖ :=
      Finset.sum_add_distrib
    _ ≤ (∑ n ∈ Finset.Ioc Y (2 * Y), ‖F n‖) + 12 * H * Y / I.1 :=
      add_le_add (le_refl _) herror
    _ = _ := by
      rw [hdual]
      congr 1
      apply congrArg norm
      apply Finset.sum_congr rfl
      intro n hn
      exact congrArg (fun z ↦ mrtDualPhase (F n) * z)
        (mrtRawCommonShortSum_eq_primeSum blocks I Z f n H α)

theorem mrtExists_rawRamareBlock_minorArc_saving :
    ∃ C : ℝ, 0 < C ∧ ∀ H W P q : ℕ, ∀ a : ℤ, ∀ α : ℝ,
      2 ≤ W → W ≤ q → q ≤ H / W + 1 → W ^ 200 ≤ P → P ≤ H / W ^ 3 →
      Nat.Coprime a.natAbs q → |α - (a : ℝ) / q| ≤ (W : ℝ) / ((H : ℝ) * q) →
      ∀ (blocks : Finset (ℕ × ℕ)) (I : ℕ × ℕ) (S : Finset ℕ) (Z Y : ℕ) (f θ : ℕ → ℂ),
        H ≤ Y → S ⊆ primesInBlock I → S ⊆ dyadicPrimeBlock P 0 →
        (∀ J ∈ blocks, J ≠ I → Disjoint (primesInBlock I) (primesInBlock J)) →
        (∀ r, 0 < r → ‖f r‖ ≤ 1) → (∀ n ∈ Finset.Ioc Y (2 * Y), ‖θ n‖ ≤ 1) →
        ‖∑ n ∈ Finset.Ioc Y (2 * Y), θ n * mrtRawRamarePrimeSum blocks I S Z f n H α‖ ^ 4 ≤
          C * (H : ℝ) ^ 4 * (Y : ℝ) ^ 4 * Real.log H /
            ((W : ℝ) * Real.log P ^ 4) := by
  obtain ⟨C, hC, hsaving⟩ := mrtExists_windowBlock_minorArc_saving
  refine ⟨C, hC, ?_⟩
  intro H W P q a α hW hWq hq hWP hPH ha hα blocks I S Z Y f θ hHY hSI hSP hdisj hf hθ
  have hP : 0 < P := (pow_pos (by omega : 0 < W) 200).trans_le hWP
  have hPS : ∀ p ∈ S, P ≤ p := by
    intro p hp
    have hh := (mem_dyadicPrimeBlock.1 (hSP hp)).2.1
    simpa using hh.le
  rw [mrtDual_rawRamarePrimeSum_eq_windowRow hSI hP hPS hHY hdisj f θ α]
  exact hsaving H W P q a α hW hWq hq hWP hPH ha hα S Z Y f
    (mrtTypicalCofactorWeight blocks I f) θ hSP
    (fun p hp ↦ hf p (hP.trans_le (hPS p hp)))
    (fun m hm ↦ mrtNorm_typicalCofactorWeight_le blocks I hf (Finset.mem_Icc.1 hm).1) hθ

end

end Erdos67b
