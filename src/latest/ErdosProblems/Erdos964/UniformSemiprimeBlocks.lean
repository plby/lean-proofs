import ErdosProblems.Erdos964.SemiprimeSavingParameters

/-!
# Uniform logarithmic savings for dyadic semiprime blocks

The threshold and constant are independent of the smaller-prime block,
the product endpoint, and the reduced residue representatives. The modulus
exponent is measured relative to `L`, whose square is the product cap.
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard

theorem exists_uniform_dyadicSemiprimeBlock_logSaving (a : ℕ) (η θ : ℝ)
    (hη : 0 < η) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℕ, 16 ≤ L₀ ∧
      ∀ L : ℕ, L₀ ≤ L → ∀ M : ℕ, Real.rpow (L : ℝ) η / 2 ≤ M → M ≤ L →
      ∀ X : ℕ → ℕ,
        (∀ q, 0 < q → q ≤ modulusCutoff θ L → X q ∈ Finset.Icc 1 (L ^ 2)) →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p ≤ L) →
        P ⊆ Finset.Ioc M (M + M) →
      ∀ r : ℕ → ℕ, (∀ q, 0 < q → q ≤ modulusCutoff θ L → (r q).Coprime q) →
      let Q := (Finset.Ioc L (L ^ 2 / M)).filter Nat.Prime
      (∑ q ∈ Finset.Ioc 0 (modulusCutoff θ L),
        |(finiteResidueCount (primeProductBlock P Q (X q)) q (r q) : ℝ) -
          ((primeProductBlock P Q (X q)).card : ℝ) / q.totient|) ≤
        C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ (a + 1) := by
  let b := a + 4
  let B := b + 1
  obtain ⟨C, hC, N₁, hN₁, hfinite⟩ := exists_dyadicSemiprimeBlock_sum_discrepancy_bound
    ((2 * B : ℕ) : ℝ) (B : ℝ) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  obtain ⟨N₂, hN₂, hparameters⟩ := exists_semiprime_saving_parameters b η θ hη hθ hθ1
  refine ⟨semiprimeSavingConstant C, ?_, max N₁ N₂, hN₂.trans (le_max_right _ _), ?_⟩
  · unfold semiprimeSavingConstant
    have hc3 := akbaryHambrookC3_pos.le
    positivity
  intro L hL M hMlower hML X hX P hP hPL hPinterval r hr
  have hLN₁ : N₁ ≤ L := (le_max_left _ _).trans hL
  have hLN₂ : N₂ ≤ L := (le_max_right _ _).trans hL
  have hL16 : 16 ≤ L := hN₂.trans hLN₂
  have hL4 : 4 ≤ L := by omega
  have hlogpos : 0 < Real.log (L : ℝ) := by
    have := two_le_log_natCast_of_sixteen_le hL16
    linarith
  let s := (Real.log (L : ℝ)) ^ b
  let D := ⌊(Real.log (L : ℝ)) ^ B⌋₊
  let T := modulusCutoff θ L
  let U := L ^ 2 / M
  obtain ⟨hs, hD, hDT, hTL, hTs, hsD, hDlog, hslog, hMsaving⟩ := hparameters L hLN₂
  have hsM : s ^ 2 ≤ M := hMsaving M hMlower
  have hM : 0 < M := by
    have hMone : (1 : ℝ) ≤ M := by nlinarith
    exact_mod_cast hMone
  have hLU : L ≤ U := by
    apply (Nat.le_div_iff_mul_le hM).mpr
    simpa only [pow_two] using Nat.mul_le_mul_left L hML
  have hU : 0 < U := by omega
  have hT : 0 < T := hD.trans_le hDT
  have hMU : (M : ℝ) * U ≤ (L : ℝ) ^ 2 := by
    have hprod : M * U ≤ L ^ 2 := by
      simpa only [U, mul_comm] using Nat.div_mul_le_self (L ^ 2) M
    exact_mod_cast hprod
  have hMN : M ≤ L ^ 2 := hML.trans (by nlinarith)
  have hcap : L ^ 2 ≤ (M + M) * U := le_double_mul_div (L ^ 2) M hM hMN
  have hXcap (q : ℕ) (hq : 0 < q) (hqT : q ≤ T) :
      X q ∈ Finset.Icc 1 ((M + M) * U) :=
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (hX q hq hqT)).1,
      (Finset.mem_Icc.mp (hX q hq hqT)).2.trans hcap⟩
  have hDlogReal : (D : ℝ) ≤ Real.rpow (Real.log (L : ℝ)) (B : ℝ) := by
    simpa only [Real.rpow_eq_pow, Real.rpow_natCast] using hDlog
  have hbound := hfinite L U M D T hLN₁ hLU hM hD hDT hTL hDlogReal X hXcap
    P hP hPL hPinterval r hr
  calc
    _ ≤ (4 * (1 + Real.log (T : ℝ))) *
        (C * (D : ℝ) * (M : ℝ) * U / (Real.log (L : ℝ)) ^ (2 * B) +
          dyadicSemiprimeLargeEnvelope M U D T + dyadicSemiprimeCorrectionEnvelope M U T) := by
      simpa only [Real.rpow_eq_pow, Real.rpow_natCast] using hbound
    _ ≤ semiprimeSavingConstant C * (Real.log (L : ℝ)) ^ 3 * ((L : ℝ) ^ 2 / s) :=
      dyadicSemiprimeFullEnvelope_le_saving C B L M U D T s hC hL4 hM hU hT
        hML hTL.le hMU hs hsM hTs hsD hDlog hslog
    _ = _ := by
      dsimp only [s, b]
      rw [show a + 4 = (a + 1) + 3 by omega, pow_add]
      field_simp

end Erdos964
