/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CertificateData

namespace Erdos232

/-- The 26 pair-correlation terms (the zeroth Bessel term is the unit-distance row). -/
noncomputable def pairSpectralValue (correlation : Fin 27 → ℝ) : ℝ :=
  ∑ j : Fin 26, (dualWeight ⟨j.val + 1, by omega⟩ : ℝ) *
    correlation ⟨j.val + 1, by omega⟩

private theorem summable_bessel_product {ι : Type*} (κ frequency : ι → ℝ)
    (hκ : Summable κ) (hκ0 : ∀ i, 0 ≤ κ i) (j : Fin 27) :
    Summable (fun i => κ i * besselJ0 (frequency i * dualDistance j)) := by
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hκ0 i)]
    exact mul_le_of_le_one_right (hκ0 i) (abs_besselJ0_le_one _)) hκ

private theorem tsum_fin_sum {ι : Type*} {n : ℕ} (f : ι → Fin n → ℝ)
    (hf : ∀ j, Summable (fun i => f i j)) :
    (∑' i, ∑ j, f i j) = ∑ j, ∑' i, f i j := by
  exact (hasSum_sum fun j (_ : j ∈ Finset.univ) => (hf j).hasSum).tsum_eq

/-- Summing the certified pointwise Bessel inequality against nonnegative Fourier masses gives
the spectral half of weak duality. -/
theorem spectralCertificate_bound
    {ι : Type*} (κ frequency : ι → ℝ) (δ : ℝ) (correlation : Fin 27 → ℝ)
    (hκ : Summable κ) (hκ0 : ∀ i, 0 ≤ κ i)
    (hδ : ∑' i, κ i = δ)
    (hcorrelation : ∀ j, correlation j =
      ∑' i, κ i * besselJ0 (frequency i * dualDistance j))
    (hunit : correlation 0 = 0)
    (hspectral : ∀ i, 1 ≤ (dualConstant : ℝ) +
      spectralSum dualWeight dualDistance (frequency i)) :
    δ ≤ (dualConstant : ℝ) * δ + pairSpectralValue correlation := by
  let term : ι → Fin 27 → ℝ := fun i j =>
    κ i * besselJ0 (frequency i * dualDistance j) * (dualWeight j : ℝ)
  have hterm (j : Fin 27) : Summable (fun i => term i j) := by
    exact (summable_bessel_product κ frequency hκ hκ0 j).mul_right (dualWeight j : ℝ)
  have hfinite : Summable (fun i => ∑ j, term i j) :=
    summable_sum fun j (_ : j ∈ Finset.univ) => hterm j
  have hright : Summable (fun i => κ i *
      ((dualConstant : ℝ) + spectralSum dualWeight dualDistance (frequency i))) := by
    have hc : Summable (fun i => (dualConstant : ℝ) * κ i) := hκ.mul_left _
    have heq : (fun i => κ i *
        ((dualConstant : ℝ) + spectralSum dualWeight dualDistance (frequency i))) =
        fun i => (dualConstant : ℝ) * κ i + ∑ j, term i j := by
      funext i
      simp only [spectralSum, term]
      rw [mul_add, Finset.mul_sum]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro j _
        ring
    rw [heq]
    exact hc.add hfinite
  have hsum : (∑' i, κ i) ≤ ∑' i, κ i *
      ((dualConstant : ℝ) + spectralSum dualWeight dualDistance (frequency i)) := by
    exact Summable.tsum_le_tsum (fun i => by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hspectral i) (hκ0 i)) hκ hright
  have hrewrite : (∑' i, κ i *
      ((dualConstant : ℝ) + spectralSum dualWeight dualDistance (frequency i))) =
      (dualConstant : ℝ) * δ + ∑ j, (dualWeight j : ℝ) * correlation j := by
    have heq : (fun i => κ i *
        ((dualConstant : ℝ) + spectralSum dualWeight dualDistance (frequency i))) =
        fun i => (dualConstant : ℝ) * κ i + ∑ j, term i j := by
      funext i
      simp only [spectralSum, term]
      rw [mul_add, Finset.mul_sum]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro j _
        ring
    rw [heq, (hκ.mul_left (dualConstant : ℝ)).tsum_add hfinite,
      hκ.tsum_mul_left, hδ, tsum_fin_sum term hterm]
    apply congrArg ((dualConstant : ℝ) * δ + ·)
    apply Finset.sum_congr rfl
    intro j _
    rw [hcorrelation]
    simp only [term]
    rw [(summable_bessel_product κ frequency hκ hκ0 j).tsum_mul_right]
    ring
  rw [hδ, hrewrite] at hsum
  have hsplit : (∑ j : Fin 27, (dualWeight j : ℝ) * correlation j) =
      (dualWeight 0 : ℝ) * correlation 0 + pairSpectralValue correlation := by
    simp [pairSpectralValue, Fin.sum_univ_succ]
  rw [hsplit, hunit] at hsum
  simpa using hsum

end Erdos232
