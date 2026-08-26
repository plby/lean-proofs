import ErdosProblems.Erdos67b.MRScheduledSmallEnergy
import ErdosProblems.Erdos67b.MRShortIntervalBudget

/-!
# The complex nonpretentious short-interval mean square

This proves the unmodulated complex mean-square input from the actual
scheduled energy, finite sieve density, and corrected Perron reduction.
The common threshold precedes both the distance and short-length choices.
-/

open Finset MeasureTheory

namespace Erdos67b

noncomputable section

/-- Unconditional complex MR mean square with the required parameter order. -/
theorem mrComplexNonpretentiousMeanSquareInput : MRComplexNonpretentiousMeanSquareInput := by
  intro epsilon hepsilon
  let alpha : ℝ := epsilon ^ 2 / 4
  let e : ℝ := alpha / (8 * (lemma14UniversalScaledLowConstant + 1))
  let d : ℝ := alpha / 2
  have halpha : 0 < alpha := by dsimp only [alpha]; positivity
  have hlow := lemma14UniversalScaledLowConstant_nonneg
  have he : 0 < e := by dsimp only [e]; positivity
  have hd : 0 < d := by dsimp only [d]; positivity
  obtain ⟨p, q, _, _, _, _, _, _, _, M₀, X₀, _, _, hsource⟩ :=
    mrExists_scheduled_small_energy_and_density
      (by norm_num : (0 : ℝ) < 1 / 12) (le_refl (1 / 12 : ℝ)) he hd 0
  let c : ℝ := Real.exp (-q)
  have hc : 0 < c := Real.exp_pos _
  let K : ℝ := mrShortIntervalTailCost c
  let B : ℕ := max 1 (max M₀ ⌈K / alpha⌉₊)
  refine ⟨B, le_max_left _ _, ?_⟩
  intro A H hA hH
  let X₁ : ℕ := max (max A H) (max X₀ ⌈2 * (H : ℝ) / alpha⌉₊)
  refine ⟨X₁, le_max_left _ _, ?_⟩
  intro X hX f hmul hbound hnonpret
  have hM : M₀ ≤ A := by dsimp only [B] at hA; omega
  have hHX : H ≤ X := by dsimp only [X₁] at hX; omega
  have hX₀ : X₀ ≤ X := by dsimp only [X₁] at hX; omega
  have hHpos : 0 < H := by dsimp only [B] at hH; omega
  have hXpos : 0 < X := hHpos.trans_le hHX
  have hHR : (0 : ℝ) < H := by exact_mod_cast hHpos
  have hXR : (0 : ℝ) < X := by exact_mod_cast hXpos
  obtain ⟨J, _, _, _, hdensity, henergy⟩ := hsource hM hX₀
  have hE : (∫ t in -(c * X)..(c * X),
      ‖mrTypicalDyadicPolynomial (mrScheduledBlocks p q J) f X t‖ ^ 2) ≤ e := by
    apply henergy hmul hbound hnonpret (mul_pos hc hXR).le
    exact le_of_eq (mul_comm c (X : ℝ))
  have hbad := hdensity (2 * X + H) (by omega)
  have hmain := mrShortInterval_le_typical_energy_density
    (mrScheduledBlocks p q J) hbound hHpos hHX hc he.le hE hbad
  have hcentral : 8 * lemma14UniversalScaledLowConstant * e ≤ alpha := by
    dsimp only [e]
    have hden : 0 < lemma14UniversalScaledLowConstant + 1 := by positivity
    calc
      _ = alpha * (lemma14UniversalScaledLowConstant /
          (lemma14UniversalScaledLowConstant + 1)) := by field_simp
      _ ≤ alpha * 1 := mul_le_mul_of_nonneg_left
        ((div_le_one hden).2 (by linarith)) halpha.le
      _ = alpha := mul_one _
  have hdensityCost : 2 * d = alpha := by dsimp only [d]; ring
  have hHceil : ⌈K / alpha⌉₊ ≤ H := by dsimp only [B] at hH; omega
  have hKlinear : K ≤ (H : ℝ) * alpha :=
    (div_le_iff₀ halpha).1 (Nat.le_of_ceil_le hHceil)
  have hHone : (1 : ℝ) ≤ H := by exact_mod_cast hHpos
  have hK : K ≤ alpha * (H : ℝ) ^ 2 := by
    nlinarith [mul_nonneg halpha.le (show 0 ≤ (H : ℝ) ^ 2 - H by nlinarith)]
  have hXceil : ⌈2 * (H : ℝ) / alpha⌉₊ ≤ X := by dsimp only [X₁] at hX; omega
  have hboundaryLinear : 2 * (H : ℝ) ≤ (X : ℝ) * alpha :=
    (div_le_iff₀ halpha).1 (Nat.le_of_ceil_le hXceil)
  have hboundary : 2 * (H : ℝ) ^ 3 ≤ alpha * (H : ℝ) ^ 2 * X := by
    have hh := mul_le_mul_of_nonneg_right hboundaryLinear (sq_nonneg (H : ℝ))
    nlinarith
  have henergyCost : (8 * lemma14UniversalScaledLowConstant * e + 2 * d) *
      (H : ℝ) ^ 2 * X ≤ 2 * alpha * (H : ℝ) ^ 2 * X := by
    have hh : 8 * lemma14UniversalScaledLowConstant * e + 2 * d ≤ 2 * alpha := by
      linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hh (sq_nonneg _)) hXR.le
  have htail := mul_le_mul_of_nonneg_right hK hXR.le
  change mrShortIntervalTailCost c * (X : ℝ) ≤ _ at htail
  calc
    _ ≤ (8 * lemma14UniversalScaledLowConstant * e + 2 * d) * (H : ℝ) ^ 2 * X +
        mrShortIntervalTailCost c * X + 2 * (H : ℝ) ^ 3 := hmain
    _ ≤ 4 * alpha * (H : ℝ) ^ 2 * X := by linarith
    _ = epsilon ^ 2 * (H : ℝ) ^ 2 * X := by dsimp only [alpha]; ring

end

end Erdos67b
