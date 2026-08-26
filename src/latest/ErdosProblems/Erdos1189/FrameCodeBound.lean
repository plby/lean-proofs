/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The entropy bound for one choice of coordinate order, family sizes, and remainder.
Informal source: BBMST Section 7.2.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.UniformFrameEntropy
import ErdosProblems.Erdos1189.FrameEntropyBudget
import ErdosProblems.Erdos1189.FiniteFamilyEncoding

namespace Erdos1189

open Finset

lemma frame_code_log_bound {N T x : ℕ} (rank : PrimeCoordinate N → ℕ)
    {b E : ℝ}
    (hframe : ∀ i, Real.log (frameAllowedModuli rank i T).card ≤
      b * rootLog (prefixWeight (largeCoordinates N T) rank
        (fun c => coordinateSize c - 1) i) + E)
    (hrest : Real.log (boundedProfileModuli N N.factorization).card ≤
      b * rootLog (largeCoordinateWeight N T) + E) :
    (∑ i : largeCoordinates N T, ((coordinateSize i.val - 1 : ℕ) : ℝ) *
      Real.log (frameAllowedModuli rank i T).card) +
      x * Real.log (boundedProfileModuli N N.factorization).card ≤
        b * ((∑ i ∈ largeCoordinates N T, ((coordinateSize i - 1 : ℕ) : ℝ) *
          rootLog (prefixWeight (largeCoordinates N T) rank
            (fun c => coordinateSize c - 1) i)) +
              x * rootLog (largeCoordinateWeight N T)) +
                ((largeCoordinateWeight N T : ℝ) + x) * E := by
  rw [sum_coe_sort (largeCoordinates N T) (fun i =>
    ((coordinateSize i - 1 : ℕ) : ℝ) * Real.log (frameAllowedModuli rank i T).card)]
  have h := sum_le_sum (s := largeCoordinates N T) (fun i _ =>
    mul_le_mul_of_nonneg_left (hframe i) (Nat.cast_nonneg (coordinateSize i - 1)))
  have hx := mul_le_mul_of_nonneg_left hrest (Nat.cast_nonneg x (α := ℝ))
  apply (add_le_add h hx).trans_eq
  simp only [mul_add, sum_add_distrib, ← sum_mul, ← mul_sum, mul_left_comm,
    ← Nat.cast_sum, largeCoordinateWeight]
  ring

noncomputable def frameCodeBound (a b E n M : ℝ) : ℝ :=
  b * ((2 / (3 * Real.sqrt a)) * M * Real.sqrt M / Real.sqrt (Real.log n) +
    M * Real.sqrt (n ^ a) / Real.sqrt (Real.log 2)) + M * E

lemma frame_code_card_le_exp {N T x : ℕ} (rank : PrimeCoordinate N → ℕ)
    (sizes : largeCoordinates N T → ℕ) (hinj : Function.Injective rank)
    (hsizes : ∀ i, sizes i ≤ coordinateSize i.val - 1) {a b E n : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hn : 1 < n)
    (hframe : ∀ i, Real.log (frameAllowedModuli rank i T).card ≤
      b * rootLog (prefixWeight (largeCoordinates N T) rank
        (fun c => coordinateSize c - 1) i) + E)
    (hrest : Real.log (boundedProfileModuli N N.factorization).card ≤
      b * rootLog (largeCoordinateWeight N T) + E) :
    ((familyUnionUniverse (fun i : largeCoordinates N T => frameAllowedModuli rank i T)
      sizes (boundedProfileModuli N N.factorization) x).card : ℝ) ≤
        Real.exp (frameCodeBound a b E n ((largeCoordinateWeight N T : ℝ) + x)) := by
  have hcard := familyUnionUniverse_card_le_exp
    (fun i : largeCoordinates N T => frameAllowedModuli rank i T)
    sizes (fun i => coordinateSize i.val - 1) (boundedProfileModuli N N.factorization) x
    hsizes (fun _ => boundedProfileModuli_card_pos _ _) (boundedProfileModuli_card_pos _ _)
  apply hcard.trans (Real.exp_le_exp.mpr ?_)
  apply (frame_code_log_bound rank hframe hrest).trans
  have hbudget := frame_and_remainder_entropy_budget (largeCoordinates N T) rank
    (fun c => coordinateSize c - 1) hinj.injOn ha hn (Nat.cast_nonneg x (α := ℝ))
  exact add_le_add (mul_le_mul_of_nonneg_left hbudget hb) le_rfl

lemma frameCodeBound_mono {a b E n M M' : ℝ} (hb : 0 ≤ b) (hE : 0 ≤ E)
    (hM : 0 ≤ M) (hMM : M ≤ M') :
    frameCodeBound a b E n M ≤ frameCodeBound a b E n M' := by
  unfold frameCodeBound
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ hb
    apply add_le_add
    · apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
      have hprod := mul_le_mul hMM (Real.sqrt_le_sqrt hMM)
        (Real.sqrt_nonneg M) (hM.trans hMM)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod
        (show 0 ≤ 2 / (3 * Real.sqrt a) by positivity)
    · exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hMM (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  · exact mul_le_mul_of_nonneg_right hMM hE

end Erdos1189
