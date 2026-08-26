/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Counting all frame encodings for a fixed least common multiple.
Informal source: BBMST Section 7.2.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.FrameParameters
import ErdosProblems.Erdos1189.FrameCodeBound

namespace Erdos1189

open Finset

theorem frameUniverse_card_le_exp {N T k : ℕ} {a b E η : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hE : 0 ≤ E) (hη : 0 ≤ η)
    (hk : 1 < k) (hW : simpsonWeight N ≤ k)
    (hframe : ∀ (rank : PrimeCoordinate N → ℕ) i,
      Real.log (frameAllowedModuli rank i T).card ≤
        b * rootLog (prefixWeight (largeCoordinates N T) rank
          (fun c => coordinateSize c - 1) i) + E)
    (hrest : Real.log (boundedProfileModuli N N.factorization).card ≤
      b * rootLog (largeCoordinateWeight N T) + E) :
    ((frameUniverse N T k η).card : ℝ) ≤
      Real.exp (((2 * k + 1 : ℕ) : ℝ) * Real.log ((k : ℝ) + 1) +
        frameCodeBound a b E k ((1 + η) * k)) := by
  classical
  let B := frameCodeBound a b E k ((1 + η) * k)
  have hcodes : ∀ c ∈ validFrameCodes N T k η,
      ((frameCodeUniverse c).card : ℝ) ≤ Real.exp B := by
    intro c hc
    obtain ⟨hinj, hsizes, hbudget⟩ := (mem_filter.mp hc).2
    have h := frame_code_card_le_exp (n := (k : ℝ)) (x := c.2.2.val)
      (fun i => (c.1 i).val)
      (fun i => (c.2.1 i).val) hinj hsizes ha hb (by exact_mod_cast hk)
      (hframe _) hrest
    apply h.trans (Real.exp_le_exp.mpr ?_)
    apply frameCodeBound_mono hb hE (by positivity)
    have hW' : (simpsonWeight N : ℝ) ≤ k := by exact_mod_cast hW
    nlinarith
  have hparam : (validFrameCodes N T k η).card ≤ (k + 1) ^ (2 * k + 1) :=
    (card_le_card (filter_subset _ _)).trans
      (by simpa only [card_univ] using card_frameCode_le (T := T) hW)
  have hsum : ((frameUniverse N T k η).card : ℝ) ≤
      (∑ c ∈ validFrameCodes N T k η, ((frameCodeUniverse c).card : ℝ)) := by
    exact_mod_cast card_biUnion_le
  calc
    _ ≤ _ := hsum
    _ ≤ (validFrameCodes N T k η).card * Real.exp B := by
      simpa only [sum_const, nsmul_eq_mul] using sum_le_sum hcodes
    _ ≤ ((k + 1) ^ (2 * k + 1) : ℕ) * Real.exp B :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hparam) (Real.exp_pos B).le
    _ = _ := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by positivity)]
      push_cast
      rfl

noncomputable def countingEntropyError (C : ℝ) (T : ℕ) (k : ℝ) : ℝ :=
  C + T * Real.log (k + 1) + Real.log 2 + T * Real.log ((T : ℝ) + 1)

lemma countingEntropyError_nonneg {C k : ℝ} (hC : 0 ≤ C) (hk : 0 ≤ k) (T : ℕ) :
    0 ≤ countingEntropyError C T k := by
  have hlog : 0 ≤ Real.log (k + 1) := Real.log_nonneg (by linarith)
  have hT : 0 ≤ Real.log ((T : ℝ) + 1) :=
    Real.log_nonneg (by have := Nat.cast_nonneg T (α := ℝ); linarith)
  have h2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold countingEntropyError
  positivity

lemma frameEntropyError_le {C : ℝ} {N T k : ℕ} (hW : simpsonWeight N ≤ k) :
    frameEntropyError C N T ≤ countingEntropyError C T k := by
  unfold frameEntropyError countingEntropyError
  have hlog : Real.log ((simpsonWeight N : ℝ) + 1) ≤ Real.log ((k : ℝ) + 1) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast Nat.add_le_add_right hW 1
  have h := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg T (α := ℝ))
  linarith

lemma countingEntropyError_ge_constant (C : ℝ) (T : ℕ) {k : ℝ} (hk : 0 ≤ k) :
    C + Real.log 2 ≤ countingEntropyError C T k := by
  have hklog : 0 ≤ Real.log (k + 1) := Real.log_nonneg (by linarith)
  have hTlog : 0 ≤ Real.log ((T : ℝ) + 1) :=
    Real.log_nonneg (by have := Nat.cast_nonneg T (α := ℝ); linarith)
  have h1 := mul_nonneg (Nat.cast_nonneg T (α := ℝ)) hklog
  have h2 := mul_nonneg (Nat.cast_nonneg T (α := ℝ)) hTlog
  unfold countingEntropyError
  linarith

end Erdos1189
