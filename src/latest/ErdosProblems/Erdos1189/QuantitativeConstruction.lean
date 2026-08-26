/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The exact-cardinality construction and its logarithmic modulus bound.
Informal source: Sections 6 and 7 of Pickhardt and Omniscience Research Agent.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.BoundedFrame
import ErdosProblems.Erdos1189.PaddingCutoff

namespace Erdos1189

open Finset Filter

def constructionConstant (C : ℕ) : ℝ :=
  128 * ((C : ℝ) + 16 + 2048 * ((C : ℝ) + 1))

lemma constructionConstant_pos (C : ℕ) : 0 < constructionConstant C := by
  unfold constructionConstant
  positivity

lemma frameBound_le_logarithmic {C P B k : ℕ} (hP : P.Prime)
    (hbudget : primeWeightSum P + 1 ≤ k) (hPk : P ≤ k) (hlog : 1 ≤ Real.log P)
    (hweight : (P : ℝ) ^ 2 ≤ 128 * primeWeightSum P * Real.log P)
    (hB : (B : ℝ) ^ 2 ≤ 2048 * P * Real.log P) :
    (frameBound C P B : ℝ) ≤ constructionConstant C * k * (Real.log k) ^ 2 := by
  have hlog0 : 0 ≤ Real.log P := by linarith
  have hlogle : Real.log P ≤ Real.log k :=
    Real.log_le_log (by exact_mod_cast hP.pos) (by exact_mod_cast hPk)
  have hAk : (primeWeightSum P : ℝ) ≤ k := by exact_mod_cast (show primeWeightSum P ≤ k by omega)
  have hBmul := mul_le_mul_of_nonneg_left hB
    (show (0 : ℝ) ≤ ((C : ℝ) + 1) * P by positivity)
  have hfirst : ((C : ℝ) + 16) * P ^ 2 ≤ ((C : ℝ) + 16) * P ^ 2 * Real.log P :=
    le_mul_of_one_le_right (by positivity) hlog
  have hw := mul_le_mul_of_nonneg_right hweight hlog0
  have hw' : (P : ℝ) ^ 2 * Real.log P ≤ 128 * primeWeightSum P * (Real.log P) ^ 2 := by
    nlinarith
  let A : ℝ := (C : ℝ) + 16 + 2048 * ((C : ℝ) + 1)
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  calc
    (frameBound C P B : ℝ) = ((C : ℝ) + 16) * P ^ 2 + ((C : ℝ) + 1) * P * B ^ 2 := by
      simp [frameBound]
    _ ≤ A * P ^ 2 * Real.log P := by dsimp [A]; nlinarith
    _ ≤ constructionConstant C * primeWeightSum P * (Real.log P) ^ 2 := by
      have hh := mul_le_mul_of_nonneg_left hw' hA0
      dsimp [A, constructionConstant] at *
      nlinarith
    _ ≤ constructionConstant C * k * (Real.log k) ^ 2 := by
      have hK := (constructionConstant_pos C).le
      gcongr

/-- The quantitative construction retains every squarefree-product class below
its terminal prime. These classes are used for the reciprocal-sum lower bound. -/
theorem eventually_bounded_construction :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      ∃ P : ℕ, ∃ S : Finset ℕ, P.Prime ∧ P ≤ k ∧ k ≤ P ^ 2 + 2 * P ∧
        IsIrreducibleCoveringSet S ∧ S.card = k ∧
        (∀ d ∈ S, (d : ℝ) ≤ K * k * (Real.log k) ^ 2) ∧
        ∀ q : ℕ, q.Prime → q < P → ∀ d ∈ squarefreeUpto (q - 1), q * d ∈ S := by
  obtain ⟨C, hC, hcount⟩ := exists_uniform_seed_constant
  refine ⟨constructionConstant C, constructionConstant_pos C, ?_⟩
  have htlog : Tendsto (fun P : ℕ => Real.log P) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hgood : ∀ᶠ P : ℕ in atTop,
      3 * P ≤ (smallSquarefreeSeeds P (16 * P)).card ∧
      paddingCutoff P < P ∧ 2 * P ≤ primeWeightSum (paddingCutoff P) ∧
      (paddingCutoff P : ℝ) ^ 2 ≤ 2048 * P * Real.log P ∧
      (P : ℝ) ^ 2 ≤ 128 * primeWeightSum P * Real.log P ∧ 1 ≤ Real.log P := by
    filter_upwards [eventually_small_squarefree_seeds, eventually_paddingCutoff_bounds,
      eventually_primeWeightSum_lower, htlog.eventually (eventually_ge_atTop 1)]
      with P hstock hpad hw hl
    exact ⟨hstock, hpad.1, hpad.2.1, hpad.2.2, hw, hl⟩
  obtain ⟨P₀, hP₀⟩ := eventually_atTop.mp hgood
  filter_upwards [eventually_ge_atTop (max 2 (P₀ ^ 2 + 2 * P₀ + 1))] with k hk
  obtain ⟨P, hP, hbudget, hgap⟩ := exists_prime_budget (show 2 ≤ k by omega)
  have hPlarge : P₀ < P := prime_budget_large hP hbudget hgap (by omega)
  obtain ⟨hstock, hB, hBweight, hBsq, hweight, hlog⟩ := hP₀ P hPlarge.le
  obtain ⟨D, hD, hDsum⟩ := prime_weights_complete_cutoff (paddingCutoff P)
    (show k - 1 - primeWeightSum P ≤ primeWeightSum (paddingCutoff P) by omega)
  obtain ⟨F⟩ := exists_frame_seed_family hP hB hD hC hcount hstock
  obtain ⟨hS, hScard⟩ := F.irreducible_frameInteger hP hB hD
  have hDP : D ⊆ Nat.primesLE P := fun q hq => Nat.mem_primesLE.mpr
    ⟨(Nat.le_of_mem_primesLE (hD hq)).trans hB.le, Nat.prime_of_mem_primesLE (hD hq)⟩
  rw [frameInteger_weight hDP, hDsum] at hScard
  have hcard : F.moduli.card = k := by omega
  obtain ⟨hPk, hkP⟩ := prime_budget_bounds hP hbudget hgap
  refine ⟨P, F.moduli, hP, hPk, hkP, hS, hcard, ?_, ?_⟩
  · intro d hd
    exact (show (d : ℝ) ≤ frameBound C P (paddingCutoff P) by
      exact_mod_cast F.all_moduli_le hP hB hD d hd).trans
        (frameBound_le_logarithmic hP hbudget hPk hlog hweight hBsq)
  · intro q hq hqP d hd
    exact F.contains_squarefree_products hq hqP hd

end Erdos1189
