/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The sharp asymptotic upper bound and the counting asymptotic.
Informal source: BBMST, applied to modulus sets as in the selected writeup.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.CountingUpperNormalization
import ErdosProblems.Erdos1189.CountingLower

namespace Erdos1189

open Filter

lemma exists_counting_upper_parameters {B : ℝ} (hB : 4 * Real.sqrt tau / 3 < B) :
    ∃ a b η : ℝ, 0 < a ∧ a < 1 ∧ 2 * Real.sqrt tau < b ∧
      0 < η ∧ η < 1 ∧ countingUpperCoefficient a b η < B := by
  have hcont : ContinuousAt
      (fun t : ℝ => countingUpperCoefficient (1 - t) (2 * Real.sqrt tau + t) t) 0 := by
    unfold countingUpperCoefficient
    fun_prop (disch := norm_num)
  have hto : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ => show (n : ℝ) ≤ (n : ℝ) + 2 by linarith)
      tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (nhds 0) := by
    exact hto.const_div_atTop 1
  have ht := hcont.tendsto.comp hsmall
  have hval : countingUpperCoefficient 1 (2 * Real.sqrt tau) 0 = 4 * Real.sqrt tau / 3 := by
    norm_num [countingUpperCoefficient]
    ring
  simp only [sub_zero, add_zero, hval] at ht
  obtain ⟨n, hn⟩ := ((tendsto_order.mp ht).2 B hB).exists
  let t : ℝ := 1 / ((n : ℝ) + 2)
  have ht0 : 0 < t := by dsimp only [t]; positivity
  have ht1 : t < 1 := by
    dsimp only [t]
    apply (div_lt_one (by positivity)).mpr
    have := Nat.cast_nonneg n (α := ℝ)
    linarith
  exact ⟨1 - t, 2 * Real.sqrt tau + t, t, by linarith, by linarith,
    by linarith, ht0, ht1, hn⟩

theorem irreducibleCount_eventually_upper {B : ℝ} (hB : 4 * Real.sqrt tau / 3 < B) :
    ∀ᶠ k : ℕ in atTop,
      Real.log (irreducibleCount k) * Real.sqrt (Real.log k) /
        ((k : ℝ) * Real.sqrt k) < B := by
  obtain ⟨a, b, η, ha, ha1, hb, hη, hη1, hcoef⟩ := exists_counting_upper_parameters hB
  obtain ⟨C, _, T, hfinite⟩ := irreducibleCount_finite_upper ha hb hη hη1
  have ht := countingUpperExponent_normalized ha1 b C T hη.le
  filter_upwards [(tendsto_order.mp ht).2 B hcoef, eventually_ge_atTop 5] with k hk hk5
  have hcount0 : (0 : ℝ) < irreducibleCount k := by exact_mod_cast irreducibleCount_pos hk5
  have hlog : Real.log (irreducibleCount k) ≤ countingUpperExponent a b C T η k := by
    have h := Real.log_le_log hcount0 (hfinite k (by omega))
    rwa [Real.log_exp] at h
  exact (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hlog (Real.sqrt_nonneg _)) (by positivity)).trans_lt hk

theorem counting_asymptotic : CountingAsymptotic := by
  refine ⟨finite_irreducibleSetsOfSize, tendsto_order.mpr ⟨?_, ?_⟩⟩
  · exact fun b hb => irreducibleCount_eventually_lower hb
  · exact fun b hb => irreducibleCount_eventually_upper hb

end Erdos1189
