/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A small prime cutoff with enough total weight to fill the cardinality deficit.
Informal source: Section 6.1 of Pickhardt and Omniscience Research Agent.
Constants are enlarged to use the proved coarse prime-weight estimates.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.PrimeWeightBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Instances.Nat

namespace Erdos1189

open Filter

noncomputable def paddingCutoff (P : ℕ) : ℕ :=
  ⌈Real.sqrt (512 * (P : ℝ) * Real.log P)⌉₊

lemma paddingCutoff_square_lower (P : ℕ) :
    512 * (P : ℝ) * Real.log P ≤ (paddingCutoff P : ℝ) ^ 2 := by
  have hnonneg : 0 ≤ 512 * (P : ℝ) * Real.log P := by
    exact mul_nonneg (by positivity) (Real.log_natCast_nonneg P)
  have hle := Nat.le_ceil (Real.sqrt (512 * (P : ℝ) * Real.log P))
  have hs := Real.sq_sqrt hnonneg
  have hspos := Real.sqrt_nonneg (512 * (P : ℝ) * Real.log P)
  change Real.sqrt (512 * (P : ℝ) * Real.log P) ≤ (paddingCutoff P : ℝ) at hle
  nlinarith

lemma paddingCutoff_square_upper {P : ℕ} (hP : 1 ≤ P) (hlog : 1 ≤ Real.log P) :
    (paddingCutoff P : ℝ) ^ 2 ≤ 2048 * (P : ℝ) * Real.log P := by
  have hPr : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hnonneg : 0 ≤ 512 * (P : ℝ) * Real.log P := by positivity
  have hs := Real.sq_sqrt hnonneg
  have hspos := Real.sqrt_nonneg (512 * (P : ℝ) * Real.log P)
  have hsone : 1 ≤ Real.sqrt (512 * (P : ℝ) * Real.log P) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hceil := Nat.ceil_lt_add_one hspos
  change (paddingCutoff P : ℝ) < Real.sqrt (512 * (P : ℝ) * Real.log P) + 1 at hceil
  have hBpos : (0 : ℝ) ≤ paddingCutoff P := by positivity
  nlinarith

lemma paddingCutoff_tendsto : Tendsto paddingCutoff atTop atTop := by
  have htlog : Tendsto (fun P : ℕ => Real.log P) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htg : Tendsto (fun P : ℕ => 512 * (P : ℝ) * Real.log P) atTop atTop :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop
      (by norm_num : (0 : ℝ) < 512)).atTop_mul_atTop₀ htlog
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [(Real.tendsto_sqrt_atTop.comp htg).eventually
    (eventually_ge_atTop (b : ℝ))] with P hP
  have hh : (b : ℝ) ≤ (paddingCutoff P : ℝ) := hP.trans (Nat.le_ceil _)
  exact Nat.cast_le.mp hh

/-- For all sufficiently large `P`, the padding cutoff lies below `P`, has
weight at least `2P`, and its square is at most a constant times `P log P`. -/
theorem eventually_paddingCutoff_bounds :
    ∀ᶠ P : ℕ in atTop, paddingCutoff P < P ∧
      2 * P ≤ primeWeightSum (paddingCutoff P) ∧
      (paddingCutoff P : ℝ) ^ 2 ≤ 2048 * P * Real.log P := by
  have htlog : Tendsto (fun P : ℕ => Real.log P) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htdiv : Tendsto (fun P : ℕ => Real.log P / P) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1, htlog.eventually (eventually_ge_atTop 1),
    (tendsto_order.mp htdiv).2 (1 / 2048) (by norm_num),
    paddingCutoff_tendsto.eventually eventually_primeWeightSum_lower,
    paddingCutoff_tendsto.eventually (eventually_ge_atTop 1)] with P hP hlog hratio hweight hB
  have hPr : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hBpos : (0 : ℝ) < paddingCutoff P := by exact_mod_cast (show 0 < paddingCutoff P by omega)
  have hu := paddingCutoff_square_upper hP hlog
  have hl := paddingCutoff_square_lower P
  have hlogsmall : 2048 * Real.log P < P := by
    rw [div_lt_iff₀ hPr] at hratio
    linarith
  have hlt : paddingCutoff P < P := by
    have hlt' : (paddingCutoff P : ℝ) < P := by
      have hh := mul_lt_mul_of_pos_left hlogsmall hPr
      nlinarith
    exact_mod_cast hlt'
  refine ⟨hlt, ?_, hu⟩
  have hlogle : Real.log (paddingCutoff P) ≤ Real.log P :=
    Real.log_le_log hBpos (by exact_mod_cast hlt.le)
  have hw := mul_le_mul_of_nonneg_left hlogle
    (show (0 : ℝ) ≤ 128 * primeWeightSum (paddingCutoff P) by positivity)
  have hW : (2 : ℝ) * P ≤ primeWeightSum (paddingCutoff P) := by
    nlinarith
  exact_mod_cast hW

end Erdos1189
