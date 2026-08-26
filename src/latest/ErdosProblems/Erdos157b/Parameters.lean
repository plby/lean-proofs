import ErdosProblems.Erdos157.PrefixParameters
import Mathlib.Analysis.Real.Sqrt

/-!
Polynomial-sized tag spaces and a fourth-root prefix for the binary construction.
Integer rounding is deliberately expressed using `Nat.clog` and `Nat.sqrt`.
-/

namespace Erdos157.Binary

open Filter Elementary
open scoped Topology

def tagDimension (i : ℕ) : ℕ := 1 + 40 * Nat.clog 7 (i + 1)

def prefixLength (k : ℕ) : ℕ := Nat.sqrt (Nat.sqrt k) + 1

def trialCount (k : ℕ) : ℕ := k ^ 10

theorem tagDimension_pos (i : ℕ) : 0 < tagDimension i := by unfold tagDimension; omega

theorem tagDimension_mono : Monotone tagDimension := by
  intro i j hij
  have h := Nat.clog_mono_right 7 (Nat.add_le_add_right hij 1)
  unfold tagDimension
  omega

theorem tag_card_lower (i : ℕ) : 7 * (i + 1) ^ 40 ≤ 7 ^ tagDimension i := by
  have h := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 7) (i + 1)) 40
  calc
    _ ≤ 7 * (7 ^ Nat.clog 7 (i + 1)) ^ 40 := Nat.mul_le_mul_left 7 h
    _ = _ := by rw [← pow_mul, mul_comm (Nat.clog 7 (i + 1)) 40, tagDimension, pow_add]; simp

theorem prefixLength_pos (k : ℕ) : 0 < prefixLength k := by unfold prefixLength; omega

theorem level_le_prefix_fourth (k : ℕ) : k ≤ prefixLength k ^ 4 := by
  have h₁ : k ≤ (Nat.sqrt k + 1) ^ 2 := (Nat.succ_le_succ_sqrt' k).trans' (by omega)
  have h₂ : Nat.sqrt k + 1 ≤ prefixLength k ^ 2 := Nat.succ_le_succ_sqrt' (Nat.sqrt k)
  calc
    _ ≤ (Nat.sqrt k + 1) ^ 2 := h₁
    _ ≤ (prefixLength k ^ 2) ^ 2 := Nat.pow_le_pow_left h₂ 2
    _ = _ := by ring

theorem enough_high_tags (k i : ℕ) (hi : prefixLength k ≤ i) :
    7 * trialCount k ≤ 7 ^ tagDimension i := by
  have h : k ≤ (i + 1) ^ 4 :=
    (level_le_prefix_fourth k).trans (Nat.pow_le_pow_left (by omega) 4)
  calc
    _ ≤ 7 * ((i + 1) ^ 4) ^ 10 := Nat.mul_le_mul_left 7 (Nat.pow_le_pow_left h 10)
    _ = 7 * (i + 1) ^ 40 := by rw [← pow_mul]
    _ ≤ _ := tag_card_lower i

theorem prefixDegree_le_sqrt (k : ℕ) :
    (prefixLength k : ℝ) ^ 2 ≤ 2 * (Nat.sqrt k : ℝ) + 2 := by
  have hs : (Nat.sqrt (Nat.sqrt k) : ℝ) ^ 2 ≤ Nat.sqrt k := by
    exact_mod_cast Nat.sqrt_le' (Nat.sqrt k)
  dsimp only [prefixLength]
  push_cast
  nlinarith [sq_nonneg ((Nat.sqrt (Nat.sqrt k) : ℝ) - 1)]

theorem tendsto_natSqrt_div_self :
    Tendsto (fun k : ℕ => (Nat.sqrt k : ℝ) / k) atTop (𝓝 0) := by
  have hu : Tendsto (fun k : ℕ => Real.sqrt (k : ℝ) / k) atTop (𝓝 0) := by
    simp_rw [Real.sqrt_div_self]
    exact tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  apply squeeze_zero (fun k => by positivity) _ hu
  intro k
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg k)
  apply (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr
  exact_mod_cast Nat.sqrt_le' k

theorem tendsto_prefixDegree_div_level :
    Tendsto (fun k : ℕ => (prefixLength k : ℝ) ^ 2 / k) atTop (𝓝 0) := by
  have hconstant : Tendsto (fun k : ℕ => (2 : ℝ) / k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun k : ℕ => (2 * (Nat.sqrt k : ℝ) + 2) / k) atTop (𝓝 0) := by
    convert (tendsto_natSqrt_div_self.const_mul 2).add hconstant using 1
    · ext k
      ring
    · norm_num
  exact squeeze_zero (fun k => by positivity)
    (fun k => div_le_div_of_nonneg_right (prefixDegree_le_sqrt k) (Nat.cast_nonneg k)) hu

theorem tagDimension_le_log (i : ℕ) :
    (tagDimension i : ℝ) ≤ 40 * Real.logb 7 (i + 1) + 41 := by
  have hlog : 0 ≤ Real.logb 7 (i + 1 : ℝ) :=
    Real.logb_nonneg (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) i; linarith)
  have hc : (Nat.clog 7 (i + 1) : ℝ) ≤ Real.logb 7 (i + 1 : ℝ) + 1 := by
    rw [← Real.natCeil_logb_natCast]
    push_cast
    exact (Nat.ceil_lt_add_one hlog).le
  dsimp only [tagDimension]
  push_cast
  linarith

theorem tendsto_tagDimension_div_level :
    Tendsto (fun k : ℕ => (tagDimension k : ℝ) / k) atTop (𝓝 0) := by
  have hcast : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun k : ℕ => Real.logb 7 (k + 1 : ℝ) / k) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_logb_div_mul_add_atTop (b := 7) 1 0 1 one_ne_zero).comp
      (hcast.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
    have hr : Tendsto (fun k : ℕ => (k + 1 : ℝ) / k) atTop (𝓝 1) := by
      have hz : Tendsto (fun k : ℕ => (1 : ℝ) / k) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hcast
      have hh : Tendsto (fun k : ℕ => (1 : ℝ) + 1 / k) atTop (𝓝 1) := by
        simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add hz
      apply hh.congr'
      filter_upwards [eventually_ge_atTop 1] with k hk
      have hn : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      field_simp
    have hh := h.mul hr
    convert hh using 1
    · ext k
      simp only [Function.comp_def, one_mul, add_zero, pow_one]
      have hp : (k + 1 : ℝ) ≠ 0 := by positivity
      field_simp
    · norm_num
  have hc : Tendsto (fun k : ℕ => (41 : ℝ) / k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hcast
  have hu : Tendsto (fun k : ℕ => (40 * Real.logb 7 (k + 1 : ℝ) + 41) / k) atTop (𝓝 0) := by
    convert (hlog.const_mul 40).add hc using 1
    · ext k
      ring
    · norm_num
  exact squeeze_zero (fun k => by positivity)
    (fun k => div_le_div_of_nonneg_right (tagDimension_le_log k) (Nat.cast_nonneg k)) hu

end Erdos157.Binary
