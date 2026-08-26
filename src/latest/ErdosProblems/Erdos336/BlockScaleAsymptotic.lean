import Mathlib
import ErdosProblems.Erdos336.ConditionalFiniteStructure

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Asymptotics of the explicit block-scale finite bound
-/

namespace Erdos336

open Filter Topology

/-- The canonical block index. -/
def removalBlockIndex (h : ℕ) : ℕ := Nat.log 128 (h + 1) + 1

/-- The finite cost supplied conditionally by F-068. -/
def structuralRemovalCost (h : ℕ) : ℕ :=
  2 ^ 26 * (h * 64 ^ removalBlockIndex h) + extensionRankOneCost h

lemma removalBlockIndex_pos (h : ℕ) : 0 < removalBlockIndex h := by
  dsimp [removalBlockIndex]
  omega

lemma removalBlockIndex_covers (h : ℕ) :
    h + 1 < 128 ^ removalBlockIndex h := by
  simpa [removalBlockIndex, Nat.succ_eq_add_one] using
    (Nat.lt_pow_succ_log_self (b := 128) (by omega) (h + 1))

lemma tendsto_log128_succ :
    Tendsto (fun h : ℕ => Nat.log 128 (h + 1)) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro k
  filter_upwards [eventually_ge_atTop (128 ^ k)] with h hh
  calc
    k = Nat.log 128 (128 ^ k) := by rw [Nat.log_pow (by omega)]
    _ ≤ Nat.log 128 (h + 1) :=
      Nat.log_monotone (le_trans hh (Nat.le_add_right h 1))

lemma blockMultiplier_ratio_bound {h : ℕ} (hh : 1 ≤ h) :
    ((64 ^ removalBlockIndex h : ℕ) : ℝ) / (h : ℝ) ≤
      128 * ((1 / 2 : ℝ) ^ (Nat.log 128 (h + 1))) := by
  let n := Nat.log 128 (h + 1)
  have hpow : 128 ^ n ≤ h + 1 := by
    exact Nat.pow_log_le_self 128 (by omega)
  have hh2 : h + 1 ≤ 2 * h := by omega
  have hdenNat : 128 ^ n ≤ 2 * h := le_trans hpow hh2
  have hden : ((128 ^ n : ℕ) : ℝ) ≤ 2 * (h : ℝ) := by
    exact_mod_cast hdenNat
  have hhR : (0 : ℝ) < h := by positivity
  have hpR : (0 : ℝ) < (128 : ℝ) ^ n := by positivity
  change (((64 ^ (n + 1) : ℕ) : ℝ) / (h : ℝ) ≤
    128 * ((1 / 2 : ℝ) ^ n))
  push_cast at hden ⊢
  rw [pow_succ]
  have hratio : (64 : ℝ) ^ n / (128 : ℝ) ^ n = (1 / 2 : ℝ) ^ n := by
    rw [← div_pow]
    norm_num
  rw [← hratio]
  rw [show 128 * ((64 : ℝ) ^ n / (128 : ℝ) ^ n) =
      (128 * (64 : ℝ) ^ n) / (128 : ℝ) ^ n by ring]
  apply (div_le_div_iff₀ hhR hpR).2
  have hmul := mul_le_mul_of_nonneg_left hden
    (show (0 : ℝ) ≤ (64 : ℝ) ^ n by positivity)
  nlinarith

lemma tendsto_blockMultiplier_ratio_zero :
    Tendsto (fun h : ℕ => ((64 ^ removalBlockIndex h : ℕ) : ℝ) / (h : ℝ))
      atTop (𝓝 0) := by
  have hgeom : Tendsto
      (fun h : ℕ => 128 * ((1 / 2 : ℝ) ^ (Nat.log 128 (h + 1))))
      atTop (𝓝 0) := by
    have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hc := hp.comp tendsto_log128_succ
    simpa using (tendsto_const_nhds.mul hc :
      Tendsto (fun h : ℕ => 128 * ((1 / 2 : ℝ) ^ Nat.log 128 (h + 1)))
        atTop (𝓝 (128 * 0)))
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hzero hgeom
  · filter_upwards with h
    positivity
  · filter_upwards [eventually_ge_atTop 1] with h hh
    exact blockMultiplier_ratio_bound hh

lemma tendsto_structural_overhead_zero :
    Tendsto
      (fun h : ℕ =>
        ((2 ^ 26 * (h * 64 ^ removalBlockIndex h) : ℕ) : ℝ) /
          (h : ℝ) ^ 2)
      atTop (𝓝 0) := by
  have hc : Tendsto (fun _ : ℕ => ((2 ^ 26 : ℕ) : ℝ)) atTop
      (𝓝 ((2 ^ 26 : ℕ) : ℝ)) := tendsto_const_nhds
  have hm := hc.mul tendsto_blockMultiplier_ratio_zero
  have hm0 : Tendsto
      (fun h : ℕ => ((2 ^ 26 : ℕ) : ℝ) *
        (((64 ^ removalBlockIndex h : ℕ) : ℝ) / (h : ℝ)))
      atTop (𝓝 0) := by simpa using hm
  apply hm0.congr'
  filter_upwards [eventually_ge_atTop 1] with h hh
  have hhR : (h : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

lemma tendsto_extensionRankOneCost_third :
    Tendsto (fun h : ℕ => (extensionRankOneCost h : ℝ) / (h : ℝ) ^ 2)
      atTop (𝓝 (1 / 3 : ℝ)) := by
  let lower : ℕ → ℝ := fun h => (1 / 3 : ℝ)
  let upper : ℕ → ℝ := fun h =>
    (1 / 3 : ℝ) + 2 / (h : ℝ) + (11 / 3 : ℝ) / (h : ℝ) ^ 2
  have hinv : Tendsto (fun h : ℕ => (1 : ℝ) / (h : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) 1
  have hinv2 : Tendsto (fun h : ℕ => (1 : ℝ) / (h : ℝ) ^ 2)
      atTop (𝓝 0) := by
    simpa [div_pow] using hinv.pow 2
  have hlower : Tendsto lower atTop (𝓝 (1 / 3 : ℝ)) := tendsto_const_nhds
  have hupper : Tendsto upper atTop (𝓝 (1 / 3 : ℝ)) := by
    have hconst2 : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2) :=
      tendsto_const_nhds
    have hconst11 : Tendsto (fun _ : ℕ => (11 / 3 : ℝ)) atTop
        (𝓝 (11 / 3 : ℝ)) := tendsto_const_nhds
    have htwo : Tendsto (fun h : ℕ => (2 : ℝ) * (1 / (h : ℝ)))
        atTop (𝓝 0) := by simpa using hconst2.mul hinv
    have heleven : Tendsto
        (fun h : ℕ => (11 / 3 : ℝ) * (1 / (h : ℝ) ^ 2))
        atTop (𝓝 0) := by simpa using hconst11.mul hinv2
    simpa [upper, div_eq_mul_inv] using
      (tendsto_const_nhds.add htwo).add heleven
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_ge_atTop 1] with h hh
    have hceil := extensionRankOneCost_ceiling h
    have hhpos : (0 : ℝ) < (h : ℝ) ^ 2 := by positivity
    apply (le_div_iff₀ hhpos).2
    have hnat : h ^ 2 ≤ 3 * extensionRankOneCost h :=
      le_trans (Nat.pow_le_pow_left (Nat.le_add_right h 3) 2) hceil
    have hreal : (h : ℝ) ^ 2 ≤ 3 * extensionRankOneCost h := by
      exact_mod_cast hnat
    dsimp [lower]
    nlinarith
  · filter_upwards [eventually_ge_atTop 1] with h hh
    have hbound := extensionRankOneCost_bound h
    have hhpos : (0 : ℝ) < (h : ℝ) ^ 2 := by positivity
    apply (div_le_iff₀ hhpos).2
    have hboundR : (3 : ℝ) * extensionRankOneCost h ≤
        (h : ℝ) ^ 2 + 6 * h + 11 := by exact_mod_cast hbound
    have hhne : (h : ℝ) ≠ 0 := by positivity
    have hident : upper h * (h : ℝ) ^ 2 =
        (h : ℝ) ^ 2 / 3 + 2 * h + 11 / 3 := by
      dsimp [upper]
      field_simp
    rw [hident]
    nlinarith

/-- The explicit conditional finite cost has normalized limit `1/3`. -/
theorem tendsto_structuralRemovalCost_third :
    Tendsto (fun h : ℕ => (structuralRemovalCost h : ℝ) / (h : ℝ) ^ 2)
      atTop (𝓝 (1 / 3 : ℝ)) := by
  have hs := tendsto_structural_overhead_zero.add
    tendsto_extensionRankOneCost_third
  have hs' : Tendsto
      (fun h : ℕ =>
        ((2 ^ 26 * (h * 64 ^ removalBlockIndex h) : ℕ) : ℝ) / (h : ℝ) ^ 2 +
          (extensionRankOneCost h : ℝ) / (h : ℝ) ^ 2)
      atTop (𝓝 (1 / 3 : ℝ)) := by simpa using hs
  apply hs'.congr'
  filter_upwards [eventually_ge_atTop 1] with h hh
  dsimp [structuralRemovalCost]
  push_cast
  have hhR : (h : ℝ) ≠ 0 := by positivity
  field_simp

/-- Assuming the one structural input, the explicit cost is an eventual
cyclic removal bound. -/
theorem eventually_cyclicRemovalBound_structuralCost
    (hstruct : HasHighPowerRankDenseStructure) :
    ∀ᶠ h : ℕ in atTop, CyclicRemovalBound h (structuralRemovalCost h) := by
  filter_upwards [eventually_ge_atTop 15] with h hh
  simpa [structuralRemovalCost] using
    cyclicRemovalBound_of_structure_block hstruct hh
      (removalBlockIndex_pos h) (removalBlockIndex_covers h)

end Erdos336
