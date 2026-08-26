/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Asymptotic density of the cardinalities of the counting frames.
Informal argument: use integer parameters and n(x+1)/n(x) tending to one;
no uniqueness of coordinate scores is required.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.CountingLoss

namespace Erdos1189

open Filter Asymptotics
open scoped Asymptotics

lemma realLogPower_shift_ratio (r : ℕ) :
    Tendsto (fun x : ℝ => realLogPower r (x + 1) / realLogPower r x) atTop (nhds 1) := by
  have heq : (fun x : ℝ => x + 1) ~[atTop] (fun x : ℝ => x) :=
    IsEquivalent.refl.add_const_of_norm_tendsto_atTop tendsto_norm_atTop_atTop
  have h := (heq.pow r).div (heq.log tendsto_id)
  change (fun x : ℝ => (x + 1) ^ r / Real.log (x + 1)) ~[atTop]
    (fun x : ℝ => x ^ r / Real.log x) at h
  exact (isEquivalent_iff_tendsto_one (realLogPower_eventually_ne_zero r)).mp h

lemma countingSize_shift_ratio :
    Tendsto (fun x : ℝ => (countingSize (x + 1) : ℝ) / countingSize x)
      atTop (nhds 1) := by
  have hshift : Tendsto (fun x : ℝ => x + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_id
  have hc : tau / 2 ≠ 0 := (div_pos tau_pos (by norm_num)).ne'
  have ht := ((countingSize_asymptotic.comp hshift).div countingSize_asymptotic hc).mul
    (realLogPower_shift_ratio 2)
  simp only [div_self hc, one_mul] at ht
  apply ht.congr'
  filter_upwards [realLogPower_eventually_ne_zero 2,
    hshift.eventually (realLogPower_eventually_ne_zero 2)] with x hx hx1
  dsimp only [Pi.div_apply, Function.comp_apply]
  field_simp

lemma exists_larger_frame_size (k : ℕ) : ∃ j : ℕ, k < countingSize ((j : ℝ) + 1) := by
  have hshift : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  exact ((countingSize_tendsto.comp hshift).eventually (eventually_gt_atTop k)).exists

noncomputable def precedingFrameIndex (k : ℕ) : ℕ := Nat.find (exists_larger_frame_size k)

lemma precedingFrameIndex_upper (k : ℕ) :
    k < countingSize ((precedingFrameIndex k : ℝ) + 1) :=
  Nat.find_spec (exists_larger_frame_size k)

lemma countingSize_zero : countingSize 0 = 1 := by
  rw [countingSize_eq]
  have hcoords : countingCoordinates 0 = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro c hc
    have h := (mem_countingCoordinates.mp hc).2
    have hp := coordinateScore_pos (mem_countingCoordinates.mp hc).1 c.2
    linarith
  simp only [hcoords, Finset.sum_empty, add_zero]

lemma precedingFrameIndex_lower {k : ℕ} (hk : 1 ≤ k) :
    countingSize (precedingFrameIndex k : ℝ) ≤ k := by
  by_cases hj : precedingFrameIndex k = 0
  · simpa only [hj, Nat.cast_zero, countingSize_zero] using hk
  · by_contra hnot
    have hjpos : 0 < precedingFrameIndex k := Nat.pos_of_ne_zero hj
    have hcast : ((precedingFrameIndex k - 1 : ℕ) : ℝ) + 1 = precedingFrameIndex k := by
      rw [Nat.cast_sub hjpos, Nat.cast_one]
      ring
    have hsmall : k < countingSize (((precedingFrameIndex k - 1 : ℕ) : ℝ) + 1) := by
      rw [hcast]
      omega
    have hmin := Nat.find_min' (exists_larger_frame_size k) hsmall
    change precedingFrameIndex k ≤ precedingFrameIndex k - 1 at hmin
    omega

lemma precedingFrameIndex_tendsto : Tendsto precedingFrameIndex atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [eventually_ge_atTop (countingSize ((N : ℝ) + 1))] with k hk
  by_contra hnot
  have hidx : (precedingFrameIndex k : ℝ) + 1 ≤ (N : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right (le_of_not_ge hnot) 1
  have h := (precedingFrameIndex_upper k).trans_le (countingSize_mono hidx)
  omega

lemma precedingFrameIndex_real_tendsto :
    Tendsto (fun k : ℕ => (precedingFrameIndex k : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp precedingFrameIndex_tendsto

lemma precedingFrameSize_ratio :
    Tendsto (fun k : ℕ => (countingSize (precedingFrameIndex k : ℝ) : ℝ) / k)
      atTop (nhds 1) := by
  have hratio := (countingSize_shift_ratio.comp precedingFrameIndex_real_tendsto).inv₀
    (by norm_num : (1 : ℝ) ≠ 0)
  simp only [inv_one, Function.comp_apply, inv_div] at hratio
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hratio tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hupper : (k : ℝ) ≤ countingSize ((precedingFrameIndex k : ℝ) + 1) := by
      exact_mod_cast (precedingFrameIndex_upper k).le
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hk0 hupper
  · filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    apply (div_le_one hk0).mpr
    exact_mod_cast precedingFrameIndex_lower hk

end Erdos1189
