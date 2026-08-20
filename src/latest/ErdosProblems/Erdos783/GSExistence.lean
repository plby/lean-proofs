/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos783.GSSection61

/-! # The canonical Granville--Soundararajan Volterra solution

This module constructs the canonical solution of the continuous sieve equation
as the locally finite alternating moment expansion.  Local finiteness makes the
formula continuous without any appeal to an infinite-series convergence
argument.
-/

open MeasureTheory Set Finset Filter
open scoped Convolution Topology

namespace Erdos783

noncomputable section

lemma continuousOn_gsMoment
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (n : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    ContinuousOn (gsMoment chi n) (Icc (0 : ℝ) K) := by
  induction n with
  | zero => exact continuousOn_const
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        simpa only [Nat.zero_add, Nat.add_eq, Nat.succ_eq_add_one] using
          continuousOn_gsMoment_one_Icc hchi hK
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        let clamp : ℝ → ℝ := fun x => min K (max 0 x)
        let g : ℝ → ℝ := fun x => gsMoment chi n (clamp x)
        let L : ℝ := K + 1
        have hclamp : Continuous clamp := by
          dsimp only [clamp]
          fun_prop
        have hclampMem : ∀ x : ℝ, clamp x ∈ Icc (0 : ℝ) K := by
          intro x
          dsimp only [clamp]
          constructor <;> simp [hK]
        have hg : Continuous g := by
          simpa only [g, Function.comp_def] using
            ih.comp_continuous hclamp hclampMem
        have hgBound : BddAbove (Set.range fun x => ‖g x‖) := by
          let B : ℝ := max 1 (gsLogScale chi (max 1 K) ^ n)
          refine ⟨B, ?_⟩
          rintro _ ⟨x, rfl⟩
          have hU : 1 ≤ max 1 K := le_max_left _ _
          have hcl0 : 0 ≤ clamp x := (hclampMem x).1
          have hclU : clamp x ≤ max 1 K :=
            (hclampMem x).2.trans (le_max_right _ _)
          have hmMono := gsMoment_mono_Ici_zero hchi n
            (mem_Ici.mpr hcl0) (mem_Ici.mpr (zero_le_one.trans hU)) hclU
          have hm := hmMono.trans (gsMoment_le_logScale_pow hchi n hU)
          have hm0 := gsMoment_nonneg hchi n hcl0
          dsimp only [g, B]
          rw [Real.norm_eq_abs, abs_of_nonneg hm0]
          exact hm.trans (le_max_right _ _)
        have hL : 1 ≤ L := by dsimp only [L]; linarith
        have hd : Integrable (gsDefectLocal chi L) :=
          integrable_gsDefectLocal hchi hL
        have hconv : Continuous
            (gsDefectLocal chi L ⋆[ContinuousLinearMap.mul ℝ ℝ] g) :=
          hgBound.continuous_convolution_right_of_integrable
            (ContinuousLinearMap.mul ℝ ℝ) hd hg
        apply hconv.continuousOn.congr
        intro x hx
        have hxL : x < L := by dsimp only [L]; linarith [hx.2]
        have hrec := gsDefectLocal_convolution_momentLocal hchi n hx.1 hxL
        rw [← hrec]
        rw [convolution_def]
        apply integral_congr_ae
        filter_upwards with t
        by_cases ht : t ∈ Ioo (0 : ℝ) L
        · rw [gsDefectLocal, gsLocalize, indicator_of_mem ht]
          by_cases htx : t ≤ x
          · have hsub : x - t ∈ Icc (0 : ℝ) K := by
              exact ⟨sub_nonneg.mpr htx, (sub_le_self _ ht.1.le).trans hx.2⟩
            have hclampEq : clamp (x - t) = x - t := by
              dsimp only [clamp]
              simp [hsub.1, hsub.2]
            dsimp only [g]
            rw [hclampEq]
            by_cases heq : t = x
            · subst t
              simp [gsMomentLocal, gsLocalize,
                gsMoment_eq_zero_of_le_one chi hn1]
            · have hmem : x - t ∈ Ioo (0 : ℝ) L :=
                ⟨sub_pos.mpr (lt_of_le_of_ne htx heq), by
                  linarith [ht.1, hx.2]⟩
              rw [gsMomentLocal, gsLocalize, indicator_of_mem hmem]
          · have hneg : x - t < 0 := sub_neg.mpr (lt_of_not_ge htx)
            have hclampZero : clamp (x - t) = 0 := by
              dsimp only [clamp]
              simp [hneg.le, hK]
            have hmzero : gsMoment chi n 0 = 0 :=
              gsMoment_eq_zero_of_le_one chi hn1 (by norm_num) (by norm_num)
            have hnot : x - t ∉ Ioo (0 : ℝ) L := by
              intro hmem
              exact (not_lt_of_ge hneg.le) hmem.1
            rw [gsMomentLocal, gsLocalize, Set.indicator_of_notMem hnot]
            dsimp only [g]
            rw [hclampZero, hmzero]
        · rw [gsDefectLocal, gsLocalize, Set.indicator_of_notMem ht]
          simp

lemma continuousOn_gsMoment_Ici
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (n : ℕ) :
    ContinuousOn (gsMoment chi n) (Ici (0 : ℝ)) := by
  intro x hx
  change 0 ≤ x at hx
  let K : ℝ := x + 1
  have hK0 : 0 ≤ K := by dsimp only [K]; linarith [hx]
  have hxK : x < K := by dsimp only [K]; linarith
  have hlocal := continuousOn_gsMoment hchi n hK0
  apply (hlocal x ⟨hx, hxK.le⟩).mono_of_mem_nhdsWithin
  rw [← Ici_inter_Iic]
  apply inter_mem self_mem_nhdsWithin
  exact mem_nhdsWithin_of_mem_nhds
    (mem_of_superset (Iio_mem_nhds hxK) Iio_subset_Iic_self)

lemma test_continuousOn_gsAlternatingMomentSum
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (N : ℕ) :
    ContinuousOn (gsAlternatingMomentSum chi N) (Ici (0 : ℝ)) := by
  unfold gsAlternatingMomentSum
  refine continuousOn_finsetSum _ fun j _ => ?_
  exact (continuousOn_const.mul
    (continuousOn_gsMoment_Ici hchi j)).div_const _

lemma gsAlternatingMomentSum_stable
    {chi : ℝ → ℝ} {m n : ℕ} {u : ℝ}
    (hu0 : 0 ≤ u) (hmn : m ≤ n) (hum : u < (m : ℝ) + 1) :
    gsAlternatingMomentSum chi m u = gsAlternatingMomentSum chi n u := by
  unfold gsAlternatingMomentSum
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hmn))
  intro j hjn hjm
  have hmj : m < j := by
    have hjm' : ¬j < m + 1 := by
      simpa only [Finset.mem_range] using hjm
    omega
  have huj : u < (j : ℝ) := by
    have hmjR : (m : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hmj
    exact hum.trans_le hmjR
  rw [gsMoment_eq_zero_of_lt hu0 huj, mul_zero, zero_div]

def gsCanonicalSolution (chi : ℝ → ℝ) (u : ℝ) : ℝ :=
  gsAlternatingMomentSum chi ⌈u⌉₊ u

lemma gsCanonicalSolution_eq_fixed
    {chi : ℝ → ℝ} {u : ℝ} (hu0 : 0 ≤ u) {N : ℕ}
    (huN : u ≤ (N : ℝ)) :
    gsCanonicalSolution chi u = gsAlternatingMomentSum chi N u := by
  apply gsAlternatingMomentSum_stable hu0
  · exact Nat.ceil_le.mpr huN
  · exact (Nat.le_ceil u).trans_lt (lt_add_one _)

theorem isGSSolution_gsCanonicalSolution
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) :
    IsGSSolution chi (gsCanonicalSolution chi) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    let N : ℕ := ⌈x + 1⌉₊
    have hxN : x ≤ (N : ℝ) := by
      dsimp only [N]
      exact (show x ≤ x + 1 by linarith).trans (Nat.le_ceil (x + 1))
    have hfixed := test_continuousOn_gsAlternatingMomentSum hchi N
    have heq : ∀ᶠ y in 𝓝[Ici (0 : ℝ)] x,
        gsCanonicalSolution chi y = gsAlternatingMomentSum chi N y := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds
          (Iio_mem_nhds (show x < x + 1 by linarith)),
        self_mem_nhdsWithin] with y hy hy0
      apply gsCanonicalSolution_eq_fixed hy0
      have hyN0 : y ≤ x + 1 := hy.le
      exact hyN0.trans (Nat.le_ceil (x + 1))
    exact (hfixed x hx).congr_of_eventuallyEq heq
      (gsCanonicalSolution_eq_fixed hx hxN)
  · intro u hu0 hu1
    unfold gsCanonicalSolution
    exact gsAlternatingMomentSum_eq_one_of_le_one chi ⌈u⌉₊ hu0 hu1
  · intro u hu1
    have hu0 : 0 ≤ u := zero_le_one.trans hu1
    let N : ℕ := ⌈u⌉₊
    have huN : u ≤ (N : ℝ) := by
      dsimp only [N]
      exact Nat.le_ceil u
    have huLt : u < (N : ℝ) + 1 := by
      dsimp only [N]
      exact (Nat.le_ceil u).trans_lt (lt_add_one _)
    have heq := gs_alternatingMomentSum_equation_of_lt hchi N hu0 huLt
    have hcanonU : gsCanonicalSolution chi u =
        gsAlternatingMomentSum chi N u := gsCanonicalSolution_eq_fixed hu0 huN
    calc
      u * gsCanonicalSolution chi u =
          u * gsAlternatingMomentSum chi N u := by rw [hcanonU]
      _ = ∫ t in 0..u, chi t * gsAlternatingMomentSum chi N (u - t) :=
        heq.symm
      _ = ∫ t in 0..u, chi t * gsCanonicalSolution chi (u - t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hu0] at ht
        have hut0 : 0 ≤ u - t := sub_nonneg.mpr ht.2
        have hutN : u - t ≤ (N : ℝ) :=
          (sub_le_self _ ht.1).trans huN
        change chi t * gsAlternatingMomentSum chi N (u - t) =
          chi t * gsCanonicalSolution chi (u - t)
        rw [gsCanonicalSolution_eq_fixed hut0 hutN]

end

end Erdos783
