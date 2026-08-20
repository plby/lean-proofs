/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos783.GSMomentConvolution

/-! # Bounded local uniqueness for the GS Volterra equation -/

open MeasureTheory Set

namespace Erdos783

noncomputable section

/-- Two bounded normalized solutions of the GS equation agree on a compact
interval.  No continuity of the second function is assumed.  On each unit
interval the homogeneous equation contracts the supremum norm by at most
`1/(n+1)`; a `sSup` argument avoids requiring that the supremum be attained. -/
theorem gs_local_solution_unique_of_bounded
    {chi sigma tau : ℝ → ℝ} (hchi : IsGSKernel chi)
    {U B : ℝ} (hU : 0 ≤ U)
    (hsigmaOne : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → sigma u = 1)
    (htauOne : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → tau u = 1)
    (hsigmaEq : ∀ u : ℝ, 1 ≤ u → u ≤ U →
      u * sigma u = ∫ t : ℝ in 0..u, chi t * sigma (u - t))
    (htauEq : ∀ u : ℝ, 1 ≤ u → u ≤ U →
      u * tau u = ∫ t : ℝ in 0..u, chi t * tau (u - t))
    (hsigmaInt : ∀ u : ℝ, 1 ≤ u → u ≤ U →
      IntervalIntegrable (fun t : ℝ ↦ chi t * sigma (u - t)) volume 0 u)
    (htauInt : ∀ u : ℝ, 1 ≤ u → u ≤ U →
      IntervalIntegrable (fun t : ℝ ↦ chi t * tau (u - t)) volume 0 u)
    (hbound : ∀ u ∈ Icc (0 : ℝ) U, |sigma u - tau u| ≤ B) :
    ∀ u ∈ Icc (0 : ℝ) U, sigma u = tau u := by
  let d : ℝ → ℝ := fun u ↦ sigma u - tau u
  have hB0 : 0 ≤ B := by
    have h := hbound 0 ⟨le_rfl, hU⟩
    exact (abs_nonneg (sigma 0 - tau 0)).trans h
  have hdeq : ∀ u : ℝ, 1 ≤ u → u ≤ U →
      u * d u = ∫ t : ℝ in 0..u, chi t * d (u - t) := by
    intro u hu1 huU
    have hs := hsigmaEq u hu1 huU
    have ht := htauEq u hu1 huU
    have hsInt := hsigmaInt u hu1 huU
    have htInt := htauInt u hu1 huU
    dsimp only [d]
    rw [show (fun t : ℝ ↦ chi t * (sigma (u - t) - tau (u - t))) =
        (fun t ↦ chi t * sigma (u - t) - chi t * tau (u - t)) by
      funext t
      ring,
      intervalIntegral.integral_sub hsInt htInt]
    linarith
  have hstep : ∀ n : ℕ, 1 ≤ n →
      ∀ u : ℝ, 0 ≤ u → u ≤ U → u ≤ n → d u = 0 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        intro u hu0 huU hu1
        dsimp only [d]
        rw [hsigmaOne u hu0 (by simpa using hu1),
          htauOne u hu0 (by simpa using hu1)]
        ring
    | succ n hn ih =>
        intro u hu0 huU huSucc
        by_cases hun : u ≤ n
        · exact ih u hu0 huU hun
        · have hnu : (n : ℝ) < u := lt_of_not_ge hun
          have hnu' : (n : ℝ) ≤ u := hnu.le
          have hn0 : (0 : ℝ) ≤ n := by positivity
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
          let b : ℝ := min U (n + 1)
          have hub : u ≤ b := le_min huU (by exact_mod_cast huSucc)
          have hnb : (n : ℝ) ≤ b := hnu'.trans hub
          let S : Set ℝ := (fun v : ℝ ↦ |d v|) '' Icc (n : ℝ) b
          have hSne : S.Nonempty := ⟨|d u|, u, ⟨hnu', hub⟩, rfl⟩
          have hSbdd : BddAbove S := by
            refine ⟨B, ?_⟩
            intro z hz
            rcases hz with ⟨v, hv, rfl⟩
            apply hbound v
            exact ⟨hn0.trans hv.1, hv.2.trans (min_le_left _ _)⟩
          let M : ℝ := sSup S
          have hM0 : 0 ≤ M := by
            exact (abs_nonneg (d u)).trans
              (le_csSup hSbdd ⟨u, ⟨hnu', hub⟩, rfl⟩)
          have hcontract : ∀ v ∈ Icc (n : ℝ) b,
              |d v| ≤ M / (n + 1 : ℝ) := by
            intro v hv
            have hvU : v ≤ U := hv.2.trans (min_le_left _ _)
            have hvSucc : v ≤ (n : ℝ) + 1 :=
              hv.2.trans (min_le_right _ _)
            have hv0 : 0 ≤ v := hn0.trans hv.1
            let a : ℝ := v - n
            have ha0 : 0 ≤ a := sub_nonneg.mpr hv.1
            have ha1 : a ≤ 1 := by dsimp only [a]; linarith
            have hav : a ≤ v := by dsimp only [a]; linarith
            have hsInt := hsigmaInt v (hn1.trans hv.1) hvU
            have htInt := htauInt v (hn1.trans hv.1) hvU
            have hfull : IntervalIntegrable
                (fun t : ℝ ↦ chi t * d (v - t)) volume 0 v := by
              dsimp only [d]
              rw [show (fun t : ℝ ↦ chi t * (sigma (v - t) - tau (v - t))) =
                  (fun t ↦ chi t * sigma (v - t) -
                    chi t * tau (v - t)) by
                funext t
                ring]
              exact hsInt.sub htInt
            have hleft : IntervalIntegrable
                (fun t : ℝ ↦ chi t * d (v - t)) volume 0 a := by
              apply hfull.mono_set
              rw [uIcc_of_le hv0, uIcc_of_le ha0]
              exact Icc_subset_Icc le_rfl hav
            have hright : IntervalIntegrable
                (fun t : ℝ ↦ chi t * d (v - t)) volume a v := by
              apply hfull.mono_set
              rw [uIcc_of_le hv0, uIcc_of_le hav]
              exact Icc_subset_Icc ha0 le_rfl
            have hrightZero :
                (∫ t : ℝ in a..v, chi t * d (v - t)) = 0 := by
              rw [show (∫ t : ℝ in a..v, chi t * d (v - t)) =
                  ∫ _t : ℝ in a..v, (0 : ℝ) by
                apply intervalIntegral.integral_congr
                intro t ht
                rw [uIcc_of_le hav] at ht
                have harg0 : 0 ≤ v - t := sub_nonneg.mpr ht.2
                have hargn : v - t ≤ n := by
                  dsimp only [a] at ht
                  linarith [ht.1]
                change chi t * d (v - t) = 0
                rw [ih (v - t) harg0
                  ((sub_le_self _ (ha0.trans ht.1)).trans hvU) hargn]
                simp]
              simp
            have hleftNorm :
                |(∫ t : ℝ in 0..a, chi t * d (v - t))| ≤ a * M := by
              have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
                (C := M) (f := fun t : ℝ ↦ chi t * d (v - t)) (by
                  intro t ht
                  rw [uIoc_of_le ha0] at ht
                  have ht' : t ∈ Icc (0 : ℝ) a := ⟨ht.1.le, ht.2⟩
                  have hchiOne : chi t = 1 :=
                    hchi.2.2.2 t ht'.1 (ht'.2.trans ha1)
                  have harg : v - t ∈ Icc (n : ℝ) b := by
                    constructor
                    · dsimp only [a] at ht'
                      linarith [ht'.2]
                    · exact (sub_le_self _ ht'.1).trans hv.2
                  rw [hchiOne, one_mul, Real.norm_eq_abs]
                  exact le_csSup hSbdd ⟨v - t, harg, rfl⟩)
              simpa [abs_of_nonneg ha0, mul_comm] using hnorm
            have hsplit := intervalIntegral.integral_add_adjacent_intervals
              hleft hright
            have heq := hdeq v (hn1.trans hv.1) hvU
            have hmain : v * |d v| ≤ a * M := by
              calc
                v * |d v| = |v * d v| := by
                  rw [abs_mul, abs_of_nonneg hv0]
                _ = |(∫ t : ℝ in 0..v, chi t * d (v - t))| := by rw [heq]
                _ = |(∫ t : ℝ in 0..a, chi t * d (v - t))| := by
                  rw [← hsplit, hrightZero, add_zero]
                _ ≤ a * M := hleftNorm
            have hden : (0 : ℝ) < n + 1 := by positivity
            have hscaled : ((n : ℝ) + 1) * |d v| ≤ M := by
              dsimp only [a] at hmain
              have hvpos : 0 < v := lt_of_lt_of_le zero_lt_one
                (hn1.trans hv.1)
              have hmain' := mul_nonneg hden.le (sub_nonneg.mpr hmain)
              have hgap := mul_nonneg
                (mul_nonneg (by positivity : (0 : ℝ) ≤ n)
                  (sub_nonneg.mpr hvSucc)) hM0
              have hmul : v * (((n : ℝ) + 1) * |d v|) ≤ v * M := by
                nlinarith
              by_contra hnot
              have hlt : M < ((n : ℝ) + 1) * |d v| :=
                lt_of_not_ge hnot
              have hpos := mul_pos hvpos (sub_pos.mpr hlt)
              nlinarith
            exact (le_div_iff₀ hden).2 (by simpa [mul_comm] using hscaled)
          have hMle : M ≤ M / (n + 1 : ℝ) := by
            apply csSup_le hSne
            intro z hz
            rcases hz with ⟨v, hv, rfl⟩
            exact hcontract v hv
          have hMeq : M = 0 := by
            have hden : (1 : ℝ) < n + 1 := by
              exact_mod_cast Nat.lt_add_one_of_le hn
            by_cases hMz : M = 0
            · exact hMz
            · have hMpos : 0 < M := lt_of_le_of_ne hM0 (Ne.symm hMz)
              have hdiv : M / (n + 1 : ℝ) < M :=
                div_lt_self hMpos hden
              exact (not_lt_of_ge hMle hdiv).elim
          have hduM : |d u| ≤ M :=
            le_csSup hSbdd ⟨u, ⟨hnu', hub⟩, rfl⟩
          exact abs_eq_zero.mp (le_antisymm (hduM.trans_eq hMeq)
            (abs_nonneg _))
  intro u hu
  let n : ℕ := max 1 ⌈U⌉₊
  have hn1 : 1 ≤ n := le_max_left _ _
  have hUn : U ≤ n := (Nat.le_ceil U).trans (by
    exact_mod_cast (le_max_right 1 ⌈U⌉₊))
  have hd := hstep n hn1 u hu.1 hu.2 (hu.2.trans hUn)
  dsimp only [d] at hd
  linarith

/-- A bounded normalized subsolution of the GS Volterra equation lies below
the normalized solution on every compact interval.  This is the one-sided
version of `gs_local_solution_unique_of_bounded`, proved by the same
unit-interval supremum contraction. -/
theorem gs_local_subsolution_le_of_bounded
    {chi sigma tau : ℝ → ℝ} (hchi : IsGSKernel chi)
    {U B : ℝ} (hU : 0 ≤ U)
    (hbase : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → tau u ≤ sigma u)
    (hsigmaSuper : ∀ u : ℝ, 1 ≤ u → u ≤ U →
      (∫ t : ℝ in 0..u, chi t * sigma (u - t)) ≤ u * sigma u)
    (htauSub : ∀ u : ℝ, 1 ≤ u → u ≤ U →
      u * tau u ≤ ∫ t : ℝ in 0..u, chi t * tau (u - t))
    (hsigmaInt : ∀ u : ℝ, 1 ≤ u → u ≤ U →
      IntervalIntegrable (fun t : ℝ ↦ chi t * sigma (u - t)) volume 0 u)
    (htauInt : ∀ u : ℝ, 1 ≤ u → u ≤ U →
      IntervalIntegrable (fun t : ℝ ↦ chi t * tau (u - t)) volume 0 u)
    (hbound : ∀ u ∈ Icc (0 : ℝ) U, max (tau u - sigma u) 0 ≤ B) :
    ∀ u ∈ Icc (0 : ℝ) U, tau u ≤ sigma u := by
  let d : ℝ → ℝ := fun u ↦ tau u - sigma u
  have hB0 : 0 ≤ B := by
    have h := hbound 0 ⟨le_rfl, hU⟩
    exact (le_max_right (d 0) 0).trans h
  have hdeq : ∀ u : ℝ, 1 ≤ u → u ≤ U →
      u * d u ≤ ∫ t : ℝ in 0..u, chi t * d (u - t) := by
    intro u hu1 huU
    have hs := hsigmaSuper u hu1 huU
    have ht := htauSub u hu1 huU
    have hsInt := hsigmaInt u hu1 huU
    have htInt := htauInt u hu1 huU
    dsimp only [d]
    rw [show (fun t : ℝ ↦ chi t * (tau (u - t) - sigma (u - t))) =
        (fun t ↦ chi t * tau (u - t) - chi t * sigma (u - t)) by
      funext t
      ring,
      intervalIntegral.integral_sub htInt hsInt]
    linarith
  have hstep : ∀ n : ℕ, 1 ≤ n →
      ∀ u : ℝ, 0 ≤ u → u ≤ U → u ≤ n → d u ≤ 0 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        intro u hu0 huU hu1
        dsimp only [d]
        exact sub_nonpos.mpr (hbase u hu0 (by simpa using hu1))
    | succ n hn ih =>
        intro u hu0 huU huSucc
        by_cases hun : u ≤ n
        · exact ih u hu0 huU hun
        · have hnu : (n : ℝ) < u := lt_of_not_ge hun
          have hnu' : (n : ℝ) ≤ u := hnu.le
          have hn0 : (0 : ℝ) ≤ n := by positivity
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
          let b : ℝ := min U (n + 1)
          have hub : u ≤ b := le_min huU (by exact_mod_cast huSucc)
          have hnb : (n : ℝ) ≤ b := hnu'.trans hub
          let S : Set ℝ := (fun v : ℝ ↦ max (d v) 0) '' Icc (n : ℝ) b
          have hSne : S.Nonempty := ⟨max (d u) 0, u, ⟨hnu', hub⟩, rfl⟩
          have hSbdd : BddAbove S := by
            refine ⟨B, ?_⟩
            intro z hz
            rcases hz with ⟨v, hv, rfl⟩
            apply hbound v
            exact ⟨hn0.trans hv.1, hv.2.trans (min_le_left _ _)⟩
          let M : ℝ := sSup S
          have hM0 : 0 ≤ M := by
            exact (le_max_right (d u) 0).trans
              (le_csSup hSbdd ⟨u, ⟨hnu', hub⟩, rfl⟩)
          have hcontract : ∀ v ∈ Icc (n : ℝ) b,
              max (d v) 0 ≤ M / (n + 1 : ℝ) := by
            intro v hv
            have hvU : v ≤ U := hv.2.trans (min_le_left _ _)
            have hvSucc : v ≤ (n : ℝ) + 1 :=
              hv.2.trans (min_le_right _ _)
            have hv0 : 0 ≤ v := hn0.trans hv.1
            let a : ℝ := v - n
            have ha0 : 0 ≤ a := sub_nonneg.mpr hv.1
            have ha1 : a ≤ 1 := by dsimp only [a]; linarith
            have hav : a ≤ v := by dsimp only [a]; linarith
            have hsInt := hsigmaInt v (hn1.trans hv.1) hvU
            have htInt := htauInt v (hn1.trans hv.1) hvU
            have hfull : IntervalIntegrable
                (fun t : ℝ ↦ chi t * d (v - t)) volume 0 v := by
              dsimp only [d]
              rw [show (fun t : ℝ ↦ chi t * (tau (v - t) - sigma (v - t))) =
                  (fun t ↦ chi t * tau (v - t) -
                    chi t * sigma (v - t)) by
                funext t
                ring]
              exact htInt.sub hsInt
            have hleft : IntervalIntegrable
                (fun t : ℝ ↦ chi t * d (v - t)) volume 0 a := by
              apply hfull.mono_set
              rw [uIcc_of_le hv0, uIcc_of_le ha0]
              exact Icc_subset_Icc le_rfl hav
            have hright : IntervalIntegrable
                (fun t : ℝ ↦ chi t * d (v - t)) volume a v := by
              apply hfull.mono_set
              rw [uIcc_of_le hv0, uIcc_of_le hav]
              exact Icc_subset_Icc ha0 le_rfl
            have hrightUpper :
                (∫ t : ℝ in a..v, chi t * d (v - t)) ≤ 0 := by
              have hz : IntervalIntegrable (fun _t : ℝ ↦ (0 : ℝ))
                  volume a v := intervalIntegrable_const
              have hle := intervalIntegral.integral_mono_on hav hright hz (by
                intro t ht
                have harg0 : 0 ≤ v - t := sub_nonneg.mpr ht.2
                have hargn : v - t ≤ n := by
                  dsimp only [a] at ht
                  linarith [ht.1]
                have hdle := ih (v - t) harg0
                  ((sub_le_self _ (ha0.trans ht.1)).trans hvU) hargn
                exact mul_nonpos_of_nonneg_of_nonpos
                  (hchi.2.1 t (ha0.trans ht.1)) hdle)
              simpa using hle
            have hleftUpper :
                (∫ t : ℝ in 0..a, chi t * d (v - t)) ≤ a * M := by
              have hc : IntervalIntegrable (fun _t : ℝ ↦ M) volume 0 a :=
                intervalIntegrable_const
              calc
                (∫ t : ℝ in 0..a, chi t * d (v - t)) ≤
                    ∫ _t : ℝ in 0..a, M := by
                  apply intervalIntegral.integral_mono_on ha0 hleft hc
                  intro t ht
                  have hchiOne : chi t = 1 :=
                    hchi.2.2.2 t ht.1 (ht.2.trans ha1)
                  have harg : v - t ∈ Icc (n : ℝ) b := by
                    constructor
                    · dsimp only [a] at ht
                      linarith [ht.2]
                    · exact (sub_le_self _ ht.1).trans hv.2
                  rw [hchiOne, one_mul]
                  exact (le_max_left (d (v - t)) 0).trans
                    (le_csSup hSbdd ⟨v - t, harg, rfl⟩)
                _ = a * M := by simp
            have hsplit := intervalIntegral.integral_add_adjacent_intervals
              hleft hright
            have heq := hdeq v (hn1.trans hv.1) hvU
            have hmain : v * d v ≤ a * M := by
              calc
                v * d v ≤ ∫ t : ℝ in 0..v, chi t * d (v - t) := heq
                _ = (∫ t : ℝ in 0..a, chi t * d (v - t)) +
                      ∫ t : ℝ in a..v, chi t * d (v - t) := hsplit.symm
                _ ≤ a * M := by linarith
            have hden : (0 : ℝ) < n + 1 := by positivity
            by_cases hdv : d v ≤ 0
            · rw [max_eq_right hdv]
              exact div_nonneg hM0 hden.le
            · have hdv0 : 0 < d v := lt_of_not_ge hdv
              rw [max_eq_left hdv0.le]
              have hscaled : ((n : ℝ) + 1) * d v ≤ M := by
                dsimp only [a] at hmain
                have hvpos : 0 < v := lt_of_lt_of_le zero_lt_one
                  (hn1.trans hv.1)
                have hmain' := mul_nonneg hden.le (sub_nonneg.mpr hmain)
                have hgap := mul_nonneg
                  (mul_nonneg (by positivity : (0 : ℝ) ≤ n)
                    (sub_nonneg.mpr hvSucc)) hM0
                have hmul : v * (((n : ℝ) + 1) * d v) ≤ v * M := by
                  nlinarith
                by_contra hnot
                have hlt : M < ((n : ℝ) + 1) * d v := lt_of_not_ge hnot
                have hpos := mul_pos hvpos (sub_pos.mpr hlt)
                nlinarith
              exact (le_div_iff₀ hden).2 (by simpa [mul_comm] using hscaled)
          have hMle : M ≤ M / (n + 1 : ℝ) := by
            apply csSup_le hSne
            intro z hz
            rcases hz with ⟨v, hv, rfl⟩
            exact hcontract v hv
          have hMeq : M = 0 := by
            have hden : (1 : ℝ) < n + 1 := by
              exact_mod_cast Nat.lt_add_one_of_le hn
            by_cases hMz : M = 0
            · exact hMz
            · have hMpos : 0 < M := lt_of_le_of_ne hM0 (Ne.symm hMz)
              have hdiv : M / (n + 1 : ℝ) < M :=
                div_lt_self hMpos hden
              exact (not_lt_of_ge hMle hdiv).elim
          have hduM : max (d u) 0 ≤ M :=
            le_csSup hSbdd ⟨u, ⟨hnu', hub⟩, rfl⟩
          exact (le_max_left (d u) 0).trans (hduM.trans_eq hMeq)
  intro u hu
  let n : ℕ := max 1 ⌈U⌉₊
  have hn1 : 1 ≤ n := le_max_left _ _
  have hUn : U ≤ n := (Nat.le_ceil U).trans (by
    exact_mod_cast (le_max_right 1 ⌈U⌉₊))
  have hd := hstep n hn1 u hu.1 hu.2 (hu.2.trans hUn)
  dsimp only [d] at hd
  linarith

end

end Erdos783
