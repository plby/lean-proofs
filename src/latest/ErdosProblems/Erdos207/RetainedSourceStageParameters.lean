/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RetainedVortexPowerGeometry
import ErdosProblems.Erdos207.SourceStageExponentSchedule
import ErdosProblems.Erdos207.KSSSCoefficientChoice

/-! # Fix every retained-stage analytic exponent before quantifying the ambient order -/

namespace Erdos207

theorem retained_stage_exponent_le_ambient (Rfixed step ell i : ℕ) :
    retainedStageExponent Rfixed step ell i ≤ Rfixed + step * ell := by
  by_cases hi : i = 0
  · simp only [retainedStageExponent, if_pos hi, le_refl]
  · simp only [retainedStageExponent, if_neg hi]
    exact (Nat.mul_le_mul_left step (Nat.sub_le ell i)).trans (Nat.le_add_left _ _)

theorem retained_stage_exponent_ratio_gap
    (Rfixed step ell length m rootPower K : ℕ) (hsplit : length + m = ell)
    (hroot : rootPower ≤ step * m) (hrootGap : K * (2 * step + 1) ≤ rootPower)
    (hfirstGap : K * (Rfixed + step + 1) ≤ Rfixed + step * ell) (i : Fin length) :
    1 ≤ retainedRatioExponent Rfixed step i.val ∧
      K * retainedRatioExponent Rfixed step i.val ≤ retainedStageExponent Rfixed step ell i.val := by
  by_cases hi : i.val = 0
  · simpa [retainedRatioExponent, retainedStageExponent, hi] using
      And.intro (show 1 ≤ Rfixed + step + 1 by omega) hfirstGap
  · simp only [retainedRatioExponent, retainedStageExponent, if_neg hi]
    refine ⟨by omega, hrootGap.trans (hroot.trans ?_)⟩
    exact Nat.mul_le_mul_left step (by have := i.isLt; omega)

theorem source_stage_multiplier_denominator_bounds
    (q b B k Rmin D d : ℕ) (hmin : 1 ≤ Rmin)
    (hgap : ksssPowerDenominatorExponent q b B k Rmin * (d + 1) ≤ D) :
    D + 1 ≤ ksssPowerDenominatorExponent q (b * (D + 1)) B (k * (D + 1)) (Rmin * (D + 1)) ∧
      ksssPowerDenominatorExponent q (b * (D + 1)) B (k * (D + 1)) (Rmin * (D + 1)) * (d + 1) ≤
        D * (D + 1) := by
  have hc : 1 ≤ D + 1 := by omega
  have hminScale : D + 1 ≤ Rmin * (D + 1) := by
    simpa only [one_mul] using Nat.mul_le_mul_right (D + 1) hmin
  constructor
  · apply hminScale.trans
    unfold ksssPowerDenominatorExponent
    omega
  · calc
      _ ≤ (ksssPowerDenominatorExponent q b B k Rmin * (D + 1)) * (d + 1) :=
        Nat.mul_le_mul_right _ (ksssPowerDenominatorExponent_scale_le q b B k Rmin (D + 1) hc)
      _ = (ksssPowerDenominatorExponent q b B k Rmin * (d + 1)) * (D + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right (D + 1) hgap

theorem retained_source_stage_scale_bounds
    (q B k Rmin decay K Rfixed step ell length m rootPower T : ℕ)
    (hmin : 1 ≤ Rmin) (hdecay : 1 ≤ decay)
    (hK : ksssPowerDenominatorExponent q 2 B k Rmin * (decay + 1) ≤ K)
    (hsplit : length + m = ell) (hroot : rootPower ≤ step * m)
    (hrootGap : K * (2 * step + 1) ≤ rootPower)
    (hfirstGap : K * (Rfixed + step + 1) ≤ Rfixed + step * ell)
    (i : Fin length) (t n : ℕ) (ht : 1 ≤ t)
    (hlo : t ^ retainedStageExponent Rfixed step ell i.val ≤ n)
    (hhi : n ≤ t ^ (retainedStageExponent Rfixed step ell i.val + 1))
    (hthreshold : (max 2 T) ^ (retainedStageExponent Rfixed step ell i.val + 1) ≤ t) :
    let D := retainedStageExponent Rfixed step ell i.val
    let v := retainedRatioExponent Rfixed step i.val
    let c := D + 1
    let den := ksssPowerDenominatorExponent q (2 * c) B (k * c) (Rmin * c)
    let u := dyadicPowerScale den n
    1 ≤ c ∧ u ^ den ≤ n ∧ 1 ≤ u ∧ u ≤ t ∧ t ^ (decay * v) ≤ u ^ c ∧ T ≤ u ∧
      (∀ N R : ℕ, N ≤ t ^ R → N ≤ u ^ (c * R)) := by
  dsimp only
  let D := retainedStageExponent Rfixed step ell i.val
  let v := retainedRatioExponent Rfixed step i.val
  let c := D + 1
  let den := ksssPowerDenominatorExponent q (2 * c) B (k * c) (Rmin * c)
  let u := dyadicPowerScale den n
  have hv := retained_stage_exponent_ratio_gap Rfixed step ell length m rootPower K
    hsplit hroot hrootGap hfirstGap i
  have hgap : ksssPowerDenominatorExponent q 2 B k Rmin * (decay * v + 1) ≤ D := by
    calc
      _ ≤ ksssPowerDenominatorExponent q 2 B k Rmin * ((decay + 1) * v) :=
        Nat.mul_le_mul_left _ (by nlinarith only [hv.1])
      _ = (ksssPowerDenominatorExponent q 2 B k Rmin * (decay + 1)) * v := by ring
      _ ≤ K * v := Nat.mul_le_mul_right v hK
      _ ≤ D := hv.2
  have hden := source_stage_multiplier_denominator_bounds q 2 B k Rmin D (decay * v) hmin hgap
  have hc : 1 ≤ c := by dsimp only [c]; omega
  have ht0 : 0 < t := Nat.zero_lt_one.trans_le ht
  have hn0 : n ≠ 0 := Nat.ne_of_gt ((pow_pos ht0 D).trans_le hlo)
  have hdenPos : 0 < den := by dsimp only [den, c]; omega
  have hround : 2 ^ c ≤ t := (Nat.pow_le_pow_left (le_max_left 2 T) c).trans hthreshold
  have hpower : t ^ (decay * v) ≤ u ^ c :=
    dyadicStageScale_cutoff_power_lower t n D den c (decay * v) ht0 hdenPos hlo hden.2 hround
  have htuc : t ≤ u ^ c := by
    have hprod : 1 ≤ decay * v := by
      simpa only [one_mul] using Nat.mul_le_mul hdecay hv.1
    have hle : t ≤ t ^ (decay * v) := by
      simpa only [pow_one] using Nat.pow_le_pow_right ht0 hprod
    exact hle.trans hpower
  refine ⟨hc, dyadicPowerScale_pow_le hn0, one_le_dyadicPowerScale _ _,
    dyadicStageScale_le_base t n D den ht hn0 hden.1 hhi, hpower, ?_, ?_⟩
  · apply (Nat.pow_le_pow_iff_left (by dsimp only [c]; omega : c ≠ 0)).mp
    exact ((Nat.pow_le_pow_left (le_max_right 2 T) c).trans hthreshold).trans htuc
  · intro N R hN
    calc
      N ≤ t ^ R := hN
      _ ≤ (u ^ c) ^ R := Nat.pow_le_pow_left htuc R
      _ = _ := (pow_mul u c R).symm

theorem InitialPowerVortexPackage.retained_source_process_scales
    {q h n ell t rootPower step length m Rfixed K : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (B k Rmin decay T : ℕ) (hmin : 1 ≤ Rmin) (hdecay : 1 ≤ decay)
    (hK : ksssPowerDenominatorExponent q 2 B k Rmin * (decay + 1) ≤ K)
    (hsplit : length + m = ell) (hlength : 2 ≤ length) (ht : 2 ≤ t)
    (hroot : rootPower ≤ step * m) (hrootUpper : step * m ≤ rootPower + step)
    (hrootGap : K * (2 * step + 1) ≤ rootPower)
    (hfirstGap : K * (Rfixed + step + 1) ≤ Rfixed + step * ell)
    (hnlo : t ^ (Rfixed + step * ell) ≤ n) (hnhi : n ≤ t ^ (Rfixed + step * ell + 1))
    (hthreshold : (max 2 T) ^ (Rfixed + step * ell + 1) ≤ t) (i : Fin length) :
    let W := P.retainedVortex length (by omega) (by omega)
    let D := retainedStageExponent Rfixed step ell i.val
    let v := retainedRatioExponent Rfixed step i.val
    let c := D + 1
    let den := ksssPowerDenominatorExponent q (2 * c) B (k * c) (Rmin * c)
    let u := dyadicPowerScale den (W.U i.castSucc).card
    1 ≤ c ∧ u ^ den ≤ (W.U i.castSucc).card ∧ 1 ≤ u ∧ u ≤ t ∧
      t ^ (decay * v) ≤ u ^ c ∧ T ≤ u ∧ n ≤ u ^ (c * (Rfixed + step * ell + 1)) := by
  dsimp only
  let W := P.retainedVortex length (by omega) (by omega)
  have hgeom := P.retainedVortex_stage_power_geometry hsplit hlength ht hroot hrootUpper
    hrootGap hfirstGap hnlo hnhi i
  have hlocalThreshold : (max 2 T) ^ (retainedStageExponent Rfixed step ell i.val + 1) ≤ t := by
    apply le_trans _ hthreshold
    apply Nat.pow_le_pow_right (by omega : 0 < max 2 T)
    exact Nat.add_le_add_right (retained_stage_exponent_le_ambient Rfixed step ell i.val) 1
  have hscales := retained_source_stage_scale_bounds q B k Rmin decay K Rfixed step ell length m
    rootPower T hmin hdecay hK hsplit hroot hrootGap hfirstGap i t (W.U i.castSucc).card
    (by omega) hgeom.1 hgeom.2.1 hlocalThreshold
  exact ⟨hscales.1, hscales.2.1, hscales.2.2.1, hscales.2.2.2.1, hscales.2.2.2.2.1,
    hscales.2.2.2.2.2.1, hscales.2.2.2.2.2.2 n (Rfixed + step * ell + 1) hnhi⟩

end Erdos207
