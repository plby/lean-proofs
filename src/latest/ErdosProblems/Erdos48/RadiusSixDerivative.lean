/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.LocalAnnularMass
import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveLFunctionRadiusTwelve

/-!
# High derivatives and the radius-six zero multiset

The fixed-disk regularization removes every zero in the radius-six disk.
Cauchy's estimate then bounds all derivatives of the remaining logarithmic
derivative.  This file records the resulting approximation in the exact
`Finsupp` form consumed by the zero detector.
-/

namespace Erdos48

open Complex Metric Set
open BoundedGaps.Maynard

noncomputable section

private theorem radiusSix_divisor_finsum_eq_finsupp
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (t : ℝ) (s : ℂ) :
    (∑ᶠ rho : ℂ,
        ((MeromorphicOn.divisor (DirichletCharacter.LFunction chi)
          (closedBall ((2 : ℂ) + t * I) 6) rho : ℤ) : ℂ) /
            (s - rho)) =
      ∑ᶠ rho : ℂ,
        (radiusSixZeroFinsupp hq chi hchi t rho : ℂ) /
          (s - rho) := by
  apply finsum_congr
  intro rho
  rw [← radiusSixZeroFinsupp_apply_eq_divisor hq chi hchi t rho]
  norm_cast

private theorem radiusSix_poleSum_analyticAt
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (t : ℝ) {s : ℂ}
    (hne : ∀ rho ∈ (radiusSixZeroFinsupp hq chi hchi t).support,
      s ≠ rho) :
    AnalyticAt ℂ (fun w : ℂ ↦
      ∑ᶠ rho : ℂ,
        (radiusSixZeroFinsupp hq chi hchi t rho : ℂ) /
          (w - rho)) s := by
  let D := radiusSixZeroFinsupp hq chi hchi t
  have hfun : (fun w : ℂ ↦ ∑ᶠ rho : ℂ, (D rho : ℂ) / (w - rho)) =
      (fun w : ℂ ↦ ∑ rho ∈ D.support, (D rho : ℂ) / (w - rho)) := by
    funext w
    apply finsum_eq_sum_of_support_subset
    intro rho hrho
    rw [Function.mem_support] at hrho
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro hzero
    exact hrho (by simp [hzero])
  rw [show (fun w : ℂ ↦
      ∑ᶠ rho : ℂ,
        (radiusSixZeroFinsupp hq chi hchi t rho : ℂ) / (w - rho)) =
      (fun w : ℂ ↦ ∑ᶠ rho : ℂ, (D rho : ℂ) / (w - rho)) by rfl,
    hfun]
  have han : AnalyticAt ℂ
      (∑ rho ∈ D.support,
        (fun w : ℂ ↦ (D rho : ℂ) / (w - rho))) s := by
    apply Finset.analyticAt_sum D.support
    intro rho hrho
    exact (analyticAt_const.div
      (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr (hne rho hrho)))
  convert han using 1
  funext w
  simp

/-- Uniform fixed-disk approximation of a high logarithmic derivative by
the reciprocal powers of the radius-six zero multiset. -/
theorem exists_radiusSix_iteratedDeriv_approximation :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], ∀ (hq : 1 < q),
        ∀ (chi : DirichletCharacter ℂ q), ∀ (hchi : chi.IsPrimitive),
          ∀ (t eta : ℝ), 0 < eta → eta ≤ 1 →
            ∀ k : ℕ,
              let z : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
              ‖iteratedDeriv k
                    (fun w ↦ -logDeriv (DirichletCharacter.LFunction chi) w) z -
                  (-1 : ℂ) ^ (k + 1) * k.factorial *
                    (radiusSixZeroFinsupp hq chi hchi t).sum
                      (fun rho m ↦ (m : ℂ) / (z - rho) ^ (k + 1))‖ ≤
                k.factorial *
                  (16 * ((A : ℝ) *
                    Real.log ((q : ℝ) * (|t| + 2))) / 3) := by
  obtain ⟨A, hA, hgrowth⟩ :=
    exists_nat_norm_LFunction_radiusTwelveSphere_le_exp_mul_center
  refine ⟨A, hA, ?_⟩
  intro q _ hq chi hchi t eta heta0 heta1 k
  dsimp only
  let f : ℂ → ℂ := DirichletCharacter.LFunction chi
  let c : ℂ := (2 : ℂ) + t * I
  let z : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
  let B : ℝ := (q : ℝ) * (|t| + 2)
  let M : ℝ := (A : ℝ) * Real.log B
  let D : ℂ →₀ ℕ := radiusSixZeroFinsupp hq chi hchi t
  have hB4 : (4 : ℝ) ≤ B := by
    dsimp [B]
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
    have ht2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
    nlinarith
  have hM : 0 < M := by
    dsimp [M]
    exact mul_pos (by exact_mod_cast (show 0 < A by omega))
      (Real.log_pos (by linarith))
  have hf : AnalyticOnNhd ℂ f (closedBall c (4 * (3 : ℝ))) := by
    intro w hw
    exact (DirichletCharacter.differentiable_LFunction
      (character_ne_one_of_isPrimitive hq chi hchi)).analyticAt w
  have hc : f c ≠ 0 := by
    have hc_re : 1 < c.re := by simp [c]
    change DirichletCharacter.LFunction chi c ≠ 0
    rw [DirichletCharacter.LFunction_eq_LSeries chi hc_re]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re chi hc_re
  have hbound : ∀ w ∈ sphere c (4 * (3 : ℝ)),
      ‖f w‖ ≤ Real.exp M * ‖f c‖ := by
    intro w hw
    norm_num at hw
    simpa [f, c, M, B] using
      hgrowth q hq chi hchi t w (by simpa [c] using hw)
  obtain ⟨G, hG, hGne, hidentity, hGbound⟩ :=
    exists_regularizedLogDeriv_data_erdos48
      (f := f) (c := c) (R := (3 : ℝ)) (M := M)
      (by norm_num) hM hf hc hbound
  have hzre : z.re = 1 + eta := by simp [z]
  have hzc : dist z c = 1 - eta := by
    rw [Complex.dist_eq]
    have heq : z - c = ((eta - 1 : ℝ) : ℂ) := by
      simp only [z, c]
      push_cast
      ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    ring
  have hzball : z ∈ closedBall c 3 := by
    rw [mem_closedBall, hzc]
    linarith
  have hLz : f z ≠ 0 := by
    change DirichletCharacter.LFunction chi z ≠ 0
    exact chi.LFunction_ne_zero_of_one_le_re
      (.inl (character_ne_one_of_isPrimitive hq chi hchi))
      (by rw [hzre]; linarith)
  have hDne : ∀ rho ∈ D.support, z ≠ rho := by
    intro rho hrho hzr
    subst rho
    have hDzero : D z = 0 := by
      change radiusSixZeroMultiplicity chi t z = 0
      unfold radiusSixZeroMultiplicity
      split
      next hdist =>
        by_contra horder
        exact hLz (by simpa [f] using
          apply_eq_zero_of_analyticOrderNatAt_ne_zero horder)
      next hdist => rfl
    exact (Finsupp.mem_support_iff.mp hrho) hDzero
  let P : ℂ → ℂ := fun w ↦
    ∑ᶠ rho : ℂ, (D rho : ℂ) / (w - rho)
  let U : Set ℂ := {w | 1 < w.re ∧ dist w c < 3}
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt (continuous_id.dist continuous_const) continuous_const)
  have hzU : z ∈ U := by
    refine ⟨by rw [hzre]; linarith, ?_⟩
    rw [hzc]
    linarith
  have heqOn : Set.EqOn (logDeriv G)
      (fun w ↦ logDeriv f w - P w) U := by
    intro w hw
    have hwball : w ∈ closedBall c 3 := mem_closedBall.mpr hw.2.le
    have hfw : f w ≠ 0 := by
      change DirichletCharacter.LFunction chi w ≠ 0
      exact chi.LFunction_ne_zero_of_one_le_re
        (.inl (character_ne_one_of_isPrimitive hq chi hchi)) hw.1.le
    have hid := hidentity w hwball hfw
    change logDeriv G w =
        logDeriv (DirichletCharacter.LFunction chi) w -
          ∑ᶠ rho : ℂ,
            ((MeromorphicOn.divisor (DirichletCharacter.LFunction chi)
              (closedBall ((2 : ℂ) + t * I) (2 * 3)) rho : ℤ) : ℂ) /
                (w - rho) at hid
    rw [show (2 : ℝ) * 3 = 6 by norm_num] at hid
    rw [hid]
    dsimp only [P, D, f]
    rw [radiusSix_divisor_finsum_eq_finsupp hq chi hchi t w]
  have hderivEq := heqOn.iteratedDeriv_of_isOpen hUopen k hzU
  have hlogAnalytic : AnalyticAt ℂ (logDeriv f) z := by
    have hfz : AnalyticAt ℂ f z := hf z (by
      exact closedBall_subset_closedBall
        (by norm_num : (3 : ℝ) ≤ 4 * 3) hzball)
    simpa [logDeriv] using hfz.deriv.div hfz hLz
  have hPAnalytic : AnalyticAt ℂ P z := by
    simpa only [P, D] using
      radiusSix_poleSum_analyticAt hq chi hchi t hDne
  have hGP :
      iteratedDeriv k (logDeriv G) z =
        iteratedDeriv k (logDeriv f) z - iteratedDeriv k P z := by
    rw [hderivEq]
    exact iteratedDeriv_sub hlogAnalytic.contDiffAt hPAnalytic.contDiffAt
  have hPderiv : iteratedDeriv k P z =
      (-1 : ℂ) ^ k * k.factorial *
        D.sum (fun rho m ↦ (m : ℂ) / (z - rho) ^ (k + 1)) := by
    have hraw := iteratedDeriv_weighted_inv_sub_finsum (k := k)
      (b := fun rho ↦ (D rho : ℂ))
      (hb := by
        exact D.support.finite_toSet.subset <| by
          intro rho hrho
          rw [Function.mem_support] at hrho
          rw [Finset.mem_coe, Finsupp.mem_support_iff]
          intro hzero
          exact hrho (by simp [hzero]))
      (z := z) (hne := by
        intro rho hrho
        rw [Function.mem_support] at hrho
        apply hDne rho
        rw [Finsupp.mem_support_iff]
        intro hzero
        exact hrho (by simp [hzero]))
    have hsum :
        (∑ᶠ rho : ℂ, (D rho : ℂ) / (z - rho) ^ (k + 1)) =
          D.sum (fun rho m ↦ (m : ℂ) / (z - rho) ^ (k + 1)) := by
      rw [Finsupp.sum]
      apply finsum_eq_sum_of_support_subset
      intro rho hrho
      rw [Function.mem_support] at hrho
      rw [Finset.mem_coe, Finsupp.mem_support_iff]
      intro hzero
      exact hrho (by simp [hzero])
    rw [hsum] at hraw
    simpa only [P] using hraw
  have hGderiv := norm_iteratedDeriv_logDeriv_le_of_regularized_data
    (G := G) (c := c) (z := z) (R := (3 : ℝ)) (r := (1 : ℝ))
    (C := 16 * M / 3) (by norm_num) (by norm_num) hG hGne
    (by
      intro w hw
      rw [mem_closedBall] at hw ⊢
      calc
        dist w c ≤ dist w z + dist z c := dist_triangle _ _ _
        _ ≤ 1 + (1 - eta) := add_le_add hw hzc.le
        _ ≤ 3 := by linarith)
    hGbound k
  have hneg : iteratedDeriv k (fun w ↦ -logDeriv f w) z =
      -iteratedDeriv k (logDeriv f) z := iteratedDeriv_neg k _ _
  change ‖iteratedDeriv k (fun w ↦ -logDeriv f w) z -
      (-1 : ℂ) ^ (k + 1) * k.factorial *
        D.sum (fun rho m ↦ (m : ℂ) / (z - rho) ^ (k + 1))‖ ≤
      k.factorial * (16 * M / 3)
  rw [hneg]
  have hsign : -((-1 : ℂ) ^ k) = (-1 : ℂ) ^ (k + 1) := by
    rw [pow_succ]
    ring
  rw [← hsign]
  have hdiff :
      -iteratedDeriv k (logDeriv f) z -
          (-((-1 : ℂ) ^ k) * k.factorial *
            D.sum (fun rho m ↦ (m : ℂ) / (z - rho) ^ (k + 1))) =
        -iteratedDeriv k (logDeriv G) z := by
    calc
      -iteratedDeriv k (logDeriv f) z -
          (-((-1 : ℂ) ^ k) * k.factorial *
            D.sum (fun rho m ↦ (m : ℂ) / (z - rho) ^ (k + 1))) =
          -iteratedDeriv k (logDeriv f) z +
            ((-1 : ℂ) ^ k * k.factorial *
              D.sum (fun rho m ↦ (m : ℂ) / (z - rho) ^ (k + 1))) := by
        ring
      _ = -iteratedDeriv k (logDeriv f) z + iteratedDeriv k P z := by
        rw [hPderiv]
      _ = -iteratedDeriv k (logDeriv G) z := by
        rw [hGP]
        ring
  rw [hdiff, norm_neg]
  simpa [M, B, f, z, D] using hGderiv

end

end Erdos48
