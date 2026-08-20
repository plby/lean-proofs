/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.DetectorLowPrefix
import ErdosProblems.Erdos48.ZeroSelection

/-!
# A band-limited zero detector

The short initial segment of the propagated detector is removed uniformly.
Its new lower endpoint is a fixed power of the global conductor-height
parameter; this is the localization which makes the log-free density estimate
possible.
-/

namespace Erdos48

open Complex
open BoundedGaps.Maynard

noncomputable section

/-- Binary logarithmic length used for the lower end of the detector. -/
noncomputable def zeroDetectorLowerLog (B : ℝ) : ℕ :=
  ⌊8 * Real.log B⌋₊

/-- The lower endpoint of the band detector. -/
noncomputable def zeroDetectorLowerCutoff (B : ℝ) : ℕ :=
  2 ^ zeroDetectorLowerLog B

/-- The detector restricted to its long-index band. -/
noncomputable def bandZeroDetectorPolynomial
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (eta : ℝ) (k N : ℕ) (B t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc (zeroDetectorLowerCutoff B) N,
    (weightedVonMangoldtMajorant eta k n : ℂ) * chi n *
      Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))

private theorem norm_detector_prefix_le_majorant
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (eta : ℝ) (k M : ℕ) (t : ℝ) :
    ‖∑ n ∈ Finset.Icc 1 (2 ^ M),
        (weightedVonMangoldtMajorant eta k n : ℂ) * chi n *
          Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ ≤
      ∑ n ∈ Finset.Icc 1 (2 ^ M),
        weightedVonMangoldtMajorant eta k n := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 (2 ^ M),
        ‖(weightedVonMangoldtMajorant eta k n : ℂ) * chi n *
          Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 (2 ^ M),
        weightedVonMangoldtMajorant eta k n := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (by
          unfold weightedVonMangoldtMajorant
          positivity), Complex.norm_exp]
      have him :
          (I * (((-t * Real.log n) : ℝ) : ℂ)).re = 0 := by
        rw [Complex.mul_re]
        simp only [Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, one_mul, sub_self]
      rw [him, Real.exp_zero, mul_one]
      exact mul_le_of_le_one_right (by
        unfold weightedVonMangoldtMajorant
        positivity)
        (DirichletCharacter.norm_le_one chi (n : ZMod q))

private theorem full_detector_eq_prefix_add_band
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (eta : ℝ) (k N M : ℕ) (t : ℝ) (hMN : 2 ^ M ≤ N) :
    finiteZeroDetectorPolynomial chi eta k N t =
      (∑ n ∈ Finset.Icc 1 (2 ^ M),
        (weightedVonMangoldtMajorant eta k n : ℂ) * chi n *
          Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))) +
      (∑ n ∈ Finset.Ioc (2 ^ M) N,
        (weightedVonMangoldtMajorant eta k n : ℂ) * chi n *
          Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))) := by
  classical
  unfold finiteZeroDetectorPolynomial
  rw [← Finset.sum_union]
  · have hunion : Finset.Icc 1 (2 ^ M) ∪ Finset.Ioc (2 ^ M) N =
        Finset.Icc 1 N := by
      have hpow : 1 ≤ 2 ^ M := Nat.one_le_pow M 2 (by omega)
      ext n
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    rw [hunion]
  · exact Finset.disjoint_left.mpr (by
      intro n hn1 hn2
      have h1 := Finset.mem_Icc.mp hn1
      have h2 := Finset.mem_Ioc.mp hn2
      omega)

private theorem detector_prefix_small
    {theta eta lambda : ℝ} {j M : ℕ}
    (htheta : theta = 1 / (1000 * (Real.log 4 + 4)))
    (heta : 0 < eta) (hetaSmall : eta ≤ theta / 36)
    (hlambdaSmall : lambda ≤ theta / 36)
    (hetaM : (eta : ℝ) * M ≤ 8 * lambda)
    (hj : 2 ≤ j) :
    2 * (Real.log 4 + 4) * (M : ℝ) *
        (((M + 1 : ℕ) : ℝ) * Real.log 2) ^ (j - 1) ≤
      (j - 1).factorial * (1 / 96 : ℝ) *
        (2 * eta)⁻¹ ^ j := by
  let C : ℝ := Real.log 4 + 4
  have hC : 1 ≤ C := by
    dsimp [C]
    have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hthetaPos : 0 < theta := by rw [htheta]; positivity
  have hthetaOne : theta ≤ 1 := by
    rw [htheta]
    have hden : (1 : ℝ) ≤ 1000 * C := by nlinarith
    exact (div_le_one (mul_pos (by norm_num) hCpos)).2 hden
  have hMle : (M : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by norm_num
  have hlogTwo : Real.log 2 ≤ 1 :=
    (Real.log_le_sub_one_of_pos (by norm_num)).trans_eq (by norm_num)
  have hetaM1 : eta * ((M + 1 : ℕ) : ℝ) ≤ theta / 4 := by
    rw [Nat.cast_add, Nat.cast_one]
    calc
      eta * ((M : ℝ) + 1) = eta * M + eta := by ring
      _ ≤ 8 * lambda + theta / 36 := add_le_add hetaM hetaSmall
      _ ≤ 8 * (theta / 36) + theta / 36 := by gcongr
      _ ≤ theta / 4 := by linarith
  have hbase : 2 * eta * (((M + 1 : ℕ) : ℝ) * Real.log 2) ≤ theta / 2 := by
    calc
      2 * eta * (((M + 1 : ℕ) : ℝ) * Real.log 2) ≤
          2 * eta * (((M + 1 : ℕ) : ℝ) * 1) := by gcongr
      _ = 2 * (eta * ((M + 1 : ℕ) : ℝ)) := by ring
      _ ≤ 2 * (theta / 4) := by gcongr
      _ = theta / 2 := by ring
  have hbase' : 2 * eta * ((M + 1 : ℕ) : ℝ) ≤ theta / 2 := by
    calc
      2 * eta * ((M + 1 : ℕ) : ℝ) =
          2 * (eta * ((M + 1 : ℕ) : ℝ)) := by ring
      _ ≤ 2 * (theta / 4) := by gcongr
      _ = theta / 2 := by ring
  have hbaseNonneg :
      0 ≤ 2 * eta * (((M + 1 : ℕ) : ℝ) * Real.log 2) := by positivity
  have hpow :
      (2 * eta * ((M + 1 : ℕ) : ℝ)) ^ j ≤ theta ^ j := by
    apply pow_le_pow_left₀ (by positivity)
    exact hbase'.trans (by linarith [hthetaPos])
  have hthetaPow : theta ^ j ≤ theta ^ 2 :=
    pow_le_pow_of_le_one hthetaPos.le hthetaOne hj
  have hnumeric : 2 * C * theta ^ 2 ≤ 1 / 96 := by
    rw [htheta]
    field_simp
    nlinarith
  have hscaled :
      (2 * C * (M : ℝ) *
          (((M + 1 : ℕ) : ℝ) * Real.log 2) ^ (j - 1)) *
          (2 * eta) ^ j ≤ 1 / 96 := by
    have hMnonneg : (0 : ℝ) ≤ M := by positivity
    have hfac :
        (M : ℝ) * (((M + 1 : ℕ) : ℝ) * Real.log 2) ^ (j - 1) *
            (2 * eta) ^ j ≤
          (2 * eta * ((M + 1 : ℕ) : ℝ)) ^ j := by
      let A : ℝ := ((M + 1 : ℕ) : ℝ) * Real.log 2
      have hA : 0 ≤ A := by dsimp [A]; positivity
      have hAstep : (M : ℝ) * A ^ (j - 1) * (2 * eta) ^ j ≤
          ((M + 1 : ℕ) : ℝ) * A ^ (j - 1) * (2 * eta) ^ j := by
        gcongr
      have hjpos : 0 < j := by omega
      have hAle : A ≤ ((M + 1 : ℕ) : ℝ) := by
        dsimp [A]
        calc
          ((M + 1 : ℕ) : ℝ) * Real.log 2 ≤
              ((M + 1 : ℕ) : ℝ) * 1 := by gcongr
          _ = ((M + 1 : ℕ) : ℝ) := by ring
      calc
        (M : ℝ) * A ^ (j - 1) * (2 * eta) ^ j ≤
            ((M + 1 : ℕ) : ℝ) * A ^ (j - 1) * (2 * eta) ^ j := hAstep
        _ ≤ ((M + 1 : ℕ) : ℝ) ^ j * (2 * eta) ^ j := by
          apply mul_le_mul_of_nonneg_right
          · calc
              ((M + 1 : ℕ) : ℝ) * A ^ (j - 1) ≤
                  ((M + 1 : ℕ) : ℝ) *
                    ((M + 1 : ℕ) : ℝ) ^ (j - 1) :=
                mul_le_mul_of_nonneg_left
                  (pow_le_pow_left₀ hA hAle (j - 1)) (by positivity)
              _ = ((M + 1 : ℕ) : ℝ) ^ j := by
                calc
                  ((M + 1 : ℕ) : ℝ) *
                      ((M + 1 : ℕ) : ℝ) ^ (j - 1) =
                      ((M + 1 : ℕ) : ℝ) ^ ((j - 1) + 1) := by
                    rw [pow_succ']
                  _ = ((M + 1 : ℕ) : ℝ) ^ j := by
                    congr 1
                    omega
          · positivity
        _ = (2 * eta * ((M + 1 : ℕ) : ℝ)) ^ j := by
          rw [mul_pow]
          ring
    calc
      (2 * C * (M : ℝ) *
          (((M + 1 : ℕ) : ℝ) * Real.log 2) ^ (j - 1)) *
          (2 * eta) ^ j ≤
          2 * C *
            (2 * eta * ((M + 1 : ℕ) : ℝ)) ^ j := by
        nlinarith [hfac]
      _ ≤ 2 * C * theta ^ j := by gcongr
      _ ≤ 2 * C * theta ^ 2 := by gcongr
      _ ≤ 1 / 96 := hnumeric
  have hfactorial : (1 : ℝ) ≤ (j - 1).factorial := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hpowPos : 0 < (2 * eta) ^ j := by positivity
  rw [inv_pow]
  apply (le_div_iff₀ hpowPos).2
  calc
    (2 * C * (M : ℝ) *
        (((M + 1 : ℕ) : ℝ) * Real.log 2) ^ (j - 1)) *
        (2 * eta) ^ j ≤ 1 / 96 := hscaled
    _ ≤ (j - 1).factorial * (1 / 96 : ℝ) := by
      calc
        (1 / 96 : ℝ) = 1 * (1 / 96 : ℝ) := by ring
        _ ≤ (j - 1).factorial * (1 / 96 : ℝ) :=
          mul_le_mul_of_nonneg_right hfactorial (by norm_num)

/-- Uniform parameters for a propagated detector supported beyond a fixed
power of the global conductor-height parameter. -/
theorem exists_uniform_band_zero_detector :
    ∃ L J : ℕ, 2 ≤ L ∧ L ≤ J ∧
      ∃ lambda R delta eta₀ : ℝ,
        0 < lambda ∧ 0 < R ∧ 0 < delta ∧ delta ≤ 1 ∧
        0 < eta₀ ∧ eta₀ ≤ 1 / 8 ∧
        ∀ (Q : ℕ), 2 ≤ Q → ∀ (T eta : ℝ), 0 ≤ T →
          0 < eta → eta ≤ eta₀ →
          eta * Real.log ((Q : ℝ) * (T + 2)) ≤ lambda →
          ∀ (q : ℕ) [NeZero q], ∀ (hq : 1 < q), q ≤ Q →
          ∀ (chi : DirichletCharacter ℂ q), ∀ (hchi : chi.IsPrimitive),
            ∃ S : Finset ℝ, ∃ order : ℝ → ℕ,
              S ⊆ highZeroOrdinates hq chi hchi eta T ∧
              (∀ x ∈ S, ∀ y ∈ S, x ≠ y →
                2 * delta * eta < dist x y) ∧
              (∀ x ∈ highZeroOrdinates hq chi hchi eta T,
                ∃ y ∈ S, dist x y ≤ 2 * delta * eta) ∧
              (zeroDetectorLowerCutoff ((Q : ℝ) * (T + 2)) ≤
                zeroDetectorCutoff R eta) ∧
              ∀ t ∈ S,
                L ≤ order t ∧ order t ≤ J ∧
                  ∀ u : ℝ, |u - t| ≤ delta * eta →
                    (order t - 1).factorial * (1 / 96 : ℝ) *
                        (2 * eta)⁻¹ ^ order t <
                      ‖bandZeroDetectorPolynomial chi eta (order t - 1)
                        (zeroDetectorCutoff R eta)
                        ((Q : ℝ) * (T + 2)) u‖ := by
  obtain ⟨L, J, hL2, hLJ, lambdaD, R, delta,
      hlambdaD, hR, hdelta, hdelta1, hselection⟩ :=
    exists_uniform_detected_zero_selection
  let C : ℝ := Real.log 4 + 4
  let theta : ℝ := 1 / (1000 * C)
  let eta₀ : ℝ := min (1 / 8) (theta / 36)
  let lambda : ℝ := min lambdaD (min (theta / 36) (R / 16))
  have hC : 0 < C := by dsimp [C]; positivity
  have htheta : 0 < theta := by dsimp [theta]; positivity
  have heta₀ : 0 < eta₀ := by
    dsimp [eta₀]
    exact lt_min (by norm_num) (by positivity)
  have heta₀8 : eta₀ ≤ 1 / 8 := min_le_left _ _
  have hlambda : 0 < lambda := by
    dsimp [lambda]
    exact lt_min hlambdaD (lt_min (by positivity) (by positivity))
  have hlambdaD' : lambda ≤ lambdaD := min_le_left _ _
  have hlambdaTheta : lambda ≤ theta / 36 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hlambdaR : lambda ≤ R / 16 :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨L, J, hL2, hLJ, lambda, R, delta, eta₀,
    hlambda, hR, hdelta, hdelta1, heta₀, heta₀8, ?_⟩
  intro Q hQ T eta hT heta hetaSmall hglobal q _ hq hqQ chi hchi
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hBpos : 0 < (Q : ℝ) * (T + 2) := by positivity
  have hlogNonneg : 0 ≤ Real.log ((Q : ℝ) * (T + 2)) :=
    Real.log_nonneg (by
      have : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
      nlinarith)
  have hqcast : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hqLog :
      eta * Real.log ((q : ℝ) * (T + 2)) ≤ lambdaD := by
    have hinside : (0 : ℝ) < (q : ℝ) * (T + 2) := by positivity
    have hlogle : Real.log ((q : ℝ) * (T + 2)) ≤
        Real.log ((Q : ℝ) * (T + 2)) := by
      apply Real.log_le_log hinside
      exact mul_le_mul_of_nonneg_right hqcast (by linarith)
    exact (mul_le_mul_of_nonneg_left hlogle heta.le).trans
      (hglobal.trans (hlambdaD'))
  obtain ⟨S, order, hSsub, hsep, hcover, horder⟩ :=
    hselection q hq chi hchi eta T heta
      (hetaSmall.trans heta₀8) hT hqLog
  let B : ℝ := (Q : ℝ) * (T + 2)
  let M : ℕ := zeroDetectorLowerLog B
  let N : ℕ := zeroDetectorCutoff R eta
  have hfloor : (M : ℝ) ≤ 8 * Real.log B := by
    dsimp [M, zeroDetectorLowerLog]
    exact Nat.floor_le (by dsimp [B]; positivity)
  have hetaM : eta * (M : ℝ) ≤ 8 * lambda := by
    calc
      eta * (M : ℝ) ≤ eta * (8 * Real.log B) :=
        mul_le_mul_of_nonneg_left hfloor heta.le
      _ = 8 * (eta * Real.log B) := by ring
      _ ≤ 8 * lambda := by
        exact mul_le_mul_of_nonneg_left (by simpa only [B] using hglobal)
          (by norm_num)
  have hMNreal : ((2 ^ M : ℕ) : ℝ) ≤ Real.exp (R / eta) := by
    calc
      ((2 ^ M : ℕ) : ℝ) = (2 : ℝ) ^ M := by norm_cast
      _ = (2 : ℝ) ^ (M : ℝ) := (Real.rpow_natCast 2 M).symm
      _ = Real.exp (Real.log 2 * (M : ℝ)) :=
        Real.rpow_def_of_pos (by norm_num) _
      _ ≤ Real.exp (R / eta) := by
        apply Real.exp_le_exp.mpr
        apply (le_div_iff₀ heta).2
        calc
          (Real.log 2 * (M : ℝ)) * eta ≤ 1 * (M : ℝ) * eta := by
            gcongr
            exact (Real.log_le_sub_one_of_pos (by norm_num)).trans_eq (by norm_num)
          _ = eta * M := by ring
          _ ≤ 8 * lambda := hetaM
          _ ≤ R := by
            calc
              8 * lambda ≤ 8 * (R / 16) := by gcongr
              _ ≤ R := by linarith
  have hMN : 2 ^ M ≤ N := by
    exact_mod_cast hMNreal.trans (exp_div_le_zeroDetectorCutoff R eta)
  refine ⟨S, order, hSsub, hsep, hcover, ?_, ?_⟩
  · change 2 ^ M ≤ N
    exact hMN
  · intro t ht
    obtain ⟨hLt, htJ, htPoly⟩ := horder t ht
    refine ⟨hLt, htJ, ?_⟩
    intro u hu
    have hfull := htPoly u hu
    let lowPart : ℂ :=
      ∑ n ∈ Finset.Icc 1 (2 ^ M),
        (weightedVonMangoldtMajorant eta (order t - 1) n : ℂ) * chi n *
          Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ))
    have hprefix : ‖lowPart‖ ≤
        (order t - 1).factorial * (1 / 96 : ℝ) *
          (2 * eta)⁻¹ ^ order t := by
      calc
        ‖lowPart‖ ≤ ∑ n ∈ Finset.Icc 1 (2 ^ M),
            weightedVonMangoldtMajorant eta (order t - 1) n :=
          norm_detector_prefix_le_majorant chi eta (order t - 1) M u
        _ ≤ 2 * (Real.log 4 + 4) * (M : ℝ) *
            (((M + 1 : ℕ) : ℝ) * Real.log 2) ^ (order t - 1) :=
          sum_weightedVonMangoldtMajorant_Icc_two_pow_le
            eta heta (order t - 1) M
        _ ≤ _ := detector_prefix_small
          (theta := theta) (lambda := lambda)
          (by rfl) heta (hetaSmall.trans (min_le_right _ _))
          hlambdaTheta hetaM (hL2.trans hLt)
    have hdecomp := full_detector_eq_prefix_add_band
      chi eta (order t - 1) N M u hMN
    have htriangle :
        ‖finiteZeroDetectorPolynomial chi eta (order t - 1) N u‖ ≤
          ‖lowPart‖ +
            ‖bandZeroDetectorPolynomial chi eta (order t - 1) N B u‖ := by
      rw [hdecomp]
      simpa only [lowPart, bandZeroDetectorPolynomial,
        zeroDetectorLowerCutoff, M] using
          norm_add_le lowPart
            (∑ n ∈ Finset.Ioc (2 ^ M) N,
              (weightedVonMangoldtMajorant eta (order t - 1) n : ℂ) * chi n *
                Complex.exp (I * (((-u * Real.log n) : ℝ) : ℂ)))
    change (order t - 1).factorial * (1 / 96 : ℝ) *
        (2 * eta)⁻¹ ^ order t < _
    dsimp only [N, B] at htriangle
    dsimp [lowPart] at hprefix htriangle
    linarith

end

end Erdos48
