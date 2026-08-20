/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.PointwiseZeroDetectorSecond

/-!
# Numerical parameters for the variable-order zero detector

This file isolates the elementary estimate behind the use of Turan's
second main theorem.  Once the detector is multiplied by `(2 * eta)^j`, all
four analytic errors have the same geometric factor `2^{-j}`.  The remaining
dependence on conductor and height is only through `eta * log B`.
-/

namespace Erdos48

noncomputable section

/-- Common coefficient in the scaled variable-order detector error. -/
noncomputable def pointwiseSecondErrorCoefficient
    (Al Af Ad : ℕ) (h : ℝ) : ℝ :=
  64 * (Real.log 4 + 4) +
    (4096 * (Al : ℝ) / 3 + 16 * (Af : ℝ) +
      64 * (Ad : ℝ) / 3) * h

theorem pointwiseSecondErrorCoefficient_nonneg
    (Al Af Ad : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    0 ≤ pointwiseSecondErrorCoefficient Al Af Ad h := by
  unfold pointwiseSecondErrorCoefficient
  positivity

/-- After the natural Turan scaling, every error term is bounded by one
copy of `2^{-j}` times a coefficient linear in `eta * log B`. -/
theorem pointwiseZeroDetectorError_second_scaled_le
    (Al Af Ad q j : ℕ) (t eta : ℝ)
    (heta : 0 < eta) (heta8 : eta ≤ 1 / 8) (hj : 1 ≤ j)
    (hlog : 0 ≤ Real.log ((q : ℝ) * (|t| + 2))) :
    (2 * eta) ^ j * pointwiseZeroDetectorError Al Af Ad q t eta j ≤
      (1 / 2 : ℝ) ^ j *
        pointwiseSecondErrorCoefficient Al Af Ad
          (eta * Real.log ((q : ℝ) * (|t| + 2))) := by
  let u : ℝ := Real.log ((q : ℝ) * (|t| + 2))
  let h : ℝ := eta * u
  have hu : 0 ≤ u := by simpa only [u] using hlog
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have h4eta : 0 ≤ 4 * eta := by positivity
  have h4etaHalf : 4 * eta ≤ (1 / 2 : ℝ) := by linarith
  have h2eta : 0 ≤ 2 * eta := by positivity
  have h2etaHalf : 2 * eta ≤ (1 / 2 : ℝ) := by linarith
  have hratio : (2 * eta) / (4 * eta) = (1 / 2 : ℝ) := by
    field_simp [heta.ne']
    norm_num
  have hratio2 : (2 * eta) / (1 / 2 : ℝ) = 4 * eta := by
    field_simp
    ring
  have hpowDecomp (x : ℝ) : x ^ j = x ^ (j - 1) * x := by
    calc
      x ^ j = x ^ ((j - 1) + 1) := by rw [show j - 1 + 1 = j by omega]
      _ = x ^ (j - 1) * x := by rw [pow_succ]
  have hterm1 :
      (2 * eta) ^ j *
          (64 * (Real.log 4 + 4) / (4 * eta) ^ j) =
        (1 / 2 : ℝ) ^ j * (64 * (Real.log 4 + 4)) := by
    calc
      (2 * eta) ^ j *
          (64 * (Real.log 4 + 4) / (4 * eta) ^ j) =
          64 * (Real.log 4 + 4) *
            ((2 * eta) ^ j / (4 * eta) ^ j) := by ring
      _ = 64 * (Real.log 4 + 4) *
            ((2 * eta) / (4 * eta)) ^ j := by rw [div_pow]
      _ = _ := by rw [hratio]; ring
  have hjpred : j - 1 + 1 = j := by omega
  have hterm2 :
      (2 * eta) ^ j *
          (((1024 * (Al : ℝ) / 3) * u) / (4 * eta) ^ (j - 1)) =
        (1 / 2 : ℝ) ^ j * ((4096 * (Al : ℝ) / 3) * h) := by
    calc
      (2 * eta) ^ j *
          (((1024 * (Al : ℝ) / 3) * u) / (4 * eta) ^ (j - 1)) =
          ((1024 * (Al : ℝ) / 3) * u) * (2 * eta) *
            ((2 * eta) ^ (j - 1) / (4 * eta) ^ (j - 1)) := by
              rw [hpowDecomp]
              ring
      _ = ((1024 * (Al : ℝ) / 3) * u) * (2 * eta) *
            ((2 * eta) / (4 * eta)) ^ (j - 1) := by rw [div_pow]
      _ = ((1024 * (Al : ℝ) / 3) * u) * (2 * eta) *
            (1 / 2 : ℝ) ^ (j - 1) := by rw [hratio]
      _ = _ := by
        rw [hpowDecomp (1 / 2 : ℝ)]
        dsimp [h]
        ring
  have hpow4 : (4 * eta) ^ (j - 1) ≤ (1 / 2 : ℝ) ^ (j - 1) :=
    pow_le_pow_left₀ h4eta h4etaHalf _
  have hterm3 :
      (2 * eta) ^ j *
          ((2 * (Af : ℝ) * u) / (1 / 2 : ℝ) ^ j) ≤
        (1 / 2 : ℝ) ^ j * (16 * (Af : ℝ) * h) := by
    have heq :
        (2 * eta) ^ j *
            ((2 * (Af : ℝ) * u) / (1 / 2 : ℝ) ^ j) =
          2 * (Af : ℝ) * u * (4 * eta) ^ j := by
      calc
        (2 * eta) ^ j *
            ((2 * (Af : ℝ) * u) / (1 / 2 : ℝ) ^ j) =
            (2 * (Af : ℝ) * u) *
              ((2 * eta) ^ j / (1 / 2 : ℝ) ^ j) := by ring
        _ = 2 * (Af : ℝ) * u *
              (((2 * eta) / (1 / 2 : ℝ)) ^ j) := by rw [← div_pow]
        _ = _ := by rw [hratio2]
    rw [heq, hpowDecomp (4 * eta), hpowDecomp (1 / 2 : ℝ)]
    calc
      2 * (Af : ℝ) * u * ((4 * eta) ^ (j - 1) * (4 * eta)) ≤
          2 * (Af : ℝ) * u *
            ((1 / 2 : ℝ) ^ (j - 1) * (4 * eta)) := by
              gcongr
      _ = (1 / 2 : ℝ) ^ (j - 1) * (1 / 2) *
          (16 * (Af : ℝ) * h) := by
            dsimp [h]
            ring
  have hpow2 : (2 * eta) ^ (j - 1) ≤ (1 / 2 : ℝ) ^ (j - 1) :=
    pow_le_pow_left₀ h2eta h2etaHalf _
  have hterm4 :
      (2 * eta) ^ j *
          (16 * ((Ad : ℝ) * u) / 3) ≤
        (1 / 2 : ℝ) ^ j * ((64 * (Ad : ℝ) / 3) * h) := by
    rw [hpowDecomp (2 * eta), hpowDecomp (1 / 2 : ℝ)]
    calc
      ((2 * eta) ^ (j - 1) * (2 * eta)) *
          (16 * ((Ad : ℝ) * u) / 3) ≤
        ((1 / 2 : ℝ) ^ (j - 1) * (2 * eta)) *
          (16 * ((Ad : ℝ) * u) / 3) := by
            gcongr
      _ = (1 / 2 : ℝ) ^ (j - 1) * (1 / 2) *
          ((64 * (Ad : ℝ) / 3) * h) := by
            dsimp [h]
            ring
  unfold pointwiseZeroDetectorError
  change (2 * eta) ^ j *
      (64 * (Real.log 4 + 4) / (4 * eta) ^ j +
        ((1024 * (Al : ℝ) / 3) * u) / (4 * eta) ^ (j - 1) +
        (2 * (Af : ℝ) * u) / (1 / 2 : ℝ) ^ j +
        16 * ((Ad : ℝ) * u) / 3) ≤ _
  rw [mul_add, mul_add, mul_add, hterm1, hterm2]
  exact (add_le_add (add_le_add le_rfl hterm3) hterm4).trans_eq (by
    unfold pointwiseSecondErrorCoefficient
    dsimp only [h]
    ring)

/-- A natural-valued finitely supported function has at least as much total
mass as the cardinality of its support. -/
theorem finsupp_support_card_le_sum_nat {α : Type*} (Z : α →₀ ℕ) :
    Z.support.card ≤ Z.sum (fun _ m ↦ m) := by
  rw [Finsupp.sum]
  calc
    Z.support.card = ∑ _rho ∈ Z.support, 1 := by simp
    _ ≤ ∑ rho ∈ Z.support, Z rho := by
      apply Finset.sum_le_sum
      intro rho hrho
      exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hrho)

/-- The elementary exponential estimate used to absorb the two polynomial
factors in Turan's coefficient loss. -/
theorem nat_mul_succ_le_four_pow {K : ℕ} (hK : 1 ≤ K) :
    K * (K + 1) ≤ 4 ^ K := by
  induction K with
  | zero => omega
  | succ k ih =>
      by_cases hk : k = 0
      · subst k
        norm_num
      · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
        have hih := ih hk1
        rw [pow_succ]
        calc
          (k + 1) * (k + 1 + 1) ≤ 4 * (k * (k + 1)) := by nlinarith
          _ ≤ 4 * 4 ^ k := Nat.mul_le_mul_left 4 hih
          _ = 4 ^ k * 4 := by ring

/-- For positive `H`, the factor `H` is absorbed by a half-power. -/
theorem nat_le_two_pow_pred {H : ℕ} (hH : 1 ≤ H) :
    H ≤ 2 ^ (H - 1) := by
  induction H with
  | zero => omega
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        norm_num
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        have hih := ih hn1
        have hpred : n + 1 - 1 = n := by omega
        rw [hpred]
        calc
          n + 1 ≤ 2 * n := by omega
          _ ≤ 2 * 2 ^ (n - 1) := Nat.mul_le_mul_left 2 hih
          _ = 2 ^ (n - 1) * 2 := by ring
          _ = 2 ^ n := by rw [← pow_succ, show n - 1 + 1 = n by omega]

/-- Closed form of the loss factor in Turan's second theorem. -/
theorem turanSecondLoss_eq_closed (K M : ℕ) :
    turanSecondLoss K M =
      ((K : ℝ) * (K + 1 : ℝ) / 2) *
        (17 / 16 : ℝ) ^ M * (136 : ℝ) ^ K := by
  unfold turanSecondLoss
  calc
    (K : ℝ) * ((17 / 16 : ℝ) ^ M *
        ((K + 1 : ℝ) * (2 : ℝ) ^ K) /
          (2 * (68 : ℝ)⁻¹ ^ K)) =
        ((K : ℝ) * (K + 1 : ℝ) / 2) *
          (17 / 16 : ℝ) ^ M *
            ((2 : ℝ) ^ K / (68 : ℝ)⁻¹ ^ K) := by ring
    _ = ((K : ℝ) * (K + 1 : ℝ) / 2) *
          (17 / 16 : ℝ) ^ M *
            (((2 : ℝ) / (68 : ℝ)⁻¹) ^ K) := by rw [← div_pow]
    _ = _ := by norm_num

/-- A sufficiently large starting-order multiplier makes the loss in
Turan's second theorem absorb any coefficient which is linear in the
height parameter.  Crucially, the chosen multiplier depends only on the
two fixed coefficients, not on the conductor, height, or zero. -/
theorem exists_turanSecond_contraction_parameter
    (κ : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℕ, 1 ≤ D ∧
      ∀ (H K j : ℕ), 1 ≤ H → 1 ≤ K → K ≤ κ * H →
        D * H + 1 ≤ j →
        turanSecondLoss K (D * H) * (1 / 2 : ℝ) ^ j *
            (C * H) ≤ 1 / 4 := by
  let W : ℝ := max 1 C
  have hW : 1 ≤ W := le_max_left _ _
  have hWpos : 0 < W := lt_of_lt_of_le zero_lt_one hW
  have htarget : 0 < (1 : ℝ) / (2 * W * (544 : ℝ) ^ κ) := by positivity
  obtain ⟨D₀, hD₀⟩ := exists_pow_lt_of_lt_one htarget
    (by norm_num : (17 / 32 : ℝ) < 1)
  let D := max 1 D₀
  have hD : 1 ≤ D := le_max_left _ _
  have hpowD : (17 / 32 : ℝ) ^ D <
      1 / (2 * W * (544 : ℝ) ^ κ) := by
    exact (pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (le_max_right 1 D₀)).trans_lt hD₀
  have hbase : (17 / 32 : ℝ) ^ D * (544 : ℝ) ^ κ < 1 / (2 * W) := by
    have h544 : 0 < (544 : ℝ) ^ κ := by positivity
    calc
      (17 / 32 : ℝ) ^ D * (544 : ℝ) ^ κ <
          (1 / (2 * W * (544 : ℝ) ^ κ)) * (544 : ℝ) ^ κ :=
        mul_lt_mul_of_pos_right hpowD h544
      _ = 1 / (2 * W) := by field_simp
  refine ⟨D, hD, ?_⟩
  intro H K j hH hK hKκ hj
  let b : ℝ := (17 / 32 : ℝ) ^ D * (544 : ℝ) ^ κ
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hbHalf : b ≤ 1 / 2 := by
    exact hbase.le.trans (by
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * W)
        (by norm_num : (0 : ℝ) < 2)).2
      nlinarith [hW])
  have hCb : C * b ≤ 1 / 2 := by
    have hCW : C ≤ W := le_max_right _ _
    exact (calc
        C * b ≤ W * b := mul_le_mul_of_nonneg_right hCW hb0
        _ < W * (1 / (2 * W)) := mul_lt_mul_of_pos_left hbase hWpos
        _ = 1 / 2 := by field_simp).le
  have hHhalf : (H : ℝ) * (1 / 2 : ℝ) ^ (H - 1) ≤ 1 := by
    have hnat := nat_le_two_pow_pred hH
    have hcast : (H : ℝ) ≤ (2 : ℝ) ^ (H - 1) := by exact_mod_cast hnat
    have hpowPos : 0 < (2 : ℝ) ^ (H - 1) := by positivity
    calc
      (H : ℝ) * (1 / 2 : ℝ) ^ (H - 1) =
          (H : ℝ) / (2 : ℝ) ^ (H - 1) := by rw [one_div_pow]; ring
      _ ≤ (2 : ℝ) ^ (H - 1) / (2 : ℝ) ^ (H - 1) :=
        div_le_div_of_nonneg_right hcast hpowPos.le
      _ = 1 := div_self hpowPos.ne'
  have hpolyNat := nat_mul_succ_le_four_pow hK
  have hpoly : (K : ℝ) * (K + 1 : ℝ) ≤ (4 : ℝ) ^ K := by
    exact_mod_cast hpolyNat
  have hjpow : (1 / 2 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ (D * H + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
  have hKpow : (544 : ℝ) ^ K ≤ (544 : ℝ) ^ (κ * H) :=
    pow_le_pow_right₀ (by norm_num) hKκ
  have hloss := turanSecondLoss_eq_closed K (D * H)
  rw [hloss]
  have hraw :
      (((K : ℝ) * (K + 1 : ℝ) / 2) *
          (17 / 16 : ℝ) ^ (D * H) * (136 : ℝ) ^ K) *
          (1 / 2 : ℝ) ^ j * (C * H) ≤
        (1 / 4 : ℝ) * ((17 / 32 : ℝ) ^ (D * H) *
          (544 : ℝ) ^ K) * (C * H) := by
    calc
      (((K : ℝ) * (K + 1 : ℝ) / 2) *
          (17 / 16 : ℝ) ^ (D * H) * (136 : ℝ) ^ K) *
          (1 / 2 : ℝ) ^ j * (C * H) ≤
          (((4 : ℝ) ^ K / 2) *
            (17 / 16 : ℝ) ^ (D * H) * (136 : ℝ) ^ K) *
            (1 / 2 : ℝ) ^ (D * H + 1) * (C * H) := by
              gcongr
      _ = (1 / 4 : ℝ) * ((17 / 32 : ℝ) ^ (D * H) *
          (544 : ℝ) ^ K) * (C * H) := by
            rw [pow_add, pow_one]
            have hfirst :
                (17 / 16 : ℝ) ^ (D * H) * (1 / 2 : ℝ) ^ (D * H) =
                  (17 / 32 : ℝ) ^ (D * H) := by
              rw [← mul_pow]
              norm_num
            have hsecond : (4 : ℝ) ^ K * (136 : ℝ) ^ K =
                (544 : ℝ) ^ K := by
              rw [← mul_pow]
              norm_num
            calc
              ((4 : ℝ) ^ K / 2 * (17 / 16 : ℝ) ^ (D * H) *
                    (136 : ℝ) ^ K) *
                  ((1 / 2 : ℝ) ^ (D * H) * (1 / 2)) * (C * H) =
                  (1 / 4 : ℝ) *
                    (((17 / 16 : ℝ) ^ (D * H) *
                      (1 / 2 : ℝ) ^ (D * H)) *
                    ((4 : ℝ) ^ K * (136 : ℝ) ^ K)) * (C * H) := by ring
              _ = _ := by rw [hfirst, hsecond]
  calc
    (((K : ℝ) * (K + 1 : ℝ) / 2) *
        (17 / 16 : ℝ) ^ (D * H) * (136 : ℝ) ^ K) *
        (1 / 2 : ℝ) ^ j * (C * H) ≤
        (1 / 4 : ℝ) * ((17 / 32 : ℝ) ^ (D * H) *
          (544 : ℝ) ^ K) * (C * H) := hraw
    _ ≤ (1 / 4 : ℝ) * ((17 / 32 : ℝ) ^ (D * H) *
          (544 : ℝ) ^ (κ * H)) * (C * H) := by gcongr
    _ = (1 / 4 : ℝ) * b ^ H * (C * H) := by
      dsimp [b]
      rw [pow_mul, pow_mul, mul_pow]
    _ = (1 / 4 : ℝ) * ((C * b) *
          ((H : ℝ) * b ^ (H - 1))) := by
      rw [show b ^ H = b ^ (H - 1) * b by
        calc
          b ^ H = b ^ ((H - 1) + 1) := by congr 1 <;> omega
          _ = b ^ (H - 1) * b := by rw [pow_succ]]
      ring
    _ ≤ (1 / 4 : ℝ) * ((1 / 2 : ℝ) * 1) := by
      gcongr
      calc
        (H : ℝ) * b ^ (H - 1) ≤
            (H : ℝ) * (1 / 2 : ℝ) ^ (H - 1) := by gcongr
        _ ≤ 1 := hHhalf
    _ ≤ 1 / 4 := by norm_num

end

end Erdos48
