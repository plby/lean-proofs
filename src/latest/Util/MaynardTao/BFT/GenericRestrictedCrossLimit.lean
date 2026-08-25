import Util.MaynardTao.BFT.LargeFiberFactor
import Util.MaynardTao.BFT.GenericRestrictedCrossBound

/-!
# The generic restricted S2 cross correction is negligible
-/

namespace MaynardBFT.Sieve

open Erdos6.Maynard

open Filter

noncomputable section

variable [P : Parameters] [T : ShiftTuple]

theorem tendsto_normalizedTupleRestrictedCross_zero
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha) (m : H) :
    Tendsto (fun N : ℕ =>
      tupleRestrictedCross H alpha (tupleLargeCandidate H) N m /
        (BoundedGaps.Maynard.preSieveSingularSeries
            (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
          Real.log (maynardRadius alpha N) ^ 2 *
          tupleNaturalScale (tupleOffFace H m) alpha N))
      atTop (nhds 0) := by
  let D : ℕ → ℕ := fun N =>
    BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  let R : ℕ → ℕ := fun N => maynardRadius alpha N
  let L : ℕ → ℝ := fun N => Real.log (R N)
  let S : ℕ → ℝ := fun N =>
    BoundedGaps.Maynard.preSieveSingularSeries (D N)
  let Q : ℕ → ℝ := fun N => S N * L N
  let M : ℕ → ℝ := fun N =>
    BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeMean
      (maynardModulus N) (R N)
  let k := (Finset.univ.erase m).card
  let A : ℕ → ℝ := fun N =>
    8 / (D N : ℝ) + (8 * Real.exp 8 / (D N : ℝ)) *
      (1 + 8 * Real.exp 8 / (D N : ℝ)) ^ (k - 1)
  let E : ℕ → ℝ := fun N => tupleRestrictedTransformEnvelope H alpha N m
  let Tail : ℕ → ℝ := fun N =>
    (32 * Real.exp 32 / (D N : ℝ)) *
      ((BoundedGaps.Maynard.offDiagonalPairs H).card : ℝ) *
      (Real.exp 32) ^
        ((BoundedGaps.Maynard.offDiagonalPairs H).card - 1)
  let Ctail : ℝ := 32 * Real.exp 32 *
    ((BoundedGaps.Maynard.offDiagonalPairs H).card : ℝ) *
    (Real.exp 32) ^
      ((BoundedGaps.Maynard.offDiagonalPairs H).card - 1)
  let Cenv : ℝ := 16 * (1 + (k : ℝ))
  have hDtop : Tendsto (fun N => (D N : ℝ)) atTop atTop := by
    dsimp [D]
    exact tendsto_natCast_atTop_atTop.comp
      BoundedGaps.Maynard.tendsto_shifted_tripleLogCutoff
  have hinvD : Tendsto (fun N => (1 : ℝ) / D N) atTop (nhds 0) := by
    simpa [one_div] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
        atTop (nhds 1)).div_atTop hDtop)
  have hterm : Tendsto (fun N => 8 * Real.exp 8 / D N)
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hinvD.const_mul (8 * Real.exp 8)
  have hpow : Tendsto (fun N =>
      (1 + 8 * Real.exp 8 / D N) ^ (k - 1)) atTop (nhds 1) := by
    simpa [add_comm] using (hterm.add_const 1).pow (k - 1)
  have hA : Tendsto A atTop (nhds 0) := by
    have hfirst : Tendsto (fun N => (8 : ℝ) / D N)
        atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using hinvD.const_mul 8
    have hsecond := hterm.mul hpow
    simpa [A] using hfirst.add hsecond
  have hAsmall : ∀ᶠ N : ℕ in atTop, 0 ≤ A N ∧ A N ≤ 1 := by
    filter_upwards [hA.eventually
      (Metric.ball_mem_nhds (0 : ℝ) one_pos),
      hDtop.eventually (eventually_gt_atTop 0)] with N hN hDN
    have h0 : 0 ≤ A N := by dsimp [A]; positivity
    exact ⟨h0, le_of_lt (by
      simpa [Real.dist_eq, abs_of_nonneg h0] using hN)⟩
  have hLtop : Tendsto L atTop atTop := by
    simpa [L, R, maynardRadius] using
      BoundedGaps.Maynard.tendsto_log_engelsmaMaynardRadius_atTop halpha
  have hLratio : ∀ᶠ N : ℕ in atTop,
      0 ≤ (1 + L N) / L N ∧ (1 + L N) / L N ≤ 2 := by
    filter_upwards [hLtop.eventually (eventually_ge_atTop (1 : ℝ))] with N hN
    have hp : 0 < L N := lt_of_lt_of_le zero_lt_one hN
    exact ⟨div_nonneg (by linarith) hp.le, (div_le_iff₀ hp).2 (by linarith)⟩
  have hS : ∀ᶠ N : ℕ in atTop, 0 < S N ∧ S N ≤ 1 := by
    filter_upwards [] with N
    exact ⟨BoundedGaps.Maynard.preSieveSingularSeries_pos _,
      BoundedGaps.Maynard.preSieveSingularSeries_le_one _⟩
  have hQ : ∀ᶠ N : ℕ in atTop, 0 < Q N := by
    filter_upwards [hS, hLtop.eventually (eventually_gt_atTop 0)] with
        N hSN hLN
    exact mul_pos hSN.1 hLN
  have hLpos : ∀ᶠ N : ℕ in atTop, 0 < L N :=
    hLtop.eventually (eventually_gt_atTop 0)
  have hmean : Tendsto (fun N => M N / Q N) atTop (nhds 1) := by
    simpa [M, Q, S, L, D, R, maynardModulus,
      BoundedGaps.Maynard.engelsmaMaynardModulus] using
      BoundedGaps.Maynard.tendsto_engelsmaReciprocalGSquarefreeMean_div_leadingTerm_one
        halpha
  have hmeanPow : Tendsto (fun N => M N ^ k / Q N ^ k)
      atTop (nhds 1) := by simpa [div_pow] using hmean.pow k
  have hmassLe : ∀ᶠ N : ℕ in atTop, M N ^ k / Q N ^ k ≤ 2 := by
    filter_upwards [hmeanPow.eventually
      (Metric.ball_mem_nhds (1 : ℝ) one_pos)] with N hN
    have hd : |M N ^ k / Q N ^ k - 1| < 1 := by
      simpa [Real.dist_eq] using hN
    linarith [le_abs_self (M N ^ k / Q N ^ k - 1)]
  have hcond :=
    BoundedGaps.Maynard.eventually_engelsmaMaynardCrossBound_conditions halpha
  have hRone :=
    BoundedGaps.Maynard.eventually_one_lt_engelsmaMaynardRadius halpha
  have hD2 : ∀ᶠ N : ℕ in atTop, 2 ≤ D N := by
    obtain ⟨N₀, hN₀⟩ := BoundedGaps.Maynard.exists_tripleLogCutoff_ge 2
    filter_upwards [eventually_ge_atTop (N₀ + 1)] with N hN
    exact hN₀ (N - 1) (by omega)
  have henv : ∀ᶠ N : ℕ in atTop,
      0 ≤ E N / Q N ∧ E N / Q N ≤ Cenv := by
    filter_upwards [hcond, hD2, hLratio, hAsmall, hS,
      hLtop.eventually (eventually_gt_atTop 0)] with
      N hCN hD2N hLR hAN hSN hLN
    have hEdivL : E N / L N =
        8 * S N * ((1 + L N) / L N) * (1 + (k : ℝ) * A N) := by
      dsimp [E, L, S, A, D, R, k]
      unfold tupleRestrictedTransformEnvelope
      simp only [maynardModulus, BoundedGaps.Maynard.engelsmaMaynardModulus,
        Finset.univ_eq_attach]
      rw [BoundedGaps.Maynard.preSieveSingularSeries_eq_totient_div]
      field_simp [hLN.ne']
    have hEdiv : E N / Q N =
        8 * ((1 + L N) / L N) * (1 + (k : ℝ) * A N) := by
      calc
        E N / Q N = (E N / L N) / S N := by
          dsimp [Q]
          field_simp [hLN.ne', hSN.1.ne']
        _ = (8 * S N * ((1 + L N) / L N) *
            (1 + (k : ℝ) * A N)) / S N := by rw [hEdivL]
        _ = 8 * ((1 + L N) / L N) *
            (1 + (k : ℝ) * A N) := by field_simp [hSN.1.ne']
    have hfac0 : 0 ≤ 1 + (k : ℝ) * A N := by positivity
    have hfacLe : 1 + (k : ℝ) * A N ≤ 1 + (k : ℝ) := by
      simpa [add_comm] using add_le_add_left
        (mul_le_mul_of_nonneg_left hAN.2 (Nat.cast_nonneg k)) 1
    rw [hEdiv]
    constructor
    · positivity
    · calc
        8 * ((1 + L N) / L N) * (1 + (k : ℝ) * A N) ≤
            8 * 2 * (1 + (k : ℝ) * A N) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hLR.2 (by norm_num)) hfac0
        _ ≤ 8 * 2 * (1 + (k : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hfacLe (by norm_num)
        _ = Cenv := by dsimp [Cenv]; ring
  have htail : Tendsto Tail atTop (nhds 0) := by
    have h := hinvD.const_mul Ctail
    simpa [Tail, Ctail, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      using h
  have hzero : Tendsto (fun N => (2 * Cenv ^ 2) * Tail N)
      atTop (nhds 0) := by
    simpa using htail.const_mul (2 * Cenv ^ 2)
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ hzero
  filter_upwards [hcond, hRone, hD2, henv, hmassLe, hQ, hLpos] with
      N hCN hRoneN hD2N hEN hMN hQN hLN
  have hcorr' := abs_tupleRestrictedCross_le_explicit m hRoneN hD2N hCN.2.2
  have hM0 : 0 ≤ M N := by
    unfold M BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeMean
    exact Finset.sum_nonneg fun n hn => tupleReciprocalGSquarefreeAF_nonneg _ n
  have hTail0 : 0 ≤ Tail N := by dsimp [Tail]; positivity
  have hden : 0 < Q N ^ (k + 2) := pow_pos hQN _
  have hcard : Fintype.card (tupleOffFace H m) = k := by
    calc
      Fintype.card (tupleOffFace H m) = (tupleOffFace H m).card :=
        Fintype.card_coe _
      _ = H.card - 1 := by
        unfold tupleOffFace
        rw [Finset.card_erase_of_mem m.2]
      _ = k := by
        dsimp [k]
        rw [Finset.card_erase_of_mem (Finset.mem_attach H m), Finset.card_attach]
  have houterEq : tupleNaturalScale (tupleOffFace H m) alpha N = Q N ^ k := by
    unfold tupleNaturalScale
    rw [hcard]
  have hscaleEq :
      BoundedGaps.Maynard.preSieveSingularSeries (D N) ^ 2 * L N ^ 2 *
          tupleNaturalScale (tupleOffFace H m) alpha N =
        Q N ^ (k + 2) := by
    rw [houterEq]
    dsimp [Q]
    rw [pow_add]
    ring
  rw [show BoundedGaps.Maynard.preSieveSingularSeries
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
        Real.log (maynardRadius alpha N) ^ 2 *
          tupleNaturalScale (tupleOffFace H m) alpha N =
        Q N ^ (k + 2) by simpa [D, L, R] using hscaleEq,
      abs_div, abs_of_pos hden]
  calc
    |tupleRestrictedCross H alpha (tupleLargeCandidate H) N m| /
          Q N ^ (k + 2) ≤
        E N ^ 2 * Tail N * M N ^ k / Q N ^ (k + 2) :=
      div_le_div_of_nonneg_right (by
        simpa [E, Tail, M, D, R, k] using hcorr') hden.le
    _ = (E N / Q N) ^ 2 * Tail N * (M N ^ k / Q N ^ k) := by
      field_simp [hQN.ne']
      ring
    _ ≤ Cenv ^ 2 * Tail N * (M N ^ k / Q N ^ k) := by
      have hs := pow_le_pow_left₀ hEN.1 hEN.2 2
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hs hTail0)
        (div_nonneg (pow_nonneg hM0 _) (pow_nonneg hQN.le _))
    _ ≤ Cenv ^ 2 * Tail N * 2 := by
      exact mul_le_mul_of_nonneg_left hMN
        (mul_nonneg (sq_nonneg _) hTail0)
    _ = (2 * Cenv ^ 2) * Tail N := by ring

end

end MaynardBFT.Sieve
