import ErdosProblems.Erdos6.LargeRestrictedYBridge

/-!
# Strong decay of the restricted-Y perturbation envelope
-/

namespace Erdos6.Maynard

open Filter

noncomputable section

theorem tendsto_tupleCoordinateOneSquarePerturbationEnvelope_div_squareScale_zero
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha) (m : H) :
    Tendsto (fun N : ℕ =>
      tupleCoordinateOneSquarePerturbationEnvelope H
        (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
        (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) m 1 /
      ((BoundedGaps.Maynard.preSieveSingularSeries
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) : ℝ) ^ 2 *
        Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) ^ 2))
      atTop (nhds 0) := by
  let k : ℝ := ((Finset.univ.erase m).card : ℝ)
  let L : ℕ → ℝ := fun N => Real.log
    (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
  let D : ℕ → ℝ := fun N =>
    BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  let S : ℕ → ℝ := fun N =>
    BoundedGaps.Maynard.preSieveSingularSeries
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
  let A : ℕ → ℝ := fun N =>
    8 / D N + (8 * Real.exp 8 / D N) *
      (1 + 8 * Real.exp 8 / D N) ^ ((Finset.univ.erase m).card - 1)
  have hL : Tendsto L atTop atTop := by
    simpa [L] using
      BoundedGaps.Maynard.tendsto_log_engelsmaMaynardRadius_atTop halpha
  have hD : Tendsto D atTop atTop := by
    change Tendsto (fun N : ℕ =>
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1) : ℝ)) atTop atTop
    exact tendsto_natCast_atTop_atTop.comp
      BoundedGaps.Maynard.tendsto_shifted_tripleLogCutoff
  have hinvD : Tendsto (fun N => (1 : ℝ) / D N) atTop (nhds 0) := by
    simpa [one_div] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
        atTop (nhds 1)).div_atTop hD)
  have hterm : Tendsto (fun N => 8 * Real.exp 8 / D N)
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hinvD.const_mul (8 * Real.exp 8)
  have hpow : Tendsto (fun N =>
      (1 + 8 * Real.exp 8 / D N) ^ ((Finset.univ.erase m).card - 1))
      atTop (nhds 1) := by
    simpa [add_comm] using (hterm.add_const 1).pow
      ((Finset.univ.erase m).card - 1)
  have hA : Tendsto A atTop (nhds 0) := by
    have hfirst : Tendsto (fun N => (8 : ℝ) / D N)
        atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using hinvD.const_mul 8
    have hsecond : Tendsto (fun N =>
        (8 * Real.exp 8 / D N) *
          (1 + 8 * Real.exp 8 / D N) ^
            ((Finset.univ.erase m).card - 1)) atTop (nhds 0) := by
      simpa using hterm.mul hpow
    simpa [A] using hfirst.add hsecond
  have hsmallA : ∀ᶠ N : ℕ in atTop, 0 ≤ A N ∧ A N ≤ 1 := by
    filter_upwards [hA.eventually
      (Metric.ball_mem_nhds (0 : ℝ) one_pos),
      hD.eventually (eventually_gt_atTop 0)] with N hN hDN
    have h0 : 0 ≤ A N := by dsimp [A]; positivity
    exact ⟨h0, le_of_lt (by
      simpa [Real.dist_eq, abs_of_nonneg h0] using hN)⟩
  have hLone : ∀ᶠ N : ℕ in atTop, 1 ≤ L N :=
    hL.eventually (eventually_ge_atTop 1)
  have hWL :=
    BoundedGaps.Maynard.eventually_engelsmaMaynardCrossBound_conditions halpha
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have hupper : Tendsto (fun N : ℕ =>
      (512 * k * (1 + k)) * A N) atTop (nhds 0) := by
    simpa using hA.const_mul (512 * k * (1 + k))
  apply squeeze_zero' (Eventually.of_forall (fun N => abs_nonneg _)) ?_ hupper
  filter_upwards [hsmallA, hLone, hWL] with N hAN hL1 hcond
  let R := BoundedGaps.Maynard.engelsmaMaynardRadius alpha N
  let DD := BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  let SS := BoundedGaps.Maynard.preSieveSingularSeries DD
  let LL := L N
  let MM := BoundedGaps.Maynard.preSievedCoordinateInvTotientMass
    (primorial DD) R
  let AA := A N
  have hS : 0 < SS := BoundedGaps.Maynard.preSieveSingularSeries_pos DD
  have hLpos : 0 < LL := lt_of_lt_of_le zero_lt_one hL1
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hAA0 : 0 ≤ AA := by simpa [AA] using hAN.1
  have hAA1 : AA ≤ 1 := by simpa [AA] using hAN.2
  have hSeq : SS = (Nat.totient (primorial DD) : ℝ) /
      (primorial DD : ℝ) := by
    simpa [SS] using
      BoundedGaps.Maynard.preSieveSingularSeries_eq_totient_div DD
  have hM : MM ≤ 8 * SS * (1 + LL) := by
    have hp : MM ≤ BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean
        (primorial DD) R := by
      simpa [MM, BoundedGaps.Maynard.preSievedCoordinateInvTotientMass] using
        BoundedGaps.Maynard.preSievedCoordinateInvTotientSum_le
          (primorial DD) R
    have hm := BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean_le_log
      (W := primorial DD) (Q := R) (primorial_pos DD) (by
        simpa [R, DD, BoundedGaps.Maynard.engelsmaMaynardModulus] using
          hcond.2.2)
    simpa [MM, SS, LL, R, DD,
      BoundedGaps.Maynard.preSieveSingularSeries_eq_totient_div] using
      hp.trans hm
  have hratio : (1 + LL) / LL ≤ 2 := by
    apply (div_le_iff₀ hLpos).2
    linarith
  have hMr : MM / (SS * LL) ≤ 8 * ((1 + LL) / LL) := by
    calc
      MM / (SS * LL) ≤ (8 * SS * (1 + LL)) / (SS * LL) :=
        div_le_div_of_nonneg_right hM (by positivity)
      _ = 8 * ((1 + LL) / LL) := by field_simp [hS.ne', hLpos.ne']
  have hMr0 : 0 ≤ MM / (SS * LL) := by
    unfold MM BoundedGaps.Maynard.preSievedCoordinateInvTotientMass
    positivity
  have hfac : 0 ≤ 8 * ((1 + LL) / LL) := by positivity
  have hfacLe : 8 * ((1 + LL) / LL) ≤ 16 := by nlinarith
  have hfirst : MM / (SS * LL) + k * 8 * ((1 + LL) / LL) * AA ≤
      16 * (1 + k) := by
    have ht : k * 8 * ((1 + LL) / LL) * AA ≤ 16 * k := by
      calc
        k * 8 * ((1 + LL) / LL) * AA ≤
            k * 8 * ((1 + LL) / LL) := by
          simpa [mul_assoc] using mul_le_mul_of_nonneg_left hAA1
            (mul_nonneg hk hfac)
        _ ≤ 16 * k := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            mul_le_mul_of_nonneg_left hfacLe hk
    calc
      _ ≤ 8 * ((1 + LL) / LL) + 16 * k := add_le_add hMr ht
      _ ≤ 16 + 16 * k := add_le_add hfacLe le_rfl
      _ = 16 * (1 + k) := by ring
  have hsecond : k * 8 * ((1 + LL) / LL) * AA ≤ 16 * k * AA := by
    have ht : k * 8 * ((1 + LL) / LL) ≤ 16 * k := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_left hfacLe hk
    exact mul_le_mul_of_nonneg_right ht hAA0
  have hratioBound :
      2 * (MM / (SS * LL) + k * 8 * ((1 + LL) / LL) * AA) *
          (k * 8 * ((1 + LL) / LL) * AA) ≤
        512 * k * (1 + k) * AA := by
    calc
      _ ≤ (2 * (16 * (1 + k))) * (16 * k * AA) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hfirst (by positivity))
          hsecond (by positivity) (by positivity)
      _ = _ := by ring
  have hEid :
      tupleCoordinateOneSquarePerturbationEnvelope H R DD m 1 /
          (SS ^ 2 * LL ^ 2) =
        2 * (MM / (SS * LL) + k * 8 * ((1 + LL) / LL) * AA) *
          (k * 8 * ((1 + LL) / LL) * AA) := by
    unfold tupleCoordinateOneSquarePerturbationEnvelope
    rw [← hSeq]
    field_simp [hS.ne', hLpos.ne']
    ring
  have hE0 : 0 ≤ tupleCoordinateOneSquarePerturbationEnvelope
      H R DD m 1 := by
    unfold tupleCoordinateOneSquarePerturbationEnvelope
    rw [← hSeq]
    have hMM : 0 ≤ MM := by
      unfold MM BoundedGaps.Maynard.preSievedCoordinateInvTotientMass
      positivity
    positivity
  rw [abs_of_nonneg (div_nonneg hE0 (by positivity)), hEid]
  simpa [k, L, D, S, A, R, DD, SS, LL, MM, AA] using hratioBound

end

end Erdos6.Maynard
