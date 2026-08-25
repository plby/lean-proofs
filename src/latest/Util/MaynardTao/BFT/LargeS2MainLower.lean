import ErdosProblems.Erdos6.GenericPrimeCount
import Util.MaynardTao.BFT.LargeRestrictedGKernelLimit

/-!
# A positive lower bound for the normalized large-tuple S2 main term
-/

namespace MaynardBFT.Sieve

open Erdos6.Maynard

open Filter
open scoped BigOperators

noncomputable section

variable [P : Parameters] [T : ShiftTuple]

private theorem restricted_main_term_normalized_eq
    {H : Finset ℕ} {alpha : ℝ} {N : ℕ} (m : H)
    (hN : 0 < N)
    (hRnat : 0 < Real.log (maynardRadius alpha N))
    (hRreal : 0 < Real.log
      (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)) :
    (tupleShiftedPrimeIntervalCount N m *
        ((Nat.totient (maynardModulus N) : ℝ)⁻¹ *
          tupleRestrictedGKernel H alpha (tupleLargeCandidate H) N m)) /
        tupleMaynardScale H alpha N =
      ((tupleShiftedPrimeIntervalCount N m / (N : ℝ)) *
          Real.log (maynardRadius alpha N)) *
        (Real.log (maynardRadius alpha N) /
          Real.log (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)) ^
            Fintype.card H *
        (tupleRestrictedGKernel H alpha (tupleLargeCandidate H) N m /
          (BoundedGaps.Maynard.preSieveSingularSeries
              (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
            Real.log (maynardRadius alpha N) ^ 2 *
            tupleNaturalScale (tupleOffFace H m) alpha N)) := by
  let D := BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  let W := maynardModulus N
  let S := BoundedGaps.Maynard.preSieveSingularSeries D
  let Ln := Real.log (maynardRadius alpha N)
  let Lr := Real.log
    (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)
  let K := Fintype.card H
  have hWnat : 0 < W := by
    dsimp [W, maynardModulus]
    exact primorial_pos _
  have hW : (0 : ℝ) < W := by exact_mod_cast hWnat
  have hphiNat : 0 < Nat.totient W := Nat.totient_pos.mpr hWnat
  have hphi : (0 : ℝ) < Nat.totient W := by exact_mod_cast hphiNat
  have hS : 0 < S := by
    dsimp [S]
    exact BoundedGaps.Maynard.preSieveSingularSeries_pos _
  have hK : 0 < K := by
    exact Fintype.card_pos_iff.mpr ⟨m⟩
  have hcard : Fintype.card (tupleOffFace H m) = K - 1 := by
    calc
      Fintype.card (tupleOffFace H m) = (tupleOffFace H m).card :=
        Fintype.card_coe _
      _ = H.card - 1 := by
        unfold tupleOffFace
        rw [Finset.card_erase_of_mem m.2]
      _ = K - 1 := by simp [K]
  have hnatScale :
      S ^ 2 * Ln ^ 2 * tupleNaturalScale (tupleOffFace H m) alpha N =
        (S * Ln) ^ (K + 1) := by
    have hExp : K + 1 = 2 + (K - 1) := by omega
    unfold tupleNaturalScale
    rw [hcard, hExp, pow_add]
    ring
  change
    (tupleShiftedPrimeIntervalCount N m *
        ((Nat.totient W : ℝ)⁻¹ *
          tupleRestrictedGKernel H alpha (tupleLargeCandidate H) N m)) /
        tupleMaynardScale H alpha N = _
  rw [show
      BoundedGaps.Maynard.preSieveSingularSeries
            (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
          Real.log (maynardRadius alpha N) ^ 2 *
          tupleNaturalScale (tupleOffFace H m) alpha N =
        (S * Ln) ^ (K + 1) by simpa [S, Ln, D] using hnatScale]
  unfold tupleMaynardScale BoundedGaps.Maynard.maynardSieveScale
  change
    (tupleShiftedPrimeIntervalCount N m *
        ((Nat.totient W : ℝ)⁻¹ *
          tupleRestrictedGKernel H alpha (tupleLargeCandidate H) N m)) /
        (((Nat.totient W : ℝ) ^ K * (N : ℝ) * Lr ^ K) /
          (W : ℝ) ^ (K + 1)) = _
  have hSeq : S = (Nat.totient W : ℝ) / (W : ℝ) := by
    simpa [S, W, D, maynardModulus,
      BoundedGaps.Maynard.engelsmaMaynardModulus] using
      BoundedGaps.Maynard.preSieveSingularSeries_eq_totient_div D
  rw [hSeq]
  dsimp [Ln, Lr, K]
  simp only [div_pow]
  ring_nf
  field_simp [hW.ne', hphi.ne', (Nat.cast_pos.mpr hN).ne',
    hRnat.ne', hRreal.ne', inv_inv]
  let T := tupleShiftedPrimeIntervalCount N m *
    tupleRestrictedGKernel H alpha (tupleLargeCandidate H) N m
  change T = T * Real.log (maynardRadius alpha N) ^ Fintype.card H *
    (1 / Real.log (maynardRadius alpha N)) ^ Fintype.card H
  have hcancel :
      Real.log (maynardRadius alpha N) ^ Fintype.card H *
          (1 / Real.log (maynardRadius alpha N)) ^ Fintype.card H = 1 := by
    rw [← mul_pow]
    field_simp [hRnat.ne']
    exact one_pow _
  rw [mul_assoc, hcancel, mul_one]

theorem eventually_largeTupleS2Main_normalized_gt (v : ℕ → ℕ)
    {alpha beta c : ℝ} (halpha : 0 < alpha)
    (hbeta : 0 < beta) (hbetaAlpha : beta < alpha)
    (hc : 0 < c) (hcCoeff : c < largeFiberLowerCoefficient) :
    ∀ᶠ N : ℕ in atTop,
      (largeK : ℝ) * beta * c <
        tupleMaynardS2Main largePowerTuple alpha v
            largeTupleCandidate N /
          tupleMaynardScale largePowerTuple alpha N := by
  let factor := fun (m : largePowerTuple) (N : ℕ) =>
    ((tupleShiftedPrimeIntervalCount N m / (N : ℝ)) *
        Real.log (maynardRadius alpha N)) *
      (Real.log (maynardRadius alpha N) /
        Real.log (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)) ^
          Fintype.card largePowerTuple
  let kernel := fun (m : largePowerTuple) (N : ℕ) =>
    tupleRestrictedGKernel largePowerTuple alpha
        (tupleLargeCandidate largePowerTuple) N m /
      (BoundedGaps.Maynard.preSieveSingularSeries
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
        Real.log (maynardRadius alpha N) ^ 2 *
        tupleNaturalScale (largeOffFace m) alpha N)
  have hfactor (m : largePowerTuple) :
      Tendsto (factor m) atTop (nhds alpha) := by
    have hp := tendsto_tupleShiftedPrimeIntervalFactor halpha m
    have hr :=
      (BoundedGaps.Maynard.tendsto_log_engelsmaMaynardRadius_div_realRadius
        halpha).pow (Fintype.card largePowerTuple)
    simpa [factor] using hp.mul hr
  have hall : ∀ᶠ N : ℕ in atTop,
      ∀ m : largePowerTuple, beta < factor m N ∧ c < kernel m N := by
    have hall' := (Finset.univ : Finset largePowerTuple).eventually_all.mpr
      (fun m hm =>
        ((hfactor m).eventually (eventually_gt_nhds hbetaAlpha)).and
          (eventually_tupleRestrictedGKernel_normalized_gt
            m halpha hcCoeff))
    simpa [kernel] using hall'
  have hRnat :=
    BoundedGaps.Maynard.tendsto_log_engelsmaMaynardRadius_atTop halpha
  have hRreal : Tendsto (fun N : ℕ =>
      Real.log (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N))
      atTop atTop := by
    apply Real.tendsto_log_atTop.comp
    unfold BoundedGaps.Maynard.engelsmaMaynardRealRadius
      BoundedGaps.Maynard.maynardRealCutoff
    apply (tendsto_rpow_atTop halpha).comp
    exact tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1)
  filter_upwards [hall, hRnat.eventually (eventually_gt_atTop 0),
    hRreal.eventually (eventually_gt_atTop 0),
    eventually_ge_atTop 1] with N hallN hLn hLr hN
  have hmain := tupleMaynardS2Main_eq_shift_sum largePowerTuple alpha
    v largeTupleCandidate N
  rw [hmain, Finset.sum_div]
  have hattach : largePowerTuple.attach.Nonempty := by
    let m : largePowerTuple :=
      ⟨largePowerTuple_nonempty.choose, largePowerTuple_nonempty.choose_spec⟩
    exact ⟨m, Finset.mem_attach largePowerTuple m⟩
  calc
    (largeK : ℝ) * beta * c =
        ∑ _m ∈ largePowerTuple.attach, beta * c := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_attach,
        largePowerTuple_card]
      ring
    _ < ∑ m ∈ largePowerTuple.attach, factor m N * kernel m N := by
      apply Finset.sum_lt_sum_of_nonempty hattach
      intro m hm
      have hf := (hallN m).1
      have hk := (hallN m).2
      exact mul_lt_mul hf hk.le hc (hbeta.trans hf).le
    _ = ∑ m ∈ largePowerTuple.attach,
        (tupleShiftedPrimeIntervalCount N m *
          tupleRestrictedMainCoefficient largePowerTuple alpha
            largeTupleCandidate N m) /
          tupleMaynardScale largePowerTuple alpha N := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [tupleRestrictedMainCoefficient_eq_invTotient_mul_GKernel]
      rw [← tupleLargeCandidate_largePowerTuple_eq]
      have heq := restricted_main_term_normalized_eq m
        (by omega) hLn hLr
      dsimp only [factor, kernel]
      rw [← tupleOffFace_largePowerTuple]
      exact heq.symm

end

end MaynardBFT.Sieve
