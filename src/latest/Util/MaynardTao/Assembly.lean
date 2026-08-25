/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Util.MaynardTao.Natural
import ErdosProblems.Erdos6.GenericPrimeCount
import ErdosProblems.Erdos6.GenericS2ErrorLimit
import ErdosProblems.Erdos6.GenericDiagonal

/-!
# Tuple-generic Maynard assembly

The files under Erdos6 establish finite-tuple identities and error estimates,
but their final consumers specialize to one fixed power tuple.  This file
keeps the same proved ingredients generic in the finite shift set.
-/

namespace MaynardTao

open Filter Set
open scoped BigOperators

noncomputable section

def tupleYDiagonal (H : Finset ℕ) (alpha : ℝ)
    (F : (H → ℝ) → ℝ) (N : ℕ) : ℝ :=
  BoundedGaps.Maynard.maynardYDiagonalSum H
    (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
    (BoundedGaps.Maynard.engelsmaMaynardModulus N)
    (BoundedGaps.Maynard.maynardYValue H
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N) F)

theorem tupleYDiagonal_eq_tupleMaynardDiagonal
    (H : Finset ℕ) (alpha : ℝ) (F : (H → ℝ) → ℝ) (N : ℕ) :
    tupleYDiagonal H alpha F N =
      Erdos6.Maynard.tupleMaynardDiagonal H alpha F N := by
  unfold tupleYDiagonal
  rw [BoundedGaps.Maynard.maynardYDiagonalSum_maynardYValue_eq_explicit]
  unfold Erdos6.Maynard.tupleMaynardDiagonal
    Erdos6.Maynard.tupleNormalizedLogPoint
  apply Finset.sum_congr rfl
  intro u hu
  rw [Erdos6.Maynard.reciprocalTotientTupleWeight_eq_one_div_product]
  ring

theorem eventually_normalizedTupleYDiagonal_eq_natural_mul_logRatio
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    (F : (H → ℝ) → ℝ) :
    ∀ᶠ N : ℕ in atTop,
      (((N : ℝ) / BoundedGaps.Maynard.engelsmaMaynardModulus N) *
          tupleYDiagonal H alpha F N) /
          Erdos6.Maynard.tupleMaynardScale H alpha N =
        Erdos6.Maynard.normalizedTupleMaynardDiagonal H alpha F N *
          (Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) /
            Real.log (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)) ^
              Fintype.card H := by
  have hR := BoundedGaps.Maynard.eventually_one_lt_engelsmaMaynardRadius halpha
  filter_upwards [hR, eventually_ge_atTop 3] with N hRN hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hW : (0 : ℝ) < BoundedGaps.Maynard.engelsmaMaynardModulus N := by
    exact_mod_cast primorial_pos
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
  have hphi : (0 : ℝ) < Nat.totient
      (BoundedGaps.Maynard.engelsmaMaynardModulus N) := by
    exact_mod_cast Nat.totient_pos.mpr
      (primorial_pos
        (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))
  have hLnat : 0 < Real.log
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) :=
    Real.log_pos (by exact_mod_cast hRN)
  have hRreal : 1 < BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N := by
    unfold BoundedGaps.Maynard.engelsmaMaynardRealRadius
      BoundedGaps.Maynard.maynardRealCutoff
    apply Real.one_lt_rpow
    · exact_mod_cast (show 1 < N - 1 by omega)
    · exact halpha
  have hLreal : 0 < Real.log
      (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N) :=
    Real.log_pos hRreal
  rw [tupleYDiagonal_eq_tupleMaynardDiagonal]
  unfold Erdos6.Maynard.normalizedTupleMaynardDiagonal
    Erdos6.Maynard.tupleNaturalScale Erdos6.Maynard.tupleMaynardScale
  simpa only [BoundedGaps.Maynard.engelsmaMaynardModulus] using
    (Erdos6.Maynard.normalized_maynardScale_eq_natural_mul_logRatio
      (H := H)
      (D := BoundedGaps.Maynard.tripleLogCutoff (N - 1))
      (N := N)
      (Rnat := BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (Rreal := BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)
      (Y := Erdos6.Maynard.tupleMaynardDiagonal H alpha F N)
      hNpos hW hphi hLnat hLreal)

theorem tendsto_normalizedTupleYDiagonal
    {H : Finset ℕ} {alpha I : ℝ} (halpha : 0 < alpha)
    (F : (H → ℝ) → ℝ)
    (hdiag : Tendsto (fun N : ℕ =>
      Erdos6.Maynard.normalizedTupleMaynardDiagonal H alpha F N)
      atTop (nhds I)) :
    Tendsto (fun N : ℕ =>
      (((N : ℝ) / BoundedGaps.Maynard.engelsmaMaynardModulus N) *
        tupleYDiagonal H alpha F N) /
        Erdos6.Maynard.tupleMaynardScale H alpha N)
      atTop (nhds I) := by
  have hratio :=
    (BoundedGaps.Maynard.tendsto_log_engelsmaMaynardRadius_div_realRadius
      halpha).pow (Fintype.card H)
  have hmul := hdiag.mul hratio
  simpa using hmul.congr' (by
    filter_upwards [
      eventually_normalizedTupleYDiagonal_eq_natural_mul_logRatio
        (H := H) halpha F] with N hN
    exact hN.symm)

theorem tendsto_normalizedTupleS1Main
    {H : Finset ℕ} {alpha I : ℝ} (halpha : 0 < alpha)
    (F : (H → ℝ) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ t, |F t| ≤ B)
    (hdiag : Tendsto (fun N : ℕ =>
      Erdos6.Maynard.normalizedTupleMaynardDiagonal H alpha F N)
      atTop (nhds I)) :
    Tendsto (fun N : ℕ =>
      Erdos6.Maynard.tupleMaynardS1Main H alpha F N /
        Erdos6.Maynard.tupleMaynardScale H alpha N) atTop (nhds I) := by
  have hy := tendsto_normalizedTupleYDiagonal halpha F hdiag
  have hcross := Erdos6.Maynard.tendsto_normalized_tupleMaynardS1Cross_zero
    H halpha F hB hF
  have hsub := hy.sub hcross
  simpa using hsub.congr' (by
    filter_upwards [] with N
    rw [Erdos6.Maynard.tupleMaynardS1Main_eq_diagonal_sub_cross]
    unfold tupleYDiagonal Erdos6.Maynard.maynardModulus
      Erdos6.Maynard.maynardRadius
    ring)

theorem tendsto_normalizedTupleS1
    {H : Finset ℕ} {alpha I : ℝ} (halpha : 0 < alpha)
    (halphaQuarter : alpha < 1 / 4) (v : ℕ → ℕ)
    (F : (H → ℝ) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ t, |F t| ≤ B)
    (hdiag : Tendsto (fun N : ℕ =>
      Erdos6.Maynard.normalizedTupleMaynardDiagonal H alpha F N)
      atTop (nhds I)) :
    Tendsto (fun N : ℕ =>
      BoundedGaps.Maynard.sieveWeightSum N
          (Erdos6.Maynard.tupleMaynardWeight H alpha v F N) /
        Erdos6.Maynard.tupleMaynardScale H alpha N)
      atTop (nhds I) := by
  have hmain := tendsto_normalizedTupleS1Main halpha F hB hF hdiag
  have herror := Erdos6.Maynard.tendsto_normalized_tupleMaynardS1Error_zero
    H halpha halphaQuarter v F hB hF
  have hsum := hmain.add herror
  simpa using hsum.congr' (by
    filter_upwards [Erdos6.Maynard.eventually_tupleMaynardS1_eq_main_add_error
      H alpha v F] with N hN
    rw [hN]
    ring)

/-- Algebraic normalization of one coordinate of the S₂ main term.

This is the tuple- and candidate-generic form of the calculation used by the
fixed large-power-tuple development. -/
theorem restrictedMainTerm_normalized_eq
    {H : Finset ℕ} {alpha : ℝ} {F : (H → ℝ) → ℝ}
    {N : ℕ} (m : H)
    (hN : 0 < N)
    (hRnat : 0 < Real.log (Erdos6.Maynard.maynardRadius alpha N))
    (hRreal : 0 < Real.log
      (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)) :
    (Erdos6.Maynard.tupleShiftedPrimeIntervalCount N m *
        ((Nat.totient (Erdos6.Maynard.maynardModulus N) : ℝ)⁻¹ *
          Erdos6.Maynard.tupleRestrictedGKernel H alpha F N m)) /
        Erdos6.Maynard.tupleMaynardScale H alpha N =
      ((Erdos6.Maynard.tupleShiftedPrimeIntervalCount N m / (N : ℝ)) *
          Real.log (Erdos6.Maynard.maynardRadius alpha N)) *
        (Real.log (Erdos6.Maynard.maynardRadius alpha N) /
          Real.log (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)) ^
            Fintype.card H *
        (Erdos6.Maynard.tupleRestrictedGKernel H alpha F N m /
          (BoundedGaps.Maynard.preSieveSingularSeries
              (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
            Real.log (Erdos6.Maynard.maynardRadius alpha N) ^ 2 *
            Erdos6.Maynard.tupleNaturalScale
              (Erdos6.Maynard.tupleOffFace H m) alpha N)) := by
  let D := BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  let W := Erdos6.Maynard.maynardModulus N
  let S := BoundedGaps.Maynard.preSieveSingularSeries D
  let Ln := Real.log (Erdos6.Maynard.maynardRadius alpha N)
  let Lr := Real.log
    (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)
  let K := Fintype.card H
  have hWnat : 0 < W := by
    dsimp [W, Erdos6.Maynard.maynardModulus]
    exact primorial_pos _
  have hW : (0 : ℝ) < W := by exact_mod_cast hWnat
  have hphiNat : 0 < Nat.totient W := Nat.totient_pos.mpr hWnat
  have hphi : (0 : ℝ) < Nat.totient W := by exact_mod_cast hphiNat
  have hS : 0 < S := by
    dsimp [S]
    exact BoundedGaps.Maynard.preSieveSingularSeries_pos _
  have hK : 0 < K := by
    exact Fintype.card_pos_iff.mpr ⟨m⟩
  have hcard : Fintype.card (Erdos6.Maynard.tupleOffFace H m) = K - 1 := by
    calc
      Fintype.card (Erdos6.Maynard.tupleOffFace H m) =
          (Erdos6.Maynard.tupleOffFace H m).card :=
        Fintype.card_coe _
      _ = H.card - 1 := by
        unfold Erdos6.Maynard.tupleOffFace
        rw [Finset.card_erase_of_mem m.2]
      _ = K - 1 := by simp [K]
  have hnatScale :
      S ^ 2 * Ln ^ 2 *
          Erdos6.Maynard.tupleNaturalScale
            (Erdos6.Maynard.tupleOffFace H m) alpha N =
        (S * Ln) ^ (K + 1) := by
    have hExp : K + 1 = 2 + (K - 1) := by omega
    unfold Erdos6.Maynard.tupleNaturalScale
    rw [hcard, hExp, pow_add]
    ring
  change
    (Erdos6.Maynard.tupleShiftedPrimeIntervalCount N m *
        ((Nat.totient W : ℝ)⁻¹ *
          Erdos6.Maynard.tupleRestrictedGKernel H alpha F N m)) /
        Erdos6.Maynard.tupleMaynardScale H alpha N = _
  rw [show
      BoundedGaps.Maynard.preSieveSingularSeries
            (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
          Real.log (Erdos6.Maynard.maynardRadius alpha N) ^ 2 *
          Erdos6.Maynard.tupleNaturalScale
            (Erdos6.Maynard.tupleOffFace H m) alpha N =
        (S * Ln) ^ (K + 1) by simpa [S, Ln, D] using hnatScale]
  unfold Erdos6.Maynard.tupleMaynardScale
    BoundedGaps.Maynard.maynardSieveScale
  change
    (Erdos6.Maynard.tupleShiftedPrimeIntervalCount N m *
        ((Nat.totient W : ℝ)⁻¹ *
          Erdos6.Maynard.tupleRestrictedGKernel H alpha F N m)) /
        (((Nat.totient W : ℝ) ^ K * (N : ℝ) * Lr ^ K) /
          (W : ℝ) ^ (K + 1)) = _
  have hSeq : S = (Nat.totient W : ℝ) / (W : ℝ) := by
    simpa [S, W, D, Erdos6.Maynard.maynardModulus,
      BoundedGaps.Maynard.engelsmaMaynardModulus] using
      BoundedGaps.Maynard.preSieveSingularSeries_eq_totient_div D
  rw [hSeq]
  dsimp [Ln, Lr, K]
  simp only [div_pow]
  ring_nf
  field_simp [hW.ne', hphi.ne', (Nat.cast_pos.mpr hN).ne',
    hRnat.ne', hRreal.ne', inv_inv]
  let T := Erdos6.Maynard.tupleShiftedPrimeIntervalCount N m *
    Erdos6.Maynard.tupleRestrictedGKernel H alpha F N m
  change T = T * Real.log (Erdos6.Maynard.maynardRadius alpha N) ^
      Fintype.card H *
    (1 / Real.log (Erdos6.Maynard.maynardRadius alpha N)) ^
      Fintype.card H
  have hcancel :
      Real.log (Erdos6.Maynard.maynardRadius alpha N) ^ Fintype.card H *
          (1 / Real.log (Erdos6.Maynard.maynardRadius alpha N)) ^
            Fintype.card H = 1 := by
    rw [← mul_pow]
    field_simp [hRnat.ne']
    exact one_pow _
  rw [mul_assoc, hcancel, mul_one]

/-- A uniform lower bound for every normalized restricted kernel gives the
expected lower bound for the full normalized S₂ main term. -/
theorem eventually_tupleS2Main_normalized_gt_of_kernel
    {H : Finset ℕ} {alpha beta c : ℝ}
    (hH : H.Nonempty) (halpha : 0 < alpha)
    (hbeta : 0 < beta) (hbetaAlpha : beta < alpha)
    (hc : 0 < c) (v : ℕ → ℕ) (F : (H → ℝ) → ℝ)
    (hkernel : ∀ m : H, ∀ᶠ N : ℕ in atTop,
      c <
        Erdos6.Maynard.tupleRestrictedGKernel H alpha F N m /
          (BoundedGaps.Maynard.preSieveSingularSeries
              (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
            Real.log (Erdos6.Maynard.maynardRadius alpha N) ^ 2 *
            Erdos6.Maynard.tupleNaturalScale
              (Erdos6.Maynard.tupleOffFace H m) alpha N)) :
    ∀ᶠ N : ℕ in atTop,
      (H.card : ℝ) * beta * c <
        Erdos6.Maynard.tupleMaynardS2Main H alpha v F N /
          Erdos6.Maynard.tupleMaynardScale H alpha N := by
  let factor := fun (m : H) (N : ℕ) =>
    ((Erdos6.Maynard.tupleShiftedPrimeIntervalCount N m / (N : ℝ)) *
        Real.log (Erdos6.Maynard.maynardRadius alpha N)) *
      (Real.log (Erdos6.Maynard.maynardRadius alpha N) /
        Real.log (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)) ^
          Fintype.card H
  let kernel := fun (m : H) (N : ℕ) =>
    Erdos6.Maynard.tupleRestrictedGKernel H alpha F N m /
      (BoundedGaps.Maynard.preSieveSingularSeries
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
        Real.log (Erdos6.Maynard.maynardRadius alpha N) ^ 2 *
        Erdos6.Maynard.tupleNaturalScale
          (Erdos6.Maynard.tupleOffFace H m) alpha N)
  have hfactor (m : H) :
      Tendsto (factor m) atTop (nhds alpha) := by
    have hp := Erdos6.Maynard.tendsto_tupleShiftedPrimeIntervalFactor halpha m
    have hr :=
      (BoundedGaps.Maynard.tendsto_log_engelsmaMaynardRadius_div_realRadius
        halpha).pow (Fintype.card H)
    simpa [factor] using hp.mul hr
  have hall : ∀ᶠ N : ℕ in atTop,
      ∀ m : H, beta < factor m N ∧ c < kernel m N := by
    have hall' := (Finset.univ : Finset H).eventually_all.mpr
      (fun m _ =>
        ((hfactor m).eventually (eventually_gt_nhds hbetaAlpha)).and
          (hkernel m))
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
  have hmain := Erdos6.Maynard.tupleMaynardS2Main_eq_shift_sum H alpha v F N
  rw [hmain, Finset.sum_div]
  have hattach : H.attach.Nonempty := by
    obtain ⟨m, hm⟩ := hH
    exact ⟨⟨m, hm⟩, Finset.mem_attach H ⟨m, hm⟩⟩
  calc
    (H.card : ℝ) * beta * c =
        ∑ _m ∈ H.attach, beta * c := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_attach]
      ring
    _ < ∑ m ∈ H.attach, factor m N * kernel m N := by
      apply Finset.sum_lt_sum_of_nonempty hattach
      intro m hm
      have hf := (hallN m).1
      have hk := (hallN m).2
      exact mul_lt_mul hf hk.le hc (hbeta.trans hf).le
    _ = ∑ m ∈ H.attach,
        (Erdos6.Maynard.tupleShiftedPrimeIntervalCount N m *
          Erdos6.Maynard.tupleRestrictedMainCoefficient H alpha F N m) /
          Erdos6.Maynard.tupleMaynardScale H alpha N := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Erdos6.Maynard.tupleRestrictedMainCoefficient_eq_invTotient_mul_GKernel]
      exact (restrictedMainTerm_normalized_eq m
        (by omega) hLn hLr).symm

/-- Generic final assembly of Maynard's weighted-sieve inequality.

The fixed-configuration development packages this argument together with its
particular candidate.  Keeping it separate here makes the only
candidate-specific inputs explicit: the `S₁` diagonal limit and a uniform
positive lower bound for every restricted `S₂` kernel. -/
theorem hasEventuallyPositiveSieveExcess_of_diagonal_and_kernel
    {H : Finset ℕ} (hH : H.Nonempty) {rho theta delta beta I c B : ℝ}
    (htheta : 0 < theta) (hthetaHalf : theta < 1 / 2)
    (hlevel : BoundedGaps.Maynard.hasPrimeLevel theta)
    (hdelta : 0 < delta) (hdeltaTheta : delta < theta / 2)
    (hbeta : 0 < beta) (hbetaAlpha : beta < theta / 2 - delta)
    (hc : 0 < c) (hrho : 0 ≤ rho)
    (hmargin : rho * I < (H.card : ℝ) * beta * c)
    (v : ℕ → ℕ)
    (hv : ∀ N : ℕ, ∀ h ∈ H,
      Nat.Coprime (v N + h) (Erdos6.Maynard.maynardModulus N))
    (F : (H → ℝ) → ℝ) (hB : 0 ≤ B) (hF : ∀ t, |F t| ≤ B)
    (hdiag : Tendsto (fun N : ℕ =>
      Erdos6.Maynard.normalizedTupleMaynardDiagonal H
        (theta / 2 - delta) F N) atTop (nhds I))
    (hkernel : ∀ m : H, ∀ᶠ N : ℕ in atTop,
      c <
        Erdos6.Maynard.tupleRestrictedGKernel H (theta / 2 - delta) F N m /
          (BoundedGaps.Maynard.preSieveSingularSeries
              (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
            Real.log (Erdos6.Maynard.maynardRadius
              (theta / 2 - delta) N) ^ 2 *
            Erdos6.Maynard.tupleNaturalScale
              (Erdos6.Maynard.tupleOffFace H m) (theta / 2 - delta) N)) :
    BoundedGaps.Maynard.HasEventuallyPositiveSieveExcess H rho := by
  let alpha := theta / 2 - delta
  let S := (H.card : ℝ) * beta * c
  let eps := (S - rho * I) / (2 * (rho + 1))
  have halpha : 0 < alpha := by dsimp [alpha]; linarith
  have halphaQuarter : alpha < 1 / 4 := by
    dsimp [alpha]
    linarith
  have hSI : rho * I < S := by simpa only [S] using hmargin
  have hrhoOne : 0 < rho + 1 := by linarith
  have heps : 0 < eps := by
    dsimp [eps]
    exact div_pos (sub_pos.mpr hSI) (mul_pos (by norm_num) hrhoOne)
  have hmain := eventually_tupleS2Main_normalized_gt_of_kernel
    hH halpha hbeta hbetaAlpha hc v F (by
      simpa only [alpha] using hkernel)
  have hs1 := tendsto_normalizedTupleS1 halpha halphaQuarter v F hB hF
    (by simpa only [alpha] using hdiag)
  have hs1Upper : ∀ᶠ N : ℕ in atTop,
      BoundedGaps.Maynard.sieveWeightSum N
          (Erdos6.Maynard.tupleMaynardWeight H alpha v F N) /
          Erdos6.Maynard.tupleMaynardScale H alpha N < I + eps := by
    have hmem : Set.Iio (I + eps) ∈ nhds I :=
      Iio_mem_nhds (lt_add_of_pos_right I heps)
    exact hs1.eventually hmem
  have herr := Erdos6.Maynard.tendsto_normalized_tupleMaynardS2Error_zero_of_primeLevel
    H hH v F B hB hF hv htheta hthetaHalf hdelta hdeltaTheta hlevel
  have herrLower : ∀ᶠ N : ℕ in atTop,
      -eps <
        Erdos6.Maynard.tupleMaynardS2Error H alpha v F N /
          Erdos6.Maynard.tupleMaynardScale H alpha N := by
    have hmem : Set.Ioi (-eps) ∈ nhds (0 : ℝ) :=
      Ioi_mem_nhds (neg_lt_zero.mpr heps)
    simpa only [alpha] using herr.eventually hmem
  have hS2eq := Erdos6.Maynard.eventually_tupleMaynardS2_eq_main_add_error
    H hthetaHalf hdelta hdeltaTheta v F
  have hscale := Erdos6.Maynard.eventually_tupleMaynardScale_pos
    (H := H) halpha
  have hpos : ∀ᶠ N : ℕ in atTop,
      0 < BoundedGaps.Maynard.sieveExcess H N rho
        (Erdos6.Maynard.tupleMaynardWeight H alpha v F N) := by
    filter_upwards [hmain, hs1Upper, herrLower, hS2eq, hscale] with
        N hmainN hs1N herrN hS2eqN hscaleN
    have hS2norm : S - eps <
        BoundedGaps.Maynard.primeWeightedSieveSum H N
            (Erdos6.Maynard.tupleMaynardWeight H alpha v F N) /
          Erdos6.Maynard.tupleMaynardScale H alpha N := by
      have heq :
          BoundedGaps.Maynard.primeWeightedSieveSum H N
              (Erdos6.Maynard.tupleMaynardWeight H alpha v F N) =
            Erdos6.Maynard.tupleMaynardS2Main H alpha v F N +
              Erdos6.Maynard.tupleMaynardS2Error H alpha v F N := by
        simpa only [alpha, Erdos6.Maynard.tupleMaynardWeight] using hS2eqN
      rw [heq, add_div]
      change S <
        Erdos6.Maynard.tupleMaynardS2Main H alpha v F N /
          Erdos6.Maynard.tupleMaynardScale H alpha N at hmainN
      linarith
    have hnorm : 0 <
        BoundedGaps.Maynard.sieveExcess H N rho
            (Erdos6.Maynard.tupleMaynardWeight H alpha v F N) /
          Erdos6.Maynard.tupleMaynardScale H alpha N := by
      unfold BoundedGaps.Maynard.sieveExcess
      rw [show
        (BoundedGaps.Maynard.primeWeightedSieveSum H N
            (Erdos6.Maynard.tupleMaynardWeight H alpha v F N) -
          rho * BoundedGaps.Maynard.sieveWeightSum N
            (Erdos6.Maynard.tupleMaynardWeight H alpha v F N)) /
            Erdos6.Maynard.tupleMaynardScale H alpha N =
          BoundedGaps.Maynard.primeWeightedSieveSum H N
              (Erdos6.Maynard.tupleMaynardWeight H alpha v F N) /
                Erdos6.Maynard.tupleMaynardScale H alpha N -
            rho * (BoundedGaps.Maynard.sieveWeightSum N
              (Erdos6.Maynard.tupleMaynardWeight H alpha v F N) /
                Erdos6.Maynard.tupleMaynardScale H alpha N) by ring]
      have hs1mul : rho *
          (BoundedGaps.Maynard.sieveWeightSum N
              (Erdos6.Maynard.tupleMaynardWeight H alpha v F N) /
            Erdos6.Maynard.tupleMaynardScale H alpha N) ≤
          rho * (I + eps) :=
        mul_le_mul_of_nonneg_left hs1N.le hrho
      have hgap : 0 < S - rho * I := sub_pos.mpr hSI
      have hdiff : 0 < S - eps - rho * (I + eps) := by
        have heq : S - eps - rho * (I + eps) =
            (S - rho * I) / 2 := by
          dsimp only [eps]
          field_simp [hrhoOne.ne']
          ring
        rw [heq]
        linarith
      linarith
    have heq :
        BoundedGaps.Maynard.sieveExcess H N rho
            (Erdos6.Maynard.tupleMaynardWeight H alpha v F N) =
          (BoundedGaps.Maynard.sieveExcess H N rho
              (Erdos6.Maynard.tupleMaynardWeight H alpha v F N) /
            Erdos6.Maynard.tupleMaynardScale H alpha N) *
              Erdos6.Maynard.tupleMaynardScale H alpha N := by
      field_simp [hscaleN.ne']
    rw [heq]
    exact mul_pos hnorm hscaleN
  rw [BoundedGaps.Maynard.HasEventuallyPositiveSieveExcess]
  rw [Filter.eventually_atTop] at hpos
  obtain ⟨N₀, hN₀⟩ := hpos
  refine ⟨N₀, fun N hN => ⟨
    Erdos6.Maynard.tupleMaynardWeight H alpha v F N, ?_, hN₀ N hN⟩⟩
  intro n hn
  unfold Erdos6.Maynard.tupleMaynardWeight
  exact BoundedGaps.Maynard.preSievedSquareDivisorWeight_nonneg _ _ _ _ _ _

end

end MaynardTao
