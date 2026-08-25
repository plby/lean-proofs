/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Util.MaynardTao.Assembly
import ErdosProblems.Erdos6.LargeRestrictedYLimit
import ErdosProblems.Erdos6.GenericRestrictedCrossLimit

/-!
# Candidate-generic restricted-kernel bridge

The fixed large-tuple files already prove that the purely arithmetic
perturbations are negligible.  Those estimates only use a uniform bound on
the sampled test function, so we expose the genuinely generic form needed by
arbitrary-dimensional Maynard candidates.
-/

namespace MaynardTao

open Filter
open scoped BigOperators

noncomputable section

/-- The coordinate-fiber square diagonal for an arbitrary tuple test
function. -/
def tupleCoordinateFiberSquareDiagonalFor
    (H : Finset ℕ) (alpha : ℝ) (F : (H → ℝ) → ℝ)
    (N : ℕ) (m : H) : ℝ :=
  ∑ r ∈ (BoundedGaps.Maynard.maynardDivisorTupleSupport H
      (Erdos6.Maynard.maynardRadius alpha N)
      (Erdos6.Maynard.maynardModulus N)).filter (fun r => r m = 1),
    BoundedGaps.Maynard.maynardS2CoordinateFiberSum H
        (Erdos6.Maynard.maynardRadius alpha N)
        (Erdos6.Maynard.maynardModulus N)
        (BoundedGaps.Maynard.maynardYValue H
          (Erdos6.Maynard.maynardRadius alpha N)
          (Erdos6.Maynard.maynardModulus N) F) m r ^ 2 /
      ∏ h : H, (BoundedGaps.Maynard.maynardS2G (r h) : ℝ)

/-- The summed restricted-Y perturbation with an arbitrary pointwise bound
`B` on the underlying test function. -/
def tupleCoordinateOneSquarePerturbationFor
    (H : Finset ℕ) (alpha : ℝ) (N : ℕ) (m : H) (B : ℝ) : ℝ :=
  ∑ r ∈ (BoundedGaps.Maynard.maynardDivisorTupleSupport H
      (Erdos6.Maynard.maynardRadius alpha N)
      (Erdos6.Maynard.maynardModulus N)).filter (fun r => r m = 1),
    Erdos6.Maynard.tupleCoordinateOneSquarePerturbationEnvelope H
        (Erdos6.Maynard.maynardRadius alpha N)
        (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) m B /
      |∏ h : H, (BoundedGaps.Maynard.maynardS2G (r h) : ℝ)|

theorem abs_tupleCoordinateOneYDiagonal_sub_fiberSquareDiagonalFor_le
    {H : Finset ℕ} {alpha : ℝ} (F : (H → ℝ) → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hF : ∀ t, |F t| ≤ B) (N : ℕ) (m : H)
    (hD : 0 < BoundedGaps.Maynard.tripleLogCutoff (N - 1))
    (hWL : (Erdos6.Maynard.maynardModulus N : ℝ) ≤
      1 + Real.log (Erdos6.Maynard.maynardRadius alpha N)) :
    |Erdos6.Maynard.tupleCoordinateOneYDiagonal H alpha F N m -
        tupleCoordinateFiberSquareDiagonalFor H alpha F N m| ≤
      tupleCoordinateOneSquarePerturbationFor H alpha N m B := by
  let R := Erdos6.Maynard.maynardRadius alpha N
  let D := BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  let W := primorial D
  let y := BoundedGaps.Maynard.maynardYValue H R W F
  have hy : BoundedGaps.Maynard.IsSupportedMaynardY H R W y :=
    BoundedGaps.Maynard.isSupportedMaynardY_maynardYValue _ _ _ _
  have hyBound : ∀ r, |y r| ≤ B := by
    intro r
    exact BoundedGaps.Maynard.abs_maynardYValue_le H R W F hB hF r
  have hD' : 0 < D := by simpa [D] using hD
  have hWL' : (W : ℝ) ≤ 1 + Real.log R := by
    simpa [W, R, D, Erdos6.Maynard.maynardModulus,
      BoundedGaps.Maynard.engelsmaMaynardModulus] using hWL
  have hsum := Erdos6.Maynard.abs_tupleRestrictedYSum_sub_fiberSum_le
    hy m hD' hWL' hB hyBound
  rw [Erdos6.Maynard.tupleCoordinateOneYDiagonal_eq_explicit]
  unfold tupleCoordinateFiberSquareDiagonalFor
    tupleCoordinateOneSquarePerturbationFor
  simpa only [R, D, W, y, Erdos6.Maynard.maynardRadius,
    Erdos6.Maynard.maynardModulus,
    BoundedGaps.Maynard.engelsmaMaynardModulus] using hsum

theorem tupleCoordinateOneSquarePerturbationEnvelope_scale
    (H : Finset ℕ) (R D : ℕ) (m : H) (B : ℝ) :
    Erdos6.Maynard.tupleCoordinateOneSquarePerturbationEnvelope H R D m B =
      B ^ 2 *
        Erdos6.Maynard.tupleCoordinateOneSquarePerturbationEnvelope H R D m 1 := by
  unfold Erdos6.Maynard.tupleCoordinateOneSquarePerturbationEnvelope
  ring

theorem tupleCoordinateOneSquarePerturbationFor_eq_scale
    (H : Finset ℕ) (alpha : ℝ) (N : ℕ) (m : H) (B : ℝ) :
    tupleCoordinateOneSquarePerturbationFor H alpha N m B =
      B ^ 2 * Erdos6.Maynard.tupleCoordinateOneSquarePerturbation H alpha N m := by
  unfold tupleCoordinateOneSquarePerturbationFor
    Erdos6.Maynard.tupleCoordinateOneSquarePerturbation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [tupleCoordinateOneSquarePerturbationEnvelope_scale]
  ring

theorem tendsto_normalizedTupleCoordinateOneSquarePerturbationFor_zero
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha) (m : H) (B : ℝ) :
    Tendsto (fun N : ℕ =>
      tupleCoordinateOneSquarePerturbationFor H alpha N m B /
        (BoundedGaps.Maynard.preSieveSingularSeries
            (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
          Real.log (Erdos6.Maynard.maynardRadius alpha N) ^ 2 *
          Erdos6.Maynard.tupleNaturalScale
            (Erdos6.Maynard.tupleOffFace H m) alpha N))
      atTop (nhds 0) := by
  have h := Erdos6.Maynard.tendsto_normalizedTupleCoordinateOneSquarePerturbation_zero
    (H := H) halpha m
  have hs := h.const_mul (B ^ 2)
  simpa [tupleCoordinateOneSquarePerturbationFor_eq_scale,
    mul_div_assoc] using hs

/-- The restricted-transform envelope with an arbitrary bound on the test
function. -/
def tupleRestrictedTransformEnvelopeFor
    (H : Finset ℕ) (alpha : ℝ) (N : ℕ) (m : H) (B : ℝ) : ℝ :=
  B * Erdos6.Maynard.tupleRestrictedTransformEnvelope H alpha N m

theorem abs_tupleRestrictedY_le_transformEnvelopeFor
    {H : Finset ℕ} {alpha : ℝ} {N : ℕ} (m : H) {r : H → ℕ}
    (F : (H → ℝ) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ t, |F t| ≤ B)
    (hD : 0 < BoundedGaps.Maynard.tripleLogCutoff (N - 1))
    (hWL : (Erdos6.Maynard.maynardModulus N : ℝ) ≤
      1 + Real.log (Erdos6.Maynard.maynardRadius alpha N))
    (hr : BoundedGaps.Maynard.IsMaynardDivisorTuple H
      (Erdos6.Maynard.maynardRadius alpha N)
      (Erdos6.Maynard.maynardModulus N) r)
    (hrm : r m = 1) :
    |BoundedGaps.Maynard.maynardS2RestrictedYFromCoefficients H
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H
          (Erdos6.Maynard.maynardRadius alpha N)
          (Erdos6.Maynard.maynardModulus N))
        (BoundedGaps.Maynard.maynardCoefficientFromY H
          (Erdos6.Maynard.maynardRadius alpha N)
          (Erdos6.Maynard.maynardModulus N)
          (BoundedGaps.Maynard.maynardYValue H
            (Erdos6.Maynard.maynardRadius alpha N)
            (Erdos6.Maynard.maynardModulus N) F)) m r| ≤
      tupleRestrictedTransformEnvelopeFor H alpha N m B := by
  have h := BoundedGaps.Maynard.abs_maynardS2RestrictedY_le_log
    (BoundedGaps.Maynard.isSupportedMaynardY_maynardYValue H
      (Erdos6.Maynard.maynardRadius alpha N)
      (Erdos6.Maynard.maynardModulus N) F)
    m hD hWL hr hrm hB
    (fun u => BoundedGaps.Maynard.abs_maynardYValue_le H
      (Erdos6.Maynard.maynardRadius alpha N)
      (Erdos6.Maynard.maynardModulus N) F hB hF u)
  convert h using 1 <;>
    simp [tupleRestrictedTransformEnvelopeFor,
      Erdos6.Maynard.tupleRestrictedTransformEnvelope,
      Erdos6.Maynard.maynardModulus,
      BoundedGaps.Maynard.engelsmaMaynardModulus] <;> ring

theorem abs_tupleRestrictedCross_le_explicitFor
    {H : Finset ℕ} {alpha : ℝ} {N : ℕ} (m : H)
    (F : (H → ℝ) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ t, |F t| ≤ B)
    (hR : 1 < Erdos6.Maynard.maynardRadius alpha N)
    (hD : 2 ≤ BoundedGaps.Maynard.tripleLogCutoff (N - 1))
    (hWL : (Erdos6.Maynard.maynardModulus N : ℝ) ≤
      1 + Real.log (Erdos6.Maynard.maynardRadius alpha N)) :
    |Erdos6.Maynard.tupleRestrictedCross H alpha F N m| ≤
      tupleRestrictedTransformEnvelopeFor H alpha N m B ^ 2 *
        ((32 * Real.exp 32 /
            (BoundedGaps.Maynard.tripleLogCutoff (N - 1) : ℝ)) *
          ((BoundedGaps.Maynard.offDiagonalPairs H).card : ℝ) *
          (Real.exp 32) ^
            ((BoundedGaps.Maynard.offDiagonalPairs H).card - 1)) *
        (BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeMean
          (Erdos6.Maynard.maynardModulus N)
          (Erdos6.Maynard.maynardRadius alpha N)) ^
            (Finset.univ.erase m).card := by
  let D := BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  let R := Erdos6.Maynard.maynardRadius alpha N
  let W := Erdos6.Maynard.maynardModulus N
  let y := BoundedGaps.Maynard.maynardYValue H R W F
  let E := tupleRestrictedTransformEnvelopeFor H alpha N m B
  let T := BoundedGaps.Maynard.roughS2CrossTupleReciprocalGSquareTail H D R
  let M := BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeMean W R
  have hcoeff : Erdos6.Maynard.tupleMaynardCoefficient H alpha F N =
      BoundedGaps.Maynard.maynardCoefficientFromY H R W y := by
    funext d
    exact BoundedGaps.Maynard.maynardCoefficient_eq_fromYValue _ _ _ _ d
  have hbase : |Erdos6.Maynard.tupleRestrictedCross H alpha F N m| ≤
      E ^ 2 * T *
        BoundedGaps.Maynard.restrictedS2CommonReciprocalGMass H W R m := by
    unfold Erdos6.Maynard.tupleRestrictedCross
    rw [hcoeff]
    apply BoundedGaps.Maynard.abs_incompatibleRestrictedS2_le_crossTail_mul_commonMass
      hR hD (by
        unfold E tupleRestrictedTransformEnvelopeFor
        exact mul_nonneg hB
          (Erdos6.Maynard.tupleRestrictedTransformEnvelope_nonneg
            (Nat.zero_lt_of_lt hD) hWL))
    intro r hr hrm
    exact abs_tupleRestrictedY_le_transformEnvelopeFor m F hB hF
      (Nat.zero_lt_of_lt hD) hWL hr hrm
  have htail0 : 0 ≤ T := by
    unfold T BoundedGaps.Maynard.roughS2CrossTupleReciprocalGSquareTail
    exact Finset.sum_nonneg fun s hs => by
      unfold BoundedGaps.Maynard.roughS2CrossTupleReciprocalGSquareWeight
      exact Finset.prod_nonneg fun x hx =>
        Finset.prod_nonneg fun p hp =>
          BoundedGaps.Maynard.maynardS2CrossPrimeSquareWeight_nonneg p
  have hM0 : 0 ≤ M := by
    unfold M BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeMean
    exact Finset.sum_nonneg fun n hn =>
      Erdos6.Maynard.tupleReciprocalGSquarefreeAF_nonneg _ n
  have hmass := BoundedGaps.Maynard.restrictedS2CommonReciprocalGMass_le
    (H := H) (W := W) (R := R) (m := m)
  have htail := BoundedGaps.Maynard.roughS2CrossTupleReciprocalGSquareTail_le
    (H := H) (Q := R) hD
  calc
    _ ≤ E ^ 2 * T *
        BoundedGaps.Maynard.restrictedS2CommonReciprocalGMass H W R m := hbase
    _ ≤ E ^ 2 * T * M ^ (Finset.univ.erase m).card :=
      mul_le_mul_of_nonneg_left hmass (mul_nonneg (sq_nonneg _) htail0)
    _ ≤ E ^ 2 *
        ((32 * Real.exp 32 / (D : ℝ)) *
          ((BoundedGaps.Maynard.offDiagonalPairs H).card : ℝ) *
          (Real.exp 32) ^
            ((BoundedGaps.Maynard.offDiagonalPairs H).card - 1)) *
          M ^ (Finset.univ.erase m).card :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left htail (sq_nonneg _))
        (pow_nonneg hM0 _)
    _ = _ := by rfl

theorem tendsto_normalizedTupleRestrictedCrossFor_zero
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    (F : (H → ℝ) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ t, |F t| ≤ B) (m : H) :
    Tendsto (fun N : ℕ =>
      Erdos6.Maynard.tupleRestrictedCross H alpha F N m /
        (BoundedGaps.Maynard.preSieveSingularSeries
            (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
          Real.log (Erdos6.Maynard.maynardRadius alpha N) ^ 2 *
          Erdos6.Maynard.tupleNaturalScale
            (Erdos6.Maynard.tupleOffFace H m) alpha N))
      atTop (nhds 0) := by
  let D : ℕ → ℕ := fun N =>
    BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  let R : ℕ → ℕ := fun N => Erdos6.Maynard.maynardRadius alpha N
  let L : ℕ → ℝ := fun N => Real.log (R N)
  let S : ℕ → ℝ := fun N =>
    BoundedGaps.Maynard.preSieveSingularSeries (D N)
  let Q : ℕ → ℝ := fun N => S N * L N
  let M : ℕ → ℝ := fun N =>
    BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeMean
      (Erdos6.Maynard.maynardModulus N) (R N)
  let k := (Finset.univ.erase m).card
  let A : ℕ → ℝ := fun N =>
    8 / (D N : ℝ) + (8 * Real.exp 8 / (D N : ℝ)) *
      (1 + 8 * Real.exp 8 / (D N : ℝ)) ^ (k - 1)
  let E : ℕ → ℝ := fun N =>
    tupleRestrictedTransformEnvelopeFor H alpha N m B
  let Tail : ℕ → ℝ := fun N =>
    (32 * Real.exp 32 / (D N : ℝ)) *
      ((BoundedGaps.Maynard.offDiagonalPairs H).card : ℝ) *
      (Real.exp 32) ^
        ((BoundedGaps.Maynard.offDiagonalPairs H).card - 1)
  let Ctail : ℝ := 32 * Real.exp 32 *
    ((BoundedGaps.Maynard.offDiagonalPairs H).card : ℝ) *
    (Real.exp 32) ^
      ((BoundedGaps.Maynard.offDiagonalPairs H).card - 1)
  let Cenv : ℝ := B * (16 * (1 + (k : ℝ)))
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
    simpa [L, R, Erdos6.Maynard.maynardRadius] using
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
    simpa [M, Q, S, L, D, R, Erdos6.Maynard.maynardModulus,
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
    have hEdiv : E N / Q N =
        B * (8 * ((1 + L N) / L N) * (1 + (k : ℝ) * A N)) := by
      dsimp [E, Q, L, S, A, D, R, k]
      unfold tupleRestrictedTransformEnvelopeFor
        Erdos6.Maynard.tupleRestrictedTransformEnvelope
      simp only [Erdos6.Maynard.maynardModulus,
        BoundedGaps.Maynard.engelsmaMaynardModulus,
        Finset.univ_eq_attach]
      rw [BoundedGaps.Maynard.preSieveSingularSeries_eq_totient_div]
      have hW : (primorial (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) : ℝ) ≠ 0 := by
        exact_mod_cast (primorial_pos
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1))).ne'
      have hphi : (Nat.totient
          (primorial (BoundedGaps.Maynard.tripleLogCutoff (N - 1))) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.mpr (primorial_pos
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))).ne'
      field_simp [hLN.ne', hW, hphi]
    have hfac0 : 0 ≤ 1 + (k : ℝ) * A N := by positivity
    have hfacLe : 1 + (k : ℝ) * A N ≤ 1 + (k : ℝ) := by
      simpa [add_comm] using add_le_add_left
        (mul_le_mul_of_nonneg_left hAN.2 (Nat.cast_nonneg k)) 1
    rw [hEdiv]
    constructor
    · positivity
    · calc
        B * (8 * ((1 + L N) / L N) * (1 + (k : ℝ) * A N)) ≤
            B * (8 * 2 * (1 + (k : ℝ) * A N)) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hLR.2 (by norm_num)) hfac0) hB
        _ ≤ B * (8 * 2 * (1 + (k : ℝ))) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hfacLe (by norm_num)) hB
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
  have hcorr' := abs_tupleRestrictedCross_le_explicitFor m F hB hF
    hRoneN hD2N hCN.2.2
  have hM0 : 0 ≤ M N := by
    unfold M BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeMean
    exact Finset.sum_nonneg fun n hn =>
      Erdos6.Maynard.tupleReciprocalGSquarefreeAF_nonneg _ n
  have hTail0 : 0 ≤ Tail N := by dsimp [Tail]; positivity
  have hden : 0 < Q N ^ (k + 2) := pow_pos hQN _
  have hcard : Fintype.card (Erdos6.Maynard.tupleOffFace H m) = k := by
    calc
      Fintype.card (Erdos6.Maynard.tupleOffFace H m) =
          (Erdos6.Maynard.tupleOffFace H m).card := Fintype.card_coe _
      _ = H.card - 1 := by
        unfold Erdos6.Maynard.tupleOffFace
        rw [Finset.card_erase_of_mem m.2]
      _ = k := by
        dsimp [k]
        rw [Finset.card_erase_of_mem (Finset.mem_attach H m), Finset.card_attach]
  have houterEq : Erdos6.Maynard.tupleNaturalScale
      (Erdos6.Maynard.tupleOffFace H m) alpha N = Q N ^ k := by
    unfold Erdos6.Maynard.tupleNaturalScale
    rw [hcard]
  have hscaleEq :
      BoundedGaps.Maynard.preSieveSingularSeries (D N) ^ 2 * L N ^ 2 *
          Erdos6.Maynard.tupleNaturalScale
            (Erdos6.Maynard.tupleOffFace H m) alpha N =
        Q N ^ (k + 2) := by
    rw [houterEq]
    dsimp [Q]
    rw [pow_add]
    ring
  rw [show BoundedGaps.Maynard.preSieveSingularSeries
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
        Real.log (Erdos6.Maynard.maynardRadius alpha N) ^ 2 *
          Erdos6.Maynard.tupleNaturalScale
            (Erdos6.Maynard.tupleOffFace H m) alpha N =
        Q N ^ (k + 2) by simpa [D, L, R] using hscaleEq,
      abs_div, abs_of_pos hden]
  calc
    |Erdos6.Maynard.tupleRestrictedCross H alpha F N m| /
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

/-- If the full coordinate fiber has a positive normalized lower bound and
the restricted cross term is negligible, then the restricted kernel has the
same lower bound up to an arbitrary strict margin. -/
theorem eventually_tupleRestrictedGKernel_normalized_gt_of_fiber
    {H : Finset ℕ} {alpha c C B : ℝ} (halpha : 0 < alpha)
    (F : (H → ℝ) → ℝ) (hB : 0 ≤ B) (hF : ∀ t, |F t| ≤ B)
    (m : H) (hc : c < C)
    (hfiber : ∀ᶠ N : ℕ in atTop,
      C < tupleCoordinateFiberSquareDiagonalFor H alpha F N m /
        (BoundedGaps.Maynard.preSieveSingularSeries
            (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
          Real.log (Erdos6.Maynard.maynardRadius alpha N) ^ 2 *
          Erdos6.Maynard.tupleNaturalScale
            (Erdos6.Maynard.tupleOffFace H m) alpha N))
    (hcross : Tendsto (fun N : ℕ =>
      Erdos6.Maynard.tupleRestrictedCross H alpha F N m /
        (BoundedGaps.Maynard.preSieveSingularSeries
            (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
          Real.log (Erdos6.Maynard.maynardRadius alpha N) ^ 2 *
          Erdos6.Maynard.tupleNaturalScale
            (Erdos6.Maynard.tupleOffFace H m) alpha N))
      atTop (nhds 0)) :
    ∀ᶠ N : ℕ in atTop,
      c < Erdos6.Maynard.tupleRestrictedGKernel H alpha F N m /
        (BoundedGaps.Maynard.preSieveSingularSeries
            (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
          Real.log (Erdos6.Maynard.maynardRadius alpha N) ^ 2 *
          Erdos6.Maynard.tupleNaturalScale
            (Erdos6.Maynard.tupleOffFace H m) alpha N) := by
  let scale : ℕ → ℝ := fun N =>
    BoundedGaps.Maynard.preSieveSingularSeries
        (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
      Real.log (Erdos6.Maynard.maynardRadius alpha N) ^ 2 *
      Erdos6.Maynard.tupleNaturalScale
        (Erdos6.Maynard.tupleOffFace H m) alpha N
  have hpert := tendsto_normalizedTupleCoordinateOneSquarePerturbationFor_zero
    halpha m B
  have hgap : 0 < C - c := sub_pos.mpr hc
  have hthird : 0 < (C - c) / 3 := div_pos hgap (by norm_num)
  have hsmall : ∀ᶠ N : ℕ in atTop,
      tupleCoordinateOneSquarePerturbationFor H alpha N m B / scale N <
        (C - c) / 3 := by
    have he := hpert.eventually (eventually_lt_nhds hthird)
    simpa [scale] using he
  have hcrossSmall : ∀ᶠ N : ℕ in atTop,
      |Erdos6.Maynard.tupleRestrictedCross H alpha F N m / scale N| <
        (C - c) / 3 := by
    have ha := ((tendsto_zero_iff_abs_tendsto_zero _).1 hcross).eventually
      (eventually_lt_nhds hthird)
    simpa [scale] using ha
  have hcond := BoundedGaps.Maynard.eventually_engelsmaMaynardCrossBound_conditions
    halpha
  have hRone := BoundedGaps.Maynard.eventually_one_lt_engelsmaMaynardRadius halpha
  have houter := Erdos6.Maynard.eventually_tupleNaturalScale_pos
    (H := Erdos6.Maynard.tupleOffFace H m) halpha
  filter_upwards [hfiber, hsmall, hcrossSmall, hcond, hRone, houter] with
      N hfiberN hsmallN hcrossN hcondN hRoneN houterN
  have hlog : 0 < Real.log (Erdos6.Maynard.maynardRadius alpha N) :=
    Real.log_pos (by exact_mod_cast hRoneN)
  have hpre : 0 < BoundedGaps.Maynard.preSieveSingularSeries
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) :=
    BoundedGaps.Maynard.preSieveSingularSeries_pos _
  have hscale : 0 < scale N := by
    dsimp [scale]
    exact mul_pos (mul_pos (sq_pos_of_pos hpre) (sq_pos_of_pos hlog)) houterN
  have hbridge := abs_tupleCoordinateOneYDiagonal_sub_fiberSquareDiagonalFor_le
    F hB hF N m hcondN.2.1 hcondN.2.2
  have hdiagLower :
      tupleCoordinateFiberSquareDiagonalFor H alpha F N m -
          tupleCoordinateOneSquarePerturbationFor H alpha N m B ≤
        Erdos6.Maynard.tupleCoordinateOneYDiagonal H alpha F N m := by
    have hn := neg_le_of_abs_le hbridge
    linarith
  have hdiagDiv := div_le_div_of_nonneg_right hdiagLower hscale.le
  have hcrossUpper :
      Erdos6.Maynard.tupleRestrictedCross H alpha F N m / scale N <
        (C - c) / 3 :=
    lt_of_abs_lt hcrossN
  have hid := Erdos6.Maynard.tupleRestrictedGKernel_eq_quadratic_sub_cross
    (H := H) (alpha := alpha) (F := F) (N := N) m
  rw [Erdos6.Maynard.tupleRestrictedQuadratic_eq_yDiagonal,
    Erdos6.Maynard.tupleRestrictedYDiagonal_eq_coordinateOne] at hid
  rw [hid, sub_div]
  rw [sub_div] at hdiagDiv
  simpa [scale] using (show c <
      Erdos6.Maynard.tupleCoordinateOneYDiagonal H alpha F N m / scale N -
        Erdos6.Maynard.tupleRestrictedCross H alpha F N m / scale N by
    linarith)

end

end MaynardTao
