import ErdosProblems.Erdos239.External.Erdos67.LogSecondDerivative

/-!
# One-step logarithmic-phase estimates with a real starting point

Residue-class decomposition changes the beginning of a dyadic block from an
integer to a positive real number.  This file proves the one-step van der
Corput estimate directly for that real start and for an arbitrary prefix
length.  No rounding loss is hidden in the statement.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace Erdos67.LogSecondDerivativeReal

noncomputable section

open Erdos1149
open Erdos67.LogPhaseHigherDerivative
open Erdos67.LogSecondDerivative

/-- A logarithmic phase on a block with positive real starting point `U`. -/
def realBlockPhase (a U : ℝ) (n : ℕ) : ℂ :=
  HigherDerivative.phase (shiftedLogPhase a U n)

@[simp]
theorem norm_realBlockPhase (a U : ℝ) {n : ℕ} :
    ‖realBlockPhase a U n‖ = 1 :=
  HigherDerivative.norm_phase _

/-- The lag correlation bound with a real starting point.  The prefix
length `P` is independent of `U`; `P ≤ U` supplies enough room for the
calculus window. -/
theorem norm_intervalCorrelation_realBlockPhase_le
    {a U : ℝ} {P r : ℕ}
    (ha : 0 < a) (hU : 0 < U) (hPU : (P : ℝ) ≤ U)
    (hr : 0 < r) (hrP : r < P)
    (hscale : 8 * (r : ℝ) * a ≤ U ^ 2) :
    ‖intervalCorrelation (realBlockPhase a U) P r‖ ≤
      9 * U ^ 2 / (a * r) := by
  let lam : ℝ := (r : ℝ) * a / (9 * U ^ 2)
  have hrRpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hU2pos : 0 < U ^ 2 := by positivity
  have hra : (r : ℝ) * a ≤ U ^ 2 / 8 := by linarith
  have hlampos : 0 < lam := by
    dsimp only [lam]
    positivity
  have hlam72 : lam ≤ 1 / 72 := by
    dsimp only [lam]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 9 * U ^ 2)).2
    nlinarith
  have hlamhalf : lam ≤ 1 / 2 := hlam72.trans (by norm_num)
  have hwindow :
      ((P - r : ℕ) : ℝ) + (1 : ℝ) * 2 * r + 1 ≤ 2 * U := by
    have hnat : P - r + 1 * 2 * r + 1 ≤ 2 * P := by omega
    calc
      ((P - r : ℕ) : ℝ) + (1 : ℝ) * 2 * r + 1 =
          ((P - r + 1 * 2 * r + 1 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (2 * P : ℕ) := by exact_mod_cast hnat
      _ = 2 * (P : ℝ) := by norm_cast
      _ ≤ 2 * U := by gcongr
  have hlower : lam ≤ (r : ℝ) ^ 1 *
      (a * (Nat.factorial 1 : ℝ) *
        (3 * U) ^ (-((1 + 1 : ℕ) : ℤ))) := by
    dsimp only [lam]
    simp only [pow_one, Nat.factorial_one]
    rw [zpow_neg, zpow_natCast]
    field_simp
    norm_num
    nlinarith
  have hupperQuarter : ((2 : ℝ) * r) ^ 1 *
      (a * (Nat.factorial 1 : ℝ) *
        U ^ (-((1 + 1 : ℕ) : ℤ))) ≤ 1 / 4 := by
    simp only [pow_one, Nat.factorial_one]
    rw [zpow_neg, zpow_natCast]
    norm_num only [Nat.cast_one, mul_one]
    calc
      2 * (r : ℝ) * (a * (U ^ 2)⁻¹) =
          (2 * (r : ℝ) * a) / U ^ 2 := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ 1 / 4 := by
        apply (div_le_iff₀ hU2pos).2
        nlinarith
  have hupper : ((2 : ℝ) * r) ^ 1 *
      (a * (Nat.factorial 1 : ℝ) *
        U ^ (-((1 + 1 : ℕ) : ℤ))) ≤ 1 - lam := by
    exact hupperQuarter.trans (by linarith)
  have hcond := terminalIncrementCondition_shiftedLog
    (a := a) (X := U) (lam := lam)
    (s := 1) (K := 2) (d := r) (P := P - r)
    ha hU (by norm_num) [(r, 1, 0)] (singleton_lag_mem r)
    (by norm_num at hwindow ⊢; exact hwindow) hlower hupper
  have hKL := HigherDerivative.norm_phaseSum_le_inv_of_terminalIncrementCondition
    (HigherDerivative.iteratedPairDifference
      (fun n ↦ shiftedLogPhase a U n) [(r, 1, 0)])
    (P - r) lam hlampos hlamhalf hcond
  have hcorr : intervalCorrelation (realBlockPhase a U) P r =
      ∑ n ∈ range (P - r),
        HigherDerivative.phase
          (HigherDerivative.iteratedPairDifference
            (fun n ↦ shiftedLogPhase a U n) [(r, 1, 0)] n) := by
    unfold intervalCorrelation realBlockPhase
    apply sum_congr rfl
    intro n hn
    simpa only [RestrictedWeyl.translatedPairCorrelation,
      HigherDerivative.iteratedPairDifference,
      HigherDerivative.pairDifference, one_mul, zero_mul, add_zero] using
      HigherDerivative.translatedPairCorrelation_phase_eq
        (fun x : ℕ ↦ shiftedLogPhase a U x) r 1 0 n
  rw [hcorr]
  calc
    ‖∑ n ∈ range (P - r),
        HigherDerivative.phase
          (HigherDerivative.iteratedPairDifference
            (fun n ↦ shiftedLogPhase a U n) [(r, 1, 0)] n)‖ ≤
        1 / lam := hKL
    _ = 9 * U ^ 2 / (a * r) := by
      dsimp only [lam]
      field_simp

/-- Summed lag correlations for a real-start prefix. -/
theorem sum_norm_intervalCorrelation_realBlockPhase_le
    {a U : ℝ} {P H : ℕ}
    (ha : 0 < a) (hU : 0 < U) (hPU : (P : ℝ) ≤ U)
    (hH : 0 < H) (hHP : H ≤ P)
    (hscale : 8 * (H : ℝ) * a ≤ U ^ 2) :
    (∑ r ∈ Ico 1 H,
        ‖intervalCorrelation (realBlockPhase a U) P r‖) ≤
      9 * (U ^ 2 / a) * (1 + Real.log (H : ℝ)) := by
  have hUa0 : 0 ≤ U ^ 2 / a := by positivity
  calc
    (∑ r ∈ Ico 1 H,
        ‖intervalCorrelation (realBlockPhase a U) P r‖) ≤
        ∑ r ∈ Ico 1 H,
          9 * (U ^ 2 / a) * ((1 : ℝ) / r) := by
      apply sum_le_sum
      intro r hrmem
      have hrdata := Finset.mem_Ico.mp hrmem
      have hrpos : 0 < r := by omega
      have hrP : r < P := hrdata.2.trans_le hHP
      have hrH : (r : ℝ) ≤ H := by exact_mod_cast hrdata.2.le
      have hrscale : 8 * (r : ℝ) * a ≤ U ^ 2 := by
        calc
          8 * (r : ℝ) * a ≤ 8 * (H : ℝ) * a := by gcongr
          _ ≤ U ^ 2 := hscale
      have hcorr := norm_intervalCorrelation_realBlockPhase_le
        ha hU hPU hrpos hrP hrscale
      calc
        ‖intervalCorrelation (realBlockPhase a U) P r‖ ≤
            9 * U ^ 2 / (a * r) := hcorr
        _ = 9 * (U ^ 2 / a) * ((1 : ℝ) / r) := by field_simp
    _ = 9 * (U ^ 2 / a) *
        (∑ r ∈ Ico 1 H, (1 : ℝ) / r) := by rw [Finset.mul_sum]
    _ ≤ 9 * (U ^ 2 / a) * (1 + Real.log (H : ℝ)) := by
      gcongr
      exact sum_Ico_one_div_le_one_add_log hH

/-- Coarse explicit one-step van der Corput inequality at a positive real
start `U`, for every prefix of length at most `U`. -/
theorem norm_realLogBlock_sq_vanDerCorput
    {a U : ℝ} {P H : ℕ}
    (hH : 0 < H) (hHP : H ≤ P)
    (ha : 0 < a) (hU : 0 < U) (hPU : (P : ℝ) ≤ U)
    (hscale : 8 * (H : ℝ) * a ≤ U ^ 2) :
    (H : ℝ) ^ 2 *
        ‖∑ n ∈ range P, realBlockPhase a U n‖ ^ 2 ≤
      ((P + H : ℕ) : ℝ) *
        ((H : ℝ) * P +
          18 * H * (U ^ 2 / a) * (1 + Real.log (H : ℝ))) := by
  have hvdc := interval_vanDerCorput_lag
    (realBlockPhase a U) P H hH hHP
      (fun n hn ↦ (norm_realBlockPhase a U).le)
  have hcorr := sum_norm_intervalCorrelation_realBlockPhase_le
    ha hU hPU hH hHP hscale
  calc
    (H : ℝ) ^ 2 * ‖∑ n ∈ range P, realBlockPhase a U n‖ ^ 2 ≤
        ((P + H : ℕ) : ℝ) *
          ((H : ℝ) * P +
            2 * H * ∑ r ∈ Ico 1 H,
              ‖intervalCorrelation (realBlockPhase a U) P r‖) := hvdc
    _ ≤ ((P + H : ℕ) : ℝ) *
        ((H : ℝ) * P +
          2 * H *
            (9 * (U ^ 2 / a) *
              (1 + Real.log (H : ℝ)))) := by
      gcongr
    _ = ((P + H : ℕ) : ℝ) *
        ((H : ℝ) * P +
          18 * H * (U ^ 2 / a) *
            (1 + Real.log (H : ℝ))) := by ring

/-- Square-root form of the real-start estimate.  Its coefficient tends to
zero with the freely chosen lag budget `H`.  The condition `U ≤ a` is the
lower half of the classical second-derivative band; the separated upper
condition is recorded by `hscale`. -/
theorem norm_realLogBlock_le_sqrt
    {a U : ℝ} {P H : ℕ}
    (hH : 0 < H) (hHP : H ≤ P)
    (ha : 0 < a) (hU : 0 < U) (hPU : (P : ℝ) ≤ U)
    (hUa : U ≤ a) (hscale : 8 * (H : ℝ) * a ≤ U ^ 2) :
    ‖∑ n ∈ range P, realBlockPhase a U n‖ ≤
      U * Real.sqrt
        (38 * (1 + Real.log (H : ℝ)) / (H : ℝ)) := by
  let S : ℝ := ‖∑ n ∈ range P, realBlockPhase a U n‖
  let L : ℝ := 1 + Real.log (H : ℝ)
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hHone : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hlogH : 0 ≤ Real.log (H : ℝ) := Real.log_nonneg hHone
  have hLone : 1 ≤ L := by dsimp only [L]; linarith
  have hLnonneg : 0 ≤ L := zero_le_one.trans hLone
  have hHPR : (H : ℝ) ≤ P := by exact_mod_cast hHP
  have hPadd : ((P + H : ℕ) : ℝ) ≤ 2 * U := by
    push_cast
    linarith
  have hratio : U ^ 2 / a ≤ U := by
    apply (div_le_iff₀ ha).2
    nlinarith
  have hinside :
      (H : ℝ) * P + 18 * H * (U ^ 2 / a) * L ≤
        19 * H * U * L := by
    have hHnonneg : (0 : ℝ) ≤ H := hHR.le
    have hratioNonneg : 0 ≤ U ^ 2 / a := by positivity
    have hfirst : (H : ℝ) * P ≤ H * U :=
      mul_le_mul_of_nonneg_left hPU hHnonneg
    have hsecond : 18 * (H : ℝ) * (U ^ 2 / a) * L ≤
        18 * H * U * L := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio (by positivity)) hLnonneg
    have hfirstL : (H : ℝ) * U ≤ H * U * L := by
      exact (le_mul_iff_one_le_right (mul_pos hHR hU)).2 hLone
    calc
      (H : ℝ) * P + 18 * H * (U ^ 2 / a) * L ≤
          H * U + 18 * H * U * L := add_le_add hfirst hsecond
      _ ≤ H * U * L + 18 * H * U * L := by
        exact add_le_add hfirstL le_rfl
      _ = 19 * H * U * L := by ring
  have hvdc := norm_realLogBlock_sq_vanDerCorput
    hH hHP ha hU hPU hscale
  have hscaled : (H : ℝ) ^ 2 * S ^ 2 ≤
      38 * H * U ^ 2 * L := by
    dsimp only [S, L]
    calc
      (H : ℝ) ^ 2 *
          ‖∑ n ∈ range P, realBlockPhase a U n‖ ^ 2 ≤
          ((P + H : ℕ) : ℝ) *
            ((H : ℝ) * P +
              18 * H * (U ^ 2 / a) *
                (1 + Real.log (H : ℝ))) := hvdc
      _ ≤ (2 * U) * (19 * H * U * (1 + Real.log (H : ℝ))) := by
        gcongr
      _ = 38 * H * U ^ 2 * (1 + Real.log (H : ℝ)) := by ring
  have hcancel : (H : ℝ) * S ^ 2 ≤ 38 * U ^ 2 * L := by
    have hmul : (H : ℝ) * ((H : ℝ) * S ^ 2) ≤
        (H : ℝ) * (38 * U ^ 2 * L) := by
      calc
        (H : ℝ) * ((H : ℝ) * S ^ 2) = (H : ℝ) ^ 2 * S ^ 2 := by ring
        _ ≤ 38 * H * U ^ 2 * L := hscaled
        _ = (H : ℝ) * (38 * U ^ 2 * L) := by ring
    exact le_of_mul_le_mul_left hmul hHR
  have hsquare : S ^ 2 ≤ 38 * U ^ 2 * L / H := by
    apply (le_div_iff₀ hHR).2
    simpa only [mul_comm] using hcancel
  have hrad : 0 ≤ 38 * L / (H : ℝ) := by positivity
  have htarget : 0 ≤ U * Real.sqrt (38 * L / (H : ℝ)) := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) htarget).mp
  change S ^ 2 ≤ (U * Real.sqrt (38 * L / (H : ℝ))) ^ 2
  rw [mul_pow, Real.sq_sqrt hrad]
  calc
    S ^ 2 ≤ 38 * U ^ 2 * L / H := hsquare
    _ = U ^ 2 * (38 * L / H) := by field_simp

/-- Closed dyadic intervals may contribute one endpoint more than the clean
condition `P ≤ U` permits.  Removing that final unit term costs exactly
one, while preserving the same cancellation bound on the preceding prefix. -/
theorem norm_realLogBlock_le_sqrt_add_one
    {a U : ℝ} {P H : ℕ}
    (hH : 0 < H) (hHP : H + 1 ≤ P)
    (ha : 0 < a) (hU : 0 < U) (hPU : (P : ℝ) ≤ U + 1)
    (hUa : U ≤ a) (hscale : 8 * (H : ℝ) * a ≤ U ^ 2) :
    ‖∑ n ∈ range P, realBlockPhase a U n‖ ≤
      U * Real.sqrt
        (38 * (1 + Real.log (H : ℝ)) / (H : ℝ)) + 1 := by
  have hPpos : 0 < P := by omega
  obtain ⟨P', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hPpos.ne'
  have hHP' : H ≤ P' := by omega
  have hP'U : (P' : ℝ) ≤ U := by
    push_cast at hPU
    linarith
  have hmain := norm_realLogBlock_le_sqrt
    hH hHP' ha hU hP'U hUa hscale
  rw [sum_range_succ]
  calc
    ‖(∑ n ∈ range P', realBlockPhase a U n) +
        realBlockPhase a U P'‖ ≤
        ‖∑ n ∈ range P', realBlockPhase a U n‖ +
          ‖realBlockPhase a U P'‖ := norm_add_le _ _
    _ ≤ U * Real.sqrt
          (38 * (1 + Real.log (H : ℝ)) / (H : ℝ)) + 1 := by
      rw [norm_realBlockPhase]
      gcongr

end

end Erdos67.LogSecondDerivativeReal
