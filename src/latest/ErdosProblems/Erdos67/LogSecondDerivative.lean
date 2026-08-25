import ErdosProblems.Erdos67.IntervalVanDerCorput
import ErdosProblems.Erdos67.LogPhaseHigherDerivative
import ErdosProblems.Erdos1149.AnalyticParameters

/-!
# One-step van der Corput for a logarithmic phase

This file treats the height band which corresponds to one classical
second-derivative step.  For the phase `a * log (N+n)`, a lag `r` produces
the singleton controlled-Weyl history `[(r,1,0)]`.  Its terminal increment
has size comparable to `a*r/N^2`; the finite Kusmin--Landau theorem therefore
bounds the lag correlation by `9*N^2/(a*r)`.  Summing over the lags gives the
usual harmonic loss.
-/

open scoped BigOperators ComplexConjugate
open Finset
open Filter

namespace Erdos67.LogSecondDerivative

noncomputable section

open Erdos1149
open Erdos67.LogPhaseHigherDerivative

/-- The logarithmic phase sequence on the dyadic block starting at `N`. -/
def blockPhase (a : ℝ) (N n : ℕ) : ℂ :=
  HigherDerivative.phase (shiftedLogPhase a N n)

@[simp]
theorem norm_blockPhase (a : ℝ) {N n : ℕ} :
    ‖blockPhase a N n‖ = 1 :=
  HigherDerivative.norm_phase _

/-- The singleton history which represents the positive lag `r` is one of
the two off-diagonal leaves for shift count two. -/
lemma singleton_lag_mem (r : ℕ) :
    [(r, 1, 0)] ∈ RestrictedWeyl.offDiagonalHistoryLeaves
      (HigherDerivative.constantControlledSteps 1 2 r (by norm_num)) [] := by
  simp only [HigherDerivative.constantControlledSteps, List.replicate_one,
    RestrictedWeyl.offDiagonalHistoryLeaves, Finset.mem_biUnion,
    Finset.mem_singleton]
  refine ⟨[(r, 1, 0)], ?_, rfl⟩
  apply RestrictedWeyl.cons_mem_offDiagonalChildren
  all_goals simp [HigherDerivative.controlledStep]

/-- The interval correlation is exactly the phase sum associated with the
singleton controlled leaf. -/
lemma intervalCorrelation_blockPhase_eq (a : ℝ) (N r : ℕ) :
    intervalCorrelation (blockPhase a N) N r =
      ∑ n ∈ range (N - r),
        HigherDerivative.phase
          (HigherDerivative.iteratedPairDifference
            (fun n ↦ shiftedLogPhase a N n) [(r, 1, 0)] n) := by
  unfold intervalCorrelation blockPhase
  apply sum_congr rfl
  intro n hn
  simpa only [RestrictedWeyl.translatedPairCorrelation,
    HigherDerivative.iteratedPairDifference,
    HigherDerivative.pairDifference, one_mul, zero_mul, add_zero] using
    HigherDerivative.translatedPairCorrelation_phase_eq
      (fun x : ℕ ↦ shiftedLogPhase a N x) r 1 0 n

/-- One lag of the logarithmic block has the classical reciprocal-lag
bound.  The scale hypothesis is deliberately stated in the form consumed
later for every `r < H`. -/
theorem norm_intervalCorrelation_blockPhase_le
    {a : ℝ} {N r : ℕ}
    (ha : 0 < a) (hr : 0 < r) (hrN : r < N)
    (hscale : 8 * (r : ℝ) * a ≤ (N : ℝ) ^ 2) :
    ‖intervalCorrelation (blockPhase a N) N r‖ ≤
      9 * (N : ℝ) ^ 2 / (a * r) := by
  let lam : ℝ := (r : ℝ) * a / (9 * (N : ℝ) ^ 2)
  have hNpos : 0 < N := hr.trans hrN
  have hNRpos : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hrRpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hN2pos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have hra : (r : ℝ) * a ≤ (N : ℝ) ^ 2 / 8 := by
    linarith
  have hlampos : 0 < lam := by
    dsimp only [lam]
    positivity
  have hlam72 : lam ≤ 1 / 72 := by
    dsimp only [lam]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 9 * (N : ℝ) ^ 2)).2
    nlinarith
  have hlamhalf : lam ≤ 1 / 2 := hlam72.trans (by norm_num)
  have hwindow :
      ((N - r : ℕ) : ℝ) + (1 : ℝ) * 2 * r + 1 ≤ 2 * (N : ℝ) := by
    exact_mod_cast (show N - r + 1 * 2 * r + 1 ≤ 2 * N by omega)
  have hlower : lam ≤ (r : ℝ) ^ 1 *
      (a * (Nat.factorial 1 : ℝ) *
        (3 * (N : ℝ)) ^ (-((1 + 1 : ℕ) : ℤ))) := by
    dsimp only [lam]
    simp only [pow_one, Nat.factorial_one]
    rw [zpow_neg, zpow_natCast]
    field_simp <;> ring_nf
    all_goals exact le_rfl
  have hupperQuarter : ((2 : ℝ) * r) ^ 1 *
      (a * (Nat.factorial 1 : ℝ) *
        (N : ℝ) ^ (-((1 + 1 : ℕ) : ℤ))) ≤ 1 / 4 := by
    simp only [pow_one, Nat.factorial_one]
    rw [zpow_neg, zpow_natCast]
    norm_num only [Nat.cast_one, mul_one]
    calc
      2 * (r : ℝ) * (a * ((N : ℝ) ^ 2)⁻¹) =
          (2 * (r : ℝ) * a) / (N : ℝ) ^ 2 := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ 1 / 4 := by
        apply (div_le_iff₀ hN2pos).2
        nlinarith
  have hupper : ((2 : ℝ) * r) ^ 1 *
      (a * (Nat.factorial 1 : ℝ) *
        (N : ℝ) ^ (-((1 + 1 : ℕ) : ℤ))) ≤ 1 - lam := by
    exact hupperQuarter.trans (by linarith)
  have hcond := terminalIncrementCondition_shiftedLog
    (a := a) (X := (N : ℝ)) (lam := lam)
    (s := 1) (K := 2) (d := r) (P := N - r)
    ha hNRpos (by norm_num) [(r, 1, 0)] (singleton_lag_mem r)
    (by norm_num at hwindow ⊢; exact hwindow) hlower hupper
  have hKL := HigherDerivative.norm_phaseSum_le_inv_of_terminalIncrementCondition
    (HigherDerivative.iteratedPairDifference
      (fun n ↦ shiftedLogPhase a N n) [(r, 1, 0)])
    (N - r) lam hlampos hlamhalf hcond
  rw [intervalCorrelation_blockPhase_eq]
  calc
    ‖∑ n ∈ range (N - r),
        HigherDerivative.phase
          (HigherDerivative.iteratedPairDifference
            (fun n ↦ shiftedLogPhase a N n) [(r, 1, 0)] n)‖ ≤
        1 / lam := hKL
    _ = 9 * (N : ℝ) ^ 2 / (a * r) := by
      dsimp only [lam]
      field_simp

/-- The real reciprocal mass of the nonzero lags below `H` is bounded by
the standard harmonic estimate. -/
lemma sum_Ico_one_div_le_one_add_log {H : ℕ} (_hH : 0 < H) :
    (∑ r ∈ Ico 1 H, (1 : ℝ) / r) ≤ 1 + Real.log (H : ℝ) := by
  calc
    (∑ r ∈ Ico 1 H, (1 : ℝ) / r) ≤
        ∑ r ∈ Icc 1 H, (1 : ℝ) / r := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.Ico_subset_Icc_self
      intro r hrIcc hrNot
      positivity
    _ = ((harmonic H : ℚ) : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      simp only [Rat.cast_inv, Rat.cast_natCast, one_div]
    _ ≤ 1 + Real.log (H : ℝ) := harmonic_le_one_add_log H

/-- Summed correlation estimate for all van der Corput lags below `H`. -/
theorem sum_norm_intervalCorrelation_blockPhase_le
    {a : ℝ} {N H : ℕ}
    (ha : 0 < a) (hH : 0 < H) (hHN : H ≤ N)
    (hscale : 8 * (H : ℝ) * a ≤ (N : ℝ) ^ 2) :
    (∑ r ∈ Ico 1 H, ‖intervalCorrelation (blockPhase a N) N r‖) ≤
      9 * ((N : ℝ) ^ 2 / a) * (1 + Real.log (H : ℝ)) := by
  have ha0 : 0 ≤ a := ha.le
  have hNa0 : 0 ≤ (N : ℝ) ^ 2 / a := by positivity
  calc
    (∑ r ∈ Ico 1 H, ‖intervalCorrelation (blockPhase a N) N r‖) ≤
        ∑ r ∈ Ico 1 H, 9 * ((N : ℝ) ^ 2 / a) * ((1 : ℝ) / r) := by
      apply sum_le_sum
      intro r hrmem
      have hrdata := Finset.mem_Ico.mp hrmem
      have hrpos : 0 < r := by omega
      have hrN : r < N := hrdata.2.trans_le hHN
      have hrH : (r : ℝ) ≤ H := by exact_mod_cast hrdata.2.le
      have hrscale : 8 * (r : ℝ) * a ≤ (N : ℝ) ^ 2 := by
        calc
          8 * (r : ℝ) * a ≤ 8 * (H : ℝ) * a := by gcongr
          _ ≤ (N : ℝ) ^ 2 := hscale
      have hcorr := norm_intervalCorrelation_blockPhase_le
        ha hrpos hrN hrscale
      calc
        ‖intervalCorrelation (blockPhase a N) N r‖ ≤
            9 * (N : ℝ) ^ 2 / (a * r) := hcorr
        _ = 9 * ((N : ℝ) ^ 2 / a) * ((1 : ℝ) / r) := by
          field_simp
    _ = 9 * ((N : ℝ) ^ 2 / a) *
        (∑ r ∈ Ico 1 H, (1 : ℝ) / r) := by
      rw [Finset.mul_sum]
    _ ≤ 9 * ((N : ℝ) ^ 2 / a) * (1 + Real.log (H : ℝ)) := by
      gcongr
      exact sum_Ico_one_div_le_one_add_log hH

/-- Coarse explicit one-step second-derivative bound for a logarithmic
phase.  The condition `8*H*a ≤ N^2` is the advertised range
`H ≤ (1/8) N^2/a`; the additional two inequalities record the height band
`N ≤ a ≤ N^2` used by the global decomposition. -/
theorem norm_logBlock_sq_vanDerCorput
    {a : ℝ} {N H : ℕ}
    (hH : 0 < H) (hHN : H ≤ N)
    (ha : 0 < a) (_haLower : (N : ℝ) ≤ a)
    (_haUpper : a ≤ (N : ℝ) ^ 2)
    (hscale : 8 * (H : ℝ) * a ≤ (N : ℝ) ^ 2) :
    (H : ℝ) ^ 2 *
        ‖∑ n ∈ range N, blockPhase a N n‖ ^ 2 ≤
      ((N + H : ℕ) : ℝ) *
        ((H : ℝ) * N +
          18 * H * ((N : ℝ) ^ 2 / a) *
            (1 + Real.log (H : ℝ))) := by
  have hvdc := interval_vanDerCorput_lag
    (blockPhase a N) N H hH hHN
      (fun n hn ↦ (norm_blockPhase a).le)
  have hcorr := sum_norm_intervalCorrelation_blockPhase_le
    ha hH hHN hscale
  calc
    (H : ℝ) ^ 2 * ‖∑ n ∈ range N, blockPhase a N n‖ ^ 2 ≤
        ((N + H : ℕ) : ℝ) *
          ((H : ℝ) * N +
            2 * H * ∑ r ∈ Ico 1 H,
              ‖intervalCorrelation (blockPhase a N) N r‖) := hvdc
    _ ≤ ((N + H : ℕ) : ℝ) *
        ((H : ℝ) * N +
          2 * H *
            (9 * ((N : ℝ) ^ 2 / a) *
              (1 + Real.log (H : ℝ)))) := by
      gcongr
    _ = ((N + H : ℕ) : ℝ) *
        ((H : ℝ) * N +
          18 * H * ((N : ℝ) ^ 2 / a) *
            (1 + Real.log (H : ℝ))) := by ring

/-- A normalized version of the one-step estimate.  This form makes the
power saving transparent once `H` is chosen as a small fixed power of `N`. -/
theorem norm_logBlock_sq_le_div
    {a : ℝ} {N H : ℕ}
    (hH : 0 < H) (hHN : H ≤ N)
    (ha : 0 < a) (haLower : (N : ℝ) ≤ a)
    (haUpper : a ≤ (N : ℝ) ^ 2)
    (hscale : 8 * (H : ℝ) * a ≤ (N : ℝ) ^ 2) :
    ‖∑ n ∈ range N, blockPhase a N n‖ ^ 2 ≤
      2 * (N : ℝ) ^ 2 * (19 + 18 * Real.log (H : ℝ)) / H := by
  have hmain := norm_logBlock_sq_vanDerCorput
    hH hHN ha haLower haUpper hscale
  have hHRpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hNRpos : (0 : ℝ) < N := by
    exact_mod_cast hH.trans_le hHN
  have hlogH : 0 ≤ Real.log (H : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hH)
  have hNa : (N : ℝ) ^ 2 / a ≤ N := by
    apply (div_le_iff₀ ha).2
    nlinarith
  have hright :
      ((N + H : ℕ) : ℝ) *
          ((H : ℝ) * N +
            18 * H * ((N : ℝ) ^ 2 / a) *
              (1 + Real.log (H : ℝ))) ≤
        2 * (N : ℝ) *
          ((H : ℝ) * N * (19 + 18 * Real.log (H : ℝ))) := by
    have hNH : ((N + H : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
      push_cast
      have hHNR : (H : ℝ) ≤ N := by exact_mod_cast hHN
      linarith
    have hinner :
        (H : ℝ) * N +
            18 * H * ((N : ℝ) ^ 2 / a) *
              (1 + Real.log (H : ℝ)) ≤
          (H : ℝ) * N * (19 + 18 * Real.log (H : ℝ)) := by
      calc
        (H : ℝ) * N +
            18 * H * ((N : ℝ) ^ 2 / a) *
              (1 + Real.log (H : ℝ)) ≤
            (H : ℝ) * N +
              18 * H * N * (1 + Real.log (H : ℝ)) := by
          gcongr
        _ = (H : ℝ) * N * (19 + 18 * Real.log (H : ℝ)) := by ring
    exact mul_le_mul hNH hinner (by positivity) (by positivity)
  have hsq : (H : ℝ) ^ 2 *
      ‖∑ n ∈ range N, blockPhase a N n‖ ^ 2 ≤
        2 * (N : ℝ) *
          ((H : ℝ) * N * (19 + 18 * Real.log (H : ℝ))) :=
    hmain.trans hright
  apply (le_div_iff₀ hHRpos).2
  calc
    ‖∑ n ∈ range N, blockPhase a N n‖ ^ 2 * H ≤
        ((H : ℝ) ^ 2 *
          ‖∑ n ∈ range N, blockPhase a N n‖ ^ 2) / H := by
      field_simp
      exact le_rfl
    _ ≤ (2 * (N : ℝ) *
          ((H : ℝ) * N * (19 + 18 * Real.log (H : ℝ)))) / H := by
      gcongr
    _ = 2 * (N : ℝ) ^ 2 * (19 + 18 * Real.log (H : ℝ)) := by
      field_simp

/-! ## Real starts and arbitrary prefixes -/

/-- The same logarithmic phase sequence, based at an arbitrary positive real
number.  This is the form needed after splitting a Dirichlet character into
residue classes. -/
def realStartBlockPhase (a U : ℝ) (n : ℕ) : ℂ :=
  HigherDerivative.phase (shiftedLogPhase a U n)

@[simp]
theorem norm_realStartBlockPhase (a U : ℝ) (n : ℕ) :
    ‖realStartBlockPhase a U n‖ = 1 :=
  HigherDerivative.norm_phase _

lemma intervalCorrelation_realStartBlockPhase_eq (a U : ℝ) (P r : ℕ) :
    intervalCorrelation (realStartBlockPhase a U) P r =
      ∑ n ∈ range (P - r),
        HigherDerivative.phase
          (HigherDerivative.iteratedPairDifference
            (fun n ↦ shiftedLogPhase a U n) [(r, 1, 0)] n) := by
  unfold intervalCorrelation realStartBlockPhase
  apply sum_congr rfl
  intro n hn
  simpa only [RestrictedWeyl.translatedPairCorrelation,
    HigherDerivative.iteratedPairDifference,
    HigherDerivative.pairDifference, one_mul, zero_mul, add_zero] using
    HigherDerivative.translatedPairCorrelation_phase_eq
      (fun x : ℕ ↦ shiftedLogPhase a U x) r 1 0 n

/-- Reciprocal-lag bound at an arbitrary positive real start. -/
theorem norm_intervalCorrelation_realStartBlockPhase_le
    {a U : ℝ} {P r : ℕ}
    (ha : 0 < a) (hU : 0 < U) (hr : 0 < r) (hrP : r < P)
    (hwindow : ((P - r : ℕ) : ℝ) + 2 * r + 1 ≤ 2 * U)
    (hscale : 8 * (r : ℝ) * a ≤ U ^ 2) :
    ‖intervalCorrelation (realStartBlockPhase a U) P r‖ ≤
      9 * U ^ 2 / (a * r) := by
  let lam : ℝ := (r : ℝ) * a / (9 * U ^ 2)
  have hrRpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hU2pos : (0 : ℝ) < U ^ 2 := by positivity
  have hra : (r : ℝ) * a ≤ U ^ 2 / 8 := by linarith
  have hlampos : 0 < lam := by dsimp only [lam]; positivity
  have hlam72 : lam ≤ 1 / 72 := by
    dsimp only [lam]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 9 * U ^ 2)).2
    nlinarith
  have hlamhalf : lam ≤ 1 / 2 := hlam72.trans (by norm_num)
  have hlower : lam ≤ (r : ℝ) ^ 1 *
      (a * (Nat.factorial 1 : ℝ) *
        (3 * U) ^ (-((1 + 1 : ℕ) : ℤ))) := by
    dsimp only [lam]
    simp only [pow_one, Nat.factorial_one]
    rw [zpow_neg, zpow_natCast]
    field_simp <;> ring_nf
    all_goals exact le_rfl
  have hupperQuarter : ((2 : ℝ) * r) ^ 1 *
      (a * (Nat.factorial 1 : ℝ) * U ^ (-((1 + 1 : ℕ) : ℤ))) ≤ 1 / 4 := by
    simp only [pow_one, Nat.factorial_one]
    rw [zpow_neg, zpow_natCast]
    norm_num only [Nat.cast_one, mul_one]
    calc
      2 * (r : ℝ) * (a * (U ^ 2)⁻¹) =
          (2 * (r : ℝ) * a) / U ^ 2 := by rw [div_eq_mul_inv]; ring
      _ ≤ 1 / 4 := by
        apply (div_le_iff₀ hU2pos).2
        nlinarith
  have hupper : ((2 : ℝ) * r) ^ 1 *
      (a * (Nat.factorial 1 : ℝ) * U ^ (-((1 + 1 : ℕ) : ℤ))) ≤ 1 - lam :=
    hupperQuarter.trans (by linarith)
  have hcond := terminalIncrementCondition_shiftedLog
    (a := a) (X := U) (lam := lam) (s := 1) (K := 2) (d := r)
    (P := P - r) ha hU (by norm_num) [(r, 1, 0)] (singleton_lag_mem r)
    (by norm_num at hwindow ⊢; exact hwindow) hlower hupper
  have hKL := HigherDerivative.norm_phaseSum_le_inv_of_terminalIncrementCondition
    (HigherDerivative.iteratedPairDifference
      (fun n ↦ shiftedLogPhase a U n) [(r, 1, 0)])
    (P - r) lam hlampos hlamhalf hcond
  rw [intervalCorrelation_realStartBlockPhase_eq]
  calc
    ‖∑ n ∈ range (P - r),
        HigherDerivative.phase
          (HigherDerivative.iteratedPairDifference
            (fun n ↦ shiftedLogPhase a U n) [(r, 1, 0)] n)‖ ≤ 1 / lam := hKL
    _ = 9 * U ^ 2 / (a * r) := by dsimp only [lam]; field_simp

/-- Arbitrary-prefix, arbitrary-real-start form of the one-step estimate. -/
theorem norm_realStartBlock_sq_vanDerCorput
    {a U : ℝ} {X P H : ℕ}
    (hH : 0 < H) (hHP : H ≤ P) (hPX : P ≤ X)
    (ha : 0 < a) (hU : 0 < U) (hXU : (X : ℝ) ≤ U)
    (hscale : 8 * (H : ℝ) * a ≤ U ^ 2) :
    (H : ℝ) ^ 2 *
        ‖∑ n ∈ range P, realStartBlockPhase a U n‖ ^ 2 ≤
      ((P + H : ℕ) : ℝ) *
        ((H : ℝ) * P +
          18 * H * (U ^ 2 / a) * (1 + Real.log (H : ℝ))) := by
  have hvdc := interval_vanDerCorput_lag
    (realStartBlockPhase a U) P H hH hHP
      (fun n hn ↦ (norm_realStartBlockPhase a U n).le)
  have hsum :
      (∑ r ∈ Ico 1 H,
        ‖intervalCorrelation (realStartBlockPhase a U) P r‖) ≤
        9 * (U ^ 2 / a) * (1 + Real.log (H : ℝ)) := by
    calc
      (∑ r ∈ Ico 1 H,
          ‖intervalCorrelation (realStartBlockPhase a U) P r‖) ≤
          ∑ r ∈ Ico 1 H,
            9 * (U ^ 2 / a) * ((1 : ℝ) / r) := by
        apply sum_le_sum
        intro r hrmem
        have hrdata := mem_Ico.mp hrmem
        have hrpos : 0 < r := by omega
        have hrP : r < P := hrdata.2.trans_le hHP
        have hrH : (r : ℝ) ≤ H := by exact_mod_cast hrdata.2.le
        have hrscale : 8 * (r : ℝ) * a ≤ U ^ 2 :=
          (by gcongr : 8 * (r : ℝ) * a ≤ 8 * (H : ℝ) * a) |>.trans hscale
        have hwindow : ((P - r : ℕ) : ℝ) + 2 * r + 1 ≤ 2 * U := by
          have hnat : P - r + 2 * r + 1 ≤ 2 * X := by omega
          have hreal : (((P - r + 2 * r + 1 : ℕ) : ℕ) : ℝ) ≤
              2 * (X : ℝ) := by exact_mod_cast hnat
          push_cast at hreal
          exact hreal.trans (by gcongr)
        have hcorr := norm_intervalCorrelation_realStartBlockPhase_le
          ha hU hrpos hrP hwindow hrscale
        calc
          ‖intervalCorrelation (realStartBlockPhase a U) P r‖ ≤
              9 * U ^ 2 / (a * r) := hcorr
          _ = 9 * (U ^ 2 / a) * ((1 : ℝ) / r) := by field_simp
      _ = 9 * (U ^ 2 / a) *
          (∑ r ∈ Ico 1 H, (1 : ℝ) / r) := by rw [Finset.mul_sum]
      _ ≤ 9 * (U ^ 2 / a) * (1 + Real.log (H : ℝ)) := by
        gcongr
        exact sum_Ico_one_div_le_one_add_log hH
  calc
    (H : ℝ) ^ 2 * ‖∑ n ∈ range P, realStartBlockPhase a U n‖ ^ 2 ≤
        ((P + H : ℕ) : ℝ) *
          ((H : ℝ) * P + 2 * H *
            ∑ r ∈ Ico 1 H,
              ‖intervalCorrelation (realStartBlockPhase a U) P r‖) := hvdc
    _ ≤ ((P + H : ℕ) : ℝ) *
        ((H : ℝ) * P +
          2 * H * (9 * (U ^ 2 / a) * (1 + Real.log (H : ℝ)))) := by gcongr
    _ = _ := by ring

/-- Normalized arbitrary-prefix form on a comparison scale `X`, valid for
every real start `U ∈ [X,2X]`. -/
theorem norm_realStartBlock_sq_le_div
    {a U : ℝ} {X P H : ℕ}
    (hH : 0 < H) (hHP : H ≤ P) (hPX : P ≤ X)
    (ha : 0 < a) (haLower : (X : ℝ) ≤ a)
    (hXU : (X : ℝ) ≤ U) (hUX : U ≤ 2 * X)
    (hscale : 8 * (H : ℝ) * a ≤ U ^ 2) :
    ‖∑ n ∈ range P, realStartBlockPhase a U n‖ ^ 2 ≤
      2 * (X : ℝ) ^ 2 * (73 + 72 * Real.log (H : ℝ)) / H := by
  have hXRpos : (0 : ℝ) < X := by exact_mod_cast hH.trans_le (hHP.trans hPX)
  have hmain := norm_realStartBlock_sq_vanDerCorput
    hH hHP hPX ha (hXRpos.trans_le hXU) hXU hscale
  have hHRpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hlogH : 0 ≤ Real.log (H : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hH)
  have hUquot : U ^ 2 / a ≤ 4 * X := by
    apply (div_le_iff₀ ha).2
    have hU0 : 0 ≤ U := (hXRpos.trans_le hXU).le
    nlinarith [sq_nonneg (U - 2 * X)]
  have hright :
      ((P + H : ℕ) : ℝ) *
          ((H : ℝ) * P +
            18 * H * (U ^ 2 / a) * (1 + Real.log (H : ℝ))) ≤
        2 * (X : ℝ) *
          ((H : ℝ) * X * (73 + 72 * Real.log (H : ℝ))) := by
    have hPH : ((P + H : ℕ) : ℝ) ≤ 2 * (X : ℝ) := by
      push_cast
      exact_mod_cast (show P + H ≤ 2 * X by omega)
    have hinner :
        (H : ℝ) * P + 18 * H * (U ^ 2 / a) *
            (1 + Real.log (H : ℝ)) ≤
          (H : ℝ) * X * (73 + 72 * Real.log (H : ℝ)) := by
      calc
        (H : ℝ) * P + 18 * H * (U ^ 2 / a) *
              (1 + Real.log (H : ℝ)) ≤
            (H : ℝ) * X + 18 * H * (4 * X) *
              (1 + Real.log (H : ℝ)) := by gcongr
        _ = (H : ℝ) * X * (73 + 72 * Real.log (H : ℝ)) := by ring
    exact mul_le_mul hPH hinner (by positivity) (by positivity)
  have hsq := hmain.trans hright
  apply (le_div_iff₀ hHRpos).2
  calc
    ‖∑ n ∈ range P, realStartBlockPhase a U n‖ ^ 2 * H ≤
        ((H : ℝ) ^ 2 *
          ‖∑ n ∈ range P, realStartBlockPhase a U n‖ ^ 2) / H := by
      field_simp
      exact le_rfl
    _ ≤ (2 * (X : ℝ) *
          ((H : ℝ) * X * (73 + 72 * Real.log (H : ℝ)))) / H := by gcongr
    _ = 2 * (X : ℝ) ^ 2 * (73 + 72 * Real.log (H : ℝ)) := by field_simp

/-! ## A uniform power-saving specialization -/

/-- The shift count used in the fixed-power specialization of the
second-derivative estimate. -/
def secondDerivativeShiftCount (N : ℕ) : ℕ :=
  ⌊(N : ℝ) ^ (1 / 32 : ℝ)⌋₊

/-- Eventually the one-step logarithmic block estimate gives a fixed power
saving, uniformly throughout the height band `N ≤ a ≤ N^(15/8)`.

The deliberately generous exponent `1/1024` makes all rounding and the
single logarithmic loss harmless.  Its only purpose is to provide a clean
fixed positive saving for the finite-depth diagonal argument. -/
theorem eventually_norm_logBlock_le_rpow :
    ∀ᶠ N : ℕ in atTop, ∀ a : ℝ,
      (N : ℝ) ≤ a → a ≤ (N : ℝ) ^ (15 / 8 : ℝ) →
      ‖∑ n ∈ range N, blockPhase a N n‖ ≤
        9 * (N : ℝ) ^ (1 - 1 / 1024 : ℝ) := by
  have hpow32 : ∀ᶠ N : ℕ in atTop,
      (2 : ℝ) ≤ (N : ℝ) ^ (1 / 32 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 32)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  have hpow64 : ∀ᶠ N : ℕ in atTop,
      (2 : ℝ) ≤ (N : ℝ) ^ (1 / 64 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 64)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  have hpowScale : ∀ᶠ N : ℕ in atTop,
      (8 : ℝ) ≤ (N : ℝ) ^ (3 / 32 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 32)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 8)
  have hpow256 : ∀ᶠ N : ℕ in atTop,
      (1 : ℝ) ≤ (N : ℝ) ^ (1 / 256 : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  have hlog : ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / 256 : ℝ) := by
    have hlittle :=
      ((isLittleO_log_rpow_atTop
          (by norm_num : (0 : ℝ) < 1 / 256)).comp_tendsto
        tendsto_natCast_atTop_atTop).eventuallyLE
    filter_upwards [hlittle, eventually_ge_atTop 1] with N hNlog hN
    have hlog0 : 0 ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hN)
    simp only [Function.comp_apply] at hNlog
    rw [Real.norm_of_nonneg hlog0,
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)] at hNlog
    exact hNlog
  filter_upwards [hpow32, hpow64, hpowScale, hpow256, hlog,
      eventually_ge_atTop 1] with N h32 h64 hScale h256 hlogN hN a haLower haUpper
  let H := secondDerivativeShiftCount N
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNR
  have hHpos : 0 < H := by
    exact Erdos1149.AnalyticParameters.natFloor_pos h32
  have hHupper : (H : ℝ) ≤ (N : ℝ) ^ (1 / 32 : ℝ) := by
    exact Erdos1149.AnalyticParameters.natFloor_le (Real.rpow_nonneg hNpos.le _)
  have hHlower : (N : ℝ) ^ (1 / 64 : ℝ) ≤ H := by
    have hfloor := Erdos1149.AnalyticParameters.half_le_natFloor h32
    have hsq : (N : ℝ) ^ (1 / 32 : ℝ) =
        ((N : ℝ) ^ (1 / 64 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
      norm_num
    have hroot0 : 0 ≤ (N : ℝ) ^ (1 / 64 : ℝ) :=
      Real.rpow_nonneg hNpos.le _
    dsimp only [H, secondDerivativeShiftCount]
    calc
      (N : ℝ) ^ (1 / 64 : ℝ) ≤
          ((N : ℝ) ^ (1 / 64 : ℝ)) ^ 2 / 2 := by nlinarith
      _ = (N : ℝ) ^ (1 / 32 : ℝ) / 2 := by rw [hsq]
      _ ≤ (⌊(N : ℝ) ^ (1 / 32 : ℝ)⌋₊ : ℝ) := hfloor
  have hHNreal : (H : ℝ) ≤ N := by
    calc
      (H : ℝ) ≤ (N : ℝ) ^ (1 / 32 : ℝ) := hHupper
      _ ≤ (N : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hNR (by norm_num)
      _ = N := by simp
  have hHN : H ≤ N := by exact_mod_cast hHNreal
  have ha : 0 < a := hNpos.trans_le haLower
  have haUpperTwo : a ≤ (N : ℝ) ^ 2 := by
    calc
      a ≤ (N : ℝ) ^ (15 / 8 : ℝ) := haUpper
      _ ≤ (N : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hNR (by norm_num)
      _ = (N : ℝ) ^ 2 := Real.rpow_natCast _ _
  have hscale : 8 * (H : ℝ) * a ≤ (N : ℝ) ^ 2 := by
    calc
      8 * (H : ℝ) * a ≤
          8 * ((N : ℝ) ^ (1 / 32 : ℝ) *
            (N : ℝ) ^ (15 / 8 : ℝ)) := by
        rw [mul_assoc]
        gcongr
      _ ≤ (N : ℝ) ^ (3 / 32 : ℝ) *
          ((N : ℝ) ^ (1 / 32 : ℝ) *
            (N : ℝ) ^ (15 / 8 : ℝ)) :=
        mul_le_mul_of_nonneg_right hScale (by positivity)
      _ = (N : ℝ) ^ 2 := by
        rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
        norm_num
  have hlogH : Real.log (H : ℝ) ≤ (N : ℝ) ^ (1 / 256 : ℝ) := by
    calc
      Real.log (H : ℝ) ≤ Real.log (N : ℝ) :=
        Real.log_le_log (by exact_mod_cast hHpos) hHNreal
      _ ≤ (N : ℝ) ^ (1 / 256 : ℝ) := hlogN
  have hsq := norm_logBlock_sq_le_div hHpos hHN ha haLower haUpperTwo hscale
  have hcoarse :
      ‖∑ n ∈ range N, blockPhase a N n‖ ^ 2 ≤
        74 * (N : ℝ) ^ (2 - 3 / 256 : ℝ) := by
    calc
      ‖∑ n ∈ range N, blockPhase a N n‖ ^ 2 ≤
          2 * (N : ℝ) ^ 2 * (19 + 18 * Real.log (H : ℝ)) / H := hsq
      _ ≤ 2 * (N : ℝ) ^ 2 *
          (37 * (N : ℝ) ^ (1 / 256 : ℝ)) /
            ((N : ℝ) ^ (1 / 64 : ℝ)) := by
        apply div_le_div₀ (by positivity)
        · gcongr
          nlinarith
        · exact Real.rpow_pos_of_pos hNpos _
        · exact hHlower
      _ = 74 * (N : ℝ) ^ (2 - 3 / 256 : ℝ) := by
        have hden : (N : ℝ) ^ (1 / 64 : ℝ) =
            (N : ℝ) ^ (1 / 256 : ℝ) *
              (N : ℝ) ^ (3 / 256 : ℝ) := by
          rw [← Real.rpow_add hNpos]
          norm_num
        rw [Real.rpow_sub hNpos, Real.rpow_two, hden]
        field_simp <;> ring_nf <;> rfl
  have hexponent :
      (N : ℝ) ^ (2 - 3 / 256 : ℝ) ≤
        (N : ℝ) ^ (2 - 1 / 512 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hNR (by norm_num)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    ‖∑ n ∈ range N, blockPhase a N n‖ ^ 2 ≤
        74 * (N : ℝ) ^ (2 - 3 / 256 : ℝ) := hcoarse
    _ ≤ 81 * (N : ℝ) ^ (2 - 1 / 512 : ℝ) := by
      calc
        74 * (N : ℝ) ^ (2 - 3 / 256 : ℝ) ≤
            74 * (N : ℝ) ^ (2 - 1 / 512 : ℝ) := by gcongr
        _ ≤ 81 * (N : ℝ) ^ (2 - 1 / 512 : ℝ) := by gcongr <;> norm_num
    _ = (9 * (N : ℝ) ^ (1 - 1 / 1024 : ℝ)) ^ 2 := by
      have hrpowSq : ((N : ℝ) ^ (1 - 1 / 1024 : ℝ)) ^ 2 =
          (N : ℝ) ^ (2 - 1 / 512 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
        norm_num
      rw [mul_pow, hrpowSq]
      norm_num

/-- Threshold form of `eventually_norm_logBlock_le_rpow`, convenient for
downstream finite band decompositions. -/
theorem exists_secondDerivative_threshold :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ a : ℝ,
      (N : ℝ) ≤ a → a ≤ (N : ℝ) ^ (15 / 8 : ℝ) →
      ‖∑ n ∈ range N, blockPhase a N n‖ ≤
        9 * (N : ℝ) ^ (1 - 1 / 1024 : ℝ) := by
  simpa only [eventually_atTop] using eventually_norm_logBlock_le_rpow

/-- Uniform prefix form of the second-derivative saving.  Both the real start
and the prefix length are quantified after the scale, as required for residue
class decompositions. -/
theorem eventually_norm_realStartBlock_le_rpow :
    ∀ᶠ X : ℕ in atTop, ∀ P : ℕ, P ≤ X → ∀ a U : ℝ,
      (X : ℝ) ≤ U → U ≤ 2 * X →
      (X : ℝ) ≤ a → a ≤ (X : ℝ) ^ (15 / 8 : ℝ) →
      ‖∑ n ∈ range P, realStartBlockPhase a U n‖ ≤
        18 * (X : ℝ) ^ (1 - 1 / 1024 : ℝ) := by
  have hpow32 : ∀ᶠ X : ℕ in atTop,
      (2 : ℝ) ≤ (X : ℝ) ^ (1 / 32 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 32)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  have hpow64 : ∀ᶠ X : ℕ in atTop,
      (2 : ℝ) ≤ (X : ℝ) ^ (1 / 64 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 64)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  have hpowScale : ∀ᶠ X : ℕ in atTop,
      (8 : ℝ) ≤ (X : ℝ) ^ (3 / 32 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 32)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 8)
  have hpow256 : ∀ᶠ X : ℕ in atTop,
      (1 : ℝ) ≤ (X : ℝ) ^ (1 / 256 : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with X hX
    exact Real.one_le_rpow (by exact_mod_cast hX) (by norm_num)
  have hlog : ∀ᶠ X : ℕ in atTop,
      Real.log (X : ℝ) ≤ (X : ℝ) ^ (1 / 256 : ℝ) := by
    have hlittle :=
      ((isLittleO_log_rpow_atTop
          (by norm_num : (0 : ℝ) < 1 / 256)).comp_tendsto
        tendsto_natCast_atTop_atTop).eventuallyLE
    filter_upwards [hlittle, eventually_ge_atTop 1] with X hXlog hX
    have hlog0 : 0 ≤ Real.log (X : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hX)
    simp only [Function.comp_apply] at hXlog
    rw [Real.norm_of_nonneg hlog0,
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg X) _)] at hXlog
    exact hXlog
  filter_upwards [hpow32, hpow64, hpowScale, hpow256, hlog,
      eventually_ge_atTop 1] with X h32 h64 hScale h256 hlogX hX
      P hPX a U hXU hUX haLower haUpper
  let H := secondDerivativeShiftCount X
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < X := zero_lt_one.trans_le hXR
  have hUpos : 0 < U := hXpos.trans_le hXU
  have hHpos : 0 < H :=
    Erdos1149.AnalyticParameters.natFloor_pos h32
  have hHupper : (H : ℝ) ≤ (X : ℝ) ^ (1 / 32 : ℝ) :=
    Erdos1149.AnalyticParameters.natFloor_le (Real.rpow_nonneg hXpos.le _)
  have hHlower : (X : ℝ) ^ (1 / 64 : ℝ) ≤ H := by
    have hfloor := Erdos1149.AnalyticParameters.half_le_natFloor h32
    have hsq : (X : ℝ) ^ (1 / 32 : ℝ) =
        ((X : ℝ) ^ (1 / 64 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le]
      norm_num
    have hroot0 : 0 ≤ (X : ℝ) ^ (1 / 64 : ℝ) :=
      Real.rpow_nonneg hXpos.le _
    dsimp only [H, secondDerivativeShiftCount]
    calc
      (X : ℝ) ^ (1 / 64 : ℝ) ≤
          ((X : ℝ) ^ (1 / 64 : ℝ)) ^ 2 / 2 := by nlinarith
      _ = (X : ℝ) ^ (1 / 32 : ℝ) / 2 := by rw [hsq]
      _ ≤ (⌊(X : ℝ) ^ (1 / 32 : ℝ)⌋₊ : ℝ) := hfloor
  have hHXreal : (H : ℝ) ≤ X := by
    calc
      (H : ℝ) ≤ (X : ℝ) ^ (1 / 32 : ℝ) := hHupper
      _ ≤ (X : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hXR (by norm_num)
      _ = X := by simp
  have hHX : H ≤ X := by exact_mod_cast hHXreal
  by_cases hsmall : P < H
  · have hsum : ‖∑ n ∈ range P, realStartBlockPhase a U n‖ ≤ P := by
      calc
        ‖∑ n ∈ range P, realStartBlockPhase a U n‖ ≤
            ∑ n ∈ range P, ‖realStartBlockPhase a U n‖ := norm_sum_le _ _
        _ = P := by simp
    have hPpow : (P : ℝ) ≤ (X : ℝ) ^ (1 / 32 : ℝ) :=
      (by exact_mod_cast hsmall.le : (P : ℝ) ≤ H) |>.trans hHupper
    have hexp : (X : ℝ) ^ (1 / 32 : ℝ) ≤
        (X : ℝ) ^ (1 - 1 / 1024 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hXR (by norm_num)
    calc
      ‖∑ n ∈ range P, realStartBlockPhase a U n‖ ≤ P := hsum
      _ ≤ (X : ℝ) ^ (1 / 32 : ℝ) := hPpow
      _ ≤ (X : ℝ) ^ (1 - 1 / 1024 : ℝ) := hexp
      _ ≤ 18 * (X : ℝ) ^ (1 - 1 / 1024 : ℝ) := by
        have := Real.rpow_nonneg hXpos.le (1 - 1 / 1024 : ℝ)
        nlinarith
  · have hHP : H ≤ P := by omega
    have ha : 0 < a := hXpos.trans_le haLower
    have hscaleX : 8 * (H : ℝ) * a ≤ (X : ℝ) ^ 2 := by
      calc
        8 * (H : ℝ) * a ≤
            8 * ((X : ℝ) ^ (1 / 32 : ℝ) *
              (X : ℝ) ^ (15 / 8 : ℝ)) := by
          rw [mul_assoc]
          gcongr
        _ ≤ (X : ℝ) ^ (3 / 32 : ℝ) *
            ((X : ℝ) ^ (1 / 32 : ℝ) *
              (X : ℝ) ^ (15 / 8 : ℝ)) :=
          mul_le_mul_of_nonneg_right hScale (by positivity)
        _ = (X : ℝ) ^ 2 := by
          rw [← Real.rpow_add hXpos, ← Real.rpow_add hXpos]
          norm_num
    have hscale : 8 * (H : ℝ) * a ≤ U ^ 2 := by
      exact hscaleX.trans (sq_le_sq₀ hXpos.le hUpos.le |>.2 hXU)
    have hlogH : Real.log (H : ℝ) ≤ (X : ℝ) ^ (1 / 256 : ℝ) := by
      calc
        Real.log (H : ℝ) ≤ Real.log (X : ℝ) :=
          Real.log_le_log (by exact_mod_cast hHpos) hHXreal
        _ ≤ (X : ℝ) ^ (1 / 256 : ℝ) := hlogX
    have hsq := norm_realStartBlock_sq_le_div
      hHpos hHP hPX ha haLower hXU hUX hscale
    have hcoarse :
        ‖∑ n ∈ range P, realStartBlockPhase a U n‖ ^ 2 ≤
          290 * (X : ℝ) ^ (2 - 3 / 256 : ℝ) := by
      calc
        ‖∑ n ∈ range P, realStartBlockPhase a U n‖ ^ 2 ≤
            2 * (X : ℝ) ^ 2 * (73 + 72 * Real.log (H : ℝ)) / H := hsq
        _ ≤ 2 * (X : ℝ) ^ 2 *
            (145 * (X : ℝ) ^ (1 / 256 : ℝ)) /
              ((X : ℝ) ^ (1 / 64 : ℝ)) := by
          apply div_le_div₀ (by positivity)
          · gcongr
            nlinarith
          · exact Real.rpow_pos_of_pos hXpos _
          · exact hHlower
        _ = 290 * (X : ℝ) ^ (2 - 3 / 256 : ℝ) := by
          have hden : (X : ℝ) ^ (1 / 64 : ℝ) =
              (X : ℝ) ^ (1 / 256 : ℝ) *
                (X : ℝ) ^ (3 / 256 : ℝ) := by
            rw [← Real.rpow_add hXpos]
            norm_num
          rw [Real.rpow_sub hXpos, Real.rpow_two, hden]
          field_simp <;> ring_nf
    have hexponent : (X : ℝ) ^ (2 - 3 / 256 : ℝ) ≤
        (X : ℝ) ^ (2 - 1 / 512 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hXR (by norm_num)
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    calc
      ‖∑ n ∈ range P, realStartBlockPhase a U n‖ ^ 2 ≤
          290 * (X : ℝ) ^ (2 - 3 / 256 : ℝ) := hcoarse
      _ ≤ 324 * (X : ℝ) ^ (2 - 1 / 512 : ℝ) := by
        calc
          290 * (X : ℝ) ^ (2 - 3 / 256 : ℝ) ≤
              290 * (X : ℝ) ^ (2 - 1 / 512 : ℝ) := by gcongr
          _ ≤ 324 * (X : ℝ) ^ (2 - 1 / 512 : ℝ) := by gcongr <;> norm_num
      _ = (18 * (X : ℝ) ^ (1 - 1 / 1024 : ℝ)) ^ 2 := by
        have hrpowSq : ((X : ℝ) ^ (1 - 1 / 1024 : ℝ)) ^ 2 =
            (X : ℝ) ^ (2 - 1 / 512 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le]
          norm_num
        rw [mul_pow, hrpowSq]
        norm_num

/-- Threshold form of the uniform arbitrary-prefix second-derivative
estimate. -/
theorem exists_realStartSecondDerivative_threshold :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℕ, P ≤ X → ∀ a U : ℝ,
      (X : ℝ) ≤ U → U ≤ 2 * X →
      (X : ℝ) ≤ a → a ≤ (X : ℝ) ^ (15 / 8 : ℝ) →
      ‖∑ n ∈ range P, realStartBlockPhase a U n‖ ≤
        18 * (X : ℝ) ^ (1 - 1 / 1024 : ℝ) := by
  simpa only [eventually_atTop] using eventually_norm_realStartBlock_le_rpow

end

end Erdos67.LogSecondDerivative
