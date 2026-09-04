import ErdosProblems.Erdos67.UniformResidueLogPhase
import ErdosProblems.Erdos67.DyadicGeometric
import ErdosProblems.Erdos67.LSeriesLowCutoff
import ErdosProblems.Erdos67.LSeriesHighSegment
import ErdosProblems.Erdos67.LSeriesHeightTail
import ErdosProblems.Erdos67.LSeriesFiniteDecomposition
import ErdosProblems.Erdos67.LSeriesSublinearGeometry
import ErdosProblems.Erdos67.ResidueFixedDepthEpsilon
import ErdosProblems.Erdos67.TwistSeparationLFunction
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Bounded-conductor sublinear bounds for high Dirichlet L-series

This is the global fixed-depth assembly.  A small initial segment is paid
for harmonically, the middle range is split into dyadic blocks and estimated
by the uniform residue-class cancellation theorem, the remaining
bounded-ratio high segment is absolute, and the infinite tail is controlled
by the height-tail estimate.
-/

open scoped BigOperators LSeries.notation
open Filter

namespace Erdos67.LSeriesSublinear

noncomputable section

open Erdos67.LogPhaseSum
open Erdos67.LSeriesLogPhaseBridge
open Erdos67.LSeriesLowCutoff
open Erdos67.LSeriesHighSegment
open Erdos67.LSeriesHeightTail
open Erdos67.LSeriesFiniteDecomposition
open Erdos67.LSeriesSublinearGeometry
open Erdos67.ResidueFixedDepthEpsilon
open Erdos67.ResidueLogPhase
open Erdos67.UniformResidueLogPhase
open Erdos67.DyadicGeometric

/-- A scaled low cutoff.  The conductor-square factor makes every residue
comparison scale beyond this point at least the root cutoff. -/
def boundedConductorLowCutoff (Q : ℕ) (T : ℝ) (R : ℕ) : ℕ :=
  Q ^ 2 * heightRootCutoff T R

/-- The end of the cancellation range; the rest up to `ceil T` has bounded
multiplicative length. -/
def cancellationCutoff (T : ℝ) : ℕ :=
  ⌊T / 16⌋₊

/-- One dyadic L-series block, reduced to the already uniform raw residue
prefix estimate. -/
theorem norm_sum_Ioc_character_LSeries_term_le_of_uniformResidue
    {q R S X B : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {t sigma η : ℝ}
    (hη : 0 < η) (hsigma : 1 ≤ sigma)
    (hX : 0 < X) (hXB : X < B) (hB : B ≤ 2 * X)
    (hS : q * S ≤ X + 1)
    (hUa : (X + 2 : ℕ) ≤ positiveLogCoefficient t)
    (hupper : positiveLogCoefficient t < (S : ℝ) ^ (R + 1))
    (hresidue : ∀ {A M : ℕ} (c : ZMod q),
      0 < A → M ≤ 2 * A →
      S ≤ firstResidueAtOrAbove A c / q →
      (firstResidueAtOrAbove A c : ℝ) / q ≤
        positiveLogCoefficient t →
      positiveLogCoefficient t <
        ((firstResidueAtOrAbove A c / q : ℕ) : ℝ) ^ (R + 1) →
      ‖residueClassSum (Finset.Icc A M) c
          (fun n ↦ natLogTwist n t)‖ ≤
        η * (firstResidueAtOrAbove A c / q : ℕ)) :
    ‖∑ n ∈ Finset.Ioc X B,
        LSeries.term (fun m : ℕ ↦ chi m)
          ((sigma : ℂ) + Complex.I * (t : ℂ)) n‖ ≤
      q * η := by
  let A := X + 1
  have hA : 0 < A := by omega
  have hIoc : Finset.Ioc X B = Finset.Icc A B := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc, A]
    omega
  rw [hIoc]
  have hres : ∀ n ∈ Finset.Icc A B, ∀ c : ZMod q,
      ‖residueClassSum (Finset.Icc A n) c
          (fun m ↦ natLogTwist m t)‖ ≤ η * A := by
    intro n hn c
    have hnB : n ≤ 2 * A := by
      have hnB' := (Finset.mem_Icc.mp hn).2.trans hB
      dsimp only [A]
      omega
    have hScomp : S ≤ firstResidueAtOrAbove A c / q :=
      comparisonScale_ge_of_mul_le c (by simpa only [A] using hS)
    have hcompA : firstResidueAtOrAbove A c / q ≤ A :=
      comparisonScale_le_leftEndpoint c
    have hUcomp : (firstResidueAtOrAbove A c : ℝ) / q <
        (firstResidueAtOrAbove A c / q : ℕ) + 1 := by
      have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
      have hnat : firstResidueAtOrAbove A c <
          q * (firstResidueAtOrAbove A c / q + 1) := by
        simpa only [mul_comm] using
          Nat.lt_mul_div_succ (firstResidueAtOrAbove A c) hq
      apply (div_lt_iff₀ (by exact_mod_cast hq : (0 : ℝ) < q)).2
      push_cast
      exact_mod_cast (by simpa only [mul_comm] using hnat)
    have hUheight : (firstResidueAtOrAbove A c : ℝ) / q ≤
        positiveLogCoefficient t := by
      have hAc : ((firstResidueAtOrAbove A c / q : ℕ) : ℝ) ≤ A := by
        exact_mod_cast hcompA
      have hAheight : (A : ℝ) + 1 ≤ positiveLogCoefficient t := by
        dsimp only [A]
        norm_num at hUa ⊢
        linarith
      linarith
    have hpowMono : (S : ℝ) ^ (R + 1) ≤
        ((firstResidueAtOrAbove A c / q : ℕ) : ℝ) ^ (R + 1) := by
      exact pow_le_pow_left₀ (Nat.cast_nonneg S) (by exact_mod_cast hScomp) _
    have hraw := hresidue c hA hnB hScomp hUheight
      (hupper.trans_le hpowMono)
    calc
      ‖residueClassSum (Finset.Icc A n) c
          (fun m ↦ natLogTwist m t)‖ ≤
          η * (firstResidueAtOrAbove A c / q : ℕ) := hraw
      _ ≤ η * A := by
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcompA) hη.le
  have hweighted :=
    norm_sum_character_LSeries_term_le_of_residue_prefix_bounds
      chi t hA (by omega : A ≤ B) (by linarith : 0 ≤ sigma)
      (mul_nonneg hη.le (Nat.cast_nonneg A)) hres
  have hAone : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hpow : (A : ℝ) ^ (-sigma) ≤ (A : ℝ) ^ (-1 : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_le hAone (by linarith)
  calc
    ‖∑ n ∈ Finset.Icc A B,
        LSeries.term (fun m : ℕ ↦ chi m)
          ((sigma : ℂ) + Complex.I * (t : ℂ)) n‖ ≤
        (q * (η * A)) * (A : ℝ) ^ (-sigma) := hweighted
    _ ≤ (q * (η * A)) * (A : ℝ) ^ (-1 : ℝ) := by
      gcongr
    _ = q * η := by
      rw [Real.rpow_neg_one]
      field_simp

/-- The height-independent part of the four-piece L-series estimate. -/
def sublinearConstant (Q : ℕ) (e : ℝ) : ℝ :=
  2 + 2 * Real.log Q + Real.log 2 + e * Real.log 2 / 8 +
    Real.log 64 + 5 * Q ^ 2

/-- The global estimate once the cutoff geometry and logarithmic absorption
inequality have been supplied.  This is kept separate from the eventual
threshold selection so all rounding-sensitive analytic bookkeeping is
visible in one finite statement. -/
theorem norm_character_LSeries_le_of_height_data
    {Q R S₀ N : ℕ} (hQ : 0 < Q) (hR : 2 ≤ R)
    {e : ℝ} (he : 0 < e) (heOne : e ≤ 1)
    (hRlarge : (8 : ℝ) ≤ e * R)
    (hresidue : ∀ {q A M : ℕ} [NeZero q] (c : ZMod q) {t : ℝ},
      0 < A → M ≤ 2 * A → t ≠ 0 →
      S₀ ≤ firstResidueAtOrAbove A c / q →
      (firstResidueAtOrAbove A c : ℝ) / q ≤ positiveLogCoefficient t →
      positiveLogCoefficient t <
        ((firstResidueAtOrAbove A c / q : ℕ) : ℝ) ^ (R + 1) →
      ‖residueClassSum (Finset.Icc A M) c
          (fun n ↦ natLogTwist n t)‖ ≤
        (e * Real.log 2 / (16 * (Q : ℝ) ^ 2)) *
          (firstResidueAtOrAbove A c / q : ℕ))
    (hN : 0 < N) (hNQ : N ≤ Q ^ 2)
    (chi : DirichletCharacter ℂ N) {sigma v : ℝ}
    (hsigma : 1 < sigma) (hsigma2 : sigma ≤ 2)
    (hTthree : (3 : ℝ) ≤ |v|)
    (hheight :
      let T : ℝ := |v|
      let S : ℕ := heightRootCutoff T R
      let M : ℕ := Q ^ 2 * S
      let K : ℕ := cancellationCutoff T
      let H : ℕ := Nat.ceil T
      0 < M ∧ M ≤ K ∧ K < H ∧ S₀ ≤ S ∧
        H - 1 ≤ 64 * (K + 1) ∧
        ((K + 2 : ℕ) : ℝ) ≤ positiveLogCoefficient v ∧
        positiveLogCoefficient v < (S : ℝ) ^ (R + 1))
    (habsorb : sublinearConstant Q e ≤ e * Real.log |v| / 2) :
    ‖L ↗chi ((sigma : ℝ) + Complex.I * (v : ℂ))‖ ≤
      e * Real.log |v| := by
  let T : ℝ := |v|
  let S : ℕ := heightRootCutoff T R
  let M : ℕ := boundedConductorLowCutoff Q T R
  let K : ℕ := cancellationCutoff T
  let H : ℕ := Nat.ceil T
  let eta : ℝ := e * Real.log 2 / (16 * (Q : ℝ) ^ 2)
  have hMdef : M = Q ^ 2 * S := rfl
  change 0 < M ∧ M ≤ K ∧ K < H ∧ S₀ ≤ S ∧
    H - 1 ≤ 64 * (K + 1) ∧
    ((K + 2 : ℕ) : ℝ) ≤ positiveLogCoefficient v ∧
    positiveLogCoefficient v < (S : ℝ) ^ (R + 1) at hheight
  obtain ⟨hMpos, hMK, hKH, hS₀S, hHratio, hKcoeff, hcoeffUpper⟩ := hheight
  let : NeZero N := ⟨hN.ne'⟩
  have hHpos : 0 < H := by omega
  have hTthree' : (3 : ℝ) ≤ T := by simpa only [T] using hTthree
  have hTpos : 0 < T := by linarith
  have hTone : 1 ≤ T := by linarith
  have hvne : v ≠ 0 := abs_pos.mp hTpos
  have hSpos : 0 < S := by
    dsimp only [S]
    exact heightRootCutoff_pos hTpos R
  have hRpos : 0 < R := by omega
  have heta : 0 < eta := by
    dsimp only [eta]
    positivity
  let f : ℕ → ℂ := fun n ↦
    LSeries.term (fun m : ℕ ↦ chi m)
      ((sigma : ℂ) + Complex.I * (v : ℂ)) n
  have hlowRaw : ‖∑ n ∈ Finset.Icc 1 M, f n‖ ≤ 1 + Real.log M := by
    simpa only [f] using
      norm_sum_Icc_character_LSeries_term_le_one_add_log chi v sigma M hsigma.le
  have hlogS : Real.log S ≤ Real.log 2 + Real.log T / R :=
    log_heightRootCutoff_le hTone hRpos
  have hlogM : Real.log M = 2 * Real.log Q + Real.log S := by
    rw [hMdef, Nat.cast_mul, Real.log_mul]
    · rw [Nat.cast_pow, Real.log_pow]
      norm_num
    · exact_mod_cast (pow_ne_zero 2 hQ.ne')
    · exact_mod_cast hSpos.ne'
  have hRinv : (1 : ℝ) / R ≤ e / 8 := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < R) (by norm_num : (0 : ℝ) < 8)]
    simpa [mul_comm] using hRlarge
  have hlogTnonneg : 0 ≤ Real.log T := Real.log_nonneg hTone
  have hlow : ‖∑ n ∈ Finset.Icc 1 M, f n‖ ≤
      1 + 2 * Real.log Q + Real.log 2 + e * Real.log T / 8 := by
    calc
      ‖∑ n ∈ Finset.Icc 1 M, f n‖ ≤ 1 + Real.log M := hlowRaw
      _ = 1 + 2 * Real.log Q + Real.log S := by rw [hlogM]; ring
      _ ≤ 1 + 2 * Real.log Q +
          (Real.log 2 + Real.log T / R) := by linarith
      _ ≤ 1 + 2 * Real.log Q + Real.log 2 + e * Real.log T / 8 := by
        have hm := mul_le_mul_of_nonneg_right hRinv hlogTnonneg
        have hm' : Real.log T / R ≤ e * Real.log T / 8 := by
          calc
            Real.log T / R = ((R : ℝ)⁻¹) * Real.log T := by ring
            _ ≤ (e / 8) * Real.log T := by simpa only [one_div] using hm
            _ = e * Real.log T / 8 := by ring
        linarith
  have hmiddleRaw : ‖∑ n ∈ Finset.Ioc M K, f n‖ ≤
      ((Nat.log 2 K - Nat.log 2 M + 1 : ℕ) : ℝ) *
        ((Q ^ 2 : ℕ) * eta) := by
    apply norm_sum_Ioc_le_log_mul_of_dyadic_bound_on f hMpos
      (mul_nonneg (Nat.cast_nonneg _) heta.le)
    intro X Y hMX hYK hX hXY hYtwo
    have hNS : N * S ≤ X + 1 := by
      have : N * S ≤ Q ^ 2 * S := Nat.mul_le_mul_right S hNQ
      rw [hMdef] at hMX
      omega
    have hXcoeff : ((X + 2 : ℕ) : ℝ) ≤ positiveLogCoefficient v := by
      apply le_trans _ hKcoeff
      exact_mod_cast (by omega : X + 2 ≤ K + 2)
    have hblock := norm_sum_Ioc_character_LSeries_term_le_of_uniformResidue
      chi heta hsigma.le hX hXY hYtwo hNS hXcoeff hcoeffUpper
      (fun c hA hAM hScomp hUa hupper ↦
        hresidue c hA hAM hvne (hS₀S.trans hScomp) hUa hupper)
    calc
      ‖∑ n ∈ Finset.Ioc X Y, f n‖ ≤ N * eta := by
        simpa only [f] using hblock
      _ ≤ (Q ^ 2 : ℕ) * eta := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hNQ) heta.le
  have hHreal : (H : ℝ) ≤ 2 * T := by
    dsimp only [H]
    exact Erdos1149.AnalyticParameters.natCeil_le_two_mul hTone
  have hlogH : Real.log H ≤ Real.log 2 + Real.log T := by
    calc
      Real.log H ≤ Real.log (2 * T) :=
        Real.strictMonoOn_log.monotoneOn
          (show (0 : ℝ) < H by exact_mod_cast hHpos)
          (show (0 : ℝ) < 2 * T by positivity) hHreal
      _ = Real.log 2 + Real.log T := by rw [Real.log_mul] <;> positivity
  have hKpos : 0 < K := hMpos.trans_le hMK
  have hlogK : (Nat.log 2 K : ℝ) ≤ Real.log K / Real.log 2 :=
    natLog_two_le_realLog_div hKpos
  have hlogKT : Real.log K ≤ Real.log T := by
    have hKT : (K : ℝ) ≤ T := by
      have hfloor : (K : ℝ) ≤ T / 16 := by
        dsimp only [K, cancellationCutoff]
        exact Nat.floor_le (by positivity)
      linarith
    exact Real.strictMonoOn_log.monotoneOn
      (show (0 : ℝ) < K by exact_mod_cast hKpos) hTpos hKT
  have hcount : ((Nat.log 2 K - Nat.log 2 M + 1 : ℕ) : ℝ) ≤
      Real.log T / Real.log 2 + 1 := by
    have hn : Nat.log 2 K - Nat.log 2 M + 1 ≤ Nat.log 2 K + 1 := by omega
    have hnR : ((Nat.log 2 K - Nat.log 2 M + 1 : ℕ) : ℝ) ≤
        (Nat.log 2 K : ℝ) + 1 := by exact_mod_cast hn
    have hdiv : Real.log K / Real.log 2 ≤ Real.log T / Real.log 2 :=
      div_le_div_of_nonneg_right hlogKT
        (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    linarith
  have hQeta : ((Q ^ 2 : ℕ) : ℝ) * eta = e * Real.log 2 / 16 := by
    dsimp only [eta]
    push_cast
    field_simp [hQ.ne']
  have hmiddle : ‖∑ n ∈ Finset.Ioc M K, f n‖ ≤
      e * Real.log T / 16 + e * Real.log 2 / 16 := by
    have hqetaNonneg : 0 ≤ ((Q ^ 2 : ℕ) : ℝ) * eta := by positivity
    calc
      ‖∑ n ∈ Finset.Ioc M K, f n‖ ≤
          ((Nat.log 2 K - Nat.log 2 M + 1 : ℕ) : ℝ) *
            ((Q ^ 2 : ℕ) * eta) := hmiddleRaw
      _ ≤ (Real.log T / Real.log 2 + 1) *
            ((Q ^ 2 : ℕ) * eta) :=
        mul_le_mul_of_nonneg_right hcount hqetaNonneg
      _ = e * Real.log T / 16 + e * Real.log 2 / 16 := by
        rw [hQeta]
        field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  have hhigh : ‖∑ n ∈ Finset.Ioc K (H - 1), f n‖ ≤
      1 + Real.log 64 := by
    simpa only [f, Nat.cast_ofNat] using
      norm_sum_Ioc_character_LSeries_term_le_one_add_log chi v sigma
        (show K ≤ H - 1 by omega) (by norm_num : 0 < (64 : ℕ))
        (show 0 < H - 1 by omega) hHratio hsigma.le
  have hdecomp : (∑ n ∈ Finset.range H, f n) =
      (∑ n ∈ Finset.Icc 1 M, f n) +
        (∑ n ∈ Finset.Ioc M K, f n) +
          ∑ n ∈ Finset.Ioc K (H - 1), f n :=
    sum_range_eq_low_add_middle_add_high f (by simp [f]) hMpos hMK hKH
  have hfinite : ‖∑ n ∈ Finset.range H, f n‖ ≤
      (1 + 2 * Real.log Q + Real.log 2 + e * Real.log T / 8) +
        (e * Real.log T / 16 + e * Real.log 2 / 16) +
          (1 + Real.log 64) := by
    rw [hdecomp]
    exact (norm_add_le _ _).trans <| add_le_add
      ((norm_add_le _ _).trans (add_le_add hlow hmiddle)) hhigh
  have htail : ‖L ↗chi ((sigma : ℝ) + Complex.I * (v : ℂ)) -
      ∑ n ∈ Finset.range H, f n‖ ≤ 5 * N := by
    simpa only [H, T, f] using
      norm_character_LSeries_height_tail_le chi hsigma hsigma2
        (by simpa only [T] using hTthree')
  have htailQ : (5 : ℝ) * N ≤ 5 * Q ^ 2 := by
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hNQ) (by norm_num)
  calc
    ‖L ↗chi ((sigma : ℝ) + Complex.I * (v : ℂ))‖ =
        ‖(L ↗chi ((sigma : ℝ) + Complex.I * (v : ℂ)) -
            ∑ n ∈ Finset.range H, f n) +
          ∑ n ∈ Finset.range H, f n‖ := by congr 1; ring
    _ ≤ ‖L ↗chi ((sigma : ℝ) + Complex.I * (v : ℂ)) -
            ∑ n ∈ Finset.range H, f n‖ +
          ‖∑ n ∈ Finset.range H, f n‖ := norm_add_le _ _
    _ ≤ 5 * Q ^ 2 +
        ((1 + 2 * Real.log Q + Real.log 2 + e * Real.log T / 8) +
          (e * Real.log T / 16 + e * Real.log 2 / 16) +
            (1 + Real.log 64)) := by linarith
    _ ≤ sublinearConstant Q e + 3 * e * Real.log T / 16 := by
      dsimp only [sublinearConstant]
      have heLog : e * Real.log 2 / 16 ≤ e * Real.log 2 / 8 := by
        nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
      linarith
    _ ≤ e * Real.log T := by
      have habsorb' : sublinearConstant Q e ≤ e * Real.log T / 2 := by
        simpa only [T] using habsorb
      nlinarith

/-- Uniformly for all Dirichlet characters of conductor at most `Q²`, their
L-functions on `1 < re s ≤ 2` are `o(log |im s|)`.  The depth is selected
after the requested error and before the character and height, exactly as
needed by the Section 4 twist-separation argument. -/
theorem boundedConductorLSeriesSublinear (Q : ℕ) :
    Erdos67.BoundedConductorLSeriesSublinear Q := by
  intro epsilon hepsilon
  by_cases hQzero : Q = 0
  · subst Q
    refine ⟨3, le_rfl, ?_⟩
    intro N hN hNQ
    omega
  have hQ : 0 < Q := Nat.pos_of_ne_zero hQzero
  let e : ℝ := min epsilon 1
  have he : 0 < e := lt_min hepsilon zero_lt_one
  have heOne : e ≤ 1 := min_le_right epsilon 1
  have heEpsilon : e ≤ epsilon := min_le_left epsilon 1
  obtain ⟨Rbase : ℕ, hRbase⟩ := exists_nat_ge (8 / e)
  let R : ℕ := max 2 Rbase
  have hR : 2 ≤ R := Nat.le_max_left 2 Rbase
  have hRbaseR : Rbase ≤ R := Nat.le_max_right 2 Rbase
  have hRlarge : (8 : ℝ) ≤ e * R := by
    have hdiv : (8 : ℝ) / e ≤ R := hRbase.trans (by exact_mod_cast hRbaseR)
    have := (div_le_iff₀ he).1 hdiv
    nlinarith
  let eta : ℝ := e * Real.log 2 / (16 * (Q : ℝ) ^ 2)
  have heta : 0 < eta := by
    dsimp only [eta]
    positivity
  obtain ⟨S₀, hresidue⟩ :=
    exists_residuePrefix_mul_comparison_threshold R hR heta
  obtain ⟨Vgeo, hVgeoThree, hgeometry⟩ :=
    exists_cutoffGeometry_threshold Q R S₀ hQ hR
  have habsorbEventually : ∀ᶠ T : ℝ in atTop,
      2 * sublinearConstant Q e / e ≤ Real.log T :=
    Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop (2 * sublinearConstant Q e / e))
  obtain ⟨Tabsorb, hTabsorb⟩ := eventually_atTop.1 habsorbEventually
  obtain ⟨Vabsorb : ℕ, hVabsorb⟩ := exists_nat_ge Tabsorb
  let V₀ : ℕ := max Vgeo Vabsorb
  have hV₀Three : 3 ≤ V₀ := hVgeoThree.trans (Nat.le_max_left _ _)
  refine ⟨V₀, hV₀Three, ?_⟩
  intro N hN hNQ chi sigma v hv hsigma hsigma2
  have hVgeoV₀ : Vgeo ≤ V₀ := Nat.le_max_left _ _
  have hVabsorbV₀ : Vabsorb ≤ V₀ := Nat.le_max_right _ _
  have hvgeo : (Vgeo : ℝ) ≤ |v| := by
    have hcast : (Vgeo : ℝ) ≤ V₀ := by exact_mod_cast hVgeoV₀
    exact hcast.trans hv
  have hvabsorb : (Vabsorb : ℝ) ≤ |v| := by
    have hcast : (Vabsorb : ℝ) ≤ V₀ := by exact_mod_cast hVabsorbV₀
    exact hcast.trans hv
  have hTthreshold : Tabsorb ≤ |v| :=
    hVabsorb.trans hvabsorb
  have hlogThreshold := hTabsorb |v| hTthreshold
  have habsorb : sublinearConstant Q e ≤ e * Real.log |v| / 2 := by
    have heNonzero : e ≠ 0 := he.ne'
    calc
      sublinearConstant Q e =
          e * (2 * sublinearConstant Q e / e) / 2 := by
        field_simp
      _ ≤ e * Real.log |v| / 2 := by gcongr
  have hthree : (3 : ℝ) ≤ |v| := by
    have hcast : (3 : ℝ) ≤ V₀ := by exact_mod_cast hV₀Three
    exact hcast.trans hv
  have hNQ' : N ≤ Q ^ 2 := by simpa only [pow_two] using hNQ
  have hbound := norm_character_LSeries_le_of_height_data
    hQ hR he heOne hRlarge
    (by
      intro q A M _ c t hA hM ht hscale hUa hupper
      exact hresidue c hA hM ht hscale hUa hupper)
    hN hNQ' chi hsigma hsigma2 hthree (hgeometry v hvgeo) habsorb
  calc
    ‖L ↗chi ((sigma : ℝ) + Complex.I * (v : ℂ))‖ ≤
        e * Real.log |v| := hbound
    _ ≤ epsilon * Real.log |v| := by
      exact mul_le_mul_of_nonneg_right heEpsilon
        (Real.log_nonneg (by linarith : (1 : ℝ) ≤ |v|))

/-- The uniform family of sublinear high-height bounds. -/
theorem all_boundedConductorLSeriesSublinear :
    ∀ Q : ℕ, Erdos67.BoundedConductorLSeriesSublinear Q :=
  boundedConductorLSeriesSublinear

/-- Unconditional bounded-character polynomial-height twist separation in
the exact eventual form consumed by Tao's Section 4 probability argument. -/
theorem eventuallyTwoScaleTwistSeparation_unconditional :
    Erdos67.EventuallyTwoScaleTwistSeparation :=
  Erdos67.eventuallyTwoScaleTwistSeparation_of_lseriesSublinear
    all_boundedConductorLSeriesSublinear

end

end Erdos67.LSeriesSublinear
