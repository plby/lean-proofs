import Util.MaynardTao.BFT.S1
import Util.MaynardTao.BFT.LargeS2MainLower
import Util.MaynardTao.BFT.KernelSelection
import Util.MaynardTao.BFT.ProgressionS2ErrorLimit

/-! # Positive sieve excess in a prescribed progression -/

namespace MaynardBFT.Sieve

open Filter Erdos6.Maynard BoundedGaps.Maynard

variable [P : Parameters] [T : ShiftTuple]

theorem tendsto_normalized_progressionS1 {q : ℕ} (hq : 0 < q) (v : ℕ → ℕ)
    {alpha : ℝ} (halpha : 0 < alpha) (halphaQuarter : alpha < 1 / 4) :
    Tendsto (fun N : ℕ =>
      sieveWeightSum N (progressionWeight largePowerTuple q alpha v largeTupleCandidate N) /
        tupleMaynardScale largePowerTuple alpha N) atTop
      (nhds (maynardI largeK largeCandidate / q)) := by
  have hmain := (tendsto_normalizedLargeTupleS1Main halpha).div_const (q : ℝ)
  have herr := tendsto_normalized_progressionS1Error_zero hq largePowerTuple
    halpha halphaQuarter v largeTupleCandidate (B := 1) (by norm_num)
    largeTupleCandidate_abs_le_one
  have hsum := hmain.add herr
  simpa only [add_zero] using hsum.congr' (by
    filter_upwards [eventually_progressionS1_eq_main_add_error largePowerTuple q alpha v
      largeTupleCandidate, eventually_progressionS1Main_eq hq largePowerTuple alpha
      largeTupleCandidate] with N hsplit hmainN
    rw [hsplit, hmainN]
    ring)

theorem eventually_progression_excess_pos {q : ℕ} (hq : 0 < q) (v : ℕ → ℕ)
    (hv : ∀ᶠ N : ℕ in atTop, ∀ h ∈ largePowerTuple,
      Nat.Coprime (v N + h) (progressionModulus q N))
    {rho : ℝ} (hrho : 0 ≤ rho) (hA : 1024 * rho ≤ largeA) :
    ∀ᶠ N : ℕ in atTop,
      0 < sieveExcess largePowerTuple N rho
        (progressionWeight largePowerTuple q (5 / 32) v largeTupleCandidate N) := by
  let I := maynardI largeK largeCandidate
  let J := (largeK : ℝ) * (1 / 8 : ℝ) * kernelMargin
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hgap : 0 < J / q - rho * (I / q) := by
    have hmargin := positive_sieve_margin hrho hA
    have hdiv := div_pos (sub_pos.mpr hmargin) hqR
    dsimp [I, J]
    simpa only [sub_div, mul_div_assoc] using hdiv
  have hS1 := tendsto_normalized_progressionS1 hq v
    (by norm_num : (0 : ℝ) < 5 / 32) (by norm_num : (5 : ℝ) / 32 < 1 / 4)
  have herr := tendsto_normalized_progressionS2Error_zero hq largePowerTuple
    largePowerTuple_nonempty v largeTupleCandidate 1 (by norm_num)
    largeTupleCandidate_abs_le_one hv
    (by norm_num : (0 : ℝ) < 3 / 8) (by norm_num : (3 : ℝ) / 8 < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 32) (by norm_num : (1 : ℝ) / 32 < (3 / 8) / 2)
    selected_prime_level
  have herr' : Tendsto (fun N : ℕ =>
      progressionS2Error largePowerTuple q (5 / 32) v largeTupleCandidate N /
        tupleMaynardScale largePowerTuple (5 / 32) N) atTop (nhds 0) := by
    convert herr using 1 <;> norm_num
  have hconst : Tendsto (fun _N : ℕ => J / q) atTop (nhds (J / q)) :=
    tendsto_const_nhds
  have hlim := (hconst.add herr').sub (hS1.const_mul rho)
  have hpositive : ∀ᶠ N : ℕ in atTop,
      0 < J / q +
        progressionS2Error largePowerTuple q (5 / 32) v largeTupleCandidate N /
          tupleMaynardScale largePowerTuple (5 / 32) N -
        rho * (sieveWeightSum N
          (progressionWeight largePowerTuple q (5 / 32) v largeTupleCandidate N) /
          tupleMaynardScale largePowerTuple (5 / 32) N) := by
    have hlim' : Tendsto (fun N : ℕ => J / q +
        progressionS2Error largePowerTuple q (5 / 32) v largeTupleCandidate N /
          tupleMaynardScale largePowerTuple (5 / 32) N -
        rho * (sieveWeightSum N
          (progressionWeight largePowerTuple q (5 / 32) v largeTupleCandidate N) /
          tupleMaynardScale largePowerTuple (5 / 32) N)) atTop
        (nhds (J / q - rho * (I / q))) := by
      simpa only [add_zero] using hlim
    exact hlim'.eventually (eventually_gt_nhds hgap)
  have hmain := eventually_largeTupleS2Main_normalized_gt v
    (by norm_num : (0 : ℝ) < 5 / 32) (by norm_num : (0 : ℝ) < 1 / 8)
    (by norm_num : (1 : ℝ) / 8 < 5 / 32) kernelMargin_pos kernelMargin_lt_coefficient
  have hsplit := eventually_progressionS2_eq_main_add_error largePowerTuple q
    (by norm_num : (3 : ℝ) / 8 < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 32)
    (by norm_num : (1 : ℝ) / 32 < (3 / 8) / 2) v largeTupleCandidate
  have hsplit' : ∀ᶠ N : ℕ in atTop,
      primeWeightedSieveSum largePowerTuple N
        (progressionWeight largePowerTuple q (5 / 32) v largeTupleCandidate N) =
      progressionS2Main largePowerTuple q (5 / 32) v largeTupleCandidate N +
        progressionS2Error largePowerTuple q (5 / 32) v largeTupleCandidate N := by
    convert hsplit using 1 <;> norm_num
  filter_upwards [hpositive, hmain, hsplit',
    eventually_progressionS2Main_eq hq largePowerTuple (5 / 32) v largeTupleCandidate,
    eventually_tupleMaynardScale_pos (H := largePowerTuple)
      (by norm_num : (0 : ℝ) < 5 / 32)] with N hpositiveN hmainN hsplitN hmainEq hscale
  have hdiv := div_lt_div_of_pos_right hmainN hqR
  have hmainLower : J / q <
      progressionS2Main largePowerTuple q (5 / 32) v largeTupleCandidate N /
        tupleMaynardScale largePowerTuple (5 / 32) N := by
    rw [hmainEq]
    rw [div_right_comm]
    exact hdiv
  have hnormalized : 0 < sieveExcess largePowerTuple N rho
      (progressionWeight largePowerTuple q (5 / 32) v largeTupleCandidate N) /
        tupleMaynardScale largePowerTuple (5 / 32) N := by
    unfold sieveExcess
    rw [hsplitN, sub_div, add_div, mul_div_assoc]
    linarith
  exact (div_pos_iff_of_pos_right hscale).mp hnormalized

end MaynardBFT.Sieve
