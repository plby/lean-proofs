/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos294.SharpAssembly
import ErdosProblems.Erdos294.SharpOuterScales

/-! # The quantitative Liu--Sawhney lower bound -/

open Filter Finset Real
open scoped BigOperators Topology

namespace Erdos294.SharpLower

open Erdos297 Erdos297.ActiveLcm Erdos297.PrimeIntervals
open Erdos294.SharpAssembly Erdos294.SharpBridge
open Erdos294.SharpOuterScales Erdos294.SharpParameters
open Erdos294.SharpRepresentation Erdos294.SharpSupply

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A fixed constant small enough to leave wide separation between the two
denominator intervals in the gluing construction. -/
def lowerConstant : ℝ := 1 / (10 : ℝ) ^ 6

lemma lowerConstant_pos : 0 < lowerConstant := by
  norm_num [lowerConstant]

private lemma lowerProfile_eq_outerScaleReal (N : ℕ) :
    Erdos294.lowerProfile outerExponent N =
      (N : ℝ) / outerScaleReal N := by
  rfl

/-- Every requested denominator in the quantitative range, apart from the
two elementary cases `1` and `2`, is representable. -/
theorem eventually_represents_of_three_le_of_le_profile :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℕ,
      3 ≤ t →
      (t : ℝ) ≤ lowerConstant * Erdos294.lowerProfile outerExponent N →
      Erdos294.Represents N t := by
  have hrepLocal := tendsto_outerScale_atTop.eventually
    eventually_exists_sharpGoodSet_recSum_eq_div
  have hrepLarge := eventually_exists_sharpGoodSet_recSum_eq_div
  have hbridgeLocal := tendsto_outerScale_atTop.eventually
    eventually_bridgeModulus_dvd_sharpActiveLcm
  have hbridgeSize := tendsto_outerScale_atTop.eventually
    eventually_exp_sharpS_div_twenty_le_bridgeModulus
  have htransport := eventually_primeProduct_dvd_sharpActiveLcm
  have hlocalChain := tendsto_outerScale_atTop.eventually
    eventually_sharp_safe_scale_chain
  have hlocalS200 := tendsto_outerScale_atTop.eventually
    eventually_two_hundred_le_sharpS
  have hlargeChain := eventually_sharp_safe_scale_chain
  filter_upwards [eventually_pos_scales, eventually_outerScaleReal_pos,
      eventually_outerScale_bounds, eventually_sharpS_outerScale_ge_forty_log,
      eventually_two_outerScale_le_sharpS,
      tendsto_outerScale_atTop.eventually_ge_atTop 200,
      eventually_ge_atTop (1000 : ℕ), hrepLocal, hrepLarge,
      hbridgeLocal, hbridgeSize, htransport, hlocalChain, hlocalS200,
      hlargeChain] with
      N hpos hDpos hXbounds hSXlog hXtransport hX200 hN1000
        hrepX hrepN hQdivX hQsize hsupplyN hchainX hSX200 hchainN
  intro t ht hprofile
  let X := outerScale N
  let P := primesHalfFull (sharpS X)
  let Q := bridgeModulus X
  let m := glueMultiplier t Q
  let s := glueResidual t Q
  have hNpos : 0 < (N : ℝ) := hpos.1
  have hLpos : 0 < logScale N := zero_lt_one.trans hpos.2.1
  have hDpos' : 0 < outerScaleReal N := hDpos
  have htReal : (t : ℝ) * outerScaleReal N ≤ lowerConstant * N := by
    rw [lowerProfile_eq_outerScaleReal] at hprofile
    calc
      (t : ℝ) * outerScaleReal N ≤
          (lowerConstant * ((N : ℝ) / outerScaleReal N)) *
            outerScaleReal N := by gcongr
      _ = lowerConstant * N := by field_simp
  have htXReal : (t : ℝ) * (X : ℝ) ≤ (N : ℝ) / 1000000 := by
    calc
      (t : ℝ) * X ≤ (t : ℝ) * outerScaleReal N := by
        gcongr
        exact hXbounds.2.1
      _ ≤ lowerConstant * N := htReal
      _ = (N : ℝ) / 1000000 := by rw [lowerConstant]; ring
  have hmillion : 1000000 * (t * X) ≤ N := by
    have hcast : (((1000000 * (t * X) : ℕ) : ℝ)) ≤ (N : ℝ) := by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      calc
        (1000000 : ℝ) * ((t : ℝ) * (X : ℝ)) ≤
            1000000 * ((N : ℝ) / 1000000) := by gcongr
        _ = (N : ℝ) := by ring
    exact_mod_cast hcast
  have htXmul : 1000 * (t * X) ≤ N := by
    omega
  have htX : t * X ≤ N / 1000 := by omega
  have hXposNat : 1 ≤ X := by omega
  have htLeTX : t ≤ t * X := by
    simpa using Nat.mul_le_mul_left t hXposNat
  have htSmall : t < N / 1000 := by
    omega
  have hQdivX' : Q ∣ activeLcm (sharpGoodSet X) := by
    simpa [Q, X] using hQdivX
  have hPconditions : ∀ q ∈ P,
      q.Prime ∧ 3 ≤ q ∧ q ≤ sharpS N ∧ 2 * q ≤ KSafe N := by
    intro q hq
    have hqData := mem_primesHalfFull.mp hq
    have hqLeX : q ≤ X := hqData.2.1.trans
      (hchainX.1.trans (hchainX.2.1.trans hchainX.2.2))
    have hqGlobalS : q ≤ sharpS N := by
      exact hqLeX.trans (by omega : X ≤ sharpS N)
    have htwoq : 2 * q ≤ KSafe N := by
      calc
        2 * q ≤ 2 * sharpS X := Nat.mul_le_mul_left 2 hqData.2.1
        _ ≤ 2 * X := Nat.mul_le_mul_left 2
          (hchainX.1.trans (hchainX.2.1.trans hchainX.2.2))
        _ ≤ sharpS N := hXtransport
        _ ≤ KSafe N := hchainN.1
    have hqThree : 3 ≤ q := by
      have hSX200' : 200 ≤ sharpS X := by simpa [X] using hSX200
      have : 3 ≤ sharpS X / 2 := by
        omega
      exact this.trans hqData.1
    exact ⟨hqData.2.2, hqThree, hqGlobalS, htwoq⟩
  have hQdivN : Q ∣ activeLcm (sharpGoodSet N) := by
    have := hsupplyN P hPconditions
    simpa [Q, P, bridgeModulus] using this
  have hexpN : Real.exp (2 * logScale N) = (N : ℝ) ^ 2 := by
    calc
      Real.exp (2 * logScale N) = Real.exp (logScale N) ^ 2 := by
        convert Real.exp_nat_mul (logScale N) 2 using 1
        all_goals norm_num
      _ = (N : ℝ) ^ 2 := by rw [logScale, Real.exp_log hNpos]
  have hNtwoQ : (N : ℝ) ^ 2 ≤ (Q : ℝ) := by
    calc
      (N : ℝ) ^ 2 = Real.exp (2 * logScale N) := hexpN.symm
      _ ≤ Real.exp ((sharpS X : ℝ) / 20) := by
        apply Real.exp_le_exp.mpr
        have : 40 * logScale N ≤ (sharpS X : ℝ) := by
          simpa [X] using hSXlog
        linarith
      _ ≤ (Q : ℝ) := by simpa [Q, X] using hQsize
  have hNleQ : N ≤ Q := by
    have hreal : (N : ℝ) ≤ (Q : ℝ) := by
      calc
        (N : ℝ) ≤ (N : ℝ) ^ 2 := by
          have : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
          nlinarith
        _ ≤ (Q : ℝ) := hNtwoQ
    exact_mod_cast hreal
  have hlarge : 100 * t < Q := by
    have : 100 * t < N := by omega
    omega
  have hQpos : 0 < Q := by omega
  have hres := glueResidual_bounds ht hlarge
  have hQmt : Q ≤ m * t := by
    have htpos : 0 < t := by omega
    have hQt : Q + Q / 3 < m * t := by
      simpa [m, glueMultiplier, Nat.mul_comm] using
        Nat.lt_mul_div_succ (Q + Q / 3) htpos
    omega
  have hmQ : m ≤ Q := hres.2.2.trans (by omega)
  have hsEq : s + Q = m * t := by
    dsimp [s, glueResidual]
    exact Nat.sub_add_cancel hQmt
  have hsLowerNat : Q ≤ 3 * s := by
    have htpos : 0 < t := by omega
    have hQt : Q + Q / 3 < m * t := by
      simpa [m, glueMultiplier, Nat.mul_comm] using
        Nat.lt_mul_div_succ (Q + Q / 3) htpos
    omega
  have hsLower : (1 / 3 : ℝ) ≤ (s : ℝ) / Q := by
    rw [le_div_iff₀ (by exact_mod_cast hQpos)]
    have hcast : (Q : ℝ) ≤ 3 * (s : ℝ) := by exact_mod_cast hsLowerNat
    linarith
  have hsUpper : (s : ℝ) / Q ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hQpos)]
    have : s ≤ Q := by omega
    exact_mod_cast this
  obtain ⟨B, hBX, hBsum⟩ := hrepX s Q hQpos hQdivX' hsLower hsUpper
  have hcLowerNat : Q ≤ 3 * (Q - m) := by
    omega
  have hcLower : (1 / 3 : ℝ) ≤ ((Q - m : ℕ) : ℝ) / Q := by
    rw [le_div_iff₀ (by exact_mod_cast hQpos)]
    have hcast : (Q : ℝ) ≤ 3 * ((Q - m : ℕ) : ℝ) := by
      exact_mod_cast hcLowerNat
    linarith
  have hcUpper : ((Q - m : ℕ) : ℝ) / Q ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hQpos)]
    exact_mod_cast Nat.sub_le Q m
  obtain ⟨C, hCN, hCsum⟩ := hrepN (Q - m) Q hQpos hQdivN hcLower hcUpper
  have hBbounds : ∀ n ∈ sharpGoodSet X, 2 ≤ n ∧ n ≤ X := by
    intro n hn
    have hnI := mem_Icc.mp (sharpGoodSet_subset_Icc X hn)
    have hM : 2 ≤ sharpM X := by simp [sharpM]; omega
    exact ⟨hM.trans hnI.1, hnI.2⟩
  have hCbounds : ∀ n ∈ sharpGoodSet N, N / 100 ≤ n ∧ n ≤ N := by
    intro n hn
    simpa [sharpM] using mem_Icc.mp (sharpGoodSet_subset_Icc N hn)
  exact represents_of_glued_subsums (N := N) (t := t) (X := X)
    (Q := Q) (m := m) (s := s) (B := B) (C := C)
    (by omega) hQpos rfl hQmt hmQ hBX hCN hBsum hCsum
    hBbounds hCbounds htX htSmall hN1000

lemma represents_one {N : ℕ} (hN : 1 ≤ N) : Erdos294.Represents N 1 := by
  refine ⟨by norm_num, {1}, by simp, ?_, ?_⟩
  · intro n hn
    simp only [Finset.mem_singleton] at hn
    subst n
    exact ⟨le_rfl, hN⟩
  · norm_num [UnitFractions.rec_sum]

lemma represents_two {N : ℕ} (hN : 6 ≤ N) : Erdos294.Represents N 2 := by
  refine ⟨by norm_num, {2, 3, 6}, by simp, ?_, ?_⟩
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl
    · omega
    · omega
    · omega
  · norm_num [UnitFractions.rec_sum]

/-- Quantitative lower half of the resolution, with exponent `20` made
explicit. -/
theorem eventually_lowerProfile_le_firstForbidden :
    ∃ k : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop,
        c * Erdos294.lowerProfile k N ≤ Erdos294.firstForbidden N := by
  refine ⟨outerExponent, lowerConstant, lowerConstant_pos, ?_⟩
  filter_upwards [eventually_represents_of_three_le_of_le_profile,
      eventually_ge_atTop (6 : ℕ)] with N hrep hN
  by_contra hnot
  have hlt : (Erdos294.firstForbidden N : ℝ) <
      lowerConstant * Erdos294.lowerProfile outerExponent N :=
    lt_of_not_ge hnot
  have hffpos := Erdos294.firstForbidden_spec N |>.1
  have hrepresented : Erdos294.Represents N (Erdos294.firstForbidden N) := by
    by_cases hthree : 3 ≤ Erdos294.firstForbidden N
    · exact hrep (Erdos294.firstForbidden N) hthree hlt.le
    · have hcases : Erdos294.firstForbidden N = 1 ∨
          Erdos294.firstForbidden N = 2 := by omega
      rcases hcases with h | h
      · simpa [h] using represents_one (show 1 ≤ N by omega)
      · simpa [h] using represents_two hN
  exact Erdos294.not_represents_firstForbidden N hrepresented

end

end Erdos294.SharpLower
