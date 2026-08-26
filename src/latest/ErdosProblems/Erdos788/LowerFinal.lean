import ErdosProblems.Erdos788.SampledShearer
import ErdosProblems.Erdos788.LowerAnalytic
import ErdosProblems.Erdos788.Normalization
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The quantitative lower bound

This module joins the exact sampling--Shearer inequality to the
elementary optimization and then transfers the result through the exact
normalization/min--max identity.
-/

namespace Erdos788

open Finset

private theorem samplingPower_le_three_mul_succ_alt {N b t : ℕ}
    (hbN : b ≤ N)
    (hmin : t = 0 ∨ N * (2 ^ t) ^ 2 < 8 * b ^ 3) :
    2 ^ t ≤ 3 * (b + 1) := by
  rcases hmin with (rfl | hupper)
  · omega
  by_cases hb : b = 0
  · subst b
    simp at hupper
  have hbpos : 0 < b := Nat.pos_of_ne_zero hb
  have hmul : b * (2 ^ t) ^ 2 < b * (8 * b ^ 2) := by
    calc
      b * (2 ^ t) ^ 2 ≤ N * (2 ^ t) ^ 2 :=
        Nat.mul_le_mul_right _ hbN
      _ < 8 * b ^ 3 := hupper
      _ = b * (8 * b ^ 2) := by ring
  have hsq : (2 ^ t) ^ 2 < 8 * b ^ 2 :=
    (Nat.mul_lt_mul_left hbpos).mp hmul
  have hlt : 2 ^ t < 3 * b := by nlinarith
  omega

private theorem samplingPower_mul_averageCutoff_le_alt
    {b q : ℕ} (hqB : q ≤ 3 * (b + 1)) :
    q * (2 * (2 * (b + 1) / q + 1)) ≤ 10 * (b + 1) := by
  have hdiv : q * (2 * (b + 1) / q) ≤ 2 * (b + 1) := by
    simpa [mul_comm] using! Nat.div_mul_le_self (2 * (b + 1)) q
  nlinarith

private theorem arithmeticCutoff_le_shearerCutoff_alt {b q : ℕ}
    (hq : 0 < q) :
    8 * (b + 1) / q + 1 ≤
      2 * (2 * (2 * (b + 1) / q + 1)) + 1 := by
  let U := 2 * (b + 1)
  let V := 4 * (U / q + 1)
  have hbase : U < q * (U / q + 1) := Nat.lt_mul_div_succ U hq
  have hscaled : 4 * U < q * V := by
    dsimp only [V]
    nlinarith
  have hdiv : 4 * U / q < V := by
    by_contra h
    have hle : V ≤ 4 * U / q := Nat.le_of_not_gt h
    have hmul : V * q ≤ 4 * U := (Nat.le_div_iff_mul_le hq).mp hle
    nlinarith
  calc
    8 * (b + 1) / q + 1 = 4 * U / q + 1 := by
      congr 2
      simp only [U]
      ring
    _ ≤ V + 1 := Nat.add_le_add_right hdiv.le 1
    _ = 2 * (2 * (2 * (b + 1) / q + 1)) + 1 := by
      simp only [V, U]
      ring

set_option maxHeartbeats 1000000
/-- Every normalized sum graph has score at least a fixed multiple of the
square-root logarithmic scale. -/
theorem normalizedScore_lower {N : ℕ} (A : Finset ℕ) (hN : 2 ≤ N) :
    (1 / 1000 : ℝ) * Real.sqrt ((N : ℝ) * Real.log (N : ℝ)) ≤
      (A.card : ℝ) + ((sumGraph N A).indepNum : ℝ) := by
  let b : ℕ := A.card
  let a : ℕ := (sumGraph N A).indepNum
  let X : ℝ := Real.sqrt ((N : ℝ) * Real.log (N : ℝ))
  have hNpos : 0 < N := by omega
  have hlogN : 0 ≤ Real.log (N : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ N by omega)
  have hXnonneg : 0 ≤ X := Real.sqrt_nonneg _
  have hXsq : X ^ 2 = (N : ℝ) * Real.log (N : ℝ) := by
    exact Real.sq_sqrt (mul_nonneg (by positivity) hlogN)
  have hXleN : X ≤ (N : ℝ) := by
    simpa only [X] using! sqrt_mul_log_le_self hN
  have haOne : 1 ≤ a := by
    let v : Fin N := ⟨0, by omega⟩
    have hv : (sumGraph N A).IsIndepSet ({v} : Finset (Fin N)) := by
      simp
    simpa only [a, card_singleton] using! hv.card_le_indepNum
  by_cases hlarge : X ≤ 1000 * (b : ℝ)
  · change (1 / 1000 : ℝ) * X ≤ (b : ℝ) + (a : ℝ)
    have haNonneg : (0 : ℝ) ≤ a := by positivity
    norm_num at ⊢
    nlinarith
  · have hsmall : 1000 * (b : ℝ) < X := lt_of_not_ge hlarge
    have hbX : (b : ℝ) ≤ X := by
      have hbNonneg : (0 : ℝ) ≤ b := by positivity
      nlinarith
    have hbNR : (b : ℝ) ≤ (N : ℝ) := hbX.trans hXleN
    have hbN : b ≤ N := by exact_mod_cast hbNR
    obtain ⟨t, hscale, hminimal⟩ := exists_sampling_exponent N b hNpos
    let q : ℕ := 2 ^ t
    let B : ℕ := b + 1
    let K : ℕ := 2 * (2 * B / q + 1)
    have hqpos : 0 < q := by simp [q]
    have hqB : q ≤ 3 * B := by
      simpa only [q, B] using!
        samplingPower_le_three_mul_succ_alt hbN hminimal
    have hqK : q * K ≤ 10 * B := by
      simpa only [K, B] using!
        samplingPower_mul_averageCutoff_le_alt hqB
    have hsample :
        (N : ℝ) * Real.log (2 * K + 1 : ℕ) ≤
          16 * q * K * (a : ℝ) := by
      simpa only [q, B, K, b, a] using!
        sumGraph_indepNum_log_lower A t hscale
    have hqKR : (q : ℝ) * (K : ℝ) ≤ 10 * (B : ℝ) := by
      exact_mod_cast hqK
    have hmaster :
        (N : ℝ) * Real.log (2 * K + 1 : ℕ) ≤
          160 * (B : ℝ) * (a : ℝ) := by
      calc
        (N : ℝ) * Real.log (2 * K + 1 : ℕ) ≤
            16 * (q : ℝ) * (K : ℝ) * (a : ℝ) := hsample
        _ = 16 * ((q : ℝ) * (K : ℝ)) * (a : ℝ) := by ring
        _ ≤ 16 * (10 * (B : ℝ)) * (a : ℝ) := by gcongr
        _ = 160 * (B : ℝ) * (a : ℝ) := by ring
    have hBscore : (B : ℝ) ≤ (b : ℝ) + (a : ℝ) := by
      have hBNat : B ≤ b + a := by
        simp only [B]
        omega
      exact_mod_cast hBNat
    have hascore : (a : ℝ) ≤ (b : ℝ) + (a : ℝ) := by
      have hbNonneg : (0 : ℝ) ≤ b := by positivity
      linarith
    have hscoreNonneg : (0 : ℝ) ≤ (b : ℝ) + (a : ℝ) := by
      positivity
    have finish_of_square
        (hsq : X ^ 2 ≤ 1280 * (B : ℝ) * (a : ℝ)) :
        (1 / 1000 : ℝ) * X ≤ (b : ℝ) + (a : ℝ) := by
      have hprod : (B : ℝ) * (a : ℝ) ≤
          ((b : ℝ) + (a : ℝ)) ^ 2 := by
        calc
          (B : ℝ) * (a : ℝ) ≤
              ((b : ℝ) + (a : ℝ)) *
                ((b : ℝ) + (a : ℝ)) :=
            mul_le_mul hBscore hascore (by positivity) hscoreNonneg
          _ = ((b : ℝ) + (a : ℝ)) ^ 2 := by ring
      have hsq' : X ^ 2 ≤
          (1000 * ((b : ℝ) + (a : ℝ))) ^ 2 := by
        calc
          X ^ 2 ≤ 1280 * (B : ℝ) * (a : ℝ) := hsq
          _ ≤ 1280 * (((b : ℝ) + (a : ℝ)) ^ 2) := by
            have hm := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 1280)
            simpa only [mul_assoc] using! hm
          _ ≤ (1000 * ((b : ℝ) + (a : ℝ))) ^ 2 := by
            nlinarith [sq_nonneg ((b : ℝ) + (a : ℝ))]
      have hXbound : X ≤ 1000 * ((b : ℝ) + (a : ℝ)) :=
        (sq_le_sq₀ hXnonneg (mul_nonneg (by norm_num) hscoreNonneg)).mp hsq'
      norm_num at ⊢
      nlinarith
    rcases hminimal with (htZero | hupper)
    · subst t
      by_cases hbFourth : b ^ 4 ≤ N
      · have hBX : (B : ℝ) * X ≤ 4 * (N : ℝ) := by
          simpa only [B, b, X] using!
            add_one_mul_sqrt_mul_log_le_four hN hbFourth
        have hfourK : 4 ≤ 2 * K + 1 := by
          have hK : 2 ≤ K := by simp [K]
          omega
        have hlogFour : Real.log (4 : ℝ) ≤
            Real.log ((2 * K + 1 : ℕ) : ℝ) := by
          apply Real.log_le_log (by norm_num)
          exact_mod_cast hfourK
        have hlogD : (1 : ℝ) ≤ Real.log (2 * K + 1 : ℕ) := by
          have hlogFourEq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
            norm_num
          rw [hlogFourEq] at hlogFour
          nlinarith [Real.log_two_gt_d9]
        have hNmaster : (N : ℝ) ≤
            160 * (B : ℝ) * (a : ℝ) := by
          calc
            (N : ℝ) ≤ (N : ℝ) * Real.log (2 * K + 1 : ℕ) := by
              nlinarith
            _ ≤ 160 * (B : ℝ) * (a : ℝ) := hmaster
        have hcancel : (B : ℝ) * X ≤
            (B : ℝ) * (640 * (a : ℝ)) := by
          calc
            (B : ℝ) * X ≤ 4 * (N : ℝ) := hBX
            _ ≤ 4 * (160 * (B : ℝ) * (a : ℝ)) := by gcongr
            _ = (B : ℝ) * (640 * (a : ℝ)) := by ring
        have hBpos : (0 : ℝ) < (B : ℝ) := by
          exact_mod_cast (show 0 < B by simp [B])
        have hXa : X ≤ 640 * (a : ℝ) :=
          le_of_mul_le_mul_left hcancel hBpos
        change (1 / 1000 : ℝ) * X ≤ (b : ℝ) + (a : ℝ)
        norm_num at ⊢
        have hbNonneg : (0 : ℝ) ≤ b := by positivity
        nlinarith
      · have hNbFourth : N < b ^ 4 := Nat.lt_of_not_ge hbFourth
        have hbD : b ≤ 2 * K + 1 := by
          simp only [K, q, pow_zero, Nat.div_one, B]
          omega
        have hlog : Real.log (N : ℝ) ≤
            4 * Real.log (2 * K + 1 : ℕ) :=
          log_le_four_log_of_lt_fourth_power
            hNpos hNbFourth hbD
        have hsq : X ^ 2 ≤ 1280 * (B : ℝ) * (a : ℝ) := by
          rw [hXsq]
          calc
            (N : ℝ) * Real.log (N : ℝ) ≤
                (N : ℝ) * (4 * Real.log (2 * K + 1 : ℕ)) := by gcongr
            _ = 4 * ((N : ℝ) * Real.log (2 * K + 1 : ℕ)) := by ring
            _ ≤ 4 * (160 * (B : ℝ) * (a : ℝ)) := by gcongr
            _ ≤ 1280 * (B : ℝ) * (a : ℝ) := by
              have hBa : (0 : ℝ) ≤ (B : ℝ) * (a : ℝ) := by positivity
              nlinarith
        exact finish_of_square hsq
    · let d : ℕ := 8 * B / q + 1
      have hcut : 8 * N < b * d ^ 2 := by
        simpa only [d, B] using! cutoff_growth hNpos hqpos hupper
      have hlogCut : Real.log (N : ℝ) ≤ 8 * Real.log (d : ℕ) :=
        log_le_eight_log_cutoff hN hcut hbX
      have hdD : d ≤ 2 * K + 1 := by
        simpa only [d, K, B] using!
          arithmeticCutoff_le_shearerCutoff_alt (b := b) (q := q) hqpos
      have hdpos : 0 < d := by simp [d]
      have hlogMono : Real.log (d : ℕ) ≤
          Real.log (2 * K + 1 : ℕ) := by
        apply Real.log_le_log (by positivity)
        exact_mod_cast hdD
      have hlog : Real.log (N : ℝ) ≤
          8 * Real.log (2 * K + 1 : ℕ) := by
        calc
          Real.log (N : ℝ) ≤ 8 * Real.log (d : ℕ) := hlogCut
          _ ≤ 8 * Real.log (2 * K + 1 : ℕ) := by gcongr
      have hsq : X ^ 2 ≤ 1280 * (B : ℝ) * (a : ℝ) := by
        rw [hXsq]
        calc
          (N : ℝ) * Real.log (N : ℝ) ≤
              (N : ℝ) * (8 * Real.log (2 * K + 1 : ℕ)) := by gcongr
          _ = 8 * ((N : ℝ) * Real.log (2 * K + 1 : ℕ)) := by ring
          _ ≤ 8 * (160 * (B : ℝ) * (a : ℝ)) := by gcongr
          _ = 1280 * (B : ℝ) * (a : ℝ) := by ring
      exact finish_of_square hsq

/-- The normalized estimate transferred to the exact finite min--max score,
still at the natural vertex scale `n - 1`. -/
theorem fNat_lower_at_normalizedScale {n : ℕ} (hn : 3 ≤ n) :
    (1 / 1000 : ℝ) *
        Real.sqrt (((n - 1 : ℕ) : ℝ) * Real.log ((n - 1 : ℕ) : ℝ)) ≤
      (fNat n : ℝ) := by
  obtain ⟨B, _hB, hBscore⟩ := exists_graphScore_eq_minGraphScore n
  let A : Finset ℕ := normalizePalette n B
  have hN : 2 ≤ n - 1 := by omega
  have hnormalized := normalizedScore_lower A hN
  have hscoreNat :
      A.card + (sumGraph (n - 1) A).indepNum ≤ minGraphScore n := by
    calc
      A.card + (sumGraph (n - 1) A).indepNum =
          graphScore n (activePalette n B) := by
        symm
        exact graphScore_activePalette_eq_normalized n B
      _ ≤ graphScore n B := graphScore_activePalette_le n B
      _ = minGraphScore n := hBscore
  have hscoreReal :
      (A.card : ℝ) + ((sumGraph (n - 1) A).indepNum : ℝ) ≤
        (fNat n : ℝ) := by
    rw [fNat_eq_minGraphScore]
    exact_mod_cast hscoreNat
  exact hnormalized.trans hscoreReal

/-- Replacing `n - 1` by `n` costs only a factor of two. -/
theorem sqrt_scale_le_two_normalizedScale {n : ℕ} (hn : 3 ≤ n) :
    Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
      2 * Real.sqrt (((n - 1 : ℕ) : ℝ) *
        Real.log ((n - 1 : ℕ) : ℝ)) := by
  let N : ℕ := n - 1
  let S : ℝ := Real.sqrt ((n : ℝ) * Real.log (n : ℝ))
  let T : ℝ := Real.sqrt ((N : ℝ) * Real.log (N : ℝ))
  have hN : 2 ≤ N := by simp only [N]; omega
  have hnpos : (0 : ℝ) < n := by positivity
  have hNpos : (0 : ℝ) < N := by positivity
  have hlogn : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hlogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hnTwoN : (n : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast (show n ≤ 2 * N by simp only [N]; omega)
  have hnNSq : n ≤ N ^ 2 := by
    have hnEq : n = N + 1 := by
      simp only [N]
      omega
    rw [hnEq]
    nlinarith
  have hlog : Real.log (n : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    calc
      Real.log (n : ℝ) ≤ Real.log ((N : ℝ) ^ 2) := by
        apply Real.log_le_log hnpos
        exact_mod_cast hnNSq
      _ = 2 * Real.log (N : ℝ) := by
        rw [Real.log_pow]
        norm_num
  have hproduct : (n : ℝ) * Real.log (n : ℝ) ≤
      4 * ((N : ℝ) * Real.log (N : ℝ)) := by
    calc
      (n : ℝ) * Real.log (n : ℝ) ≤
          (2 * (N : ℝ)) * (2 * Real.log (N : ℝ)) :=
        mul_le_mul hnTwoN hlog hlogn (by positivity)
      _ = 4 * ((N : ℝ) * Real.log (N : ℝ)) := by ring
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hT0 : 0 ≤ T := Real.sqrt_nonneg _
  have hSsq : S ^ 2 = (n : ℝ) * Real.log (n : ℝ) := by
    exact Real.sq_sqrt (mul_nonneg hnpos.le hlogn)
  have hTsq : T ^ 2 = (N : ℝ) * Real.log (N : ℝ) := by
    exact Real.sq_sqrt (mul_nonneg hNpos.le hlogN)
  have hsquares : S ^ 2 ≤ (2 * T) ^ 2 := by
    calc
      S ^ 2 = (n : ℝ) * Real.log (n : ℝ) := hSsq
      _ ≤ 4 * ((N : ℝ) * Real.log (N : ℝ)) := hproduct
      _ = 4 * T ^ 2 := by rw [hTsq]
      _ = (2 * T) ^ 2 := by ring
  have hST : S ≤ 2 * T :=
    (sq_le_sq₀ hS0 (mul_nonneg (by norm_num) hT0)).mp hsquares
  simpa only [S, T, N] using! hST

/-- Explicit lower bound for the natural-valued extremal function. -/
theorem cast_fNat_lower {n : ℕ} (hn : 3 ≤ n) :
    (1 / 2000 : ℝ) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
      (fNat n : ℝ) := by
  have hscale := sqrt_scale_le_two_normalizedScale hn
  have hnormalized := fNat_lower_at_normalizedScale hn
  calc
    (1 / 2000 : ℝ) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
        (1 / 2000 : ℝ) *
          (2 * Real.sqrt (((n - 1 : ℕ) : ℝ) *
            Real.log ((n - 1 : ℕ) : ℝ))) := by gcongr
    _ = (1 / 1000 : ℝ) *
        Real.sqrt (((n - 1 : ℕ) : ℝ) *
          Real.log ((n - 1 : ℕ) : ℝ)) := by ring
    _ ≤ (fNat n : ℝ) := hnormalized

/-- The same explicit lower bound for the integer-valued function in the
problem statement. -/
theorem cast_f_lower {n : ℕ} (hn : 3 ≤ n) :
    (1 / 2000 : ℝ) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
      (f n : ℝ) := by
  simpa [f] using! cast_fNat_lower hn

/-- Eventual quantified form of the lower bound. -/
theorem exists_lowerBound_threshold :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      (1 / 2000 : ℝ) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
        (f n : ℝ) := by
  exact ⟨3, by norm_num, fun _n hn ↦ cast_f_lower hn⟩

end Erdos788
