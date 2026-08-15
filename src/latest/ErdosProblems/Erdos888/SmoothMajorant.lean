import ErdosProblems.Erdos888.BlockMajorant
import ErdosProblems.Erdos888.SmoothCore
import ErdosProblems.Erdos888.SmoothCoreBridge
import ErdosProblems.Erdos888.DyadicTransport

/-!
# The global smooth-core majorant

This file applies the finite min/square-root crossover to the mixed
`2 T M sqrt N` term in the canonical triangular block sum.
-/

open Filter Asymptotics
open scoped BigOperators

namespace Erdos888

noncomputable section

private lemma dyadicPrimeBlock_eq_dyadicPrimes_majorant (i : ℕ) :
    dyadicPrimeBlock i = dyadicPrimes (2 ^ i) := by
  ext p
  simp only [mem_dyadicPrimeBlock, mem_dyadicPrimes]
  rw [pow_succ]
  simp only [Nat.mul_comm]

private theorem dyadicPrimeBlock_card_le_pow (j : ℕ) :
    (dyadicPrimeBlock j).card ≤ 2 ^ j := by
  calc
    (dyadicPrimeBlock j).card ≤ (Finset.Ioc (2 ^ j) (2 ^ (j + 1))).card :=
      Finset.card_filter_le _ _
    _ = 2 ^ j := by simp [pow_succ]; omega

theorem blockCoreCandidates_subset_smoothCoreSet
    {n i j : ℕ} (hij : i ≤ j) :
    blockCoreCandidates n i j ⊆ smoothCoreSet n (2 ^ i) := by
  intro c hc
  have h := mem_blockCoreCandidates.mp hc
  rw [mem_smoothCoreSet]
  refine ⟨h.1, h.2.1, h.2.2.2.1, ?_, ?_⟩
  · calc
      c * (2 ^ i) ^ 2 = c * 2 ^ i * 2 ^ i := by ring
      _ ≤ c * 2 ^ i * 2 ^ j := by
        exact Nat.mul_le_mul_left (c * 2 ^ i) (Nat.pow_le_pow_right (by norm_num) hij)
      _ ≤ n := h.2.2.2.2.1
  · intro p hp
    have hprime := h.2.2.2.2.2 p hp
    simpa [pow_succ, Nat.mul_comm] using hprime

theorem blockCoreCandidates_card_le_T0 {n i j : ℕ} (hij : i ≤ j) :
    (blockCoreCandidates n i j).card ≤ T0 n (2 ^ i) := by
  exact Finset.card_le_card (blockCoreCandidates_subset_smoothCoreSet hij)

theorem blockCoreCandidates_card_le_div_majorant (n i j : ℕ) :
    (blockCoreCandidates n i j).card ≤ n / (2 ^ i * 2 ^ j) := by
  have hsubset : blockCoreCandidates n i j ⊆
      Finset.Icc 1 (n / (2 ^ i * 2 ^ j)) := by
    intro c hc
    have h := mem_blockCoreCandidates.mp hc
    exact Finset.mem_Icc.mpr ⟨h.1,
      (Nat.le_div_iff_mul_le (by positivity)).2 (by
        simpa [Nat.mul_assoc] using h.2.2.2.2.1)⟩
  calc
    (blockCoreCandidates n i j).card ≤
        (Finset.Icc 1 (n / (2 ^ i * 2 ^ j))).card :=
      Finset.card_le_card hsubset
    _ ≤ n / (2 ^ i * 2 ^ j) := by simp

private theorem triangular_sum_eq_iterated (n : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ ij ∈ triangularBlockIndices n, f ij.1 ij.2) =
      ∑ i ∈ Finset.range (Nat.log 2 n + 1),
        ∑ j ∈ Finset.Ico i (Nat.log 2 n + 1), f i j := by
  unfold triangularBlockIndices
  rw [Finset.sum_filter]
  change (∑ a ∈ (Finset.range (Nat.log 2 n + 1)) ×ˢ
      (Finset.range (Nat.log 2 n + 1)),
      (fun x : ℕ × ℕ ↦ if x.1 ≤ x.2 then f x.1 x.2 else 0) a) = _
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    tauto
  · intro j hj
    rfl

private theorem smoothCore_scale_identity {n X : ℕ} (hX : 0 < X) :
    ((X : ℝ) / lambda (X : ℝ)) *
        Real.sqrt (((n : ℝ) / (X : ℝ)) * (T0 n X : ℝ)) =
      smoothCoreTerm n X := by
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hlam : 0 < lambda (X : ℝ) := lambda_pos (by exact_mod_cast hX)
  unfold smoothCoreTerm
  rw [Real.sqrt_mul (div_nonneg (by positivity) hXr.le),
    Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity)]
  have hsqrtX : Real.sqrt (X : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hXr)
  field_simp
  rw [Real.sq_sqrt hXr.le]
  ring

private theorem inner_smoothCore_le {C : ℝ} (hC : 0 < C)
    (hprime : ∀ i : ℕ, ((dyadicPrimeBlock i).card : ℝ) ≤
      C * (((2 ^ i : ℕ) : ℝ) / lambda ((2 ^ i : ℕ) : ℝ)))
    {n i : ℕ} (hn : 0 < n) :
    (∑ j ∈ Finset.Ico i (Nat.log 2 n + 1),
      2 * ((blockCoreCandidates n i j).card : ℝ) *
        ((dyadicPrimeBlock i).card : ℝ) *
          Real.sqrt ((dyadicPrimeBlock j).card : ℝ)) ≤
      (160 * C) * smoothCoreTerm n (2 ^ i) := by
  let X : ℕ := 2 ^ i
  let T : ℕ := T0 n X
  have hX : 0 < X := by simp [X]
  by_cases hTzero : T = 0
  · have hczero : ∀ j ∈ Finset.Ico i (Nat.log 2 n + 1),
        (blockCoreCandidates n i j).card = 0 := by
      intro j hj
      have hcard := blockCoreCandidates_card_le_T0
        (n := n) (i := i) (j := j) (Finset.mem_Ico.mp hj).1
      simpa [T, X, hTzero] using hcard
    have hsumzero : (∑ j ∈ Finset.Ico i (Nat.log 2 n + 1),
        2 * ((blockCoreCandidates n i j).card : ℝ) *
          ((dyadicPrimeBlock i).card : ℝ) *
            Real.sqrt ((dyadicPrimeBlock j).card : ℝ)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [hczero j hj]
      simp
    rw [hsumzero]
    exact mul_nonneg (by positivity) (smoothCoreTerm_nonneg n (2 ^ i))
  have hT : 0 < T := Nat.pos_of_ne_zero hTzero
  let Q : ℕ := n / (X * T)
  let B : ℝ := (n : ℝ) / (X : ℝ)
  have hTdiv : T ≤ n / X ^ 2 := by
    simpa [T] using T0_le_div n X hX
  have hXsqT : X ^ 2 * T ≤ n := by
    simpa [mul_comm] using (Nat.le_div_iff_mul_le (pow_pos hX 2)).1 hTdiv
  have hXT : X * T ≤ n := by
    calc
      X * T ≤ X ^ 2 * T := Nat.mul_le_mul_right T (Nat.le_pow (by norm_num : 0 < 2))
      _ ≤ n := hXsqT
  have hQ : 0 < Q := by
    dsimp [Q]
    exact Nat.div_pos hXT (Nat.mul_pos hX hT)
  have hlow : (T : ℝ) * (Q : ℝ) ≤ B := by
    have hnat : X * (T * Q) ≤ n := by
      simpa [Q, Nat.mul_assoc] using Nat.mul_div_le n (X * T)
    dsimp [B]
    rw [le_div_iff₀ (by exact_mod_cast hX)]
    exact_mod_cast (show T * Q * X ≤ n by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hnat)
  have hhigh : B ≤ 2 * (T : ℝ) * (Q : ℝ) := by
    have hden : 0 < X * T := Nat.mul_pos hX hT
    have hnlt : n < (Q + 1) * (X * T) := by
      apply Nat.lt_mul_of_div_lt (c := X * T)
      · simp [Q]
      · exact hden
    have hQone : 1 ≤ Q := hQ
    have hfactor : ((Q + 1 : ℕ) : ℝ) * (T : ℝ) ≤
        2 * (T : ℝ) * (Q : ℝ) := by
      exact_mod_cast (show (Q + 1) * T ≤ 2 * T * Q by
        calc
          (Q + 1) * T ≤ (2 * Q) * T :=
            Nat.mul_le_mul_right T (by omega)
          _ = 2 * T * Q := by ring)
    dsimp [B]
    rw [div_le_iff₀ (by exact_mod_cast hX)]
    calc
      (n : ℝ) ≤ ((Q + 1 : ℕ) : ℝ) * (X : ℝ) * (T : ℝ) := by
        exact_mod_cast (show n ≤ (Q + 1) * X * T by
          simpa [Nat.mul_assoc] using hnlt.le)
      _ = (X : ℝ) * (((Q + 1 : ℕ) : ℝ) * (T : ℝ)) := by ring
      _ ≤ (X : ℝ) * (2 * (T : ℝ) * (Q : ℝ)) := by gcongr
      _ = 2 * (T : ℝ) * (Q : ℝ) * (X : ℝ) := by ring
  have hcross := dyadicMinSqrtCrossover_le
    (T := (T : ℝ)) (B := B) (Q := Q) (i := i)
    (R := Nat.log 2 n + 1) (by exact_mod_cast hT) (by positivity) hQ hlow hhigh
  have hterm : ∀ j ∈ Finset.Ico i (Nat.log 2 n + 1),
      2 * ((blockCoreCandidates n i j).card : ℝ) *
          ((dyadicPrimeBlock i).card : ℝ) *
            Real.sqrt ((dyadicPrimeBlock j).card : ℝ) ≤
        (2 * ((dyadicPrimeBlock i).card : ℝ)) *
          (min (T : ℝ) (B / (2 : ℝ) ^ j) *
            Real.sqrt ((2 : ℝ) ^ (j + 1))) := by
    intro j hj
    have hij := (Finset.mem_Ico.mp hj).1
    have hcoreT : ((blockCoreCandidates n i j).card : ℝ) ≤ T := by
      exact_mod_cast blockCoreCandidates_card_le_T0 hij
    have hcoreDivNat := blockCoreCandidates_card_le_div_majorant n i j
    have hcoreDiv : ((blockCoreCandidates n i j).card : ℝ) ≤
        B / (2 : ℝ) ^ j := by
      calc
        ((blockCoreCandidates n i j).card : ℝ) ≤
            ((n / (2 ^ i * 2 ^ j) : ℕ) : ℝ) := by exact_mod_cast hcoreDivNat
        _ ≤ (n : ℝ) / ((2 ^ i * 2 ^ j : ℕ) : ℝ) := Nat.cast_div_le
        _ = B / (2 : ℝ) ^ j := by
          simp [B, X]
          ring
    have hcore : ((blockCoreCandidates n i j).card : ℝ) ≤
        min (T : ℝ) (B / (2 : ℝ) ^ j) := le_min hcoreT hcoreDiv
    have hblock : ((dyadicPrimeBlock j).card : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
      calc
        ((dyadicPrimeBlock j).card : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
          exact_mod_cast dyadicPrimeBlock_card_le_pow j
        _ ≤ (2 : ℝ) ^ (j + 1) := by
          exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ))
            (Nat.le_succ j)
    have hsqrt := Real.sqrt_le_sqrt hblock
    have hmin : 0 ≤ min (T : ℝ) (B / (2 : ℝ) ^ j) := by
      exact le_min (by positivity) (by positivity)
    calc
      2 * ((blockCoreCandidates n i j).card : ℝ) *
          ((dyadicPrimeBlock i).card : ℝ) *
            Real.sqrt ((dyadicPrimeBlock j).card : ℝ) ≤
          2 * min (T : ℝ) (B / (2 : ℝ) ^ j) *
            ((dyadicPrimeBlock i).card : ℝ) *
              Real.sqrt ((dyadicPrimeBlock j).card : ℝ) := by gcongr
      _ ≤ 2 * min (T : ℝ) (B / (2 : ℝ) ^ j) *
            ((dyadicPrimeBlock i).card : ℝ) *
              Real.sqrt ((2 : ℝ) ^ (j + 1)) := by gcongr
      _ = (2 * ((dyadicPrimeBlock i).card : ℝ)) *
          (min (T : ℝ) (B / (2 : ℝ) ^ j) *
            Real.sqrt ((2 : ℝ) ^ (j + 1))) := by ring
  calc
    (∑ j ∈ Finset.Ico i (Nat.log 2 n + 1),
      2 * ((blockCoreCandidates n i j).card : ℝ) *
        ((dyadicPrimeBlock i).card : ℝ) *
          Real.sqrt ((dyadicPrimeBlock j).card : ℝ)) ≤
        ∑ j ∈ Finset.Ico i (Nat.log 2 n + 1),
          (2 * ((dyadicPrimeBlock i).card : ℝ)) *
            (min (T : ℝ) (B / (2 : ℝ) ^ j) *
              Real.sqrt ((2 : ℝ) ^ (j + 1))) := Finset.sum_le_sum hterm
    _ = (2 * ((dyadicPrimeBlock i).card : ℝ)) *
        ∑ j ∈ Finset.Ico i (Nat.log 2 n + 1),
          min (T : ℝ) (B / (2 : ℝ) ^ j) *
            Real.sqrt ((2 : ℝ) ^ (j + 1)) := by rw [Finset.mul_sum]
    _ ≤ (2 * ((dyadicPrimeBlock i).card : ℝ)) *
        (80 * Real.sqrt (B * T)) := by gcongr
    _ ≤ (2 * (C * ((X : ℝ) / lambda (X : ℝ)))) *
        (80 * Real.sqrt (B * T)) := by
      gcongr
      simpa [X] using hprime i
    _ = (160 * C) * smoothCoreTerm n X := by
      rw [← smoothCore_scale_identity hX]
      ring
    _ = (160 * C) * smoothCoreTerm n (2 ^ i) := by rfl

theorem universalSmoothCoreTerm_le_smoothCoreS3 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      universalSmoothCoreTerm n ≤ C * smoothCoreS3 n := by
  obtain ⟨C, hC, hprime⟩ := exists_forall_dyadicPrimeCount_le_scale
  refine ⟨160 * C, mul_pos (by norm_num) hC, fun n hn ↦ ?_⟩
  have hblock : ∀ i : ℕ, ((dyadicPrimeBlock i).card : ℝ) ≤
      C * (((2 ^ i : ℕ) : ℝ) / lambda ((2 ^ i : ℕ) : ℝ)) := by
    intro i
    rw [dyadicPrimeBlock_eq_dyadicPrimes_majorant]
    exact hprime (2 ^ i)
  rw [universalSmoothCoreTerm,
    triangular_sum_eq_iterated n (fun i j ↦
      2 * ((blockCoreCandidates n i j).card : ℝ) *
        ((dyadicPrimeBlock i).card : ℝ) *
          Real.sqrt ((dyadicPrimeBlock j).card : ℝ))]
  calc
    (∑ i ∈ Finset.range (Nat.log 2 n + 1),
      ∑ j ∈ Finset.Ico i (Nat.log 2 n + 1),
        2 * ((blockCoreCandidates n i j).card : ℝ) *
          ((dyadicPrimeBlock i).card : ℝ) *
            Real.sqrt ((dyadicPrimeBlock j).card : ℝ)) ≤
        ∑ i ∈ Finset.range (Nat.log 2 n + 1),
          (160 * C) * smoothCoreTerm n (2 ^ i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact inner_smoothCore_le hC hblock hn
    _ = (160 * C) * smoothCoreS3 n := by
      rw [smoothCoreS3, Finset.mul_sum]

private theorem nat_div_log_isBigO_scale_majorant :
    (fun n : ℕ ↦ (n : ℝ) / Real.log (n : ℝ)) =O[atTop] scale := by
  apply Asymptotics.IsBigO.of_bound 1
  have hloglog : ∀ᶠ n : ℕ in atTop,
      1 ≤ Real.log (Real.log (n : ℝ)) :=
    (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop 1
  have hlogpos := (Real.tendsto_log_atTop.comp
    tendsto_natCast_atTop_atTop).eventually_gt_atTop 0
  filter_upwards [hloglog, hlogpos] with n hll hlog
  have hleft : 0 ≤ (n : ℝ) / Real.log (n : ℝ) := by positivity
  have hscale : 0 ≤ scale n := by
    unfold scale
    positivity
  rw [Real.norm_of_nonneg hleft, Real.norm_of_nonneg hscale, one_mul]
  unfold scale
  calc
    (n : ℝ) / Real.log (n : ℝ) ≤
        (n : ℝ) * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by
      apply div_le_div_of_nonneg_right _ hlog.le
      simpa using mul_le_mul_of_nonneg_left hll (Nat.cast_nonneg n)
    _ = _ := rfl

theorem universalSmoothCoreTerm_isBigO_scale :
    universalSmoothCoreTerm =O[atTop] scale := by
  obtain ⟨C, hC, hpoint⟩ := universalSmoothCoreTerm_le_smoothCoreS3
  have hbridge : universalSmoothCoreTerm =O[atTop] smoothCoreS3 := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    rw [Real.norm_of_nonneg (universalSmoothCoreTerm_nonneg n),
      Real.norm_of_nonneg (smoothCoreS3_nonneg n)]
    exact hpoint n hn
  exact hbridge.trans <| smoothCoreS3_isBigO.trans nat_div_log_isBigO_scale_majorant

end

end Erdos888
