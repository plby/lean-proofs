/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.ControlledGeneralEventually
import ErdosProblems.Erdos360.PrimePoolSharpNumerics
import ErdosProblems.Erdos360.ControlledSharpOrdinary
import ErdosProblems.Erdos360.PrimeRandomControlledEventually
import ErdosProblems.Erdos360.DivisorCountEventually

/-!
# Eventual sharp rooms for the canonical prime pool

This file supplies the asymptotic estimates needed by the finite sharp
prime-pool record.  The lower-window constant is kept as a parameter: it
will be chosen only after the absolute sieve constants are known.
-/

namespace Erdos360

open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable

private lemma eventually_const_mul_y_mul_U_le_n_at
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (K : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      let y := initialLowerY n (lowerColorCount c n)
      K * y * controlledPrimeU n ≤ n := by
  have hpTop : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (83 / 400 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_controlledPrime_endpoint_parameters_at hc hc1,
    eventually_initialLowerY_lt_rpow_267_400_at hc hc1,
    hpTop.eventually (eventually_ge_atTop ((K * 1002 : ℕ) : ℝ))] with
      n hend hyUpper hpLarge
  dsimp only at hend hyUpper ⊢
  let y := initialLowerY n (lowerColorCount c n)
  have hn : 0 < n := by
    by_contra hn0
    have : n = 0 := Nat.eq_zero_of_not_pos hn0
    subst n
    norm_num [controlledPrimeU] at hend
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hUcast := (controlledPrimeU_cast_bounds n).2
  have hp8one : (1 : ℝ) ≤ Real.rpow (n : ℝ) (1 / 8 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have hUrough : (controlledPrimeU n : ℝ) <
      1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ) := by nlinarith
  have hyU : (y : ℝ) * controlledPrimeU n <
      Real.rpow (n : ℝ) (267 / 400 : ℝ) *
        (1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ)) :=
    (mul_lt_mul_of_pos_right hyUpper
      (by exact_mod_cast hend.1 : (0 : ℝ) < controlledPrimeU n)).trans
      (mul_lt_mul_of_pos_left hUrough
        (Real.rpow_pos_of_pos hnR (267 / 400 : ℝ)))
  have hpow : Real.rpow (n : ℝ) (267 / 400 : ℝ) *
      Real.rpow (n : ℝ) (1 / 8 : ℝ) =
        Real.rpow (n : ℝ) (317 / 400 : ℝ) := by
    convert (Real.rpow_add hnR (267 / 400 : ℝ) (1 / 8 : ℝ)).symm using 1 <;>
      norm_num
  have hnSplit : (n : ℝ) =
      Real.rpow (n : ℝ) (317 / 400 : ℝ) *
        Real.rpow (n : ℝ) (83 / 400 : ℝ) := by
    calc
      (n : ℝ) = Real.rpow (n : ℝ) 1 := (Real.rpow_one _).symm
      _ = Real.rpow (n : ℝ)
          ((317 / 400 : ℝ) + (83 / 400 : ℝ)) := by norm_num
      _ = _ := Real.rpow_add hnR _ _
  have hroomR : (((K * y * controlledPrimeU n : ℕ) : ℝ)) ≤
      (n : ℝ) := by
    push_cast
    calc
      (K : ℝ) * y * controlledPrimeU n ≤
          (K : ℝ) *
            (Real.rpow (n : ℝ) (267 / 400 : ℝ) *
              (1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ))) := by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hyU.le
          (Nat.cast_nonneg K)
      _ = ((K * 1002 : ℕ) : ℝ) *
          Real.rpow (n : ℝ) (317 / 400 : ℝ) := by
        push_cast
        rw [← hpow]
        ring
      _ ≤ Real.rpow (n : ℝ) (317 / 400 : ℝ) *
          Real.rpow (n : ℝ) (83 / 400 : ℝ) := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hpLarge
          (Real.rpow_nonneg hnR.le (317 / 400 : ℝ))
      _ = n := hnSplit.symm
  exact_mod_cast hroomR

private lemma eventually_const_mul_y_le_n_at
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (K : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      K * initialLowerY n (lowerColorCount c n) ≤ n := by
  filter_upwards [eventually_const_mul_y_mul_U_le_n_at hc hc1 K,
    eventually_controlledPrime_endpoint_parameters_at hc hc1] with n h hpar
  dsimp only at h hpar ⊢
  calc
    K * initialLowerY n (lowerColorCount c n) =
        K * initialLowerY n (lowerColorCount c n) * 1 := by simp
    _ ≤ K * initialLowerY n (lowerColorCount c n) * controlledPrimeU n :=
      Nat.mul_le_mul_left _ hpar.1
    _ ≤ n := h

private lemma eventually_const_mul_U_le_y_at
    {c : ℝ} (hc : 0 < c) (K : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      K * controlledPrimeU n ≤
        initialLowerY n (lowerColorCount c n) := by
  have hpTop : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (103 / 200 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 0,
    eventually_rpow_sixteen_twentyfive_le_initialLowerY_at hc,
    hpTop.eventually (eventually_ge_atTop ((K * 1002 : ℕ) : ℝ))] with
      n hn hyLower hpLarge
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hUcast := (controlledPrimeU_cast_bounds n).2
  have hp8one : (1 : ℝ) ≤ Real.rpow (n : ℝ) (1 / 8 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have hUrough : (controlledPrimeU n : ℝ) <
      1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ) := by nlinarith
  have hsplit : Real.rpow (n : ℝ) (16 / 25 : ℝ) =
      Real.rpow (n : ℝ) (1 / 8 : ℝ) *
        Real.rpow (n : ℝ) (103 / 200 : ℝ) := by
    convert Real.rpow_add hnR (1 / 8 : ℝ) (103 / 200 : ℝ) using 1 <;>
      norm_num
  have hKU : (((K * controlledPrimeU n : ℕ) : ℝ)) ≤
      Real.rpow (n : ℝ) (16 / 25 : ℝ) := by
    push_cast
    calc
      (K : ℝ) * controlledPrimeU n ≤
          ((K * 1002 : ℕ) : ℝ) *
            Real.rpow (n : ℝ) (1 / 8 : ℝ) := by
        push_cast
        simpa [mul_assoc] using
          mul_le_mul_of_nonneg_left hUrough.le (Nat.cast_nonneg K)
      _ ≤ Real.rpow (n : ℝ) (1 / 8 : ℝ) *
          Real.rpow (n : ℝ) (103 / 200 : ℝ) := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hpLarge
          (Real.rpow_nonneg hnR.le (1 / 8 : ℝ))
      _ = _ := hsplit.symm
  exact_mod_cast hKU.trans hyLower

private lemma eventually_sharp_pool_and_size_rooms_at
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      let y := initialLowerY n (lowerColorCount c n)
      let U := controlledPrimeU n
      let Q := controlledPrimeExtractedFloorTwelve n y
      16 * U + 256 ≤ sharpUniformPoolFloor Q controlledPrimeEll ∧
        64 * controlledPrimeEll ≤ Q ∧
        controlledPrimeClassCapTwelve n y ≤ y := by
  let K := 4096 * controlledPrimeEll
  have hpTop : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (7 / 25 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_const_mul_y_mul_U_le_n_at hc hc1 K,
    eventually_const_mul_y_le_n_at hc hc1 (128 * controlledPrimeEll),
    eventually_rpow_sixteen_twentyfive_le_initialLowerY_at hc,
    eventually_controlledPrimeTwelve_choice_numerics_at hc hc1,
    eventually_gt_atTop 0,
    hpTop.eventually (eventually_ge_atTop (2 : ℝ))] with
      n hKU hyConst hyLower hchoice hn hpLarge
  dsimp only at hKU hyConst hyLower hchoice ⊢
  let y := initialLowerY n (lowerColorCount c n)
  let U := controlledPrimeU n
  let Q := controlledPrimeExtractedFloorTwelve n y
  let M := controlledPrimeClassCapTwelve n y
  have hy : 0 < y := hchoice.U_pos.trans_le hchoice.U_le_y
  have hnQ : n ≤ y * Q := by
    simpa [y, Q] using controlledPrime_target_le_y_mul_floor hchoice
  have hQmain : 4096 * controlledPrimeEll * U ≤ Q := by
    exact Nat.le_of_mul_le_mul_left (by
      simpa [K, y, U, Q, mul_assoc, mul_comm, mul_left_comm] using
        hKU.trans hnQ) hy
  have hQconst : 128 * controlledPrimeEll ≤ Q := by
    exact Nat.le_of_mul_le_mul_left (by
      simpa [y, Q, mul_assoc, mul_comm, mul_left_comm] using
        hyConst.trans hnQ) hy
  have hpool : 16 * U + 256 ≤
      sharpUniformPoolFloor Q controlledPrimeEll := by
    unfold sharpUniformPoolFloor
    apply (Nat.le_div_iff_mul_le (by
      norm_num [controlledPrimeEll] : 0 < 8 * controlledPrimeEll)).2
    have hUone : 1 ≤ U := hchoice.U_pos
    calc
      (16 * U + 256) * (8 * controlledPrimeEll) ≤
          4096 * controlledPrimeEll * U := by
        nlinarith [show 0 < controlledPrimeEll by
          norm_num [controlledPrimeEll]]
      _ ≤ Q := hQmain
  have hMle : M ≤ y := by
    dsimp [M, controlledPrimeClassCapTwelve]
    apply (Nat.div_le_iff_le_mul (by positivity : 0 < 4 * y)).2
    have hyPow : (2 : ℝ) * n ≤ (y : ℝ) ^ 2 := by
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hpowLe : (2 : ℝ) * n ≤
          Real.rpow (n : ℝ) (32 / 25 : ℝ) := by
        have hsplit : Real.rpow (n : ℝ) (32 / 25 : ℝ) =
            (n : ℝ) * Real.rpow (n : ℝ) (7 / 25 : ℝ) := by
          calc
            Real.rpow (n : ℝ) (32 / 25 : ℝ) =
                Real.rpow (n : ℝ) (1 + 7 / 25 : ℝ) := by norm_num
            _ = Real.rpow (n : ℝ) 1 *
                Real.rpow (n : ℝ) (7 / 25 : ℝ) :=
              Real.rpow_add hnR _ _
            _ = _ := by simp
        rw [hsplit]
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hpLarge hnR.le
      have hsquare : (Real.rpow (n : ℝ) (16 / 25 : ℝ)) ^ 2 =
          Real.rpow (n : ℝ) (32 / 25 : ℝ) := by
        calc
          (Real.rpow (n : ℝ) (16 / 25 : ℝ)) ^ 2 =
              Real.rpow (Real.rpow (n : ℝ) (16 / 25 : ℝ)) (2 : ℝ) :=
            (Real.rpow_natCast _ 2).symm
          _ = Real.rpow (n : ℝ) ((16 / 25 : ℝ) * 2) :=
            (Real.rpow_mul hnR.le _ _).symm
          _ = _ := by norm_num
      rw [← hsquare] at hpowLe
      have hp0 := Real.rpow_nonneg hnR.le (16 / 25 : ℝ)
      have hy0 : (0 : ℝ) ≤ y := by positivity
      have hpSq : (Real.rpow (n : ℝ) (16 / 25 : ℝ)) ^ 2 ≤
          (y : ℝ) ^ 2 := by
        simpa [y, pow_two] using mul_self_le_mul_self hp0 hyLower
      exact hpowLe.trans hpSq
    have hnY : 2 * n ≤ y ^ 2 := by exact_mod_cast hyPow
    have hlt : 5 * n < (4 * y) * (y + 1) := by
      calc
        5 * n ≤ 3 * y ^ 2 := by omega
        _ < (4 * y) * (y + 1) := by nlinarith
    have heq : (4 * y) * (y + 1) = y * (4 * y) + 4 * y := by ring
    rw [heq] at hlt
    omega
  have hz : 64 * controlledPrimeEll ≤ Q := by
    exact (Nat.mul_le_mul_right controlledPrimeEll (by norm_num : 64 ≤ 128)).trans
      hQconst
  exact ⟨hpool, hz, hMle⟩

private lemma eventually_sharp_diversity_room_at
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      let y := initialLowerY n (lowerColorCount c n)
      128 * controlledPrimeEll * controlledPrimeU n ≤ fourthRootCeil y := by
  have hpTop : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (7 / 200 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 0,
    eventually_rpow_sixteen_twentyfive_le_initialLowerY_at hc,
    hpTop.eventually (eventually_ge_atTop
      (((128 * controlledPrimeEll * 1002 : ℕ) : ℝ)))] with
      n hn hyLower hpLarge
  dsimp only
  let y := initialLowerY n (lowerColorCount c n)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hy : 0 < y := by
    have hp : (0 : ℝ) < Real.rpow (n : ℝ) (16 / 25 : ℝ) :=
      Real.rpow_pos_of_pos hnR _
    exact_mod_cast hp.trans_le hyLower
  have hUcast := (controlledPrimeU_cast_bounds n).2
  have hp8one : (1 : ℝ) ≤ Real.rpow (n : ℝ) (1 / 8 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have hUrough : (controlledPrimeU n : ℝ) <
      1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ) := by nlinarith
  have hquarter := Real.rpow_le_rpow
    (Real.rpow_nonneg hnR.le (16 / 25 : ℝ)) hyLower
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hlowRoot : Real.rpow (n : ℝ) (4 / 25 : ℝ) ≤
      Real.rpow (y : ℝ) (1 / 4 : ℝ) := by
    calc
      Real.rpow (n : ℝ) (4 / 25 : ℝ) =
          Real.rpow (Real.rpow (n : ℝ) (16 / 25 : ℝ))
            (1 / 4 : ℝ) := by
        convert Real.rpow_mul hnR.le (16 / 25 : ℝ) (1 / 4 : ℝ) using 1 <;>
          norm_num
      _ ≤ _ := hquarter
  have hsplit : Real.rpow (n : ℝ) (4 / 25 : ℝ) =
      Real.rpow (n : ℝ) (1 / 8 : ℝ) *
        Real.rpow (n : ℝ) (7 / 200 : ℝ) := by
    convert Real.rpow_add hnR (1 / 8 : ℝ) (7 / 200 : ℝ) using 1 <;>
      norm_num
  have hroomR : (((128 * controlledPrimeEll * controlledPrimeU n : ℕ) : ℝ)) <
      Real.rpow (n : ℝ) (4 / 25 : ℝ) := by
    push_cast
    calc
      (128 : ℝ) * controlledPrimeEll * controlledPrimeU n <
          (((128 * controlledPrimeEll * 1002 : ℕ) : ℝ)) *
            Real.rpow (n : ℝ) (1 / 8 : ℝ) := by
        push_cast
        have hconst : (0 : ℝ) < 128 * controlledPrimeEll := by
          norm_num [controlledPrimeEll]
        simpa [mul_assoc] using mul_lt_mul_of_pos_left hUrough hconst
      _ ≤ Real.rpow (n : ℝ) (1 / 8 : ℝ) *
          Real.rpow (n : ℝ) (7 / 200 : ℝ) := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hpLarge
          (Real.rpow_nonneg hnR.le (1 / 8 : ℝ))
      _ = _ := hsplit.symm
  exact_mod_cast hroomR.le.trans
    (hlowRoot.trans (rpow_one_fourth_le_fourthRootCeil y))

private lemma eventually_sharp_fiber_ambient_at
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      let y := initialLowerY n (lowerColorCount c n)
      2000000000 * (128 * y / controlledPrimeEll + controlledPrimeU n) ≤ y := by
  filter_upwards [eventually_const_mul_U_le_y_at hc 4000000000] with n hU
  dsimp only at hU ⊢
  let y := initialLowerY n (lowerColorCount c n)
  let a := 128 * y / controlledPrimeEll
  have hell : 4000000000 * 128 ≤ controlledPrimeEll := by
    norm_num [controlledPrimeEll]
  have haMul : a * controlledPrimeEll ≤ 128 * y := by
    dsimp [a]
    exact Nat.div_mul_le_self _ _
  have ha : 4000000000 * a ≤ y := by
    have hscaled : (4000000000 * a) * controlledPrimeEll ≤
        y * controlledPrimeEll := by
      calc
        (4000000000 * a) * controlledPrimeEll =
            4000000000 * (a * controlledPrimeEll) := by ring
        _ ≤ 4000000000 * (128 * y) := Nat.mul_le_mul_left _ haMul
        _ = (4000000000 * 128) * y := by ring
        _ ≤ controlledPrimeEll * y := Nat.mul_le_mul_right y hell
        _ = y * controlledPrimeEll := by ring
    exact Nat.le_of_mul_le_mul_right hscaled (by
      norm_num [controlledPrimeEll])
  dsimp [y] at hU ⊢
  dsimp [a] at ha ⊢
  omega

private lemma eventually_sharp_increment_and_growth_rooms_at
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      let y := initialLowerY n (lowerColorCount c n)
      let U := controlledPrimeU n
      let Q := controlledPrimeExtractedFloorTwelve n y
      64 * sharpUniformIncrementCeiling y Q ≤
          primePoolSharpGrowthThreshold y ∧
        U * (4 * primePoolSharpGrowthThreshold y + 1) ≤ y := by
  have hpIncTop : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (29 / 200 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hpGrowthTop : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (23 / 1600 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 0,
    eventually_controlledPrimeTwelve_choice_numerics_at hc hc1,
    eventually_rpow_sixteen_twentyfive_le_initialLowerY_at hc,
    eventually_initialLowerY_lt_rpow_267_400_at hc hc1,
    hpIncTop.eventually (eventually_ge_atTop (64 * 65536 : ℝ)),
    hpGrowthTop.eventually (eventually_ge_atTop (50000 : ℝ))] with
      n hn hchoice hyLower hyUpper hpInc hpGrowth
  dsimp only at hchoice hyLower hyUpper ⊢
  let y := initialLowerY n (lowerColorCount c n)
  let U := controlledPrimeU n
  let Q := controlledPrimeExtractedFloorTwelve n y
  let E := sharpUniformIncrementCeiling y Q
  let G := primePoolSharpGrowthThreshold y
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hy : 0 < y := hchoice.U_pos.trans_le hchoice.U_le_y
  have hQ : 0 < Q := by
    dsimp [Q]
    exact hchoice.U_pos.trans_le hchoice.U_le_floor
  have hnQ : n ≤ y * Q := by
    simpa [y, Q] using controlledPrime_target_le_y_mul_floor hchoice
  have hEn : E * n ≤ 65536 * y ^ 2 := by
    have hEQ : E * Q ≤ 65536 * y := by
      dsimp [E, sharpUniformIncrementCeiling]
      exact Nat.div_mul_le_self _ _
    calc
      E * n ≤ E * (y * Q) := Nat.mul_le_mul_left E hnQ
      _ = y * (E * Q) := by ring
      _ ≤ y * (65536 * y) := Nat.mul_le_mul_left y hEQ
      _ = 65536 * y ^ 2 := by ring
  have hySqUpper : (y : ℝ) ^ 2 <
      Real.rpow (n : ℝ) (267 / 200 : ℝ) := by
    have hsq := pow_lt_pow_left₀ hyUpper (by positivity : (0 : ℝ) ≤ y)
      (by omega : 2 ≠ 0)
    have heq : (Real.rpow (n : ℝ) (267 / 400 : ℝ)) ^ 2 =
        Real.rpow (n : ℝ) (267 / 200 : ℝ) := by
      calc
        (Real.rpow (n : ℝ) (267 / 400 : ℝ)) ^ 2 =
            Real.rpow (Real.rpow (n : ℝ) (267 / 400 : ℝ)) (2 : ℝ) :=
          (Real.rpow_natCast _ 2).symm
        _ = Real.rpow (n : ℝ) ((267 / 400 : ℝ) * 2) :=
          (Real.rpow_mul hnR.le _ _).symm
        _ = _ := by norm_num
    calc
      (y : ℝ) ^ 2 =
          (initialLowerY n (lowerColorCount c n) : ℝ) ^ 2 := rfl
      _ < (Real.rpow (n : ℝ) (267 / 400 : ℝ)) ^ 2 := hsq
      _ = _ := heq
  have hESplit : Real.rpow (n : ℝ) (267 / 200 : ℝ) =
      Real.rpow (n : ℝ) (67 / 200 : ℝ) * n := by
    calc
      Real.rpow (n : ℝ) (267 / 200 : ℝ) =
          Real.rpow (n : ℝ) ((67 / 200 : ℝ) + 1) := by norm_num
      _ = Real.rpow (n : ℝ) (67 / 200 : ℝ) *
          Real.rpow (n : ℝ) 1 := Real.rpow_add hnR _ _
      _ = _ := by simp
  have hEUpper : (E : ℝ) <
      65536 * Real.rpow (n : ℝ) (67 / 200 : ℝ) := by
    have hEnR : (E : ℝ) * n ≤ 65536 * (y : ℝ) ^ 2 := by
      exact_mod_cast hEn
    have hmul : (E : ℝ) * n <
        (65536 * Real.rpow (n : ℝ) (67 / 200 : ℝ)) * n := by
      calc
        (E : ℝ) * n ≤ 65536 * (y : ℝ) ^ 2 := hEnR
        _ < 65536 * Real.rpow (n : ℝ) (267 / 200 : ℝ) :=
          mul_lt_mul_of_pos_left hySqUpper (by norm_num)
        _ = _ := by rw [hESplit]; ring
    exact lt_of_mul_lt_mul_right hmul hnR.le
  have hlowRoot : Real.rpow (n : ℝ) (4 / 25 : ℝ) ≤
      (fourthRootCeil y : ℝ) := by
    have hquarter := Real.rpow_le_rpow
      (Real.rpow_nonneg hnR.le (16 / 25 : ℝ)) hyLower
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    calc
      Real.rpow (n : ℝ) (4 / 25 : ℝ) =
          Real.rpow (Real.rpow (n : ℝ) (16 / 25 : ℝ))
            (1 / 4 : ℝ) := by
        convert Real.rpow_mul hnR.le (16 / 25 : ℝ) (1 / 4 : ℝ) using 1 <;>
          norm_num
      _ ≤ Real.rpow (y : ℝ) (1 / 4 : ℝ) := hquarter
      _ ≤ fourthRootCeil y := rpow_one_fourth_le_fourthRootCeil y
  have hGLower : Real.rpow (n : ℝ) (12 / 25 : ℝ) ≤ (G : ℝ) := by
    have hp0 := Real.rpow_nonneg hnR.le (4 / 25 : ℝ)
    have hpow := pow_le_pow_left₀ hp0 hlowRoot 3
    have heq : (Real.rpow (n : ℝ) (4 / 25 : ℝ)) ^ 3 =
        Real.rpow (n : ℝ) (12 / 25 : ℝ) := by
      calc
        (Real.rpow (n : ℝ) (4 / 25 : ℝ)) ^ 3 =
            Real.rpow (Real.rpow (n : ℝ) (4 / 25 : ℝ)) (3 : ℝ) :=
          (Real.rpow_natCast _ 3).symm
        _ = Real.rpow (n : ℝ) ((4 / 25 : ℝ) * 3) :=
          (Real.rpow_mul hnR.le _ _).symm
        _ = _ := by norm_num
    rw [← heq]
    simpa [G, primePoolSharpGrowthThreshold] using hpow
  have hIncSplit : Real.rpow (n : ℝ) (12 / 25 : ℝ) =
      Real.rpow (n : ℝ) (67 / 200 : ℝ) *
        Real.rpow (n : ℝ) (29 / 200 : ℝ) := by
    convert Real.rpow_add hnR (67 / 200 : ℝ) (29 / 200 : ℝ) using 1 <;>
      norm_num
  have hIncrement : 64 * E ≤ G := by
    have hR : (((64 * E : ℕ) : ℝ)) <
        Real.rpow (n : ℝ) (12 / 25 : ℝ) := by
      push_cast
      calc
        (64 : ℝ) * E <
            (64 * 65536 : ℝ) *
              Real.rpow (n : ℝ) (67 / 200 : ℝ) := by
          nlinarith [hEUpper]
        _ ≤ Real.rpow (n : ℝ) (67 / 200 : ℝ) *
            Real.rpow (n : ℝ) (29 / 200 : ℝ) := by
          simpa [mul_comm] using mul_le_mul_of_nonneg_left hpInc
            (Real.rpow_nonneg hnR.le (67 / 200 : ℝ))
        _ = _ := hIncSplit.symm
    exact_mod_cast hR.le.trans hGLower
  have hRootUpper := fourthRootCeil_cast_lt_two_mul_rpow hy
  have hGPowUpper : (G : ℝ) <
      8 * Real.rpow (y : ℝ) (3 / 4 : ℝ) := by
    have hpow := pow_lt_pow_left₀ hRootUpper (by positivity : (0 : ℝ) ≤ fourthRootCeil y)
      (by omega : 3 ≠ 0)
    have heq : (Real.rpow (y : ℝ) (1 / 4 : ℝ)) ^ 3 =
        Real.rpow (y : ℝ) (3 / 4 : ℝ) := by
      calc
        (Real.rpow (y : ℝ) (1 / 4 : ℝ)) ^ 3 =
            Real.rpow (Real.rpow (y : ℝ) (1 / 4 : ℝ)) (3 : ℝ) :=
          (Real.rpow_natCast _ 3).symm
        _ = Real.rpow (y : ℝ) ((1 / 4 : ℝ) * 3) :=
          (Real.rpow_mul (by positivity) _ _).symm
        _ = _ := by norm_num
    rw [← heq]
    dsimp [G, primePoolSharpGrowthThreshold]
    norm_num only [Nat.cast_pow]
    ring_nf at hpow ⊢
    exact hpow
  have hyThreeQuarter : Real.rpow (y : ℝ) (3 / 4 : ℝ) <
      Real.rpow (n : ℝ) (801 / 1600 : ℝ) := by
    have h := Real.rpow_lt_rpow (by positivity : (0 : ℝ) ≤ y) hyUpper
      (by norm_num : (0 : ℝ) < 3 / 4)
    calc
      Real.rpow (y : ℝ) (3 / 4 : ℝ) <
          Real.rpow (Real.rpow (n : ℝ) (267 / 400 : ℝ))
            (3 / 4 : ℝ) := h
      _ = Real.rpow (n : ℝ) ((267 / 400 : ℝ) * (3 / 4 : ℝ)) :=
        (Real.rpow_mul hnR.le _ _).symm
      _ = _ := by norm_num
  have hUcast := (controlledPrimeU_cast_bounds n).2
  have hp8one : (1 : ℝ) ≤ Real.rpow (n : ℝ) (1 / 8 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have hUrough : (U : ℝ) <
      1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ) := by
    change (controlledPrimeU n : ℝ) <
      1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ)
    nlinarith
  have hUG : (U : ℝ) * (4 * G + 1) <
      50000 * Real.rpow (n : ℝ) (1001 / 1600 : ℝ) := by
    have hGone : (G : ℝ) + 1 ≤ 2 * G := by
      have hGpos : (0 : ℕ) < G := by
        have hp : (0 : ℝ) < Real.rpow (n : ℝ) (12 / 25 : ℝ) :=
          Real.rpow_pos_of_pos hnR _
        exact_mod_cast hp.trans_le hGLower
      exact_mod_cast (by omega : G + 1 ≤ 2 * G)
    have hfour : (4 : ℝ) * G + 1 ≤ 5 * G := by nlinarith
    have hGupper : (G : ℝ) <
        8 * Real.rpow (n : ℝ) (801 / 1600 : ℝ) :=
      hGPowUpper.trans (mul_lt_mul_of_pos_left hyThreeQuarter (by norm_num))
    have hsecond : (4 : ℝ) * G + 1 <
        5 * (8 * Real.rpow (n : ℝ) (801 / 1600 : ℝ)) :=
      hfour.trans_lt (mul_lt_mul_of_pos_left hGupper (by norm_num))
    have hmul : (U : ℝ) * (4 * G + 1) <
        (1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ)) *
          (5 * (8 * Real.rpow (n : ℝ) (801 / 1600 : ℝ))) := by
      exact mul_lt_mul hUrough hsecond.le
        (by positivity) (by positivity)
    calc
      (U : ℝ) * (4 * G + 1) <
          (1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ)) *
          (5 * (8 * Real.rpow (n : ℝ) (801 / 1600 : ℝ))) := hmul
      _ = 40080 * (Real.rpow (n : ℝ) (1 / 8 : ℝ) *
          Real.rpow (n : ℝ) (801 / 1600 : ℝ)) := by ring
      _ ≤ 50000 * Real.rpow (n : ℝ) (1001 / 1600 : ℝ) := by
        have heq : Real.rpow (n : ℝ) (1 / 8 : ℝ) *
            Real.rpow (n : ℝ) (801 / 1600 : ℝ) =
              Real.rpow (n : ℝ) (1001 / 1600 : ℝ) := by
          convert (Real.rpow_add hnR (1 / 8 : ℝ)
            (801 / 1600 : ℝ)).symm using 1 <;> norm_num
        rw [heq]
        exact mul_le_mul_of_nonneg_right (by norm_num)
          (Real.rpow_nonneg hnR.le _)
  have hGrowthSplit : Real.rpow (n : ℝ) (16 / 25 : ℝ) =
      Real.rpow (n : ℝ) (1001 / 1600 : ℝ) *
        Real.rpow (n : ℝ) (23 / 1600 : ℝ) := by
    convert Real.rpow_add hnR (1001 / 1600 : ℝ) (23 / 1600 : ℝ) using 1 <;>
      norm_num
  have hGrowth : U * (4 * G + 1) ≤ y := by
    have hR : (((U * (4 * G + 1) : ℕ) : ℝ)) <
        Real.rpow (n : ℝ) (16 / 25 : ℝ) := by
      push_cast
      calc
        (U : ℝ) * (4 * G + 1) <
            50000 * Real.rpow (n : ℝ) (1001 / 1600 : ℝ) := hUG
        _ ≤ Real.rpow (n : ℝ) (1001 / 1600 : ℝ) *
            Real.rpow (n : ℝ) (23 / 1600 : ℝ) := by
          simpa [mul_comm] using mul_le_mul_of_nonneg_left hpGrowth
            (Real.rpow_nonneg hnR.le (1001 / 1600 : ℝ))
        _ = _ := hGrowthSplit.symm
    exact_mod_cast hR.le.trans hyLower
  exact ⟨hIncrement, hGrowth⟩

private lemma eventually_sharp_probability_at
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      let y := initialLowerY n (lowerColorCount c n)
      (2 : ℝ) * (((2 * y : ℕ) : ℝ) + 1) *
        Real.exp (-(primeRandomPoolDiversity y controlledPrimeEll : ℝ) / 24) < 1 := by
  let p : ℕ → ℝ := fun n ↦ Real.rpow (n : ℝ) (1 / 8 : ℝ)
  have hpTop : Tendsto p atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hdecay : Tendsto (fun n : ℕ ↦
      (p n) ^ 8 * Real.exp (-(p n))) atTop (nhds 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 8 |>.comp hpTop
  have hscaled : Tendsto (fun n : ℕ ↦
      6 * ((p n) ^ 8 * Real.exp (-(p n)))) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hdecay
  have hsmall := hscaled.eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_gt_atTop 0,
    eventually_controlledPrime_endpoint_parameters_at hc hc1,
    eventually_sharp_diversity_room_at hc, hsmall] with
      n hn hend hdivroom hsmallN
  dsimp only at hend hdivroom ⊢
  let y := initialLowerY n (lowerColorCount c n)
  let D := primeRandomPoolDiversity y controlledPrimeEll
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hy : 0 < y := hend.1.trans_le hend.2.1
  have hyn : y ≤ n := by omega
  have hDU : controlledPrimeU n ≤ D := by
    dsimp [D, primeRandomPoolDiversity]
    apply (Nat.le_div_iff_mul_le (by
      norm_num [controlledPrimeEll] : 0 < 32 * controlledPrimeEll)).2
    calc
      controlledPrimeU n * (32 * controlledPrimeEll) ≤
          controlledPrimeU n * (128 * controlledPrimeEll) := by gcongr; norm_num
      _ = 128 * controlledPrimeEll * controlledPrimeU n := by ring
      _ ≤ fourthRootCeil y := by simpa [y] using hdivroom
  have hUp : p n ≤ (controlledPrimeU n : ℝ) / 24 := by
    have hU := (controlledPrimeU_cast_bounds n).1
    have hp0 : 0 ≤ p n := by dsimp [p]; positivity
    dsimp [p] at hU ⊢
    nlinarith
  have hpD : p n ≤ (D : ℝ) / 24 :=
    hUp.trans (div_le_div_of_nonneg_right (by exact_mod_cast hDU)
      (by norm_num : (0 : ℝ) ≤ 24))
  have hexp : Real.exp (-(D : ℝ) / 24) ≤ Real.exp (-(p n)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hcoeffNat : 2 * (2 * y + 1) ≤ 6 * n := by omega
  have hcoeff : (2 : ℝ) * (((2 * y : ℕ) : ℝ) + 1) ≤
      6 * (n : ℝ) := by exact_mod_cast hcoeffNat
  have hpPow : (p n) ^ 8 = (n : ℝ) := by
    dsimp [p]
    calc
      (Real.rpow (n : ℝ) (1 / 8 : ℝ)) ^ 8 =
          Real.rpow (Real.rpow (n : ℝ) (1 / 8 : ℝ)) (8 : ℝ) :=
        (Real.rpow_natCast _ 8).symm
      _ = Real.rpow (n : ℝ) ((1 / 8 : ℝ) * 8) :=
        (Real.rpow_mul hnR.le _ _).symm
      _ = n := by norm_num
  have hexp0 : 0 ≤ Real.exp (-(p n)) := (Real.exp_pos _).le
  calc
    (2 : ℝ) * (((2 * y : ℕ) : ℝ) + 1) *
        Real.exp (-(D : ℝ) / 24) ≤
        (2 : ℝ) * (((2 * y : ℕ) : ℝ) + 1) *
          Real.exp (-(p n)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ (6 * (n : ℝ)) * Real.exp (-(p n)) :=
      mul_le_mul_of_nonneg_right hcoeff hexp0
    _ = 6 * ((p n) ^ 8 * Real.exp (-(p n))) := by rw [hpPow]; ring
    _ < 1 := by simpa [p] using hsmallN

private lemma eventually_sharp_growth_budget_at
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      let y := initialLowerY n (lowerColorCount c n)
      let Q := controlledPrimeExtractedFloorTwelve n y
      sharpUniformLogBudget y Q controlledPrimeEll ≤
        sharpUniformPoolFloor Q controlledPrimeEll / 64 := by
  let C₁ : ℝ := 4096 * 501 ^ 2 * (16 * controlledPrimeEll)
  let C₂ : ℝ :=
    65536 * 501 * 8 * (16 * controlledPrimeEll) ^ 2
  have hpOneTop : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (5 / 16 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hpTwoTop : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (247 / 1600 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 1,
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_controlledPrimeTwelve_choice_numerics_at hc hc1,
    eventually_controlledPrime_endpoint_parameters_at hc hc1,
    eventually_initialLowerY_lt_rpow_267_400_at hc hc1,
    eventually_sharp_pool_and_size_rooms_at hc hc1,
    hpOneTop.eventually (eventually_ge_atTop C₁),
    hpTwoTop.eventually (eventually_ge_atTop C₂)] with
      n hn hlog hchoice hend hyUpper hpool hpOne hpTwo
  dsimp only at hchoice hend hyUpper hpool ⊢
  let y := initialLowerY n (lowerColorCount c n)
  let Q := controlledPrimeExtractedFloorTwelve n y
  let p := sharpUniformPoolFloor Q controlledPrimeEll
  let h := Nat.log 2 (2 * y) + 1
  let G := primePoolSharpGrowthThreshold y
  let budget := sharpUniformLogBudget y Q controlledPrimeEll
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hy : 0 < y := hchoice.U_pos.trans_le hchoice.U_le_y
  have hQ : 0 < Q := by
    dsimp [Q]
    exact hchoice.U_pos.trans_le hchoice.U_le_floor
  have hpRoom : 16 * controlledPrimeU n + 256 ≤ p := by
    simpa [y, Q, p] using hpool.1
  have hp256 : 256 ≤ p := by omega
  have hnQ : n ≤ y * Q := by
    simpa [y, Q] using controlledPrime_target_le_y_mul_floor hchoice
  have hQlower : Real.rpow (n : ℝ) (133 / 400 : ℝ) < (Q : ℝ) := by
    have hnQReal : (n : ℝ) ≤ (y : ℝ) * Q := by exact_mod_cast hnQ
    have hstrict : (n : ℝ) <
        Real.rpow (n : ℝ) (267 / 400 : ℝ) * Q :=
      hnQReal.trans_lt (mul_lt_mul_of_pos_right hyUpper (by exact_mod_cast hQ))
    have hsplit : (n : ℝ) =
        Real.rpow (n : ℝ) (267 / 400 : ℝ) *
          Real.rpow (n : ℝ) (133 / 400 : ℝ) := by
      calc
        (n : ℝ) = Real.rpow (n : ℝ) 1 := (Real.rpow_one _).symm
        _ = Real.rpow (n : ℝ)
            ((267 / 400 : ℝ) + (133 / 400 : ℝ)) := by norm_num
        _ = _ := Real.rpow_add hnR _ _
    apply lt_of_mul_lt_mul_left (a := Real.rpow (n : ℝ) (267 / 400 : ℝ))
    · calc
        Real.rpow (n : ℝ) (267 / 400 : ℝ) *
            Real.rpow (n : ℝ) (133 / 400 : ℝ) = n := hsplit.symm
        _ < Real.rpow (n : ℝ) (267 / 400 : ℝ) * Q := hstrict
    · exact Real.rpow_nonneg hnR.le _
  have hQp : Q < 16 * controlledPrimeEll * p := by
    have hrem : Q < (p + 1) * (8 * controlledPrimeEll) := by
      dsimp [p, sharpUniformPoolFloor]
      simpa [mul_comm] using Nat.lt_mul_div_succ Q
        (by norm_num [controlledPrimeEll] : 0 < 8 * controlledPrimeEll)
    calc
      Q < (p + 1) * (8 * controlledPrimeEll) := hrem
      _ ≤ (2 * p) * (8 * controlledPrimeEll) := by gcongr; omega
      _ = 16 * controlledPrimeEll * p := by ring
  have hpLower : Real.rpow (n : ℝ) (133 / 400 : ℝ) /
      (16 * controlledPrimeEll : ℝ) < (p : ℝ) := by
    have hQpR : (Q : ℝ) < (16 * controlledPrimeEll : ℝ) * p := by
      exact_mod_cast hQp
    apply (div_lt_iff₀ (by
      norm_num [controlledPrimeEll] : (0 : ℝ) < 16 * controlledPrimeEll)).2
    exact hQlower.trans (by simpa [mul_comm] using hQpR)
  have h2yn : 2 * y ≤ 2 * n := by
    have hyLinear : 140 * y ≤ n := by simpa [y] using hend.2.2.2.2.2.2
    have : y ≤ n := by omega
    exact Nat.mul_le_mul_left 2 this
  have hlogNat : (Nat.log 2 (2 * y) : ℝ) ≤
      2 * Real.log ((2 * y : ℕ) : ℝ) :=
    natLogTwo_cast_le_two_mul_log (by positivity)
  have hlog2y : Real.log ((2 * y : ℕ) : ℝ) ≤
      2 * Real.log (n : ℝ) := by
    have h2ynR : (((2 * y : ℕ) : ℝ)) ≤ ((2 * n : ℕ) : ℝ) := by
      exact_mod_cast h2yn
    have hmono := Real.log_le_log
      (by exact_mod_cast (show 0 < 2 * y by positivity)) h2ynR
    have hlogMul : Real.log ((2 * n : ℕ) : ℝ) =
        Real.log 2 + Real.log (n : ℝ) := by
      push_cast
      rw [Real.log_mul (by norm_num) hnR.ne']
    rw [hlogMul] at hmono
    have hlogTwo : Real.log 2 ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    linarith
  have hlogPower : Real.log (n : ℝ) ≤
      100 * Real.rpow (n : ℝ) (1 / 100 : ℝ) := by
    simpa [div_eq_mul_inv, mul_comm] using Real.log_le_rpow_div hnR.le
      (show (0 : ℝ) < 1 / 100 by norm_num)
  have hp01one : (1 : ℝ) ≤ Real.rpow (n : ℝ) (1 / 100 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hn0) (by norm_num)
  have hhUpper : (h : ℝ) ≤
      501 * Real.rpow (n : ℝ) (1 / 100 : ℝ) := by
    calc
      (h : ℝ) = (Nat.log 2 (2 * y) : ℝ) + 1 := by
        simp [h]
      _ ≤ 2 * Real.log ((2 * y : ℕ) : ℝ) + 1 := by linarith
      _ ≤ 4 * Real.log (n : ℝ) + 1 := by linarith
      _ ≤ 400 * Real.rpow (n : ℝ) (1 / 100 : ℝ) + 1 := by
        linarith
      _ ≤ 501 * Real.rpow (n : ℝ) (1 / 100 : ℝ) := by
        nlinarith
  have hGUpper : (G : ℝ) <
      8 * Real.rpow (n : ℝ) (801 / 1600 : ℝ) := by
    have hroot := fourthRootCeil_cast_lt_two_mul_rpow hy
    have hpow := pow_lt_pow_left₀ hroot (by positivity : (0 : ℝ) ≤ fourthRootCeil y)
      (by omega : 3 ≠ 0)
    have hy34 : Real.rpow (y : ℝ) (3 / 4 : ℝ) <
        Real.rpow (n : ℝ) (801 / 1600 : ℝ) := by
      have ht := Real.rpow_lt_rpow (by positivity : (0 : ℝ) ≤ y) hyUpper
        (by norm_num : (0 : ℝ) < 3 / 4)
      calc
        Real.rpow (y : ℝ) (3 / 4 : ℝ) <
            Real.rpow (Real.rpow (n : ℝ) (267 / 400 : ℝ))
              (3 / 4 : ℝ) := ht
        _ = Real.rpow (n : ℝ) ((267 / 400 : ℝ) * (3 / 4 : ℝ)) :=
          (Real.rpow_mul hnR.le _ _).symm
        _ = _ := by norm_num
    have hpEq : (Real.rpow (y : ℝ) (1 / 4 : ℝ)) ^ 3 =
        Real.rpow (y : ℝ) (3 / 4 : ℝ) := by
      calc
        _ = Real.rpow (Real.rpow (y : ℝ) (1 / 4 : ℝ)) (3 : ℝ) :=
          (Real.rpow_natCast _ 3).symm
        _ = Real.rpow (y : ℝ) ((1 / 4 : ℝ) * 3) :=
          (Real.rpow_mul (by positivity) _ _).symm
        _ = _ := by norm_num
    have hGy : (G : ℝ) < 8 * Real.rpow (y : ℝ) (3 / 4 : ℝ) := by
      rw [← hpEq]
      dsimp [G, primePoolSharpGrowthThreshold]
      norm_num only [Nat.cast_pow]
      ring_nf at hpow ⊢
      exact hpow
    exact hGy.trans (mul_lt_mul_of_pos_left hy34 (by norm_num))
  have hroughOne : 4096 * h ^ 2 ≤ p := by
    have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ h) hhUpper 2
    have hsplit : Real.rpow (n : ℝ) (133 / 400 : ℝ) =
        Real.rpow (n : ℝ) (1 / 50 : ℝ) *
          Real.rpow (n : ℝ) (5 / 16 : ℝ) := by
      convert Real.rpow_add hnR (1 / 50 : ℝ) (5 / 16 : ℝ) using 1 <;>
        norm_num
    have hR : (((4096 * h ^ 2 : ℕ) : ℝ)) ≤
        Real.rpow (n : ℝ) (133 / 400 : ℝ) /
          (16 * controlledPrimeEll : ℝ) := by
      norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [hsplit]
      apply (le_div_iff₀ (by
        norm_num [controlledPrimeEll] : (0 : ℝ) < 16 * controlledPrimeEll)).2
      calc
        (4096 : ℝ) * h ^ 2 * (16 * controlledPrimeEll) ≤
            C₁ * Real.rpow (n : ℝ) (1 / 50 : ℝ) := by
          dsimp [C₁]
          have hpSq : (Real.rpow (n : ℝ) (1 / 100 : ℝ)) ^ 2 =
              Real.rpow (n : ℝ) (1 / 50 : ℝ) := by
            calc
              _ = Real.rpow (Real.rpow (n : ℝ) (1 / 100 : ℝ)) (2 : ℝ) :=
                (Real.rpow_natCast _ 2).symm
              _ = Real.rpow (n : ℝ) ((1 / 100 : ℝ) * 2) :=
                (Real.rpow_mul hnR.le _ _).symm
              _ = _ := by norm_num
          have hsq' : (h : ℝ) ^ 2 ≤
              501 ^ 2 * Real.rpow (n : ℝ) (1 / 50 : ℝ) := by
            calc
              (h : ℝ) ^ 2 ≤
                  (501 * Real.rpow (n : ℝ) (1 / 100 : ℝ)) ^ 2 := hsq
              _ = 501 ^ 2 * Real.rpow (n : ℝ) (1 / 50 : ℝ) := by
                rw [mul_pow, hpSq]
          have hconst : (0 : ℝ) ≤ 4096 * (16 * controlledPrimeEll) := by
            positivity
          have hmul := mul_le_mul_of_nonneg_left hsq' hconst
          simpa [C₁, mul_assoc, mul_comm, mul_left_comm] using hmul
        _ ≤ Real.rpow (n : ℝ) (5 / 16 : ℝ) *
            Real.rpow (n : ℝ) (1 / 50 : ℝ) := by
          simpa [mul_comm] using mul_le_mul_of_nonneg_right hpOne
            (Real.rpow_nonneg hnR.le (1 / 50 : ℝ))
        _ = _ := by ring
    exact_mod_cast hR.trans hpLower.le
  have hroughTwo : 65536 * h * G ≤ p ^ 2 := by
    have hsplit : Real.rpow (n : ℝ) (133 / 200 : ℝ) =
        Real.rpow (n : ℝ) (817 / 1600 : ℝ) *
          Real.rpow (n : ℝ) (247 / 1600 : ℝ) := by
      convert Real.rpow_add hnR (817 / 1600 : ℝ) (247 / 1600 : ℝ) using 1 <;>
        norm_num
    have hbaseSq : (Real.rpow (n : ℝ) (133 / 400 : ℝ)) ^ 2 =
        Real.rpow (n : ℝ) (133 / 200 : ℝ) := by
      calc
        _ = Real.rpow (Real.rpow (n : ℝ) (133 / 400 : ℝ)) (2 : ℝ) :=
          (Real.rpow_natCast _ 2).symm
        _ = Real.rpow (n : ℝ) ((133 / 400 : ℝ) * 2) :=
          (Real.rpow_mul hnR.le _ _).symm
        _ = _ := by norm_num
    have hbasePos : (0 : ℝ) < Real.rpow (n : ℝ) (133 / 400 : ℝ) /
        (16 * controlledPrimeEll : ℝ) := by
      exact div_pos (Real.rpow_pos_of_pos hnR _) (by
        norm_num [controlledPrimeEll])
    have hpLowerSq : (Real.rpow (n : ℝ) (133 / 400 : ℝ) /
        (16 * controlledPrimeEll : ℝ)) ^ 2 < (p : ℝ) ^ 2 :=
      pow_lt_pow_left₀ hpLower hbasePos.le (by omega)
    have hR : (((65536 * h * G : ℕ) : ℝ)) ≤
        (Real.rpow (n : ℝ) (133 / 400 : ℝ) /
          (16 * controlledPrimeEll : ℝ)) ^ 2 := by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      rw [div_pow]
      apply (le_div_iff₀ (by
        norm_num [controlledPrimeEll] : (0 : ℝ) <
          (16 * controlledPrimeEll : ℝ) ^ 2)).2
      have hprod : (h : ℝ) * G <
          (501 * 8) * Real.rpow (n : ℝ) (817 / 1600 : ℝ) := by
        have hpEq : Real.rpow (n : ℝ) (1 / 100 : ℝ) *
            Real.rpow (n : ℝ) (801 / 1600 : ℝ) =
              Real.rpow (n : ℝ) (817 / 1600 : ℝ) := by
          convert (Real.rpow_add hnR (1 / 100 : ℝ)
            (801 / 1600 : ℝ)).symm using 1 <;> norm_num
        calc
          (h : ℝ) * G <
              (501 * Real.rpow (n : ℝ) (1 / 100 : ℝ)) *
                (8 * Real.rpow (n : ℝ) (801 / 1600 : ℝ)) :=
            (mul_le_mul_of_nonneg_right hhUpper (by positivity)).trans_lt
              (mul_lt_mul_of_pos_left hGUpper (by positivity))
          _ = _ := by
            calc
              (501 * Real.rpow (n : ℝ) (1 / 100 : ℝ)) *
                    (8 * Real.rpow (n : ℝ) (801 / 1600 : ℝ)) =
                  (501 * 8) *
                    (Real.rpow (n : ℝ) (1 / 100 : ℝ) *
                      Real.rpow (n : ℝ) (801 / 1600 : ℝ)) := by ring
              _ = _ := by rw [hpEq]
      calc
        (65536 : ℝ) * h * G * (16 * controlledPrimeEll : ℝ) ^ 2 ≤
            C₂ * Real.rpow (n : ℝ) (817 / 1600 : ℝ) := by
          dsimp [C₂]
          have hconst : (0 : ℝ) ≤
              65536 * (16 * controlledPrimeEll) ^ 2 := by positivity
          simpa [mul_assoc, mul_comm, mul_left_comm] using
            mul_le_mul_of_nonneg_left hprod.le hconst
        _ ≤ Real.rpow (n : ℝ) (817 / 1600 : ℝ) *
            Real.rpow (n : ℝ) (247 / 1600 : ℝ) := by
          simpa [mul_comm] using mul_le_mul_of_nonneg_left hpTwo
            (Real.rpow_nonneg hnR.le (817 / 1600 : ℝ))
        _ = Real.rpow (n : ℝ) (133 / 200 : ℝ) := hsplit.symm
        _ = _ := hbaseSq.symm
    exact_mod_cast hR.trans hpLowerSq.le
  have hdpos : 0 < p / 128 := Nat.div_pos (by omega) (by norm_num)
  have hqMul : 256 * h * (G / (p / 128)) ≤ p := by
    have hhpos : 0 < h := by dsimp [h]; omega
    have hdivMul : (G / (p / 128)) * (p / 128) ≤ G :=
      Nat.div_mul_le_self _ _
    have hpLe : p ≤ 256 * (p / 128) := by
      have hrem : p < (p / 128 + 1) * 128 :=
        by simpa [mul_comm] using
          Nat.lt_mul_div_succ p (by norm_num : 0 < 128)
      omega
    have hscaled : 256 * h * (G / (p / 128)) * p ≤ p ^ 2 := by
      calc
        256 * h * (G / (p / 128)) * p ≤
            256 * h * (G / (p / 128)) * (256 * (p / 128)) :=
          Nat.mul_le_mul_left (256 * h * (G / (p / 128))) hpLe
        _ = 65536 * h * ((G / (p / 128)) * (p / 128)) := by ring
        _ ≤ 65536 * h * G := by gcongr
        _ ≤ p ^ 2 := hroughTwo
    have := Nat.le_of_mul_le_mul_right hscaled (by omega : 0 < p)
    simpa [mul_assoc, mul_comm, mul_left_comm] using this
  have hhpos : 0 < h := by dsimp [h]; omega
  have hhLe : h ≤ p / 4096 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4096)).2
    have : h ≤ h ^ 2 := by nlinarith
    simpa [mul_comm] using (Nat.mul_le_mul_left 4096 this).trans hroughOne
  have hbudget : budget ≤ p / 64 := by
    have hq' : h * (G / (p / 128)) ≤ p / 256 := by
      apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 256)).2
      simpa [mul_assoc, mul_comm, mul_left_comm] using hqMul
    have htwo : 2 * h ^ 2 ≤ p / 2048 := by
      apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2048)).2
      calc
        2 * h ^ 2 * 2048 = 4096 * h ^ 2 := by ring
        _ ≤ p := hroughOne
    have hsum : 2 * h ^ 2 + h * (G / (p / 128)) + h ≤ p / 64 := by
      calc
        2 * h ^ 2 + h * (G / (p / 128)) + h ≤
            p / 2048 + p / 256 + p / 4096 := by gcongr
        _ ≤ p / 64 := by omega
    change h * (2 * h + (G / (p / 128) + 1)) ≤ p / 64
    calc
      h * (2 * h + (G / (p / 128) + 1)) =
          2 * h ^ 2 + h * (G / (p / 128)) + h := by ring
      _ ≤ p / 64 := hsum
  simpa [budget, p] using hbudget

private lemma eventually_sharp_unsaturated_budget_at
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      let y := initialLowerY n (lowerColorCount c n)
      let Q := controlledPrimeExtractedFloorTwelve n y
      let M := controlledPrimeClassCapTwelve n y
      sharpUniformTargetCeiling y controlledPrimeEll ≤
        (65536 * y / M + 1) *
          (sharpUniformPoolFloor Q controlledPrimeEll / 16 -
            sharpUniformLogBudget y Q controlledPrimeEll) := by
  filter_upwards [eventually_controlledPrimeTwelve_choice_numerics_at hc hc1,
    eventually_sharp_pool_and_size_rooms_at hc hc1,
    eventually_sharp_growth_budget_at hc hc1,
    eventually_const_mul_U_le_y_at hc controlledPrimeEll,
    eventually_const_mul_y_le_n_at hc hc1
      (65536 * controlledPrimeEll)] with
      n hchoice hpool hbudget hEll hQscale
  dsimp only at hchoice hpool hbudget hEll hQscale ⊢
  let y := initialLowerY n (lowerColorCount c n)
  let Q := controlledPrimeExtractedFloorTwelve n y
  let M := controlledPrimeClassCapTwelve n y
  let p := sharpUniformPoolFloor Q controlledPrimeEll
  let budget := sharpUniformLogBudget y Q controlledPrimeEll
  let d := 50000 * y / Q
  let s := p / 64
  have hy : 0 < y := hchoice.U_pos.trans_le hchoice.U_le_y
  have hQ : 0 < Q := hchoice.U_pos.trans_le hchoice.U_le_floor
  have hQM : Q ≤ M := by
    dsimp [Q, M]
    exact (Nat.le_add_right _ _).trans hchoice.loss_room
  have hQy : Q ≤ y := hQM.trans (by simpa [y, M, Q] using hpool.2.2)
  have hpRoom : 16 * controlledPrimeU n + 256 ≤ p := by
    simpa [y, Q, p] using hpool.1
  have hnQ : n ≤ y * Q := by
    simpa [y, Q] using controlledPrime_target_le_y_mul_floor hchoice
  have hQhuge : 65536 * controlledPrimeEll ≤ Q := by
    exact Nat.le_of_mul_le_mul_left (by
      simpa [y, Q, mul_assoc, mul_comm, mul_left_comm] using
        hQscale.trans hnQ) hy
  have hp4096 : 4096 ≤ p := by
    dsimp [p, sharpUniformPoolFloor]
    apply (Nat.le_div_iff_mul_le (by
      norm_num [controlledPrimeEll] : 0 < 8 * controlledPrimeEll)).2
    calc
      4096 * (8 * controlledPrimeEll) ≤ 65536 * controlledPrimeEll := by
        nlinarith [show 0 < controlledPrimeEll by norm_num [controlledPrimeEll]]
      _ ≤ Q := hQhuge
  have hQlarge : 5 ≤ Q := by
    have hpQ : p ≤ Q := by
      dsimp [p, sharpUniformPoolFloor]
      exact (Nat.div_le_self _ _)
    omega
  have hMrel : 4 * M ≤ 5 * Q := by
    have hMmul : M * (4 * y) ≤ 5 * n := by
      dsimp [M, controlledPrimeClassCapTwelve]
      exact Nat.div_mul_le_self _ _
    have hQrem : 6 * n < 5 * y * (Q + 1) := by
      dsimp [Q, controlledPrimeExtractedFloorTwelve]
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        Nat.lt_mul_div_succ (6 * n) (by positivity : 0 < 5 * y)
    have hscaled : (6 * y) * (4 * M) < (6 * y) * (5 * Q) := by
      calc
        (6 * y) * (4 * M) = 6 * (M * (4 * y)) := by ring
        _ ≤ 6 * (5 * n) := Nat.mul_le_mul_left 6 hMmul
        _ = 30 * n := by ring
        _ < 25 * y * (Q + 1) := by nlinarith [hQrem]
        _ ≤ 30 * y * Q := by
          have : 25 * (Q + 1) ≤ 30 * Q := by omega
          nlinarith
        _ = (6 * y) * (5 * Q) := by ring
    exact (Nat.lt_of_mul_lt_mul_left hscaled).le
  have hMpos : 0 < M := hQ.trans_le hQM
  have hdD : d ≤ 65536 * y / M := by
    apply (Nat.le_div_iff_mul_le hMpos).2
    have hdQ : d * Q ≤ 50000 * y := by
      dsimp [d]
      exact Nat.div_mul_le_self _ _
    have hcross : 50000 * y * M ≤ 65536 * y * Q := by
      calc
        50000 * y * M = 12500 * y * (4 * M) := by ring
        _ ≤ 12500 * y * (5 * Q) := by gcongr
        _ ≤ 65536 * y * Q := by nlinarith
    have hscaled : (d * M) * Q ≤ (65536 * y) * Q := by
      calc
        (d * M) * Q = M * (d * Q) := by ring
        _ ≤ M * (50000 * y) := Nat.mul_le_mul_left M hdQ
        _ = 50000 * y * M := by ring
        _ ≤ 65536 * y * Q := hcross
    exact Nat.le_of_mul_le_mul_right hscaled hQ
  have hremaining : 3 * s ≤ p / 16 - budget := by
    have hb : budget ≤ p / 64 := by simpa [p, budget, y, Q] using hbudget
    have hthree : 3 * (p / 64) ≤ p / 16 - p / 64 := by omega
    dsimp [s]
    omega
  have hs64 : 64 ≤ s := by
    dsimp [s]
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 64)).2 (by
      simpa using hp4096)
  have hQp : Q < 9 * controlledPrimeEll * p := by
    have hrem : Q < (p + 1) * (8 * controlledPrimeEll) := by
      dsimp [p, sharpUniformPoolFloor]
      simpa [mul_comm] using Nat.lt_mul_div_succ Q
        (by norm_num [controlledPrimeEll] : 0 < 8 * controlledPrimeEll)
    have hpRatio : 8 * (p + 1) ≤ 9 * p := by omega
    calc
      Q < (p + 1) * (8 * controlledPrimeEll) := hrem
      _ = (8 * (p + 1)) * controlledPrimeEll := by ring
      _ ≤ (9 * p) * controlledPrimeEll := Nat.mul_le_mul_right _ hpRatio
      _ = 9 * controlledPrimeEll * p := by ring
  have hpS : p < 65 * s := by
    have hrem : p < (s + 1) * 64 := by
      dsimp [s]
      simpa [mul_comm] using Nat.lt_mul_div_succ p (by norm_num : 0 < 64)
    calc
      p < (s + 1) * 64 := hrem
      _ ≤ s * 65 := by nlinarith
      _ = 65 * s := by ring
  have hQS : Q < 585 * controlledPrimeEll * s := by
    calc
      Q < 9 * controlledPrimeEll * p := hQp
      _ < 9 * controlledPrimeEll * (65 * s) :=
        Nat.mul_lt_mul_of_pos_left hpS (by
          norm_num [controlledPrimeEll] : 0 < 9 * controlledPrimeEll)
      _ = 585 * controlledPrimeEll * s := by ring
  have hdQlower : 49000 * y ≤ d * Q := by
    have hrem : 50000 * y < Q * (d + 1) := by
      dsimp [d]
      simpa using Nat.lt_mul_div_succ (50000 * y) hQ
    rw [Nat.mul_add, Nat.mul_one] at hrem
    have : Q * d = d * Q := by ring
    rw [this] at hrem
    omega
  have hds : 49000 * y < 585 * controlledPrimeEll * (d * s) := by
    have hdpos : 0 < d := by
      apply Nat.div_pos
      · calc Q ≤ y := hQy
        _ ≤ 50000 * y := by nlinarith
      · exact hQ
    calc
      49000 * y ≤ d * Q := hdQlower
      _ < d * (585 * controlledPrimeEll * s) :=
        Nat.mul_lt_mul_of_pos_left hQS hdpos
      _ = 585 * controlledPrimeEll * (d * s) := by ring
  have htarget : sharpUniformTargetCeiling y controlledPrimeEll ≤ 3 * d * s := by
    have hellY : controlledPrimeEll ≤ y := by
      calc
        controlledPrimeEll = controlledPrimeEll * 1 := by simp
        _ ≤ controlledPrimeEll * controlledPrimeU n :=
          Nat.mul_le_mul_left _ hchoice.U_pos
        _ ≤ y := by simpa [y] using hEll
    have hbig : 128 * y + controlledPrimeEll <
        controlledPrimeEll * (3 * d * s) := by
      have h129 : 128 * y + controlledPrimeEll ≤ 129 * y := by omega
      have hconst : 585 * 129 < 3 * 49000 := by norm_num
      have hscaled := Nat.mul_lt_mul_of_pos_left hds (by norm_num : 0 < 3)
      nlinarith
    unfold sharpUniformTargetCeiling
    have hmul : (128 * y / controlledPrimeEll + 1) * controlledPrimeEll <
        (3 * d * s) * controlledPrimeEll := by
      calc
        (128 * y / controlledPrimeEll + 1) * controlledPrimeEll =
            (128 * y / controlledPrimeEll) * controlledPrimeEll +
              controlledPrimeEll := by ring
        _ ≤ 128 * y + controlledPrimeEll := by
          exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
        _ < controlledPrimeEll * (3 * d * s) := hbig
        _ = (3 * d * s) * controlledPrimeEll := by ring
    exact (Nat.lt_of_mul_lt_mul_right hmul).le
  calc
    sharpUniformTargetCeiling y controlledPrimeEll ≤ 3 * d * s := htarget
    _ ≤ (65536 * y / M + 1) * (p / 16 - budget) := by
      have hd' : d ≤ 65536 * y / M + 1 := hdD.trans (Nat.le_add_right _ 1)
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        Nat.mul_le_mul hd' hremaining

private lemma eventually_sharp_polynomial_reverse_at
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      let y := initialLowerY n (lowerColorCount c n)
      let Q := controlledPrimeExtractedFloorTwelve n y
      2 ^ 712 * (4 * sharpUniformIncrementCeiling y Q) ^ 100 <
        (primePoolSharpGrowthThreshold y /
            (2 * sharpUniformIncrementCeiling y Q)) ^ 2 *
          sharpUniformRemainderFloor Q controlledPrimeEll ^ 100 := by
  let CU : ℝ := 2 ^ 712 * (4 * 100000) ^ 100
  let CL : ℝ := (1 / 400000) ^ 2 *
    (1 / (256 * controlledPrimeEll : ℝ)) ^ 100
  have hCU : 0 < CU := by dsimp [CU]; positivity
  have hCL : 0 < CL := by
    dsimp [CL]
    norm_num [controlledPrimeEll]
  have hpTop : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (1 / 25 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 0,
    eventually_controlledPrimeTwelve_choice_numerics_at hc hc1,
    eventually_initialLowerY_lt_rpow_267_400_at hc hc1,
    eventually_rpow_sixteen_twentyfive_le_initialLowerY_at hc,
    eventually_sharp_pool_and_size_rooms_at hc hc1,
    eventually_sharp_increment_and_growth_rooms_at hc hc1,
    hpTop.eventually (eventually_ge_atTop (CU / CL))] with
      n hn hchoice hyUpper hyLower hpool hrooms hpLarge
  dsimp only at hchoice hyUpper hyLower hpool hrooms ⊢
  let y := initialLowerY n (lowerColorCount c n)
  let Q := controlledPrimeExtractedFloorTwelve n y
  let p := sharpUniformPoolFloor Q controlledPrimeEll
  let E := sharpUniformIncrementCeiling y Q
  let G := primePoolSharpGrowthThreshold y
  let R := sharpUniformRemainderFloor Q controlledPrimeEll
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hy : 0 < y := hchoice.U_pos.trans_le hchoice.U_le_y
  have hQ : 0 < Q := hchoice.U_pos.trans_le hchoice.U_le_floor
  have hnQ : n ≤ y * Q := by
    simpa [y, Q] using controlledPrime_target_le_y_mul_floor hchoice
  have hEn : E * n ≤ 65536 * y ^ 2 := by
    have hEQ : E * Q ≤ 65536 * y := by
      dsimp [E, sharpUniformIncrementCeiling]
      exact Nat.div_mul_le_self _ _
    calc
      E * n ≤ E * (y * Q) := Nat.mul_le_mul_left E hnQ
      _ = y * (E * Q) := by ring
      _ ≤ y * (65536 * y) := Nat.mul_le_mul_left y hEQ
      _ = 65536 * y ^ 2 := by ring
  have hySqUpper : (y : ℝ) ^ 2 <
      Real.rpow (n : ℝ) (267 / 200 : ℝ) := by
    have hsq := pow_lt_pow_left₀ hyUpper (by positivity : (0 : ℝ) ≤ y)
      (by omega : 2 ≠ 0)
    have heq : (Real.rpow (n : ℝ) (267 / 400 : ℝ)) ^ 2 =
        Real.rpow (n : ℝ) (267 / 200 : ℝ) := by
      calc
        _ = Real.rpow (Real.rpow (n : ℝ) (267 / 400 : ℝ)) (2 : ℝ) :=
          (Real.rpow_natCast _ 2).symm
        _ = Real.rpow (n : ℝ) ((267 / 400 : ℝ) * 2) :=
          (Real.rpow_mul hnR.le _ _).symm
        _ = _ := by norm_num
    calc
      (y : ℝ) ^ 2 =
          (initialLowerY n (lowerColorCount c n) : ℝ) ^ 2 := rfl
      _ < (Real.rpow (n : ℝ) (267 / 400 : ℝ)) ^ 2 := hsq
      _ = _ := heq
  have hESplit : Real.rpow (n : ℝ) (267 / 200 : ℝ) =
      Real.rpow (n : ℝ) (67 / 200 : ℝ) * n := by
    calc
      _ = Real.rpow (n : ℝ) ((67 / 200 : ℝ) + 1) := by norm_num
      _ = Real.rpow (n : ℝ) (67 / 200 : ℝ) *
          Real.rpow (n : ℝ) 1 := Real.rpow_add hnR _ _
      _ = _ := by simp
  have hEUpper : (E : ℝ) <
      100000 * Real.rpow (n : ℝ) (67 / 200 : ℝ) := by
    have hEnR : (E : ℝ) * n ≤ 65536 * (y : ℝ) ^ 2 := by exact_mod_cast hEn
    have hmul : (E : ℝ) * n <
        (100000 * Real.rpow (n : ℝ) (67 / 200 : ℝ)) * n := by
      calc
        (E : ℝ) * n ≤ 65536 * (y : ℝ) ^ 2 := hEnR
        _ < 65536 * Real.rpow (n : ℝ) (267 / 200 : ℝ) :=
          mul_lt_mul_of_pos_left hySqUpper (by norm_num)
        _ ≤ 100000 * Real.rpow (n : ℝ) (267 / 200 : ℝ) := by
          exact mul_le_mul_of_nonneg_right (by norm_num)
            (Real.rpow_nonneg hnR.le _)
        _ = _ := by rw [hESplit]; ring
    exact lt_of_mul_lt_mul_right hmul hnR.le
  have hlowRoot : Real.rpow (n : ℝ) (4 / 25 : ℝ) ≤
      (fourthRootCeil y : ℝ) := by
    have hquarter := Real.rpow_le_rpow
      (Real.rpow_nonneg hnR.le (16 / 25 : ℝ)) hyLower
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    calc
      Real.rpow (n : ℝ) (4 / 25 : ℝ) =
          Real.rpow (Real.rpow (n : ℝ) (16 / 25 : ℝ))
            (1 / 4 : ℝ) := by
        convert Real.rpow_mul hnR.le (16 / 25 : ℝ) (1 / 4 : ℝ) using 1 <;>
          norm_num
      _ ≤ Real.rpow (y : ℝ) (1 / 4 : ℝ) := hquarter
      _ ≤ fourthRootCeil y := rpow_one_fourth_le_fourthRootCeil y
  have hGLower : Real.rpow (n : ℝ) (12 / 25 : ℝ) ≤ (G : ℝ) := by
    have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hnR.le _) hlowRoot 3
    have heq : (Real.rpow (n : ℝ) (4 / 25 : ℝ)) ^ 3 =
        Real.rpow (n : ℝ) (12 / 25 : ℝ) := by
      calc
        _ = Real.rpow (Real.rpow (n : ℝ) (4 / 25 : ℝ)) (3 : ℝ) :=
          (Real.rpow_natCast _ 3).symm
        _ = Real.rpow (n : ℝ) ((4 / 25 : ℝ) * 3) :=
          (Real.rpow_mul hnR.le _ _).symm
        _ = _ := by norm_num
    rw [← heq]
    simpa [G, primePoolSharpGrowthThreshold] using hpow
  have hpRoom : 16 * controlledPrimeU n + 256 ≤ p := by
    simpa [y, Q, p] using hpool.1
  have hp256 : 256 ≤ p := by omega
  have hQlower : Real.rpow (n : ℝ) (133 / 400 : ℝ) < (Q : ℝ) := by
    have hnQR : (n : ℝ) ≤ (y : ℝ) * Q := by exact_mod_cast hnQ
    have hstrict : (n : ℝ) <
        Real.rpow (n : ℝ) (267 / 400 : ℝ) * Q :=
      hnQR.trans_lt (mul_lt_mul_of_pos_right hyUpper (by exact_mod_cast hQ))
    have hsplit : (n : ℝ) =
        Real.rpow (n : ℝ) (267 / 400 : ℝ) *
          Real.rpow (n : ℝ) (133 / 400 : ℝ) := by
      calc
        (n : ℝ) = Real.rpow (n : ℝ) 1 := (Real.rpow_one _).symm
        _ = Real.rpow (n : ℝ) ((267 / 400 : ℝ) + (133 / 400 : ℝ)) := by
          norm_num
        _ = _ := Real.rpow_add hnR _ _
    apply lt_of_mul_lt_mul_left (a := Real.rpow (n : ℝ) (267 / 400 : ℝ))
    · calc
        _ = (n : ℝ) := hsplit.symm
        _ < _ := hstrict
    · exact Real.rpow_nonneg hnR.le _
  have hQp : Q < 16 * controlledPrimeEll * p := by
    have hrem : Q < (p + 1) * (8 * controlledPrimeEll) := by
      dsimp [p, sharpUniformPoolFloor]
      simpa [mul_comm] using Nat.lt_mul_div_succ Q
        (by norm_num [controlledPrimeEll] : 0 < 8 * controlledPrimeEll)
    calc
      Q < (p + 1) * (8 * controlledPrimeEll) := hrem
      _ ≤ (2 * p) * (8 * controlledPrimeEll) := by gcongr; omega
      _ = 16 * controlledPrimeEll * p := by ring
  have hpLower : Real.rpow (n : ℝ) (133 / 400 : ℝ) /
      (16 * controlledPrimeEll : ℝ) < (p : ℝ) := by
    apply (div_lt_iff₀ (by
      norm_num [controlledPrimeEll] : (0 : ℝ) < 16 * controlledPrimeEll)).2
    exact hQlower.trans (by
      have : (Q : ℝ) < (16 * controlledPrimeEll : ℝ) * p := by
        exact_mod_cast hQp
      simpa [mul_comm] using this)
  have hRLower : Real.rpow (n : ℝ) (133 / 400 : ℝ) /
      (256 * controlledPrimeEll : ℝ) < (R : ℝ) := by
    have hrem : p < (R + 1) * 8 := by
      change p < (p / 8 + 1) * 8
      simpa [mul_comm] using Nat.lt_mul_div_succ p (by norm_num : 0 < 8)
    have hRpos : 0 < R := by
      change 0 < p / 8
      exact Nat.div_pos (by omega) (by norm_num)
    have hpR : p < 16 * R := by
      calc
        p < (R + 1) * 8 := hrem
        _ ≤ (2 * R) * 8 := by gcongr; omega
        _ = 16 * R := by ring
    apply (div_lt_iff₀ (by
      norm_num [controlledPrimeEll] : (0 : ℝ) < 256 * controlledPrimeEll)).2
    have hpRreal : (p : ℝ) < 16 * R := by exact_mod_cast hpR
    have hbase : Real.rpow (n : ℝ) (133 / 400 : ℝ) <
        (16 * controlledPrimeEll : ℝ) * p :=
      by simpa [mul_comm] using
        (div_lt_iff₀ (by
          norm_num [controlledPrimeEll] : (0 : ℝ) < 16 * controlledPrimeEll)).mp
          hpLower
    calc
      Real.rpow (n : ℝ) (133 / 400 : ℝ) <
          (16 * controlledPrimeEll : ℝ) * p := hbase
      _ < (16 * controlledPrimeEll : ℝ) * (16 * R) :=
        mul_lt_mul_of_pos_left hpRreal (by norm_num [controlledPrimeEll])
      _ = (R : ℝ) * (256 * controlledPrimeEll) := by ring
  have hQy : Q ≤ y := by
    have hQM : Q ≤ controlledPrimeClassCapTwelve n y := by
      exact (Nat.le_add_right _ _).trans hchoice.loss_room
    exact hQM.trans (by simpa [y, Q] using hpool.2.2)
  have hEpos : 0 < E := by
    dsimp [E, sharpUniformIncrementCeiling]
    apply Nat.div_pos
    · exact hQy.trans (Nat.le_mul_of_pos_left y (by norm_num))
    · exact hQ
  have hGfour : 4 * E ≤ G := by
    have h64 : 64 * E ≤ G := by simpa [y, Q, E, G] using hrooms.1
    omega
  let q := G / (2 * E)
  have hqpos : 0 < q := by
    dsimp [q]
    apply Nat.div_pos
    · omega
    · positivity
  have hGq : G < 4 * E * q := by
    have hrem : G < (q + 1) * (2 * E) := by
      dsimp [q]
      simpa [mul_comm] using Nat.lt_mul_div_succ G (by positivity : 0 < 2 * E)
    calc
      G < (q + 1) * (2 * E) := hrem
      _ ≤ (2 * q) * (2 * E) := by gcongr; omega
      _ = 4 * E * q := by ring
  have hqLower : (1 / 400000 : ℝ) *
      Real.rpow (n : ℝ) (29 / 200 : ℝ) < (q : ℝ) := by
    have hsplit : Real.rpow (n : ℝ) (12 / 25 : ℝ) =
        Real.rpow (n : ℝ) (67 / 200 : ℝ) *
          Real.rpow (n : ℝ) (29 / 200 : ℝ) := by
      convert Real.rpow_add hnR (67 / 200 : ℝ) (29 / 200 : ℝ) using 1 <;>
        norm_num
    have hnum : Real.rpow (n : ℝ) (12 / 25 : ℝ) <
        (4 * (100000 * Real.rpow (n : ℝ) (67 / 200 : ℝ))) * q := by
      calc
        Real.rpow (n : ℝ) (12 / 25 : ℝ) ≤ G := hGLower
        _ < ((4 * E * q : ℕ) : ℝ) := by exact_mod_cast hGq
        _ < (4 * (100000 * Real.rpow (n : ℝ) (67 / 200 : ℝ))) * q := by
          norm_num only [Nat.cast_mul]
          exact mul_lt_mul_of_pos_right
            (mul_lt_mul_of_pos_left hEUpper (by norm_num)) (by exact_mod_cast hqpos)
    rw [hsplit] at hnum
    have hp67 := Real.rpow_pos_of_pos hnR (67 / 200 : ℝ)
    field_simp
    nlinarith
  have hUpper : (((2 ^ 712 * (4 * E) ^ 100 : ℕ) : ℝ)) ≤
      CU * Real.rpow (n : ℝ) (67 / 2 : ℝ) := by
    let D : ℝ := (2 : ℝ) ^ 712
    have h4E : ((4 * E : ℕ) : ℝ) ≤
        4 * (100000 * Real.rpow (n : ℝ) (67 / 200 : ℝ)) := by
      norm_num only [Nat.cast_mul]
      gcongr
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (4 * E : ℕ))
      h4E 100
    have hpEq : (Real.rpow (n : ℝ) (67 / 200 : ℝ)) ^ 100 =
        Real.rpow (n : ℝ) (67 / 2 : ℝ) := by
      calc
        _ = Real.rpow (Real.rpow (n : ℝ) (67 / 200 : ℝ)) (100 : ℝ) :=
          (Real.rpow_natCast _ 100).symm
        _ = Real.rpow (n : ℝ) ((67 / 200 : ℝ) * 100) :=
          (Real.rpow_mul hnR.le _ _).symm
        _ = _ := by norm_num
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    change D * ((4 : ℝ) * E) ^ 100 ≤
      CU * Real.rpow (n : ℝ) (67 / 2 : ℝ)
    calc
      D * ((4 : ℝ) * E) ^ 100 ≤
          D * (4 * (100000 * Real.rpow (n : ℝ) (67 / 200 : ℝ))) ^ 100 :=
        by
          let a : ℝ := ((4 : ℝ) * E) ^ 100
          let b : ℝ :=
            (4 * (100000 * Real.rpow (n : ℝ) (67 / 200 : ℝ))) ^ 100
          have hab : a ≤ b := by simpa [a, b] using hpow
          have hDpos : 0 < D := by
            dsimp [D]
            exact pow_pos (by norm_num) _
          change D * a ≤ D * b
          exact mul_le_mul_of_nonneg_left hab hDpos.le
      _ = CU *
          Real.rpow (n : ℝ) (67 / 2 : ℝ) := by
        simp only [mul_pow, hpEq]
        dsimp [D, CU]
        ring
  have hLower : CL * Real.rpow (n : ℝ) (1677 / 50 : ℝ) <
      (q : ℝ) ^ 2 * (R : ℝ) ^ 100 := by
    have hqBasePos : (0 : ℝ) < (1 / 400000 : ℝ) *
        Real.rpow (n : ℝ) (29 / 200 : ℝ) :=
      mul_pos (by norm_num) (Real.rpow_pos_of_pos hnR _)
    have hRBasePos : (0 : ℝ) < Real.rpow (n : ℝ) (133 / 400 : ℝ) /
        (256 * controlledPrimeEll : ℝ) := by
      exact div_pos (Real.rpow_pos_of_pos hnR _) (by
        norm_num [controlledPrimeEll])
    have hqPow := pow_lt_pow_left₀ hqLower hqBasePos.le (by omega : 2 ≠ 0)
    have hRPow := pow_lt_pow_left₀ hRLower hRBasePos.le (by omega : 100 ≠ 0)
    have hqEq : ((1 / 400000 : ℝ) *
        Real.rpow (n : ℝ) (29 / 200 : ℝ)) ^ 2 =
          (1 / 400000 : ℝ) ^ 2 *
            Real.rpow (n : ℝ) (29 / 100 : ℝ) := by
      rw [mul_pow]
      congr 1
      calc
        _ = Real.rpow (Real.rpow (n : ℝ) (29 / 200 : ℝ)) (2 : ℝ) :=
          (Real.rpow_natCast _ 2).symm
        _ = Real.rpow (n : ℝ) ((29 / 200 : ℝ) * 2) :=
          (Real.rpow_mul hnR.le _ _).symm
        _ = _ := by norm_num
    have hREq : (Real.rpow (n : ℝ) (133 / 400 : ℝ) /
        (256 * controlledPrimeEll : ℝ)) ^ 100 =
          (1 / (256 * controlledPrimeEll : ℝ)) ^ 100 *
            Real.rpow (n : ℝ) (133 / 4 : ℝ) := by
      have hp : (Real.rpow (n : ℝ) (133 / 400 : ℝ)) ^ 100 =
          Real.rpow (n : ℝ) (133 / 4 : ℝ) := by
        calc
          _ = Real.rpow (Real.rpow (n : ℝ) (133 / 400 : ℝ)) (100 : ℝ) :=
            (Real.rpow_natCast _ 100).symm
          _ = Real.rpow (n : ℝ) ((133 / 400 : ℝ) * 100) :=
            (Real.rpow_mul hnR.le _ _).symm
          _ = _ := by norm_num
      rw [div_pow, hp]
      ring
    have hpEq : Real.rpow (n : ℝ) (29 / 100 : ℝ) *
        Real.rpow (n : ℝ) (133 / 4 : ℝ) =
          Real.rpow (n : ℝ) (1677 / 50 : ℝ) := by
      convert (Real.rpow_add hnR (29 / 100 : ℝ) (133 / 4 : ℝ)).symm using 1 <;>
        norm_num
    have hprod :
        (((1 / 400000 : ℝ) * Real.rpow (n : ℝ) (29 / 200 : ℝ)) ^ 2) *
          ((Real.rpow (n : ℝ) (133 / 400 : ℝ) /
            (256 * controlledPrimeEll : ℝ)) ^ 100) <
              (q : ℝ) ^ 2 * (R : ℝ) ^ 100 :=
      mul_lt_mul hqPow hRPow.le (by positivity) (by positivity)
    rw [hqEq, hREq] at hprod
    calc
      CL * Real.rpow (n : ℝ) (1677 / 50 : ℝ) =
          ((1 / 400000 : ℝ) ^ 2 *
            (1 / (256 * controlledPrimeEll : ℝ)) ^ 100) *
              Real.rpow (n : ℝ) (1677 / 50 : ℝ) := by rfl
      _ = ((1 / 400000 : ℝ) ^ 2 *
            (1 / (256 * controlledPrimeEll : ℝ)) ^ 100) *
          (Real.rpow (n : ℝ) (29 / 100 : ℝ) *
            Real.rpow (n : ℝ) (133 / 4 : ℝ)) := by rw [hpEq]
      _ =
          ((1 / 400000 : ℝ) ^ 2 *
              Real.rpow (n : ℝ) (29 / 100 : ℝ)) *
            ((1 / (256 * controlledPrimeEll : ℝ)) ^ 100 *
              Real.rpow (n : ℝ) (133 / 4 : ℝ)) := by
        ring
      _ < (q : ℝ) ^ 2 * (R : ℝ) ^ 100 := hprod
  have hPowerSplit : Real.rpow (n : ℝ) (1677 / 50 : ℝ) =
      Real.rpow (n : ℝ) (67 / 2 : ℝ) *
        Real.rpow (n : ℝ) (1 / 25 : ℝ) := by
    convert Real.rpow_add hnR (67 / 2 : ℝ) (1 / 25 : ℝ) using 1 <;>
      norm_num
  have hmiddle : CU * Real.rpow (n : ℝ) (67 / 2 : ℝ) ≤
      CL * Real.rpow (n : ℝ) (1677 / 50 : ℝ) := by
    rw [hPowerSplit]
    have hcoeff : CU ≤ CL * Real.rpow (n : ℝ) (1 / 25 : ℝ) := by
      calc
        CU = CL * (CU / CL) := by field_simp [hCL.ne']
        _ ≤ CL * Real.rpow (n : ℝ) (1 / 25 : ℝ) :=
          mul_le_mul_of_nonneg_left hpLarge hCL.le
    have hpMain := Real.rpow_nonneg hnR.le (67 / 2 : ℝ)
    calc
      CU * Real.rpow (n : ℝ) (67 / 2 : ℝ) ≤
          (CL * Real.rpow (n : ℝ) (1 / 25 : ℝ)) *
            Real.rpow (n : ℝ) (67 / 2 : ℝ) := by
        exact mul_le_mul_of_nonneg_right hcoeff hpMain
      _ = CL * (Real.rpow (n : ℝ) (67 / 2 : ℝ) *
          Real.rpow (n : ℝ) (1 / 25 : ℝ)) := by ring
  have hfinalR : (((2 ^ 712 * (4 * E) ^ 100 : ℕ) : ℝ)) <
      ((q ^ 2 * R ^ 100 : ℕ) : ℝ) := by
    have hmain := (hUpper.trans hmiddle).trans_lt hLower
    simpa only [Nat.cast_mul, Nat.cast_pow] using hmain
  exact_mod_cast hfinalR

private lemma eventually_sharp_long_scale_at
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    {S : ℕ} (hS : 0 < S) :
    ∀ᶠ n : ℕ in atTop,
      let y := initialLowerY n (lowerColorCount c n)
      let Q := controlledPrimeExtractedFloorTwelve n y
      (upperSieveCutoff 10 n *
          (upperSieveCutoff (4 * S) n ^ S) ^ 2) ^ 3 ≤
        sharpUniformRemainderFloor Q controlledPrimeEll := by
  let K : ℝ := 8000000 * (256 * controlledPrimeEll)
  have hpTop : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (61 / 400 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 1,
    eventually_controlledPrimeTwelve_choice_numerics_at hc hc1,
    eventually_initialLowerY_lt_rpow_267_400_at hc hc1,
    eventually_sharp_pool_and_size_rooms_at hc hc1,
    hpTop.eventually (eventually_ge_atTop K)] with
      n hn hchoice hyUpper hpool hpLarge
  dsimp only at hchoice hyUpper hpool ⊢
  let y := initialLowerY n (lowerColorCount c n)
  let Q := controlledPrimeExtractedFloorTwelve n y
  let p := sharpUniformPoolFloor Q controlledPrimeEll
  let R := sharpUniformRemainderFloor Q controlledPrimeEll
  let D := (upperSieveCutoff (4 * S) n ^ S) ^ 2
  let L := upperSieveCutoff 10 n
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hy : 0 < y := hchoice.U_pos.trans_le hchoice.U_le_y
  have hQ : 0 < Q := hchoice.U_pos.trans_le hchoice.U_le_floor
  have hnQ : n ≤ y * Q := by
    simpa [y, Q] using controlledPrime_target_le_y_mul_floor hchoice
  have hQlower : Real.rpow (n : ℝ) (133 / 400 : ℝ) < (Q : ℝ) := by
    have hnQR : (n : ℝ) ≤ (y : ℝ) * Q := by exact_mod_cast hnQ
    have hstrict : (n : ℝ) <
        Real.rpow (n : ℝ) (267 / 400 : ℝ) * Q :=
      hnQR.trans_lt (mul_lt_mul_of_pos_right hyUpper (by exact_mod_cast hQ))
    have hsplit : (n : ℝ) =
        Real.rpow (n : ℝ) (267 / 400 : ℝ) *
          Real.rpow (n : ℝ) (133 / 400 : ℝ) := by
      calc
        (n : ℝ) = Real.rpow (n : ℝ) 1 := (Real.rpow_one _).symm
        _ = Real.rpow (n : ℝ) ((267 / 400 : ℝ) + (133 / 400 : ℝ)) := by
          norm_num
        _ = _ := Real.rpow_add hnR _ _
    apply lt_of_mul_lt_mul_left (a := Real.rpow (n : ℝ) (267 / 400 : ℝ))
    · calc
        _ = (n : ℝ) := hsplit.symm
        _ < _ := hstrict
    · exact Real.rpow_nonneg hnR.le _
  have hpRoom : 16 * controlledPrimeU n + 256 ≤ p := by
    simpa [y, Q, p] using hpool.1
  have hp256 : 256 ≤ p := by omega
  have hQp : Q < 16 * controlledPrimeEll * p := by
    have hrem : Q < (p + 1) * (8 * controlledPrimeEll) := by
      dsimp [p, sharpUniformPoolFloor]
      simpa [mul_comm] using Nat.lt_mul_div_succ Q
        (by norm_num [controlledPrimeEll] : 0 < 8 * controlledPrimeEll)
    calc
      Q < (p + 1) * (8 * controlledPrimeEll) := hrem
      _ ≤ (2 * p) * (8 * controlledPrimeEll) := by gcongr; omega
      _ = 16 * controlledPrimeEll * p := by ring
  have hpLower : Real.rpow (n : ℝ) (133 / 400 : ℝ) /
      (16 * controlledPrimeEll : ℝ) < (p : ℝ) := by
    apply (div_lt_iff₀ (by
      norm_num [controlledPrimeEll] : (0 : ℝ) < 16 * controlledPrimeEll)).2
    have hQpR : (Q : ℝ) < (16 * controlledPrimeEll : ℝ) * p := by
      exact_mod_cast hQp
    exact hQlower.trans (by simpa [mul_comm] using hQpR)
  have hRLower : Real.rpow (n : ℝ) (133 / 400 : ℝ) /
      (256 * controlledPrimeEll : ℝ) < (R : ℝ) := by
    have hrem : p < (R + 1) * 8 := by
      change p < (p / 8 + 1) * 8
      simpa [mul_comm] using Nat.lt_mul_div_succ p (by norm_num : 0 < 8)
    have hRpos : 0 < R := by
      change 0 < p / 8
      exact Nat.div_pos (by omega) (by norm_num)
    have hpR : p < 16 * R := by
      calc
        p < (R + 1) * 8 := hrem
        _ ≤ (2 * R) * 8 := by gcongr; omega
        _ = 16 * R := by ring
    apply (div_lt_iff₀ (by
      norm_num [controlledPrimeEll] : (0 : ℝ) < 256 * controlledPrimeEll)).2
    have hbase : Real.rpow (n : ℝ) (133 / 400 : ℝ) <
        (16 * controlledPrimeEll : ℝ) * p := by
      simpa [mul_comm] using
        (div_lt_iff₀ (by
          norm_num [controlledPrimeEll] : (0 : ℝ) < 16 * controlledPrimeEll)).mp
          hpLower
    have hpRreal : (p : ℝ) < 16 * R := by exact_mod_cast hpR
    calc
      _ < (16 * controlledPrimeEll : ℝ) * p := hbase
      _ < (16 * controlledPrimeEll : ℝ) * (16 * R) :=
        mul_lt_mul_of_pos_left hpRreal (by norm_num [controlledPrimeEll])
      _ = (R : ℝ) * (256 * controlledPrimeEll) := by ring
  have hL : (L : ℝ) ≤ 200 * Real.rpow (n : ℝ) (1 / 100 : ℝ) := by
    have hfloor : (L : ℝ) ≤
        Real.rpow (n : ℝ) (1 / 100 : ℝ) := by
      have hexp : (1 / (10 * (10 : ℕ) : ℝ)) = (1 / 100 : ℝ) := by
        norm_num
      have hf := Nat.floor_le
        (Real.rpow_nonneg hnR.le (1 / (10 * (10 : ℕ) : ℝ)))
      have hrpow : Real.rpow (n : ℝ) (1 / (10 * (10 : ℕ) : ℝ)) =
          Real.rpow (n : ℝ) (1 / 100 : ℝ) := by
        exact congrArg (Real.rpow (n : ℝ)) hexp
      simpa only [L, upperSieveCutoff, Real.rpow_eq_pow] using hf.trans_eq hrpow
    have hp0 := Real.rpow_nonneg hnR.le (1 / 100 : ℝ)
    nlinarith
  have hD : (D : ℝ) ≤ Real.rpow (n : ℝ) (1 / 20 : ℝ) := by
    have hfloor : (upperSieveCutoff (4 * S) n : ℝ) ≤
        Real.rpow (n : ℝ) (1 / (40 * S : ℝ)) := by
      have hSr : (S : ℝ) ≠ 0 := by exact_mod_cast hS.ne'
      have hexp : (1 / (10 * ((4 * S : ℕ) : ℝ))) =
          (1 / (40 * S : ℝ)) := by
        push_cast
        field_simp [hSr]
        ring
      have hf := Nat.floor_le
        (Real.rpow_nonneg hnR.le (1 / (10 * ((4 * S : ℕ) : ℝ))))
      have hrpow : Real.rpow (n : ℝ) (1 / (10 * ((4 * S : ℕ) : ℝ))) =
          Real.rpow (n : ℝ) (1 / (40 * S : ℝ)) := by
        exact congrArg (Real.rpow (n : ℝ)) hexp
      simpa only [upperSieveCutoff, Real.rpow_eq_pow] using hf.trans_eq hrpow
    dsimp [D]
    norm_num only [Nat.cast_pow]
    calc
      ((upperSieveCutoff (4 * S) n : ℝ) ^ S) ^ 2 =
          (upperSieveCutoff (4 * S) n : ℝ) ^ (2 * S) := by
        calc
          ((upperSieveCutoff (4 * S) n : ℝ) ^ S) ^ 2 =
              (upperSieveCutoff (4 * S) n : ℝ) ^ (S * 2) :=
            (pow_mul _ _ _).symm
          _ = _ := by congr 1; omega
      _ ≤ (Real.rpow (n : ℝ) (1 / (40 * S : ℝ))) ^ (2 * S) := by
        exact pow_le_pow_left₀ (by positivity) hfloor (2 * S)
      _ = Real.rpow (n : ℝ) ((1 / (40 * S : ℝ)) * (2 * S : ℕ)) := by
        rw [← Real.rpow_natCast]
        exact (Real.rpow_mul hnR.le _ _).symm
      _ = Real.rpow (n : ℝ) (1 / 20 : ℝ) := by
        congr 1
        push_cast
        field_simp
        ring
  have hLD : ((L * D : ℕ) : ℝ) ≤
      200 * Real.rpow (n : ℝ) (3 / 50 : ℝ) := by
    norm_num only [Nat.cast_mul]
    have hD0 : (0 : ℝ) ≤ D := by positivity
    have hUpper0 : (0 : ℝ) ≤
        200 * Real.rpow (n : ℝ) (1 / 100 : ℝ) := by
      exact mul_nonneg (by norm_num) (Real.rpow_nonneg hnR.le _)
    have hmul := mul_le_mul hL hD hD0 hUpper0
    calc
      (L : ℝ) * D ≤
          (200 * Real.rpow (n : ℝ) (1 / 100 : ℝ)) *
            Real.rpow (n : ℝ) (1 / 20 : ℝ) := hmul
      _ = 200 * Real.rpow (n : ℝ) (3 / 50 : ℝ) := by
        have heq : Real.rpow (n : ℝ) (1 / 100 : ℝ) *
            Real.rpow (n : ℝ) (1 / 20 : ℝ) =
              Real.rpow (n : ℝ) (3 / 50 : ℝ) := by
          convert (Real.rpow_add hnR (1 / 100 : ℝ) (1 / 20 : ℝ)).symm using 1 <;>
            norm_num
        calc
          200 * Real.rpow (n : ℝ) (1 / 100 : ℝ) *
              Real.rpow (n : ℝ) (1 / 20 : ℝ) =
              200 * (Real.rpow (n : ℝ) (1 / 100 : ℝ) *
                Real.rpow (n : ℝ) (1 / 20 : ℝ)) := by ring
          _ = _ := by rw [heq]
  have hcube : (((L * D) ^ 3 : ℕ) : ℝ) ≤
      8000000 * Real.rpow (n : ℝ) (9 / 50 : ℝ) := by
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (L * D : ℕ))
      hLD 3
    norm_num only [Nat.cast_pow]
    calc
      ((L * D : ℕ) : ℝ) ^ 3 ≤
          (200 * Real.rpow (n : ℝ) (3 / 50 : ℝ)) ^ 3 := hp
      _ = 8000000 * Real.rpow (n : ℝ) (9 / 50 : ℝ) := by
        have heq : (Real.rpow (n : ℝ) (3 / 50 : ℝ)) ^ 3 =
            Real.rpow (n : ℝ) (9 / 50 : ℝ) := by
          calc
            _ = Real.rpow (Real.rpow (n : ℝ) (3 / 50 : ℝ)) (3 : ℝ) :=
              (Real.rpow_natCast _ 3).symm
            _ = Real.rpow (n : ℝ) ((3 / 50 : ℝ) * 3) :=
              (Real.rpow_mul hnR.le _ _).symm
            _ = _ := by norm_num
        rw [mul_pow, heq]
        norm_num
  have hsplit : Real.rpow (n : ℝ) (133 / 400 : ℝ) =
      Real.rpow (n : ℝ) (9 / 50 : ℝ) *
        Real.rpow (n : ℝ) (61 / 400 : ℝ) := by
    convert Real.rpow_add hnR (9 / 50 : ℝ) (61 / 400 : ℝ) using 1 <;>
      norm_num
  have hmain : (((L * D) ^ 3 : ℕ) : ℝ) < (R : ℝ) := by
    calc
      (((L * D) ^ 3 : ℕ) : ℝ) ≤
          8000000 * Real.rpow (n : ℝ) (9 / 50 : ℝ) := hcube
      _ ≤ Real.rpow (n : ℝ) (133 / 400 : ℝ) /
          (256 * controlledPrimeEll : ℝ) := by
        rw [hsplit]
        apply (le_div_iff₀ (by
          norm_num [controlledPrimeEll] : (0 : ℝ) < 256 * controlledPrimeEll)).2
        dsimp [K] at hpLarge
        have hp0 := Real.rpow_nonneg hnR.le (9 / 50 : ℝ)
        have hmul := mul_le_mul_of_nonneg_left hpLarge hp0
        simpa [mul_assoc, mul_comm, mul_left_comm] using hmul
      _ < (R : ℝ) := hRLower
  exact_mod_cast hmain.le

private lemma resolutionScaleTotient_cube_identity
    {n : ℕ} (hn : 0 < n)
    (hL : 0 < Real.log (n : ℝ))
    (hLL : 0 < Real.log (Real.log (n : ℝ))) :
    (resolutionScale n * (Nat.totient n : ℝ)) ^ 3 *
        Real.log (n : ℝ) * Real.log (Real.log (n : ℝ)) ^ 2 =
      (n : ℝ) ^ 4 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hphi : (0 : ℝ) < Nat.totient n := by
    exact_mod_cast Nat.totient_pos.mpr hn
  have hscale : 0 < resolutionScale n := by
    rw [resolutionScale]
    exact div_pos
      (mul_pos (Real.rpow_pos_of_pos hnR _)
        (div_pos hnR hphi))
      (mul_pos (Real.rpow_pos_of_pos hL _)
        (Real.rpow_pos_of_pos hLL _))
  have hden : 0 < Real.log (n : ℝ) *
      Real.log (Real.log (n : ℝ)) ^ 2 * resolutionScale n ^ 2 := by
    positivity
  have hid := resolutionScale_mainTerm_identity hn hL hLL
  have hid' :
      (n : ℝ) * ((n : ℝ) / Nat.totient n) ^ 3 =
        resolutionScale n *
          (Real.log (n : ℝ) *
            Real.log (Real.log (n : ℝ)) ^ 2 *
              resolutionScale n ^ 2) :=
    (div_eq_iff hden.ne').mp hid
  calc
    (resolutionScale n * (Nat.totient n : ℝ)) ^ 3 *
          Real.log (n : ℝ) * Real.log (Real.log (n : ℝ)) ^ 2 =
        (Nat.totient n : ℝ) ^ 3 *
          (resolutionScale n *
            (Real.log (n : ℝ) *
              Real.log (Real.log (n : ℝ)) ^ 2 *
                resolutionScale n ^ 2)) := by ring
    _ = (Nat.totient n : ℝ) ^ 3 *
        ((n : ℝ) * ((n : ℝ) / Nat.totient n) ^ 3) := by
      rw [← hid']
    _ = (n : ℝ) ^ 4 := by
      field_simp [hphi.ne']

private theorem exists_eventually_sharp_main_scale
    (D : ℝ) (hD : 0 < D) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ᶠ n : ℕ in atTop,
        let y := initialLowerY n (lowerColorCount c n)
        D * (y : ℝ) ^ 3 * Real.log (Real.log (n : ℝ)) <
          (n : ℝ) ^ 2 * Real.log (n : ℝ) := by
  let c : ℝ := 1 / (1000 * (D + 1) ^ 2)
  have hDone : 1 < D + 1 := by linarith
  have hden : 0 < 1000 * (D + 1) ^ 2 := by positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by
    dsimp [c]
    apply (div_le_one hden).2
    nlinarith [sq_nonneg D]
  have hDpow : D ^ 2 < (D + 1) ^ 6 := by
    have htwo : D ^ 2 < (D + 1) ^ 2 :=
      pow_lt_pow_left₀ (by linarith : D < D + 1) hD.le (by norm_num)
    exact htwo.trans_le
      (pow_le_pow_right₀ hDone.le (by norm_num : 2 ≤ 6))
  have hcoeff : D ^ 2 * ((400 / 3 : ℝ) * c) ^ 3 < 1 := by
    have hratio : D ^ 2 / (D + 1) ^ 6 < 1 :=
      (div_lt_one (pow_pos (by positivity : 0 < D + 1) 6)).2 hDpow
    calc
      D ^ 2 * ((400 / 3 : ℝ) * c) ^ 3 =
          (8 / 3375 : ℝ) * (D ^ 2 / (D + 1) ^ 6) := by
        dsimp [c]
        field_simp
        ring
      _ < (8 / 3375 : ℝ) * 1 :=
        mul_lt_mul_of_pos_left hratio (by norm_num)
      _ < 1 := by norm_num
  refine ⟨c, hc, hc1, ?_⟩
  filter_upwards [eventually_initialLowerY_sq_lt_scale_mul_at hc hc1,
    eventually_gt_atTop 0,
    tendsto_log_coe_at_top.eventually (eventually_gt_atTop 0),
    tendsto_log_log_coe_at_top.eventually (eventually_gt_atTop 0)] with
      n hySq hn hL hLL
  dsimp only at hySq ⊢
  let y := initialLowerY n (lowerColorCount c n)
  let H := resolutionScale n * (Nat.totient n : ℝ)
  let L := Real.log (n : ℝ)
  let LL := Real.log L
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hH : 0 < H := by
    dsimp [H]
    have hphi : (0 : ℝ) < Nat.totient n := by
      exact_mod_cast Nat.totient_pos.mpr hn
    have hscale : 0 < resolutionScale n := by
      rw [resolutionScale]
      exact div_pos
        (mul_pos (Real.rpow_pos_of_pos hnR _)
          (div_pos hnR hphi))
        (mul_pos (Real.rpow_pos_of_pos hL _)
          (Real.rpow_pos_of_pos hLL _))
    positivity
  have hySq' : (y : ℝ) ^ 2 < (400 / 3 : ℝ) * c * H * L := by
    simpa [y, H, L] using hySq
  have hySix : (y : ℝ) ^ 6 <
      ((400 / 3 : ℝ) * c) ^ 3 * H ^ 3 * L ^ 3 := by
    have hp := pow_lt_pow_left₀ hySq'
      (sq_nonneg (y : ℝ)) (by norm_num : 3 ≠ 0)
    calc
      (y : ℝ) ^ 6 = ((y : ℝ) ^ 2) ^ 3 := by ring
      _ < (((400 / 3 : ℝ) * c) * H * L) ^ 3 := hp
      _ = _ := by ring
  have hid : H ^ 3 * L * LL ^ 2 = (n : ℝ) ^ 4 := by
    simpa [H, L, LL] using resolutionScaleTotient_cube_identity hn hL hLL
  have hsquare :
      (D * (y : ℝ) ^ 3 * LL) ^ 2 <
        ((n : ℝ) ^ 2 * L) ^ 2 := by
    calc
      (D * (y : ℝ) ^ 3 * LL) ^ 2 =
          D ^ 2 * ((y : ℝ) ^ 6 * LL ^ 2) := by ring
      _ < D ^ 2 *
          (((400 / 3 : ℝ) * c) ^ 3 * H ^ 3 * L ^ 3 * LL ^ 2) := by
        gcongr
      _ = (D ^ 2 * ((400 / 3 : ℝ) * c) ^ 3) *
          (H ^ 3 * L * LL ^ 2) * L ^ 2 := by ring
      _ = (D ^ 2 * ((400 / 3 : ℝ) * c) ^ 3) *
          (n : ℝ) ^ 4 * L ^ 2 := by rw [hid]
      _ < (n : ℝ) ^ 4 * L ^ 2 := by
        have hright : 0 < (n : ℝ) ^ 4 * L ^ 2 := by positivity
        nlinarith
      _ = ((n : ℝ) ^ 2 * L) ^ 2 := by ring
  have hleft : 0 ≤ D * (y : ℝ) ^ 3 * LL := by positivity
  have hright : 0 ≤ (n : ℝ) ^ 2 * L := by positivity
  nlinarith [sq_nonneg
    (D * (y : ℝ) ^ 3 * LL - (n : ℝ) ^ 2 * L)]

private lemma eventually_sharp_error_scale_at
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (D : ℝ) (hD : 0 < D) :
    ∀ᶠ n : ℕ in atTop,
      let y := initialLowerY n (lowerColorCount c n)
      D * (y : ℝ) ^ 3 <
        (n : ℝ) ^ 2 * (upperSieveCutoff 10 n : ℝ) := by
  have hpTop : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (3 / 400 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hqTop : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (1 / 100 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 0,
    eventually_initialLowerY_lt_rpow_267_400_at hc hc1,
    hpTop.eventually (eventually_ge_atTop (2 * D)),
    hqTop.eventually (eventually_ge_atTop (2 : ℝ))] with
      n hn hyUpper hpLarge hqLarge
  dsimp only at hyUpper ⊢
  let y := initialLowerY n (lowerColorCount c n)
  let q := upperSieveCutoff 10 n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hyCube : (y : ℝ) ^ 3 <
      Real.rpow (n : ℝ) (801 / 400 : ℝ) := by
    have hp := pow_lt_pow_left₀ hyUpper (by positivity : (0 : ℝ) ≤ y)
      (by norm_num : 3 ≠ 0)
    calc
      (y : ℝ) ^ 3 <
          (Real.rpow (n : ℝ) (267 / 400 : ℝ)) ^ 3 := hp
      _ = Real.rpow (n : ℝ) (801 / 400 : ℝ) := by
        calc
          _ = Real.rpow (Real.rpow (n : ℝ) (267 / 400 : ℝ))
              (3 : ℝ) := (Real.rpow_natCast _ 3).symm
          _ = Real.rpow (n : ℝ) ((267 / 400 : ℝ) * 3) :=
            (Real.rpow_mul hnR.le _ _).symm
          _ = _ := by norm_num
  have hqLower : Real.rpow (n : ℝ) (1 / 100 : ℝ) / 2 ≤ (q : ℝ) := by
    have hexp : (1 / (10 * (10 : ℕ) : ℝ)) = (1 / 100 : ℝ) := by
      norm_num
    have hxFloor : Real.rpow (n : ℝ) (1 / 100 : ℝ) < (q : ℝ) + 1 := by
      have hx := Nat.lt_floor_add_one
        (Real.rpow (n : ℝ) (1 / (10 * (10 : ℕ) : ℝ)))
      have hrpow : Real.rpow (n : ℝ) (1 / (10 * (10 : ℕ) : ℝ)) =
          Real.rpow (n : ℝ) (1 / 100 : ℝ) := by
        exact congrArg (Real.rpow (n : ℝ)) hexp
      calc
        Real.rpow (n : ℝ) (1 / 100 : ℝ) =
            Real.rpow (n : ℝ) (1 / (10 * (10 : ℕ) : ℝ)) := hrpow.symm
        _ < (q : ℝ) + 1 := by
          simpa only [q, upperSieveCutoff, Real.rpow_eq_pow] using hx
    have hqPos : 0 < q := by
      dsimp [q, upperSieveCutoff]
      apply Nat.floor_pos.mpr
      change 1 ≤ Real.rpow (n : ℝ) (1 / (10 * (10 : ℕ) : ℝ))
      rw [hexp]
      linarith
    have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hqPos
    linarith
  have hpowSplit : Real.rpow (n : ℝ) (1 / 100 : ℝ) =
      Real.rpow (n : ℝ) (1 / 400 : ℝ) *
        Real.rpow (n : ℝ) (3 / 400 : ℝ) := by
    convert Real.rpow_add hnR (1 / 400 : ℝ) (3 / 400 : ℝ) using 1 <;>
      norm_num
  have hsmall : D * Real.rpow (n : ℝ) (1 / 400 : ℝ) ≤
      Real.rpow (n : ℝ) (1 / 100 : ℝ) / 2 := by
    rw [hpowSplit]
    have hp0 := Real.rpow_nonneg hnR.le (1 / 400 : ℝ)
    nlinarith [mul_le_mul_of_nonneg_left hpLarge hp0]
  have hmainSplit : Real.rpow (n : ℝ) (801 / 400 : ℝ) =
      (n : ℝ) ^ 2 * Real.rpow (n : ℝ) (1 / 400 : ℝ) := by
    calc
      _ = Real.rpow (n : ℝ) ((2 : ℝ) + (1 / 400 : ℝ)) := by norm_num
      _ = Real.rpow (n : ℝ) 2 *
          Real.rpow (n : ℝ) (1 / 400 : ℝ) :=
        Real.rpow_add hnR _ _
      _ = _ := by
        rw [show Real.rpow (n : ℝ) 2 = (n : ℝ) ^ 2 by
          simpa only [Real.rpow_eq_pow] using Real.rpow_two (n : ℝ)]
  calc
    D * (y : ℝ) ^ 3 <
        D * Real.rpow (n : ℝ) (801 / 400 : ℝ) :=
      mul_lt_mul_of_pos_left hyCube hD
    _ = (n : ℝ) ^ 2 *
        (D * Real.rpow (n : ℝ) (1 / 400 : ℝ)) := by
      rw [hmainSplit]
      ring
    _ ≤ (n : ℝ) ^ 2 *
        (Real.rpow (n : ℝ) (1 / 100 : ℝ) / 2) := by
      gcongr
    _ ≤ (n : ℝ) ^ 2 * (q : ℝ) := by gcongr

private lemma sharp_sieve_reverse_of_scales
    {N Y E R q L LL a B P x : ℝ}
    (hN : 0 < N) (hY : 0 < Y) (hq : 0 < q)
    (hL : 0 < L) (hLL : 0 ≤ LL)
    (ha : 0 < a) (hB : 0 < B) (hP : 0 < P)
    (hE : 0 ≤ E) (hx : 0 ≤ x)
    (hEn : E * N ≤ 65536 * Y ^ 2)
    (hNR : N < P * Y * R)
    (hxBound : x ≤ B * LL / L)
    (hmain : (2 * a * 65536 * P * B) * Y ^ 3 * LL < N ^ 2 * L)
    (herror : (2 * a * 65536 * P) * Y ^ 3 < N ^ 2 * q) :
    (a * E) * (x + 1 / q) < R := by
  have hEUpper : E ≤ 65536 * Y ^ 2 / N := by
    exact (le_div_iff₀ hN).2 (by simpa [mul_comm] using hEn)
  have hRLower : N / (P * Y) < R := by
    apply (div_lt_iff₀ (mul_pos hP hY)).2
    nlinarith [hNR]
  have hmainTarget :
      a * (65536 * Y ^ 2 / N) * (B * LL / L) <
        N / (2 * P * Y) := by
    rw [show a * (65536 * Y ^ 2 / N) * (B * LL / L) =
        (a * 65536 * B * Y ^ 2 * LL) / (N * L) by
      field_simp [hN.ne', hL.ne']]
    rw [div_lt_div_iff₀ (mul_pos hN hL)
      (by positivity : 0 < 2 * P * Y)]
    nlinarith [hmain]
  have herrorTarget :
      a * (65536 * Y ^ 2 / N) * (1 / q) <
        N / (2 * P * Y) := by
    rw [show a * (65536 * Y ^ 2 / N) * (1 / q) =
        (a * 65536 * Y ^ 2) / (N * q) by
      field_simp [hN.ne', hq.ne']]
    rw [div_lt_div_iff₀ (mul_pos hN hq)
      (by positivity : 0 < 2 * P * Y)]
    nlinarith [herror]
  have hmainPart : a * E * x < N / (2 * P * Y) := by
    calc
      a * E * x ≤ a * (65536 * Y ^ 2 / N) * x := by gcongr
      _ ≤ a * (65536 * Y ^ 2 / N) * (B * LL / L) := by gcongr
      _ < _ := hmainTarget
  have herrorPart : a * E * (1 / q) < N / (2 * P * Y) := by
    calc
      a * E * (1 / q) ≤
          a * (65536 * Y ^ 2 / N) * (1 / q) := by gcongr
      _ < _ := herrorTarget
  calc
    (a * E) * (x + 1 / q) = a * E * x + a * E * (1 / q) := by ring
    _ < N / (2 * P * Y) + N / (2 * P * Y) :=
      add_lt_add hmainPart herrorPart
    _ = N / (P * Y) := by field_simp [hP.ne', hY.ne']; ring
    _ < R := hRLower

private theorem exists_eventually_sharp_sieve_reverse
    {A C CT : ℝ} (hA : 1 ≤ A) (hC : 0 < C) (hCT : 0 < CT)
    {S : ℕ} (hS : 101 ≤ S) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ᶠ n : ℕ in atTop,
        let y := initialLowerY n (lowerColorCount c n)
        let Q := controlledPrimeExtractedFloorTwelve n y
        (((192 * 48 : ℕ) : ℝ) * sharpUniformIncrementCeiling y Q) *
            (((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
                (C * (CT * Real.log (Real.log (n : ℝ))) /
                  Real.log (upperSieveCutoff (4 * S) n : ℝ))) +
              1 / (upperSieveCutoff 10 n : ℝ)) <
          sharpUniformRemainderFloor Q controlledPrimeEll := by
  let a : ℝ := (192 * 48 : ℕ)
  let P : ℝ := 256 * controlledPrimeEll
  let B : ℝ :=
    (1 + 4 * A / 3) * C * CT * (80 * S)
  let Dmain : ℝ := 2 * a * 65536 * P * B
  let Derror : ℝ := 2 * a * 65536 * P
  have ha : 0 < a := by dsimp [a]; norm_num
  have hP : 0 < P := by dsimp [P]; norm_num [controlledPrimeEll]
  have hAfac : 0 < 1 + 4 * A / 3 := by nlinarith
  have hB : 0 < B := by dsimp [B]; positivity
  have hDmain : 0 < Dmain := by dsimp [Dmain]; positivity
  have hDerror : 0 < Derror := by dsimp [Derror]; positivity
  obtain ⟨c, hc, hc1, hmainEventually⟩ :=
    exists_eventually_sharp_main_scale Dmain hDmain
  refine ⟨c, hc, hc1, ?_⟩
  filter_upwards [hmainEventually,
    eventually_sharp_error_scale_at hc hc1 Derror hDerror,
    eventually_controlledPrimeTwelve_choice_numerics_at hc hc1,
    eventually_sharp_pool_and_size_rooms_at hc hc1,
    eventually_log_upperSieveCutoff_lower
      (show 0 < 4 * S by omega),
    (upperSieveCutoff_tendsto_atTop (show 0 < 4 * S by omega)).eventually
      (eventually_ge_atTop 2),
    (upperSieveCutoff_tendsto_atTop (show 0 < 10 by omega)).eventually
      (eventually_ge_atTop 1),
    tendsto_log_coe_at_top.eventually (eventually_gt_atTop 0),
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop 0)] with
      n hmainScale herrorScale hchoice hpool hcutLog hcutTwo hqPosNat
        hlog hloglog
  dsimp only at hmainScale herrorScale hchoice hpool ⊢
  let y := initialLowerY n (lowerColorCount c n)
  let Q := controlledPrimeExtractedFloorTwelve n y
  let p := sharpUniformPoolFloor Q controlledPrimeEll
  let R := sharpUniformRemainderFloor Q controlledPrimeEll
  let E := sharpUniformIncrementCeiling y Q
  let q := upperSieveCutoff 10 n
  let cutoff := upperSieveCutoff (4 * S) n
  let eta : ℝ := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
  let x : ℝ := (1 + eta) *
    (C * (CT * Real.log (Real.log (n : ℝ))) /
      Real.log (cutoff : ℝ))
  have hn : 0 < n := by
    by_contra hn0
    have : n = 0 := Nat.eq_zero_of_not_pos hn0
    subst n
    norm_num at hlog
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hy : 0 < y := hchoice.U_pos.trans_le hchoice.U_le_y
  have hQ : 0 < Q := hchoice.U_pos.trans_le hchoice.U_le_floor
  have hpRoom : 256 ≤ p := by
    have hbase : 256 ≤
        sharpUniformPoolFloor
          (controlledPrimeExtractedFloorTwelve n
            (initialLowerY n (lowerColorCount c n))) controlledPrimeEll := by
      omega
    simpa only [p, Q, y] using hbase
  have hpPos : 0 < p := by omega
  have hRPos : 0 < R := by
    change 0 < p / 8
    exact Nat.div_pos (by omega) (by norm_num)
  have hnQ : n ≤ y * Q := by
    simpa [y, Q] using controlledPrime_target_le_y_mul_floor hchoice
  have hQp : Q < 16 * controlledPrimeEll * p := by
    have hrem : Q < (p + 1) * (8 * controlledPrimeEll) := by
      dsimp [p, sharpUniformPoolFloor]
      simpa [mul_comm] using Nat.lt_mul_div_succ Q
        (by norm_num [controlledPrimeEll] : 0 < 8 * controlledPrimeEll)
    calc
      Q < (p + 1) * (8 * controlledPrimeEll) := hrem
      _ ≤ (2 * p) * (8 * controlledPrimeEll) := by gcongr; omega
      _ = 16 * controlledPrimeEll * p := by ring
  have hpR : p < 16 * R := by
    have hrem : p < (R + 1) * 8 := by
      change p < (p / 8 + 1) * 8
      simpa [mul_comm] using Nat.lt_mul_div_succ p (by norm_num : 0 < 8)
    calc
      p < (R + 1) * 8 := hrem
      _ ≤ (2 * R) * 8 := by gcongr; omega
      _ = 16 * R := by ring
  have hnRemainder : (n : ℝ) < P * (y : ℝ) * (R : ℝ) := by
    have hNat : n < 256 * controlledPrimeEll * y * R := by
      calc
        n ≤ y * Q := hnQ
        _ < y * (16 * controlledPrimeEll * p) :=
          Nat.mul_lt_mul_of_pos_left hQp hy
        _ < y * (16 * controlledPrimeEll * (16 * R)) :=
          Nat.mul_lt_mul_of_pos_left
            (Nat.mul_lt_mul_of_pos_left hpR
              (by norm_num [controlledPrimeEll])) hy
        _ = 256 * controlledPrimeEll * y * R := by ring
    have hNatR : (n : ℝ) <
        (256 * controlledPrimeEll : ℕ) * (y : ℝ) * (R : ℝ) := by
      exact_mod_cast hNat
    norm_num [P, controlledPrimeEll] at hNatR ⊢
    exact hNatR
  have hEnNat : E * n ≤ 65536 * y ^ 2 := by
    have hEQ : E * Q ≤ 65536 * y := by
      dsimp [E, sharpUniformIncrementCeiling]
      exact Nat.div_mul_le_self _ _
    calc
      E * n ≤ E * (y * Q) := Nat.mul_le_mul_left E hnQ
      _ = y * (E * Q) := by ring
      _ ≤ y * (65536 * y) := Nat.mul_le_mul_left y hEQ
      _ = 65536 * y ^ 2 := by ring
  have hEn : (E : ℝ) * n ≤ 65536 * (y : ℝ) ^ 2 := by
    exact_mod_cast hEnNat
  have hcutPos : 0 < Real.log (cutoff : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hcutTwo
  have hqPos : (0 : ℝ) < q := by exact_mod_cast hqPosNat
  have hetaNonneg : 0 ≤ eta := by
    dsimp [eta]
    positivity
  have hetaBound : 1 + eta ≤ 1 + 4 * A / 3 := by
    dsimp [eta]
    have hpow : (1 / 4 : ℝ) ^ (S - 100) ≤ 1 := by
      exact pow_le_one₀ (by norm_num) (by norm_num)
    have hcoef : 0 ≤ 4 * A / 3 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hpow hcoef]
  have hcutLower : Real.log (n : ℝ) / (80 * (S : ℝ)) ≤
      Real.log (cutoff : ℝ) := by
    have hcoef : (1 / (20 * (4 * S : ℕ) : ℝ)) =
        1 / (80 * (S : ℝ)) := by
      push_cast
      field_simp
      ring
    calc
      Real.log (n : ℝ) / (80 * (S : ℝ)) =
          (1 / (20 * (4 * S : ℕ) : ℝ)) *
            Real.log (n : ℝ) := by rw [hcoef]; ring
      _ ≤ Real.log (cutoff : ℝ) := by simpa [cutoff] using hcutLog
  have hinvCut : 1 / Real.log (cutoff : ℝ) ≤
      (80 * (S : ℝ)) / Real.log (n : ℝ) := by
    have hleftPos : 0 < Real.log (n : ℝ) / (80 * (S : ℝ)) := by
      positivity
    have hinv := one_div_le_one_div_of_le hleftPos hcutLower
    calc
      1 / Real.log (cutoff : ℝ) ≤
          1 / (Real.log (n : ℝ) / (80 * (S : ℝ))) := hinv
      _ = _ := by field_simp [hlog.ne']
  have hxNonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hxBound : x ≤ B * Real.log (Real.log (n : ℝ)) /
      Real.log (n : ℝ) := by
    have hmult : 0 ≤
        (1 + eta) * C * CT * Real.log (Real.log (n : ℝ)) := by
      positivity
    calc
      x = ((1 + eta) * C * CT * Real.log (Real.log (n : ℝ))) *
          (1 / Real.log (cutoff : ℝ)) := by
        dsimp [x]
        ring
      _ ≤ ((1 + eta) * C * CT * Real.log (Real.log (n : ℝ))) *
          ((80 * (S : ℝ)) / Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hinvCut hmult
      _ ≤ (((1 + 4 * A / 3) * C * CT * (80 * (S : ℝ))) *
          Real.log (Real.log (n : ℝ))) / Real.log (n : ℝ) := by
        let t : ℝ := C * CT * Real.log (Real.log (n : ℝ)) *
          ((80 * (S : ℝ)) / Real.log (n : ℝ))
        have ht : 0 ≤ t := by dsimp [t]; positivity
        calc
          ((1 + eta) * C * CT * Real.log (Real.log (n : ℝ))) *
              ((80 * (S : ℝ)) / Real.log (n : ℝ)) =
            (1 + eta) * t := by dsimp [t]; ring
          _ ≤ (1 + 4 * A / 3) * t :=
            mul_le_mul_of_nonneg_right hetaBound ht
          _ = _ := by dsimp [t]; ring
      _ = B * Real.log (Real.log (n : ℝ)) /
          Real.log (n : ℝ) := by
        dsimp [B]
  have hmainScale' :
      (2 * a * 65536 * P * B) * (y : ℝ) ^ 3 *
          Real.log (Real.log (n : ℝ)) <
        (n : ℝ) ^ 2 * Real.log (n : ℝ) := by
    simpa [Dmain] using hmainScale
  have herrorScale' :
      (2 * a * 65536 * P) * (y : ℝ) ^ 3 <
        (n : ℝ) ^ 2 * (q : ℝ) := by
    simpa [Derror] using herrorScale
  have hresult := sharp_sieve_reverse_of_scales
    (N := (n : ℝ)) (Y := (y : ℝ)) (E := (E : ℝ))
    (R := (R : ℝ)) (q := (q : ℝ))
    (L := Real.log (n : ℝ))
    (LL := Real.log (Real.log (n : ℝ)))
    (a := a) (B := B) (P := P) (x := x)
    hnR (by exact_mod_cast hy) hqPos hlog hloglog ha hB hP
    (by positivity) hxNonneg hEn hnRemainder hxBound
    hmainScale' herrorScale'
  norm_num [a, E, x, eta, cutoff, q, Q, R, y] at hresult ⊢
  exact hresult

private lemma eventually_sharp_sieveCutoff_le_B_at
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    {S : ℕ} (hS : 101 ≤ S) :
    ∀ᶠ n : ℕ in atTop,
      let y := initialLowerY n (lowerColorCount c n)
      upperSieveCutoff (4 * S) n ≤ y / controlledPrimeU n := by
  have hpTop : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (101 / 200 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 0,
    eventually_rpow_sixteen_twentyfive_le_initialLowerY_at hc,
    hpTop.eventually (eventually_ge_atTop (1002 : ℝ))] with
      n hn hyLower hpLarge
  dsimp only
  let y := initialLowerY n (lowerColorCount c n)
  let cutoff := upperSieveCutoff (4 * S) n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hUpos := controlledPrimeU_pos hn
  have hUcast := (controlledPrimeU_cast_bounds n).2
  have hp8one : (1 : ℝ) ≤ Real.rpow (n : ℝ) (1 / 8 : ℝ) :=
    Real.one_le_rpow hnOne (by norm_num)
  have hUrough : (controlledPrimeU n : ℝ) <
      1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ) := by
    nlinarith
  have he : (1 / (10 * ((4 * S : ℕ) : ℝ))) ≤ (1 / 100 : ℝ) := by
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 100)
    push_cast
    nlinarith [show (101 : ℝ) ≤ S by exact_mod_cast hS]
  have hcutCast : (cutoff : ℝ) ≤
      Real.rpow (n : ℝ) (1 / 100 : ℝ) := by
    have hfloor : (cutoff : ℝ) ≤
        Real.rpow (n : ℝ) (1 / (10 * ((4 * S : ℕ) : ℝ))) := by
      dsimp [cutoff, upperSieveCutoff]
      simpa only [Real.rpow_eq_pow] using
        Nat.floor_le (Real.rpow_nonneg hnR.le _)
    exact hfloor.trans (by
      simpa only [Real.rpow_eq_pow] using
        Real.rpow_le_rpow_of_exponent_le hnOne he)
  have hpowProduct : Real.rpow (n : ℝ) (1 / 100 : ℝ) *
      Real.rpow (n : ℝ) (1 / 8 : ℝ) =
        Real.rpow (n : ℝ) (27 / 200 : ℝ) := by
    convert (Real.rpow_add hnR (1 / 100 : ℝ) (1 / 8 : ℝ)).symm using 1 <;>
      norm_num
  have hpowSplit : Real.rpow (n : ℝ) (16 / 25 : ℝ) =
      Real.rpow (n : ℝ) (27 / 200 : ℝ) *
        Real.rpow (n : ℝ) (101 / 200 : ℝ) := by
    convert Real.rpow_add hnR (27 / 200 : ℝ) (101 / 200 : ℝ) using 1 <;>
      norm_num
  have hproduct : (cutoff : ℝ) * controlledPrimeU n < (y : ℝ) := by
    calc
      (cutoff : ℝ) * controlledPrimeU n ≤
          Real.rpow (n : ℝ) (1 / 100 : ℝ) * controlledPrimeU n := by
        gcongr
      _ <
          Real.rpow (n : ℝ) (1 / 100 : ℝ) *
            (1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ)) :=
        mul_lt_mul_of_pos_left hUrough (Real.rpow_pos_of_pos hnR _)
      _ = 1002 * Real.rpow (n : ℝ) (27 / 200 : ℝ) := by
        rw [← hpowProduct]
        ring
      _ ≤ Real.rpow (n : ℝ) (16 / 25 : ℝ) := by
        rw [hpowSplit]
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hpLarge
          (Real.rpow_nonneg hnR.le _)
      _ ≤ (y : ℝ) := hyLower
  apply (Nat.le_div_iff_mul_le hUpos).2
  exact_mod_cast hproduct.le

/-- The sharp CFP prime-pool theorem supplies the ordinary callback for the
canonical controlled ledger at one fixed positive resolution constant. -/
theorem exists_eventually_controlledPrimeOrdinarySource :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ᶠ n : ℕ in atTop,
        let colors := lowerColorCount c n
        let y := initialLowerY n colors
        ∃ hy : 2 * y < n,
          CFPControlledPrimeOrdinarySourceCompletion n colors y
            (controlledPrimeU n) (controlledPrimeB n y)
            (controlledPrimeL y) (controlledPrimeClassCapTwelve n y)
            controlledPrimeEll
            (primeStructuredBelowTarget n y (controlledPrimeU n) hy) := by
  obtain ⟨A, C, hA, hC, hsieve⟩ :=
    exists_growth_gt_of_stepBoundedLongProgressionCover_absorbed
  obtain ⟨CT, hCT, hratioEventually⟩ :=
    exists_eventually_mul_totientRatio_le_loglog
  obtain ⟨S, hS, hSlog⟩ := exists_upper_sieve_depth hA
  obtain ⟨c, hc, hc1, hreverseEventually⟩ :=
    exists_eventually_sharp_sieve_reverse hA hC hCT hS
  refine ⟨c, hc, hc1, ?_⟩
  filter_upwards [eventually_gt_atTop 0,
    eventually_controlledPrime_endpoint_parameters_at hc hc1,
    eventually_canonicalControlledPrimeNumericalLedger_at hc hc1,
    eventually_sharp_pool_and_size_rooms_at hc hc1,
    eventually_sharp_probability_at hc hc1,
    eventually_sharp_diversity_room_at hc,
    eventually_sharp_increment_and_growth_rooms_at hc hc1,
    eventually_sharp_growth_budget_at hc hc1,
    eventually_sharp_unsaturated_budget_at hc hc1,
    eventually_sharp_fiber_ambient_at hc,
    eventually_sharp_polynomial_reverse_at hc hc1,
    eventually_sharp_long_scale_at hc hc1 (show 0 < S by omega),
    hreverseEventually,
    eventually_sharp_sieveCutoff_le_B_at hc hc1 hS,
    (upperSieveCutoff_tendsto_atTop (show 0 < 4 * S by omega)).eventually
      (eventually_ge_atTop 2),
    (upperSieveCutoff_tendsto_atTop (show 0 < 10 by omega)).eventually
      (eventually_ge_atTop 1),
    hratioEventually,
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop 0)] with
      n hn hend hledger hpool hprob hdiversity hgrowth hbudget hunsaturated
        hfiber hpolynomial hlong hreverse hcut hcutTwo hqOne hratioN hloglog
  dsimp only at hend hledger hpool hprob hdiversity hgrowth hbudget hunsaturated hfiber hpolynomial hlong hreverse hcut ⊢
  let colors := lowerColorCount c n
  let y := initialLowerY n colors
  let U := controlledPrimeU n
  let Bcut := controlledPrimeB n y
  let L := controlledPrimeL y
  let M := controlledPrimeClassCapTwelve n y
  let Q := controlledPrimeExtractedFloorTwelve n y
  let cutoff := upperSieveCutoff (4 * S) n
  let sieveQ := upperSieveCutoff 10 n
  let ratio := CT * Real.log (Real.log (n : ℝ))
  have hyPos : 0 < y := hend.1.trans_le hend.2.1
  have hyTarget : 2 * y < n := by
    have hlarge : 140 * y ≤ n := by
      simpa [y, colors] using hend.2.2.2.2.2.2
    omega
  have htwoY : 2 * y ≤ n := hyTarget.le
  have hratioNonneg : 0 ≤ ratio := by dsimp [ratio]; positivity
  have hratioBound : ∀ step : ℕ, 0 < step → step ≤ 2 * y →
      ((n * step : ℕ) : ℝ) / Nat.totient (n * step) ≤ ratio := by
    intro step hstep hstepY
    exact hratioN step hstep (hstepY.trans htwoY)
  have hgrowthBudget : sharpUniformLogBudget y Q controlledPrimeEll ≤
      sharpUniformPoolFloor Q controlledPrimeEll / 16 := by
    have hb : sharpUniformLogBudget y Q controlledPrimeEll ≤
        sharpUniformPoolFloor Q controlledPrimeEll / 64 := by
      simpa [y, colors, Q] using hbudget
    exact hb.trans (Nat.div_le_div_left (by omega) (by omega))
  have hrooms : CFPPrimePoolSharpUniformRooms A C ratio n S cutoff sieveQ
      y U Q M controlledPrimeEll :=
    { ell_pos := by norm_num [controlledPrimeEll]
      U_pos := hend.1
      pool_room := hpool.1
      z_room := hpool.2.1
      M_le_y := hpool.2.2
      probability := hprob
      diversity_room := hdiversity
      increment_below := hgrowth.1
      growth_ambient := hgrowth.2
      growth_budget := hgrowthBudget
      unsaturated_budget := hunsaturated
      fiber_ambient := hfiber
      polynomial_reverse := hpolynomial
      A_ge_one := hA
      C_pos := hC
      n_pos := hn
      sieveCutoff_ge := hcutTwo
      sieveLevel_ge := hS
      sieveQ_pos := hqOne
      log_bound := hSlog
      ratio_nonneg := hratioNonneg
      ratio_bound := hratioBound
      long_scale := hlong
      sieve_reverse := hreverse }
  have hsharp : ∀ d z : ℕ, 0 < d → d ≤ U → Q ≤ z → z ≤ M →
      CFPPrimePoolSharpNumerics A C ratio n S cutoff sieveQ
        y U z controlledPrimeEll d := by
    intro d z hd hdU hQz hzM
    exact hrooms.toSharpNumerics hd hdU hQz hzM
  refine ⟨hyTarget, ?_⟩
  exact controlledPrimeOrdinarySourceCompletion_of_sharp_post
    A C ratio hsieve hledger hcut hsharp

private lemma directPrime_hundredth_error_budgets
    {n y U : ℕ} (hn : 0 < n) (hlogy : 0 < Real.log (y : ℝ))
    (htailSimple : (100 : ℝ) * n.divisors.card ≤ U + 1)
    (hdeleteSimple : (100 : ℝ) * U * n.divisors.card *
      Real.log (y : ℝ) ≤ y) :
    (n.divisors.card : ℝ) / (U + 1) ≤
        (1 / 100 : ℝ) * ((n : ℝ) / Nat.totient n) ∧
      ((boundedTargetDivisors n U).card : ℝ) * n.primeFactors.card ≤
        ((n : ℝ) / Nat.totient n) * (y : ℝ) /
          (100 * Real.log (y : ℝ)) := by
  have hphi : Nat.totient n ≤ n := Nat.totient_le n
  have hphiPos : (0 : ℝ) < Nat.totient n := by
    exact_mod_cast Nat.totient_pos.mpr hn
  have hratio : (1 : ℝ) ≤ (n : ℝ) / Nat.totient n := by
    rw [le_div_iff₀ hphiPos]
    simpa using (Nat.cast_le.mpr hphi : (Nat.totient n : ℝ) ≤ n)
  have hUden : (0 : ℝ) < U + 1 := by positivity
  constructor
  · calc
      (n.divisors.card : ℝ) / (U + 1) ≤ 1 / 100 := by
        rw [div_le_iff₀ hUden]
        nlinarith
      _ ≤ (1 / 100 : ℝ) * ((n : ℝ) / Nat.totient n) := by
        nlinarith
  · have hcardB : ((boundedTargetDivisors n U).card : ℝ) ≤ U := by
      exact_mod_cast card_boundedTargetDivisors_le n U
    have hcardP : (n.primeFactors.card : ℝ) ≤ n.divisors.card := by
      exact_mod_cast primeFactors_card_le_divisors_card hn.ne'
    have hprod : ((boundedTargetDivisors n U).card : ℝ) *
        n.primeFactors.card ≤ (U : ℝ) * n.divisors.card := by
      exact mul_le_mul hcardB hcardP (by positivity) (by positivity)
    have hbase : (U : ℝ) * n.divisors.card ≤
        (y : ℝ) / (100 * Real.log (y : ℝ)) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 100 * Real.log (y : ℝ))]
      nlinarith
    calc
      ((boundedTargetDivisors n U).card : ℝ) * n.primeFactors.card ≤
          (U : ℝ) * n.divisors.card := hprod
      _ ≤ (y : ℝ) / (100 * Real.log (y : ℝ)) := hbase
      _ ≤ ((n : ℝ) / Nat.totient n) * (y : ℝ) /
          (100 * Real.log (y : ℝ)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hyLog : 0 ≤ (y : ℝ) * (100 * Real.log (y : ℝ)) := by
          positivity
        simpa only [one_mul, mul_assoc] using
          mul_le_mul_of_nonneg_right hratio hyLog

private lemma eventually_controlledPrime_count_error_budgets_at
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      let y := initialLowerY n (lowerColorCount c n)
      let U := controlledPrimeU n
      (n.divisors.card : ℝ) / (U + 1) ≤
          (1 / 100 : ℝ) * ((n : ℝ) / Nat.totient n) ∧
        ((boundedTargetDivisors n U).card : ℝ) * n.primeFactors.card ≤
          ((n : ℝ) / Nat.totient n) * (y : ℝ) /
            (100 * Real.log (y : ℝ)) := by
  let K : ℝ := 100 * 1002 * 100
  have hpTop : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (329 / 800 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 1,
    eventually_card_divisors_le_rpow_three_thirtytwo,
    eventually_rpow_sixteen_twentyfive_le_initialLowerY_at hc,
    eventually_controlledPrime_endpoint_parameters_at hc hc1,
    hpTop.eventually (eventually_ge_atTop K)] with
      n hn htau hyLower hend hpLarge
  dsimp only at hend ⊢
  let y := initialLowerY n (lowerColorCount c n)
  let U := controlledPrimeU n
  have hnPos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hnPos
  have hyPos : 0 < y := hend.1.trans_le hend.2.1
  have hyLe : y ≤ n := by
    have := hend.2.2.2.2.2.2
    omega
  have hlogy : 0 < Real.log (y : ℝ) := by
    apply Real.log_pos
    have : (1 : ℝ) < y := by
      have hone : (1 : ℝ) < Real.rpow (n : ℝ) (16 / 25 : ℝ) := by
        simpa only [Real.rpow_eq_pow, Real.one_rpow] using
          Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 1)
            (by exact_mod_cast hn : (1 : ℝ) < n)
            (by norm_num : (0 : ℝ) < 16 / 25)
      exact hone.trans_le hyLower
    exact_mod_cast this
  have hlogyLe : Real.log (y : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by exact_mod_cast hyPos) (by exact_mod_cast hyLe)
  have hlogPow : Real.log (n : ℝ) ≤
      100 * Real.rpow (n : ℝ) (1 / 100 : ℝ) := by
    simpa [div_eq_mul_inv, mul_comm] using Real.log_le_rpow_div hnR.le
      (show (0 : ℝ) < 1 / 100 by norm_num)
  have hUupper : (U : ℝ) ≤
      1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ) := by
    rw [Real.rpow_eq_pow]
    have hcast : (U : ℝ) <
        1000 * ((n : ℝ) ^ (1 / 8 : ℝ)) + 1 := by
      simpa only [U, Real.rpow_eq_pow] using
        (controlledPrimeU_cast_bounds n).2
    have hone : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 8 : ℝ) :=
      Real.one_le_rpow hnOne (by norm_num : (0 : ℝ) ≤ 1 / 8)
    nlinarith
  have hsplitTail : Real.rpow (n : ℝ) (1 / 8 : ℝ) =
      Real.rpow (n : ℝ) (3 / 32 : ℝ) *
        Real.rpow (n : ℝ) (1 / 32 : ℝ) := by
    convert Real.rpow_add hnR (3 / 32 : ℝ) (1 / 32 : ℝ) using 1 <;>
      norm_num
  have htailSimple : (100 : ℝ) * n.divisors.card ≤ U + 1 := by
    have hgapOne : (1 : ℝ) ≤ Real.rpow (n : ℝ) (1 / 32 : ℝ) :=
      Real.one_le_rpow hnOne (by norm_num)
    have hUlower := (controlledPrimeU_cast_bounds n).1
    dsimp [U] at hUlower ⊢
    calc
      (100 : ℝ) * n.divisors.card ≤
          100 * Real.rpow (n : ℝ) (3 / 32 : ℝ) := by gcongr
      _ ≤ 100 * Real.rpow (n : ℝ) (1 / 8 : ℝ) := by
        rw [hsplitTail]
        nlinarith [mul_le_mul_of_nonneg_left hgapOne
          (Real.rpow_nonneg hnR.le (3 / 32 : ℝ))]
      _ ≤ 1000 * Real.rpow (n : ℝ) (1 / 8 : ℝ) := by
        exact mul_le_mul_of_nonneg_right (by norm_num)
          (Real.rpow_nonneg hnR.le _)
      _ ≤ controlledPrimeU n := hUlower
      _ ≤ controlledPrimeU n + 1 := by norm_num
  have hpowProduct : Real.rpow (n : ℝ) (1 / 8 : ℝ) *
      Real.rpow (n : ℝ) (3 / 32 : ℝ) *
        Real.rpow (n : ℝ) (1 / 100 : ℝ) =
      Real.rpow (n : ℝ) (183 / 800 : ℝ) := by
    have haddOne : Real.rpow (n : ℝ) (1 / 8 : ℝ) *
        Real.rpow (n : ℝ) (3 / 32 : ℝ) =
          Real.rpow (n : ℝ) ((1 / 8 : ℝ) + (3 / 32 : ℝ)) := by
      simpa only [Real.rpow_eq_pow] using
        (Real.rpow_add hnR (1 / 8 : ℝ) (3 / 32 : ℝ)).symm
    have haddTwo : Real.rpow (n : ℝ) ((1 / 8 : ℝ) + (3 / 32 : ℝ)) *
        Real.rpow (n : ℝ) (1 / 100 : ℝ) =
          Real.rpow (n : ℝ)
            (((1 / 8 : ℝ) + (3 / 32 : ℝ)) + (1 / 100 : ℝ)) := by
      simpa only [Real.rpow_eq_pow] using
        (Real.rpow_add hnR ((1 / 8 : ℝ) + (3 / 32 : ℝ))
          (1 / 100 : ℝ)).symm
    calc
      _ = Real.rpow (n : ℝ) ((1 / 8 : ℝ) + (3 / 32 : ℝ)) *
          Real.rpow (n : ℝ) (1 / 100 : ℝ) := by rw [haddOne]
      _ = Real.rpow (n : ℝ)
          (((1 / 8 : ℝ) + (3 / 32 : ℝ)) + (1 / 100 : ℝ)) := haddTwo
      _ = _ := by norm_num
  have hpowSplit : Real.rpow (n : ℝ) (16 / 25 : ℝ) =
      Real.rpow (n : ℝ) (183 / 800 : ℝ) *
        Real.rpow (n : ℝ) (329 / 800 : ℝ) := by
    convert Real.rpow_add hnR (183 / 800 : ℝ) (329 / 800 : ℝ) using 1 <;>
      norm_num
  have hdeleteSimple : (100 : ℝ) * U * n.divisors.card *
      Real.log (y : ℝ) ≤ y := by
    calc
      (100 : ℝ) * U * n.divisors.card * Real.log (y : ℝ) ≤
          100 * (1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ)) *
            n.divisors.card * Real.log (y : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hUupper (by norm_num)) (by positivity))
          hlogy.le
      _ ≤ 100 * (1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ)) *
            Real.rpow (n : ℝ) (3 / 32 : ℝ) *
              Real.log (y : ℝ) := by
        have hcoef : 0 ≤
            100 * (1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ)) := by
          exact mul_nonneg (by norm_num)
            (mul_nonneg (by norm_num) (Real.rpow_nonneg hnR.le _))
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left htau hcoef) hlogy.le
      _ ≤ 100 * (1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ)) *
            Real.rpow (n : ℝ) (3 / 32 : ℝ) *
              (100 * Real.rpow (n : ℝ) (1 / 100 : ℝ)) := by
        have hcoef : 0 ≤
            100 * (1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ)) *
              Real.rpow (n : ℝ) (3 / 32 : ℝ) := by
          exact mul_nonneg
            (mul_nonneg (by norm_num)
              (mul_nonneg (by norm_num) (Real.rpow_nonneg hnR.le _)))
            (Real.rpow_nonneg hnR.le _)
        exact mul_le_mul_of_nonneg_left (hlogyLe.trans hlogPow) hcoef
      _ = K * Real.rpow (n : ℝ) (183 / 800 : ℝ) := by
        rw [← hpowProduct]
        dsimp [K]
        ring
      _ ≤ Real.rpow (n : ℝ) (16 / 25 : ℝ) := by
        rw [hpowSplit]
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hpLarge
          (Real.rpow_nonneg hnR.le (183 / 800 : ℝ))
      _ ≤ (y : ℝ) := hyLower
  exact directPrime_hundredth_error_budgets hnPos hlogy htailSimple hdeleteSimple

private lemma eventually_controlledPrime_mertensLog_at
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      let colors := lowerColorCount c n
      let y := initialLowerY n colors
      5 * initialMissingEulerProduct n colors * Real.log (y : ℝ) ≤
        24 * ((n : ℝ) / Nat.totient n) := by
  have hpTop : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (1 / 100 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 1,
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_initialMissingMertensBounds_lowerColorCount hc,
    eventually_initialLowerY_lt_rpow_267_400_at hc hc1,
    eventually_controlledPrime_endpoint_parameters_at hc hc1,
    hpTop.eventually (eventually_ge_atTop (60 / c))] with
      n hn hlog hloglog hMertens hyUpper hend hpLarge
  dsimp only at hMertens hyUpper ⊢
  let colors := lowerColorCount c n
  let y := initialLowerY n colors
  have hnPos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hnPos
  have hscaleLower := resolutionScale_ge_rpow_three_tenths hnPos hlog hloglog
  have hscalePos : 0 < resolutionScale n := by
    have hp : 0 < Real.rpow (n : ℝ) (3 / 10 : ℝ) := by
      simpa only [Real.rpow_eq_pow] using
        Real.rpow_pos_of_pos hnR (3 / 10 : ℝ)
    exact (mul_pos (by norm_num : (0 : ℝ) < 1 / 30) hp).trans_le hscaleLower
  have hcolorFloor := (lowerColorCount_bounds hc.le hscalePos.le).2
  have hsplit : Real.rpow (n : ℝ) (3 / 10 : ℝ) =
      Real.rpow (n : ℝ) (29 / 100 : ℝ) *
        Real.rpow (n : ℝ) (1 / 100 : ℝ) := by
    convert Real.rpow_add hnR (29 / 100 : ℝ) (1 / 100 : ℝ) using 1 <;>
      norm_num
  have hcolorRaw : 2 * Real.rpow (n : ℝ) (29 / 100 : ℝ) ≤
      c * resolutionScale n := by
    have hcScale : (c / 30) * Real.rpow (n : ℝ) (3 / 10 : ℝ) ≤
        c * resolutionScale n := by
      have := mul_le_mul_of_nonneg_left hscaleLower hc.le
      nlinarith
    have hp0 : 0 ≤ Real.rpow (n : ℝ) (29 / 100 : ℝ) := by
      simpa only [Real.rpow_eq_pow] using
        Real.rpow_nonneg hnR.le (29 / 100 : ℝ)
    have hcGap : (60 : ℝ) ≤
        c * Real.rpow (n : ℝ) (1 / 100 : ℝ) := by
      have := (div_le_iff₀ hc).mp hpLarge
      nlinarith
    have hlargeScaled := mul_le_mul_of_nonneg_left hcGap hp0
    rw [hsplit] at hcScale
    have hcoeff : 2 * Real.rpow (n : ℝ) (29 / 100 : ℝ) ≤
        (c / 30) * (Real.rpow (n : ℝ) (29 / 100 : ℝ) *
          Real.rpow (n : ℝ) (1 / 100 : ℝ)) := by
      nlinarith
    exact hcoeff.trans (hcScale.trans (le_rfl))
  have hpowOne : (1 : ℝ) ≤ Real.rpow (n : ℝ) (29 / 100 : ℝ) :=
    by simpa only [Real.rpow_eq_pow] using
      Real.one_le_rpow hnOne (by norm_num : (0 : ℝ) ≤ 29 / 100)
  have hcolorLower : Real.rpow (n : ℝ) (29 / 100 : ℝ) ≤
      (colors : ℝ) := by
    have hfloor : c * resolutionScale n < (colors : ℝ) + 1 := by
      simpa [colors] using hcolorFloor
    nlinarith
  have hcolorPos : (0 : ℝ) < colors :=
    (Real.rpow_pos_of_pos hnR _).trans_le hcolorLower
  have hlogColorLower : (29 / 100 : ℝ) * Real.log (n : ℝ) ≤
      Real.log (colors : ℝ) := by
    calc
      (29 / 100 : ℝ) * Real.log (n : ℝ) =
          Real.log (Real.rpow (n : ℝ) (29 / 100 : ℝ)) :=
        (Real.log_rpow hnR _).symm
      _ ≤ Real.log (colors : ℝ) :=
        Real.log_le_log (Real.rpow_pos_of_pos hnR _) hcolorLower
  have hyPos : (0 : ℝ) < y := by
    exact_mod_cast (show 0 < y by
      simpa [y, colors] using hend.1.trans_le hend.2.1)
  have hlogYUpper : Real.log (y : ℝ) ≤
      (267 / 400 : ℝ) * Real.log (n : ℝ) := by
    calc
      Real.log (y : ℝ) ≤
          Real.log (Real.rpow (n : ℝ) (267 / 400 : ℝ)) :=
        Real.log_le_log hyPos hyUpper.le
      _ = _ := Real.log_rpow hnR _
  have hlogColorPos : 0 < Real.log (colors : ℝ) := by
    have hpowStrict : (1 : ℝ) <
        Real.rpow (n : ℝ) (29 / 100 : ℝ) := by
      simpa only [Real.rpow_eq_pow, Real.one_rpow] using
        Real.one_lt_rpow (by exact_mod_cast hn) (by norm_num)
    have : (1 : ℝ) < colors := hpowStrict.trans_le hcolorLower
    exact Real.log_pos this
  have hratioNonneg : 0 ≤ (n : ℝ) / Nat.totient n := by positivity
  have hV := hMertens.2.2
  have hscaledV : 5 * initialMissingEulerProduct n colors * Real.log (y : ℝ) ≤
      10 * ((n : ℝ) / Nat.totient n) /
        Real.log (colors : ℝ) * Real.log (y : ℝ) := by
    have hUlower := (controlledPrimeU_cast_bounds n).1
    have hyOne : (1 : ℝ) ≤ y := by
      have hUy : controlledPrimeU n ≤ y := by
        simpa [y, colors] using hend.2.1
      have hUone : (1 : ℝ) ≤ controlledPrimeU n := by
        have hpOne : (1 : ℝ) ≤
            Real.rpow (n : ℝ) (1 / 8 : ℝ) := by
          simpa only [Real.rpow_eq_pow] using
            Real.one_le_rpow hnOne (by norm_num : (0 : ℝ) ≤ 1 / 8)
        nlinarith
      exact hUone.trans (by exact_mod_cast hUy)
    have hlogYNonneg : 0 ≤ Real.log (y : ℝ) := Real.log_nonneg hyOne
    have hmul := mul_le_mul_of_nonneg_right hV hlogYNonneg
    calc
      5 * initialMissingEulerProduct n colors * Real.log (y : ℝ) =
          5 * (initialMissingEulerProduct n colors * Real.log (y : ℝ)) := by ring
      _ ≤ 5 * ((2 * ((n : ℝ) / Nat.totient n) /
          Real.log (colors : ℝ)) * Real.log (y : ℝ)) :=
        mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ = 10 * ((n : ℝ) / Nat.totient n) /
          Real.log (colors : ℝ) * Real.log (y : ℝ) := by ring
  calc
    5 * initialMissingEulerProduct n colors * Real.log (y : ℝ) ≤
        10 * ((n : ℝ) / Nat.totient n) /
          Real.log (colors : ℝ) * Real.log (y : ℝ) := hscaledV
    _ ≤ 24 * ((n : ℝ) / Nat.totient n) := by
      rw [div_mul_eq_mul_div]
      rw [div_le_iff₀ hlogColorPos]
      have hmain := mul_le_mul_of_nonneg_left hlogYUpper hratioNonneg
      have hlower := mul_le_mul_of_nonneg_left hlogColorLower hratioNonneg
      nlinarith

/-- The canonical controlled interval contains enough prime-structured
test points to support the class cap.  This is the final assembly of the
dyadic prime-number theorem, the divisor-count error estimate, and the
Mertens-product comparison. -/
private theorem eventually_controlledPrime_testSet_count_at
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      let colors := lowerColorCount c n
      let y := initialLowerY n colors
      initialMissingEulerProduct n colors * (y : ℝ) / 12 ≤
        ((primeStructuredTestSet n y (controlledPrimeU n)).card : ℝ) := by
  obtain ⟨T, hPNT⟩ :=
    exists_dyadicPrimes_card_nineteen_twentieth_threshold
  filter_upwards [eventually_gt_atTop 0,
    eventually_controlledPrime_endpoint_parameters_at hc hc1,
    eventually_const_mul_U_le_y_at hc (max T 20),
    eventually_controlledPrime_count_error_budgets_at hc hc1,
    eventually_controlledPrime_mertensLog_at hc hc1] with
      n hn hend hroom herror hMertensLog
  dsimp only at hend hroom herror hMertensLog ⊢
  let colors := lowerColorCount c n
  let y := initialLowerY n colors
  let U := controlledPrimeU n
  have hU : 0 < U := by simpa [U] using hend.1
  have hTU : T * U ≤ y := by
    have hmax : T * U ≤ max T 20 * U :=
      Nat.mul_le_mul_right U (Nat.le_max_left T 20)
    exact hmax.trans (by simpa [U, y, colors] using hroom)
  have htwentyU : 20 * U ≤ y := by
    have hmax : 20 * U ≤ max T 20 * U :=
      Nat.mul_le_mul_right U (Nat.le_max_right T 20)
    exact hmax.trans (by simpa [U, y, colors] using hroom)
  apply initialMissingEulerProduct_mul_y_div_twelve_le_primeStructuredTestSet_card
    hn hU hPNT
  · intro u hu
    apply (Nat.le_div_iff_mul_le (boundedTargetDivisor_pos hu)).2
    exact (Nat.mul_le_mul_left T (mem_boundedTargetDivisors.mp hu).2.2).trans hTU
  · intro u hu
    exact (Nat.mul_le_mul_left 20
      (mem_boundedTargetDivisors.mp hu).2.2).trans htwentyU
  · simpa [U, y, colors] using herror.1
  · simpa [U, y, colors] using herror.2
  · simpa [y, colors] using hMertensLog

/-- All analytic and combinatorial estimates are simultaneously valid for
one fixed positive resolution constant, yielding the exact eventual source
package consumed by the final resolution connector. -/
theorem exists_eventually_controlledPrimeRandomTheorem :
    ∃ c : ℝ, 0 < c ∧ EventuallyCFPControlledPrimeRandomTheorem c := by
  obtain ⟨c, hc, hc1, hordinaryEventually⟩ :=
    exists_eventually_controlledPrimeOrdinarySource
  refine ⟨c, hc, ?_⟩
  filter_upwards [eventually_gt_atTop 0,
    eventually_three_le_lowerColorCount hc,
    eventually_controlledPrime_endpoint_parameters_at hc hc1,
    eventually_canonicalControlledPrimeNumericalLedger_at hc hc1,
    eventually_controlledPrime_testSet_count_at hc hc1,
    hordinaryEventually] with
      n hn hcolors hend hledger hcount hordinaryData
  dsimp only at hend hledger hcount hordinaryData ⊢
  let colors := lowerColorCount c n
  let y := initialLowerY n colors
  let U := controlledPrimeU n
  let B := controlledPrimeB n y
  let L := controlledPrimeL y
  let M := controlledPrimeClassCapTwelve n y
  obtain ⟨hy, hordinary⟩ := hordinaryData
  have hcolorsPos : 0 < colors := by dsimp [colors]; omega
  have hcard : colors * M ≤
      (primeStructuredBelowTarget n y U hy).card := by
    rw [card_primeStructuredBelowTarget]
    simpa [colors, y, U, M, controlledPrimeClassCap] using
      controlledPrimeClassCap_mul_le_primeStructured_card
        hn hcolorsPos rfl hcount
  refine ⟨U, B, L, M, hy, ?_, hcard, ?_⟩
  · simpa [B, y, colors] using hend.2.2.1
  · exact controlledRandomTestSetSource_of_numericalLedger hledger hordinary

end Erdos360
