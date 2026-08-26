import ErdosProblems.Erdos394.GlobalDenominatorSum

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Euler-product form of the global denominator lower bound
-/

open Nat Finset

namespace Erdos394

/-- The floor-normalized contribution of one selected subset has exactly the
expected `1/(K^|T| ∏T)` scale, with an explicit absolute constant. -/
theorem selected_main_term_lower
    (T : Finset ℕ) (K C0 X : ℕ)
    (hK : 0 < K) (hC0 : 0 < C0)
    (hprime : ∀ p ∈ T, p.Prime)
    (hhorizon : 2 * (C0 * K ^ (T.card + 1)) ≤ primeProduct T)
    (hX : 64 * primeProduct T ≤ X) :
    (Real.log 2 * (X : ℝ) ^ 2 /
        (524288 * (C0 : ℝ) * (K : ℝ) * Real.log X)) *
        (∏ p ∈ T, (1 / ((K : ℝ) * (p : ℝ)))) ≤
      ((selectedHorizon K C0 T : ℕ) : ℝ) / 4 *
        (Real.log 2 * (selectedPrimeBase X T : ℝ) ^ 2 /
          (16 * Real.log (selectedPrimeBase X T))) := by
  let q := primeProduct T
  let Y := selectedHorizon K C0 T
  let N := selectedPrimeBase X T
  have hqposNat : 0 < q := by
    dsimp [q, primeProduct]
    exact Finset.prod_pos fun p hp ↦ (hprime p hp).pos
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hqposNat
  have hYlower : (q : ℝ) /
      (2 * ((C0 * K ^ (T.card + 1) : ℕ) : ℝ)) ≤ (Y : ℝ) := by
    dsimp [q, Y, selectedHorizon]
    exact horizon_floor_lower K C0 (primeProduct T) T.card hK hC0 hhorizon
  have hNlower : (X : ℝ) / (64 * (q : ℝ)) ≤ (N : ℝ) := by
    dsimp [q, N, selectedPrimeBase]
    exact primeBase_floor_lower X (primeProduct T) hqposNat hX
  have hNtwo : 2 ≤ N := by
    dsimp [N, selectedPrimeBase]
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 32 * primeProduct T)).2
    nlinarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hNXnat : N ≤ X := by
    dsimp [N, selectedPrimeBase]
    exact Nat.div_le_self X (32 * primeProduct T)
  have hXtwo : 2 ≤ X := hNtwo.trans hNXnat
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogle : Real.log (N : ℝ) ≤ Real.log (X : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn hNpos
      (show (0 : ℝ) < X by exact_mod_cast (show 0 < X by omega))
      (by exact_mod_cast hNXnat)
  have hN2 : ((X : ℝ) / (64 * (q : ℝ))) ^ 2 ≤ (N : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hNlower 2
  have hY0 : 0 ≤ (Y : ℝ) := by positivity
  have hleftY0 : 0 ≤ (q : ℝ) /
      (2 * ((C0 * K ^ (T.card + 1) : ℕ) : ℝ)) := by positivity
  have hYN : ((q : ℝ) /
        (2 * ((C0 * K ^ (T.card + 1) : ℕ) : ℝ))) *
        ((X : ℝ) / (64 * (q : ℝ))) ^ 2 ≤
      (Y : ℝ) * (N : ℝ) ^ 2 :=
    mul_le_mul hYlower hN2 (by positivity) hY0
  have hYN0 : 0 ≤ (Y : ℝ) * (N : ℝ) ^ 2 := by positivity
  have hdiv : (((q : ℝ) /
        (2 * ((C0 * K ^ (T.card + 1) : ℕ) : ℝ))) *
        ((X : ℝ) / (64 * (q : ℝ))) ^ 2) / Real.log X ≤
      ((Y : ℝ) * (N : ℝ) ^ 2) / Real.log N := by
    calc
      (((q : ℝ) /
          (2 * ((C0 * K ^ (T.card + 1) : ℕ) : ℝ))) *
          ((X : ℝ) / (64 * (q : ℝ))) ^ 2) / Real.log X ≤
        ((Y : ℝ) * (N : ℝ) ^ 2) / Real.log X :=
          div_le_div_of_nonneg_right hYN hlogX.le
      _ ≤ ((Y : ℝ) * (N : ℝ) ^ 2) / Real.log N :=
        div_le_div_of_nonneg_left hYN0 hlogN hlogle
  have hscale : 0 ≤ Real.log 2 / 64 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hdiv hscale
  have hprod := prod_inv_K_prime_eq K T hK hprime
  dsimp [q, Y, N] at hscaled
  calc
    (Real.log 2 * (X : ℝ) ^ 2 /
        (524288 * (C0 : ℝ) * (K : ℝ) * Real.log X)) *
        (∏ p ∈ T, (1 / ((K : ℝ) * (p : ℝ)))) =
      Real.log 2 / 64 *
        (((primeProduct T : ℝ) /
          (2 * ((C0 * K ^ (T.card + 1) : ℕ) : ℝ))) *
          ((X : ℝ) / (64 * (primeProduct T : ℝ))) ^ 2 /
            Real.log X) := by
      rw [hprod]
      push_cast
      field_simp [show (K : ℝ) ≠ 0 by exact_mod_cast hK.ne',
        show (C0 : ℝ) ≠ 0 by exact_mod_cast hC0.ne',
        show (primeProduct T : ℝ) ≠ 0 by exact_mod_cast hqposNat.ne',
        hlogX.ne']
      ring
    _ ≤ Real.log 2 / 64 *
        (((selectedHorizon K C0 T : ℕ) : ℝ) *
          (selectedPrimeBase X T : ℝ) ^ 2 /
            Real.log (selectedPrimeBase X T)) := hscaled
    _ = ((selectedHorizon K C0 T : ℕ) : ℝ) / 4 *
        (Real.log 2 * (selectedPrimeBase X T : ℝ) ^ 2 /
          (16 * Real.log (selectedPrimeBase X T))) := by ring

/-- Once the injective selected-subset sum is available, floor bounds and
cardinality truncation convert it to a clean full Euler-product lower bound. -/
theorem denominatorEulerProduct_lower_of_selected_sum
    (P : Finset ℕ) (K C0 X S : ℕ)
    (hK : 0 < K) (hC0 : 0 < C0) (hXlog : 1 < X)
    (hprime : ∀ p ∈ P, p.Prime)
    (hhorizon : ∀ T ∈ denominatorSelectedSubsets P S,
      2 * (C0 * K ^ (T.card + 1)) ≤ primeProduct T)
    (hX : ∀ T ∈ denominatorSelectedSubsets P S,
      64 * primeProduct T ≤ X)
    (hcut : 4 * (∑ p ∈ P, (1 / ((K : ℝ) * (p : ℝ)))) ≤
      (S + 1 : ℝ))
    (hE4 : 4 ≤ ∏ p ∈ P, (1 + 1 / ((K : ℝ) * (p : ℝ))))
    (hselected :
      (∑ T ∈ denominatorSelectedSubsets P S,
        ((selectedHorizon K C0 T : ℕ) : ℝ) / 4 *
          (Real.log 2 * (selectedPrimeBase X T : ℝ) ^ 2 /
            (16 * Real.log (selectedPrimeBase X T)))) ≤
        ∑ n ∈ Finset.Icc 1 X, (t K n : ℝ)) :
    (Real.log 2 * (X : ℝ) ^ 2 /
        (1048576 * (C0 : ℝ) * (K : ℝ) * Real.log X)) *
      (∏ p ∈ P, (1 + 1 / ((K : ℝ) * (p : ℝ)))) ≤
        ∑ n ∈ Finset.Icc 1 X, (t K n : ℝ) := by
  let A : ℝ := Real.log 2 * (X : ℝ) ^ 2 /
    (524288 * (C0 : ℝ) * (K : ℝ) * Real.log X)
  let E : ℝ := ∏ p ∈ P, (1 + 1 / ((K : ℝ) * (p : ℝ)))
  let B : ℝ := ∑ T ∈ denominatorSelectedSubsets P S,
    ∏ p ∈ T, (1 / ((K : ℝ) * (p : ℝ)))
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hXlog)
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hx0 : ∀ p ∈ P, 0 ≤ (1 / ((K : ℝ) * (p : ℝ))) := by
    intro p hp
    positivity
  have htrunc := two_mul_euler_le_four_mul_nonemptyBoundedSubsetWeight
    P S (fun p ↦ 1 / ((K : ℝ) * (p : ℝ))) hx0 hcut hE4
  have hEB : E / 2 ≤ B := by
    dsimp [E, B, denominatorSelectedSubsets] at htrunc ⊢
    nlinarith
  have hAB : (A / 2) * E ≤ A * B := by
    calc
      (A / 2) * E = A * (E / 2) := by ring
      _ ≤ A * B := mul_le_mul_of_nonneg_left hEB hA0
  have hterm : ∀ T ∈ denominatorSelectedSubsets P S,
      A * (∏ p ∈ T, (1 / ((K : ℝ) * (p : ℝ)))) ≤
        ((selectedHorizon K C0 T : ℕ) : ℝ) / 4 *
          (Real.log 2 * (selectedPrimeBase X T : ℝ) ^ 2 /
            (16 * Real.log (selectedPrimeBase X T))) := by
    intro T hT
    dsimp [A]
    exact selected_main_term_lower T K C0 X hK hC0
      (fun p hp ↦ hprime p
        ((mem_denominatorSelectedSubsets_iff.mp hT).1 hp))
      (hhorizon T hT) (hX T hT)
  have hsum : A * B ≤
      ∑ T ∈ denominatorSelectedSubsets P S,
        ((selectedHorizon K C0 T : ℕ) : ℝ) / 4 *
          (Real.log 2 * (selectedPrimeBase X T : ℝ) ^ 2 /
            (16 * Real.log (selectedPrimeBase X T))) := by
    dsimp [B]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  calc
    (Real.log 2 * (X : ℝ) ^ 2 /
        (1048576 * (C0 : ℝ) * (K : ℝ) * Real.log X)) *
      (∏ p ∈ P, (1 + 1 / ((K : ℝ) * (p : ℝ)))) =
        (A / 2) * E := by dsimp [A, E]; ring
    _ ≤ A * B := hAB
    _ ≤ _ := hsum.trans hselected

end Erdos394
