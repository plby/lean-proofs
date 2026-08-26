import ErdosProblems.Erdos67b.MRSelectedPrimeEulerBound

/-! # Rounded reciprocal-mass bounds retaining both selected-prime endpoints -/

open scoped BigOperators

namespace Erdos67b

noncomputable section

theorem mrSelected_reciprocalMass_le_interval
    (A : Finset ℕ) {P Q : ℕ} (hP : 2 ≤ P) (hPQ : P ≤ Q)
    (hA : A ⊆ primesBetween P Q) :
    (∑ p ∈ A, 1 / (p : ℝ)) ≤
      Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) +
        2 * PrimeEstimates.mertensBound := by
  have hmass := PrimeEstimates.reciprocalPrimeInterval_le_log_log_sub_add hP hPQ
  have hsum : (∑ p ∈ A, 1 / (p : ℝ)) ≤ PrimeEstimates.reciprocalPrimeInterval P Q := by
    unfold PrimeEstimates.reciprocalPrimeInterval PrimeEstimates.primesInInterval
    simpa only [primesBetween, one_div] using
      (Finset.sum_le_sum_of_subset_of_nonneg hA
        (fun p hp hnot ↦ (show 0 ≤ 1 / (p : ℝ) by positivity)))
  exact hsum.trans hmass

theorem mrSelected_reciprocalMass_le_log_ratio
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) {a b : ℝ} (ha : 4 ≤ a) (hab : a ≤ b)
    (hlower : ∀ p ∈ A, a ≤ Real.log (p : ℝ))
    (hupper : ∀ p ∈ A, Real.log (p : ℝ) ≤ b) :
    (∑ p ∈ A, 1 / (p : ℝ)) ≤
      Real.log (4 * b / a) + 2 * PrimeEstimates.mertensBound := by
  let P : ℕ := ⌊Real.exp (a / 2)⌋₊
  let Q : ℕ := ⌊Real.exp b⌋₊
  have haPos : 0 < a := by linarith
  have hbPos : 0 < b := haPos.trans_le hab
  have hexp : 2 ≤ Real.exp (a / 2) := by
    have h := Real.add_one_le_exp (a / 2)
    linarith
  have hP : 2 ≤ P := Nat.le_floor (by simpa using hexp)
  have hPQ : P ≤ Q := Nat.floor_mono (Real.exp_le_exp.mpr (by linarith))
  have hPR : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hQR : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hfloor : Real.exp (a / 2) / 2 ≤ (P : ℝ) := by
    have hlt := Nat.lt_floor_add_one (Real.exp (a / 2))
    have hPone : (1 : ℝ) ≤ P := by exact_mod_cast (show 1 ≤ P by omega)
    dsimp only [P] at hPone ⊢
    linarith
  have hlogP : a / 4 ≤ Real.log (P : ℝ) := by
    have hlog := Real.log_le_log (div_pos (Real.exp_pos _) (by norm_num)) hfloor
    rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at hlog
    have htwo : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith
  have hlogQ : Real.log (Q : ℝ) ≤ b := by
    have hh := Real.log_le_log hQR (Nat.floor_le (Real.exp_pos b).le)
    simpa only [Real.log_exp] using hh
  have hsubset : A ⊆ primesBetween P Q := by
    intro p hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast (hA p hp).pos
    apply mem_primesBetween.mpr
    refine ⟨hA p hp, ?_, ?_⟩
    · have hh : (P : ℝ) < p := by
        calc
          _ ≤ Real.exp (a / 2) := Nat.floor_le (Real.exp_pos _).le
          _ < Real.exp a := Real.exp_lt_exp.mpr (by linarith)
          _ ≤ Real.exp (Real.log (p : ℝ)) := Real.exp_le_exp.mpr (hlower p hp)
          _ = p := Real.exp_log hpR
      exact_mod_cast hh
    · apply Nat.le_floor
      calc
        (p : ℝ) = Real.exp (Real.log (p : ℝ)) := (Real.exp_log hpR).symm
        _ ≤ Real.exp b := Real.exp_le_exp.mpr (hupper p hp)
  have hm := mrSelected_reciprocalMass_le_interval A hP hPQ hsubset
  have hloglogP := Real.log_le_log (by positivity : 0 < a / 4) hlogP
  have hlogQPos : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have hloglogQ := Real.log_le_log hlogQPos hlogQ
  have hratio : Real.log b - Real.log (a / 4) = Real.log (4 * b / a) := by
    rw [Real.log_div (mul_pos (by norm_num) hbPos).ne' haPos.ne',
      Real.log_mul (by norm_num) hbPos.ne',
      Real.log_div haPos.ne' (by norm_num)]
    ring
  linarith

theorem mrSelected_log_lower_four_implies_four
    {p : ℕ} (hp : p.Prime) {a : ℝ} (ha : 4 ≤ a) (hlower : a ≤ Real.log (p : ℝ)) :
    4 ≤ p := by
  have h := Real.add_one_le_exp (Real.log (p : ℝ))
  rw [Real.exp_log (by exact_mod_cast hp.pos)] at h
  have hpR : (4 : ℝ) ≤ p := by linarith
  exact_mod_cast hpR

theorem mrSelected_tail_le_exp_cutoff_log_ratio
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) {a b tau K : ℝ}
    (ha : 4 ≤ a) (hab : a ≤ b)
    (hlower : ∀ p ∈ A, a ≤ Real.log (p : ℝ))
    (hupper : ∀ p ∈ A, Real.log (p : ℝ) ≤ b) (hK : Real.exp (tau * b) ≤ K) :
    (∑' n : ℕ, mrSelectedPrimeTailWeight A K n) ≤
      Real.exp (-tau) * Real.exp
        (2 * Real.exp 1 * (Real.log (4 * b / a) + 2 * PrimeEstimates.mertensBound)) := by
  have hb : 2 ≤ b := by linarith
  have hbPos : 0 < b := by linarith
  have hKPos : 0 < K := (Real.exp_pos _).trans_le hK
  have hinv : b⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hb
  have hsigma : 0 < 1 - b⁻¹ := by linarith
  have hsigmaOne : 1 - b⁻¹ ≤ 1 := by linarith [inv_pos.mpr hbPos]
  have htail := mrTsum_selectedPrimeTailWeight_le_rankin A hA hKPos hsigma hsigmaOne
  have hprod := mrSelected_eulerProduct_shifted_le_reciprocalMass A hb
    (fun p hp ↦ mrSelected_log_lower_four_implies_four (hA p hp) ha (hlower p hp)) hupper
  have hmass := mrSelected_reciprocalMass_le_log_ratio A hA ha hab hlower hupper
  have hpower : K ^ ((1 - b⁻¹) - 1) ≤ Real.exp (-tau) := by
    calc
      _ ≤ (Real.exp (tau * b)) ^ ((1 - b⁻¹) - 1) :=
        Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hK (by linarith)
      _ = _ := mrSelected_rankin_exp_cutoff hbPos
  apply htail.trans
  calc
    _ ≤ K ^ ((1 - b⁻¹) - 1) * Real.exp (2 * Real.exp 1 * ∑ p ∈ A, 1 / (p : ℝ)) :=
      mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hKPos.le _)
    _ ≤ Real.exp (-tau) * Real.exp (2 * Real.exp 1 * ∑ p ∈ A, 1 / (p : ℝ)) :=
      mul_le_mul_of_nonneg_right hpower (Real.exp_pos _).le
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hmass (by positivity))) (Real.exp_pos _).le

end

end Erdos67b
