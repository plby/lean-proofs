import ErdosProblems.Erdos4.JointSurvivalEstimate
import ErdosProblems.Erdos4.ReciprocalTail

/-!
# Joint survival uniformly over moving prime sets and tuples

The threshold is chosen before the finite prime-index type, the actual
prime moduli, and the finite set of integers. Thus the result applies
when all three vary with the outer parameter. Taking every sieve prime
above `(log Y)²` makes the collision contribution tend to zero.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos4.JointSurvivalAsymptotic

open RandomResidueSieve JointSurvivalEstimate

universe u

theorem eventually_uniform_relative_error (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Y : ℕ in atTop,
      ∀ (P : Type u) [Fintype P] [DecidableEq P] (ell : P → ℕ) [∀ l, Fact (ell l).Prime],
      Function.Injective ell → (∀ l, Real.log (Y : ℝ) ^ 2 ≤ ell l) →
      ∀ T : Finset ℕ, T.card ≤ r → (∀ n ∈ T, n ≤ Y) →
        |survivalMass ell T / UnitFourier.unitDensity ell ^ T.card - 1| ≤ ε := by
  let η : ℝ := Real.log (1 + ε)
  have hη : 0 < η := Real.log_pos (by linarith)
  let δ : ℝ := η / (4 * (r : ℝ) ^ 2 + 1)
  have hδ : 0 < δ := div_pos hη (by positivity)
  have hδeq : δ * (4 * (r : ℝ) ^ 2 + 1) = η := by
    dsimp [δ]
    field_simp
  have hfirst : 2 * (r : ℝ) ^ 2 * δ ≤ η / 2 := by nlinarith
  obtain ⟨K, _hK, htail⟩ := ReciprocalTail.exists_reciprocal_square_cutoff hδ
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlim : Tendsto (fun Y : ℕ => Real.log (Y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop 1,
    hlim.eventually (eventually_ge_atTop 1),
    hlim.eventually (eventually_ge_atTop ((K : ℝ) + 1)),
    hlim.eventually (eventually_ge_atTop (2 * (r : ℝ))),
    hlim.eventually (eventually_ge_atTop (4 * (r : ℝ) ^ 3 / (η * Real.log 2)))]
    with Y hY hlog1 hlogK hlogr hlogbig
  intro P _ _ ell _ hinj hell T hTr hT
  have hlog : 0 < Real.log (Y : ℝ) := lt_of_lt_of_le zero_lt_one hlog1
  have hsquare : Real.log (Y : ℝ) ≤ Real.log (Y : ℝ) ^ 2 := by nlinarith
  have hKell : ∀ l, K < ell l := by
    intro l
    have hh : (K : ℝ) < ell l := lt_of_lt_of_le (by linarith : (K : ℝ) < Real.log Y)
      (hsquare.trans (hell l))
    exact_mod_cast hh
  have hsize : ∀ l, 2 * T.card ≤ ell l := by
    intro l
    have hr : (T.card : ℝ) ≤ r := by exact_mod_cast hTr
    have hh : (2 : ℝ) * T.card ≤ ell l := by linarith [hell l]
    exact_mod_cast hh
  have hs := (ReciprocalTail.indexed_sum_lt (fun n : ℕ => 1 / (n : ℝ) ^ 2)
    (fun S hS => (htail S hS).2) ell hinj hKell).le
  have hs0 : 0 ≤ ∑ l, 1 / (ell l : ℝ) ^ 2 := Finset.sum_nonneg
    (fun l _hl => div_nonneg zero_le_one (sq_nonneg _))
  have hr : (T.card : ℝ) ≤ r := by exact_mod_cast hTr
  have hr2 := pow_le_pow_left₀ (Nat.cast_nonneg T.card) hr 2
  have hr3 := pow_le_pow_left₀ (Nat.cast_nonneg T.card) hr 3
  have hterm1 : 2 * (T.card : ℝ) ^ 2 * (∑ l, 1 / (ell l : ℝ) ^ 2) ≤ η / 2 := by
    calc
      _ ≤ 2 * (r : ℝ) ^ 2 * (∑ l, 1 / (ell l : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr2 (by norm_num)) hs0
      _ ≤ 2 * (r : ℝ) ^ 2 * δ := mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ _ := hfirst
  have hterm2 : 2 * (T.card : ℝ) ^ 3 * Real.log Y /
      (Real.log (Y : ℝ) ^ 2 * Real.log 2) ≤ η / 2 := by
    have hthreshold := (div_le_iff₀ (mul_pos hη hlog2)).mp hlogbig
    calc
      _ ≤ 2 * (r : ℝ) ^ 3 * Real.log Y /
          (Real.log (Y : ℝ) ^ 2 * Real.log 2) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr3 (by norm_num)) hlog.le)
          (by positivity)
      _ = 2 * (r : ℝ) ^ 3 / (Real.log Y * Real.log 2) := by field_simp
      _ ≤ _ := by
        apply (div_le_iff₀ (mul_pos hlog hlog2)).mpr
        nlinarith
  have hbound := uniform_relative_error_le ell hinj T hsize hY hT
    (sq_pos_of_pos hlog) hell
  calc
    _ ≤ Real.exp (2 * (T.card : ℝ) ^ 2 * (∑ l, 1 / (ell l : ℝ) ^ 2) +
        2 * (T.card : ℝ) ^ 3 * Real.log Y / (Real.log (Y : ℝ) ^ 2 * Real.log 2)) - 1 := hbound
    _ ≤ Real.exp η - 1 := sub_le_sub_right (Real.exp_le_exp.mpr (by linarith)) 1
    _ = ε := by rw [Real.exp_log (by linarith : 0 < 1 + ε)]; ring

end Erdos4.JointSurvivalAsymptotic
