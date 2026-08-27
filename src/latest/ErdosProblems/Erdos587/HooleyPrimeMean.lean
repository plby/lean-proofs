import ErdosProblems.Erdos587.HooleyPrimeIntervals
import ErdosProblems.Erdos587.HooleySmoothedMean

/-!
# A smoothed prime average of divisor moments

Only the mass of primes in unit logarithmic windows is used. Smoothing
costs `2^q`, which the cubic-factorial moment envelope absorbs. This
avoids the tuple expansion and its short-interval remainder.
-/

open MeasureTheory
open scoped BigOperators

namespace Erdos587

noncomputable def deltaPrimeWindowConstant : ℝ := 8 * Real.exp 1 + 336

lemma deltaPrimeWindowConstant_pos : 0 < deltaPrimeWindowConstant := by
  unfold deltaPrimeWindowConstant
  positivity

lemma primeIntervalReciprocal_le_unit_log_bound {x y : ℝ}
    (hx : 1 < x) (hxy : x ≤ y) (hy : y ≤ Real.exp 1 * x) :
    primeIntervalReciprocal x y ≤ deltaPrimeWindowConstant / Real.log x := by
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
  have hlogsqrt : Real.log x ≤ 2 * Real.sqrt x := by
    have h := Real.log_le_sub_one_of_pos hsqrt
    rw [Real.log_sqrt hxpos.le] at h
    linarith
  have hrecip : (168 : ℝ) / Real.sqrt x ≤ 336 / Real.log x := by
    rw [div_le_div_iff₀ hsqrt hlog]
    linarith
  have hlen : y - x ≤ Real.exp 1 * x := by linarith
  have hmain : 8 * (y - x) / (x * Real.log x) ≤ 8 * Real.exp 1 / Real.log x := by
    calc
      _ ≤ 8 * (Real.exp 1 * x) / (x * Real.log x) := by gcongr
      _ = _ := by field_simp
  have hbound := primeIntervalReciprocal_le_log_main_sqrt_error hx (sub_nonneg.mpr hxy)
  rw [add_sub_cancel] at hbound
  calc
    primeIntervalReciprocal x y ≤
        8 * (y - x) / (x * Real.log x) + 168 / Real.sqrt x := hbound
    _ ≤ 8 * Real.exp 1 / Real.log x + 336 / Real.log x := add_le_add hmain hrecip
    _ = deltaPrimeWindowConstant / Real.log x := by
      unfold deltaPrimeWindowConstant
      ring

/-- Every finite collection of primes above `Y` has bounded reciprocal
mass in every unit logarithmic interval. -/
theorem sum_reciprocal_prime_log_window_le (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) {Y : ℝ} (hY : 1 < Y)
    (hmin : ∀ p ∈ P, Y ≤ (p : ℝ)) (v : ℝ) :
    (∑ p ∈ P.filter (fun p : ℕ => v ≤ Real.log p ∧ Real.log p ≤ v + 1),
      (1 : ℝ) / p) ≤ deltaPrimeWindowConstant / Real.log Y := by
  classical
  let a := max Y (Real.exp v)
  let b := max a (Real.exp (v + 1))
  have hYa : Y ≤ a := le_max_left _ _
  have ha : 1 < a := hY.trans_le hYa
  have hab : a ≤ b := le_max_left _ _
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  have hba : b ≤ Real.exp 1 * a := by
    apply max_le
    · nlinarith [show 0 < a from lt_trans zero_lt_one ha]
    · rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right (le_max_right Y (Real.exp v)) (Real.exp_pos 1).le
        |>.trans_eq (mul_comm a (Real.exp 1))
  have hsubset : P.filter (fun p : ℕ => v ≤ Real.log p ∧ Real.log p ≤ v + 1) ⊆
      (Finset.Icc (Nat.ceil a) (Nat.floor b)).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpP, hlow, hupp⟩ := Finset.mem_filter.mp hp
    have hp : p.Prime := hprime p hpP
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hap : a ≤ (p : ℝ) := max_le (hmin p hpP)
      ((Real.le_log_iff_exp_le hpR).mp hlow)
    have hpb : (p : ℝ) ≤ b := ((Real.log_le_iff_le_exp hpR).mp hupp).trans (le_max_right _ _)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Nat.ceil_le.mpr hap, Nat.le_floor hpb⟩, hp⟩
  calc
    _ ≤ primeIntervalReciprocal a b :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => by positivity)
    _ ≤ deltaPrimeWindowConstant / Real.log a :=
      primeIntervalReciprocal_le_unit_log_bound ha hab hba
    _ ≤ deltaPrimeWindowConstant / Real.log Y :=
      div_le_div_of_nonneg_left deltaPrimeWindowConstant_pos.le (Real.log_pos hY)
        (Real.log_le_log (lt_trans zero_lt_one hY) hYa)

/-- A uniform prime average, with an exponential loss only in the moment
order. The estimate has no divisor-count or interval-length error term. -/
theorem sum_prime_deltaCount_pow_le (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) {Y : ℝ} (hY : 1 < Y)
    (hmin : ∀ p ∈ P, Y ≤ (p : ℝ)) (n : ℕ) {q : ℕ} (hq : q ≠ 0) (u : ℝ) :
    (∑ p ∈ P, (1 : ℝ) / p * deltaCount n (u - Real.log p) ^ q) ≤
      (deltaPrimeWindowConstant / Real.log Y) * 2 ^ q * deltaMoment n q := by
  classical
  apply sum_weight_mul_deltaCount_pow_le P (fun p => 1 / (p : ℝ))
    (fun p => Real.log p) (fun _ _ => by positivity) n hq u
  intro v
  have h := sum_reciprocal_prime_log_window_le P hprime hY hmin (u - v - 1)
  rw [Finset.sum_filter] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Set.indicator_apply, Set.mem_Icc]
  have hiff : u - Real.log p - 1 ≤ v ∧ v ≤ u - Real.log p ↔
      u - v - 1 ≤ Real.log p ∧ Real.log p ≤ u - v - 1 + 1 := by
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  simp only [hiff]

/-- The prime-averaged mixed moment factorizes into ordinary moments,
with the explicit unit-window smoothing loss. -/
theorem sum_prime_deltaMixedMoment_le (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) {Y : ℝ} (hY : 1 < Y)
    (hmin : ∀ p ∈ P, Y ≤ (p : ℝ)) (n : ℕ) {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    (∑ p ∈ P, (1 : ℝ) / p * deltaMixedMoment n a b (Real.log p)) ≤
      (deltaPrimeWindowConstant / Real.log Y) * 2 ^ b * deltaMoment n a * deltaMoment n b := by
  have hab : a + b ≠ 0 := by omega
  have hi (p : ℕ) : Integrable (fun u : ℝ =>
      (1 : ℝ) / p * (deltaCount n u ^ a * deltaCount n (u - Real.log p) ^ b)) :=
    (integrable_deltaCount_mixed n a b (Real.log p) hab).const_mul _
  let C := (deltaPrimeWindowConstant / Real.log Y) * 2 ^ b * deltaMoment n b
  calc
    _ = ∫ u : ℝ, ∑ p ∈ P,
        (1 : ℝ) / p * (deltaCount n u ^ a * deltaCount n (u - Real.log p) ^ b) := by
      rw [integral_finsetSum P (fun p _ => hi p)]
      apply Finset.sum_congr rfl
      intro p hp
      rw [integral_const_mul]
      rfl
    _ ≤ ∫ u : ℝ, deltaCount n u ^ a * C := by
      apply integral_mono (integrable_finsetSum P (fun p _ => hi p))
        ((integrable_deltaCount_pow ha).mul_const C)
      intro u
      change (∑ p ∈ P,
        (1 : ℝ) / p * (deltaCount n u ^ a * deltaCount n (u - Real.log p) ^ b)) ≤ _
      calc
        _ = deltaCount n u ^ a * ∑ p ∈ P,
            (1 : ℝ) / p * deltaCount n (u - Real.log p) ^ b := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          ring
        _ ≤ deltaCount n u ^ a * C :=
          mul_le_mul_of_nonneg_left (sum_prime_deltaCount_pow_le P hprime hY hmin n hb u)
            (pow_nonneg (deltaCount_nonneg n u) a)
    _ = _ := by
      rw [integral_mul_const]
      change deltaMoment n a * C = _
      dsimp only [C]
      ring

end Erdos587
