import ErdosProblems.Erdos587.HooleyApproximationShell

/-!
# The complementary short-residue approximant count

When a residue progression is too short for the uniform mean theorem,
the arbitrary subpower divisor bound is sufficient. The error count
still has no additive constant because every encoded error is nonzero.
-/

open scoped BigOperators

namespace Erdos587

lemma delta_nonzero_int_card_le_two_mul (S : Finset ℤ) {T : ℝ} (hT : 0 ≤ T)
    (hzero : ∀ t ∈ S, t ≠ 0) (hbound : ∀ t ∈ S, (t.natAbs : ℝ) ≤ T) :
    (S.card : ℝ) ≤ 2 * T := by
  have h := delta_sum_natAbs_le_twice S (Nat.floor T) (fun _ => (1 : ℝ))
    (fun _ => by norm_num) hzero (fun t ht => Nat.le_floor (hbound t ht))
  simp only [Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul, mul_one] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Nat.floor_le hT) (by norm_num))

open Classical in
lemma delta_residue_card_le {q : ℕ} (hq : 0 < q) (X c : ℕ) :
    (((Finset.Icc 1 X).filter (fun n => n % q = c)).card : ℝ) ≤ (X : ℝ) / q + 1 := by
  have h := delta_sum_residue_le_progression hq X c (fun _ => (1 : ℝ)) (fun _ => by norm_num)
  simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one] at h
  have hfloor : ((X / q : ℕ) : ℝ) ≤ (X : ℝ) / q := Nat.cast_div_le
  push_cast at h
  linarith

open Classical in
lemma delta_residue_sum_le_uniform {q : ℕ} (hq : 0 < q) (X c : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hpoint : ∀ n ∈ Finset.Icc 1 X, (hooleyDelta n : ℝ) ≤ K) :
    (∑ n ∈ (Finset.Icc 1 X).filter (fun n => n % q = c), (hooleyDelta n : ℝ)) ≤
      ((X : ℝ) / q + 1) * K := by
  calc
    _ ≤ ∑ _n ∈ (Finset.Icc 1 X).filter (fun n => n % q = c), K :=
      Finset.sum_le_sum (fun n hn => hpoint n (Finset.mem_filter.mp hn).1)
    _ = (((Finset.Icc 1 X).filter (fun n => n % q = c)).card : ℝ) * K := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (delta_residue_card_le hq X c) hK

theorem exists_delta_approximant_small_shell_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X q : ℕ, 0 < q → ∀ a : ℤ, IsCoprime a (q : ℤ) →
      ∀ B T : ℝ, 0 < B → 0 ≤ T → ∀ S : Finset DeltaApproximant,
      (∀ x ∈ S, 0 < x.index) → (∀ x ∈ S, B < x.denominator) →
      (∀ x ∈ S, (x.denominator : ℝ) ≤ 2 * B) →
      (∀ x ∈ S, x.index * x.denominator ≤ X) →
      (∀ x ∈ S, deltaApproximantError a q x ≠ 0) →
      (∀ x ∈ S, ((deltaApproximantError a q x).natAbs : ℝ) ≤ T) →
      (S.card : ℝ) ≤ C * ((X : ℝ) / q + 1) * T * (X : ℝ) ^ ε := by
  classical
  obtain ⟨C₀, hC₀, hdivisor⟩ := Erdos1148.DukeArithmetic.exists_card_divisors_le_rpow hε
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro X q hq a hcop B T hB hT S hindex hlow hupp hproduct hzero herror
  let E := S.image (deltaApproximantError a q)
  have hEzero : ∀ t ∈ E, t ≠ 0 := by
    intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    exact hzero x hx
  have hEbound : ∀ t ∈ E, (t.natAbs : ℝ) ≤ T := by
    intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    exact herror x hx
  have hEcard := delta_nonzero_int_card_le_two_mul E hT hEzero hEbound
  have hpoint : ∀ n ∈ Finset.Icc 1 X, (hooleyDelta n : ℝ) ≤ C₀ * (X : ℝ) ^ ε := by
    intro n hn
    obtain ⟨hn1, hnX⟩ := Finset.mem_Icc.mp hn
    calc
      _ ≤ (n.divisors.card : ℝ) := by exact_mod_cast hooleyDelta_le_card_divisors n
      _ ≤ C₀ * (n : ℝ) ^ ε := hdivisor n (by omega)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hnX) hε.le) hC₀.le
  have hresidue (t : ℤ) :
      (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => (q : ℤ) ∣ a * n - t),
        (hooleyDelta n : ℝ)) ≤ ((X : ℝ) / q + 1) * (C₀ * (X : ℝ) ^ ε) := by
    obtain ⟨c, hc, hequiv, hgcd⟩ := exists_delta_linear_residue (t := t) hq hcop
    simp_rw [hequiv]
    exact delta_residue_sum_le_uniform hq X c (by positivity) hpoint
  have hcount := delta_approximant_card_le_residue_delta_sum hq hB S E hindex hlow hupp hproduct
    (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hcountR : (S.card : ℝ) ≤
      ∑ t ∈ E, ∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => (q : ℤ) ∣ a * n - t),
        (hooleyDelta n : ℝ) := by exact_mod_cast hcount
  calc
    _ ≤ ∑ t ∈ E, ∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => (q : ℤ) ∣ a * n - t),
        (hooleyDelta n : ℝ) := hcountR
    _ ≤ ∑ _t ∈ E, ((X : ℝ) / q + 1) * (C₀ * (X : ℝ) ^ ε) :=
      Finset.sum_le_sum (fun t _ => hresidue t)
    _ = (E.card : ℝ) * (((X : ℝ) / q + 1) * (C₀ * (X : ℝ) ^ ε)) := by simp
    _ ≤ (2 * T) * (((X : ℝ) / q + 1) * (C₀ * (X : ℝ) ^ ε)) :=
      mul_le_mul_of_nonneg_right hEcard (by positivity)
    _ = _ := by ring

end Erdos587
