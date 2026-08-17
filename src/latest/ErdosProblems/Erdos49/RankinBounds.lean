import ErdosProblems.Erdos49.Rankin
import ErdosProblems.Erdos49.Analytic

/-!
# Explicit consequences of the Rankin majorant

The exponent in `rankinAlpha` stays at least `1 / 2`.  This makes every
local Euler factor uniformly tame.  Mertens' second theorem then bounds the
whole finite product by a fixed power of `log y`.  These deliberately coarse
constants are more than sufficient for the scale separation in Problem 49.
-/

open scoped BigOperators

namespace Erdos49

noncomputable section

lemma rankinAlpha_ge_half {y : ℕ} (hy : Real.exp 1 < y) :
    (1 / 2 : ℝ) ≤ rankinAlpha y := by
  have hy0 : 0 < (y : ℝ) := lt_trans (Real.exp_pos 1) (by exact_mod_cast hy)
  have hlog : 1 < Real.log (y : ℝ) := by
    rw [Real.lt_log_iff_exp_lt hy0]
    exact_mod_cast hy
  unfold rankinAlpha
  have hinv : 1 / (2 * Real.log (y : ℝ)) ≤ 1 / 2 := by
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  linarith

lemma rankin_prime_ratio_le_three_four {y p : ℕ}
    (hy : Real.exp 1 < y) (hp : p.Prime) :
    (p : ℝ) ^ (-rankinAlpha y) ≤ 3 / 4 := by
  calc
    (p : ℝ) ^ (-rankinAlpha y) ≤ (p : ℝ) ^ (-(1 : ℝ) / 2) := by
      apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast hp.one_le
      · linarith [rankinAlpha_ge_half hy]
    _ ≤ (2 : ℝ) ^ (-(1 : ℝ) / 2) := by
      apply Real.rpow_le_rpow_of_nonpos (by norm_num)
      · exact_mod_cast hp.two_le
      · norm_num
    _ ≤ 3 / 4 := (by
      rw [show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.sqrt_eq_rpow]
      rw [inv_lt_iff_one_lt_mul₀'
        (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))]
      have hs : (4 / 3 : ℝ) < Real.sqrt 2 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      nlinarith : (2 : ℝ) ^ (-(1 : ℝ) / 2) < 3 / 4).le

lemma rankin_prime_ratio_le_two_div {y p : ℕ}
    (hy : Real.exp 1 < y) (hp : p.Prime) (hpy : p ≤ y) :
    (p : ℝ) ^ (-rankinAlpha y) ≤ 2 / p := by
  have hy0 : 0 < (y : ℝ) := lt_trans (Real.exp_pos 1) (by exact_mod_cast hy)
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hlogy : 0 < Real.log (y : ℝ) := by
    have : 1 < Real.log (y : ℝ) := by
      rw [Real.lt_log_iff_exp_lt hy0]
      exact_mod_cast hy
    linarith
  have hlogp : Real.log (p : ℝ) ≤ Real.log (y : ℝ) :=
    Real.log_le_log hp0 (by exact_mod_cast hpy)
  have hexpHalf : Real.exp ((1 : ℝ) / 2) < 2 := by
    rw [Real.exp_half]
    have he : Real.exp 1 < 3 := Real.exp_one_lt_three
    rw [Real.sqrt_lt (Real.exp_pos 1).le (by norm_num)]
    nlinarith
  have hpow : (p : ℝ) ^ (1 / (2 * Real.log (y : ℝ))) ≤
      Real.exp ((1 : ℝ) / 2) := by
    rw [Real.rpow_def_of_pos hp0]
    apply Real.exp_le_exp.mpr
    rw [show Real.log (p : ℝ) * (1 / (2 * Real.log (y : ℝ))) =
      Real.log (p : ℝ) / (2 * Real.log (y : ℝ)) by ring]
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.log (y : ℝ))).2
    nlinarith
  rw [show -rankinAlpha y = -(1 : ℝ) +
      1 / (2 * Real.log (y : ℝ)) by simp [rankinAlpha]; ring]
  rw [Real.rpow_add hp0, Real.rpow_neg_one]
  calc
    (p : ℝ)⁻¹ * (p : ℝ) ^ (1 / (2 * Real.log (y : ℝ))) ≤
        (p : ℝ)⁻¹ * Real.exp ((1 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr hp0.le)
    _ ≤ (p : ℝ)⁻¹ * 2 :=
      mul_le_mul_of_nonneg_left hexpHalf.le (inv_nonneg.mpr hp0.le)
    _ = 2 / p := by field_simp

/-- A convenient elementary bound for a geometric local factor. -/
lemma inv_one_sub_le_exp_four {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 3 / 4) :
    (1 - x)⁻¹ ≤ Real.exp (4 * x) := by
  have hsub : 0 < 1 - x := by linarith
  have hinv : 0 < (1 - x)⁻¹ := inv_pos.mpr hsub
  rw [← Real.exp_log hinv]
  apply Real.exp_le_exp.mpr
  have hlog := Real.log_le_sub_one_of_pos hinv
  calc
    Real.log (1 - x)⁻¹ ≤ (1 - x)⁻¹ - 1 := hlog
    _ = x / (1 - x) := by field_simp; ring
    _ ≤ 4 * x := by
      rw [div_le_iff₀ hsub]
      nlinarith

/-- The Rankin Euler product is controlled by an exponential of the
reciprocal-prime sum. -/
lemma rankinEulerProduct_le_exp_primeSum {y : ℕ}
    (hy : Real.exp 1 < y) :
    rankinEulerProduct y ≤
      Real.exp (8 * ∑ p ∈ Nat.primesLE y, (1 : ℝ) / p) := by
  unfold rankinEulerProduct
  calc
    ∏ p ∈ Nat.primesLE y,
        (1 - (p : ℝ) ^ (-rankinAlpha y))⁻¹ ≤
        ∏ p ∈ Nat.primesLE y,
          Real.exp (4 * ((p : ℝ) ^ (-rankinAlpha y))) := by
      apply Finset.prod_le_prod
      · intro p hp
        apply inv_nonneg.mpr
        have hx := rankin_prime_ratio_le_three_four hy
          (Nat.prime_of_mem_primesLE hp)
        linarith
      · intro p hp
        exact inv_one_sub_le_exp_four
          (rankin_prime_ratio_nonneg y p)
          (rankin_prime_ratio_le_three_four hy
            (Nat.prime_of_mem_primesLE hp))
    _ = Real.exp (∑ p ∈ Nat.primesLE y,
          4 * ((p : ℝ) ^ (-rankinAlpha y))) := by
      rw [Real.exp_sum]
    _ ≤ Real.exp (∑ p ∈ Nat.primesLE y, 8 / (p : ℝ)) := by
      apply Real.exp_le_exp.mpr
      apply Finset.sum_le_sum
      intro p hp
      have hratio := rankin_prime_ratio_le_two_div hy
        (Nat.prime_of_mem_primesLE hp) (Nat.le_of_mem_primesLE hp)
      calc
        4 * (p : ℝ) ^ (-rankinAlpha y) ≤ 4 * (2 / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hratio (by norm_num)
        _ = 8 / (p : ℝ) := by ring
    _ = Real.exp (8 * ∑ p ∈ Nat.primesLE y, (1 : ℝ) / p) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

/-- A fixed polynomial in `log y` bounds the finite Rankin Euler product. -/
theorem exists_rankinEulerProduct_log_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℕ, Real.exp 1 < y →
      rankinEulerProduct y ≤ C * Real.log (y : ℝ) ^ 8 := by
  obtain ⟨C, hC⟩ := Mertens.sum_prime_div_eq_log_log
  refine ⟨Real.exp (8 * C), (Real.exp_pos _).le, ?_⟩
  intro y hy
  have hy2 : (2 : ℝ) ≤ y := by
    have : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
    exact (this.trans hy).le
  have hsum := hC (y : ℝ) hy2
  have hsumId :
      (∑ p ∈ Finset.Ioc 0 ⌊(y : ℝ)⌋₊ with p.Prime, (1 : ℝ) / p) =
        ∑ p ∈ Nat.primesLE y, (1 : ℝ) / p := by
    apply Finset.sum_congr
    · ext p
      simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.floor_natCast,
        Nat.mem_primesLE]
      constructor
      · rintro ⟨⟨_hp0, hpy⟩, hp⟩
        exact ⟨hpy, hp⟩
      · rintro ⟨hpy, hp⟩
        exact ⟨⟨hp.pos, hpy⟩, hp⟩
    · intro p hp
      rfl
  rw [hsumId] at hsum
  have hsumUpper :
      (∑ p ∈ Nat.primesLE y, (1 : ℝ) / p) ≤
        Real.log (Real.log (y : ℝ)) + C := by
    linarith [le_abs_self
      ((∑ p ∈ Nat.primesLE y, (1 : ℝ) / p) -
        Real.log (Real.log (y : ℝ)))]
  apply (rankinEulerProduct_le_exp_primeSum hy).trans
  calc
    Real.exp (8 * ∑ p ∈ Nat.primesLE y, (1 : ℝ) / p) ≤
        Real.exp (8 * (Real.log (Real.log (y : ℝ)) + C)) := by
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsumUpper (by norm_num))
    _ = Real.exp (8 * C) * Real.log (y : ℝ) ^ 8 := by
      have hlog : 0 < Real.log (y : ℝ) := by
        have hy0 : 0 < (y : ℝ) := lt_trans (Real.exp_pos 1) (by exact_mod_cast hy)
        have : 1 < Real.log (y : ℝ) := by
          rw [Real.lt_log_iff_exp_lt hy0]
          exact_mod_cast hy
        linarith
      rw [show 8 * (Real.log (Real.log (y : ℝ)) + C) =
          8 * C + Real.log (Real.log (y : ℝ)) * 8 by ring,
        Real.exp_add]
      congr 1
      calc
        Real.exp (Real.log (Real.log (y : ℝ)) * 8) =
            Real.exp ((8 : ℕ) * Real.log (Real.log (y : ℝ))) := by
              congr 1
              norm_num
              ring
        _ = Real.exp (Real.log (Real.log (y : ℝ))) ^ 8 :=
          Real.exp_nat_mul _ _
        _ = Real.log (y : ℝ) ^ 8 := by rw [Real.exp_log hlog]

lemma rankinAlpha_lt_one {y : ℕ} (hy : Real.exp 1 < y) :
    rankinAlpha y < 1 := by
  have hy0 : 0 < (y : ℝ) := lt_trans (Real.exp_pos 1) (by exact_mod_cast hy)
  have hlog : 0 < Real.log (y : ℝ) := by
    have : 1 < Real.log (y : ℝ) := by
      rw [Real.lt_log_iff_exp_lt hy0]
      exact_mod_cast hy
    linarith
  unfold rankinAlpha
  exact sub_lt_self _ (one_div_pos.mpr (by positivity))

/-- Concrete smooth-number consequence of the Rankin majorant. -/
theorem smoothUpTo_card_real_le {X y : ℕ} (hX : 0 < X)
    (hy : Real.exp 1 < y) :
    ((smoothUpTo X y).card : ℝ) ≤
      (X : ℝ) ^ rankinAlpha y * rankinEulerProduct y := by
  have ha : 0 ≤ rankinAlpha y := (rankinAlpha_pos hy).le
  calc
    ((smoothUpTo X y).card : ℝ) =
        ∑ n ∈ smoothUpTo X y, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ smoothUpTo X y,
        (X : ℝ) ^ rankinAlpha y * (n : ℝ) ^ (-rankinAlpha y) := by
      apply Finset.sum_le_sum
      intro n hn
      have hndata := mem_smoothUpTo.mp hn
      have hnpos : 0 < (n : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hndata.2.1
      have hpow : (n : ℝ) ^ rankinAlpha y ≤
          (X : ℝ) ^ rankinAlpha y := by
        exact Real.rpow_le_rpow (Nat.cast_nonneg n)
          (by exact_mod_cast hndata.1) ha
      calc
        (1 : ℝ) = (n : ℝ) ^ rankinAlpha y *
            (n : ℝ) ^ (-rankinAlpha y) := by
          rw [← Real.rpow_add hnpos, add_neg_cancel, Real.rpow_zero]
        _ ≤ (X : ℝ) ^ rankinAlpha y *
            (n : ℝ) ^ (-rankinAlpha y) :=
          mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = (X : ℝ) ^ rankinAlpha y *
        (∑ n ∈ smoothUpTo X y, (n : ℝ) ^ (-rankinAlpha y)) := by
      rw [Finset.mul_sum]
    _ ≤ (X : ℝ) ^ rankinAlpha y * rankinEulerProduct y :=
      mul_le_mul_of_nonneg_left (smooth_rankin_sum_le_euler hy) (by positivity)

/-- Positive `y`-smooth integers in `(D,X]`. -/
def smoothTail (X D y : ℕ) : Finset ℕ :=
  (smoothUpTo X y).filter fun d ↦ D < d

@[simp] lemma mem_smoothTail {X D y d : ℕ} :
    d ∈ smoothTail X D y ↔ d ≤ X ∧ Smooth y d ∧ D < d := by
  simp [smoothTail, and_assoc]

/-- Concrete reciprocal-tail consequence of Rankin's method. -/
theorem smoothTail_reciprocal_sum_le {X D y : ℕ} (hD : 0 < D)
    (hy : Real.exp 1 < y) :
    (∑ d ∈ smoothTail X D y, (1 : ℝ) / d) ≤
      (D : ℝ) ^ (rankinAlpha y - 1) * rankinEulerProduct y := by
  have hexp : rankinAlpha y - 1 ≤ 0 := sub_nonpos.mpr (rankinAlpha_lt_one hy).le
  calc
    (∑ d ∈ smoothTail X D y, (1 : ℝ) / d) ≤
        ∑ d ∈ smoothTail X D y,
          (D : ℝ) ^ (rankinAlpha y - 1) *
            (d : ℝ) ^ (-rankinAlpha y) := by
      apply Finset.sum_le_sum
      intro d hd
      have hddata := mem_smoothTail.mp hd
      have hdpos : 0 < (d : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hddata.2.1.1
      have hDreal : 0 < (D : ℝ) := by exact_mod_cast hD
      have hbase : (d : ℝ) ^ (rankinAlpha y - 1) ≤
          (D : ℝ) ^ (rankinAlpha y - 1) := by
        exact Real.rpow_le_rpow_of_nonpos hDreal
          (by exact_mod_cast hddata.2.2.le) hexp
      calc
        (1 : ℝ) / d = (d : ℝ)⁻¹ := by rw [one_div]
        _ = (d : ℝ) ^ (-1 : ℝ) := (Real.rpow_neg_one _).symm
        _ = (d : ℝ) ^ (rankinAlpha y - 1) *
            (d : ℝ) ^ (-rankinAlpha y) := by
          rw [← Real.rpow_add hdpos]
          congr 1
          ring
        _ ≤ (D : ℝ) ^ (rankinAlpha y - 1) *
            (d : ℝ) ^ (-rankinAlpha y) :=
          mul_le_mul_of_nonneg_right hbase (by positivity)
    _ = (D : ℝ) ^ (rankinAlpha y - 1) *
        (∑ d ∈ smoothTail X D y, (d : ℝ) ^ (-rankinAlpha y)) := by
      rw [Finset.mul_sum]
    _ ≤ (D : ℝ) ^ (rankinAlpha y - 1) *
        (∑ d ∈ smoothUpTo X y, (d : ℝ) ^ (-rankinAlpha y)) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro d hd
          exact (Finset.mem_filter.mp hd).1
        · intro d hd hnot
          positivity
      · positivity
    _ ≤ (D : ℝ) ^ (rankinAlpha y - 1) * rankinEulerProduct y :=
      mul_le_mul_of_nonneg_left (smooth_rankin_sum_le_euler hy) (by positivity)

#print axioms exists_rankinEulerProduct_log_bound
#print axioms smoothUpTo_card_real_le
#print axioms smoothTail_reciprocal_sum_le

end

end Erdos49
