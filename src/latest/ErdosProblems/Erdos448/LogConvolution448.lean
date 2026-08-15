import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open scoped BigOperators
open Set MeasureTheory intervalIntegral

namespace LogConvolution448

/-!
Finite real-power estimates used when the logarithmic variables in the
Erdos--Tenenbaum argument are convolved.  We use `j + 1` in the basic power
sum, so every base is positive and the zero convention for `Real.rpow` never
enters the estimates.
-/

/-- Integral-test bound for a finite power sum below the critical exponent. -/
lemma sum_range_succ_rpow_neg_le (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (N : ℕ) (hN : 1 ≤ N) :
    (∑ j ∈ Finset.range N, ((j + 1 : ℕ) : ℝ) ^ (-a)) ≤
      1 + ((N : ℝ) ^ (1 - a) - 1) / (1 - a) := by
  let f : ℝ → ℝ := fun x ↦ x ^ (-a)
  have hf : AntitoneOn f (Icc ((1 : ℕ) : ℝ) (N : ℝ)) := by
    exact (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (neg_nonpos.mpr ha0)).mono
      (by
        intro x hx
        norm_num at hx ⊢
        exact zero_lt_one.trans_le hx.1)
  have htail := AntitoneOn.sum_le_integral_Ico (f := f) hN hf
  have hsum :
      (∑ j ∈ Finset.range N, ((j + 1 : ℕ) : ℝ) ^ (-a)) =
        1 + ∑ j ∈ Finset.Ico 1 N, ((j + 1 : ℕ) : ℝ) ^ (-a) := by
    obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
    rw [Finset.sum_range_succ', Finset.sum_Ico_eq_sum_range]
    rw [add_comm]
    norm_num
    congr 1
    funext j
    congr 1
    ring
  rw [hsum]
  gcongr
  calc
    (∑ j ∈ Finset.Ico 1 N, ((j + 1 : ℕ) : ℝ) ^ (-a))
        ≤ ∫ x in (1 : ℝ)..(N : ℝ), x ^ (-a) := by simpa [f] using htail
    _ = ((N : ℝ) ^ (1 - a) - 1) / (1 - a) := by
      rw [integral_rpow]
      · norm_num
        ring
      · left
        linarith

/-- The `1/4` power sum in the form used in logarithmic convolutions. -/
lemma sum_range_succ_rpow_neg_quarter_le (N : ℕ) (hN : 1 ≤ N) :
    (∑ j ∈ Finset.range N, ((j + 1 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))) ≤
      2 * (N : ℝ) ^ (3 / 4 : ℝ) := by
  have h := sum_range_succ_rpow_neg_le (1 / 4 : ℝ) (by norm_num) (by norm_num) N hN
  calc
    _ ≤ 1 + ((N : ℝ) ^ (1 - (1 / 4 : ℝ)) - 1) /
          (1 - (1 / 4 : ℝ)) := h
    _ ≤ 2 * (N : ℝ) ^ (3 / 4 : ℝ) := by
      have hp : 0 ≤ (N : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (by positivity) _
      norm_num at hp ⊢
      linarith

/-- The `1/2` power sum in the form used in logarithmic convolutions. -/
lemma sum_range_succ_rpow_neg_half_le (N : ℕ) (hN : 1 ≤ N) :
    (∑ j ∈ Finset.range N, ((j + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) ≤
      2 * (N : ℝ) ^ (1 / 2 : ℝ) := by
  have h := sum_range_succ_rpow_neg_le (1 / 2 : ℝ) (by norm_num) (by norm_num) N hN
  calc
    _ ≤ 1 + ((N : ℝ) ^ (1 - (1 / 2 : ℝ)) - 1) /
          (1 - (1 / 2 : ℝ)) := h
    _ ≤ 2 * (N : ℝ) ^ (1 / 2 : ℝ) := by
      norm_num
      linarith

/-- The tail after `N` of the `5/4` p-series. -/
lemma tsum_add_succ_rpow_neg_five_quarters_le (N : ℕ) (hN : 1 ≤ N) :
    (∑' j : ℕ, ((j + N + 1 : ℕ) : ℝ) ^ (-(5 / 4 : ℝ))) ≤
      4 * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
  let f : ℝ → ℝ := fun x ↦ x ^ (-(5 / 4 : ℝ))
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hanti : AntitoneOn f (Ici (N : ℝ)) := by
    exact (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num)).mono
      (by intro x hx; exact hNR.trans_le hx)
  have hint : IntegrableOn f (Ioi (N : ℝ)) := by
    exact integrableOn_Ioi_rpow_of_lt (by norm_num) hNR
  have hnonneg : ∀ x ∈ Ioi (N : ℝ), 0 ≤ f x := by
    intro x hx
    exact Real.rpow_nonneg (hNR.trans hx).le _
  have htail := hanti.tsum_comp_add_le_integral N hint hnonneg
  calc
    (∑' j : ℕ, ((j + N + 1 : ℕ) : ℝ) ^ (-(5 / 4 : ℝ)))
        ≤ ∫ x in Ioi (N : ℝ), x ^ (-(5 / 4 : ℝ)) := by
          simpa [f, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail
    _ = 4 * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
      rw [integral_Ioi_rpow_of_lt (by norm_num) hNR]
      norm_num
      ring

/-- Including the first term costs only one further copy of the tail scale. -/
lemma tsum_add_rpow_neg_five_quarters_le (N : ℕ) (hN : 1 ≤ N) :
    (∑' j : ℕ, ((j + N : ℕ) : ℝ) ^ (-(5 / 4 : ℝ))) ≤
      5 * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
  have hsummable : Summable
      (fun j : ℕ ↦ ((j + N : ℕ) : ℝ) ^ (-(5 / 4 : ℝ))) := by
    have hbase : Summable (fun j : ℕ ↦ (j : ℝ) ^ (-(5 / 4 : ℝ))) :=
      (Real.summable_nat_rpow (p := -(5 / 4 : ℝ))).2 (by norm_num)
    simpa [Function.comp_def] using
      hbase.comp_injective (fun _ _ h ↦ Nat.add_right_cancel h)
  rw [hsummable.tsum_eq_zero_add]
  have htail := tsum_add_succ_rpow_neg_five_quarters_le N hN
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hfirst : (N : ℝ) ^ (-(5 / 4 : ℝ)) ≤ (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
    exact Real.rpow_le_rpow_of_exponent_le hNR (by norm_num)
  have htail' :
      (∑' j : ℕ, (((j + 1) + N : ℕ) : ℝ) ^ (-(5 / 4 : ℝ))) ≤
        4 * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail
  norm_num at htail' ⊢
  linarith

/-- A uniform bound for every finite partial sum of the `5/4` p-series. -/
lemma sum_Ioo_rpow_neg_five_quarters_le_five (N : ℕ) :
    (∑ j ∈ Finset.Ioo 0 N, (j : ℝ) ^ (-(5 / 4 : ℝ))) ≤ 5 := by
  have hsummable : Summable (fun j : ℕ ↦ (j : ℝ) ^ (-(5 / 4 : ℝ))) :=
    (Real.summable_nat_rpow (p := -(5 / 4 : ℝ))).2 (by norm_num)
  have hfinite :
      (∑ j ∈ Finset.Ioo 0 N, (j : ℝ) ^ (-(5 / 4 : ℝ))) ≤
        ∑' j : ℕ, (j : ℝ) ^ (-(5 / 4 : ℝ)) := by
    exact hsummable.sum_le_tsum (Finset.Ioo 0 N)
      (fun j _ ↦ Real.rpow_nonneg (Nat.cast_nonneg j) _)
  have htail := tsum_add_rpow_neg_five_quarters_le 1 (by norm_num)
  have htotal : (∑' j : ℕ, (j : ℝ) ^ (-(5 / 4 : ℝ))) ≤ 5 := by
    rw [hsummable.tsum_eq_zero_add]
    norm_num
    simpa using htail
  exact hfinite.trans htotal

/-- Reflection permutes the positive interior indices of a natural interval. -/
lemma sum_Ioo_reflect (f : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ Finset.Ioo 0 N, f (N - j)) = ∑ j ∈ Finset.Ioo 0 N, f j := by
  classical
  apply Finset.sum_bij (fun j _ ↦ N - j)
  · intro j hj
    simp only [Finset.mem_Ioo] at hj ⊢
    omega
  · intro j₁ hj₁ j₂ hj₂ heq
    simp only [Finset.mem_Ioo] at hj₁ hj₂
    omega
  · intro j hj
    refine ⟨N - j, ?_, ?_⟩
    · simp only [Finset.mem_Ioo] at hj ⊢
      omega
    · simp only [Finset.mem_Ioo] at hj
      omega
  · intro j hj
    rfl

lemma sum_Ioo_rpow_neg_quarter_le (N : ℕ) (hN : 1 ≤ N) :
    (∑ j ∈ Finset.Ioo 0 N, (j : ℝ) ^ (-(1 / 4 : ℝ))) ≤
      2 * (N : ℝ) ^ (3 / 4 : ℝ) := by
  have hsub : Finset.Ioo 0 N ⊆ Finset.Icc 1 N := by
    intro j hj
    simp only [Finset.mem_Ioo, Finset.mem_Icc] at hj ⊢
    omega
  calc
    (∑ j ∈ Finset.Ioo 0 N, (j : ℝ) ^ (-(1 / 4 : ℝ)))
        ≤ ∑ j ∈ Finset.Icc 1 N, (j : ℝ) ^ (-(1 / 4 : ℝ)) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun j _ _ ↦ Real.rpow_nonneg (by positivity) _)
    _ = ∑ j ∈ Finset.range N, ((j + 1 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) := by
      rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      congr 2
      ring
    _ ≤ 2 * (N : ℝ) ^ (3 / 4 : ℝ) :=
      sum_range_succ_rpow_neg_quarter_le N hN

lemma sum_Ioo_rpow_neg_half_le (N : ℕ) (hN : 1 ≤ N) :
    (∑ j ∈ Finset.Ioo 0 N, (j : ℝ) ^ (-(1 / 2 : ℝ))) ≤
      2 * (N : ℝ) ^ (1 / 2 : ℝ) := by
  have hsub : Finset.Ioo 0 N ⊆ Finset.Icc 1 N := by
    intro j hj
    simp only [Finset.mem_Ioo, Finset.mem_Icc] at hj ⊢
    omega
  calc
    (∑ j ∈ Finset.Ioo 0 N, (j : ℝ) ^ (-(1 / 2 : ℝ)))
        ≤ ∑ j ∈ Finset.Icc 1 N, (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun j _ _ ↦ Real.rpow_nonneg (by positivity) _)
    _ = ∑ j ∈ Finset.range N, ((j + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      congr 2
      ring
    _ ≤ 2 * (N : ℝ) ^ (1 / 2 : ℝ) :=
      sum_range_succ_rpow_neg_half_le N hN

/-- Replacing a positive scale by half of that scale costs at most a factor
two for exponents between zero and one. -/
lemma half_rpow_neg_le_two_mul (x q : ℝ) (hx : 0 < x)
    (_hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (x / 2) ^ (-q) ≤ 2 * x ^ (-q) := by
  rw [Real.div_rpow hx.le (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv]
  have htwo : ((2 : ℝ) ^ (-q))⁻¹ ≤ 2 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv]
    simpa using Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ 2 by norm_num) hq1
  calc
    x ^ (-q) * ((2 : ℝ) ^ (-q))⁻¹ ≤ x ^ (-q) * 2 :=
      mul_le_mul_of_nonneg_left htwo (Real.rpow_nonneg hx.le _)
    _ = 2 * x ^ (-q) := by ring

/-- Version of the preceding scaling estimate for exponents up to two. -/
lemma half_rpow_neg_le_four_mul (x q : ℝ) (hx : 0 < x)
    (_hq0 : 0 ≤ q) (hq2 : q ≤ 2) :
    (x / 2) ^ (-q) ≤ 4 * x ^ (-q) := by
  rw [Real.div_rpow hx.le (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv]
  have htwo : ((2 : ℝ) ^ (-q))⁻¹ ≤ 4 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv]
    have h := Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ 2 by norm_num) hq2
    norm_num at h ⊢
    exact h
  calc
    x ^ (-q) * ((2 : ℝ) ^ (-q))⁻¹ ≤ x ^ (-q) * 4 :=
      mul_le_mul_of_nonneg_left htwo (Real.rpow_nonneg hx.le _)
    _ = 4 * x ^ (-q) := by ring

/-- A split-at-half bound for the convolution occurring in Proposition 3.
The deliberately unsimplified right side exposes the two endpoint power sums
and is convenient for later rewriting by `Real.div_rpow`. -/
lemma convolution_quarter_half_le (N : ℕ) (hN : 2 ≤ N) :
    (∑ j ∈ Finset.Ioo 0 N,
        (j : ℝ) ^ (-(1 / 4 : ℝ)) *
          ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) ≤
      2 * (N : ℝ) ^ (3 / 4 : ℝ) *
          ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) +
        2 * (N : ℝ) ^ (1 / 2 : ℝ) *
          ((N : ℝ) / 2) ^ (-(1 / 4 : ℝ)) := by
  classical
  let S := Finset.Ioo 0 N
  let low : Finset ℕ := S.filter (fun j ↦ 2 * j ≤ N)
  let high : Finset ℕ := S.filter (fun j ↦ ¬ 2 * j ≤ N)
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN)
  have hhalf : (0 : ℝ) < (N : ℝ) / 2 := by positivity
  have hsplit :
      (∑ j ∈ S,
          (j : ℝ) ^ (-(1 / 4 : ℝ)) *
            ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) =
        (∑ j ∈ low,
          (j : ℝ) ^ (-(1 / 4 : ℝ)) *
            ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) +
        ∑ j ∈ high,
          (j : ℝ) ^ (-(1 / 4 : ℝ)) *
            ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
    exact (Finset.sum_filter_add_sum_filter_not S (fun j ↦ 2 * j ≤ N)
      (fun j ↦ (j : ℝ) ^ (-(1 / 4 : ℝ)) *
        ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)))).symm
  have hlow :
      (∑ j ∈ low,
          (j : ℝ) ^ (-(1 / 4 : ℝ)) *
            ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) ≤
        2 * (N : ℝ) ^ (3 / 4 : ℝ) *
          ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) := by
    calc
      _ ≤ ∑ j ∈ low, (j : ℝ) ^ (-(1 / 4 : ℝ)) *
            ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjS := (Finset.mem_filter.mp hj).1
        have hjlow := (Finset.mem_filter.mp hj).2
        have hjlt : j < N := (Finset.mem_Ioo.mp hjS).2
        have hbase : (N : ℝ) / 2 ≤ ((N - j : ℕ) : ℝ) := by
          have hNat : N ≤ 2 * (N - j) := by omega
          have hcast : (N : ℝ) ≤ 2 * ((N - j : ℕ) : ℝ) := by
            exact_mod_cast hNat
          linarith
        have hpow := Real.rpow_le_rpow_of_nonpos hhalf hbase
          (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)
        exact mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (by positivity) _)
      _ = ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) *
            ∑ j ∈ low, (j : ℝ) ^ (-(1 / 4 : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) *
            ∑ j ∈ S, (j : ℝ) ^ (-(1 / 4 : ℝ)) := by
        gcongr
        simpa [low] using Finset.filter_subset (fun j ↦ 2 * j ≤ N) S
      _ ≤ ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) *
            (2 * (N : ℝ) ^ (3 / 4 : ℝ)) := by
        gcongr
        exact sum_Ioo_rpow_neg_quarter_le N (by omega)
      _ = 2 * (N : ℝ) ^ (3 / 4 : ℝ) *
            ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) := by ring
  have hhigh :
      (∑ j ∈ high,
          (j : ℝ) ^ (-(1 / 4 : ℝ)) *
            ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) ≤
        2 * (N : ℝ) ^ (1 / 2 : ℝ) *
          ((N : ℝ) / 2) ^ (-(1 / 4 : ℝ)) := by
    calc
      _ ≤ ∑ j ∈ high, ((N : ℝ) / 2) ^ (-(1 / 4 : ℝ)) *
            ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjS := (Finset.mem_filter.mp hj).1
        have hjhigh := (Finset.mem_filter.mp hj).2
        have hjpos : 0 < j := (Finset.mem_Ioo.mp hjS).1
        have hbase : (N : ℝ) / 2 ≤ (j : ℝ) := by
          have hNat : N ≤ 2 * j := by omega
          have hcast : (N : ℝ) ≤ 2 * (j : ℝ) := by exact_mod_cast hNat
          linarith
        have hpow := Real.rpow_le_rpow_of_nonpos hhalf hbase
          (by norm_num : (-(1 / 4 : ℝ)) ≤ 0)
        exact mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (by positivity) _)
      _ = ((N : ℝ) / 2) ^ (-(1 / 4 : ℝ)) *
            ∑ j ∈ high, ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [Finset.mul_sum]
      _ ≤ ((N : ℝ) / 2) ^ (-(1 / 4 : ℝ)) *
            ∑ j ∈ S, ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
        gcongr
        simpa [high] using Finset.filter_subset (fun j ↦ ¬ 2 * j ≤ N) S
      _ = ((N : ℝ) / 2) ^ (-(1 / 4 : ℝ)) *
            ∑ j ∈ S, (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
        dsimp [S]
        apply congrArg (fun z : ℝ ↦ ((N : ℝ) / 2) ^ (-(1 / 4 : ℝ)) * z)
        exact sum_Ioo_reflect (fun j ↦ (j : ℝ) ^ (-(1 / 2 : ℝ))) N
      _ ≤ ((N : ℝ) / 2) ^ (-(1 / 4 : ℝ)) *
            (2 * (N : ℝ) ^ (1 / 2 : ℝ)) := by
        gcongr
        exact sum_Ioo_rpow_neg_half_le N (by omega)
      _ = 2 * (N : ℝ) ^ (1 / 2 : ℝ) *
            ((N : ℝ) / 2) ^ (-(1 / 4 : ℝ)) := by ring
  rw [show (∑ j ∈ Finset.Ioo 0 N,
      (j : ℝ) ^ (-(1 / 4 : ℝ)) *
        ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) =
      (∑ j ∈ S, (j : ℝ) ^ (-(1 / 4 : ℝ)) *
        ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) by rfl, hsplit]
  exact add_le_add hlow hhigh

/-- Simplified `O(N^(1/4))` form of `convolution_quarter_half_le`. -/
lemma convolution_quarter_half_le_eight (N : ℕ) (hN : 2 ≤ N) :
    (∑ j ∈ Finset.Ioo 0 N,
        (j : ℝ) ^ (-(1 / 4 : ℝ)) *
          ((N - j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) ≤
      8 * (N : ℝ) ^ (1 / 4 : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN)
  have hsplit := convolution_quarter_half_le N hN
  have hhalf := half_rpow_neg_le_two_mul (N : ℝ) (1 / 2 : ℝ) hNR
    (by norm_num) (by norm_num)
  have hquarter := half_rpow_neg_le_two_mul (N : ℝ) (1 / 4 : ℝ) hNR
    (by norm_num) (by norm_num)
  calc
    _ ≤ 2 * (N : ℝ) ^ (3 / 4 : ℝ) *
          ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) +
        2 * (N : ℝ) ^ (1 / 2 : ℝ) *
          ((N : ℝ) / 2) ^ (-(1 / 4 : ℝ)) := hsplit
    _ ≤ 2 * (N : ℝ) ^ (3 / 4 : ℝ) *
          (2 * (N : ℝ) ^ (-(1 / 2 : ℝ))) +
        2 * (N : ℝ) ^ (1 / 2 : ℝ) *
          (2 * (N : ℝ) ^ (-(1 / 4 : ℝ))) := by
      gcongr
    _ = 4 * ((N : ℝ) ^ (3 / 4 : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ))) +
          4 * ((N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (-(1 / 4 : ℝ))) := by
      ring
    _ = 8 * (N : ℝ) ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add hNR, ← Real.rpow_add hNR]
      norm_num
      ring

/-- The second endpoint convolution needed in the logarithmic estimates.  Its
`5/4` endpoint is summable, so the final scale is `N^(-1/2)`. -/
lemma convolution_half_five_quarters_le (N : ℕ) (hN : 2 ≤ N) :
    (∑ j ∈ Finset.Ioo 0 N,
        (j : ℝ) ^ (-(1 / 2 : ℝ)) *
          ((N - j : ℕ) : ℝ) ^ (-(5 / 4 : ℝ))) ≤
      2 * (N : ℝ) ^ (1 / 2 : ℝ) *
          ((N : ℝ) / 2) ^ (-(5 / 4 : ℝ)) +
        5 * ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) := by
  classical
  let S := Finset.Ioo 0 N
  let low : Finset ℕ := S.filter (fun j ↦ 2 * j ≤ N)
  let high : Finset ℕ := S.filter (fun j ↦ ¬ 2 * j ≤ N)
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN)
  have hhalf : (0 : ℝ) < (N : ℝ) / 2 := by positivity
  have hsplit :
      (∑ j ∈ S,
          (j : ℝ) ^ (-(1 / 2 : ℝ)) *
            ((N - j : ℕ) : ℝ) ^ (-(5 / 4 : ℝ))) =
        (∑ j ∈ low,
          (j : ℝ) ^ (-(1 / 2 : ℝ)) *
            ((N - j : ℕ) : ℝ) ^ (-(5 / 4 : ℝ))) +
        ∑ j ∈ high,
          (j : ℝ) ^ (-(1 / 2 : ℝ)) *
            ((N - j : ℕ) : ℝ) ^ (-(5 / 4 : ℝ)) := by
    exact (Finset.sum_filter_add_sum_filter_not S (fun j ↦ 2 * j ≤ N)
      (fun j ↦ (j : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((N - j : ℕ) : ℝ) ^ (-(5 / 4 : ℝ)))).symm
  have hlow :
      (∑ j ∈ low,
          (j : ℝ) ^ (-(1 / 2 : ℝ)) *
            ((N - j : ℕ) : ℝ) ^ (-(5 / 4 : ℝ))) ≤
        2 * (N : ℝ) ^ (1 / 2 : ℝ) *
          ((N : ℝ) / 2) ^ (-(5 / 4 : ℝ)) := by
    calc
      _ ≤ ∑ j ∈ low, (j : ℝ) ^ (-(1 / 2 : ℝ)) *
            ((N : ℝ) / 2) ^ (-(5 / 4 : ℝ)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjS := (Finset.mem_filter.mp hj).1
        have hjlow := (Finset.mem_filter.mp hj).2
        have hjlt : j < N := (Finset.mem_Ioo.mp hjS).2
        have hbase : (N : ℝ) / 2 ≤ ((N - j : ℕ) : ℝ) := by
          have hNat : N ≤ 2 * (N - j) := by omega
          have hcast : (N : ℝ) ≤ 2 * ((N - j : ℕ) : ℝ) := by
            exact_mod_cast hNat
          linarith
        have hpow := Real.rpow_le_rpow_of_nonpos hhalf hbase
          (by norm_num : (-(5 / 4 : ℝ)) ≤ 0)
        exact mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (by positivity) _)
      _ = ((N : ℝ) / 2) ^ (-(5 / 4 : ℝ)) *
            ∑ j ∈ low, (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ ((N : ℝ) / 2) ^ (-(5 / 4 : ℝ)) *
            ∑ j ∈ S, (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
        gcongr
        simpa [low] using Finset.filter_subset (fun j ↦ 2 * j ≤ N) S
      _ ≤ ((N : ℝ) / 2) ^ (-(5 / 4 : ℝ)) *
            (2 * (N : ℝ) ^ (1 / 2 : ℝ)) := by
        gcongr
        exact sum_Ioo_rpow_neg_half_le N (by omega)
      _ = 2 * (N : ℝ) ^ (1 / 2 : ℝ) *
            ((N : ℝ) / 2) ^ (-(5 / 4 : ℝ)) := by ring
  have hhigh :
      (∑ j ∈ high,
          (j : ℝ) ^ (-(1 / 2 : ℝ)) *
            ((N - j : ℕ) : ℝ) ^ (-(5 / 4 : ℝ))) ≤
        5 * ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) := by
    calc
      _ ≤ ∑ j ∈ high, ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) *
            ((N - j : ℕ) : ℝ) ^ (-(5 / 4 : ℝ)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjS := (Finset.mem_filter.mp hj).1
        have hjhigh := (Finset.mem_filter.mp hj).2
        have hbase : (N : ℝ) / 2 ≤ (j : ℝ) := by
          have hNat : N ≤ 2 * j := by omega
          have hcast : (N : ℝ) ≤ 2 * (j : ℝ) := by exact_mod_cast hNat
          linarith
        have hpow := Real.rpow_le_rpow_of_nonpos hhalf hbase
          (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)
        exact mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (by positivity) _)
      _ = ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) *
            ∑ j ∈ high, ((N - j : ℕ) : ℝ) ^ (-(5 / 4 : ℝ)) := by
        rw [Finset.mul_sum]
      _ ≤ ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) *
            ∑ j ∈ S, ((N - j : ℕ) : ℝ) ^ (-(5 / 4 : ℝ)) := by
        gcongr
        simpa [high] using Finset.filter_subset (fun j ↦ ¬ 2 * j ≤ N) S
      _ = ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) *
            ∑ j ∈ S, (j : ℝ) ^ (-(5 / 4 : ℝ)) := by
        dsimp [S]
        apply congrArg (fun z : ℝ ↦ ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) * z)
        exact sum_Ioo_reflect (fun j ↦ (j : ℝ) ^ (-(5 / 4 : ℝ))) N
      _ ≤ ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) * 5 := by
        gcongr
        exact sum_Ioo_rpow_neg_five_quarters_le_five N
      _ = 5 * ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) := by ring
  rw [show (∑ j ∈ Finset.Ioo 0 N,
      (j : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((N - j : ℕ) : ℝ) ^ (-(5 / 4 : ℝ))) =
      (∑ j ∈ S, (j : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((N - j : ℕ) : ℝ) ^ (-(5 / 4 : ℝ))) by rfl, hsplit]
  exact add_le_add hlow hhigh

/-- Simplified form of the `1/2`--`5/4` endpoint convolution. -/
lemma convolution_half_five_quarters_le_eighteen (N : ℕ) (hN : 2 ≤ N) :
    (∑ j ∈ Finset.Ioo 0 N,
        (j : ℝ) ^ (-(1 / 2 : ℝ)) *
          ((N - j : ℕ) : ℝ) ^ (-(5 / 4 : ℝ))) ≤
      18 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hsplit := convolution_half_five_quarters_le N hN
  have hfive := half_rpow_neg_le_four_mul (N : ℝ) (5 / 4 : ℝ) hNR
    (by norm_num) (by norm_num)
  have hhalf := half_rpow_neg_le_two_mul (N : ℝ) (1 / 2 : ℝ) hNR
    (by norm_num) (by norm_num)
  have hexp : (N : ℝ) ^ (-(3 / 4 : ℝ)) ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  calc
    _ ≤ 2 * (N : ℝ) ^ (1 / 2 : ℝ) *
          ((N : ℝ) / 2) ^ (-(5 / 4 : ℝ)) +
        5 * ((N : ℝ) / 2) ^ (-(1 / 2 : ℝ)) := hsplit
    _ ≤ 2 * (N : ℝ) ^ (1 / 2 : ℝ) *
          (4 * (N : ℝ) ^ (-(5 / 4 : ℝ))) +
        5 * (2 * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
      gcongr
    _ = 8 * (N : ℝ) ^ (-(3 / 4 : ℝ)) +
          10 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
      calc
        _ = 8 * ((N : ℝ) ^ (1 / 2 : ℝ) *
              (N : ℝ) ^ (-(5 / 4 : ℝ))) +
            10 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by ring
        _ = _ := by
          rw [← Real.rpow_add hNR]
          norm_num
    _ ≤ 8 * (N : ℝ) ^ (-(1 / 2 : ℝ)) +
          10 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by gcongr
    _ = 18 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by ring

end LogConvolution448
