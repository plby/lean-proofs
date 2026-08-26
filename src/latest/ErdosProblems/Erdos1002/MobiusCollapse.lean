import ErdosProblems.Erdos1002.HStar
import ErdosProblems.Erdos1002.RamanujanIdentities
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The arithmetic core of the Möbius collapse

This file isolates the exact convolution that occurs after inserting the
divisor--Möbius formula for a Ramanujan sum.  Keeping the midpoint cutoff as
an explicit three-valued function makes the equality case visible to Lean.
-/

open scoped ArithmeticFunction.Moebius BigOperators

namespace Erdos1002

noncomputable section

set_option maxHeartbeats 1000000

/-- The value `1`, `1/2`, or `0` attached to a strict tail, its endpoint,
or its complement. -/
def midpointTailWeight (n scale m : ℕ) : ℝ :=
  if n < m * scale then 1 else if n = m * scale then 1 / 2 else 0

theorem midpointTailWeight_nonneg (n scale m : ℕ) :
    0 ≤ midpointTailWeight n scale m := by
  unfold midpointTailWeight
  split_ifs <;> norm_num

theorem midpointTailWeight_le_one (n scale m : ℕ) :
    midpointTailWeight n scale m ≤ 1 := by
  unfold midpointTailWeight
  split_ifs <;> norm_num

theorem hStarRatioWeight_eq_mul_midpoint (n scale k : ℕ) :
    hStarRatioWeight n scale k =
      inverseSquare k * midpointTailWeight n scale k := by
  unfold hStarRatioWeight midpointTailWeight
  split_ifs <;> ring

/-- On a divisor pair `r * k = m`, the inverse-square denominator is exactly
`m²`; this is the finite algebraic step behind the collapse. -/
theorem weighted_moebius_divisor_sum (m : ℕ) (hm : m ≠ 0) :
    (∑ r ∈ m.divisors,
      (ArithmeticFunction.moebius r : ℝ) /
        ((r : ℝ) ^ 2 * ((m / r : ℕ) : ℝ) ^ 2)) =
      if m = 1 then 1 else 0 := by
  have hterm : ∀ r ∈ m.divisors,
      (ArithmeticFunction.moebius r : ℝ) /
          ((r : ℝ) ^ 2 * ((m / r : ℕ) : ℝ) ^ 2) =
        (ArithmeticFunction.moebius r : ℝ) / (m : ℝ) ^ 2 := by
    intro r hr
    have hrdvd : r ∣ m := Nat.dvd_of_mem_divisors hr
    have hprod : r * (m / r) = m := Nat.mul_div_cancel' hrdvd
    have hprodR : (r : ℝ) * ((m / r : ℕ) : ℝ) = (m : ℝ) := by
      exact_mod_cast hprod
    rw [show (r : ℝ) ^ 2 * ((m / r : ℕ) : ℝ) ^ 2 =
        ((r : ℝ) * ((m / r : ℕ) : ℝ)) ^ 2 by ring, hprodR]
  rw [Finset.sum_congr rfl hterm]
  rw [← Finset.sum_div]
  have hmob : (∑ r ∈ m.divisors, (ArithmeticFunction.moebius r : ℝ)) =
      if m = 1 then 1 else 0 := by
    exact_mod_cast sum_moebius_divisors m
  rw [hmob]
  by_cases hm1 : m = 1
  · subst m
    norm_num
  · simp [hm1]

/-- Multiplying the finite convolution by a coefficient depending only on
the product does not change the cancellation away from `m = 1`. -/
theorem weighted_moebius_divisor_sum_mul (n scale m : ℕ) (hm : m ≠ 0) :
    (∑ r ∈ m.divisors,
      ((ArithmeticFunction.moebius r : ℝ) /
          ((r : ℝ) ^ 2 * ((m / r : ℕ) : ℝ) ^ 2)) *
        midpointTailWeight n scale m) =
      if m = 1 then midpointTailWeight n scale 1 else 0 := by
  rw [← Finset.sum_mul]
  rw [weighted_moebius_divisor_sum m hm]
  by_cases hm1 : m = 1
  · simp [hm1]
  · simp [hm1]

/-- The Möbius factor in the absolutely convergent product series, indexed
only by positive integers. -/
def mobiusSquareTerm (r : ℕ+) : ℝ :=
  (ArithmeticFunction.moebius (r : ℕ) : ℝ) / (r : ℝ) ^ 2

/-- The inverse-square factor in the same product series. -/
def positiveInverseSquareTerm (k : ℕ+) : ℝ :=
  1 / (k : ℝ) ^ 2

theorem summable_positiveInverseSquareTerm :
    Summable positiveInverseSquareTerm := by
  have h := (Real.summable_one_div_nat_pow.mpr
    (by norm_num : 1 < (2 : ℕ))).comp_injective PNat.coe_injective
  simpa only [Function.comp_apply, positiveInverseSquareTerm] using! h

theorem summable_norm_positiveInverseSquareTerm :
    Summable fun k ↦ ‖positiveInverseSquareTerm k‖ := by
  simpa only [positiveInverseSquareTerm, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (1 / (_ : ℝ) ^ 2))] using!
      summable_positiveInverseSquareTerm

theorem summable_norm_mobiusSquareTerm :
    Summable fun r ↦ ‖mobiusSquareTerm r‖ := by
  apply Summable.of_nonneg_of_le
      (f := fun r : ℕ+ ↦ positiveInverseSquareTerm r)
  · exact fun _ ↦ norm_nonneg _
  · intro r
    have hrpos : (0 : ℝ) < (r : ℝ) := by positivity
    have hμ : |(ArithmeticFunction.moebius (r : ℕ) : ℝ)| ≤ 1 := by
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := (r : ℕ)))
    rw [mobiusSquareTerm, positiveInverseSquareTerm, Real.norm_eq_abs, abs_div,
      abs_pow, abs_of_pos hrpos]
    exact div_le_div_of_nonneg_right hμ (sq_nonneg (r : ℝ))
  · exact summable_positiveInverseSquareTerm

/-- The absolutely convergent double series before grouping by `m = r*k`. -/
def mobiusCollapseProductTerm (n scale : ℕ) (rk : ℕ+ × ℕ+) : ℝ :=
  mobiusSquareTerm rk.1 * positiveInverseSquareTerm rk.2 *
    midpointTailWeight n scale ((rk.1 : ℕ) * (rk.2 : ℕ))

theorem summable_mobiusCollapseProductTerm (n scale : ℕ) :
    Summable (mobiusCollapseProductTerm n scale) := by
  apply Summable.of_norm
  have hdom : Summable fun rk : ℕ+ × ℕ+ ↦
      ‖mobiusSquareTerm rk.1‖ * ‖positiveInverseSquareTerm rk.2‖ := by
    exact summable_norm_mobiusSquareTerm.mul_of_nonneg
      summable_norm_positiveInverseSquareTerm
      (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)
  apply hdom.of_nonneg_of_le
  · exact fun _ ↦ norm_nonneg _
  · rintro ⟨r, k⟩
    rw [mobiusCollapseProductTerm, norm_mul, norm_mul]
    have hw0 := midpointTailWeight_nonneg n scale ((r : ℕ) * (k : ℕ))
    have hw1 := midpointTailWeight_le_one n scale ((r : ℕ) * (k : ℕ))
    change ‖mobiusSquareTerm r‖ * ‖positiveInverseSquareTerm k‖ *
      ‖midpointTailWeight n scale ((r : ℕ) * (k : ℕ))‖ ≤
        ‖mobiusSquareTerm r‖ * ‖positiveInverseSquareTerm k‖
    rw [Real.norm_of_nonneg hw0]
    exact mul_le_of_le_one_right
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hw1

/-- The natural-number form of the double-series summand.  It is used after
the product series has been transported to divisor antidiagonals. -/
def naturalCollapsePairTerm (n scale : ℕ) (rk : ℕ × ℕ) : ℝ :=
  (ArithmeticFunction.moebius rk.1 : ℝ) /
      ((rk.1 : ℝ) ^ 2 * (rk.2 : ℝ) ^ 2) *
    midpointTailWeight n scale (rk.1 * rk.2)

private theorem collapseTerm_factors_eq (n scale : ℕ) (m : ℕ+)
    (x : (m : ℕ).divisorsAntidiagonal) :
    mobiusCollapseProductTerm n scale (divisorsAntidiagonalFactors m x) =
      naturalCollapsePairTerm n scale x := by
  simp only [mobiusCollapseProductTerm, mobiusSquareTerm,
    positiveInverseSquareTerm, naturalCollapsePairTerm,
    divisorsAntidiagonalFactors, PNat.mk_coe]
  ring

private theorem collapse_antidiagonal_sum (n scale : ℕ) (m : ℕ+) :
    (∑' x : (m : ℕ).divisorsAntidiagonal,
      mobiusCollapseProductTerm n scale (divisorsAntidiagonalFactors m x)) =
      if (m : ℕ) = 1 then midpointTailWeight n scale 1 else 0 := by
  calc
    (∑' x : (m : ℕ).divisorsAntidiagonal,
        mobiusCollapseProductTerm n scale (divisorsAntidiagonalFactors m x)) =
        ∑' x : (m : ℕ).divisorsAntidiagonal,
          naturalCollapsePairTerm n scale x := by
            apply tsum_congr
            exact collapseTerm_factors_eq n scale m
    _ = ∑ x ∈ (m : ℕ).divisorsAntidiagonal,
          naturalCollapsePairTerm n scale x :=
      Finset.tsum_subtype' (m : ℕ).divisorsAntidiagonal
        (naturalCollapsePairTerm n scale)
    _ = ∑ r ∈ (m : ℕ).divisors,
          naturalCollapsePairTerm n scale (r, (m : ℕ) / r) := by
      exact Nat.sum_divisorsAntidiagonal
        (fun r k ↦ naturalCollapsePairTerm n scale (r, k))
    _ = ∑ r ∈ (m : ℕ).divisors,
          ((ArithmeticFunction.moebius r : ℝ) /
              ((r : ℝ) ^ 2 * ((((m : ℕ) / r : ℕ) : ℝ)) ^ 2)) *
            midpointTailWeight n scale (m : ℕ) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrdvd : r ∣ (m : ℕ) := Nat.dvd_of_mem_divisors hr
      have hprod : r * ((m : ℕ) / r) = (m : ℕ) := Nat.mul_div_cancel' hrdvd
      simp only [naturalCollapsePairTerm]
      rw [hprod]
    _ = if (m : ℕ) = 1 then midpointTailWeight n scale 1 else 0 :=
      weighted_moebius_divisor_sum_mul n scale (m : ℕ) m.ne_zero

/-- Exact regrouping of the absolutely convergent double series.  Every
product antidiagonal cancels by Möbius inversion except `r*k = 1`; the
endpoint weight is therefore retained without approximation. -/
theorem tsum_mobiusCollapseProductTerm (n scale : ℕ) :
    (∑' rk : ℕ+ × ℕ+, mobiusCollapseProductTerm n scale rk) =
      midpointTailWeight n scale 1 := by
  have hsigma : Summable
      (mobiusCollapseProductTerm n scale ∘ sigmaAntidiagonalEquivProd) :=
    (sigmaAntidiagonalEquivProd.summable_iff).2
      (summable_mobiusCollapseProductTerm n scale)
  calc
    (∑' rk : ℕ+ × ℕ+, mobiusCollapseProductTerm n scale rk) =
        ∑' z : (m : ℕ+) × (m : ℕ).divisorsAntidiagonal,
          mobiusCollapseProductTerm n scale (sigmaAntidiagonalEquivProd z) := by
      symm
      exact sigmaAntidiagonalEquivProd.tsum_eq (mobiusCollapseProductTerm n scale)
    _ = ∑' m : ℕ+, ∑' x : (m : ℕ).divisorsAntidiagonal,
          mobiusCollapseProductTerm n scale
            (sigmaAntidiagonalEquivProd ⟨m, x⟩) := hsigma.tsum_sigma
    _ = ∑' m : ℕ+,
          (if (m : ℕ) = 1 then midpointTailWeight n scale 1 else 0) := by
      apply tsum_congr
      intro m
      simpa [sigmaAntidiagonalEquivProd] using! collapse_antidiagonal_sum n scale m
    _ = midpointTailWeight n scale 1 := by
      rw [tsum_eq_single (1 : ℕ+)]
      · simp
      · intro m hm
        have hval : (m : ℕ) ≠ 1 := by
          intro h
          apply hm
          exact PNat.eq h
        simp [hval]

/-- The inner positive-`k` tail in the product series is exactly the sampled
`H_*` function. -/
theorem tsum_positiveInverseSquare_mul_midpoint (n scale : ℕ) (r : ℕ+) :
    (∑' k : ℕ+, positiveInverseSquareTerm k *
      midpointTailWeight n scale ((r : ℕ) * (k : ℕ))) =
      hStarRatio n ((r : ℕ) * scale) := by
  have hsum := summable_hStarRatioWeight n ((r : ℕ) * scale)
  have hzero : hStarRatioWeight n ((r : ℕ) * scale) 0 = 0 := by
    simp [hStarRatioWeight, inverseSquare]
  have hpnat := tsum_zero_pnat_eq_tsum_nat hsum
  rw [hzero, zero_add] at hpnat
  calc
    (∑' k : ℕ+, positiveInverseSquareTerm k *
        midpointTailWeight n scale ((r : ℕ) * (k : ℕ))) =
        ∑' k : ℕ+, hStarRatioWeight n ((r : ℕ) * scale) (k : ℕ) := by
      apply tsum_congr
      intro k
      rw [hStarRatioWeight_eq_mul_midpoint]
      simp [positiveInverseSquareTerm, inverseSquare_eq, midpointTailWeight,
        mul_assoc, mul_comm]
    _ = ∑' k : ℕ, hStarRatioWeight n ((r : ℕ) * scale) k := hpnat
    _ = hStarRatio n ((r : ℕ) * scale) := rfl

/-- Möbius inversion collapses the whole inverse-square `r,k` tail to the
single midpoint comparison at product one.  This is the infinite-series
identity used verbatim inside the paper's coefficient calculation. -/
theorem tsum_mobiusSquare_mul_hStarRatio (n scale : ℕ) :
    (∑' r : ℕ+, mobiusSquareTerm r *
      hStarRatio n ((r : ℕ) * scale)) =
      midpointTailWeight n scale 1 := by
  calc
    (∑' r : ℕ+, mobiusSquareTerm r *
        hStarRatio n ((r : ℕ) * scale)) =
        ∑' r : ℕ+, mobiusSquareTerm r *
          (∑' k : ℕ+, positiveInverseSquareTerm k *
            midpointTailWeight n scale ((r : ℕ) * (k : ℕ))) := by
      apply tsum_congr
      intro r
      rw [tsum_positiveInverseSquare_mul_midpoint]
    _ = ∑' r : ℕ+, ∑' k : ℕ+,
          mobiusCollapseProductTerm n scale (r, k) := by
      apply tsum_congr
      intro r
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      simp [mobiusCollapseProductTerm, mul_assoc]
    _ = ∑' rk : ℕ+ × ℕ+, mobiusCollapseProductTerm n scale rk := by
      symm
      exact (summable_mobiusCollapseProductTerm n scale).tsum_prod
    _ = midpointTailWeight n scale 1 :=
      tsum_mobiusCollapseProductTerm n scale

theorem summable_mobiusSquare_mul_hStarRatio (n scale : ℕ) :
    Summable fun r : ℕ+ ↦ mobiusSquareTerm r *
      hStarRatio n ((r : ℕ) * scale) := by
  have hsigma := (summable_mobiusCollapseProductTerm n scale).prod
  apply hsigma.congr
  intro r
  change (∑' k : ℕ+, mobiusCollapseProductTerm n scale (r, k)) = _
  calc
    (∑' k : ℕ+, mobiusCollapseProductTerm n scale (r, k)) =
        mobiusSquareTerm r *
          (∑' k : ℕ+, positiveInverseSquareTerm k *
            midpointTailWeight n scale ((r : ℕ) * (k : ℕ))) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      simp [mobiusCollapseProductTerm, mul_assoc]
    _ = mobiusSquareTerm r * hStarRatio n ((r : ℕ) * scale) := by
      rw [tsum_positiveInverseSquare_mul_midpoint]

/-- Reindex the surviving divisor `a` by its complementary divisor
`d = n/a`. -/
theorem midpoint_divisor_sum_reindex (n N : ℕ) (hn : n ≠ 0) :
    (∑ a ∈ n.divisors,
        (1 / (a : ℝ)) * midpointTailWeight n (a * N) 1) =
      ∑ d ∈ n.divisors,
        ((d : ℝ) / (n : ℝ)) * midpointTailWeight d N 1 := by
  let f : ℕ → ℕ → ℝ := fun a _d ↦
    (1 / (a : ℝ)) * midpointTailWeight n (a * N) 1
  calc
    (∑ a ∈ n.divisors,
        (1 / (a : ℝ)) * midpointTailWeight n (a * N) 1) =
        ∑ a ∈ n.divisors, f a (n / a) := by rfl
    _ = ∑ x ∈ n.divisorsAntidiagonal, f x.1 x.2 := by
      symm
      exact Nat.sum_divisorsAntidiagonal f
    _ = ∑ d ∈ n.divisors, f (n / d) d :=
      Nat.sum_divisorsAntidiagonal' f
    _ = ∑ d ∈ n.divisors,
        ((d : ℝ) / (n : ℝ)) * midpointTailWeight d N 1 := by
      apply Finset.sum_congr rfl
      intro d hd
      have hddvd : d ∣ n := Nat.dvd_of_mem_divisors hd
      have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
      have hqpos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hddvd) hdpos
      have hprod : (n / d) * d = n := Nat.div_mul_cancel hddvd
      have hrecip : (1 / ((n / d : ℕ) : ℝ)) = (d : ℝ) / (n : ℝ) := by
        have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
        have hprodR : (((n / d : ℕ) : ℝ) * (d : ℝ)) = (n : ℝ) := by
          exact_mod_cast hprod
        rw [← hprodR]
        field_simp
      have hlt : n < (n / d) * N ↔ d < N := by
        have h : (n / d) * d < (n / d) * N ↔ d < N :=
          Nat.mul_lt_mul_left hqpos
        rw [hprod] at h
        exact h
      have heq : n = (n / d) * N ↔ d = N := by
        constructor
        · intro h
          exact Nat.mul_left_cancel hqpos (hprod.trans h)
        · intro h
          exact hprod.symm.trans (congrArg (fun x ↦ (n / d) * x) h)
      have hweight : midpointTailWeight n ((n / d) * N) 1 =
          midpointTailWeight d N 1 := by
        by_cases hdlt : d < N
        · have hnlt : n < (n / d) * N := hlt.mpr hdlt
          simp only [midpointTailWeight, one_mul]
          rw [if_pos hnlt, if_pos hdlt]
        · have hnlt : ¬n < (n / d) * N := fun h ↦ hdlt (hlt.mp h)
          by_cases hdeq : d = N
          · have hneq : n = (n / d) * N := heq.mpr hdeq
            simp only [midpointTailWeight, one_mul]
            rw [if_neg hnlt, if_pos hneq, if_neg hdlt, if_pos hdeq]
          · have hneq : ¬n = (n / d) * N := fun h ↦ hdeq (heq.mp h)
            simp only [midpointTailWeight, one_mul]
            rw [if_neg hnlt, if_neg hneq, if_neg hdlt, if_neg hdeq]
      change (1 / ((n / d : ℕ) : ℝ)) *
          midpointTailWeight n ((n / d) * N) 1 = _
      rw [hrecip, hweight]

/-- Closed form of the surviving divisor sum, including the half-weight at
`d = N`. -/
theorem midpoint_divisor_sum_eq (n N : ℕ) (hn : n ≠ 0) :
    (∑ a ∈ n.divisors,
        (1 / (a : ℝ)) * midpointTailWeight n (a * N) 1) =
      (1 / (n : ℝ)) *
        ((∑ d ∈ n.divisors.filter (fun d ↦ d < N), (d : ℝ)) +
          if N ∣ n then (N : ℝ) / 2 else 0) := by
  rw [midpoint_divisor_sum_reindex n N hn]
  have hNmem : N ∈ n.divisors ↔ N ∣ n := by
    simp [Nat.mem_divisors, hn]
  have hterm (d : ℕ) :
      (d : ℝ) * midpointTailWeight d N 1 =
        (if d < N then (d : ℝ) else 0) +
          (if d = N then (d : ℝ) / 2 else 0) := by
    simp only [midpointTailWeight, one_mul]
    by_cases hlt : d < N
    · simp [hlt, ne_of_lt hlt]
    · by_cases heq : d = N
      · simp [heq]
        ring
      · simp [hlt, heq]
  have hendpoint :
      (∑ d ∈ n.divisors, if d = N then (d : ℝ) / 2 else 0) =
        if N ∈ n.divisors then (N : ℝ) / 2 else 0 := by
    by_cases hmem : N ∈ n.divisors <;> simp [hmem]
  calc
    (∑ d ∈ n.divisors,
        (d : ℝ) / (n : ℝ) * midpointTailWeight d N 1) =
        (1 / (n : ℝ)) *
          ∑ d ∈ n.divisors, (d : ℝ) * midpointTailWeight d N 1 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _hd
      ring
    _ = (1 / (n : ℝ)) *
        ((∑ d ∈ n.divisors.filter (fun d ↦ d < N), (d : ℝ)) +
          if N ∣ n then (N : ℝ) / 2 else 0) := by
      congr 1
      calc
        (∑ d ∈ n.divisors, (d : ℝ) * midpointTailWeight d N 1) =
            (∑ d ∈ n.divisors, if d < N then (d : ℝ) else 0) +
              ∑ d ∈ n.divisors, if d = N then (d : ℝ) / 2 else 0 := by
          simp_rw [hterm]
          exact Finset.sum_add_distrib
        _ = (∑ d ∈ n.divisors.filter (fun d ↦ d < N), (d : ℝ)) +
              if N ∈ n.divisors then (N : ℝ) / 2 else 0 := by
          rw [Finset.sum_filter, hendpoint]
        _ = (∑ d ∈ n.divisors.filter (fun d ↦ d < N), (d : ℝ)) +
              if N ∣ n then (N : ℝ) / 2 else 0 := by
          by_cases hNdvd : N ∣ n
          · have hNdiv : N ∈ n.divisors := hNmem.mpr hNdvd
            simp [hNdvd, hNdiv]
          · have hNdiv : N ∉ n.divisors := fun h ↦ hNdvd (hNmem.mp h)
            simp [hNdvd, hNdiv]

/-- The exact double divisor--Möbius form occurring after the Ramanujan
divisor formula has been inserted. -/
theorem divisor_mobius_hStar_collapse (n N : ℕ) (hn : n ≠ 0) :
    (∑ a ∈ n.divisors, (1 / (a : ℝ)) *
      (∑' r : ℕ+, mobiusSquareTerm r *
        hStarRatio n (a * (r : ℕ) * N))) =
      (1 / (n : ℝ)) *
        ((∑ d ∈ n.divisors.filter (fun d ↦ d < N), (d : ℝ)) +
          if N ∣ n then (N : ℝ) / 2 else 0) := by
  calc
    (∑ a ∈ n.divisors, (1 / (a : ℝ)) *
        (∑' r : ℕ+, mobiusSquareTerm r *
          hStarRatio n (a * (r : ℕ) * N))) =
        ∑ a ∈ n.divisors,
          (1 / (a : ℝ)) * midpointTailWeight n (a * N) 1 := by
      apply Finset.sum_congr rfl
      intro a _ha
      congr 1
      simpa [mul_assoc, mul_left_comm, mul_comm] using!
        (tsum_mobiusSquare_mul_hStarRatio n (a * N))
    _ = (1 / (n : ℝ)) *
        ((∑ d ∈ n.divisors.filter (fun d ↦ d < N), (d : ℝ)) +
          if N ∣ n then (N : ℝ) / 2 else 0) :=
      midpoint_divisor_sum_eq n N hn

/-- Real form of the Ramanujan divisor formula with the divisors of the
frequency fixed once and for all. -/
theorem ramanujanSum_re_eq_sum_frequency_divisors (p n : ℕ)
    (hp : p ≠ 0) (hn : n ≠ 0) :
    (ramanujanSum p (n : ℤ)).re =
      ∑ a ∈ n.divisors,
        if a ∣ p then
          (a : ℝ) * (ArithmeticFunction.moebius (p / a) : ℝ)
        else 0 := by
  have hgcd : Nat.gcd p n ≠ 0 := Nat.gcd_ne_zero_left hp
  have hset : (Nat.gcd p n).divisors =
      n.divisors.filter (fun a ↦ a ∣ p) := by
    ext a
    simp only [Finset.mem_filter]
    simp [Nat.mem_divisors, hn, hgcd, Nat.dvd_gcd_iff, and_comm]
  rw [ramanujanSum_nat_divisor_moebius p n hp, hset, Complex.re_sum]
  simp only [Complex.mul_re, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _ha
  split_ifs <;> simp

/-- Multiplication by a fixed positive integer identifies positive integers
with its positive multiples. -/
def positiveMultiplesEquiv (a : ℕ+) :
    ℕ+ ≃ {p : ℕ+ // (a : ℕ) ∣ (p : ℕ)} where
  toFun r := ⟨⟨(a : ℕ) * (r : ℕ), Nat.mul_pos a.pos r.pos⟩,
    dvd_mul_right (a : ℕ) (r : ℕ)⟩
  invFun p :=
    ⟨(p : ℕ) / (a : ℕ),
      Nat.div_pos (Nat.le_of_dvd p.1.pos p.2) a.pos⟩
  left_inv r := by
    apply PNat.eq
    simp
  right_inv p := by
    apply Subtype.ext
    apply PNat.eq
    exact Nat.mul_div_cancel' p.2

theorem fixed_multiple_term_summable (n N : ℕ) (a : ℕ+) :
    Summable fun p : ℕ+ ↦
      if (a : ℕ) ∣ (p : ℕ) then
        ((a : ℝ) * (ArithmeticFunction.moebius ((p : ℕ) / (a : ℕ)) : ℝ) /
            (p : ℝ) ^ 2) * hStarRatio n ((p : ℕ) * N)
      else 0 := by
  have hdom : Summable fun p : ℕ+ ↦
      ((a : ℝ) * (Real.pi ^ 2 / 6)) * positiveInverseSquareTerm p :=
    summable_positiveInverseSquareTerm.mul_left _
  apply Summable.of_norm
  apply hdom.of_nonneg_of_le
  · exact fun _ ↦ norm_nonneg _
  · intro p
    by_cases hp : (a : ℕ) ∣ (p : ℕ)
    · rw [if_pos hp, Real.norm_eq_abs]
      have ha0 : 0 ≤ (a : ℝ) := by positivity
      have hp0 : 0 < (p : ℝ) := by positivity
      have hmu :
          |(ArithmeticFunction.moebius ((p : ℕ) / (a : ℕ)) : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one
          (n := (p : ℕ) / (a : ℕ)))
      have hh0 := hStarRatio_nonneg n ((p : ℕ) * N)
      have hh1 := hStarRatio_le_zetaTwo n ((p : ℕ) * N)
      rw [abs_mul, abs_div, abs_mul, abs_of_nonneg ha0, abs_pow,
        abs_of_pos hp0, abs_of_nonneg hh0]
      change (a : ℝ) *
          |(ArithmeticFunction.moebius ((p : ℕ) / (a : ℕ)) : ℝ)| /
            (p : ℝ) ^ 2 * hStarRatio n ((p : ℕ) * N) ≤
        ((a : ℝ) * (Real.pi ^ 2 / 6)) * (1 / (p : ℝ) ^ 2)
      calc
        (a : ℝ) *
            |(ArithmeticFunction.moebius ((p : ℕ) / (a : ℕ)) : ℝ)| /
              (p : ℝ) ^ 2 * hStarRatio n ((p : ℕ) * N) ≤
            (a : ℝ) * 1 / (p : ℝ) ^ 2 * (Real.pi ^ 2 / 6) := by
          gcongr
        _ = ((a : ℝ) * (Real.pi ^ 2 / 6)) * (1 / (p : ℝ) ^ 2) := by
          ring
    · rw [if_neg hp, norm_zero]
      exact mul_nonneg
        (mul_nonneg (by positivity)
          (div_nonneg (sq_nonneg Real.pi) (by norm_num)))
        (by unfold positiveInverseSquareTerm; positivity)

theorem tsum_fixed_multiple_term (n N : ℕ) (a : ℕ+) :
    (∑' p : ℕ+,
      if (a : ℕ) ∣ (p : ℕ) then
        ((a : ℝ) * (ArithmeticFunction.moebius ((p : ℕ) / (a : ℕ)) : ℝ) /
            (p : ℝ) ^ 2) * hStarRatio n ((p : ℕ) * N)
      else 0) =
      (1 / (a : ℝ)) *
        (∑' r : ℕ+, mobiusSquareTerm r *
          hStarRatio n ((a : ℕ) * (r : ℕ) * N)) := by
  let S : Set ℕ+ := {p | (a : ℕ) ∣ (p : ℕ)}
  let f : ℕ+ → ℝ := fun p ↦
    ((a : ℝ) * (ArithmeticFunction.moebius ((p : ℕ) / (a : ℕ)) : ℝ) /
        (p : ℝ) ^ 2) * hStarRatio n ((p : ℕ) * N)
  calc
    (∑' p : ℕ+,
        if (a : ℕ) ∣ (p : ℕ) then
          ((a : ℝ) * (ArithmeticFunction.moebius ((p : ℕ) / (a : ℕ)) : ℝ) /
              (p : ℝ) ^ 2) * hStarRatio n ((p : ℕ) * N)
        else 0) = ∑' p : ℕ+, S.indicator f p := by
      apply tsum_congr
      intro p
      by_cases hp : (a : ℕ) ∣ (p : ℕ)
      · simp [S, f, hp]
      · simp [S, f, hp]
    _ = ∑' p : S, f p := by
      symm
      exact tsum_subtype S f
    _ = ∑' r : ℕ+, f (positiveMultiplesEquiv a r) := by
      symm
      exact (positiveMultiplesEquiv a).tsum_eq (fun p : S ↦ f p)
    _ = ∑' r : ℕ+, (1 / (a : ℝ)) *
          (mobiusSquareTerm r *
            hStarRatio n ((a : ℕ) * (r : ℕ) * N)) := by
      apply tsum_congr
      intro r
      dsimp [f, positiveMultiplesEquiv, mobiusSquareTerm]
      have haR : (a : ℝ) ≠ 0 := by positivity
      have hrR : (r : ℝ) ≠ 0 := by positivity
      rw [Nat.mul_div_cancel_left (r : ℕ) a.pos]
      push_cast
      field_simp
    _ = (1 / (a : ℝ)) *
        (∑' r : ℕ+, mobiusSquareTerm r *
          hStarRatio n ((a : ℕ) * (r : ℕ) * N)) := by
      rw [tsum_mul_left]

/-- Exact coefficient collapse in the form stated in the manuscript.  The
sum is over positive moduli, represented by `ℕ+`; no conditional exchange
of sums is used. -/
theorem ramanujan_hStar_mobius_collapse (n N : ℕ) (hn : n ≠ 0) :
    (∑' p : ℕ+,
      ((ramanujanSum (p : ℕ) (n : ℤ)).re / (p : ℝ) ^ 2) *
        hStarRatio n ((p : ℕ) * N)) =
      (1 / (n : ℝ)) *
        ((∑ d ∈ n.divisors.filter (fun d ↦ d < N), (d : ℝ)) +
          if N ∣ n then (N : ℝ) / 2 else 0) := by
  calc
    (∑' p : ℕ+,
        ((ramanujanSum (p : ℕ) (n : ℤ)).re / (p : ℝ) ^ 2) *
          hStarRatio n ((p : ℕ) * N)) =
        ∑' p : ℕ+, ∑ a ∈ n.divisors,
          if a ∣ (p : ℕ) then
            ((a : ℝ) *
                (ArithmeticFunction.moebius ((p : ℕ) / a) : ℝ) /
              (p : ℝ) ^ 2) * hStarRatio n ((p : ℕ) * N)
          else 0 := by
      apply tsum_congr
      intro p
      rw [ramanujanSum_re_eq_sum_frequency_divisors (p : ℕ) n p.ne_zero hn]
      rw [Finset.sum_div, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _ha
      split_ifs <;> ring
    _ = ∑ a ∈ n.divisors, ∑' p : ℕ+,
          if a ∣ (p : ℕ) then
            ((a : ℝ) *
                (ArithmeticFunction.moebius ((p : ℕ) / a) : ℝ) /
              (p : ℝ) ^ 2) * hStarRatio n ((p : ℕ) * N)
          else 0 := by
      rw [Summable.tsum_finsetSum]
      intro a ha
      exact fixed_multiple_term_summable n N
        ⟨a, Nat.pos_of_mem_divisors ha⟩
    _ = ∑ a ∈ n.divisors, (1 / (a : ℝ)) *
          (∑' r : ℕ+, mobiusSquareTerm r *
            hStarRatio n (a * (r : ℕ) * N)) := by
      apply Finset.sum_congr rfl
      intro a ha
      simpa using! tsum_fixed_multiple_term n N
        ⟨a, Nat.pos_of_mem_divisors ha⟩
    _ = (1 / (n : ℝ)) *
        ((∑ d ∈ n.divisors.filter (fun d ↦ d < N), (d : ℝ)) +
          if N ∣ n then (N : ℝ) / 2 else 0) :=
      divisor_mobius_hStar_collapse n N hn

end

end Erdos1002
