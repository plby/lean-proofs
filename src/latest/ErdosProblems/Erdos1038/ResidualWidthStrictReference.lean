import ErdosProblems.Erdos1038.ResidualWidthInverseBranch
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Strict-reference bounds for the inverse-width derivative series

The finite convexity argument needs absolute convergence of both the
reference inverse series and its material derivative.  This file packages
the elementary analytic estimate behind that implication.  Strict room in
the positive inverse branch gives summability with one degree of polynomial
weight; the explicit monomial derivative formula then controls every
directional coefficient by that weighted reference coefficient.
-/

set_option warningAsError false

open scoped BigOperators Real
open Finset Set

namespace Erdos1038

noncomputable section

lemma scaledLagrangeCoefficient_nonneg
    {iota : Type*} [Fintype iota]
    (a d : iota → ℝ) (ha : ∀ i, 0 < a i)
    (hd : d ∈ positiveCoordinates iota) (n : ℕ) :
    0 ≤ scaledLagrangeCoefficient a n d := by
  rw [scaledLagrangeCoefficient_eq_inverseCoeff_mul_pow a d hd n]
  exact mul_nonneg
    (coeff_lagrangeInversePowerSeries_nonneg a d ha hd n)
    (pow_nonneg (inverseMonomial_pos a d).le n)

private lemma lagrangePhiValue_eq_exp_neg_logSum
    {iota : Type*} [Fintype iota]
    (a d : iota → ℝ) {s : ℝ} (hsd : ∀ i, s < d i)
    (hd : d ∈ positiveCoordinates iota) :
    lagrangePhiValue a d s =
      Real.exp (-∑ i, a i * Real.log (1 - s / d i)) := by
  classical
  have hbase (i : iota) : 0 < 1 - s / d i := by
    rw [sub_pos, div_lt_one (hd i)]
    exact hsd i
  unfold lagrangePhiValue
  calc
    (∏ i, 1 / (1 - s / d i) ^ (a i)) =
        ∏ i, Real.exp (-(Real.log (1 - s / d i) * a i)) := by
      apply Finset.prod_congr rfl
      intro i _hi
      rw [Real.rpow_def_of_pos (hbase i), one_div, ← Real.exp_neg]
    _ = Real.exp (∑ i, -(Real.log (1 - s / d i) * a i)) := by
      rw [Real.exp_sum]
    _ = Real.exp (-∑ i, a i * Real.log (1 - s / d i)) := by
      congr 1
      rw [Finset.sum_neg_distrib]
      apply congrArg Neg.neg
      apply Finset.sum_congr rfl
      intro i _hi
      ring

lemma inverseMonomial_mul_lagrangePhiValue_eq_exp_logGap
    {iota : Type*} [Fintype iota]
    (a d : iota → ℝ) {s : ℝ} (hsd : ∀ i, s < d i)
    (hd : d ∈ positiveCoordinates iota) :
    inverseMonomial a d * lagrangePhiValue a d s =
      Real.exp (-∑ i, a i * Real.log (d i - s)) := by
  classical
  have hbase (i : iota) : 0 < 1 - s / d i := by
    rw [sub_pos, div_lt_one (hd i)]
    exact hsd i
  have hlog (i : iota) :
      Real.log (d i) + Real.log (1 - s / d i) =
        Real.log (d i - s) := by
    rw [← Real.log_mul (hd i).ne' (hbase i).ne']
    congr 1
    field_simp [(hd i).ne']
  rw [inverseMonomial,
    lagrangePhiValue_eq_exp_neg_logSum a d hsd hd, ← Real.exp_add]
  congr 1
  rw [← neg_add, ← Finset.sum_add_distrib]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← hlog i]
  ring

/-- A positive discrete logarithmic potential is exactly the strict room
condition needed by the inverse-series comparison theorem.  This is the
form suited to canonical quantile Riemann sums. -/
theorem inverseMonomial_lt_div_lagrangePhiValue_of_logPotential_pos
    {iota : Type*} [Fintype iota]
    (a d : iota → ℝ) (hd : d ∈ positiveCoordinates iota)
    {s : ℝ} (hs : 0 < s) (hsd : ∀ i, s < d i)
    (hpotential :
      0 < Real.log s + ∑ i, a i * Real.log (d i - s)) :
    inverseMonomial a d < s / lagrangePhiValue a d s := by
  have hphi : 0 < lagrangePhiValue a d s :=
    lagrangePhiValue_pos a d hd hsd
  rw [lt_div_iff₀ hphi]
  rw [inverseMonomial_mul_lagrangePhiValue_eq_exp_logGap a d hsd hd]
  calc
    Real.exp (-∑ i, a i * Real.log (d i - s)) <
        Real.exp (Real.log s) := Real.exp_lt_exp.mpr (by linarith)
    _ = s := Real.exp_log hs

/-- A quantitative lower bound on the discrete logarithmic potential gives
the corresponding uniform multiplicative room below the inverse-branch
boundary.  This strengthened form is what turns a positive continuum
margin into one geometric majorant valid for every sufficiently fine mesh. -/
theorem inverseMonomial_le_exp_neg_mul_div_lagrangePhiValue_of_logPotential
    {iota : Type*} [Fintype iota]
    (a d : iota → ℝ) (hd : d ∈ positiveCoordinates iota)
    {s p : ℝ} (hs : 0 < s) (hsd : ∀ i, s < d i)
    (hpotential :
      p ≤ Real.log s + ∑ i, a i * Real.log (d i - s)) :
    inverseMonomial a d ≤
      Real.exp (-p) * (s / lagrangePhiValue a d s) := by
  have hphi : 0 < lagrangePhiValue a d s :=
    lagrangePhiValue_pos a d hd hsd
  rw [show Real.exp (-p) * (s / lagrangePhiValue a d s) =
      (Real.exp (-p) * s) / lagrangePhiValue a d s by ring,
    le_div_iff₀ hphi,
    inverseMonomial_mul_lagrangePhiValue_eq_exp_logGap a d hsd hd]
  calc
    Real.exp (-∑ i, a i * Real.log (d i - s)) ≤
        Real.exp (-p + Real.log s) := by
      exact Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-p) * s := by
      rw [Real.exp_add, Real.exp_log hs]

private lemma summable_natCast_add_one_mul_geometric
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun n : ℕ ↦ ((n : ℝ) + 1) * q ^ n) := by
  have hnorm : ‖q‖ < (1 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hq0] using! hq1
  have hn := summable_pow_mul_geometric_of_norm_lt_one
    (R := ℝ) 1 (r := q) hnorm
  have hq := summable_geometric_of_norm_lt_one hnorm
  simpa only [pow_one, add_mul, one_mul] using! hn.add hq

/-- Strict room between the evaluation scale and a positive comparison
point gives absolute convergence with one polynomial degree of weight.
This is the quantitative convergence needed for the material derivative,
not merely convergence of the reference value. -/
theorem summable_degreeWeight_scaledLagrangeCoefficient_of_lt_comparison
    {iota : Type*} [Fintype iota]
    (a d : iota → ℝ) (ha : ∀ i, 0 < a i)
    (hd : d ∈ positiveCoordinates iota)
    {s : ℝ} (hs : 0 < s) (hsd : ∀ i, s < d i)
    (hstrict : inverseMonomial a d < s / lagrangePhiValue a d s) :
    Summable (fun n : ℕ ↦
      ((n : ℝ) + 1) * scaledLagrangeCoefficient a n d) := by
  let z : ℝ := inverseMonomial a d
  let boundary : ℝ := s / lagrangePhiValue a d s
  let zLarge : ℝ := (z + boundary) / 2
  let q : ℝ := z / zLarge
  have hz : 0 < z := inverseMonomial_pos a d
  have hstrict' : z < boundary := by
    simpa only [z, boundary] using! hstrict
  have hboundaryPos : 0 < boundary := by
    exact hz.trans hstrict'
  have hzLargePos : 0 < zLarge := by
    dsimp only [zLarge]
    exact div_pos (add_pos hz hboundaryPos) (by norm_num)
  have hzLt : z < zLarge := by
    dsimp only [zLarge]
    linarith
  have hzLargeLt : zLarge < boundary := by
    dsimp only [zLarge]
    linarith
  have hq0 : 0 ≤ q := div_nonneg hz.le hzLargePos.le
  have hq1 : q < 1 := (div_lt_one hzLargePos).2 hzLt
  have hlarge : Summable (fun n : ℕ ↦
      PowerSeries.coeff n
          (PowerSeries.lagrangeInversePowerSeries a d) * zLarge ^ n) := by
    apply summable_lagrangeInversePowerSeries_of_lt
      a d ha hd hs hsd hzLargePos.le
    simpa only [boundary] using! hzLargeLt
  let total : ℝ := ∑' n : ℕ,
    PowerSeries.coeff n
        (PowerSeries.lagrangeInversePowerSeries a d) * zLarge ^ n
  have hlargeNonneg (n : ℕ) :
      0 ≤ PowerSeries.coeff n
          (PowerSeries.lagrangeInversePowerSeries a d) * zLarge ^ n :=
    mul_nonneg
      (coeff_lagrangeInversePowerSeries_nonneg a d ha hd n)
      (pow_nonneg hzLargePos.le n)
  have htermLe (n : ℕ) :
      PowerSeries.coeff n
          (PowerSeries.lagrangeInversePowerSeries a d) * zLarge ^ n ≤
        total := by
    exact hlarge.le_tsum n (fun m _hm ↦ hlargeNonneg m)
  have hmajor : Summable (fun n : ℕ ↦
      total * (((n : ℝ) + 1) * q ^ n)) :=
    (summable_natCast_add_one_mul_geometric hq0 hq1).mul_left total
  apply Summable.of_norm_bounded hmajor
  intro n
  have hscaled :
      scaledLagrangeCoefficient a n d =
        (PowerSeries.coeff n
            (PowerSeries.lagrangeInversePowerSeries a d) * zLarge ^ n) *
          q ^ n := by
    rw [scaledLagrangeCoefficient_eq_inverseCoeff_mul_pow a d hd n]
    have hzFactor : zLarge * q = z := by
      dsimp only [q]
      field_simp [hzLargePos.ne']
    change PowerSeries.coeff n
          (PowerSeries.lagrangeInversePowerSeries a d) * z ^ n =
        (PowerSeries.coeff n
            (PowerSeries.lagrangeInversePowerSeries a d) * zLarge ^ n) *
          q ^ n
    rw [← hzFactor, mul_pow]
    ring
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (by positivity)
      (scaledLagrangeCoefficient_nonneg a d ha hd n))]
  rw [hscaled]
  have hfactorNonneg : 0 ≤ ((n : ℝ) + 1) * q ^ n :=
    mul_nonneg (by positivity) (pow_nonneg hq0 n)
  calc
    ((n : ℝ) + 1) *
          ((PowerSeries.coeff n
              (PowerSeries.lagrangeInversePowerSeries a d) * zLarge ^ n) *
            q ^ n) =
        (PowerSeries.coeff n
            (PowerSeries.lagrangeInversePowerSeries a d) * zLarge ^ n) *
          (((n : ℝ) + 1) * q ^ n) := by ring
    _ ≤ total * (((n : ℝ) + 1) * q ^ n) :=
      mul_le_mul_of_nonneg_right (htermLe n) hfactorNonneg

/-- The preceding weighted convergence includes ordinary coefficient
summability. -/
theorem summable_scaledLagrangeCoefficient_of_degreeWeight
    {iota : Type*} [Fintype iota]
    (a d : iota → ℝ) (ha : ∀ i, 0 < a i)
    (hd : d ∈ positiveCoordinates iota)
    (hsum : Summable (fun n : ℕ ↦
      ((n : ℝ) + 1) * scaledLagrangeCoefficient a n d)) :
    Summable (fun n : ℕ ↦ scaledLagrangeCoefficient a n d) := by
  apply Summable.of_norm_bounded hsum
  intro n
  rw [Real.norm_eq_abs,
    abs_of_nonneg (scaledLagrangeCoefficient_nonneg a d ha hd n)]
  have hone : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  simpa only [one_mul] using! mul_le_mul_of_nonneg_right hone
    (scaledLagrangeCoefficient_nonneg a d ha hd n)

private lemma sum_lagrangeExponent
    {iota : Type*} [Fintype iota]
    (a : iota → ℝ) {n : ℕ} {r : iota → Fin n}
    (hr : r ∈ lagrangeMultiIndices iota n) :
    ∑ i, lagrangeExponent a n r i =
      (n : ℝ) * (∑ i, a i) + (n - 1 : ℕ) := by
  classical
  have hrNat : ∑ i, (r i : ℕ) = n - 1 := by
    change r ∈ Finset.univ.filter
      (fun r : iota → Fin n ↦ ∑ i, (r i : ℕ) = n - 1) at hr
    exact (Finset.mem_filter.mp hr).2
  have hrReal : ∑ i, ((r i : ℕ) : ℝ) = (n - 1 : ℕ) := by
    exact_mod_cast hrNat
  unfold lagrangeExponent
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hrReal]

private lemma abs_inverseMonomialDirectional_le
    {iota : Type*} [Fintype iota]
    (gamma reference target : iota → ℝ)
    (hgamma : ∀ i, 0 ≤ gamma i)
    {B : ℝ}
    (hratio : ∀ i, |(target i - reference i) / reference i| ≤ B) :
    |inverseMonomialDirectional gamma reference target| ≤
      inverseMonomial gamma reference * (B * ∑ i, gamma i) := by
  have hsum :
      |∑ i, gamma i * (target i - reference i) / reference i| ≤
        B * ∑ i, gamma i := by
    calc
      |∑ i, gamma i * (target i - reference i) / reference i| ≤
          ∑ i, |gamma i * (target i - reference i) / reference i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, gamma i * B := by
        apply Finset.sum_le_sum
        intro i _hi
        rw [show gamma i * (target i - reference i) / reference i =
            gamma i * ((target i - reference i) / reference i) by ring,
          abs_mul, abs_of_nonneg (hgamma i)]
        exact mul_le_mul_of_nonneg_left (hratio i) (hgamma i)
      _ = B * ∑ i, gamma i := by
        rw [← Finset.sum_mul]
        ring
  unfold inverseMonomialDirectional
  rw [abs_mul, abs_neg, abs_of_pos (inverseMonomial_pos gamma reference)]
  exact mul_le_mul_of_nonneg_left hsum (inverseMonomial_pos gamma reference).le

/-- Every material coefficient is bounded by its reference coefficient
times the total monomial degree and the maximum relative displacement. -/
theorem abs_scaledLagrangeCoefficientDirectional_le
    {iota : Type*} [Fintype iota]
    (a reference target : iota → ℝ)
    (ha : ∀ i, 0 < a i) {n : ℕ} (hn : 0 < n)
    {B : ℝ}
    (hratio : ∀ i, |(target i - reference i) / reference i| ≤ B) :
    |scaledLagrangeCoefficientDirectional a n reference target| ≤
      B * ((n : ℝ) * (∑ i, a i) + (n - 1 : ℕ)) *
        scaledLagrangeCoefficient a n reference := by
  classical
  unfold scaledLagrangeCoefficientDirectional
  calc
    |∑ r ∈ lagrangeMultiIndices iota n,
        scaledLagrangeTermDirectional a n r reference target| ≤
      ∑ r ∈ lagrangeMultiIndices iota n,
        |scaledLagrangeTermDirectional a n r reference target| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ lagrangeMultiIndices iota n,
        (B * ((n : ℝ) * (∑ i, a i) + (n - 1 : ℕ))) *
          scaledLagrangeTerm a n r reference := by
      apply Finset.sum_le_sum
      intro r hr
      have hgamma := lagrangeExponent_nonneg a
        (fun i ↦ (ha i).le) n r
      have hpref := scaledLagrangePrefactor_pos a ha hn r
      unfold scaledLagrangeTermDirectional scaledLagrangeTerm
      rw [abs_mul, abs_of_pos hpref]
      have hmono := abs_inverseMonomialDirectional_le
        (lagrangeExponent a n r) reference target hgamma hratio
      rw [sum_lagrangeExponent a hr] at hmono
      calc
        scaledLagrangePrefactor a n r *
            |inverseMonomialDirectional
              (lagrangeExponent a n r) reference target| ≤
          scaledLagrangePrefactor a n r *
            (inverseMonomial (lagrangeExponent a n r) reference *
              (B * ((n : ℝ) * (∑ i, a i) + (n - 1 : ℕ)))) :=
          mul_le_mul_of_nonneg_left hmono hpref.le
        _ = (B * ((n : ℝ) * (∑ i, a i) + (n - 1 : ℕ))) *
            (scaledLagrangePrefactor a n r *
              inverseMonomial (lagrangeExponent a n r) reference) := by ring
    _ = B * ((n : ℝ) * (∑ i, a i) + (n - 1 : ℕ)) *
        scaledLagrangeCoefficient a n reference := by
      unfold scaledLagrangeCoefficient
      symm
      exact Finset.mul_sum _ _ _

/-- Weighted reference convergence implies absolute convergence of the odd
material derivative series whenever the relative displacement is bounded. -/
theorem summable_scaledLagrangeCoefficientDirectional_of_degreeWeight
    {iota : Type*} [Fintype iota]
    (a reference target : iota → ℝ)
    (ha : ∀ i, 0 < a i)
    (href : reference ∈ positiveCoordinates iota)
    {B : ℝ} (hB : 0 ≤ B)
    (hratio : ∀ i, |(target i - reference i) / reference i| ≤ B)
    (hsum : Summable (fun n : ℕ ↦
      ((n : ℝ) + 1) * scaledLagrangeCoefficient a n reference)) :
    Summable (fun j : ℕ ↦
      scaledLagrangeCoefficientDirectional a (2 * j + 1)
        reference target) := by
  have hsumAlpha : 0 ≤ ∑ i, a i :=
    Finset.sum_nonneg fun i _hi ↦ (ha i).le
  let K : ℝ := B * ((∑ i, a i) + 1)
  have hmajorFull : Summable (fun n : ℕ ↦
      K * (((n : ℝ) + 1) *
        scaledLagrangeCoefficient a n reference)) := hsum.mul_left K
  have hinj : Function.Injective (fun j : ℕ ↦ 2 * j + 1) := by
    intro m n hmn
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
    exact Nat.add_right_cancel hmn
  have hmajor := hmajorFull.comp_injective hinj
  apply Summable.of_norm_bounded hmajor
  intro j
  let n : ℕ := 2 * j + 1
  have hn : 0 < n := by dsimp only [n]; omega
  have hdirection := abs_scaledLagrangeCoefficientDirectional_le
    a reference target ha hn hratio
  rw [Real.norm_eq_abs]
  calc
    |scaledLagrangeCoefficientDirectional a n reference target| ≤
        B * ((n : ℝ) * (∑ i, a i) + (n - 1 : ℕ)) *
          scaledLagrangeCoefficient a n reference := hdirection
    _ ≤ K * (((n : ℝ) + 1) *
          scaledLagrangeCoefficient a n reference) := by
      have hcoeff := scaledLagrangeCoefficient_nonneg a reference ha href n
      dsimp only [K]
      have hnCast : (n - 1 : ℕ) ≤ (n : ℝ) := by
        exact_mod_cast Nat.sub_le n 1
      have hdegree :
          (n : ℝ) * (∑ i, a i) + (n - 1 : ℕ) ≤
            (n : ℝ) * ((∑ i, a i) + 1) := by
        linarith
      have hAlphaOne : 0 ≤ (∑ i, a i) + 1 := by
        linarith
      have hnStep :
          (n : ℝ) * ((∑ i, a i) + 1) ≤
            ((∑ i, a i) + 1) * ((n : ℝ) + 1) := by
        calc
          (n : ℝ) * ((∑ i, a i) + 1) ≤
              ((n : ℝ) + 1) * ((∑ i, a i) + 1) :=
            mul_le_mul_of_nonneg_right (by linarith) hAlphaOne
          _ = ((∑ i, a i) + 1) * ((n : ℝ) + 1) := by ring
      have hconstant :
          B * ((n : ℝ) * (∑ i, a i) + (n - 1 : ℕ)) ≤
            B * ((∑ i, a i) + 1) * ((n : ℝ) + 1) := by
        calc
          B * ((n : ℝ) * (∑ i, a i) + (n - 1 : ℕ)) ≤
              B * ((n : ℝ) * ((∑ i, a i) + 1)) :=
            mul_le_mul_of_nonneg_left hdegree hB
          _ ≤ B * (((∑ i, a i) + 1) * ((n : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hnStep hB
          _ = B * ((∑ i, a i) + 1) * ((n : ℝ) + 1) := by ring
      calc
        B * ((n : ℝ) * (∑ i, a i) + (n - 1 : ℕ)) *
            scaledLagrangeCoefficient a n reference ≤
          (B * ((∑ i, a i) + 1) * ((n : ℝ) + 1)) *
            scaledLagrangeCoefficient a n reference :=
          mul_le_mul_of_nonneg_right hconstant hcoeff
        _ = B * ((∑ i, a i) + 1) *
            (((n : ℝ) + 1) *
              scaledLagrangeCoefficient a n reference) := by ring
    _ = K * ((((2 * j + 1 : ℕ) : ℝ) + 1) *
          scaledLagrangeCoefficient a (2 * j + 1) reference) := by rfl

end

end Erdos1038
