import ErdosProblems.Erdos520.HarperScheduledRelativeInterval
import ErdosProblems.Erdos520.HarperFiniteSlicing

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

namespace Erdos
namespace Problem520

/-!
# Summable relative errors for scheduled product cells

The absolute strong-frequency replacement error is not merely smaller than
the Gaussian mass of a moderate lattice cell.  It is smaller by another
factor equal to the cell width `(j+1)⁻²`.  These relative losses are
summable, so their product is bounded by `exp 2`, independently of the path
length.  This is the constant-strength form needed by finite slicing.
-/

private theorem eventually_const_mul_pow_le_exp_quarter_nat_product
    (A : ℝ) (d : ℕ) :
    ∀ᶠ j : ℕ in atTop,
      A * (j : ℝ) ^ d ≤ Real.exp ((j : ℝ) / 4) := by
  have ht : Tendsto
      (fun x : ℝ ↦ Real.exp ((1 / 4 : ℝ) * x) / x ^ (d : ℝ))
      atTop atTop :=
    tendsto_exp_mul_div_rpow_atTop (d : ℝ) (1 / 4 : ℝ) (by norm_num)
  have htNat := ht.comp tendsto_natCast_atTop_atTop
  filter_upwards [htNat.eventually (eventually_ge_atTop A),
      eventually_ge_atTop (1 : ℕ)] with j hj hjOne
  have hjPos : (0 : ℝ) < j := by positivity
  have hden : 0 < (j : ℝ) ^ d := by positivity
  change A ≤ Real.exp ((1 / 4 : ℝ) * (j : ℝ)) /
    (j : ℝ) ^ (d : ℝ) at hj
  rw [Real.rpow_natCast] at hj
  rw [le_div_iff₀ hden] at hj
  calc
    A * (j : ℝ) ^ d ≤ Real.exp ((1 / 4 : ℝ) * (j : ℝ)) := hj
    _ = Real.exp ((j : ℝ) / 4) := by
      congr 1
      ring

/-- The replacement budget is eventually at most one cell-width times the
elementary Gaussian lower bound. -/
theorem eventually_harperScheduledStrongBudget_le_width_mul_relativeGaussianMass :
    ∀ᶠ j : ℕ in atTop, ∀ a : ℝ,
      |a| + 1 ≤ (1 / 4 : ℝ) * Real.sqrt (((2 ^ j : ℕ) : ℝ)) →
        260 / harperScheduledStrongComparisonFrequency j ≤
          harperScheduledRelativeIntervalWidth j *
            ((harperScheduledRelativeIntervalWidth j / 2) *
              Real.exp (-2 * (|a| + 1) ^ 2)) := by
  have hpoly :=
    eventually_const_mul_pow_le_exp_quarter_nat_product (8320 : ℝ) 4
  filter_upwards [hpoly, eventually_ge_atTop (1 : ℕ)] with j hpolyJ hjOne
  intro a ha
  let n : ℝ := ((2 ^ j : ℕ) : ℝ)
  let D : ℝ := (((j + 1 : ℕ) : ℝ) ^ 2)
  let q : ℝ := 2 * (|a| + 1) ^ 2
  let T : ℝ := harperScheduledStrongComparisonFrequency j
  have hn0 : 0 ≤ n := by dsimp [n]; positivity
  have hnPos : 0 < n := by dsimp [n]; positivity
  have hDPos : 0 < D := by dsimp [D]; positivity
  have hTPos : 0 < T := by
    dsimp [T]
    exact harperScheduledStrongComparisonFrequency_pos j
  have hjCast : ((j : ℝ) + 1) ≤ 2 * (j : ℝ) := by
    exact_mod_cast (show j + 1 ≤ 2 * j by omega)
  have hpoly' : 520 * D ^ 2 ≤ Real.exp ((j : ℝ) / 4) := by
    calc
      520 * D ^ 2 = 520 * (((j : ℝ) + 1) ^ 4) := by
        dsimp [D]
        push_cast
        ring
      _ ≤ 520 * (2 * (j : ℝ)) ^ 4 := by gcongr
      _ = 8320 * (j : ℝ) ^ 4 := by ring
      _ ≤ Real.exp ((j : ℝ) / 4) := hpolyJ
  have hjnNat : j ≤ 2 ^ j := (Nat.lt_two_pow_self (n := j)).le
  have hjn : (j : ℝ) ≤ n := by
    dsimp [n]
    exact_mod_cast hjnNat
  have hpolyN : 520 * D ^ 2 ≤ Real.exp (n / 4) :=
    hpoly'.trans (Real.exp_le_exp.mpr (by linarith))
  have hsqrtSq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0
  have haNonneg : 0 ≤ |a| + 1 := by positivity
  have hrightNonneg : 0 ≤ (1 / 4 : ℝ) * Real.sqrt n := by positivity
  have haSq : (|a| + 1) ^ 2 ≤
      ((1 / 4 : ℝ) * Real.sqrt n) ^ 2 :=
    (sq_le_sq₀ haNonneg hrightNonneg).2 (by simpa only [n] using! ha)
  have hq : q ≤ n / 8 := by
    dsimp [q]
    nlinarith
  have hexpQ : Real.exp q ≤ Real.exp (n / 8) :=
    Real.exp_le_exp.mpr hq
  have hlog : (3 / 8 : ℝ) ≤ Real.log 2 := by
    exact le_of_lt ((by norm_num : (3 / 8 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9)
  have hTexp : Real.exp (Real.log 2 * n) = T := by
    dsimp [n, T, harperScheduledStrongComparisonFrequency]
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hcross : 520 * D ^ 2 * Real.exp q ≤ T := by
    calc
      520 * D ^ 2 * Real.exp q ≤
          Real.exp (n / 4) * Real.exp q := by gcongr
      _ ≤ Real.exp (n / 4) * Real.exp (n / 8) := by gcongr
      _ = Real.exp ((3 / 8 : ℝ) * n) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (Real.log 2 * n) := by
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hlog hn0)
      _ = T := hTexp
  have hdenPos : 0 < 2 * D ^ 2 * Real.exp q := by positivity
  have hdiv : 260 / T ≤ 1 / (2 * D ^ 2 * Real.exp q) := by
    apply (div_le_div_iff₀ hTPos hdenPos).2
    convert! hcross using 1 <;> ring
  calc
    260 / harperScheduledStrongComparisonFrequency j = 260 / T := rfl
    _ ≤ 1 / (2 * D ^ 2 * Real.exp q) := hdiv
    _ = harperScheduledRelativeIntervalWidth j *
        ((harperScheduledRelativeIntervalWidth j / 2) *
          Real.exp (-2 * (|a| + 1) ^ 2)) := by
      dsimp only [harperScheduledRelativeIntervalWidth, D, q]
      rw [show -2 * (|a| + 1) ^ 2 = -(2 * (|a| + 1) ^ 2) by ring,
        Real.exp_neg]
      field_simp [Real.exp_ne_zero]

/-- One moderate scheduled cell incurs only the summable multiplicative
loss `1 + (j+1)⁻²`. -/
theorem exists_eventually_harperScheduledRelativeIntervalProbability_le_one_add_width_mul_gaussian
    (M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
          ∀ a : ℝ,
            |a| + 1 ≤ (1 / 4 : ℝ) *
              Real.sqrt (((2 ^ j : ℕ) : ℝ)) →
            (harperCenteredLinearBlockLaw y
              (harperScheduledPrimeBlock y j) t t).real
                (Ioc a (a + harperScheduledRelativeIntervalWidth j)) ≤
              (1 + harperScheduledRelativeIntervalWidth j) *
                (harperGaussianBlockLaw y
                  (harperScheduledPrimeBlock y j) t t).real
                    (Ioc a (a + harperScheduledRelativeIntervalWidth j)) := by
  obtain ⟨Jcdf, hJcdf⟩ :=
    exists_eventually_harperScheduledDiagonalCDFDistance_le_strong_unconditional M
  obtain ⟨Jvar, hJvar⟩ :=
    exists_eventually_harperScheduledDiagonalVariance_third_threeEighths M
  obtain ⟨Jbudget, hJbudget⟩ := eventually_atTop.1
    eventually_harperScheduledStrongBudget_le_width_mul_relativeGaussianMass
  refine ⟨max (max Jcdf Jvar) Jbudget, ?_⟩
  intro j hj y hy t htLower htUpper a ha
  have hjcdf : Jcdf ≤ j :=
    (le_max_left Jcdf Jvar).trans (le_max_left _ Jbudget) |>.trans hj
  have hjvar : Jvar ≤ j :=
    (le_max_right Jcdf Jvar).trans (le_max_left _ Jbudget) |>.trans hj
  have hjbudget : Jbudget ≤ j := (le_max_right _ Jbudget).trans hj
  let rho := harperCenteredLinearBlockLaw y
    (harperScheduledPrimeBlock y j) t t
  let nu := harperGaussianBlockLaw y
    (harperScheduledPrimeBlock y j) t t
  let delta := harperScheduledRelativeIntervalWidth j
  have hdist : harperCDFDistance rho nu ≤
      130 / harperScheduledStrongComparisonFrequency j :=
    hJcdf j hjcdf y hy t htLower htUpper
  have habs : |rho.real (Ioc a (a + delta)) -
      nu.real (Ioc a (a + delta))| ≤ 2 * harperCDFDistance rho nu :=
    abs_measureReal_Ioc_sub_le_two_mul_cdfDistance rho nu
      (by dsimp [delta]; linarith [harperScheduledRelativeIntervalWidth_pos j])
  have hvar := hJvar j hjvar y hy t htLower htUpper
  have hgaussian :
      (delta / 2) * Real.exp (-2 * (|a| + 1) ^ 2) ≤
        nu.real (Ioc a (a + delta)) := by
    dsimp only [nu, harperGaussianBlockLaw]
    exact gaussianReal_real_Ioc_ge_of_variance_mem
      (v := harperLinearBlockVarianceNNReal y
        (harperScheduledPrimeBlock y j) t t)
      (by simpa only [coe_harperLinearBlockVarianceNNReal] using! hvar.1.le)
      (by simpa only [coe_harperLinearBlockVarianceNNReal] using! hvar.2.le)
      (by simpa only [delta] using! harperScheduledRelativeIntervalWidth_pos j)
      (by simpa only [delta] using! harperScheduledRelativeIntervalWidth_le_one j)
  have hbudget := hJbudget j hjbudget a ha
  have herr : rho.real (Ioc a (a + delta)) -
      nu.real (Ioc a (a + delta)) ≤
        delta * nu.real (Ioc a (a + delta)) := by
    calc
      rho.real (Ioc a (a + delta)) - nu.real (Ioc a (a + delta)) ≤
          |rho.real (Ioc a (a + delta)) -
            nu.real (Ioc a (a + delta))| := le_abs_self _
      _ ≤ 2 * harperCDFDistance rho nu := habs
      _ ≤ 2 * (130 / harperScheduledStrongComparisonFrequency j) := by gcongr
      _ = 260 / harperScheduledStrongComparisonFrequency j := by ring
      _ ≤ delta * ((delta / 2) *
          Real.exp (-2 * (|a| + 1) ^ 2)) := by simpa only [delta] using! hbudget
      _ ≤ delta * nu.real (Ioc a (a + delta)) := by
        gcongr
        exact (harperScheduledRelativeIntervalWidth_pos j).le
  dsimp only [rho, nu, delta] at herr ⊢
  linarith

theorem sum_range_harperScheduledRelativeIntervalWidth_le_two (n : ℕ) :
    (∑ j ∈ Finset.range n, harperScheduledRelativeIntervalWidth j) ≤ 2 := by
  have hstrong : ∀ m : ℕ, m ≠ 0 →
      (∑ j ∈ Finset.range m,
        harperScheduledRelativeIntervalWidth j) ≤ 2 - 1 / (m : ℝ) := by
    intro m hm
    induction m with
    | zero => exact (hm rfl).elim
    | succ m ih =>
        by_cases hm0 : m = 0
        · subst m
          norm_num [harperScheduledRelativeIntervalWidth]
        · have ihm := ih hm0
          rw [Finset.sum_range_succ]
          have hmpos : (0 : ℝ) < m := by positivity
          have hsuccpos : (0 : ℝ) < m + 1 := by positivity
          have hcell : harperScheduledRelativeIntervalWidth m ≤
              1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ) := by
            unfold harperScheduledRelativeIntervalWidth
            push_cast
            calc
              (((m : ℝ) + 1) ^ 2)⁻¹ ≤
                  ((m : ℝ) * ((m : ℝ) + 1))⁻¹ := by
                simpa only [one_div] using!
                  one_div_le_one_div_of_le (mul_pos hmpos hsuccpos)
                    (by nlinarith)
              _ = 1 / (m : ℝ) - 1 / ((m : ℝ) + 1) := by
                field_simp
                ring
          calc
            (∑ j ∈ Finset.range m,
                harperScheduledRelativeIntervalWidth j) +
                  harperScheduledRelativeIntervalWidth m ≤
                (2 - 1 / (m : ℝ)) +
                  (1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ)) :=
              add_le_add ihm hcell
            _ = 2 - 1 / (((m + 1 : ℕ) : ℝ)) := by ring
  by_cases hn : n = 0
  · subst n
    simp
  exact (hstrong n hn).trans (sub_le_self _ (by positivity))

theorem sum_fin_harperScheduledRelativeIntervalWidth_le_two
    (start n : ℕ) :
    (∑ i : Fin n, harperScheduledRelativeIntervalWidth (start + (i : ℕ))) ≤ 2 := by
  have hsplit := Finset.sum_range_add harperScheduledRelativeIntervalWidth start n
  have hfirst : 0 ≤ ∑ j ∈ Finset.range start,
      harperScheduledRelativeIntervalWidth j :=
    Finset.sum_nonneg fun j _ ↦ (harperScheduledRelativeIntervalWidth_pos j).le
  calc
    (∑ i : Fin n,
        harperScheduledRelativeIntervalWidth (start + (i : ℕ))) =
        ∑ i ∈ Finset.range n,
          harperScheduledRelativeIntervalWidth (start + i) :=
      Fin.sum_univ_eq_sum_range
        (fun i ↦ harperScheduledRelativeIntervalWidth (start + i)) n
    _ ≤ (∑ j ∈ Finset.range start,
          harperScheduledRelativeIntervalWidth j) +
          ∑ i ∈ Finset.range n,
            harperScheduledRelativeIntervalWidth (start + i) :=
      le_add_of_nonneg_left hfirst
    _ = ∑ j ∈ Finset.range (start + n),
        harperScheduledRelativeIntervalWidth j := hsplit.symm
    _ ≤ 2 := sum_range_harperScheduledRelativeIntervalWidth_le_two _

/-- The product of all one-block relative losses is uniformly bounded,
independently of the starting block and the number of coordinates. -/
theorem prod_one_add_harperScheduledRelativeIntervalWidth_le_exp_two
    (start n : ℕ) :
    (∏ i : Fin n,
      (1 + harperScheduledRelativeIntervalWidth (start + (i : ℕ)))) ≤
        Real.exp 2 := by
  calc
    (∏ i : Fin n,
        (1 + harperScheduledRelativeIntervalWidth (start + (i : ℕ)))) ≤
        ∏ i : Fin n,
          Real.exp (harperScheduledRelativeIntervalWidth (start + (i : ℕ))) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact add_nonneg zero_le_one
          (harperScheduledRelativeIntervalWidth_pos
            (start + (i : ℕ))).le
      · intro i hi
        simpa only [add_comm] using!
          Real.add_one_le_exp
            (harperScheduledRelativeIntervalWidth (start + (i : ℕ)))
    _ = Real.exp (∑ i : Fin n,
        harperScheduledRelativeIntervalWidth (start + (i : ℕ))) := by
      rw [Real.exp_sum]
    _ ≤ Real.exp 2 := Real.exp_le_exp.mpr
      (sum_fin_harperScheduledRelativeIntervalWidth_le_two start n)

/-- Uniform relative comparison of every moderate scheduled lattice cell.
The constant is `exp 2`, with no path-length loss. -/
theorem exists_eventually_harperScheduledModerateCoordinateCell_le_exp_two_mul_gaussian
    (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start → ∀ n y : ℕ,
      harperBlockEndpoint (start + n) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
          ∀ z : Fin n → ℤ,
            (∀ i : Fin n,
              |(z i : ℝ) *
                  harperScheduledRelativeIntervalWidth (start + (i : ℕ))| + 1 ≤
                (1 / 4 : ℝ) *
                  Real.sqrt (((2 ^ (start + (i : ℕ)) : ℕ) : ℝ))) →
            (Measure.pi (fun i : Fin n ↦
              harperCenteredLinearBlockLaw y
                (harperScheduledPrimeBlock y (start + (i : ℕ))) t t)).real
                (harperLatticeIocCell
                  (fun i : Fin n ↦
                    harperScheduledRelativeIntervalWidth (start + (i : ℕ))) z) ≤
              Real.exp 2 *
                (Measure.pi (fun i : Fin n ↦
                  harperGaussianBlockLaw y
                    (harperScheduledPrimeBlock y (start + (i : ℕ))) t t)).real
                  (harperLatticeIocCell
                    (fun i : Fin n ↦
                      harperScheduledRelativeIntervalWidth (start + (i : ℕ))) z) := by
  obtain ⟨J, hJ⟩ :=
    exists_eventually_harperScheduledRelativeIntervalProbability_le_one_add_width_mul_gaussian M
  refine ⟨J, ?_⟩
  intro start hstart n y hy t htLower htUpper z hz
  let rho : Fin n → Measure ℝ := fun i ↦
    harperCenteredLinearBlockLaw y
      (harperScheduledPrimeBlock y (start + (i : ℕ))) t t
  let nu : Fin n → Measure ℝ := fun i ↦
    harperGaussianBlockLaw y
      (harperScheduledPrimeBlock y (start + (i : ℕ))) t t
  let delta : Fin n → ℝ := fun i ↦
    harperScheduledRelativeIntervalWidth (start + (i : ℕ))
  let C : Fin n → ℝ := fun i ↦ 1 + delta i
  have hendpoint (i : Fin n) :
      harperBlockEndpoint (start + (i : ℕ) + 1) ≤ y := by
    exact (monotone_harperBlockEndpoint (by omega)).trans hy
  have hstarti (i : Fin n) : J ≤ start + (i : ℕ) := by omega
  have hcoord (i : Fin n) :
      (rho i).real (Ioc ((z i : ℝ) * delta i)
        ((z i : ℝ) * delta i + delta i)) ≤
        C i * (nu i).real (Ioc ((z i : ℝ) * delta i)
          ((z i : ℝ) * delta i + delta i)) := by
    exact hJ (start + (i : ℕ)) (hstarti i) y (hendpoint i)
      t htLower htUpper ((z i : ℝ) * delta i)
      (by simpa only [delta] using! hz i)
  have hprod := measureReal_pi_coordinateCell_le_prod_mul rho nu C
    (fun i ↦ (z i : ℝ) * delta i) delta hcoord
  have hCprod : (∏ i, C i) ≤ Real.exp 2 := by
    simpa only [C, delta] using!
      prod_one_add_harperScheduledRelativeIntervalWidth_le_exp_two start n
  have hQnonneg : 0 ≤ (Measure.pi nu).real
      (harperCoordinateIocCell (fun i ↦ (z i : ℝ) * delta i) delta) :=
    measureReal_nonneg
  calc
    (Measure.pi rho).real (harperLatticeIocCell delta z) ≤
        (∏ i, C i) *
          (Measure.pi nu).real (harperLatticeIocCell delta z) := by
      simpa only [harperLatticeIocCell] using! hprod
    _ ≤ Real.exp 2 *
        (Measure.pi nu).real (harperLatticeIocCell delta z) := by
      exact mul_le_mul_of_nonneg_right hCprod (by positivity)

end Problem520
end Erdos
