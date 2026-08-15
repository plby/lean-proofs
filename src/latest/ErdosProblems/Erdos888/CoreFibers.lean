import ErdosProblems.Erdos888.CoreEstimate
import ErdosProblems.Erdos888.PrimeEstimates

/-!
# Arithmetic estimates for the squarefree-core fibers

This file supplies the two genuinely arithmetic hypotheses of
`CoreEstimate.eventually_squarefreeCorePairSum_le`.  The cutoff is a small
constant multiple of `log n`.  Below it, the product of the eligible primes
forces every squarefree smooth core to be at most `n^(1/2)` on the logarithmic
scale.  Above it, the constraint `d * r^3 ≤ K * n` gives the required
denominator comparison.  In both ranges, a finite Euler-product expansion
bounds the reciprocal mass of the old cores.
-/

open Filter Finset Real
open scoped BigOperators Topology

namespace Erdos888
namespace CoreFibers

noncomputable section

private abbrev L4 : ℝ := Real.log 4

/-- The positive rate which absorbs both the primorial and the factor `r²`. -/
def cutoffRate : ℝ := Real.log 4 + 2

lemma cutoffRate_pos : 0 < cutoffRate := by
  unfold cutoffRate
  have : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  linarith

/-- A sufficiently small constant multiple of `log n`. -/
def coreCutoff (n : ℕ) : ℕ :=
  ⌊Real.log (n : ℝ) / (2 * cutoffRate)⌋₊

/-- The set of old cores occurring in `smoothCoreFiber`. -/
def eligibleCores (K n r : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (K * n / r ^ 3)).filter fun d ↦
    Squarefree d ∧ ∀ p ∈ d.primeFactors, p < r

lemma smoothCoreFiber_eq_sum_eligible (K n r : ℕ) :
    CoreEstimate.smoothCoreFiber K n r =
      ∑ d ∈ eligibleCores K n r,
        1 / ((d : ℝ) * CoreEstimate.logWeight
          ((n : ℝ) / ((d : ℝ) * (r : ℝ) ^ 2))) := by
  classical
  rw [CoreEstimate.smoothCoreFiber, eligibleCores]
  simp only [Finset.sum_filter]

lemma eligibleCores_pos {K n r d : ℕ} (hd : d ∈ eligibleCores K n r) : 0 < d := by
  exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1

lemma eligibleCores_squarefree {K n r d : ℕ} (hd : d ∈ eligibleCores K n r) :
    Squarefree d :=
  (Finset.mem_filter.mp hd).2.1

lemma eligibleCores_primeFactors_lt {K n r d p : ℕ}
    (hd : d ∈ eligibleCores K n r) (hp : p ∈ d.primeFactors) : p < r :=
  (Finset.mem_filter.mp hd).2.2 p hp

lemma eligibleCores_primeFactors_subset {K n r d : ℕ}
    (hd : d ∈ eligibleCores K n r) :
    d.primeFactors ⊆ primesUpTo r := by
  intro p hp
  rw [mem_primesUpTo]
  exact ⟨Nat.prime_of_mem_primeFactors hp,
    (eligibleCores_primeFactors_lt hd hp).le⟩

private lemma primeFactors_injective_on_eligible (K n r : ℕ) :
    Set.InjOn Nat.primeFactors (eligibleCores K n r : Set ℕ) := by
  intro d hd e he hde
  have hdsf := eligibleCores_squarefree hd
  have hesf := eligibleCores_squarefree he
  calc
    d = ∏ p ∈ d.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hdsf).symm
    _ = ∏ p ∈ e.primeFactors, p := by rw [hde]
    _ = e := Nat.prod_primeFactors_of_squarefree hesf

private lemma reciprocal_eq_primeFactors_product {d : ℕ} (hd : Squarefree d) :
    (1 / (d : ℝ)) = ∏ p ∈ d.primeFactors, (1 / (p : ℝ)) := by
  have hcast : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast (Nat.prod_primeFactors_of_squarefree hd).symm
  rw [hcast]
  rw [one_div, ← Finset.prod_inv_distrib]
  simp only [one_div]

/-- The reciprocal mass of any finite collection of positive squarefree
`r`-smooth integers is bounded by the corresponding Euler product. -/
theorem sum_reciprocal_eligible_le_euler (K n r : ℕ) :
    (∑ d ∈ eligibleCores K n r, 1 / (d : ℝ)) ≤ primeEulerProduct r := by
  classical
  let F : Finset (Finset ℕ) :=
    (eligibleCores K n r).image Nat.primeFactors
  have hF : F ⊆ (primesUpTo r).powerset := by
    intro s hs
    rcases Finset.mem_image.mp hs with ⟨d, hd, rfl⟩
    exact Finset.mem_powerset.mpr (eligibleCores_primeFactors_subset hd)
  calc
    (∑ d ∈ eligibleCores K n r, 1 / (d : ℝ)) =
        ∑ s ∈ F, ∏ p ∈ s, (1 / (p : ℝ)) := by
      rw [Finset.sum_image (primeFactors_injective_on_eligible K n r)]
      apply Finset.sum_congr rfl
      intro d hd
      exact reciprocal_eq_primeFactors_product (eligibleCores_squarefree hd)
    _ ≤ ∑ s ∈ (primesUpTo r).powerset,
        ∏ p ∈ s, (1 / (p : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hF
      intro s hs hsn
      positivity
    _ = primeEulerProduct r := by
      rw [← Finset.prod_one_add]
      unfold primeEulerProduct
      simp only [one_div]

/-- The real primorial has a global Chebyshev bound. -/
lemma primePrimorial_le_exp_log4_mul (r : ℕ) :
    primePrimorial r ≤ Real.exp (Real.log 4 * r) := by
  rw [primePrimorial_eq_exp_theta]
  exact Real.exp_le_exp.mpr (Chebyshev.theta_le_log4_mul_x (by positivity))

/-- Every eligible core divides the primorial and is consequently bounded by
it. -/
lemma eligibleCore_le_primePrimorial {K n r d : ℕ}
    (hd : d ∈ eligibleCores K n r) :
    (d : ℝ) ≤ primePrimorial r := by
  have hsf := eligibleCores_squarefree hd
  have hsubset := eligibleCores_primeFactors_subset hd
  have hnat : d ≤ ∏ p ∈ primesUpTo r, p := by
    rw [← Nat.prod_primeFactors_of_squarefree hsf]
    exact Finset.prod_le_prod_of_subset_of_one_le' hsubset (fun p hp hpn ↦
      (Nat.prime_of_mem_primesLE hp).one_le)
  unfold primePrimorial
  rw [← Nat.cast_prod]
  exact_mod_cast hnat

lemma log_le_self_nat {r : ℕ} (hr : 1 ≤ r) : Real.log (r : ℝ) ≤ r := by
  have hrpos : (0 : ℝ) < r := by positivity
  exact (Real.log_le_sub_one_of_pos hrpos).trans (by linarith)

/-- Uniform Euler-product bound with the regularized logarithmic weight. -/
lemma primeEulerProduct_le_logWeight {r : ℕ} (hr : 2 ≤ r) :
    primeEulerProduct r ≤
      Real.exp Erdos469.reciprocalPrimeMertensConstant *
        CoreEstimate.logWeight r := by
  have h := primeEulerProduct_le hr
  have hlog : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ r by omega))
  have hconst : 0 ≤ Real.exp Erdos469.reciprocalPrimeMertensConstant := by positivity
  calc
    primeEulerProduct r ≤
        Real.exp Erdos469.reciprocalPrimeMertensConstant * Real.log (r : ℝ) := h
    _ ≤ Real.exp Erdos469.reciprocalPrimeMertensConstant *
        CoreEstimate.logWeight r := by
      apply mul_le_mul_of_nonneg_left _ hconst
      change Real.log (r : ℝ) ≤ lambda (r : ℝ)
      rw [lambda_eq_one_add_log (by positivity)]
      linarith

lemma coreCutoff_tendsto_atTop : Tendsto coreCutoff atTop atTop := by
  unfold coreCutoff
  apply tendsto_nat_floor_atTop.comp
  apply Filter.Tendsto.atTop_div_const
  · exact mul_pos (by norm_num) cutoffRate_pos
  · exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem eventually_two_le_coreCutoff :
    ∀ᶠ n : ℕ in atTop, 2 ≤ coreCutoff n :=
  coreCutoff_tendsto_atTop.eventually (eventually_ge_atTop 2)

theorem eventually_sq_K_le_coreCutoff (K : ℕ) :
    ∀ᶠ n : ℕ in atTop, K ^ 2 ≤ coreCutoff n :=
  coreCutoff_tendsto_atTop.eventually (eventually_ge_atTop (K ^ 2))

theorem eventually_coreCutoff_le_K_mul (K : ℕ) (hK : 1 ≤ K) :
    ∀ᶠ n : ℕ in atTop, coreCutoff n ≤ K * n := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hfloor : (coreCutoff n : ℝ) ≤
      Real.log (n : ℝ) / (2 * cutoffRate) := by
    exact Nat.floor_le (div_nonneg hlog0 (mul_nonneg (by norm_num) cutoffRate_pos.le))
  have hden : 1 ≤ 2 * cutoffRate := by
    unfold cutoffRate
    have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
    linarith
  have hquot : Real.log (n : ℝ) / (2 * cutoffRate) ≤ Real.log (n : ℝ) := by
    exact div_le_self hlog0 hden
  have hlogn : Real.log (n : ℝ) ≤ n := log_le_self_nat hn
  have hcast : (coreCutoff n : ℝ) ≤ (K * n : ℕ) := by
    calc
      (coreCutoff n : ℝ) ≤ Real.log (n : ℝ) / (2 * cutoffRate) := hfloor
      _ ≤ Real.log (n : ℝ) := hquot
      _ ≤ (n : ℝ) := hlogn
      _ ≤ (K * n : ℕ) := by exact_mod_cast (Nat.le_mul_of_pos_left n (by omega : 0 < K))
  exact_mod_cast hcast

/-- The logarithmic weight of `n` is controlled by the cutoff itself. -/
theorem eventually_logWeight_le_cutoff :
    ∀ᶠ n : ℕ in atTop,
      CoreEstimate.logWeight n ≤ (4 * cutoffRate + 1) * coreCutoff n := by
  filter_upwards [eventually_two_le_coreCutoff, eventually_ge_atTop 1]
    with n hR hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hfloor : Real.log (n : ℝ) / (2 * cutoffRate) <
      (coreCutoff n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hRone : (1 : ℝ) ≤ coreCutoff n := by exact_mod_cast (show 1 ≤ coreCutoff n by omega)
  have hlog : Real.log (n : ℝ) ≤ 4 * cutoffRate * coreCutoff n := by
    have htmp : Real.log (n : ℝ) <
        (2 * cutoffRate) * ((coreCutoff n : ℝ) + 1) := by
      calc
        Real.log (n : ℝ) = (2 * cutoffRate) *
            (Real.log (n : ℝ) / (2 * cutoffRate)) := by
              field_simp [cutoffRate_pos.ne']
        _ < (2 * cutoffRate) * ((coreCutoff n : ℝ) + 1) := by
              exact mul_lt_mul_of_pos_left hfloor
                (mul_pos (by norm_num) cutoffRate_pos)
    calc
      Real.log (n : ℝ) ≤ (2 * cutoffRate) * ((coreCutoff n : ℝ) + 1) := htmp.le
      _ ≤ 4 * cutoffRate * coreCutoff n := by
        have hrate := cutoffRate_pos.le
        nlinarith
  change lambda (n : ℝ) ≤ _
  rw [lambda_eq_one_add_log (by positivity)]
  calc
    1 + Real.log (n : ℝ) ≤ 1 + 4 * cutoffRate * coreCutoff n := by linarith
    _ ≤ (4 * cutoffRate + 1) * coreCutoff n := by
      nlinarith

/-- In the small-prime range, an eligible squarefree core times `r²` has
logarithm at most half the logarithm of `n`. -/
lemma eligibleCore_mul_sq_log_le_half {K n r d : ℕ}
    (hn : 1 ≤ n) (hr : r < coreCutoff n) (hd : d ∈ eligibleCores K n r) :
    Real.log ((d : ℝ) * (r : ℝ) ^ 2) ≤ Real.log (n : ℝ) / 2 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hcut : (coreCutoff n : ℝ) ≤
      Real.log (n : ℝ) / (2 * cutoffRate) := by
    exact Nat.floor_le (div_nonneg hlog0 (mul_nonneg (by norm_num) cutoffRate_pos.le))
  have hrr : (r : ℝ) ≤ Real.log (n : ℝ) / (2 * cutoffRate) := by
    exact (by exact_mod_cast (Nat.le_of_lt hr) : (r : ℝ) ≤ coreCutoff n) |>.trans hcut
  have hrate : cutoffRate * (r : ℝ) ≤ Real.log (n : ℝ) / 2 := by
    calc
      cutoffRate * (r : ℝ) ≤ cutoffRate *
          (Real.log (n : ℝ) / (2 * cutoffRate)) :=
        mul_le_mul_of_nonneg_left hrr cutoffRate_pos.le
      _ = Real.log (n : ℝ) / 2 := by field_simp [cutoffRate_pos.ne']
  have hdr : (d : ℝ) ≤ Real.exp (Real.log 4 * r) :=
    (eligibleCore_le_primePrimorial hd).trans (primePrimorial_le_exp_log4_mul r)
  have hr_nonneg : (0 : ℝ) ≤ r := by positivity
  have hr_exp : (r : ℝ) ≤ Real.exp (r : ℝ) := by
    calc
      (r : ℝ) ≤ (r : ℝ) + 1 := by linarith
      _ ≤ Real.exp (r : ℝ) := Real.add_one_le_exp _
  have hrsq : (r : ℝ) ^ 2 ≤ Real.exp (2 * r) := by
    calc
      (r : ℝ) ^ 2 ≤ (Real.exp (r : ℝ)) ^ 2 := by gcongr
      _ = Real.exp (2 * r) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
  have hz : (d : ℝ) * (r : ℝ) ^ 2 ≤ Real.exp (Real.log (n : ℝ) / 2) := by
    calc
      (d : ℝ) * (r : ℝ) ^ 2 ≤
          Real.exp (Real.log 4 * r) * Real.exp (2 * r) :=
        mul_le_mul hdr hrsq (by positivity) (by positivity)
      _ = Real.exp (cutoffRate * r) := by
        rw [← Real.exp_add]
        congr 1
        unfold cutoffRate
        ring
      _ ≤ Real.exp (Real.log (n : ℝ) / 2) := Real.exp_le_exp.mpr hrate
  have hzpos : 0 < (d : ℝ) * (r : ℝ) ^ 2 := by
    have hdpos := eligibleCores_pos hd
    have hrpos : 0 < r := by
      by_contra h
      have : r = 0 := Nat.eq_zero_of_not_pos h
      subst r
      simp [eligibleCores] at hd
    positivity
  exact (Real.log_le_iff_le_exp hzpos).mpr hz

/-- A logarithmic half-bound on the extracted factor gives the denominator
comparison used in the small-prime range. -/
lemma logWeight_le_two_div_of_log_le_half {x z : ℝ}
    (hx : 1 ≤ x) (hz : 0 < z)
    (hlog : Real.log z ≤ Real.log x / 2) :
    lambda x ≤ 2 * lambda (x / z) := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hxzpos : 0 < x / z := div_pos hxpos hz
  rw [lambda_eq_one_add_log hxpos.ne', lambda_eq_one_add_log hxzpos.ne',
    Real.log_div hxpos.ne' hz.ne']
  linarith

private lemma eligible_term_le_small {K n r d : ℕ}
    (hn : 1 ≤ n) (hr : r < coreCutoff n)
    (hd : d ∈ eligibleCores K n r) :
    1 / ((d : ℝ) * CoreEstimate.logWeight
        ((n : ℝ) / ((d : ℝ) * (r : ℝ) ^ 2))) ≤
      (2 / CoreEstimate.logWeight n) * (1 / (d : ℝ)) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hzpos : 0 < (d : ℝ) * (r : ℝ) ^ 2 := by
    have hdpos := eligibleCores_pos hd
    have hrpos : 0 < r := by
      by_contra h
      have : r = 0 := Nat.eq_zero_of_not_pos h
      subst r
      simp [eligibleCores] at hd
    positivity
  have hcompare : CoreEstimate.logWeight n ≤
      2 * CoreEstimate.logWeight
        ((n : ℝ) / ((d : ℝ) * (r : ℝ) ^ 2)) := by
    change lambda (n : ℝ) ≤ _
    exact logWeight_le_two_div_of_log_le_half hnR hzpos
      (eligibleCore_mul_sq_log_le_half hn hr hd)
  have hLn : 0 < CoreEstimate.logWeight n :=
    CoreEstimate.logWeight_pos_of_one_le hnR
  have hLx : 0 < CoreEstimate.logWeight
      ((n : ℝ) / ((d : ℝ) * (r : ℝ) ^ 2)) := by
    linarith
  have hinv : 1 / CoreEstimate.logWeight
      ((n : ℝ) / ((d : ℝ) * (r : ℝ) ^ 2)) ≤
      2 / CoreEstimate.logWeight n := by
    rw [div_le_div_iff₀ hLx hLn]
    simpa using hcompare
  calc
    1 / ((d : ℝ) * CoreEstimate.logWeight
        ((n : ℝ) / ((d : ℝ) * (r : ℝ) ^ 2))) =
        (1 / (d : ℝ)) *
          (1 / CoreEstimate.logWeight
            ((n : ℝ) / ((d : ℝ) * (r : ℝ) ^ 2))) := by ring
    _ ≤ (1 / (d : ℝ)) * (2 / CoreEstimate.logWeight n) := by
      gcongr
    _ = (2 / CoreEstimate.logWeight n) * (1 / (d : ℝ)) := by ring

/-- The complete small-range fiber estimate in the exact form consumed by
`CoreEstimate.eventually_squarefreeCorePairSum_le`. -/
theorem smallCoreFiber_le {K n r : ℕ} (hn : 1 ≤ n)
    (hr2 : 2 ≤ r) (hr : r < coreCutoff n) :
    (1 / (r : ℝ) ^ 2) * CoreEstimate.smoothCoreFiber K n r ≤
      (2 * Real.exp Erdos469.reciprocalPrimeMertensConstant) *
        CoreEstimate.coreSeriesTerm r / CoreEstimate.logWeight n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hLn : 0 < CoreEstimate.logWeight n :=
    CoreEstimate.logWeight_pos_of_one_le hnR
  have hsum : CoreEstimate.smoothCoreFiber K n r ≤
      (2 / CoreEstimate.logWeight n) * primeEulerProduct r := by
    rw [smoothCoreFiber_eq_sum_eligible]
    calc
      (∑ d ∈ eligibleCores K n r,
          1 / ((d : ℝ) * CoreEstimate.logWeight
            ((n : ℝ) / ((d : ℝ) * (r : ℝ) ^ 2)))) ≤
          ∑ d ∈ eligibleCores K n r,
            (2 / CoreEstimate.logWeight n) * (1 / (d : ℝ)) := by
        apply Finset.sum_le_sum
        intro d hd
        exact eligible_term_le_small hn hr hd
      _ = (2 / CoreEstimate.logWeight n) *
          (∑ d ∈ eligibleCores K n r, 1 / (d : ℝ)) := by
        rw [Finset.mul_sum]
      _ ≤ (2 / CoreEstimate.logWeight n) * primeEulerProduct r := by
        exact mul_le_mul_of_nonneg_left (sum_reciprocal_eligible_le_euler K n r)
          (by positivity)
  have heuler := primeEulerProduct_le_logWeight hr2
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have hLr : 0 < CoreEstimate.logWeight r :=
    CoreEstimate.logWeight_pos_of_one_le hrR
  calc
    (1 / (r : ℝ) ^ 2) * CoreEstimate.smoothCoreFiber K n r ≤
        (1 / (r : ℝ) ^ 2) *
          ((2 / CoreEstimate.logWeight n) * primeEulerProduct r) := by
      gcongr
    _ ≤ (1 / (r : ℝ) ^ 2) *
        ((2 / CoreEstimate.logWeight n) *
          (Real.exp Erdos469.reciprocalPrimeMertensConstant *
            CoreEstimate.logWeight r)) := by
      gcongr
    _ = (2 * Real.exp Erdos469.reciprocalPrimeMertensConstant) *
        CoreEstimate.coreSeriesTerm r / CoreEstimate.logWeight n := by
      rw [CoreEstimate.coreSeriesTerm]
      field_simp [hLn.ne', hLr.ne']

theorem eventually_smallCoreFiber (K : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ r ∈ Finset.Ico 2 (coreCutoff n), r.Prime →
      (1 / (r : ℝ) ^ 2) * CoreEstimate.smoothCoreFiber K n r ≤
        (2 * Real.exp Erdos469.reciprocalPrimeMertensConstant) *
          CoreEstimate.coreSeriesTerm r / CoreEstimate.logWeight n := by
  filter_upwards [eventually_ge_atTop 1] with n hn r hr hprime
  exact smallCoreFiber_le hn (Finset.mem_Ico.mp hr).1 (Finset.mem_Ico.mp hr).2

private lemma eligibleCore_size {K n r d : ℕ}
    (hr : 0 < r) (hd : d ∈ eligibleCores K n r) :
    d * r ^ 3 ≤ K * n := by
  have hdle : d ≤ K * n / r ^ 3 :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).2
  exact (Nat.le_div_iff_mul_le (pow_pos hr 3)).mp hdle

private lemma eligible_term_le_large {K n r d : ℕ}
    (hK : 1 ≤ K) (hrK : K ^ 2 ≤ r) (hr2 : 2 ≤ r)
    (hd : d ∈ eligibleCores K n r) :
    1 / ((d : ℝ) * CoreEstimate.logWeight
        ((n : ℝ) / ((d : ℝ) * (r : ℝ) ^ 2))) ≤
      (2 / CoreEstimate.logWeight r) * (1 / (d : ℝ)) := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have hLr : 0 < CoreEstimate.logWeight r :=
    CoreEstimate.logWeight_pos_of_one_le hrR
  have hcompare : CoreEstimate.logWeight r ≤
      2 * CoreEstimate.logWeight
        ((n : ℝ) / ((d : ℝ) * (r : ℝ) ^ 2)) := by
    exact CoreEstimate.logWeight_nat_le_two_core_denominator hK hrK
      (eligibleCores_pos hd) (eligibleCore_size (by omega) hd)
  have hLx : 0 < CoreEstimate.logWeight
      ((n : ℝ) / ((d : ℝ) * (r : ℝ) ^ 2)) := by
    linarith
  have hinv : 1 / CoreEstimate.logWeight
      ((n : ℝ) / ((d : ℝ) * (r : ℝ) ^ 2)) ≤
      2 / CoreEstimate.logWeight r := by
    rw [div_le_div_iff₀ hLx hLr]
    simpa using hcompare
  calc
    1 / ((d : ℝ) * CoreEstimate.logWeight
        ((n : ℝ) / ((d : ℝ) * (r : ℝ) ^ 2))) =
        (1 / (d : ℝ)) *
          (1 / CoreEstimate.logWeight
            ((n : ℝ) / ((d : ℝ) * (r : ℝ) ^ 2))) := by ring
    _ ≤ (1 / (d : ℝ)) * (2 / CoreEstimate.logWeight r) := by
      gcongr
    _ = (2 / CoreEstimate.logWeight r) * (1 / (d : ℝ)) := by ring

/-- The complete large-range fiber estimate. -/
theorem largeCoreFiber_le {K n r : ℕ} (hK : 1 ≤ K)
    (hrK : K ^ 2 ≤ r) (hr2 : 2 ≤ r) :
    (1 / (r : ℝ) ^ 2) * CoreEstimate.smoothCoreFiber K n r ≤
      (2 * Real.exp Erdos469.reciprocalPrimeMertensConstant) /
        (r : ℝ) ^ 2 := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have hLr : 0 < CoreEstimate.logWeight r :=
    CoreEstimate.logWeight_pos_of_one_le hrR
  have hsum : CoreEstimate.smoothCoreFiber K n r ≤
      2 * Real.exp Erdos469.reciprocalPrimeMertensConstant := by
    rw [smoothCoreFiber_eq_sum_eligible]
    calc
      (∑ d ∈ eligibleCores K n r,
          1 / ((d : ℝ) * CoreEstimate.logWeight
            ((n : ℝ) / ((d : ℝ) * (r : ℝ) ^ 2)))) ≤
          ∑ d ∈ eligibleCores K n r,
            (2 / CoreEstimate.logWeight r) * (1 / (d : ℝ)) := by
        apply Finset.sum_le_sum
        intro d hd
        exact eligible_term_le_large hK hrK hr2 hd
      _ = (2 / CoreEstimate.logWeight r) *
          (∑ d ∈ eligibleCores K n r, 1 / (d : ℝ)) := by
        rw [Finset.mul_sum]
      _ ≤ (2 / CoreEstimate.logWeight r) * primeEulerProduct r := by
        exact mul_le_mul_of_nonneg_left (sum_reciprocal_eligible_le_euler K n r)
          (by positivity)
      _ ≤ (2 / CoreEstimate.logWeight r) *
          (Real.exp Erdos469.reciprocalPrimeMertensConstant *
            CoreEstimate.logWeight r) := by
        gcongr
        exact primeEulerProduct_le_logWeight hr2
      _ = 2 * Real.exp Erdos469.reciprocalPrimeMertensConstant := by
        field_simp [hLr.ne']
  calc
    (1 / (r : ℝ) ^ 2) * CoreEstimate.smoothCoreFiber K n r ≤
        (1 / (r : ℝ) ^ 2) *
          (2 * Real.exp Erdos469.reciprocalPrimeMertensConstant) := by
      gcongr
    _ = (2 * Real.exp Erdos469.reciprocalPrimeMertensConstant) /
        (r : ℝ) ^ 2 := by ring

lemma smoothCoreFiber_nonneg_small {K n r : ℕ} (hn : 1 ≤ n)
    (hr : r < coreCutoff n) :
    0 ≤ CoreEstimate.smoothCoreFiber K n r := by
  rw [smoothCoreFiber_eq_sum_eligible]
  apply Finset.sum_nonneg
  intro d hd
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hLn : 0 < CoreEstimate.logWeight n :=
    CoreEstimate.logWeight_pos_of_one_le hnR
  have hzpos : 0 < (d : ℝ) * (r : ℝ) ^ 2 := by
    have hdpos := eligibleCores_pos hd
    have hrpos : 0 < r := by
      by_contra h
      have : r = 0 := Nat.eq_zero_of_not_pos h
      subst r
      simp [eligibleCores] at hd
    positivity
  have hcompare : CoreEstimate.logWeight n ≤
      2 * CoreEstimate.logWeight
        ((n : ℝ) / ((d : ℝ) * (r : ℝ) ^ 2)) := by
    change lambda (n : ℝ) ≤ _
    exact logWeight_le_two_div_of_log_le_half hnR hzpos
      (eligibleCore_mul_sq_log_le_half hn hr hd)
  have hLx : 0 < CoreEstimate.logWeight
      ((n : ℝ) / ((d : ℝ) * (r : ℝ) ^ 2)) := by linarith
  positivity

lemma smoothCoreFiber_nonneg_large {K n r : ℕ} (hK : 1 ≤ K)
    (hrK : K ^ 2 ≤ r) (hr2 : 2 ≤ r) :
    0 ≤ CoreEstimate.smoothCoreFiber K n r := by
  rw [smoothCoreFiber_eq_sum_eligible]
  apply Finset.sum_nonneg
  intro d hd
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have hLr : 0 < CoreEstimate.logWeight r :=
    CoreEstimate.logWeight_pos_of_one_le hrR
  have hcompare : CoreEstimate.logWeight r ≤
      2 * CoreEstimate.logWeight
        ((n : ℝ) / ((d : ℝ) * (r : ℝ) ^ 2)) :=
    CoreEstimate.logWeight_nat_le_two_core_denominator hK hrK
      (eligibleCores_pos hd) (eligibleCore_size (by omega) hd)
  have hLx : 0 < CoreEstimate.logWeight
      ((n : ℝ) / ((d : ℝ) * (r : ℝ) ^ 2)) := by linarith
  positivity

theorem eventually_largeCoreFiber (K : ℕ) (hK : 1 ≤ K) :
    ∀ᶠ n : ℕ in atTop,
      ∀ r ∈ Finset.Icc (coreCutoff n) (K * n), r.Prime →
        (1 / (r : ℝ) ^ 2) * CoreEstimate.smoothCoreFiber K n r ≤
          (2 * Real.exp Erdos469.reciprocalPrimeMertensConstant) /
            (r : ℝ) ^ 2 := by
  filter_upwards [eventually_sq_K_le_coreCutoff K, eventually_two_le_coreCutoff]
    with n hKcut h2cut r hr hprime
  have hcutr := (Finset.mem_Icc.mp hr).1
  exact largeCoreFiber_le hK (hKcut.trans hcutr) (h2cut.trans hcutr)

/-- Unconditional `O_K(1 / log n)` form of the complete pair sum.  The
constant is existential because the convergent initial series is packaged
that way in `CoreEstimate`. -/
theorem exists_eventually_squarefreeCorePairSum_le (K : ℕ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      CoreEstimate.squarefreeCorePairSum K n ≤
        C / CoreEstimate.logWeight n := by
  obtain ⟨B, hB0, hB⟩ := CoreEstimate.exists_uniform_coreSeries_bound
  let a : ℝ := 2 * Real.exp Erdos469.reciprocalPrimeMertensConstant
  let E : ℝ := 4 * cutoffRate + 1
  let C : ℝ := a * B + a * 2 * E + 1
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hE : 0 ≤ E := by
    dsimp [E]
    have := cutoffRate_pos.le
    linarith
  have hraw : 0 ≤ a * B + a * 2 * E := by positivity
  have hC : 0 < C := by
    dsimp [C]
    linarith
  refine ⟨C, hC, ?_⟩
  have hlogpos : ∀ᶠ n : ℕ in atTop,
      0 < CoreEstimate.logWeight n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact CoreEstimate.logWeight_pos_of_one_le (by exact_mod_cast hn)
  have hseries : ∀ᶠ n : ℕ in atTop,
      (∑ r ∈ Finset.Ico 2 (coreCutoff n),
        CoreEstimate.coreSeriesTerm r) ≤ B :=
    Filter.Eventually.of_forall fun n ↦ hB (coreCutoff n)
  have htail : ∀ᶠ n : ℕ in atTop,
      (∑ r ∈ Finset.Icc (coreCutoff n) (K * n),
        1 / (r : ℝ) ^ 2) ≤ (2 : ℝ) / coreCutoff n := by
    filter_upwards [eventually_two_le_coreCutoff] with n hn
    exact CoreEstimate.reciprocalSquare_Icc_le (coreCutoff n) (K * n) hn
  have hmain : ∀ᶠ n : ℕ in atTop,
      CoreEstimate.squarefreeCorePairSum K n ≤
        (a * B + a * 2 * E) / CoreEstimate.logWeight n := by
    apply CoreEstimate.eventually_squarefreeCorePairSum_le
        (K := K) (R := coreCutoff) (a := a) (b := a)
        (B := B) (D := 2) (E := E)
    · exact ha
    · exact ha
    · exact eventually_two_le_coreCutoff
    · exact eventually_coreCutoff_le_K_mul K hK
    · exact hlogpos
    · simpa [E] using eventually_logWeight_le_cutoff
    · simpa [a] using eventually_smallCoreFiber K
    · simpa [a] using eventually_largeCoreFiber K hK
    · exact hseries
    · exact htail
  filter_upwards [hmain, hlogpos] with n hn hnlog
  calc
    CoreEstimate.squarefreeCorePairSum K n ≤
        (a * B + a * 2 * E) / CoreEstimate.logWeight n := hn
    _ ≤ C / CoreEstimate.logWeight n := by
      apply div_le_div_of_nonneg_right _ hnlog.le
      dsimp [C]
      linarith

theorem eventually_squarefreeCorePairSum_nonneg (K : ℕ) (hK : 1 ≤ K) :
    ∀ᶠ n : ℕ in atTop,
      0 ≤ CoreEstimate.squarefreeCorePairSum K n := by
  filter_upwards [eventually_ge_atTop 1, eventually_two_le_coreCutoff,
    eventually_sq_K_le_coreCutoff K] with n hn hcut2 hcutK
  unfold CoreEstimate.squarefreeCorePairSum
  apply Finset.sum_nonneg
  intro r hr
  split_ifs with hprime
  · have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
    have houter : 0 ≤ 1 / (r : ℝ) ^ 2 := by positivity
    apply mul_nonneg houter
    by_cases hsmall : r < coreCutoff n
    · exact smoothCoreFiber_nonneg_small hn hsmall
    · exact smoothCoreFiber_nonneg_large hK
        (hcutK.trans (le_of_not_gt hsmall)) hr2
  · exact le_rfl

/-- Big-O packaging of the unconditional core-pair estimate. -/
theorem squarefreeCorePairSum_isBigO (K : ℕ) (hK : 1 ≤ K) :
    (fun n : ℕ ↦ CoreEstimate.squarefreeCorePairSum K n) =O[atTop]
      (fun n : ℕ ↦ 1 / CoreEstimate.logWeight n) := by
  obtain ⟨C, hC, hbound⟩ := exists_eventually_squarefreeCorePairSum_le K hK
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [hbound, eventually_squarefreeCorePairSum_nonneg K hK,
    eventually_ge_atTop 1] with n hn hnonneg hn1
  have hlog : 0 < CoreEstimate.logWeight n :=
    CoreEstimate.logWeight_pos_of_one_le (by exact_mod_cast hn1)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnonneg,
    abs_of_nonneg (by positivity : 0 ≤ 1 / CoreEstimate.logWeight n)]
  simpa [div_eq_mul_inv] using hn

end
end CoreFibers
end Erdos888
