/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.SharpPair
import ErdosProblems.Erdos896.Ford.OccupancyPotential
import ErdosProblems.Erdos896.Ford.OccupancyMultinomial
import ErdosProblems.Erdos896.Ford.StirlingScale

/-!
# Ford's weighted isolated-divisor sum

This file specializes the isolated-divisor part of Ford's lower-bound
argument to the dyadic width `sigma = log 2` and to the critical choice
`g = 1`, `k = v`.  The first part is the elementary content of Ford's
Lemma 4.5: the close-pair defect `3 * tau - 2 * W` is paid for by isolated
divisors.  The later parts combine the prime blocks and the finite occupancy
lemma to produce the factorial-scale lower bound used in the exact-one
divisor estimate.
-/

namespace Erdos896.Ford

open Filter
open scoped BigOperators

/-! ## Occupancy profiles -/

/-- Extend a finite occupancy vector by zero to the arithmetic profile
indexed by all natural block numbers. -/
def extendOccupancyProfile {v : ℕ} (b : Fin v → ℕ) (i : ℕ) : ℕ :=
  if hi : i < v then b ⟨i, hi⟩ else 0

/-- The block profile attached to a placement of `v` labelled balls in
`v` boxes, extended by zero away from the first `v` indices. -/
def occupancyProfile {v : ℕ} (f : Fin v → Fin v) (i : ℕ) : ℕ :=
  extendOccupancyProfile (Occupancy.occupancyVector f) i

@[simp]
theorem extendOccupancyProfile_of_lt {v : ℕ} (b : Fin v → ℕ)
    {i : ℕ} (hi : i < v) :
    extendOccupancyProfile b i = b ⟨i, hi⟩ := by
  simp [extendOccupancyProfile, hi]

@[simp]
theorem extendOccupancyProfile_of_le {v : ℕ} (b : Fin v → ℕ)
    {i : ℕ} (hi : v ≤ i) :
    extendOccupancyProfile b i = 0 := by
  simp [extendOccupancyProfile, Nat.not_lt.mpr hi]

@[simp]
theorem occupancyProfile_eq_extendOccupancyProfile {v : ℕ}
    (f : Fin v → Fin v) :
    occupancyProfile f =
      extendOccupancyProfile (Occupancy.occupancyVector f) := rfl

@[simp]
theorem occupancyProfile_of_lt {v : ℕ} (f : Fin v → Fin v)
    {i : ℕ} (hi : i < v) :
    occupancyProfile f i = Occupancy.boxOccupancy f ⟨i, hi⟩ := by
  simp [occupancyProfile, Occupancy.occupancyVector, hi]

@[simp]
theorem occupancyProfile_of_le {v : ℕ} (f : Fin v → Fin v)
    {i : ℕ} (hi : v ≤ i) :
    occupancyProfile f i = 0 := by
  simp [occupancyProfile, extendOccupancyProfile, Nat.not_lt.mpr hi]

/-- The arithmetic factorial denominator agrees with the finite occupancy
vector denominator used in the multinomial identity. -/
theorem profileFactorial_extendOccupancyProfile {v : ℕ} (b : Fin v → ℕ) :
    profileFactorial v (extendOccupancyProfile b) =
      ∏ j : Fin v, (b j).factorial := by
  rw [profileFactorial,
    ← Fin.prod_univ_eq_prod_range
      (fun i => (extendOccupancyProfile b i).factorial) v]
  apply Finset.prod_congr rfl
  intro i hi
  simp [extendOccupancyProfile]

/-- Every occupancy profile prescribes exactly `v` primes. -/
@[simp]
theorem profilePrimeCount_occupancyProfile {v : ℕ} (f : Fin v → Fin v) :
    profilePrimeCount v (occupancyProfile f) = v := by
  rw [profilePrimeCount]
  calc
    (∑ i ∈ Finset.range v, occupancyProfile f i) =
        ∑ i : Fin v, Occupancy.boxOccupancy f i := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => occupancyProfile f i) v]
      apply Finset.sum_congr rfl
      intro i hi
      simp [occupancyProfile, Occupancy.occupancyVector]
    _ = v := by
      simpa [Occupancy.occupancyList, List.sum_ofFn] using
        Occupancy.sum_occupancyList f

/-- Total occupancy of any represented finite vector is `v`. -/
theorem profilePrimeCount_extend_occupancyVector {v : ℕ}
    (f : Fin v → Fin v) :
    profilePrimeCount v
        (extendOccupancyProfile (Occupancy.occupancyVector f)) = v := by
  simpa only [occupancyProfile_eq_extendOccupancyProfile] using
    profilePrimeCount_occupancyProfile f

/-- Prefixes of the arithmetic profile are the cumulative box
occupancies used by the finite order-statistics argument. -/
theorem profilePrefixCount_occupancyProfile {v : ℕ}
    (f : Fin v → Fin v) {i : ℕ} (hi : i < v) :
    profilePrefixCount (occupancyProfile f) i =
      Occupancy.cumulativeOccupancy f (i + 1) := by
  rw [profilePrefixCount]
  rw [← Occupancy.sum_take_occupancyList_eq_cumulative f (by omega)]
  rw [Occupancy.occupancyList,
    ← Fin.ofFn_take_eq_take_ofFn (show i + 1 ≤ v by omega)]
  rw [List.sum_ofFn,
    ← Fin.sum_univ_eq_sum_range (fun j => occupancyProfile f j) (i + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [occupancyProfile, extendOccupancyProfile_of_lt
    (Occupancy.occupancyVector f) (show j.1 < v by omega)]
  unfold Occupancy.occupancyVector
  congr 2

/-- The real profile potential is twice the rational potential used in the
finite counting lemma.  The factor comes only from the zero-based block
index. -/
theorem profilePrefixPotential_occupancyProfile {v : ℕ}
    (f : Fin v → Fin v) :
    profilePrefixPotential v (occupancyProfile f) =
      2 * (Occupancy.expPotential f : ℝ) := by
  rw [profilePrefixPotential, Occupancy.expPotential]
  rw [← Fin.sum_univ_eq_sum_range
    (fun i => (2 : ℝ) ^ profilePrefixCount (occupancyProfile f) i /
      (2 : ℝ) ^ i) v]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [profilePrefixCount_occupancyProfile f i.isLt]
  rw [← Occupancy.prefixOccupancy_eq_cumulative f i]
  norm_num [pow_succ]
  ring

/-- A good occupancy automatically satisfies the polynomial profile cap
used in the squarefree mass estimate, already with `M = 1`. -/
theorem admissibleProfile_occupancyProfile {v : ℕ} {f : Fin v → Fin v}
    (hf : Occupancy.Good f) :
    AdmissibleProfile 1 v (occupancyProfile f) := by
  intro i hi
  have hprefix := Occupancy.cumulativeOccupancy_le hf (show i + 1 ≤ v by omega)
  have hbox : Occupancy.boxOccupancy f ⟨i, hi⟩ ≤
      Occupancy.cumulativeOccupancy f (i + 1) := by
    unfold Occupancy.boxOccupancy Occupancy.cumulativeOccupancy
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hx]
    exact Nat.lt_succ_self i
  rw [occupancyProfile_of_lt f hi]
  calc
    Occupancy.boxOccupancy f ⟨i, hi⟩ ≤
        Occupancy.cumulativeOccupancy f (i + 1) := hbox
    _ ≤ i + 1 := hprefix
    _ ≤ 1 + i ^ 2 := by nlinarith [Nat.zero_le i]

/-- The ordered occupancy list is determined by the occupancy vector. -/
theorem Occupancy.occupancyList_eq_of_occupancyVector_eq {v : ℕ}
    {f g : Fin v → Fin v}
    (hfg : Occupancy.occupancyVector f = Occupancy.occupancyVector g) :
    Occupancy.occupancyList f = Occupancy.occupancyList g := by
  unfold Occupancy.occupancyVector at hfg
  unfold Occupancy.occupancyList
  have hbox : Occupancy.boxOccupancy f = Occupancy.boxOccupancy g := by
    funext j
    exact congrFun hfg j
  exact congrArg List.ofFn hbox

theorem Occupancy.good_iff_of_occupancyVector_eq {v : ℕ}
    {f g : Fin v → Fin v}
    (hfg : Occupancy.occupancyVector f = Occupancy.occupancyVector g) :
    Occupancy.Good f ↔ Occupancy.Good g := by
  rw [Occupancy.Good, Occupancy.Good,
    Occupancy.occupancyList_eq_of_occupancyVector_eq hfg]

theorem Occupancy.expPotential_eq_of_occupancyVector_eq {v : ℕ}
    {f g : Fin v → Fin v}
    (hfg : Occupancy.occupancyVector f = Occupancy.occupancyVector g) :
    Occupancy.expPotential f = Occupancy.expPotential g := by
  unfold Occupancy.expPotential Occupancy.prefixOccupancy
  rw [Occupancy.occupancyList_eq_of_occupancyVector_eq hfg]

theorem Occupancy.goodPotential_iff_of_occupancyVector_eq {v : ℕ}
    {B : ℚ} {f g : Fin v → Fin v}
    (hfg : Occupancy.occupancyVector f = Occupancy.occupancyVector g) :
    Occupancy.GoodPotential B f ↔ Occupancy.GoodPotential B g := by
  unfold Occupancy.GoodPotential
  rw [Occupancy.good_iff_of_occupancyVector_eq hfg,
    Occupancy.expPotential_eq_of_occupancyVector_eq hfg]

/-- The bounded-potential good placements form a union of complete
multinomial occupancy fibers. -/
theorem Occupancy.goodPotential_occupancyInvariant {v : ℕ} (B : ℚ) :
    Occupancy.OccupancyInvariant
      (Finset.univ.filter (@Occupancy.GoodPotential v B)) := by
  intro f g hfg
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Occupancy.goodPotential_iff_of_occupancyVector_eq hfg

/-- The finite placement set selected by the occupancy-potential bound. -/
noncomputable def goodPotentialPlacements (v : ℕ) (B : ℚ) :
    Finset (Fin v → Fin v) :=
  Finset.univ.filter (@Occupancy.GoodPotential v B)

/-- The distinct occupancy vectors represented among the selected
placements. -/
noncomputable def goodPotentialProfiles (v : ℕ) (B : ℚ) :
    Finset (Fin v → ℕ) :=
  Occupancy.occupancyVectors (goodPotentialPlacements v B)

/-- The squarefree-number family obtained by taking all prime selections
for every selected occupancy profile. -/
noncomputable def goodProfileNumberFamily
    (start v : ℕ) (B : ℚ) : Finset ℕ :=
  (goodPotentialProfiles v B).biUnion fun b =>
    profileNumberFamily start v (extendOccupancyProfile b)

/-- The deterministic product of block upper endpoints prescribed by a
profile.  This is the natural size envelope for every number represented by
that profile. -/
noncomputable def profileEndpointProduct
    (start blocks : ℕ) (b : ℕ → ℕ) : ℕ :=
  ∏ i ∈ Finset.range blocks, primeBlockUpper (start + i) ^ b i

/-- Ford's high-end cap gives this profile-independent endpoint envelope.
The exponent at block `j` is the cap obtained from the final `v-j` boxes. -/
noncomputable def highCapEndpointProduct
    (start v M : ℕ) : ℕ :=
  ∏ j ∈ Finset.range v,
    primeBlockUpper (start + j) ^ (M + (v - j) ^ 2)

private theorem reverseQuadraticSum_exact (v : ℕ) :
    (∑ d ∈ Finset.range v, (d + 1) ^ 2 * 2 ^ (v - 1 - d)) +
        (v ^ 2 + 4 * v + 6) = 6 * 2 ^ v := by
  induction v with
  | zero => norm_num
  | succ v ih =>
      by_cases hv : v = 0
      · subst v
        norm_num
      · rw [Finset.sum_range_succ]
        have hsum :
            (∑ d ∈ Finset.range v,
              (d + 1) ^ 2 * 2 ^ (v + 1 - 1 - d)) =
              2 * ∑ d ∈ Finset.range v,
                (d + 1) ^ 2 * 2 ^ (v - 1 - d) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d hd
          have hdv : d < v := Finset.mem_range.mp hd
          rw [show v + 1 - 1 - d = (v - 1 - d) + 1 by omega, pow_succ]
          ring
        rw [hsum]
        rw [show v + 1 - 1 - v = 0 by omega, pow_zero, mul_one, pow_succ]
        calc
          2 * (∑ d ∈ Finset.range v,
                  (d + 1) ^ 2 * 2 ^ (v - 1 - d)) +
                (v + 1) ^ 2 + ((v + 1) ^ 2 + 4 * (v + 1) + 6) =
              2 * ((∑ d ∈ Finset.range v,
                  (d + 1) ^ 2 * 2 ^ (v - 1 - d)) +
                (v ^ 2 + 4 * v + 6)) := by ring
          _ = 2 * (6 * 2 ^ v) := by rw [ih]
          _ = 6 * (2 ^ v * 2) := by ring

private theorem reverseQuadraticSum_le (v : ℕ) :
    (∑ d ∈ Finset.range v, (d + 1) ^ 2 * 2 ^ (v - 1 - d)) ≤
      6 * 2 ^ v := by
  have h := reverseQuadraticSum_exact v
  omega

private theorem finReverseQuadraticSum_le (v : ℕ) :
    (∑ j : Fin v, (v - j.val) ^ 2 * 2 ^ j.val) ≤ 6 * 2 ^ v := by
  calc
    (∑ j : Fin v, (v - j.val) ^ 2 * 2 ^ j.val) =
        ∑ d : Fin v, (d.val + 1) ^ 2 * 2 ^ (v - 1 - d.val) := by
      refine (Equiv.sum_comp Fin.revPerm _).symm.trans ?_
      apply Fintype.sum_congr
      intro d
      simp only [Fin.revPerm_apply, Fin.val_rev]
      congr 2 <;> omega
    _ = ∑ d ∈ Finset.range v,
          (d + 1) ^ 2 * 2 ^ (v - 1 - d) := by
      exact Fin.sum_univ_eq_sum_range
        (fun d ↦ (d + 1) ^ 2 * 2 ^ (v - 1 - d)) v
    _ ≤ 6 * 2 ^ v := reverseQuadraticSum_le v

private theorem sumTwoPow_exact (v : ℕ) :
    (∑ j ∈ Finset.range v, 2 ^ j) + 1 = 2 ^ v := by
  induction v with
  | zero => norm_num
  | succ v ih =>
      rw [Finset.sum_range_succ, pow_succ]
      omega

private theorem finSumTwoPow_le (v : ℕ) :
    (∑ j : Fin v, 2 ^ j.val) ≤ 2 ^ v := by
  rw [show (∑ j : Fin v, 2 ^ j.val) =
      ∑ j ∈ Finset.range v, 2 ^ j by
        exact Fin.sum_univ_eq_sum_range (fun j ↦ 2 ^ j) v]
  have h := sumTwoPow_exact v
  omega

/-- The quadratic high-end caps cost only a fixed multiple of the last
dyadic block, uniformly in the number of blocks. -/
theorem finHighCapWeight_le (v M : ℕ) :
    (∑ j : Fin v, (M + (v - j.val) ^ 2) * 2 ^ j.val) ≤
      (M + 6) * 2 ^ v := by
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hM := Nat.mul_le_mul_left M (finSumTwoPow_le v)
  have hQ := finReverseQuadraticSum_le v
  omega

/-- The logarithm of the uniform endpoint envelope is bounded by a fixed
multiple of the last dyadic scale.  This is the deterministic size estimate
behind Ford's high-end occupancy truncation. -/
theorem log_highCapEndpointProduct_le (start v M : ℕ) :
    Real.log (highCapEndpointProduct start v M : ℝ) ≤
      primeBlockLogUpperConstant * (M + 6 : ℕ) *
        (2 : ℝ) ^ (start + 1) * (2 : ℝ) ^ v := by
  rw [highCapEndpointProduct, Nat.cast_prod]
  rw [Real.log_prod]
  · calc
      (∑ j ∈ Finset.range v,
          Real.log (((primeBlockUpper (start + j) ^
            (M + (v - j) ^ 2) : ℕ) : ℝ))) =
          ∑ j ∈ Finset.range v,
            (M + (v - j) ^ 2 : ℕ) *
              Real.log (primeBlockUpper (start + j) : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        push_cast
        rw [Real.log_pow]
        rw [Nat.cast_add, Nat.cast_pow]
      _ ≤ ∑ j ∈ Finset.range v,
            (M + (v - j) ^ 2 : ℕ) *
              (primeBlockLogUpperConstant * (2 : ℝ) ^ (start + j + 1)) := by
        apply Finset.sum_le_sum
        intro j hj
        gcongr
        simpa [primeBlockUpper] using
          log_endpoint_le_primeBlockLogUpperConstant_mul_pow (start + j + 1)
      _ = primeBlockLogUpperConstant * (2 : ℝ) ^ (start + 1) *
            (∑ j ∈ Finset.range v,
              ((M + (v - j) ^ 2) * 2 ^ j : ℕ)) := by
        push_cast
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [show start + j + 1 = (start + 1) + j by omega, pow_add]
        ring
      _ ≤ primeBlockLogUpperConstant * (2 : ℝ) ^ (start + 1) *
            ((M + 6 : ℕ) * 2 ^ v : ℕ) := by
        apply mul_le_mul_of_nonneg_left
        · have hNat :
              (∑ j ∈ Finset.range v,
                (M + (v - j) ^ 2) * 2 ^ j) ≤ (M + 6) * 2 ^ v := by
              rw [← Fin.sum_univ_eq_sum_range]
              exact finHighCapWeight_le v M
          exact_mod_cast hNat
        · exact mul_nonneg primeBlockLogUpperConstant_pos.le (by positivity)
      _ = primeBlockLogUpperConstant * (M + 6 : ℕ) *
          (2 : ℝ) ^ (start + 1) * (2 : ℝ) ^ v := by
        push_cast
        ring
  · intro j hj
    exact_mod_cast (pow_pos (lt_of_lt_of_le (by omega : 0 < 2)
      (two_le_primeBlockEndpoint (start + j + 1))) _).ne'

theorem highCapEndpointProduct_pos (start v M : ℕ) :
    0 < highCapEndpointProduct start v M := by
  unfold highCapEndpointProduct
  apply Finset.prod_pos
  intro j hj
  exact pow_pos (lt_of_lt_of_le (by omega : 0 < 2)
    (two_le_primeBlockEndpoint (start + j + 1))) _

/-- Exponential form of `log_highCapEndpointProduct_le`. -/
theorem cast_highCapEndpointProduct_le_exp (start v M : ℕ) :
    (highCapEndpointProduct start v M : ℝ) ≤
      Real.exp (primeBlockLogUpperConstant * (M + 6 : ℕ) *
        (2 : ℝ) ^ (start + 1) * (2 : ℝ) ^ v) := by
  have hpos : (0 : ℝ) < highCapEndpointProduct start v M := by
    exact_mod_cast highCapEndpointProduct_pos start v M
  calc
    (highCapEndpointProduct start v M : ℝ) =
        Real.exp (Real.log (highCapEndpointProduct start v M : ℝ)) :=
      (Real.exp_log hpos).symm
    _ ≤ _ := Real.exp_le_exp.mpr (log_highCapEndpointProduct_le start v M)

/-- If the last dyadic endpoint scale fits below `log y`, then the capped
endpoint envelope, and hence every represented number, has square at most
`y`. -/
theorem highCapEndpointProduct_sq_le_of_scale
    {start v M y : ℕ} (hy : 1 ≤ y)
    (hscale :
      2 * (primeBlockLogUpperConstant * (M + 6 : ℕ) *
        (2 : ℝ) ^ (start + 1) * (2 : ℝ) ^ v) ≤ Real.log (y : ℝ)) :
    (highCapEndpointProduct start v M) ^ 2 ≤ y := by
  have hpos : (0 : ℝ) < highCapEndpointProduct start v M := by
    exact_mod_cast highCapEndpointProduct_pos start v M
  have hypos : (0 : ℝ) < y := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hy)
  apply_mod_cast (show
    (highCapEndpointProduct start v M : ℝ) ^ 2 ≤ (y : ℝ) from ?_)
  calc
    (highCapEndpointProduct start v M : ℝ) ^ 2 =
        (Real.exp (Real.log (highCapEndpointProduct start v M : ℝ))) ^ 2 := by
      rw [Real.exp_log hpos]
    _ = Real.exp (2 * Real.log (highCapEndpointProduct start v M : ℝ)) := by
      rw [← Real.exp_nat_mul]
      norm_num
    _ ≤ Real.exp (Real.log (y : ℝ)) := by
      apply Real.exp_le_exp.mpr
      exact (mul_le_mul_of_nonneg_left
        (log_highCapEndpointProduct_le start v M) (by norm_num)).trans hscale
    _ = (y : ℝ) := Real.exp_log hypos

/-! ## Fixed shifts of the critical factorial scale -/

/-- The exact factorial expression supplied by the finite occupancy
argument. -/
noncomputable def criticalFactorialTerm (v : ℕ) : ℝ :=
  (2 * (v : ℝ) * Real.log 2) ^ v / ((v + 1).factorial : ℝ)

theorem criticalFactorialTerm_succ_le (n : ℕ) (hn : 1 ≤ n) :
    criticalFactorialTerm (n + 1) ≤
      (2 * Real.exp 1 * Real.log 2) * criticalFactorialTerm n := by
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hstandard := Real.one_add_inv_pow_le_exp (n := n)
  have hratio : (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ n ≤ Real.exp 1 := by
    calc
      (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ n =
          (1 + (n : ℝ)⁻¹) ^ n := by
        congr 1
        push_cast
        field_simp
      _ ≤ Real.exp 1 := hstandard
  have hfrac : (((n + 1 : ℕ) : ℝ) / (n + 2 : ℕ)) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    norm_num
  have hpowEq :
      ((((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ n) *
          (2 * (n : ℝ) * Real.log 2) ^ n =
        (2 * ((n + 1 : ℕ) : ℝ) * Real.log 2) ^ n := by
    rw [← mul_pow]
    congr 1
    push_cast
    field_simp
  rw [criticalFactorialTerm, criticalFactorialTerm]
  calc
    (2 * ((n + 1 : ℕ) : ℝ) * Real.log 2) ^ (n + 1) /
          (((n + 1 + 1).factorial : ℕ) : ℝ) =
        (2 * Real.log 2 * (((n + 1 : ℕ) : ℝ) / (n + 2 : ℕ))) *
          ((((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ n) *
            ((2 * (n : ℝ) * Real.log 2) ^ n /
              (((n + 1).factorial : ℕ) : ℝ)) := by
      calc
        (2 * ((n + 1 : ℕ) : ℝ) * Real.log 2) ^ (n + 1) /
              (((n + 1 + 1).factorial : ℕ) : ℝ) =
            (2 * Real.log 2 * (((n + 1 : ℕ) : ℝ) / (n + 2 : ℕ))) *
              (2 * ((n + 1 : ℕ) : ℝ) * Real.log 2) ^ n /
                (((n + 1).factorial : ℕ) : ℝ) := by
          rw [show n + 1 + 1 = (n + 1) + 1 by omega,
            Nat.factorial_succ, pow_succ]
          push_cast
          field_simp
        _ = _ := by
          rw [div_eq_mul_inv, div_eq_mul_inv, ← hpowEq]
          ring
    _ ≤ (2 * Real.log 2 * 1) * (Real.exp 1) *
          ((2 * (n : ℝ) * Real.log 2) ^ n /
            (((n + 1).factorial : ℕ) : ℝ)) := by
      gcongr
    _ = (2 * Real.exp 1 * Real.log 2) *
          ((2 * (n : ℝ) * Real.log 2) ^ n /
            (((n + 1).factorial : ℕ) : ℝ)) := by ring

theorem criticalFactorialTerm_add_le (d n : ℕ) (hn : 1 ≤ n) :
    criticalFactorialTerm (n + d) ≤
      (2 * Real.exp 1 * Real.log 2) ^ d * criticalFactorialTerm n := by
  induction d with
  | zero => simp
  | succ d ih =>
      calc
        criticalFactorialTerm (n + (d + 1)) =
            criticalFactorialTerm ((n + d) + 1) := by congr 1
        _ ≤ (2 * Real.exp 1 * Real.log 2) *
              criticalFactorialTerm (n + d) :=
          criticalFactorialTerm_succ_le (n + d) (by omega)
        _ ≤ (2 * Real.exp 1 * Real.log 2) *
              ((2 * Real.exp 1 * Real.log 2) ^ d *
                criticalFactorialTerm n) := by
          gcongr
        _ = (2 * Real.exp 1 * Real.log 2) ^ (d + 1) *
              criticalFactorialTerm n := by rw [pow_succ]; ring

theorem criticalFactorialTerm_le_shifted
    {d k : ℕ} (hdk : d ≤ k) (hv : 1 ≤ k - d) :
    criticalFactorialTerm k ≤
      (2 * Real.exp 1 * Real.log 2) ^ d *
        criticalFactorialTerm (k - d) := by
  calc
    criticalFactorialTerm k = criticalFactorialTerm ((k - d) + d) := by
      congr 1
      omega
    _ ≤ _ := criticalFactorialTerm_add_le d (k - d) hv

theorem stirlingTerm_le_exp_mul_criticalFactorialTerm
    {y : ℝ} (ht : 0 ≤ Real.log (Real.log y))
    (hk : 1 ≤ stirlingIndex y) :
    stirlingTerm y ≤ Real.exp 1 * criticalFactorialTerm (stirlingIndex y) := by
  let t := Real.log (Real.log y)
  let k := stirlingIndex y
  have hkR : (0 : ℝ) < k := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hquot := loglog_div_log_two_lt_stirlingIndex_add_one y
  have htupper : t ≤ ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
    apply (div_le_iff₀ hlog).mp
    exact hquot.le
  have hstandard := Real.one_add_inv_pow_le_exp (n := k)
  have hratio : (((k + 1 : ℕ) : ℝ) / (k : ℝ)) ^ k ≤ Real.exp 1 := by
    calc
      (((k + 1 : ℕ) : ℝ) / (k : ℝ)) ^ k =
          (1 + (k : ℝ)⁻¹) ^ k := by
        congr 1
        push_cast
        field_simp
      _ ≤ Real.exp 1 := hstandard
  have hpowEq :
      ((((k + 1 : ℕ) : ℝ) / (k : ℝ)) ^ k) *
          (2 * (k : ℝ) * Real.log 2) ^ k =
        (2 * ((k + 1 : ℕ) : ℝ) * Real.log 2) ^ k := by
    rw [← mul_pow]
    congr 1
    push_cast
    field_simp
  rw [stirlingTerm, criticalFactorialTerm]
  dsimp only [t, k] at htupper ⊢
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    (2 * Real.log (Real.log y)) ^ stirlingIndex y ≤
        (2 * (((stirlingIndex y + 1 : ℕ) : ℝ) * Real.log 2)) ^
          stirlingIndex y := by
      gcongr
    _ = (((stirlingIndex y + 1 : ℕ) : ℝ) /
          (stirlingIndex y : ℝ)) ^ stirlingIndex y *
            (2 * (stirlingIndex y : ℝ) * Real.log 2) ^
              stirlingIndex y := by
      simpa [k, mul_assoc] using hpowEq.symm
    _ ≤ Real.exp 1 *
          (2 * (stirlingIndex y : ℝ) * Real.log 2) ^ stirlingIndex y := by
      gcongr

/-- The positive constant lost by shifting the critical index down by `d`
blocks. -/
noncomputable def shiftedCriticalConstant (d : ℕ) : ℝ :=
  (Real.exp 1 * (2 * Real.exp 1 * Real.log 2) ^ d)⁻¹

theorem shiftedCriticalConstant_pos (d : ℕ) :
    0 < shiftedCriticalConstant d := by
  unfold shiftedCriticalConstant
  positivity

theorem shiftedCriticalConstant_mul_stirlingTerm_le
    {d : ℕ} {y : ℝ} (ht : 0 ≤ Real.log (Real.log y))
    (hk : d + 1 ≤ stirlingIndex y) :
    shiftedCriticalConstant d * stirlingTerm y ≤
      criticalFactorialTerm (stirlingIndex y - d) := by
  have hv : 1 ≤ stirlingIndex y - d := by omega
  have hfirst := stirlingTerm_le_exp_mul_criticalFactorialTerm ht
    (show 1 ≤ stirlingIndex y by omega)
  have hshift := criticalFactorialTerm_le_shifted
    (show d ≤ stirlingIndex y by omega) hv
  have hfull : stirlingTerm y ≤
      (Real.exp 1 * (2 * Real.exp 1 * Real.log 2) ^ d) *
        criticalFactorialTerm (stirlingIndex y - d) := by
    calc
      stirlingTerm y ≤ Real.exp 1 *
          criticalFactorialTerm (stirlingIndex y) := hfirst
      _ ≤ Real.exp 1 *
          ((2 * Real.exp 1 * Real.log 2) ^ d *
            criticalFactorialTerm (stirlingIndex y - d)) := by
        gcongr
      _ = _ := by ring
  calc
    shiftedCriticalConstant d * stirlingTerm y ≤
        shiftedCriticalConstant d *
          ((Real.exp 1 * (2 * Real.exp 1 * Real.log 2) ^ d) *
            criticalFactorialTerm (stirlingIndex y - d)) := by
      exact mul_le_mul_of_nonneg_left hfull
        (shiftedCriticalConstant_pos d).le
    _ = criticalFactorialTerm (stirlingIndex y - d) := by
      unfold shiftedCriticalConstant
      field_simp

/-! ## Selecting the shifted index from `y` -/

theorem two_pow_stirlingIndex_le_log {y : ℝ}
    (hlogy : 0 < Real.log y) (ht : 0 ≤ Real.log (Real.log y)) :
    (2 : ℝ) ^ stirlingIndex y ≤ Real.log y := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hidx := stirlingIndex_cast_le ht
  have hmul : (stirlingIndex y : ℝ) * Real.log 2 ≤
      Real.log (Real.log y) := by
    exact (le_div_iff₀ hlog2).mp hidx
  have hexp := Real.exp_le_exp.mpr hmul
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2),
    Real.exp_log hlogy] at hexp
  exact hexp

theorem stirlingIndex_ge_of_loglog_ge {d : ℕ} {y : ℝ}
    (hlarge : ((d : ℝ) * Real.log 2) ≤ Real.log (Real.log y)) :
    d ≤ stirlingIndex y := by
  unfold stirlingIndex
  apply Nat.le_floor
  apply (le_div_iff₀ (Real.log_pos one_lt_two)).2
  exact hlarge

theorem exists_two_pow_ge (K : ℝ) : ∃ d : ℕ, K ≤ (2 : ℝ) ^ d := by
  have hlim : Tendsto (fun d : ℕ => (2 : ℝ) ^ d) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  have hev : ∀ᶠ d : ℕ in atTop, K ≤ (2 : ℝ) ^ d :=
    hlim.eventually_ge_atTop K
  obtain ⟨d, hd⟩ := Filter.eventually_atTop.1 hev
  exact ⟨d, hd d le_rfl⟩

theorem highCap_endpoint_scale_of_shift
    {start M d y : ℕ}
    (hd : 2 * (primeBlockLogUpperConstant * (M + 6 : ℕ) *
      (2 : ℝ) ^ (start + 1)) ≤ (2 : ℝ) ^ d)
    (hdk : d ≤ stirlingIndex (y : ℝ))
    (hlogy : 0 < Real.log (y : ℝ))
    (ht : 0 ≤ Real.log (Real.log (y : ℝ))) :
    2 * (primeBlockLogUpperConstant * (M + 6 : ℕ) *
        (2 : ℝ) ^ (start + 1) *
          (2 : ℝ) ^ (stirlingIndex (y : ℝ) - d)) ≤
      Real.log (y : ℝ) := by
  calc
    2 * (primeBlockLogUpperConstant * (M + 6 : ℕ) *
        (2 : ℝ) ^ (start + 1) *
          (2 : ℝ) ^ (stirlingIndex (y : ℝ) - d)) =
      (2 * (primeBlockLogUpperConstant * (M + 6 : ℕ) *
        (2 : ℝ) ^ (start + 1))) *
          (2 : ℝ) ^ (stirlingIndex (y : ℝ) - d) := by ring
    _ ≤ (2 : ℝ) ^ d *
          (2 : ℝ) ^ (stirlingIndex (y : ℝ) - d) := by gcongr
    _ = (2 : ℝ) ^ stirlingIndex (y : ℝ) := by
      rw [← pow_add]
      congr 1
      omega
    _ ≤ Real.log (y : ℝ) := two_pow_stirlingIndex_le_log hlogy ht

theorem eventually_nat_loglog_ge (R : ℝ) :
    ∀ᶠ y : ℕ in atTop, R ≤ Real.log (Real.log (y : ℝ)) := by
  have hlim : Tendsto (fun y : ℕ => Real.log (Real.log (y : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  exact hlim.eventually_ge_atTop R

/-- Every concrete profile selection is bounded by the product of the
corresponding block upper endpoints. -/
theorem profileSelectionProduct_le_profileEndpointProduct
    {start blocks : ℕ} {b : ℕ → ℕ} {c : ProfileSelection blocks}
    (hc : c ∈ profileSelections start blocks b) :
    profileSelectionProduct c ≤ profileEndpointProduct start blocks b := by
  classical
  unfold profileSelectionProduct profileEndpointProduct
  calc
    (∏ i ∈ (Finset.range blocks).attach, ∏ p ∈ c i.1 i.2, p) ≤
        ∏ i ∈ (Finset.range blocks).attach,
          primeBlockUpper (start + i.1) ^ b i.1 := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        rw [← profileSelection_card hc i.1 i.2, ← Finset.prod_const]
        apply Finset.prod_le_prod
        · intro p hp
          omega
        · intro p hp
          exact le_primeBlockUpper_of_mem
            (profileSelection_subset_block hc i.1 i.2 hp)
    _ = ∏ i ∈ Finset.range blocks,
          primeBlockUpper (start + i) ^ b i := by
      exact Finset.prod_attach (Finset.range blocks)
        (fun i ↦ primeBlockUpper (start + i) ^ b i)

/-- Profile-family version of the endpoint-product envelope. -/
theorem mem_profileNumberFamily_le_profileEndpointProduct
    {start blocks : ℕ} {b : ℕ → ℕ} {a : ℕ}
    (ha : a ∈ profileNumberFamily start blocks b) :
    a ≤ profileEndpointProduct start blocks b := by
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ha
  exact profileSelectionProduct_le_profileEndpointProduct hc

/-- A pointwise high-end cap on a profile bounds its endpoint product by
the uniform Ford envelope. -/
theorem profileEndpointProduct_le_highCapEndpointProduct
    {start v M : ℕ} {b : ℕ → ℕ}
    (hcap : ∀ j < v, b j ≤ M + (v - j) ^ 2) :
    profileEndpointProduct start v b ≤ highCapEndpointProduct start v M := by
  classical
  unfold profileEndpointProduct highCapEndpointProduct
  apply Finset.prod_le_prod
  · intro j hj
    positivity
  · intro j hj
    exact Nat.pow_le_pow_right
      (lt_of_lt_of_le (by omega : 0 < 2)
        (two_le_primeBlockEndpoint (start + j + 1)))
      (hcap j (Finset.mem_range.mp hj))

theorem exists_goodPotential_of_mem_goodPotentialProfiles
    {v : ℕ} {B : ℚ} {b : Fin v → ℕ}
    (hb : b ∈ goodPotentialProfiles v B) :
    ∃ f : Fin v → Fin v,
      Occupancy.GoodPotential B f ∧ Occupancy.occupancyVector f = b := by
  unfold goodPotentialProfiles Occupancy.occupancyVectors at hb
  obtain ⟨f, hf, hfb⟩ := Finset.mem_image.mp hb
  refine ⟨f, ?_, hfb⟩
  simpa [goodPotentialPlacements] using hf

theorem profilePrimeCount_extend_of_mem_goodPotentialProfiles
    {v : ℕ} {B : ℚ} {b : Fin v → ℕ}
    (hb : b ∈ goodPotentialProfiles v B) :
    profilePrimeCount v (extendOccupancyProfile b) = v := by
  obtain ⟨f, hf, hfb⟩ :=
    exists_goodPotential_of_mem_goodPotentialProfiles hb
  rw [← hfb]
  exact profilePrimeCount_extend_occupancyVector f

theorem admissibleProfile_extend_of_mem_goodPotentialProfiles
    {v : ℕ} {B : ℚ} {b : Fin v → ℕ}
    (hb : b ∈ goodPotentialProfiles v B) :
    AdmissibleProfile 1 v (extendOccupancyProfile b) := by
  obtain ⟨f, hf, hfb⟩ :=
    exists_goodPotential_of_mem_goodPotentialProfiles hb
  rw [← hfb]
  exact admissibleProfile_occupancyProfile hf.1

theorem profilePrefixPotential_extend_le_of_mem_goodPotentialProfiles
    {v : ℕ} {B : ℚ} {b : Fin v → ℕ}
    (hb : b ∈ goodPotentialProfiles v B) :
    profilePrefixPotential v (extendOccupancyProfile b) ≤ 2 * (B : ℝ) := by
  obtain ⟨f, hf, hfb⟩ :=
    exists_goodPotential_of_mem_goodPotentialProfiles hb
  rw [← hfb, ← occupancyProfile_eq_extendOccupancyProfile,
    profilePrefixPotential_occupancyProfile]
  have hpot : (Occupancy.expPotential f : ℝ) ≤ (B : ℝ) := by
    exact_mod_cast hf.2
  gcongr

/-- Once a profile start controls the two summable error majorants, every
later start does too.  This lets the pair estimate and the profile-mass
estimate share one sufficiently late block. -/
theorem ProfileStartControlled.mono {M start start' : ℕ}
    (hcontrol : ProfileStartControlled M start) (hstart : start ≤ start') :
    ProfileStartControlled M start' := by
  have hp : (2 / 3 : ℝ) ^ start' ≤ (2 / 3 : ℝ) ^ start :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hstart
  constructor
  · exact (mul_le_mul_of_nonneg_right hp
      (tsum_nonneg fun i => by positivity)).trans hcontrol.1
  · exact (mul_le_mul_of_nonneg_right hp
      (tsum_nonneg fun i => by positivity)).trans hcontrol.2

/-- A controlled profile start may be required to lie beyond an arbitrary
finite threshold without changing any later constant. -/
theorem exists_profileStartControlled_ge (M threshold : ℕ) :
    ∃ start : ℕ, threshold ≤ start ∧ ProfileStartControlled M start := by
  obtain ⟨start, hstart⟩ := exists_profileStartControlled M
  exact ⟨max threshold start, le_max_left _ _,
    hstart.mono (le_max_right _ _)⟩

/-- The ordered-tuple profile mass is at most the ideal target mass, since
every greedy prime block has reciprocal mass at most `log 2`. -/
theorem profileTupleMass_le_targetProfileMass
    (start blocks : ℕ) (b : ℕ → ℕ) :
    profileTupleMass start blocks b ≤
      (Real.log 2) ^ profilePrimeCount blocks b /
        (profileFactorial blocks b : ℕ) := by
  rw [profileTupleMass]
  rw [show (Real.log 2) ^ profilePrimeCount blocks b /
      (profileFactorial blocks b : ℕ) =
      ∏ i ∈ Finset.range blocks,
        (Real.log 2) ^ b i / (b i).factorial by
    rw [profilePrimeCount, profileFactorial, Finset.prod_div_distrib,
      Finset.prod_pow_eq_pow_sum]
    congr 1
    exact_mod_cast Finset.prod_natCast (Finset.range blocks)
      (fun i => (b i).factorial)]
  apply Finset.prod_le_prod
  · intro i hi
    exact div_nonneg (pow_nonneg (primeBlockMass_nonneg _) _) (by positivity)
  · intro i hi
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (primeBlockMass_nonneg _)
        (primeBlockMass_le_log_two _) _)
      (by positivity)

/-- Any fixed real error constant is killed by moving sufficiently far out
in the double-exponential prime-block scale. -/
theorem exists_dyadic_error_small (C B : ℝ) :
    ∃ start : ℕ,
      C * (2 * B) * (1 / (2 : ℝ) ^ start) ≤ 1 / 16 := by
  have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlim : Tendsto (fun n : ℕ => C * (2 * B) * (1 / 2 : ℝ) ^ n)
      atTop (nhds 0) := by
    simpa using hp.const_mul (C * (2 * B))
  have he := hlim.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16))
  rw [eventually_atTop] at he
  obtain ⟨start, hstart⟩ := he
  refine ⟨start, ?_⟩
  rw [← one_div_pow]
  exact (hstart start le_rfl).le

/-- One common block start simultaneously controls the squarefree profile
mass and kills the universal sharp-pair error. -/
theorem exists_controlled_dyadic_error_small
    (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B) :
    ∃ start : ℕ, ProfileStartControlled 1 start ∧
      C * (2 * B) * (1 / (2 : ℝ) ^ start) ≤ 1 / 16 := by
  obtain ⟨threshold, hthreshold⟩ := exists_dyadic_error_small C B
  obtain ⟨start, hstart, hcontrol⟩ :=
    exists_profileStartControlled_ge 1 threshold
  refine ⟨start, hcontrol, ?_⟩
  have hpow : (1 / (2 : ℝ) ^ start) ≤ 1 / (2 : ℝ) ^ threshold := by
    rw [← one_div_pow, ← one_div_pow]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hstart
  exact (mul_le_mul_of_nonneg_left hpow
    (mul_nonneg hC (mul_nonneg (by norm_num) hB))).trans hthreshold

/-! ## Weighted finite sums -/

/-- The reciprocal-weighted isolated-divisor sum over a finite family. -/
noncomputable def weightedIsolatedSum (A : Finset ℕ) (sigma : ℝ) : ℝ :=
  ∑ a ∈ A, (I a sigma : ℝ) / a

/-- Ford's reciprocal-weighted close-pair defect. -/
noncomputable def weightedDivisorDefect (A : Finset ℕ) (sigma : ℝ) : ℝ :=
  ∑ a ∈ A, ((3 : ℝ) * divisorCount a - 2 * W a sigma) / a

theorem weightedIsolatedSum_nonneg (A : Finset ℕ) (sigma : ℝ) :
    0 ≤ weightedIsolatedSum A sigma := by
  unfold weightedIsolatedSum
  positivity

/-- Distinct finite occupancy vectors give disjoint squarefree-number
families: unique factorization recovers, block by block, the cardinality of
the selected prime set. -/
theorem disjoint_profileNumberFamily_extendOccupancyProfile
    {start v : ℕ} {b c : Fin v → ℕ} (hbc : b ≠ c) :
    Disjoint
      (profileNumberFamily start v (extendOccupancyProfile b))
      (profileNumberFamily start v (extendOccupancyProfile c)) := by
  classical
  rw [Finset.disjoint_left]
  intro a hab hac
  obtain ⟨sb, hsb, hsba⟩ := Finset.mem_image.mp hab
  obtain ⟨sc, hsc, hsca⟩ := Finset.mem_image.mp hac
  have hprod : profileSelectionProduct sb = profileSelectionProduct sc :=
    hsba.trans hsca.symm
  have hprimes : profileSelectionPrimes sb = profileSelectionPrimes sc := by
    rw [← primeFactors_profileSelectionProduct hsb,
      ← primeFactors_profileSelectionProduct hsc, hprod]
  apply hbc
  funext j
  have hj : j.1 ∈ Finset.range v := Finset.mem_range.mpr j.isLt
  calc
    b j = (sb j.1 hj).card := by
      simpa [extendOccupancyProfile, j.isLt] using
        (profileSelection_card hsb j.1 hj).symm
    _ = (sc j.1 hj).card := by
      congr 1
      rw [profileSelection_eq_inter_primes hsb j.1 hj,
        profileSelection_eq_inter_primes hsc j.1 hj, hprimes]
    _ = c j := by
      simpa [extendOccupancyProfile, j.isLt] using
        profileSelection_card hsc j.1 hj

theorem pairwiseDisjoint_goodProfileNumberFamilies
    (start v : ℕ) (B : ℚ) :
    Set.PairwiseDisjoint
      (↑(goodPotentialProfiles v B) : Set (Fin v → ℕ))
      (fun b => profileNumberFamily start v (extendOccupancyProfile b)) := by
  intro b hb c hc hbc
  exact disjoint_profileNumberFamily_extendOccupancyProfile hbc

/-- Every number in the assembled family is squarefree, has all prime
factors in the prescribed consecutive greedy blocks, and has exactly `v`
prime factors. -/
theorem mem_goodProfileNumberFamily_data
    {start v : ℕ} {B : ℚ} {a : ℕ}
    (ha : a ∈ goodProfileNumberFamily start v B) :
    Squarefree a ∧ a.primeFactors ⊆ primeBlockSupport start v ∧
      a.primeFactors.card = v := by
  unfold goodProfileNumberFamily at ha
  obtain ⟨b, hb, ha⟩ := Finset.mem_biUnion.mp ha
  have hdata := mem_profileFamily_data ha
  refine ⟨hdata.1, hdata.2.1, ?_⟩
  rw [hdata.2.2]
  exact profilePrimeCount_extend_of_mem_goodPotentialProfiles hb

theorem divisorCount_of_mem_goodProfileNumberFamily
    {start v : ℕ} {B : ℚ} {a : ℕ}
    (ha : a ∈ goodProfileNumberFamily start v B) :
    divisorCount a = 2 ^ v := by
  rw [divisorCount_eq_two_pow_primeFactors_card_of_squarefree
    (mem_goodProfileNumberFamily_data ha).1,
    (mem_goodProfileNumberFamily_data ha).2.2]

/-- A coarse but explicit size bound for the assembled family.  It is often
convenient when specializing the finite theorem to a parameter `y`; sharper
profile-sensitive endpoint bounds may replace it without changing the
isolated-mass argument. -/
theorem mem_goodProfileNumberFamily_le_endpoint_pow
    {start v : ℕ} {B : ℚ} {a : ℕ}
    (ha : a ∈ goodProfileNumberFamily start v B) :
    a ≤ primeBlockUpper (start + v) ^ v := by
  have hdata := mem_goodProfileNumberFamily_data ha
  rw [← Nat.prod_primeFactors_of_squarefree hdata.1]
  calc
    (∏ p ∈ a.primeFactors, p) ≤
        ∏ _p ∈ a.primeFactors, primeBlockUpper (start + v) := by
      apply Finset.prod_le_prod (fun p hp => Nat.zero_le p)
      intro p hp
      have hsupport := hdata.2.1 hp
      obtain ⟨i, hi, hpblock⟩ := Finset.mem_biUnion.mp hsupport
      exact (le_primeBlockUpper_of_mem hpblock).trans
        (primeBlockEndpoint_mono (by
          have hiv : i < v := Finset.mem_range.mp hi
          omega))
    _ = primeBlockUpper (start + v) ^ v := by
      rw [Finset.prod_const, hdata.2.2]

theorem mem_goodProfileNumberFamily_sq_le
    {start v y : ℕ} {B : ℚ}
    (hsize : (primeBlockUpper (start + v) ^ v) ^ 2 ≤ y)
    {a : ℕ} (ha : a ∈ goodProfileNumberFamily start v B) :
    a ^ 2 ≤ y := by
  exact (Nat.pow_le_pow_left
    (mem_goodProfileNumberFamily_le_endpoint_pow ha) 2).trans hsize

/-- The isolated-divisor mass of the union is the sum of the masses of its
pairwise disjoint profile families. -/
theorem weightedDyadicIsolatedMass_goodProfileNumberFamily
    (start v : ℕ) (B : ℚ) :
    weightedDyadicIsolatedMass (goodProfileNumberFamily start v B) =
      ∑ b ∈ goodPotentialProfiles v B,
        weightedDyadicIsolatedMass
          (profileNumberFamily start v (extendOccupancyProfile b)) := by
  classical
  unfold weightedDyadicIsolatedMass goodProfileNumberFamily
  exact Finset.sum_biUnion
    (pairwiseDisjoint_goodProfileNumberFamilies start v B)

/-- Exact multinomial evaluation of the ideal target mass over all selected
occupancy profiles.  This is the finite form of Ford's simplex-volume
factor `1 / v!`. -/
theorem sum_targetProfileMass_goodPotentialProfiles
    (v : ℕ) (B : ℚ) :
    (∑ b ∈ goodPotentialProfiles v B,
      (Real.log 2) ^ v /
        (profileFactorial v (extendOccupancyProfile b) : ℕ)) =
      (Real.log 2) ^ v *
        ((goodPotentialPlacements v B).card : ℝ) / v.factorial := by
  have hinvariant : Occupancy.OccupancyInvariant
      (goodPotentialPlacements v B) := by
    simpa [goodPotentialPlacements] using
      Occupancy.goodPotential_occupancyInvariant (v := v) B
  have hmulti := Occupancy.sum_inv_profileFactorial_eq_card_div_factorial
    (goodPotentialPlacements v B) hinvariant
  change (∑ b ∈ Occupancy.occupancyVectors (goodPotentialPlacements v B),
      (Real.log 2) ^ v /
        (profileFactorial v (extendOccupancyProfile b) : ℕ)) = _
  calc
    (∑ b ∈ Occupancy.occupancyVectors (goodPotentialPlacements v B),
      (Real.log 2) ^ v /
        (profileFactorial v (extendOccupancyProfile b) : ℕ)) =
        (Real.log 2) ^ v *
          (∑ b ∈ Occupancy.occupancyVectors (goodPotentialPlacements v B),
            (1 : ℝ) / ∏ j, ((b j).factorial : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [profileFactorial_extendOccupancyProfile]
      push_cast
      ring
    _ = (Real.log 2) ^ v *
        ((goodPotentialPlacements v B).card : ℝ) / v.factorial := by
      rw [hmulti]
      ring

/-! ## Arbitrary occupancy-invariant subfamilies

The size truncation used in Ford's `Y` region is an occupancy-invariant
subfamily of the bounded-potential placements.  The following definitions
and identities let the sharp profile argument be reused without paying for
the discarded profiles. -/

/-- Occupancy vectors represented by an arbitrary finite placement family. -/
noncomputable def placementProfiles {v : ℕ}
    (P : Finset (Fin v → Fin v)) : Finset (Fin v → ℕ) :=
  Occupancy.occupancyVectors P

/-- The arithmetic family associated to an arbitrary finite placement
family, after quotienting by its occupancy vectors. -/
noncomputable def placementProfileNumberFamily {v : ℕ}
    (start : ℕ) (P : Finset (Fin v → Fin v)) : Finset ℕ :=
  (placementProfiles P).biUnion fun b ↦
    profileNumberFamily start v (extendOccupancyProfile b)

theorem exists_mem_of_mem_placementProfiles
    {v : ℕ} {P : Finset (Fin v → Fin v)} {b : Fin v → ℕ}
    (hb : b ∈ placementProfiles P) :
    ∃ f ∈ P, Occupancy.occupancyVector f = b := by
  exact Finset.mem_image.mp hb

/-- A pointwise block-occupancy cap on a placement family bounds every
number represented by that family by the common endpoint envelope. -/
theorem mem_placementProfileNumberFamily_le_highCapEndpointProduct
    {start v M : ℕ} {P : Finset (Fin v → Fin v)}
    (hcap : ∀ f ∈ P, ∀ j : Fin v,
      Occupancy.boxOccupancy f j ≤ M + (v - j.val) ^ 2)
    {a : ℕ} (ha : a ∈ placementProfileNumberFamily start P) :
    a ≤ highCapEndpointProduct start v M := by
  unfold placementProfileNumberFamily at ha
  obtain ⟨b, hb, hab⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨f, hfP, hfb⟩ := exists_mem_of_mem_placementProfiles hb
  apply (mem_profileNumberFamily_le_profileEndpointProduct hab).trans
  apply profileEndpointProduct_le_highCapEndpointProduct
  intro j hj
  rw [extendOccupancyProfile_of_lt b hj]
  rw [← hfb]
  exact hcap f hfP ⟨j, hj⟩

theorem placementProfiles_subset_goodPotentialProfiles
    {v : ℕ} {P : Finset (Fin v → Fin v)} {B : ℚ}
    (hgood : ∀ f ∈ P, Occupancy.GoodPotential B f) :
    placementProfiles P ⊆ goodPotentialProfiles v B := by
  intro b hb
  obtain ⟨f, hfP, rfl⟩ := exists_mem_of_mem_placementProfiles hb
  unfold goodPotentialProfiles Occupancy.occupancyVectors
  apply Finset.mem_image.mpr
  refine ⟨f, ?_, rfl⟩
  simpa [goodPotentialPlacements] using hgood f hfP

theorem placementProfileNumberFamily_subset_goodProfileNumberFamily
    {start v : ℕ} {P : Finset (Fin v → Fin v)} {B : ℚ}
    (hgood : ∀ f ∈ P, Occupancy.GoodPotential B f) :
    placementProfileNumberFamily start P ⊆
      goodProfileNumberFamily start v B := by
  intro a ha
  unfold placementProfileNumberFamily at ha
  unfold goodProfileNumberFamily
  obtain ⟨b, hb, hab⟩ := Finset.mem_biUnion.mp ha
  exact Finset.mem_biUnion.mpr
    ⟨b, placementProfiles_subset_goodPotentialProfiles hgood hb, hab⟩

theorem mem_placementProfileNumberFamily_data
    {start v : ℕ} {P : Finset (Fin v → Fin v)} {B : ℚ}
    (hgood : ∀ f ∈ P, Occupancy.GoodPotential B f)
    {a : ℕ} (ha : a ∈ placementProfileNumberFamily start P) :
    Squarefree a ∧ a.primeFactors ⊆ primeBlockSupport start v ∧
      a.primeFactors.card = v := by
  exact mem_goodProfileNumberFamily_data
    (placementProfileNumberFamily_subset_goodProfileNumberFamily hgood ha)

theorem pairwiseDisjoint_placementProfileNumberFamilies
    {v : ℕ} (start : ℕ) (P : Finset (Fin v → Fin v)) :
    Set.PairwiseDisjoint
      (↑(placementProfiles P) : Set (Fin v → ℕ))
      (fun b ↦ profileNumberFamily start v (extendOccupancyProfile b)) := by
  intro b hb c hc hbc
  exact disjoint_profileNumberFamily_extendOccupancyProfile hbc

theorem weightedDyadicIsolatedMass_placementProfileNumberFamily
    {v : ℕ} (start : ℕ) (P : Finset (Fin v → Fin v)) :
    weightedDyadicIsolatedMass (placementProfileNumberFamily start P) =
      ∑ b ∈ placementProfiles P,
        weightedDyadicIsolatedMass
          (profileNumberFamily start v (extendOccupancyProfile b)) := by
  classical
  unfold weightedDyadicIsolatedMass placementProfileNumberFamily
  exact Finset.sum_biUnion
    (pairwiseDisjoint_placementProfileNumberFamilies start P)

theorem sum_targetProfileMass_placementProfiles
    {v : ℕ} (P : Finset (Fin v → Fin v))
    (hinvariant : Occupancy.OccupancyInvariant P) :
    (∑ b ∈ placementProfiles P,
      (Real.log 2) ^ v /
        (profileFactorial v (extendOccupancyProfile b) : ℕ)) =
      (Real.log 2) ^ v * (P.card : ℝ) / v.factorial := by
  have hmulti :=
    Occupancy.sum_inv_profileFactorial_eq_card_div_factorial P hinvariant
  change (∑ b ∈ Occupancy.occupancyVectors P,
      (Real.log 2) ^ v /
        (profileFactorial v (extendOccupancyProfile b) : ℕ)) = _
  calc
    (∑ b ∈ Occupancy.occupancyVectors P,
      (Real.log 2) ^ v /
        (profileFactorial v (extendOccupancyProfile b) : ℕ)) =
        (Real.log 2) ^ v *
          (∑ b ∈ Occupancy.occupancyVectors P,
            (1 : ℝ) / ∏ j, ((b j).factorial : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [profileFactorial_extendOccupancyProfile]
      push_cast
      ring
    _ = (Real.log 2) ^ v * (P.card : ℝ) / v.factorial := by
      rw [hmulti]
      ring

/-! ## Ford's Lemma 4.5 at `g = 1` -/

/-- The `g = 1` specialization of Ford's Lemma 4.5.  We state the
subtraction in `ℝ`, so the result remains meaningful when the defect is
negative. -/
theorem ford_lemma_four_five_one {a : ℕ} {sigma : ℝ}
    (hsigma : 0 < sigma) :
    ((3 : ℝ) * divisorCount a - 2 * W a sigma) / 2 ≤ I a sigma := by
  have h := two_mul_divisorCount_sub_W_le_I_int (a := a) hsigma
  have hR :
      (2 : ℝ) * divisorCount a - W a sigma ≤ I a sigma := by
    exact_mod_cast h
  have htau : (0 : ℝ) ≤ divisorCount a := by positivity
  linarith

/-- Summed and reciprocal-weighted form of the `g = 1` Lemma 4.5. -/
theorem ford_lemma_four_five_weighted (A : Finset ℕ) {sigma : ℝ}
    (hsigma : 0 < sigma) :
    weightedDivisorDefect A sigma / 2 ≤ weightedIsolatedSum A sigma := by
  classical
  unfold weightedDivisorDefect weightedIsolatedSum
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro a ha
  by_cases ha0 : a = 0
  · subst a
    simp
  · have haR : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero ha0
    rw [div_div]
    have h := div_le_div_of_nonneg_right
      (ford_lemma_four_five_one (a := a) hsigma) haR.le
    convert h using 1 <;> ring

/-- Dyadic form of the weighted close-pair defect inequality. -/
theorem ford_lemma_four_five_dyadic (A : Finset ℕ) :
    weightedDivisorDefect A dyadicSigma / 2 ≤
      weightedIsolatedSum A dyadicSigma :=
  ford_lemma_four_five_weighted A dyadicSigma_pos

@[simp]
theorem weightedIsolatedSum_dyadic_eq (A : Finset ℕ) :
    weightedIsolatedSum A dyadicSigma = weightedDyadicIsolatedMass A := by
  rfl

/-- The reciprocal divisor mass of a family with constant divisor count. -/
theorem weightedDivisorMass_eq_const_mul
    (A : Finset ℕ) (tau : ℕ)
    (htau : ∀ a ∈ A, divisorCount a = tau) :
    weightedDivisorMass A =
      (tau : ℝ) * reciprocalFamilyMass A := by
  unfold weightedDivisorMass reciprocalFamilyMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [htau a ha]
  ring

/-- Algebraic assembly of Ford's Lemma 4.5.  A sharp pair estimate with
error at most one quarter of the diagonal mass leaves three quarters of
that diagonal mass as isolated-divisor mass. -/
theorem three_quarters_diagonal_le_weightedDyadicIsolatedMass
    (A : Finset ℕ) (tau : ℕ) (mass error : ℝ)
    (htau : ∀ a ∈ A, divisorCount a = tau)
    (hmass : reciprocalFamilyMass A = mass)
    (hpair : weightedDyadicPairMass A ≤ (tau : ℝ) * mass + error)
    (herror : error ≤ (1 / 4 : ℝ) * (tau : ℝ) * mass) :
    (3 / 4 : ℝ) * (tau : ℝ) * mass ≤
      weightedDyadicIsolatedMass A := by
  have hdiv := weightedDivisorMass_eq_const_mul A tau htau
  rw [hmass] at hdiv
  have hiso := two_mul_weightedDivisorMass_sub_pair_le_isolated A
  rw [hdiv] at hiso
  linarith

/-! ## Sharp per-profile assembly -/

/-- Ford's Lemmas 4.5, 4.7, and the profile-mass estimate assembled for one
bounded-potential occupancy profile.  The only parameter is the universal
constant in the sharp pair estimate; moving the block start far enough
makes its contribution at most one sixteenth of the ideal target mass. -/
theorem three_sixteenths_target_le_profile_isolatedMass_of_sharp
    (C : ℝ) (hC : 0 ≤ C)
    (hsharp : ∀ (start blocks : ℕ) (b : ℕ → ℕ),
      weightedDyadicPairMass (profileNumberFamily start blocks b) ≤
        (2 : ℝ) ^ profilePrimeCount blocks b * profileMass start blocks b +
        C * (2 : ℝ) ^ profilePrimeCount blocks b *
          profileTupleMass start blocks b * (1 / (2 : ℝ) ^ start) *
            profilePrefixPotential blocks b)
    {start v : ℕ} {B : ℚ} (hB : 0 ≤ B) {b : Fin v → ℕ}
    (hb : b ∈ goodPotentialProfiles v B)
    (hcontrol : ProfileStartControlled 1 start)
    (hscale : C * (2 * (B : ℝ)) * (1 / (2 : ℝ) ^ start) ≤ 1 / 16) :
    (3 / 16 : ℝ) * (2 : ℝ) ^ v *
        ((Real.log 2) ^ v /
          (profileFactorial v (extendOccupancyProfile b) : ℕ)) ≤
      weightedDyadicIsolatedMass
        (profileNumberFamily start v (extendOccupancyProfile b)) := by
  let p := extendOccupancyProfile b
  let T : ℝ := (Real.log 2) ^ v / (profileFactorial v p : ℕ)
  let mass : ℝ := profileMass start v p
  let error : ℝ := C * (2 : ℝ) ^ v * profileTupleMass start v p *
    (1 / (2 : ℝ) ^ start) * profilePrefixPotential v p
  have hpcount : profilePrimeCount v p = v := by
    exact profilePrimeCount_extend_of_mem_goodPotentialProfiles hb
  have hadmiss : AdmissibleProfile 1 v p :=
    admissibleProfile_extend_of_mem_goodPotentialProfiles hb
  have hmass : (1 / 4 : ℝ) * T ≤ mass := by
    simpa only [T, mass, hpcount] using
      admissible_quarter_targetProfileMass_le_profileMass
        hcontrol hadmiss
  have htuple : profileTupleMass start v p ≤ T := by
    simpa only [T, hpcount] using
      profileTupleMass_le_targetProfileMass start v p
  have hpot : profilePrefixPotential v p ≤ 2 * (B : ℝ) :=
    profilePrefixPotential_extend_le_of_mem_goodPotentialProfiles hb
  have hT : 0 ≤ T := by
    dsimp [T]
    positivity
  have htau : 0 ≤ (2 : ℝ) ^ v := by positivity
  have htuple0 : 0 ≤ profileTupleMass start v p :=
    profileTupleMass_nonneg start v p
  have hpot0 : 0 ≤ profilePrefixPotential v p :=
    profilePrefixPotential_nonneg v p
  have herror : error ≤
      (1 / 4 : ℝ) * (2 : ℝ) ^ v * mass := by
    calc
      error ≤ C * (2 : ℝ) ^ v * profileTupleMass start v p *
          (1 / (2 : ℝ) ^ start) * (2 * (B : ℝ)) := by
        dsimp [error]
        gcongr
      _ ≤ C * (2 : ℝ) ^ v * T *
          (1 / (2 : ℝ) ^ start) * (2 * (B : ℝ)) := by
        gcongr
      _ = (2 : ℝ) ^ v * T *
          (C * (2 * (B : ℝ)) * (1 / (2 : ℝ) ^ start)) := by ring
      _ ≤ (2 : ℝ) ^ v * T * (1 / 16 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hscale (mul_nonneg htau hT)
      _ = (1 / 4 : ℝ) * (2 : ℝ) ^ v * ((1 / 4 : ℝ) * T) := by ring
      _ ≤ (1 / 4 : ℝ) * (2 : ℝ) ^ v * mass := by gcongr
  have hpair : weightedDyadicPairMass (profileNumberFamily start v p) ≤
      (2 : ℝ) ^ v * mass + error := by
    simpa only [hpcount] using hsharp start v p
  have hconst : ∀ a ∈ profileNumberFamily start v p,
      divisorCount a = 2 ^ v := by
    intro a ha
    simpa only [hpcount] using divisorCount_of_mem_profileNumberFamily ha
  have hisolated : (3 / 4 : ℝ) * (2 : ℝ) ^ v * mass ≤
      weightedDyadicIsolatedMass (profileNumberFamily start v p) := by
    have hcast : ((2 ^ v : ℕ) : ℝ) = (2 : ℝ) ^ v := by norm_num
    have hpair' : weightedDyadicPairMass (profileNumberFamily start v p) ≤
        ((2 ^ v : ℕ) : ℝ) * mass + error := by
      rw [hcast]
      exact hpair
    have hmain := three_quarters_diagonal_le_weightedDyadicIsolatedMass
      (profileNumberFamily start v p) (2 ^ v) mass error hconst
      (reciprocalFamilyMass_profileNumberFamily start v p) hpair'
      (by simpa using herror)
    simpa only [hcast] using hmain
  calc
    (3 / 16 : ℝ) * (2 : ℝ) ^ v *
        ((Real.log 2) ^ v /
          (profileFactorial v (extendOccupancyProfile b) : ℕ)) =
        (3 / 4 : ℝ) * (2 : ℝ) ^ v * ((1 / 4 : ℝ) * T) := by
      simp only [T, p]
      ring
    _ ≤ (3 / 4 : ℝ) * (2 : ℝ) ^ v * mass := by gcongr
    _ ≤ weightedDyadicIsolatedMass
        (profileNumberFamily start v (extendOccupancyProfile b)) := by
      simpa only [p] using hisolated

/-- Summed form of the preceding per-profile theorem.  The multinomial
fiber identity evaluates the whole ideal mass without losing an
exponential factor. -/
theorem three_sixteenths_targetDensity_le_goodProfile_isolatedMass_of_sharp
    (C : ℝ) (hC : 0 ≤ C)
    (hsharp : ∀ (start blocks : ℕ) (b : ℕ → ℕ),
      weightedDyadicPairMass (profileNumberFamily start blocks b) ≤
        (2 : ℝ) ^ profilePrimeCount blocks b * profileMass start blocks b +
        C * (2 : ℝ) ^ profilePrimeCount blocks b *
          profileTupleMass start blocks b * (1 / (2 : ℝ) ^ start) *
            profilePrefixPotential blocks b)
    {start v : ℕ} {B : ℚ} (hB : 0 ≤ B)
    (hcontrol : ProfileStartControlled 1 start)
    (hscale : C * (2 * (B : ℝ)) * (1 / (2 : ℝ) ^ start) ≤ 1 / 16) :
    (3 / 16 : ℝ) * (2 : ℝ) ^ v *
        ((Real.log 2) ^ v *
          ((goodPotentialPlacements v B).card : ℝ) / v.factorial) ≤
      weightedDyadicIsolatedMass (goodProfileNumberFamily start v B) := by
  rw [weightedDyadicIsolatedMass_goodProfileNumberFamily]
  calc
    (3 / 16 : ℝ) * (2 : ℝ) ^ v *
        ((Real.log 2) ^ v *
          ((goodPotentialPlacements v B).card : ℝ) / v.factorial) =
        ∑ b ∈ goodPotentialProfiles v B,
          (3 / 16 : ℝ) * (2 : ℝ) ^ v *
            ((Real.log 2) ^ v /
              (profileFactorial v (extendOccupancyProfile b) : ℕ)) := by
      rw [← sum_targetProfileMass_goodPotentialProfiles]
      rw [Finset.mul_sum]
    _ ≤ ∑ b ∈ goodPotentialProfiles v B,
        weightedDyadicIsolatedMass
          (profileNumberFamily start v (extendOccupancyProfile b)) := by
      apply Finset.sum_le_sum
      intro b hb
      exact three_sixteenths_target_le_profile_isolatedMass_of_sharp
        C hC hsharp hB hb hcontrol hscale

/-- The same sharp aggregation over an arbitrary occupancy-invariant
subfamily of the bounded-potential placements.  This is the form used after
Ford's high-end size truncation. -/
theorem three_sixteenths_targetDensity_le_placementProfile_isolatedMass_of_sharp
    (C : ℝ) (hC : 0 ≤ C)
    (hsharp : ∀ (start blocks : ℕ) (b : ℕ → ℕ),
      weightedDyadicPairMass (profileNumberFamily start blocks b) ≤
        (2 : ℝ) ^ profilePrimeCount blocks b * profileMass start blocks b +
        C * (2 : ℝ) ^ profilePrimeCount blocks b *
          profileTupleMass start blocks b * (1 / (2 : ℝ) ^ start) *
            profilePrefixPotential blocks b)
    {start v : ℕ} {B : ℚ} (hB : 0 ≤ B)
    (P : Finset (Fin v → Fin v))
    (hinvariant : Occupancy.OccupancyInvariant P)
    (hgood : ∀ f ∈ P, Occupancy.GoodPotential B f)
    (hcontrol : ProfileStartControlled 1 start)
    (hscale : C * (2 * (B : ℝ)) * (1 / (2 : ℝ) ^ start) ≤ 1 / 16) :
    (3 / 16 : ℝ) * (2 : ℝ) ^ v *
        ((Real.log 2) ^ v * (P.card : ℝ) / v.factorial) ≤
      weightedDyadicIsolatedMass (placementProfileNumberFamily start P) := by
  rw [weightedDyadicIsolatedMass_placementProfileNumberFamily]
  calc
    (3 / 16 : ℝ) * (2 : ℝ) ^ v *
        ((Real.log 2) ^ v * (P.card : ℝ) / v.factorial) =
        ∑ b ∈ placementProfiles P,
          (3 / 16 : ℝ) * (2 : ℝ) ^ v *
            ((Real.log 2) ^ v /
              (profileFactorial v (extendOccupancyProfile b) : ℕ)) := by
      rw [← sum_targetProfileMass_placementProfiles P hinvariant]
      rw [Finset.mul_sum]
    _ ≤ ∑ b ∈ placementProfiles P,
        weightedDyadicIsolatedMass
          (profileNumberFamily start v (extendOccupancyProfile b)) := by
      apply Finset.sum_le_sum
      intro b hb
      exact three_sixteenths_target_le_profile_isolatedMass_of_sharp
        C hC hsharp hB
          (placementProfiles_subset_goodPotentialProfiles hgood hb)
          hcontrol hscale

/-- Factorial-scale consequence for an arbitrary retained placement
subfamily. -/
theorem countConstant_mul_critical_factorial_le_placementProfile_of_sharp
    (C : ℝ) (hC : 0 ≤ C)
    (hsharp : ∀ (start blocks : ℕ) (b : ℕ → ℕ),
      weightedDyadicPairMass (profileNumberFamily start blocks b) ≤
        (2 : ℝ) ^ profilePrimeCount blocks b * profileMass start blocks b +
        C * (2 : ℝ) ^ profilePrimeCount blocks b *
          profileTupleMass start blocks b * (1 / (2 : ℝ) ^ start) *
            profilePrefixPotential blocks b)
    {start v : ℕ} (hv : 1 ≤ v) {B c : ℚ} (hB : 0 ≤ B) (hc : 0 ≤ c)
    (P : Finset (Fin v → Fin v))
    (hinvariant : Occupancy.OccupancyInvariant P)
    (hgood : ∀ f ∈ P, Occupancy.GoodPotential B f)
    (hcount : c * (v : ℚ) ^ v ≤ (v : ℚ) * (P.card : ℚ))
    (hcontrol : ProfileStartControlled 1 start)
    (hscale : C * (2 * (B : ℝ)) * (1 / (2 : ℝ) ^ start) ≤ 1 / 16) :
    (3 / 16 : ℝ) * (c : ℝ) *
        (2 * (v : ℝ) * Real.log 2) ^ v / (v + 1).factorial ≤
      weightedDyadicIsolatedMass (placementProfileNumberFamily start P) := by
  have hcountR : (c : ℝ) * (v : ℝ) ^ v ≤
      (v : ℝ) * (P.card : ℝ) := by
    have hcast : (((c * (v : ℚ) ^ v : ℚ)) : ℝ) ≤
        (((v : ℚ) * (P.card : ℚ) : ℚ) : ℝ) := Rat.cast_le.mpr hcount
    push_cast at hcast
    simpa using hcast
  have hcard : (c : ℝ) * (v : ℝ) ^ v / (v + 1 : ℕ) ≤
      (P.card : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (v + 1 : ℕ))).2
    calc
      (c : ℝ) * (v : ℝ) ^ v ≤ (v : ℝ) * (P.card : ℝ) := hcountR
      _ ≤ (v + 1 : ℕ) * (P.card : ℝ) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ v)
          (by positivity)
      _ = (P.card : ℝ) * (v + 1 : ℕ) := by ring
  have haggregate :=
    three_sixteenths_targetDensity_le_placementProfile_isolatedMass_of_sharp
      C hC hsharp hB P hinvariant hgood hcontrol hscale
  calc
    (3 / 16 : ℝ) * (c : ℝ) *
        (2 * (v : ℝ) * Real.log 2) ^ v / (v + 1).factorial =
        (3 / 16 : ℝ) * (2 : ℝ) ^ v * (Real.log 2) ^ v *
          ((c : ℝ) * (v : ℝ) ^ v / (v + 1 : ℕ)) /
            v.factorial := by
      rw [Nat.factorial_succ, mul_pow, mul_pow]
      push_cast
      field_simp
    _ ≤ (3 / 16 : ℝ) * (2 : ℝ) ^ v * (Real.log 2) ^ v *
          (P.card : ℝ) / v.factorial := by gcongr
    _ = (3 / 16 : ℝ) * (2 : ℝ) ^ v *
        ((Real.log 2) ^ v * (P.card : ℝ) / v.factorial) := by ring
    _ ≤ weightedDyadicIsolatedMass
        (placementProfileNumberFamily start P) := haggregate

/-- Version of the critical factorial bound retaining the positive density
constant delivered by the occupancy theorem. -/
theorem countConstant_mul_critical_factorial_le_isolatedMass_of_sharp
    (C : ℝ) (hC : 0 ≤ C)
    (hsharp : ∀ (start blocks : ℕ) (b : ℕ → ℕ),
      weightedDyadicPairMass (profileNumberFamily start blocks b) ≤
        (2 : ℝ) ^ profilePrimeCount blocks b * profileMass start blocks b +
        C * (2 : ℝ) ^ profilePrimeCount blocks b *
          profileTupleMass start blocks b * (1 / (2 : ℝ) ^ start) *
            profilePrefixPotential blocks b)
    {start v : ℕ} (hv : 1 ≤ v) {B c : ℚ} (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hcount : c * (v : ℚ) ^ v ≤
      (v : ℚ) * ((goodPotentialPlacements v B).card : ℚ))
    (hcontrol : ProfileStartControlled 1 start)
    (hscale : C * (2 * (B : ℝ)) * (1 / (2 : ℝ) ^ start) ≤ 1 / 16) :
    (3 / 16 : ℝ) * (c : ℝ) *
        (2 * (v : ℝ) * Real.log 2) ^ v / (v + 1).factorial ≤
      weightedDyadicIsolatedMass (goodProfileNumberFamily start v B) := by
  have hcountR : (c : ℝ) * (v : ℝ) ^ v ≤
      (v : ℝ) * ((goodPotentialPlacements v B).card : ℝ) := by
    have hcast : (((c * (v : ℚ) ^ v : ℚ)) : ℝ) ≤
        (((v : ℚ) * ((goodPotentialPlacements v B).card : ℚ) : ℚ) : ℝ) :=
      Rat.cast_le.mpr hcount
    push_cast at hcast
    simpa using hcast
  have hcard : (c : ℝ) * (v : ℝ) ^ v / (v + 1 : ℕ) ≤
      ((goodPotentialPlacements v B).card : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (v + 1 : ℕ))).2
    calc
      (c : ℝ) * (v : ℝ) ^ v ≤
          (v : ℝ) * ((goodPotentialPlacements v B).card : ℝ) := hcountR
      _ ≤ (v + 1 : ℕ) *
          ((goodPotentialPlacements v B).card : ℝ) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ v)
          (by positivity)
      _ = ((goodPotentialPlacements v B).card : ℝ) * (v + 1 : ℕ) := by ring
  have haggregate :=
    three_sixteenths_targetDensity_le_goodProfile_isolatedMass_of_sharp
      C hC hsharp (start := start) (v := v) (B := B)
        hB hcontrol hscale
  calc
    (3 / 16 : ℝ) * (c : ℝ) *
        (2 * (v : ℝ) * Real.log 2) ^ v / (v + 1).factorial =
        (3 / 16 : ℝ) * (2 : ℝ) ^ v * (Real.log 2) ^ v *
          ((c : ℝ) * (v : ℝ) ^ v / (v + 1 : ℕ)) /
            v.factorial := by
      rw [Nat.factorial_succ, mul_pow, mul_pow]
      push_cast
      field_simp
    _ ≤ (3 / 16 : ℝ) * (2 : ℝ) ^ v * (Real.log 2) ^ v *
          ((goodPotentialPlacements v B).card : ℝ) / v.factorial := by
      gcongr
    _ = (3 / 16 : ℝ) * (2 : ℝ) ^ v *
        ((Real.log 2) ^ v *
          ((goodPotentialPlacements v B).card : ℝ) / v.factorial) := by ring
    _ ≤ weightedDyadicIsolatedMass
        (goodProfileNumberFamily start v B) := haggregate

/-- The factorial-scale critical lower bound obtained from the selected
placement count.  The factor `(v+1)!` is Ford's Lemma 4.9 scale. -/
theorem critical_factorial_le_goodProfile_isolatedMass_of_sharp
    (C : ℝ) (hC : 0 ≤ C)
    (hsharp : ∀ (start blocks : ℕ) (b : ℕ → ℕ),
      weightedDyadicPairMass (profileNumberFamily start blocks b) ≤
        (2 : ℝ) ^ profilePrimeCount blocks b * profileMass start blocks b +
        C * (2 : ℝ) ^ profilePrimeCount blocks b *
          profileTupleMass start blocks b * (1 / (2 : ℝ) ^ start) *
            profilePrefixPotential blocks b)
    {start v : ℕ} (hv : 1 ≤ v) {B : ℚ} (hB : 0 ≤ B)
    (hcount : (1 / 2 : ℚ) * (v : ℚ) ^ v ≤
      (v : ℚ) * ((goodPotentialPlacements v B).card : ℚ))
    (hcontrol : ProfileStartControlled 1 start)
    (hscale : C * (2 * (B : ℝ)) * (1 / (2 : ℝ) ^ start) ≤ 1 / 16) :
    (3 / 32 : ℝ) *
        (2 * (v : ℝ) * Real.log 2) ^ v / (v + 1).factorial ≤
      weightedDyadicIsolatedMass (goodProfileNumberFamily start v B) := by
  have hcountR : (1 / 2 : ℝ) * (v : ℝ) ^ v ≤
      (v : ℝ) * ((goodPotentialPlacements v B).card : ℝ) := by
    have hc : (((1 / 2 : ℚ) * (v : ℚ) ^ v : ℚ) : ℝ) ≤
        (((v : ℚ) * ((goodPotentialPlacements v B).card : ℚ) : ℚ) : ℝ) :=
      Rat.cast_le.mpr hcount
    push_cast at hc
    simpa using hc
  have hcard : (1 / 2 : ℝ) * (v : ℝ) ^ v / (v + 1 : ℕ) ≤
      ((goodPotentialPlacements v B).card : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (v + 1 : ℕ))).2
    calc
      (1 / 2 : ℝ) * (v : ℝ) ^ v ≤
          (v : ℝ) * ((goodPotentialPlacements v B).card : ℝ) := hcountR
      _ ≤ (v + 1 : ℕ) *
          ((goodPotentialPlacements v B).card : ℝ) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ v)
          (by positivity)
      _ = ((goodPotentialPlacements v B).card : ℝ) * (v + 1 : ℕ) := by ring
  have haggregate :=
    three_sixteenths_targetDensity_le_goodProfile_isolatedMass_of_sharp
      C hC hsharp (start := start) (v := v) (B := B)
        hB hcontrol hscale
  calc
    (3 / 32 : ℝ) *
        (2 * (v : ℝ) * Real.log 2) ^ v / (v + 1).factorial =
        (3 / 16 : ℝ) * (2 : ℝ) ^ v * (Real.log 2) ^ v *
          ((1 / 2 : ℝ) * (v : ℝ) ^ v / (v + 1 : ℕ)) /
            v.factorial := by
      rw [Nat.factorial_succ, mul_pow, mul_pow]
      push_cast
      field_simp
      ring
    _ ≤ (3 / 16 : ℝ) * (2 : ℝ) ^ v * (Real.log 2) ^ v *
          ((goodPotentialPlacements v B).card : ℝ) / v.factorial := by
      gcongr
    _ = (3 / 16 : ℝ) * (2 : ℝ) ^ v *
        ((Real.log 2) ^ v *
          ((goodPotentialPlacements v B).card : ℝ) / v.factorial) := by ring
    _ ≤ weightedDyadicIsolatedMass
        (goodProfileNumberFamily start v B) := haggregate

/-- Uniform finite-`v` assembly from the two independently proved analytic
inputs.  This helper is deliberately suffixed `_of_sharp_count`; the public
theorem below instantiates both inputs and has no hypotheses standing in for
the analytic work. -/
theorem exists_uniform_finite_weighted_isolated_family_of_sharp_count
    (hsharpExists : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (start blocks : ℕ) (b : ℕ → ℕ),
        weightedDyadicPairMass (profileNumberFamily start blocks b) ≤
          (2 : ℝ) ^ profilePrimeCount blocks b * profileMass start blocks b +
          C * (2 : ℝ) ^ profilePrimeCount blocks b *
            profileTupleMass start blocks b * (1 / (2 : ℝ) ^ start) *
              profilePrefixPotential blocks b)
    (B : ℚ) (hB : 0 < B)
    (hcount : ∀ v : ℕ, 1 ≤ v →
      (1 / 2 : ℚ) * (v : ℚ) ^ v ≤
        (v : ℚ) * ((goodPotentialPlacements v B).card : ℚ)) :
    ∃ start : ℕ, ProfileStartControlled 1 start ∧
      ∀ v : ℕ, 1 ≤ v →
        (∀ a ∈ goodProfileNumberFamily start v B,
          Squarefree a ∧ a.primeFactors ⊆ primeBlockSupport start v ∧
            a.primeFactors.card = v) ∧
        (3 / 32 : ℝ) *
            (2 * (v : ℝ) * Real.log 2) ^ v / (v + 1).factorial ≤
          weightedIsolatedSum
            (goodProfileNumberFamily start v B) dyadicSigma := by
  obtain ⟨C, hC, hsharp⟩ := hsharpExists
  have hBR : (0 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB.le
  obtain ⟨start, hcontrol, hscale⟩ :=
    exists_controlled_dyadic_error_small C (B : ℝ) hC hBR
  refine ⟨start, hcontrol, fun v hv => ⟨?_, ?_⟩⟩
  · intro a ha
    exact mem_goodProfileNumberFamily_data ha
  · rw [weightedIsolatedSum_dyadic_eq]
    exact critical_factorial_le_goodProfile_isolatedMass_of_sharp
      C hC hsharp hv hB.le (hcount v hv) hcontrol hscale

/-- Existential-density form matching the public occupancy API. -/
theorem exists_uniform_finite_weighted_isolated_family_of_analytic_inputs
    (hsharpExists : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (start blocks : ℕ) (b : ℕ → ℕ),
        weightedDyadicPairMass (profileNumberFamily start blocks b) ≤
          (2 : ℝ) ^ profilePrimeCount blocks b * profileMass start blocks b +
          C * (2 : ℝ) ^ profilePrimeCount blocks b *
            profileTupleMass start blocks b * (1 / (2 : ℝ) ^ start) *
              profilePrefixPotential blocks b)
    (hcountExists : ∃ B c : ℚ, 0 < B ∧ 0 < c ∧
      ∀ v : ℕ, 1 ≤ v →
        c * (v : ℚ) ^ v ≤
          (v : ℚ) *
            ((Finset.univ.filter (@Occupancy.GoodPotential v B)).card : ℚ)) :
    ∃ B c : ℚ, ∃ start : ℕ,
      0 < B ∧ 0 < c ∧ ProfileStartControlled 1 start ∧
      ∀ v : ℕ, 1 ≤ v →
        (∀ a ∈ goodProfileNumberFamily start v B,
          Squarefree a ∧ a.primeFactors ⊆ primeBlockSupport start v ∧
            a.primeFactors.card = v) ∧
        (3 / 16 : ℝ) * (c : ℝ) *
            (2 * (v : ℝ) * Real.log 2) ^ v / (v + 1).factorial ≤
          weightedIsolatedSum
            (goodProfileNumberFamily start v B) dyadicSigma := by
  obtain ⟨C, hC, hsharp⟩ := hsharpExists
  obtain ⟨B, c, hB, hc, hcount⟩ := hcountExists
  have hBR : (0 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB.le
  obtain ⟨start, hcontrol, hscale⟩ :=
    exists_controlled_dyadic_error_small C (B : ℝ) hC hBR
  refine ⟨B, c, start, hB, hc, hcontrol, fun v hv => ⟨?_, ?_⟩⟩
  · intro a ha
    exact mem_goodProfileNumberFamily_data ha
  · rw [weightedIsolatedSum_dyadic_eq]
    apply countConstant_mul_critical_factorial_le_isolatedMass_of_sharp
      C hC hsharp hv hB.le hc.le _ hcontrol hscale
    simpa [goodPotentialPlacements] using hcount v hv

/-- The final passage from a fixed-fraction, high-end-capped placement
package to the eventual `y`-indexed family.  The public theorem below
instantiates this helper with the proved capped occupancy theorem. -/
private theorem exists_eventually_weightedIsolatedSum_lower_of_capped_package
    (hpackage : ∃ M : ℕ, ∃ B c : ℚ, 0 < B ∧ 0 < c ∧
      ∀ v : ℕ, 1 ≤ v →
        ∃ P : Finset (Fin v → Fin v),
          Occupancy.OccupancyInvariant P ∧
          (∀ f ∈ P, Occupancy.GoodPotential B f) ∧
          (∀ f ∈ P, ∀ j : Fin v,
            Occupancy.boxOccupancy f j ≤ M + (v - j.val) ^ 2) ∧
          c * (v : ℚ) ^ v ≤ (v : ℚ) * (P.card : ℚ)) :
    ∃ C : ℝ, 0 < C ∧ ∃ Y₀ : ℕ, ∀ y : ℕ, Y₀ ≤ y →
      ∃ A : Finset ℕ, (∀ a ∈ A, a ^ 2 ≤ y) ∧
        C * stirlingTerm (y : ℝ) ≤ weightedIsolatedSum A dyadicSigma := by
  obtain ⟨M, B, c, hB, hc, hpackage⟩ := hpackage
  obtain ⟨Csharp, hCsharp, hsharp⟩ := exists_fordSharpPairConstant
  have hBR : (0 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB.le
  obtain ⟨start, hcontrol, herror⟩ :=
    exists_controlled_dyadic_error_small Csharp (B : ℝ) hCsharp hBR
  obtain ⟨d, hd⟩ := exists_two_pow_ge
    (2 * (primeBlockLogUpperConstant * (M + 6 : ℕ) *
      (2 : ℝ) ^ (start + 1)))
  have hevent := eventually_nat_loglog_ge
    (((d + 1 : ℕ) : ℝ) * Real.log 2)
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨Y₀, hY₀⟩ := hevent
  refine ⟨(3 / 16 : ℝ) * (c : ℝ) * shiftedCriticalConstant d,
    mul_pos (mul_pos (by norm_num) (by exact_mod_cast hc))
      (shiftedCriticalConstant_pos d), Y₀, ?_⟩
  intro y hy
  have hlarge := hY₀ y hy
  have hthresholdPos :
      0 < (((d + 1 : ℕ) : ℝ) * Real.log 2) := by positivity
  have hloglogPos : 0 < Real.log (Real.log (y : ℝ)) :=
    hthresholdPos.trans_le hlarge
  have ht : 0 ≤ Real.log (Real.log (y : ℝ)) := hloglogPos.le
  have hlogyOne : 1 < Real.log (y : ℝ) :=
    (Real.log_pos_iff (by positivity)).mp hloglogPos
  have hlogy : 0 < Real.log (y : ℝ) := zero_lt_one.trans hlogyOne
  have hyOneR : (1 : ℝ) < y :=
    (Real.log_pos_iff (by positivity)).mp hlogy
  have hyOne : 1 ≤ y := by exact_mod_cast hyOneR.le
  have hk : d + 1 ≤ stirlingIndex (y : ℝ) :=
    stirlingIndex_ge_of_loglog_ge hlarge
  let v := stirlingIndex (y : ℝ) - d
  have hv : 1 ≤ v := by dsimp [v]; omega
  obtain ⟨P, hinvariant, hgood, hcap, hcount⟩ := hpackage v hv
  let A := placementProfileNumberFamily start P
  refine ⟨A, ?_, ?_⟩
  · intro a ha
    have haEnd : a ≤ highCapEndpointProduct start v M :=
      mem_placementProfileNumberFamily_le_highCapEndpointProduct hcap ha
    have hscale :
        2 * (primeBlockLogUpperConstant * (M + 6 : ℕ) *
          (2 : ℝ) ^ (start + 1) * (2 : ℝ) ^ v) ≤
            Real.log (y : ℝ) := by
      exact highCap_endpoint_scale_of_shift hd (by omega) hlogy ht
    exact (Nat.pow_le_pow_left haEnd 2).trans
      (highCapEndpointProduct_sq_le_of_scale hyOne hscale)
  · have hfinite := countConstant_mul_critical_factorial_le_placementProfile_of_sharp
      Csharp hCsharp hsharp hv hB.le hc.le P hinvariant hgood hcount
        hcontrol herror
    rw [weightedIsolatedSum_dyadic_eq]
    calc
      (3 / 16 : ℝ) * (c : ℝ) * shiftedCriticalConstant d *
          stirlingTerm (y : ℝ) =
        (3 / 16 : ℝ) * (c : ℝ) *
          (shiftedCriticalConstant d * stirlingTerm (y : ℝ)) := by ring
      _ ≤ (3 / 16 : ℝ) * (c : ℝ) * criticalFactorialTerm v := by
        gcongr
        exact shiftedCriticalConstant_mul_stirlingTerm_le ht hk
      _ ≤ weightedDyadicIsolatedMass A := by
        dsimp only [criticalFactorialTerm, A]
        convert hfinite using 1 <;> ring

/-- Assumption-free eventual weighted isolated-divisor lower bound.  The
family is the union of the squarefree profile families represented by the
placements which satisfy both Ford's collision-potential condition and his
high-end occupancy caps. -/
theorem exists_eventually_weightedIsolatedSum_lower :
    ∃ C : ℝ, 0 < C ∧ ∃ Y₀ : ℕ, ∀ y : ℕ, Y₀ ≤ y →
      ∃ A : Finset ℕ,
        (∀ a ∈ A, a ^ 2 ≤ y) ∧
        C * stirlingTerm (y : ℝ) ≤ weightedIsolatedSum A dyadicSigma := by
  apply exists_eventually_weightedIsolatedSum_lower_of_capped_package
  obtain ⟨M, B, c, hB, hc, hcount⟩ :=
    Occupancy.exists_goodPotential_highCap_count
  refine ⟨M, B, c, hB, hc, ?_⟩
  intro v hv
  let P : Finset (Fin v → Fin v) :=
    Finset.univ.filter (fun f ↦
      Occupancy.GoodPotential B f ∧ Occupancy.HighOccupancyCap M f)
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · intro f g hfg
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_congr
      (Occupancy.goodPotential_iff_of_occupancyVector_eq hfg)
      (Occupancy.highOccupancyCap_iff_of_occupancyVector_eq hfg)
  · intro f hf
    have hf' : Occupancy.GoodPotential B f ∧
        Occupancy.HighOccupancyCap M f := by
      simpa only [P, Finset.mem_filter, Finset.mem_univ, true_and] using hf
    exact hf'.1
  · intro f hf j
    have hf' : Occupancy.GoodPotential B f ∧
        Occupancy.HighOccupancyCap M f := by
      simpa only [P, Finset.mem_filter, Finset.mem_univ, true_and] using hf
    have hfcap : Occupancy.HighOccupancyCap M f := hf'.2
    exact Occupancy.highOccupancyCap_box_le hfcap j
  · simpa only [P] using hcount v hv

/-- Assumption-free finite-parameter assembly of Ford's sharp pair bound and
the occupancy-potential count.  The later capped theorem refines this family
to the size range required by the `H₁` construction. -/
theorem exists_uniform_finite_weighted_isolated_family :
    ∃ B c : ℚ, ∃ start : ℕ,
      0 < B ∧ 0 < c ∧ ProfileStartControlled 1 start ∧
      ∀ v : ℕ, 1 ≤ v →
        (∀ a ∈ goodProfileNumberFamily start v B,
          Squarefree a ∧ a.primeFactors ⊆ primeBlockSupport start v ∧
            a.primeFactors.card = v) ∧
        (3 / 16 : ℝ) * (c : ℝ) *
            (2 * (v : ℝ) * Real.log 2) ^ v / (v + 1).factorial ≤
          weightedIsolatedSum
            (goodProfileNumberFamily start v B) dyadicSigma := by
  exact exists_uniform_finite_weighted_isolated_family_of_analytic_inputs
    exists_fordSharpPairConstant Occupancy.exists_goodPotential_count

end Erdos896.Ford
