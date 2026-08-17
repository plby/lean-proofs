/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.LowerDefs
import ErdosProblems.Erdos896.Ford.PrimeEstimates

/-!
# Greedy prime blocks for Ford's dyadic lower bound

At the fixed width `sigma = log 2`, start at the endpoint `2`.  Given an
endpoint `x`, let `c` be the first natural number for which the reciprocal
prime mass in `(x,c]` is strictly greater than `log 2`, and use `c-1` as the
next endpoint.  Thus the block mass is at most `log 2`; its deficit is at
most the single omitted jump `1/c`.

The construction is completely finite.  Divergence of the reciprocal prime
sum proves that every crossing exists.  An elementary comparison with all
integers in `(x,c]` shows that the endpoints grow by a factor at least `3/2`.
Consequently the deficits form a summable geometric tail.  The final section
records the exact reciprocal-weighted divisor-pair inequality used to pass
from an off-diagonal estimate to isolated divisors.
-/

namespace Erdos896.Ford

open Filter
open scoped BigOperators Topology

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## The first crossing and the recursive endpoints -/

private theorem exists_primeBlockCrossing (x : ℕ) :
    ∃ n : ℕ, primeReciprocalSum x + Real.log 2 < primeReciprocalSum n := by
  have ht := primeReciprocalSum_tendsto_atTop
  rw [tendsto_atTop_atTop] at ht
  obtain ⟨N, hN⟩ := ht
    (primeReciprocalSum x + Real.log 2 + 1)
  refine ⟨max x N, ?_⟩
  have h := hN (max x N) (le_max_right x N)
  linarith

/-- The first natural cutoff at which the reciprocal prime mass after `x`
strictly exceeds `log 2`. -/
def primeBlockCrossing (x : ℕ) : ℕ :=
  Nat.find (exists_primeBlockCrossing x)

theorem primeBlockCrossing_spec (x : ℕ) :
    primeReciprocalSum x + Real.log 2 <
      primeReciprocalSum (primeBlockCrossing x) :=
  Nat.find_spec (exists_primeBlockCrossing x)

theorem primeBlockCrossing_min {x n : ℕ} (hn : n < primeBlockCrossing x) :
    primeReciprocalSum n ≤ primeReciprocalSum x + Real.log 2 := by
  exact le_of_not_gt (Nat.find_min (exists_primeBlockCrossing x) hn)

theorem lt_primeBlockCrossing (x : ℕ) : x < primeBlockCrossing x := by
  by_contra h
  have hmono := primeReciprocalSum_mono (Nat.le_of_not_gt h)
  have hspec := primeBlockCrossing_spec x
  linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

/-- The largest endpoint before the first crossing. -/
def nextPrimeBlockEndpoint (x : ℕ) : ℕ := primeBlockCrossing x - 1

theorem nextPrimeBlockEndpoint_add_one (x : ℕ) :
    nextPrimeBlockEndpoint x + 1 = primeBlockCrossing x := by
  have hx := lt_primeBlockCrossing x
  unfold nextPrimeBlockEndpoint
  omega

theorem le_nextPrimeBlockEndpoint (x : ℕ) : x ≤ nextPrimeBlockEndpoint x := by
  have hx := lt_primeBlockCrossing x
  unfold nextPrimeBlockEndpoint
  omega

/-- Greedy block endpoints, beginning with `lambda_0 = 2`. -/
def primeBlockEndpoint : ℕ → ℕ
  | 0 => 2
  | j + 1 => nextPrimeBlockEndpoint (primeBlockEndpoint j)

/-- Lower endpoint of `D_j`. -/
def primeBlockLower (j : ℕ) : ℕ := primeBlockEndpoint j

/-- Upper endpoint of `D_j`. -/
def primeBlockUpper (j : ℕ) : ℕ := primeBlockEndpoint (j + 1)

/-- Real versions retained for estimates involving reciprocal endpoints. -/
def primeBlockLowerReal (j : ℕ) : ℝ := primeBlockLower j

def primeBlockUpperReal (j : ℕ) : ℝ := primeBlockUpper j

@[simp] theorem primeBlockEndpoint_zero : primeBlockEndpoint 0 = 2 := rfl

@[simp] theorem primeBlockEndpoint_succ (j : ℕ) :
    primeBlockEndpoint (j + 1) =
      nextPrimeBlockEndpoint (primeBlockEndpoint j) := rfl

@[simp] theorem primeBlockLower_succ (j : ℕ) :
    primeBlockLower (j + 1) = primeBlockUpper j := rfl

theorem two_le_primeBlockEndpoint (j : ℕ) : 2 ≤ primeBlockEndpoint j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [primeBlockEndpoint_succ]
      exact ih.trans (le_nextPrimeBlockEndpoint _)

theorem primeBlockEndpoint_mono : Monotone primeBlockEndpoint := by
  apply monotone_nat_of_le_succ
  intro j
  rw [primeBlockEndpoint_succ]
  exact le_nextPrimeBlockEndpoint _

/-! ## Finite blocks and their exact mass -/

/-- The finite greedy prime block `D_j = (lambda_j,lambda_{j+1}]`. -/
def primeBlock (j : ℕ) : Finset ℕ :=
  Nat.primesLE (primeBlockUpper j) \ Nat.primesLE (primeBlockLower j)

/-- Reciprocal prime mass of `D_j`. -/
def primeBlockMass (j : ℕ) : ℝ :=
  ∑ p ∈ primeBlock j, (1 : ℝ) / p

@[simp] theorem mem_primeBlock {j p : ℕ} :
    p ∈ primeBlock j ↔
      p.Prime ∧ primeBlockLower j < p ∧ p ≤ primeBlockUpper j := by
  simp only [primeBlock, Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpUpper, hpPrime⟩, hpLower⟩
    exact ⟨hpPrime, lt_of_not_ge fun h ↦ hpLower ⟨h, hpPrime⟩, hpUpper⟩
  · rintro ⟨hpPrime, hpLower, hpUpper⟩
    exact ⟨⟨hpUpper, hpPrime⟩, fun h ↦ (not_le_of_gt hpLower) h.1⟩

theorem prime_of_mem_primeBlock {j p : ℕ} (hp : p ∈ primeBlock j) : p.Prime :=
  (mem_primeBlock.mp hp).1

theorem primeBlockLower_lt_of_mem {j p : ℕ} (hp : p ∈ primeBlock j) :
    primeBlockLower j < p := (mem_primeBlock.mp hp).2.1

theorem le_primeBlockUpper_of_mem {j p : ℕ} (hp : p ∈ primeBlock j) :
    p ≤ primeBlockUpper j := (mem_primeBlock.mp hp).2.2

theorem primeBlock_disjoint_of_ne {i j : ℕ} (hij : i ≠ j) :
    Disjoint (primeBlock i) (primeBlock j) := by
  rw [Finset.disjoint_left]
  intro p hpi hpj
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hi := mem_primeBlock.mp hpi
    have hj := mem_primeBlock.mp hpj
    have hEnd : primeBlockUpper i ≤ primeBlockLower j := by
      exact primeBlockEndpoint_mono (Nat.succ_le_iff.mpr hij)
    omega
  · have hi := mem_primeBlock.mp hpi
    have hj := mem_primeBlock.mp hpj
    have hEnd : primeBlockUpper j ≤ primeBlockLower i := by
      exact primeBlockEndpoint_mono (Nat.succ_le_iff.mpr hji)
    omega

theorem primeBlockMass_eq_sub (j : ℕ) :
    primeBlockMass j =
      primeReciprocalSum (primeBlockUpper j) -
        primeReciprocalSum (primeBlockLower j) := by
  rw [primeBlockMass, primeBlock, primeReciprocalSum]
  exact Finset.sum_sdiff_eq_sub
    (Nat.primesLE_mono (primeBlockEndpoint_mono (Nat.le_succ j)))

theorem primeBlockMass_nonneg (j : ℕ) : 0 ≤ primeBlockMass j := by
  unfold primeBlockMass
  positivity

/-- A reciprocal-prime prefix can jump by at most `1/n` at `n`. -/
theorem primeReciprocalSum_sub_pred_le (n : ℕ) :
    primeReciprocalSum n - primeReciprocalSum (n - 1) ≤ (1 : ℝ) / n := by
  rcases n with _ | n
  · simp [primeReciprocalSum]
  · have hsub : Nat.primesLE n ⊆ Nat.primesLE (n + 1) :=
      Nat.primesLE_mono (by omega)
    simp only [Nat.add_sub_cancel]
    rw [primeReciprocalSum, primeReciprocalSum,
      ← Finset.sum_sdiff_eq_sub hsub]
    calc
      (∑ p ∈ Nat.primesLE (n + 1) \ Nat.primesLE n, (1 : ℝ) / p) ≤
          ∑ p ∈ ({n + 1} : Finset ℕ), (1 : ℝ) / p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          simp only [Finset.mem_sdiff, Nat.mem_primesLE] at hp
          simp only [Finset.mem_singleton]
          rcases hp with ⟨⟨hle, hprime⟩, hnot⟩
          have hnle : ¬p ≤ n := fun hle' ↦ hnot ⟨hle', hprime⟩
          omega
        · intro p hp hnot
          positivity
      _ = (1 : ℝ) / ((n : ℝ) + 1) := by simp
      _ = (1 : ℝ) / (n + 1 : ℕ) := by push_cast; rfl

/-- Greedy orientation: every block has reciprocal mass at most `log 2`. -/
theorem primeBlockMass_le_log_two (j : ℕ) :
    primeBlockMass j ≤ Real.log 2 := by
  rw [primeBlockMass_eq_sub]
  have hmin := primeBlockCrossing_min
    (x := primeBlockLower j) (n := primeBlockUpper j)
  have hlt : primeBlockUpper j < primeBlockCrossing (primeBlockLower j) := by
    rw [primeBlockUpper, primeBlockLower, primeBlockEndpoint_succ]
    rw [← nextPrimeBlockEndpoint_add_one]
    omega
  specialize hmin hlt
  linarith

/-- The missing mass is at most the one prime reciprocal at the crossing. -/
theorem primeBlockMass_lower_crossing (j : ℕ) :
    Real.log 2 - (1 : ℝ) / primeBlockCrossing (primeBlockLower j) ≤
      primeBlockMass j := by
  have hspec := primeBlockCrossing_spec (primeBlockLower j)
  have hjump := primeReciprocalSum_sub_pred_le
    (primeBlockCrossing (primeBlockLower j))
  have hpred : primeBlockCrossing (primeBlockLower j) - 1 =
      primeBlockUpper j := by
    rw [primeBlockUpper, primeBlockLower, primeBlockEndpoint_succ]
    rfl
  rw [hpred] at hjump
  rw [primeBlockMass_eq_sub]
  linarith

/-! ## Endpoint growth and summable errors -/

private theorem crossing_interval_mass_le_two_thirds {x c : ℕ}
    (hx : 2 ≤ x) (hxc : x ≤ c) (hc : c ≤ x + x / 2 + 1) :
    primeReciprocalSum c - primeReciprocalSum x ≤ (2 : ℝ) / 3 := by
  have hsub : Nat.primesLE x ⊆ Nat.primesLE c := Nat.primesLE_mono hxc
  rw [primeReciprocalSum, primeReciprocalSum,
    ← Finset.sum_sdiff_eq_sub hsub]
  let s := Nat.primesLE c \ Nat.primesLE x
  have hsIoc : s ⊆ Finset.Ioc x c := by
    intro p hp
    simp only [s, Finset.mem_sdiff, Nat.mem_primesLE] at hp
    simp only [Finset.mem_Ioc]
    exact ⟨lt_of_not_ge fun h ↦ hp.2 ⟨h, hp.1.2⟩, hp.1.1⟩
  have hcard : s.card ≤ c - x := by
    simpa [Nat.card_Ioc] using Finset.card_le_card hsIoc
  have hterm : ∀ p ∈ s, (1 : ℝ) / p ≤ 1 / (x + 1 : ℕ) := by
    intro p hp
    have hpIoc := Finset.mem_Ioc.mp (hsIoc hp)
    have hpos : (0 : ℝ) < (x + 1 : ℕ) := by positivity
    exact one_div_le_one_div_of_le hpos (by exact_mod_cast hpIoc.1)
  have hsum := Finset.sum_le_card_nsmul s (fun p : ℕ ↦ (1 : ℝ) / p)
    ((1 : ℝ) / (x + 1 : ℕ)) hterm
  have hcardR : (s.card : ℝ) ≤ (c - x : ℕ) := by exact_mod_cast hcard
  have hnonneg : 0 ≤ (1 : ℝ) / (x + 1 : ℕ) := by positivity
  have hcount : (c - x : ℕ) ≤ x / 2 + 1 := by omega
  have hcountR : ((c - x : ℕ) : ℝ) ≤ (x : ℝ) / 2 + 1 := by
    calc
      ((c - x : ℕ) : ℝ) ≤ ((x / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast hcount
      _ ≤ (x : ℝ) / 2 + 1 := by
        push_cast
        simpa [add_comm] using
          (add_le_add_right (Nat.cast_div_le (α := ℝ) (m := x) (n := 2)) 1)
  have hxR : (2 : ℝ) ≤ x := by exact_mod_cast hx
  calc
    ∑ p ∈ s, (1 : ℝ) / p ≤ s.card • ((1 : ℝ) / (x + 1 : ℕ)) := hsum
    _ = (s.card : ℝ) * ((1 : ℝ) / (x + 1 : ℕ)) := by simp [nsmul_eq_mul]
    _ ≤ ((c - x : ℕ) : ℝ) * ((1 : ℝ) / (x + 1 : ℕ)) :=
      mul_le_mul_of_nonneg_right hcardR hnonneg
    _ ≤ ((x : ℝ) / 2 + 1) * ((1 : ℝ) / (x + 1 : ℕ)) :=
      mul_le_mul_of_nonneg_right hcountR hnonneg
    _ ≤ (2 : ℝ) / 3 := by
      push_cast
      rw [one_div, ← div_eq_mul_inv]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < x + 1)).2
      nlinarith

/-- The next greedy endpoint is at least `x + floor(x/2) + 1`. -/
theorem nextPrimeBlockEndpoint_growth {x : ℕ} (hx : 2 ≤ x) :
    x + x / 2 + 1 ≤ nextPrimeBlockEndpoint x := by
  have hxc : x ≤ primeBlockCrossing x := (lt_primeBlockCrossing x).le
  by_contra h
  have hc : primeBlockCrossing x ≤ x + x / 2 + 1 := by
    unfold nextPrimeBlockEndpoint at h
    omega
  have hmass := crossing_interval_mass_le_two_thirds hx hxc hc
  have hspec := primeBlockCrossing_spec x
  have hlog : (2 : ℝ) / 3 < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  linarith

theorem primeBlockEndpoint_growth (j : ℕ) :
    primeBlockEndpoint j + primeBlockEndpoint j / 2 + 1 ≤
      primeBlockEndpoint (j + 1) := by
  rw [primeBlockEndpoint_succ]
  exact nextPrimeBlockEndpoint_growth (two_le_primeBlockEndpoint j)

/-- Integral form of the uniform factor-`3/2` growth. -/
theorem three_mul_primeBlockEndpoint_le_two_mul_succ (j : ℕ) :
    3 * primeBlockEndpoint j ≤ 2 * primeBlockEndpoint (j + 1) := by
  have h := primeBlockEndpoint_growth j
  omega

/-- A denominator-free geometric endpoint bound. -/
theorem primeBlockEndpoint_geometric (j : ℕ) :
    2 * 3 ^ j ≤ 2 ^ j * primeBlockEndpoint j := by
  induction j with
  | zero => simp
  | succ j ih =>
      calc
        2 * 3 ^ (j + 1) = 3 * (2 * 3 ^ j) := by ring
        _ ≤ 3 * (2 ^ j * primeBlockEndpoint j) := Nat.mul_le_mul_left 3 ih
        _ ≤ 2 ^ j * (2 * primeBlockEndpoint (j + 1)) := by
          rw [show 3 * (2 ^ j * primeBlockEndpoint j) =
              2 ^ j * (3 * primeBlockEndpoint j) by ring]
          exact Nat.mul_le_mul_left (2 ^ j)
            (three_mul_primeBlockEndpoint_le_two_mul_succ j)
        _ = 2 ^ (j + 1) * primeBlockEndpoint (j + 1) := by
          rw [pow_succ]
          ring

/-- Reciprocal endpoints are bounded by the explicit geometric sequence
`(1/2)(2/3)^j`. -/
theorem one_div_primeBlockEndpoint_le_geometric (j : ℕ) :
    (1 : ℝ) / primeBlockEndpoint j ≤
      (1 / 2 : ℝ) * (2 / 3 : ℝ) ^ j := by
  have h := primeBlockEndpoint_geometric j
  have hR : (2 : ℝ) * 3 ^ j ≤
      2 ^ j * primeBlockEndpoint j := by exact_mod_cast h
  have hp : (0 : ℝ) < primeBlockEndpoint j := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) (two_le_primeBlockEndpoint j))
  have hthree : (0 : ℝ) < 3 ^ j := by positivity
  rw [show (1 / 2 : ℝ) * (2 / 3 : ℝ) ^ j =
      (2 : ℝ) ^ j / (2 * 3 ^ j) by rw [div_pow]; field_simp]
  exact (div_le_div_iff₀ hp (mul_pos (by norm_num) hthree)).2 (by simpa using hR)

/-- The reciprocal endpoint errors are summable. -/
theorem summable_one_div_primeBlockEndpoint :
    Summable (fun j : ℕ ↦ (1 : ℝ) / primeBlockEndpoint j) := by
  have hgeom : Summable (fun j : ℕ ↦ (1 / 2 : ℝ) * (2 / 3 : ℝ) ^ j) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(2 / 3 : ℝ)‖ < 1)).mul_left
      (1 / 2 : ℝ)
  exact hgeom.of_nonneg_of_le
    (fun j ↦ by positivity) one_div_primeBlockEndpoint_le_geometric

/-- The greedy deficits are summable, hence do not cause an exponential
loss when finitely many consecutive blocks are multiplied. -/
theorem summable_primeBlockMass_deficit :
    Summable (fun j : ℕ ↦ Real.log 2 - primeBlockMass j) := by
  have hbound : ∀ j : ℕ,
      Real.log 2 - primeBlockMass j ≤
        (1 : ℝ) / primeBlockEndpoint (j + 1) := by
    intro j
    have h := primeBlockMass_lower_crossing j
    have hc : primeBlockCrossing (primeBlockLower j) =
        primeBlockEndpoint (j + 1) + 1 := by
      rw [primeBlockLower, primeBlockEndpoint_succ,
        nextPrimeBlockEndpoint_add_one]
    rw [hc] at h
    have hmono : (1 : ℝ) / (primeBlockEndpoint (j + 1) + 1) ≤
        1 / primeBlockEndpoint (j + 1) := by
      apply one_div_le_one_div_of_le
      · exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2)
          (two_le_primeBlockEndpoint (j + 1)))
      · norm_num
    push_cast at h
    linarith
  have hs : Summable (fun j : ℕ ↦ (1 : ℝ) / primeBlockEndpoint (j + 1)) :=
    (summable_nat_add_iff 1).2 summable_one_div_primeBlockEndpoint
  exact hs.of_nonneg_of_le
    (fun j ↦ sub_nonneg.mpr (primeBlockMass_le_log_two j)) hbound

/-! ## Double-exponential endpoint scale from Mertens -/

/-- A fixed Mertens constant for the natural reciprocal-prime prefixes. -/
def primeBlockMertensConstant : ℝ :=
  Classical.choose exists_primeReciprocalSum_sub_log_log_bound

theorem primeBlockMertens_bound {x : ℕ} (hx : 2 ≤ x) :
    |primeReciprocalSum x - Real.log (Real.log x)| ≤
      primeBlockMertensConstant :=
  (Classical.choose_spec exists_primeReciprocalSum_sub_log_log_bound) x hx

theorem primeBlockMertensConstant_nonneg : 0 ≤ primeBlockMertensConstant := by
  exact (abs_nonneg _).trans (primeBlockMertens_bound (x := 2) (by norm_num))

/-- The reciprocal mass at an endpoint is exactly the sum of all preceding
block masses. -/
theorem primeReciprocalSum_endpoint_eq (j : ℕ) :
    primeReciprocalSum (primeBlockEndpoint j) =
      primeReciprocalSum 2 + ∑ i ∈ Finset.range j, primeBlockMass i := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ← ih]
      have hmass := primeBlockMass_eq_sub j
      simp only [primeBlockUpper, primeBlockLower] at hmass
      linarith

theorem primeReciprocalSum_endpoint_le (j : ℕ) :
    primeReciprocalSum (primeBlockEndpoint j) ≤
      primeReciprocalSum 2 + (j : ℝ) * Real.log 2 := by
  rw [primeReciprocalSum_endpoint_eq]
  have hsum : (∑ i ∈ Finset.range j, primeBlockMass i) ≤
      ∑ _i ∈ Finset.range j, Real.log 2 := by
    exact Finset.sum_le_sum fun i hi ↦ primeBlockMass_le_log_two i
  simpa [Finset.sum_const, nsmul_eq_mul] using add_le_add_left hsum (primeReciprocalSum 2)

theorem sum_primeBlockMass_deficit_le_one (j : ℕ) :
    (∑ i ∈ Finset.range j, (Real.log 2 - primeBlockMass i)) ≤ 1 := by
  have hdef : ∀ i : ℕ, Real.log 2 - primeBlockMass i ≤
      (1 / 2 : ℝ) * (2 / 3 : ℝ) ^ (i + 1) := by
    intro i
    have h := primeBlockMass_lower_crossing i
    have hc : primeBlockCrossing (primeBlockLower i) =
        primeBlockEndpoint (i + 1) + 1 := by
      rw [primeBlockLower, primeBlockEndpoint_succ,
        nextPrimeBlockEndpoint_add_one]
    rw [hc] at h
    push_cast at h
    have hp : (0 : ℝ) < primeBlockEndpoint (i + 1) := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2)
        (two_le_primeBlockEndpoint (i + 1)))
    have hmono : (1 : ℝ) / (primeBlockEndpoint (i + 1) + 1) ≤
        1 / primeBlockEndpoint (i + 1) :=
      one_div_le_one_div_of_le hp (by norm_num)
    linarith [one_div_primeBlockEndpoint_le_geometric (i + 1)]
  have hgeom : (∑ i ∈ Finset.range j, (2 / 3 : ℝ) ^ i) ≤ 3 := by
    have hsum := geom_sum_mul_neg (2 / 3 : ℝ) j
    have hpow : 0 ≤ (2 / 3 : ℝ) ^ j := by positivity
    norm_num at hsum ⊢
    nlinarith
  calc
    (∑ i ∈ Finset.range j, (Real.log 2 - primeBlockMass i)) ≤
        ∑ i ∈ Finset.range j, (1 / 2 : ℝ) * (2 / 3 : ℝ) ^ (i + 1) := by
      exact Finset.sum_le_sum fun i hi ↦ hdef i
    _ = (1 / 2 : ℝ) * (2 / 3 : ℝ) *
        ∑ i ∈ Finset.range j, (2 / 3 : ℝ) ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [pow_succ]
      ring
    _ ≤ (1 / 2 : ℝ) * (2 / 3 : ℝ) * 3 := by
      gcongr
    _ = 1 := by norm_num

theorem primeReciprocalSum_endpoint_lower (j : ℕ) :
    primeReciprocalSum 2 + (j : ℝ) * Real.log 2 - 1 ≤
      primeReciprocalSum (primeBlockEndpoint j) := by
  rw [primeReciprocalSum_endpoint_eq]
  have hdef := sum_primeBlockMass_deficit_le_one j
  have hconst : (∑ _i ∈ Finset.range j, Real.log 2) =
      (j : ℝ) * Real.log 2 := by simp [Finset.sum_const, nsmul_eq_mul]
  have hsplit : (∑ i ∈ Finset.range j,
      (Real.log 2 - primeBlockMass i)) =
      (j : ℝ) * Real.log 2 - ∑ i ∈ Finset.range j, primeBlockMass i := by
    rw [Finset.sum_sub_distrib, hconst]
  rw [hsplit] at hdef
  linarith

/-- Explicit constants in the two-sided estimate
`log lambda_jasymp 2^j`. -/
def primeBlockLogLowerConstant : ℝ :=
  Real.exp (primeReciprocalSum 2 - 1 - primeBlockMertensConstant)

def primeBlockLogUpperConstant : ℝ :=
  Real.exp (primeReciprocalSum 2 + primeBlockMertensConstant)

theorem primeBlockLogLowerConstant_pos : 0 < primeBlockLogLowerConstant := by
  exact Real.exp_pos _

theorem primeBlockLogUpperConstant_pos : 0 < primeBlockLogUpperConstant := by
  exact Real.exp_pos _

/-- Lower endpoint scale.  This is the sharp geometric error input needed
for Ford's prefix potential. -/
theorem primeBlockLogLowerConstant_mul_pow_le_log_endpoint (j : ℕ) :
    primeBlockLogLowerConstant * (2 : ℝ) ^ j ≤
      Real.log (primeBlockEndpoint j) := by
  have hm := primeBlockMertens_bound (two_le_primeBlockEndpoint j)
  have hmUpper : primeReciprocalSum (primeBlockEndpoint j) -
      primeBlockMertensConstant ≤ Real.log (Real.log (primeBlockEndpoint j)) := by
    have := (abs_le.mp hm).2
    linarith
  have hmass := primeReciprocalSum_endpoint_lower j
  have hloglog : primeReciprocalSum 2 - 1 - primeBlockMertensConstant +
      (j : ℝ) * Real.log 2 ≤
      Real.log (Real.log (primeBlockEndpoint j)) := by
    linarith
  have hlogPos : 0 < Real.log (primeBlockEndpoint j) :=
    Real.log_pos (by exact_mod_cast
      (lt_of_lt_of_le (by omega : 1 < 2) (two_le_primeBlockEndpoint j)))
  have hexp := Real.exp_le_exp.mpr hloglog
  rw [Real.exp_add, Real.exp_log hlogPos, Real.exp_nat_mul] at hexp
  simpa [primeBlockLogLowerConstant, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    using hexp

/-- Upper endpoint scale, used to keep products of primes from consecutive
blocks inside the required power of `y`. -/
theorem log_endpoint_le_primeBlockLogUpperConstant_mul_pow (j : ℕ) :
    Real.log (primeBlockEndpoint j) ≤
      primeBlockLogUpperConstant * (2 : ℝ) ^ j := by
  have hm := primeBlockMertens_bound (two_le_primeBlockEndpoint j)
  have hmLower : Real.log (Real.log (primeBlockEndpoint j)) ≤
      primeReciprocalSum (primeBlockEndpoint j) + primeBlockMertensConstant := by
    have := (abs_le.mp hm).1
    linarith
  have hmass := primeReciprocalSum_endpoint_le j
  have hloglog : Real.log (Real.log (primeBlockEndpoint j)) ≤
      primeReciprocalSum 2 + primeBlockMertensConstant +
        (j : ℝ) * Real.log 2 := by
    linarith
  have hlogPos : 0 < Real.log (primeBlockEndpoint j) :=
    Real.log_pos (by exact_mod_cast
      (lt_of_lt_of_le (by omega : 1 < 2) (two_le_primeBlockEndpoint j)))
  have hexp := Real.exp_le_exp.mpr hloglog
  rw [Real.exp_log hlogPos, Real.exp_add, Real.exp_nat_mul] at hexp
  simpa [primeBlockLogUpperConstant, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    using hexp

theorem sum_log_primeBlockUpper_le (start k : ℕ) :
    (∑ i ∈ Finset.range k, Real.log (primeBlockUpper (start + i))) ≤
      primeBlockLogUpperConstant * (2 : ℝ) ^ (start + k + 1) := by
  have hsumPow : (∑ i ∈ Finset.range k, (2 : ℝ) ^ i) ≤ 2 ^ k := by
    have hgeom := geom_sum_mul (2 : ℝ) k
    have hpow : 0 ≤ (2 : ℝ) ^ k := by positivity
    norm_num at hgeom ⊢
    linarith
  calc
    (∑ i ∈ Finset.range k, Real.log (primeBlockUpper (start + i))) ≤
        ∑ i ∈ Finset.range k,
          primeBlockLogUpperConstant * (2 : ℝ) ^ (start + i + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa [primeBlockUpper, Nat.add_assoc] using
        log_endpoint_le_primeBlockLogUpperConstant_mul_pow (start + i + 1)
    _ = primeBlockLogUpperConstant * (2 : ℝ) ^ (start + 1) *
        ∑ i ∈ Finset.range k, (2 : ℝ) ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [show start + i + 1 = (start + 1) + i by omega, pow_add]
      ring
    _ ≤ primeBlockLogUpperConstant * (2 : ℝ) ^ (start + 1) * 2 ^ k :=
      mul_le_mul_of_nonneg_left hsumPow
        (mul_nonneg primeBlockLogUpperConstant_pos.le (by positivity))
    _ = primeBlockLogUpperConstant * (2 : ℝ) ^ (start + k + 1) := by
      rw [show start + k + 1 = (start + 1) + k by omega, pow_add]
      ring

/-- A direct size bound for the product of the upper endpoints of `k`
consecutive blocks. -/
theorem cast_prod_primeBlockUpper_le_exp (start k : ℕ) :
    ((∏ i ∈ Finset.range k, primeBlockUpper (start + i) : ℕ) : ℝ) ≤
      Real.exp (primeBlockLogUpperConstant * (2 : ℝ) ^ (start + k + 1)) := by
  have hpos : 0 < ∏ i ∈ Finset.range k,
      (primeBlockUpper (start + i) : ℝ) := by
    apply Finset.prod_pos
    intro i hi
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2)
      (two_le_primeBlockEndpoint (start + i + 1)))
  rw [Nat.cast_prod]
  calc
    (∏ i ∈ Finset.range k, (primeBlockUpper (start + i) : ℝ)) =
        Real.exp (Real.log (∏ i ∈ Finset.range k,
          (primeBlockUpper (start + i) : ℝ))) := (Real.exp_log hpos).symm
    _ ≤ Real.exp (primeBlockLogUpperConstant *
        (2 : ℝ) ^ (start + k + 1)) := by
      apply Real.exp_le_exp.mpr
      rw [Real.log_prod (fun i hi ↦ ne_of_gt (by
        exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2)
          (two_le_primeBlockEndpoint (start + i + 1)))))]
      exact sum_log_primeBlockUpper_le start k

/-- Reciprocal-log form consumed by the off-diagonal prefix estimate. -/
theorem one_div_log_endpoint_le_geometric (j : ℕ) :
    (1 : ℝ) / Real.log (primeBlockEndpoint j) ≤
      primeBlockLogLowerConstant⁻¹ * (1 / 2 : ℝ) ^ j := by
  have hlower := primeBlockLogLowerConstant_mul_pow_le_log_endpoint j
  have hc : 0 < primeBlockLogLowerConstant := primeBlockLogLowerConstant_pos
  have hp : 0 < (2 : ℝ) ^ j := by positivity
  have hlog : 0 < Real.log (primeBlockEndpoint j) :=
    lt_of_lt_of_le (mul_pos hc hp) hlower
  rw [show primeBlockLogLowerConstant⁻¹ * (1 / 2 : ℝ) ^ j =
      (primeBlockLogLowerConstant * (2 : ℝ) ^ j)⁻¹ by
    simp [one_div, inv_pow, mul_comm]]
  simpa [one_div] using (inv_le_inv₀ hlog (mul_pos hc hp)).2 hlower

/-! ## Uniform finite-product control -/

/-- Relative loss of the `j`-th block from its target mass `log 2`. -/
def primeBlockRelativeDeficit (j : ℕ) : ℝ :=
  (Real.log 2 - primeBlockMass j) / Real.log 2

theorem primeBlockMass_deficit_le_geometric (j : ℕ) :
    Real.log 2 - primeBlockMass j ≤
      (1 / 2 : ℝ) * (2 / 3 : ℝ) ^ (j + 1) := by
  have h := primeBlockMass_lower_crossing j
  have hc : primeBlockCrossing (primeBlockLower j) =
      primeBlockEndpoint (j + 1) + 1 := by
    rw [primeBlockLower, primeBlockEndpoint_succ,
      nextPrimeBlockEndpoint_add_one]
  rw [hc] at h
  push_cast at h
  have hp : (0 : ℝ) < primeBlockEndpoint (j + 1) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2)
      (two_le_primeBlockEndpoint (j + 1)))
  have hmono : (1 : ℝ) / (primeBlockEndpoint (j + 1) + 1) ≤
      1 / primeBlockEndpoint (j + 1) :=
    one_div_le_one_div_of_le hp (by norm_num)
  linarith [one_div_primeBlockEndpoint_le_geometric (j + 1)]

theorem primeBlockRelativeDeficit_nonneg (j : ℕ) :
    0 ≤ primeBlockRelativeDeficit j := by
  exact div_nonneg (sub_nonneg.mpr (primeBlockMass_le_log_two j))
    (Real.log_pos (by norm_num)).le

theorem primeBlockRelativeDeficit_le_geometric (j : ℕ) :
    primeBlockRelativeDeficit j ≤ (2 / 3 : ℝ) ^ (j + 1) := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 :=
    Real.log_two_gt_d9.le.trans' (by norm_num)
  have hlogPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (div_le_iff₀ hlogPos).2
  calc
    Real.log 2 - primeBlockMass j ≤
        (1 / 2 : ℝ) * (2 / 3 : ℝ) ^ (j + 1) :=
      primeBlockMass_deficit_le_geometric j
    _ ≤ (2 / 3 : ℝ) ^ (j + 1) * Real.log 2 := by
      rw [mul_comm (1 / 2 : ℝ)]
      exact mul_le_mul_of_nonneg_left hlog (by positivity)

private theorem geom_sum_two_thirds_le_three (k : ℕ) :
    (∑ i ∈ Finset.range k, (2 / 3 : ℝ) ^ i) ≤ 3 := by
  have hgeom := geom_sum_mul_neg (2 / 3 : ℝ) k
  have hpow : 0 ≤ (2 / 3 : ℝ) ^ k := by positivity
  norm_num at hgeom ⊢
  nlinarith

theorem sum_primeBlockRelativeDeficit_le_half {start : ℕ}
    (hstart : 5 ≤ start) (k : ℕ) :
    (∑ i ∈ Finset.range k, primeBlockRelativeDeficit (start + i)) ≤ 1 / 2 := by
  let r : ℝ := 2 / 3
  have hr0 : 0 ≤ r := by norm_num [r]
  have hr1 : r ≤ 1 := by norm_num [r]
  have hpowStart : r ^ (start + 1) ≤ r ^ 6 := by
    exact pow_le_pow_of_le_one hr0 hr1 (by omega)
  calc
    (∑ i ∈ Finset.range k, primeBlockRelativeDeficit (start + i)) ≤
        ∑ i ∈ Finset.range k, r ^ (start + i + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa [r, Nat.add_assoc] using
        primeBlockRelativeDeficit_le_geometric (start + i)
    _ = r ^ (start + 1) * ∑ i ∈ Finset.range k, r ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← pow_add]
      congr 1
      omega
    _ ≤ r ^ (start + 1) * 3 :=
      mul_le_mul_of_nonneg_left (by simpa [r] using geom_sum_two_thirds_le_three k)
        (pow_nonneg hr0 _)
    _ ≤ r ^ 6 * 3 := mul_le_mul_of_nonneg_right hpowStart (by norm_num)
    _ ≤ 1 / 2 := by norm_num [r]

private theorem one_sub_sum_le_prod_one_sub
    (d : ℕ → ℝ) (k : ℕ) (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i ≤ 1) :
    1 - ∑ i ∈ Finset.range k, d i ≤
      ∏ i ∈ Finset.range k, (1 - d i) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, Finset.prod_range_succ]
      have hsum : 0 ≤ ∑ i ∈ Finset.range k, d i := by
        exact Finset.sum_nonneg fun i hi ↦ hd0 i
      have hmul : 0 ≤ (∑ i ∈ Finset.range k, d i) * d k :=
        mul_nonneg hsum (hd0 k)
      calc
        1 - ((∑ i ∈ Finset.range k, d i) + d k) ≤
            (1 - ∑ i ∈ Finset.range k, d i) * (1 - d k) := by
          nlinarith
        _ ≤ (∏ i ∈ Finset.range k, (1 - d i)) * (1 - d k) :=
          mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr (hd1 k))

/-- From block `5` onward, every finite consecutive product loses only one
fixed factor.  In particular there is no exponential-base loss. -/
theorem half_mul_log_two_pow_le_prod_primeBlockMass {start : ℕ}
    (hstart : 5 ≤ start) (k : ℕ) :
    (1 / 2 : ℝ) * (Real.log 2) ^ k ≤
      ∏ i ∈ Finset.range k, primeBlockMass (start + i) := by
  let d : ℕ → ℝ := fun i ↦ primeBlockRelativeDeficit (start + i)
  have hd0 : ∀ i, 0 ≤ d i := fun i ↦ primeBlockRelativeDeficit_nonneg _
  have hsum : (∑ i ∈ Finset.range k, d i) ≤ 1 / 2 := by
    simpa [d] using sum_primeBlockRelativeDeficit_le_half hstart k
  have hd1 : ∀ i, d i ≤ 1 := by
    intro i
    have hi : d i ≤ (2 / 3 : ℝ) ^ (start + i + 1) := by
      simpa [d, Nat.add_assoc] using
        primeBlockRelativeDeficit_le_geometric (start + i)
    exact hi.trans (pow_le_one₀ (by norm_num) (by norm_num))
  have hprod : (1 / 2 : ℝ) ≤ ∏ i ∈ Finset.range k, (1 - d i) := by
    have hmain := one_sub_sum_le_prod_one_sub d k hd0 hd1
    linarith
  have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  calc
    (1 / 2 : ℝ) * (Real.log 2) ^ k ≤
        (∏ i ∈ Finset.range k, (1 - d i)) * (Real.log 2) ^ k :=
      mul_le_mul_of_nonneg_right hprod (pow_nonneg hlog _)
    _ = ∏ i ∈ Finset.range k, primeBlockMass (start + i) := by
      have hpow : (Real.log 2) ^ k =
          ∏ i ∈ Finset.range k, Real.log 2 := by simp
      rw [hpow, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      simp only [d, primeBlockRelativeDeficit]
      have hlogNe : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
      field_simp
      ring

/-! ## Square-prime collision mass -/

def primeBlockSquareMass (j : ℕ) : ℝ :=
  ∑ p ∈ primeBlock j, (1 : ℝ) / (p : ℝ) ^ 2

theorem primeBlockSquareMass_le (j : ℕ) :
    primeBlockSquareMass j ≤
      (1 / (primeBlockLower j + 1 : ℕ) : ℝ) * primeBlockMass j := by
  unfold primeBlockSquareMass primeBlockMass
  calc
    (∑ p ∈ primeBlock j, (1 : ℝ) / (p : ℝ) ^ 2) ≤
        ∑ p ∈ primeBlock j,
          (1 / (primeBlockLower j + 1 : ℕ) : ℝ) * ((1 : ℝ) / p) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpPrime := prime_of_mem_primeBlock hp
      have hpPos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
      have hLower : (primeBlockLower j + 1 : ℝ) ≤ p := by
        exact_mod_cast primeBlockLower_lt_of_mem hp
      have hden : (primeBlockLower j + 1 : ℝ) * p ≤ (p : ℝ) * p :=
        mul_le_mul_of_nonneg_right hLower hpPos.le
      have hinv := one_div_le_one_div_of_le
        (mul_pos (by positivity : (0 : ℝ) < primeBlockLower j + 1) hpPos) hden
      simpa [pow_two, one_div, mul_inv, mul_assoc, mul_comm, mul_left_comm] using hinv
    _ = (1 / (primeBlockLower j + 1 : ℕ) : ℝ) *
        ∑ p ∈ primeBlock j, (1 : ℝ) / p := by rw [Finset.mul_sum]

/-! ## Concrete finite block families -/

def primeBlockSupport (start blocks : ℕ) : Finset ℕ :=
  (Finset.range blocks).biUnion fun i ↦ primeBlock (start + i)

def blockSquarefreeNumbers (start blocks k : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (∏ p ∈ primeBlockSupport start blocks, p)).filter fun a ↦
    Squarefree a ∧ a.primeFactors ⊆ primeBlockSupport start blocks ∧
      a.primeFactors.card = k

@[simp] theorem mem_blockSquarefreeNumbers {start blocks k a : ℕ} :
    a ∈ blockSquarefreeNumbers start blocks k ↔
      1 ≤ a ∧ a ≤ ∏ p ∈ primeBlockSupport start blocks, p ∧
      Squarefree a ∧ a.primeFactors ⊆ primeBlockSupport start blocks ∧
      a.primeFactors.card = k := by
  simp [blockSquarefreeNumbers, and_assoc]

theorem squarefree_of_mem_blockSquarefreeNumbers {start blocks k a : ℕ}
    (ha : a ∈ blockSquarefreeNumbers start blocks k) : Squarefree a :=
  (mem_blockSquarefreeNumbers.mp ha).2.2.1

theorem primeFactors_subset_of_mem_blockSquarefreeNumbers
    {start blocks k a : ℕ} (ha : a ∈ blockSquarefreeNumbers start blocks k) :
    a.primeFactors ⊆ primeBlockSupport start blocks :=
  (mem_blockSquarefreeNumbers.mp ha).2.2.2.1

theorem primeFactors_card_of_mem_blockSquarefreeNumbers
    {start blocks k a : ℕ} (ha : a ∈ blockSquarefreeNumbers start blocks k) :
    a.primeFactors.card = k :=
  (mem_blockSquarefreeNumbers.mp ha).2.2.2.2

/-! ## The exact weighted divisor-pair passage -/

def weightedDivisorMass (family : Finset ℕ) : ℝ :=
  ∑ a ∈ family, (divisorCount a : ℝ) / a

def weightedDyadicPairMass (family : Finset ℕ) : ℝ :=
  ∑ a ∈ family, (W a dyadicSigma : ℝ) / a

def weightedDyadicIsolatedMass (family : Finset ℕ) : ℝ :=
  ∑ a ∈ family, (I a dyadicSigma : ℝ) / a

theorem two_mul_weightedDivisorMass_le_pair_add_isolated
    (family : Finset ℕ) :
    2 * weightedDivisorMass family ≤
      weightedDyadicPairMass family + weightedDyadicIsolatedMass family := by
  rw [weightedDivisorMass, weightedDyadicPairMass,
    weightedDyadicIsolatedMass, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a ha
  have hpoint := two_mul_divisorCount_le_W_add_I (a := a) dyadicSigma_pos
  calc
    2 * ((divisorCount a : ℝ) / a) =
        ((2 * divisorCount a : ℕ) : ℝ) / a := by norm_num; ring
    _ ≤ ((W a dyadicSigma + I a dyadicSigma : ℕ) : ℝ) / a := by
      gcongr
    _ = (W a dyadicSigma : ℝ) / a + (I a dyadicSigma : ℝ) / a := by
      push_cast
      ring

theorem two_mul_weightedDivisorMass_sub_pair_le_isolated
    (family : Finset ℕ) :
    2 * weightedDivisorMass family - weightedDyadicPairMass family ≤
      weightedDyadicIsolatedMass family := by
  linarith [two_mul_weightedDivisorMass_le_pair_add_isolated family]

end

end Erdos896.Ford
