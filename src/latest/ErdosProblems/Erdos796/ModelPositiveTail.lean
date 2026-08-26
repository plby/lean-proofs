import ErdosProblems.Erdos796.GammaFinite
import ErdosProblems.Erdos796.BaselineAsymptotic
import ErdosProblems.Erdos796.ModelScoreExcess

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Uniform control of the positive cofactor tail

This file combines the `5/6`-power multiplicative-Sidon bound with an exact
regrouping of the large-prime buckets on dyadic cofactor intervals.
-/

namespace Erdos796

open Filter Topology
open scoped BigOperators Nat.Prime

/-- Positive part of the cofactor excess. -/
noncomputable def excessPos (U : ℕ → Finset ℕ) (j : ℕ) : ℝ :=
  max (excess U j) 0

theorem excess_le_excessPos (U : ℕ → Finset ℕ) (j : ℕ) :
    excess U j ≤ excessPos U j :=
  le_max_left _ _

theorem excessPos_nonneg (U : ℕ → Finset ℕ) (j : ℕ) :
    0 ≤ excessPos U j :=
  le_max_right _ _

/-- The half-open dyadic cofactor block `[K,2K)`. -/
def dyadicCofactorBlock (K : ℕ) : Finset ℕ :=
  Finset.Ico K (2 * K)

/-- Large primes whose cofactor belongs to `[K,2K)`. -/
def dyadicBlockPrimes (n K : ℕ) : Finset ℕ :=
  (largePrimes n).filter fun q => n / q ∈ dyadicCofactorBlock K

@[simp] theorem mem_dyadicBlockPrimes {n K q : ℕ} :
    q ∈ dyadicBlockPrimes n K ↔
      q ∈ largePrimes n ∧ n / q ∈ dyadicCofactorBlock K := by
  exact Finset.mem_filter

/-- One bucket is the corresponding quotient fibre of `largePrimes`. -/
theorem bucketCount_eq_card_quotientFiber (n j : ℕ) :
    bucketCount n j =
      ((largePrimes n).filter fun q => n / q = j).card := by
  simp only [bucketCount, largePrimes]
  congr 1
  ext q
  simp [and_assoc, and_left_comm, and_comm]

/-- Exact regrouping of all bucket counts in a dyadic block. -/
theorem sum_bucketCount_dyadic_eq_card (n K : ℕ) :
    (∑ j ∈ dyadicCofactorBlock K, bucketCount n j) =
      (dyadicBlockPrimes n K).card := by
  classical
  let S := dyadicBlockPrimes n K
  have hmaps : ∀ q ∈ S, n / q ∈ dyadicCofactorBlock K := by
    intro q hq
    exact (Finset.mem_filter.mp hq).2
  calc
    ∑ j ∈ dyadicCofactorBlock K, bucketCount n j =
        ∑ j ∈ dyadicCofactorBlock K,
          ∑ q ∈ S with n / q = j, 1 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [bucketCount_eq_card_quotientFiber]
      simp only [Finset.sum_const, smul_eq_mul, mul_one]
      apply congrArg Finset.card
      apply Finset.ext
      intro q
      constructor
      · intro hq
        have hq' := Finset.mem_filter.mp hq
        apply Finset.mem_filter.mpr
        refine ⟨?_, hq'.2⟩
        show q ∈ S
        exact mem_dyadicBlockPrimes.mpr
          ⟨hq'.1, by simpa [hq'.2] using! hj⟩
      · intro hq
        have hq' := Finset.mem_filter.mp hq
        have hS : q ∈ dyadicBlockPrimes n K := by exact hq'.1
        exact Finset.mem_filter.mpr
          ⟨(mem_dyadicBlockPrimes.mp hS).1, hq'.2⟩
    _ = ∑ q ∈ S, 1 :=
      Finset.sum_fiberwise_of_maps_to' hmaps (fun _ => 1)
    _ = S.card := by simp
    _ = (dyadicBlockPrimes n K).card := rfl

/-- Every prime occurring in the `K`-block is at most `n/K`. -/
theorem dyadicBlockPrimes_subset_primesLE {n K : ℕ} (hK : 0 < K) :
    dyadicBlockPrimes n K ⊆ Nat.primesLE (n / K) := by
  intro q hq
  have hq' := Finset.mem_filter.mp hq
  have hlarge := mem_largePrimes.mp hq'.1
  have hblock : K ≤ n / q := (Finset.mem_Ico.mp hq'.2).1
  have hmul : K * q ≤ n :=
    (Nat.le_div_iff_mul_le hlarge.2.2.pos).mp hblock
  have hqle : q ≤ n / K :=
    (Nat.le_div_iff_mul_le hK).mpr (by simpa [Nat.mul_comm] using! hmul)
  exact Nat.mem_primesLE.mpr ⟨hqle, hlarge.2.2⟩

/-- Consequently the total number of primes in one cofactor block is at most
`π(n/K)`. -/
theorem sum_bucketCount_dyadic_le_primeCounting {n K : ℕ} (hK : 0 < K) :
    (∑ j ∈ dyadicCofactorBlock K, bucketCount n j) ≤
      Nat.primeCounting (n / K) := by
  rw [sum_bucketCount_dyadic_eq_card]
  simpa only [Nat.primesLE_card_eq_primeCounting] using!
    Finset.card_le_card (dyadicBlockPrimes_subset_primesLE hK)

/-- Real positive contribution of one dyadic cofactor block. -/
noncomputable def dyadicPositiveBlock
    (n K : ℕ) (U : ℕ → Finset ℕ) : ℝ :=
  ∑ j ∈ dyadicCofactorBlock K,
    (bucketCount n j : ℝ) * excessPos U j

theorem dyadicPositiveBlock_nonneg
    (n K : ℕ) (U : ℕ → Finset ℕ) :
    0 ≤ dyadicPositiveBlock n K U := by
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (by positivity) (excessPos_nonneg U j)

/-- The explicit Sidon estimate also bounds the positive part of the excess. -/
theorem compatible_excessPos_le_sidonMajorant
    {U : ℕ → Finset ℕ} (hU : Compatible U) {j : ℕ} (hj : 8 ≤ j) :
    excessPos U j ≤ sidonMajorant j := by
  apply max_le
  · exact (SidonCardBound.compatible_fiber_excess_le hU hj).trans
      (explicitSidonMajorant_le_sidonMajorant (by omega))
  · exact sidonMajorant_nonneg j

/-- On `[K,2K)`, the positive excess is at most `6 K^(5/6)`. -/
theorem compatible_excessPos_le_on_dyadicBlock
    {U : ℕ → Finset ℕ} (hU : Compatible U) {K j : ℕ}
    (hK : 8 ≤ K) (hj : j ∈ dyadicCofactorBlock K) :
    excessPos U j ≤ 6 * (K : ℝ) ^ (5 / 6 : ℝ) := by
  have hjBounds := Finset.mem_Ico.mp hj
  have hj8 : 8 ≤ j := hK.trans hjBounds.1
  have hjle : j ≤ 2 * K := hjBounds.2.le
  have hfirst : excessPos U j ≤ 3 * (j : ℝ) ^ (5 / 6 : ℝ) := by
    simpa [sidonMajorant] using! compatible_excessPos_le_sidonMajorant hU hj8
  have hmono :
      (j : ℝ) ^ (5 / 6 : ℝ) ≤
        ((2 * K : ℕ) : ℝ) ^ (5 / 6 : ℝ) := by
    apply Real.rpow_le_rpow
    · positivity
    · exact_mod_cast hjle
    · norm_num
  have htwo : (2 : ℝ) ^ (5 / 6 : ℝ) ≤ 2 :=
    Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have hKpow : 0 ≤ (K : ℝ) ^ (5 / 6 : ℝ) := by positivity
  calc
    excessPos U j ≤ 3 * (j : ℝ) ^ (5 / 6 : ℝ) := hfirst
    _ ≤ 3 * ((2 * K : ℕ) : ℝ) ^ (5 / 6 : ℝ) := by gcongr
    _ = 3 * ((2 : ℝ) ^ (5 / 6 : ℝ) *
        (K : ℝ) ^ (5 / 6 : ℝ)) := by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      rw [Real.mul_rpow (by norm_num) (by positivity)]
    _ ≤ 6 * (K : ℝ) ^ (5 / 6 : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_right htwo hKpow]

/-- Dyadic block estimate: the exact regrouping saves a full factor `K` and
produces the exponent needed for a summable geometric tail. -/
theorem dyadicPositiveBlock_le
    {U : ℕ → Finset ℕ} (hU : Compatible U) {n K : ℕ} (hK : 8 ≤ K) :
    dyadicPositiveBlock n K U ≤
      6 * (Nat.primeCounting (n / K) : ℝ) *
        (K : ℝ) ^ (5 / 6 : ℝ) := by
  let C : ℝ := 6 * (K : ℝ) ^ (5 / 6 : ℝ)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hpoint : ∀ j ∈ dyadicCofactorBlock K,
      (bucketCount n j : ℝ) * excessPos U j ≤
        (bucketCount n j : ℝ) * C := by
    intro j hj
    exact mul_le_mul_of_nonneg_left
      (by simpa [C] using! compatible_excessPos_le_on_dyadicBlock hU hK hj)
      (by positivity)
  have hsum : dyadicPositiveBlock n K U ≤
      (∑ j ∈ dyadicCofactorBlock K, (bucketCount n j : ℝ)) * C := by
    unfold dyadicPositiveBlock
    calc
      (∑ j ∈ dyadicCofactorBlock K,
          (bucketCount n j : ℝ) * excessPos U j) ≤
          ∑ j ∈ dyadicCofactorBlock K,
            (bucketCount n j : ℝ) * C :=
        Finset.sum_le_sum hpoint
      _ = (∑ j ∈ dyadicCofactorBlock K,
          (bucketCount n j : ℝ)) * C := by
        rw [Finset.sum_mul]
  have hcountNat := sum_bucketCount_dyadic_le_primeCounting
    (n := n) (K := K) (by omega)
  have hcount :
      (∑ j ∈ dyadicCofactorBlock K, (bucketCount n j : ℝ)) ≤
        (Nat.primeCounting (n / K) : ℝ) := by
    exact_mod_cast hcountNat
  calc
    dyadicPositiveBlock n K U ≤
        (∑ j ∈ dyadicCofactorBlock K,
          (bucketCount n j : ℝ)) * C := hsum
    _ ≤ (Nat.primeCounting (n / K) : ℝ) * C :=
      mul_le_mul_of_nonneg_right hcount hC
    _ = 6 * (Nat.primeCounting (n / K) : ℝ) *
        (K : ℝ) ^ (5 / 6 : ℝ) := by
      dsimp [C]
      ring

/-- Ratio of successive `K^(-1/6)` bounds under dyadic dilation. -/
noncomputable def dyadicDecayRatio : ℝ :=
  (2 : ℝ) ^ (-(1 / 6 : ℝ))

theorem dyadicDecayRatio_nonneg : 0 ≤ dyadicDecayRatio := by
  rw [dyadicDecayRatio]
  positivity

theorem dyadicDecayRatio_lt_one : dyadicDecayRatio < 1 := by
  rw [dyadicDecayRatio]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

/-- A finite dyadic `(-1/6)`-power sum is bounded by its convergent geometric
series. -/
theorem sum_dyadic_neg_one_sixth_le (K R : ℕ) (hK : 0 < K) :
    (∑ r ∈ Finset.range R,
        (((2 ^ r) * K : ℕ) : ℝ) ^ (-(1 / 6 : ℝ))) ≤
      (K : ℝ) ^ (-(1 / 6 : ℝ)) *
        (1 - dyadicDecayRatio)⁻¹ := by
  have hterm : ∀ r : ℕ,
      ((((2 ^ r) * K : ℕ) : ℝ) ^ (-(1 / 6 : ℝ))) =
        (K : ℝ) ^ (-(1 / 6 : ℝ)) * dyadicDecayRatio ^ r := by
    intro r
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [Real.mul_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)]
    rw [dyadicDecayRatio]
    ring
  rw [Finset.sum_congr rfl (fun r _ => hterm r), ← Finset.mul_sum]
  have hsummable : Summable (fun r : ℕ => dyadicDecayRatio ^ r) :=
    summable_geometric_of_lt_one dyadicDecayRatio_nonneg dyadicDecayRatio_lt_one
  have hfinite :
      (∑ r ∈ Finset.range R, dyadicDecayRatio ^ r) ≤
        ∑' r : ℕ, dyadicDecayRatio ^ r :=
    hsummable.sum_le_tsum (Finset.range R)
      (fun r _ => pow_nonneg dyadicDecayRatio_nonneg r)
  calc
    (K : ℝ) ^ (-(1 / 6 : ℝ)) *
        ∑ r ∈ Finset.range R, dyadicDecayRatio ^ r ≤
      (K : ℝ) ^ (-(1 / 6 : ℝ)) *
        ∑' r : ℕ, dyadicDecayRatio ^ r := by
          gcongr
    _ = (K : ℝ) ^ (-(1 / 6 : ℝ)) *
        (1 - dyadicDecayRatio)⁻¹ := by
      rw [tsum_geometric_of_lt_one dyadicDecayRatio_nonneg
        dyadicDecayRatio_lt_one]

/-- A scale-compatible prime-count estimate converts the block theorem into
a `K^(-1/6)` estimate. -/
theorem dyadicPositiveBlock_le_of_scaled_primeCounting
    {U : ℕ → Finset ℕ} (hU : Compatible U) {n K : ℕ} (hK : 8 ≤ K)
    {C : ℝ}
    (hprime : (Nat.primeCounting (n / K) : ℝ) ≤
      C * secondOrderScale n / (K : ℝ)) :
    dyadicPositiveBlock n K U ≤
      6 * C * secondOrderScale n *
        (K : ℝ) ^ (-(1 / 6 : ℝ)) := by
  have hbasic := dyadicPositiveBlock_le hU hK (n := n)
  have hKpos : (0 : ℝ) < (K : ℝ) := by positivity
  have hKpow : 0 ≤ (K : ℝ) ^ (5 / 6 : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hprime hKpow
  calc
    dyadicPositiveBlock n K U ≤
        6 * (Nat.primeCounting (n / K) : ℝ) *
          (K : ℝ) ^ (5 / 6 : ℝ) := hbasic
    _ ≤ 6 * (C * secondOrderScale n / (K : ℝ)) *
          (K : ℝ) ^ (5 / 6 : ℝ) := by nlinarith
    _ = 6 * C * secondOrderScale n *
          (K : ℝ) ^ (-(1 / 6 : ℝ)) := by
      rw [show -(1 / 6 : ℝ) = 5 / 6 - 1 by norm_num,
        Real.rpow_sub_one hKpos.ne']
      field_simp

/-- Finite geometric summation of the dyadic block bounds.  This theorem is
deliberately stated with an abstract prime-count estimate so the combinatorial
and Chebyshev inputs remain separate. -/
theorem sum_dyadicPositiveBlock_le_of_scaled_primeCounting
    {U : ℕ → Finset ℕ} (hU : Compatible U)
    {n K R : ℕ} (hK : 8 ≤ K) {C : ℝ} (hC : 0 ≤ C)
    (hscale : 0 ≤ secondOrderScale n)
    (hprime : ∀ r < R,
      (Nat.primeCounting (n / ((2 ^ r) * K)) : ℝ) ≤
        C * secondOrderScale n / (((2 ^ r) * K : ℕ) : ℝ)) :
    (∑ r ∈ Finset.range R,
        dyadicPositiveBlock n ((2 ^ r) * K) U) ≤
      6 * C * secondOrderScale n *
        ((K : ℝ) ^ (-(1 / 6 : ℝ)) *
          (1 - dyadicDecayRatio)⁻¹) := by
  have hpoint : ∀ r ∈ Finset.range R,
      dyadicPositiveBlock n ((2 ^ r) * K) U ≤
        6 * C * secondOrderScale n *
          (((2 ^ r) * K : ℕ) : ℝ) ^ (-(1 / 6 : ℝ)) := by
    intro r hr
    have hKr : 8 ≤ (2 ^ r) * K := by
      have hpowpos : 0 < 2 ^ r := by positivity
      nlinarith
    exact dyadicPositiveBlock_le_of_scaled_primeCounting hU hKr
      (hprime r (Finset.mem_range.mp hr))
  have hfactor : 0 ≤ 6 * C * secondOrderScale n := by positivity
  calc
    (∑ r ∈ Finset.range R,
        dyadicPositiveBlock n ((2 ^ r) * K) U) ≤
      ∑ r ∈ Finset.range R,
        6 * C * secondOrderScale n *
          (((2 ^ r) * K : ℕ) : ℝ) ^ (-(1 / 6 : ℝ)) :=
      Finset.sum_le_sum hpoint
    _ = (6 * C * secondOrderScale n) *
        ∑ r ∈ Finset.range R,
          (((2 ^ r) * K : ℕ) : ℝ) ^ (-(1 / 6 : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ (6 * C * secondOrderScale n) *
        ((K : ℝ) ^ (-(1 / 6 : ℝ)) *
          (1 - dyadicDecayRatio)⁻¹) := by
      exact mul_le_mul_of_nonneg_left
        (sum_dyadic_neg_one_sixth_le K R (by omega)) hfactor
    _ = 6 * C * secondOrderScale n *
        ((K : ℝ) ^ (-(1 / 6 : ℝ)) *
          (1 - dyadicDecayRatio)⁻¹) := rfl

/-- Constant in the uniform Chebyshev estimate over all cofactor scales up
to `√n`.  The factor three comes from the robust floor-square-root logarithm
comparison already proved in `BaselineAsymptotic`. -/
noncomputable def tailChebyshevConstant : ℝ :=
  3 * (Real.log 4 + 1)

theorem tailChebyshevConstant_nonneg : 0 ≤ tailChebyshevConstant := by
  rw [tailChebyshevConstant]
  positivity

/-- Chebyshev's theorem, uniformly for every quotient `n/K` with
`1 ≤ K ≤ √n`, in exactly the scale required by the dyadic sum. -/
theorem eventually_uniform_primeCounting_natDiv :
    ∀ᶠ n : ℕ in atTop, ∀ K : ℕ, 0 < K → K ≤ n.sqrt →
      (Nat.primeCounting (n / K) : ℝ) ≤
        tailChebyshevConstant * secondOrderScale n / (K : ℝ) := by
  have hcheb :=
    Chebyshev.eventually_primeCounting_le (show (0 : ℝ) < 1 by norm_num)
  rcases (eventually_atTop.1 hcheb) with ⟨x₀, hx₀⟩
  have hsqrtLarge : ∀ᶠ n : ℕ in atTop, x₀ ≤ (n.sqrt : ℝ) :=
    tendsto_natSqrtCast_atTop.eventually (eventually_ge_atTop x₀)
  filter_upwards [eventually_ge_atTop 9, hsqrtLarge,
    eventually_log_le_three_log_sqrt] with n hn hsqrtX hlog K hK hKsqrt
  let m := n / K
  have hsqrt3 : 3 ≤ n.sqrt := by
    rw [Nat.le_sqrt]
    omega
  have hmge : n.sqrt ≤ m := by
    apply (Nat.le_div_iff_mul_le hK).mpr
    have hmul : n.sqrt * K ≤ n.sqrt * n.sqrt :=
      Nat.mul_le_mul_left n.sqrt hKsqrt
    exact hmul.trans (Nat.sqrt_le n)
  have hm3 : 3 ≤ m := hsqrt3.trans hmge
  have hmX : x₀ ≤ (m : ℝ) :=
    hsqrtX.trans (by exact_mod_cast hmge)
  have hpi : (Nat.primeCounting m : ℝ) ≤
      (Real.log 4 + 1) * (m : ℝ) / Real.log (m : ℝ) := by
    simpa using! hx₀ (m : ℝ) hmX
  have hA : 0 ≤ Real.log 4 + 1 := by positivity
  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlogsqrt_le_logm :
      Real.log (n.sqrt : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hmge)
  have hlognm : Real.log (n : ℝ) ≤ 3 * Real.log (m : ℝ) :=
    hlog.trans (mul_le_mul_of_nonneg_left hlogsqrt_le_logm (by norm_num))
  have hratio :
      (m : ℝ) / Real.log (m : ℝ) ≤
        (3 * (m : ℝ)) / Real.log (n : ℝ) := by
    have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := by positivity
    rw [div_le_div_iff₀ hlogm hlogn]
    nlinarith [mul_le_mul_of_nonneg_left hlognm hmnonneg]
  have hmK : m * K ≤ n := by
    simpa [m] using! Nat.div_mul_le_self n K
  have hmReal : (m : ℝ) ≤ (n : ℝ) / (K : ℝ) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (K : ℝ))]
    exact_mod_cast hmK
  calc
    (Nat.primeCounting (n / K) : ℝ) =
        (Nat.primeCounting m : ℝ) := rfl
    _ ≤ (Real.log 4 + 1) * (m : ℝ) / Real.log (m : ℝ) := hpi
    _ = (Real.log 4 + 1) *
        ((m : ℝ) / Real.log (m : ℝ)) := by ring
    _ ≤ (Real.log 4 + 1) *
        ((3 * (m : ℝ)) / Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hratio hA
    _ ≤ (Real.log 4 + 1) *
        ((3 * ((n : ℝ) / (K : ℝ))) / Real.log (n : ℝ)) := by
      gcongr
    _ = tailChebyshevConstant * secondOrderScale n / (K : ℝ) := by
      rw [tailChebyshevConstant, secondOrderScale]
      field_simp

/-- Uniform constant left after summing the dyadic geometric series. -/
noncomputable def positiveTailConstant : ℝ :=
  6 * tailChebyshevConstant * (1 - dyadicDecayRatio)⁻¹

theorem positiveTailConstant_nonneg : 0 ≤ positiveTailConstant := by
  have hden : 0 < 1 - dyadicDecayRatio :=
    sub_pos.mpr dyadicDecayRatio_lt_one
  rw [positiveTailConstant]
  exact mul_nonneg (mul_nonneg (by norm_num) tailChebyshevConstant_nonneg)
    (le_of_lt (inv_pos.mpr hden))

/-- Eventual uniform finite-tail estimate.  The condition on the last line
only says that every dyadic block under consideration lies in the actual
cofactor range `[1,√n]`. -/
theorem eventually_sum_dyadicPositiveBlock_le :
    ∀ᶠ n : ℕ in atTop,
      ∀ (U : ℕ → Finset ℕ), Compatible U →
      ∀ K R : ℕ, 8 ≤ K →
        (∀ r < R, (2 ^ r) * K ≤ n.sqrt) →
        (∑ r ∈ Finset.range R,
            dyadicPositiveBlock n ((2 ^ r) * K) U) ≤
          positiveTailConstant * secondOrderScale n *
            (K : ℝ) ^ (-(1 / 6 : ℝ)) := by
  filter_upwards [eventually_uniform_primeCounting_natDiv,
    eventually_ge_atTop 9] with n huniform hn U hU K R hK hblocks
  have hscale : 0 ≤ secondOrderScale n := by
    rw [secondOrderScale]
    positivity
  have hsum := sum_dyadicPositiveBlock_le_of_scaled_primeCounting hU hK
    tailChebyshevConstant_nonneg hscale
    (fun r hr => huniform ((2 ^ r) * K) (by positivity) (hblocks r hr))
  calc
    (∑ r ∈ Finset.range R,
        dyadicPositiveBlock n ((2 ^ r) * K) U) ≤
      6 * tailChebyshevConstant * secondOrderScale n *
        ((K : ℝ) ^ (-(1 / 6 : ℝ)) *
          (1 - dyadicDecayRatio)⁻¹) := hsum
    _ = positiveTailConstant * secondOrderScale n *
        (K : ℝ) ^ (-(1 / 6 : ℝ)) := by
      rw [positiveTailConstant]
      ring

/-- The same estimate after normalization by `n/log n`. -/
theorem eventually_normalized_sum_dyadicPositiveBlock_le :
    ∀ᶠ n : ℕ in atTop,
      ∀ (U : ℕ → Finset ℕ), Compatible U →
      ∀ K R : ℕ, 8 ≤ K →
        (∀ r < R, (2 ^ r) * K ≤ n.sqrt) →
        (∑ r ∈ Finset.range R,
            dyadicPositiveBlock n ((2 ^ r) * K) U) /
              secondOrderScale n ≤
          positiveTailConstant *
            (K : ℝ) ^ (-(1 / 6 : ℝ)) := by
  filter_upwards [eventually_sum_dyadicPositiveBlock_le,
    eventually_ge_atTop 9] with n hsum hn U hU K R hK hblocks
  have hscale : 0 < secondOrderScale n := by
    rw [secondOrderScale]
    exact div_pos (by positivity)
      (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
  rw [div_le_iff₀ hscale]
  have h := hsum U hU K R hK hblocks
  nlinarith

/-- The uniform normalized dyadic-tail majorant tends to zero as the initial
cofactor cutoff tends to infinity. -/
theorem positiveTailMajorant_tendsto_zero :
    Tendsto
      (fun K : ℕ => positiveTailConstant *
        (K : ℝ) ^ (-(1 / 6 : ℝ)))
      atTop (nhds 0) := by
  have hpow : Tendsto
      (fun K : ℕ => (K : ℝ) ^ (-(1 / 6 : ℝ)))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 6 by norm_num)).comp
      tendsto_natCast_atTop_atTop
  simpa using! tendsto_const_nhds.mul hpow

/-- The first `R` dyadic blocks are exactly the single interval
`[K,2^R K)`.  Thus the block estimates genuinely control a contiguous tail,
with no gaps or repeated cofactors. -/
theorem sum_dyadicPositiveBlock_eq_interval
    (n K R : ℕ) (U : ℕ → Finset ℕ) :
    (∑ r ∈ Finset.range R,
        dyadicPositiveBlock n ((2 ^ r) * K) U) =
      ∑ j ∈ Finset.Ico K ((2 ^ R) * K),
        (bucketCount n j : ℝ) * excessPos U j := by
  induction R with
  | zero => simp
  | succ R ih =>
      rw [Finset.sum_range_succ, ih]
      rw [show dyadicPositiveBlock n ((2 ^ R) * K) U =
          ∑ j ∈ Finset.Ico ((2 ^ R) * K) ((2 ^ (R + 1)) * K),
            (bucketCount n j : ℝ) * excessPos U j by
        rw [dyadicPositiveBlock, dyadicCofactorBlock, pow_succ]
        congr 2
        simp [Nat.mul_comm, Nat.mul_left_comm]]
      rw [Finset.sum_Ico_consecutive]
      · have hpow : (1 : ℕ) ≤ 2 ^ R := one_le_pow₀ (by omega)
        simpa using! Nat.mul_le_mul_right K hpow
      · rw [pow_succ]
        have hdouble : 2 ^ R ≤ (2 ^ R) * 2 := by omega
        exact Nat.mul_le_mul_right K hdouble

/-- Every positive starting scale admits a minimal finite dyadic cover. -/
theorem exists_dyadic_cover (K x : ℕ) (hK : 0 < K) :
    ∃ R : ℕ, (∀ r < R, (2 ^ r) * K ≤ x) ∧ x < (2 ^ R) * K := by
  have hexPow : ∃ R : ℕ, x < 2 ^ R :=
    pow_unbounded_of_one_lt x (by norm_num : (1 : ℕ) < 2)
  have hex : ∃ R : ℕ, x < (2 ^ R) * K := by
    obtain ⟨R, hR⟩ := hexPow
    have hmul : 2 ^ R ≤ (2 ^ R) * K := by
      have hKone : 1 ≤ K := hK
      simpa using! Nat.mul_le_mul_left (2 ^ R) hKone
    exact ⟨R, hR.trans_le hmul⟩
  let R := Nat.find hex
  refine ⟨R, ?_, Nat.find_spec hex⟩
  intro r hr
  exact Nat.le_of_not_gt (Nat.find_min hex hr)

/-- Positive part of the complete finite cofactor tail `[K,√n]`. -/
noncomputable def positiveModelTail
    (n K : ℕ) (U : ℕ → Finset ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico K (n.sqrt + 1),
    (bucketCount n j : ℝ) * excessPos U j

theorem positiveModelTail_nonneg
    (n K : ℕ) (U : ℕ → Finset ℕ) :
    0 ≤ positiveModelTail n K U := by
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (by positivity) (excessPos_nonneg U j)

/-- Interval form of the normalized finite dyadic estimate. -/
theorem eventually_normalized_dyadicInterval_le :
    ∀ᶠ n : ℕ in atTop,
      ∀ (U : ℕ → Finset ℕ), Compatible U →
      ∀ K R : ℕ, 8 ≤ K →
        (∀ r < R, (2 ^ r) * K ≤ n.sqrt) →
        (∑ j ∈ Finset.Ico K ((2 ^ R) * K),
            (bucketCount n j : ℝ) * excessPos U j) /
              secondOrderScale n ≤
          positiveTailConstant *
            (K : ℝ) ^ (-(1 / 6 : ℝ)) := by
  filter_upwards [eventually_normalized_sum_dyadicPositiveBlock_le] with
    n hn U hU K R hK hblocks
  rw [← sum_dyadicPositiveBlock_eq_interval]
  exact hn U hU K R hK hblocks

/-- Full uniform positive-tail estimate.  This is the form needed in the
upper-limit argument: after normalization, the bound depends only on the
initial cutoff `K`, not on `n` or on the compatible family. -/
theorem eventually_normalized_positiveModelTail_le :
    ∀ᶠ n : ℕ in atTop,
      ∀ (U : ℕ → Finset ℕ), Compatible U →
      ∀ K : ℕ, 8 ≤ K →
        positiveModelTail n K U / secondOrderScale n ≤
          positiveTailConstant *
            (K : ℝ) ^ (-(1 / 6 : ℝ)) := by
  filter_upwards [eventually_normalized_dyadicInterval_le,
    eventually_ge_atTop 9] with n hinterval hn U hU K hK
  have hscale : 0 < secondOrderScale n := by
    rw [secondOrderScale]
    exact div_pos (by positivity)
      (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
  by_cases hKsqrt : K ≤ n.sqrt
  · obtain ⟨R, hblocks, hcover⟩ := exists_dyadic_cover K n.sqrt (by omega)
    have hsub : Finset.Ico K (n.sqrt + 1) ⊆
        Finset.Ico K ((2 ^ R) * K) := by
      intro j hj
      have hj' := Finset.mem_Ico.mp hj
      exact Finset.mem_Ico.mpr ⟨hj'.1, hj'.2.trans_le (by omega)⟩
    have hsumle : positiveModelTail n K U ≤
        ∑ j ∈ Finset.Ico K ((2 ^ R) * K),
          (bucketCount n j : ℝ) * excessPos U j := by
      unfold positiveModelTail
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun j _ _ => mul_nonneg (by positivity) (excessPos_nonneg U j))
    have hdivle : positiveModelTail n K U / secondOrderScale n ≤
        (∑ j ∈ Finset.Ico K ((2 ^ R) * K),
          (bucketCount n j : ℝ) * excessPos U j) /
            secondOrderScale n :=
      (div_le_div_iff_of_pos_right hscale).mpr hsumle
    exact hdivle.trans (hinterval U hU K R hK hblocks)
  · have hend : n.sqrt + 1 ≤ K := by omega
    rw [positiveModelTail, Finset.Ico_eq_empty_of_le hend]
    simp only [Finset.sum_empty, zero_div]
    exact mul_nonneg positiveTailConstant_nonneg (by positivity)

/-- Epsilon formulation of uniform positive-tail decay.  The same cutoff
works simultaneously for all sufficiently large `n` and every compatible
cofactor family. -/
theorem uniform_positiveModelTail_eventually_lt
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K₀ : ℕ, 8 ≤ K₀ ∧ ∀ K ≥ K₀,
      ∀ᶠ n : ℕ in atTop,
        ∀ (U : ℕ → Finset ℕ), Compatible U →
          positiveModelTail n K U / secondOrderScale n < ε := by
  have hIio : Set.Iio ε ∈ nhds (0 : ℝ) := Iio_mem_nhds hε
  have hmajorant : ∀ᶠ K : ℕ in atTop,
      positiveTailConstant * (K : ℝ) ^ (-(1 / 6 : ℝ)) < ε :=
    positiveTailMajorant_tendsto_zero.eventually hIio
  rcases eventually_atTop.1 hmajorant with ⟨K₁, hK₁⟩
  refine ⟨max 8 K₁, le_max_left _ _, ?_⟩
  intro K hK
  have h8K : 8 ≤ K := (le_max_left 8 K₁).trans hK
  have hKmajorant :
      positiveTailConstant * (K : ℝ) ^ (-(1 / 6 : ℝ)) < ε :=
    hK₁ K ((le_max_right 8 K₁).trans hK)
  filter_upwards [eventually_normalized_positiveModelTail_le] with n hn U hU
  exact (hn U hU K h8K).trans_lt hKmajorant

end Erdos796
