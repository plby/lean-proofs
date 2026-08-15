/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.PrimeReciprocalBound

/-!
# Logarithmic-depth Brun bounds on the refined progression

This module transfers the uniform dyadic prime-reciprocal estimate to the
exact refined sieve used in Section 6.  For fixed `k`, one odd depth of size
`O(log log z)` controls the main-term tail at every endpoint, while the
finite CRT remainder remains explicit.
-/

namespace Erdos387

open scoped BigOperators

namespace CoverBPZ

/-- The neighboring even truncation used for upper-bound sieves. -/
def refinedEvenBrunDepth (a b z : ℕ) : ℕ :=
  PrimeReciprocal.logarithmicBrunDepth a b z + 1

theorem refinedEvenBrunDepth_even (a b z : ℕ) :
    Even (refinedEvenBrunDepth a b z) := by
  obtain ⟨r, hr⟩ := PrimeReciprocal.logarithmicBrunDepth_odd a b z
  refine ⟨r + 1, ?_⟩
  unfold refinedEvenBrunDepth
  omega

/-- Every prime factor left in the refined sieve lies in `(k,z)`. -/
theorem refinedSievePrimeFactor_bounds
    {B K z : ℕ} (S : BPZSection6Input B K)
    {p : ℕ} (hp : p ∈ (refinedSievePrimeProduct S z).primeFactors) :
    p.Prime ∧ S.k < p ∧ p < z := by
  have hpPrime := Nat.prime_of_mem_primeFactors hp
  have hpDvd := Nat.dvd_of_mem_primeFactors hp
  have hdata := prime_mem_refinedSievePrimes_of_dvd_product S hpPrime hpDvd
  exact ⟨hpPrime, by have := S.hk3; omega, hdata.2.2⟩

/-- Fixed natural constants give the half-Euler tail estimate for the
refined sieve at every endpoint. -/
theorem exists_refined_brunTail_le_half_logarithmicDepth
    {Cπ : ℝ} (hCπ : 0 < Cπ)
    (hcheb : ∀ t : ℕ, 2 ≤ t →
      (Nat.primeCounting t : ℝ) ≤ Cπ * t / Real.log t)
    {B K : ℕ} (S : BPZSection6Input B K) :
    ∃ a b : ℕ, ∀ z : ℕ,
      2 * brunSubsetTail (refinedSievePrimeProduct S z).primeFactors
            (fun p => binomialSieveNu S.k p)
            (PrimeReciprocal.logarithmicBrunDepth a b z) ≤
        finiteEulerProduct (refinedSievePrimeProduct S z).primeFactors
          (fun p => binomialSieveNu S.k p) := by
  obtain ⟨a, b, hab⟩ :=
    PrimeReciprocal.exists_logarithmicBrunDepth_parameters Cπ S.k
  refine ⟨a, b, ?_⟩
  intro z
  apply PrimeReciprocal.binomial_brunTail_le_half_of_exp_log_log_two_bound
    hCπ hcheb (by have := S.hk3; omega)
      (refinedSievePrimeProduct S z).primeFactors
  · intro p hp
    exact refinedSievePrimeFactor_bounds S hp
  · exact hab z

/-- The adjacent even depth obeys the same half-Euler tail estimate. -/
theorem exists_refined_brunTail_le_half_evenDepth
    {Cπ : ℝ} (hCπ : 0 < Cπ)
    (hcheb : ∀ t : ℕ, 2 ≤ t →
      (Nat.primeCounting t : ℝ) ≤ Cπ * t / Real.log t)
    {B K : ℕ} (S : BPZSection6Input B K) :
    ∃ a b : ℕ, ∀ z : ℕ,
      2 * brunSubsetTail (refinedSievePrimeProduct S z).primeFactors
            (fun p => binomialSieveNu S.k p)
            (refinedEvenBrunDepth a b z) ≤
        finiteEulerProduct (refinedSievePrimeProduct S z).primeFactors
          (fun p => binomialSieveNu S.k p) := by
  obtain ⟨a, b, hab⟩ :=
    PrimeReciprocal.exists_logarithmicBrunDepth_parameters Cπ S.k
  refine ⟨a, b, ?_⟩
  intro z
  apply PrimeReciprocal.binomial_brunTail_le_half_of_exp_log_log_two_bound
    hCπ hcheb (by have := S.hk3; omega)
      (refinedSievePrimeProduct S z).primeFactors
  · intro p hp
    exact refinedSievePrimeFactor_bounds S hp
  · exact (hab z).trans (pow_le_pow_right₀ (by norm_num) (by
      unfold refinedEvenBrunDepth
      omega))

/-- One choice of logarithmic depth simultaneously controls the omitted
tail and supplies a reciprocal lower envelope for the Euler product. -/
theorem exists_refined_tail_and_euler_reciprocal_depth
    {Cπ : ℝ} (hCπ : 0 < Cπ)
    (hcheb : ∀ t : ℕ, 2 ≤ t →
      (Nat.primeCounting t : ℝ) ≤ Cπ * t / Real.log t)
    {B K : ℕ} (S : BPZSection6Input B K) :
    ∃ a b : ℕ, ∀ z : ℕ,
      2 * brunSubsetTail (refinedSievePrimeProduct S z).primeFactors
            (fun p => binomialSieveNu S.k p)
            (PrimeReciprocal.logarithmicBrunDepth a b z) ≤
          finiteEulerProduct (refinedSievePrimeProduct S z).primeFactors
            (fun p => binomialSieveNu S.k p) ∧
      2 * brunSubsetTail (refinedSievePrimeProduct S z).primeFactors
            (fun p => binomialSieveNu S.k p)
            (refinedEvenBrunDepth a b z) ≤
          finiteEulerProduct (refinedSievePrimeProduct S z).primeFactors
            (fun p => binomialSieveNu S.k p) ∧
      1 ≤ (2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b z *
          finiteEulerProduct (refinedSievePrimeProduct S z).primeFactors
            (fun p => binomialSieveNu S.k p) := by
  obtain ⟨a, b, hab⟩ :=
    PrimeReciprocal.exists_logarithmicBrunDepth_parameters Cπ S.k
  refine ⟨a, b, ?_⟩
  intro z
  let L := PrimeReciprocal.logarithmicBrunDepth a b z
  let H := (4 * S.k : ℝ) ^ (2 * S.k + 1) *
    Real.exp ((6 * S.k : ℝ) * (2 * Cπ / Real.log 2) *
      (Nat.log 2 (Nat.log 2 z) + 2))
  let V := finiteEulerProduct (refinedSievePrimeProduct S z).primeFactors
    (fun p => binomialSieveNu S.k p)
  have htail :
      2 * brunSubsetTail (refinedSievePrimeProduct S z).primeFactors
            (fun p => binomialSieveNu S.k p) L ≤ V := by
    apply PrimeReciprocal.binomial_brunTail_le_half_of_exp_log_log_two_bound
      hCπ hcheb (by have := S.hk3; omega)
        (refinedSievePrimeProduct S z).primeFactors
    · intro p hp
      exact refinedSievePrimeFactor_bounds S hp
    · simpa [H, L] using hab z
  have htailEven :
      2 * brunSubsetTail (refinedSievePrimeProduct S z).primeFactors
            (fun p => binomialSieveNu S.k p)
            (refinedEvenBrunDepth a b z) ≤ V := by
    apply PrimeReciprocal.binomial_brunTail_le_half_of_exp_log_log_two_bound
      hCπ hcheb (by have := S.hk3; omega)
        (refinedSievePrimeProduct S z).primeFactors
    · intro p hp
      exact refinedSievePrimeFactor_bounds S hp
    · exact (hab z).trans (pow_le_pow_right₀ (by norm_num) (by
        unfold refinedEvenBrunDepth
        omega))
  have hmoment : 1 ≤ H * V := by
    let P := (refinedSievePrimeProduct S z).primeFactors
    have hP : ∀ p ∈ P, p.Prime ∧ S.k < p ∧ p < z := by
      intro p hp
      exact refinedSievePrimeFactor_bounds S hp
    have hmomentBase :=
      PrimeReciprocal.binomialMomentProduct_le_exp_log_log_two_mul_euler
        hCπ hcheb (by have := S.hk3; omega) P hP
    have hone : 1 ≤ ∏ p ∈ P, (1 + 2 * binomialSieveNu S.k p) := by
      apply Finset.one_le_prod
      intro p hp
      rw [binomialSieveNu_prime (hP p hp).1]
      exact le_add_of_nonneg_right
        (mul_nonneg (by norm_num) (div_nonneg (by positivity) (by
          exact_mod_cast (hP p hp).1.pos.le)))
    exact hone.trans (by simpa [P, H, V] using hmomentBase)
  have hHnonneg : 0 ≤ H := by dsimp [H]; positivity
  have hHpow : H ≤ (2 : ℝ) ^ L := by
    have hp := hab z
    change 2 * H ≤ (2 : ℝ) ^ (L + 1) at hp
    rw [pow_succ] at hp
    nlinarith
  have hVnonneg : 0 ≤ V := by
    dsimp [V, finiteEulerProduct]
    apply Finset.prod_nonneg
    intro p hp
    have hdata := refinedSievePrimeFactor_bounds S hp
    change 0 ≤ 1 - binomialSieveNu S.k p
    rw [binomialSieveNu_prime hdata.1]
    have hpPos : (0 : ℝ) < p := by exact_mod_cast hdata.1.pos
    exact sub_nonneg.mpr ((div_le_one hpPos).mpr
      (by exact_mod_cast hdata.2.1.le))
  refine ⟨by simpa [L, V] using htail,
    by simpa [V] using htailEven, ?_⟩
  exact hmoment.trans (mul_le_mul_of_nonneg_right hHpow hVnonneg)

/-- At the even depth, the upper main sum is nonnegative and at most
three halves of the Euler product. -/
theorem refined_even_brunMainSum_nonneg_and_le
    {Cπ : ℝ} (hCπ : 0 < Cπ)
    (hcheb : ∀ t : ℕ, 2 ≤ t →
      (Nat.primeCounting t : ℝ) ≤ Cπ * t / Real.log t)
    {B K : ℕ} (S : BPZSection6Input B K) :
    ∃ a b : ℕ, ∀ X z : ℕ,
      0 ≤ (refinedBinomialBoundingSieve S X z).mainSum
          (brunUpperWeight (refinedEvenBrunDepth a b z)) ∧
      (refinedBinomialBoundingSieve S X z).mainSum
          (brunUpperWeight (refinedEvenBrunDepth a b z)) ≤
        3 * finiteEulerProduct (refinedSievePrimeProduct S z).primeFactors
          (fun p => binomialSieveNu S.k p) / 2 := by
  obtain ⟨a, b, htail⟩ :=
    exists_refined_brunTail_le_half_evenDepth hCπ hcheb S
  refine ⟨a, b, ?_⟩
  intro X z
  have hwindow := boundingSieve_brunMainSums_half_threeHalves
    (refinedBinomialBoundingSieve S X z)
    (refinedEvenBrunDepth a b z) (htail z)
  refine ⟨?_, hwindow.2⟩
  have hEulerNonneg :
      0 ≤ finiteEulerProduct (refinedSievePrimeProduct S z).primeFactors
        (fun p => binomialSieveNu S.k p) := by
    unfold finiteEulerProduct
    apply Finset.prod_nonneg
    intro p hp
    have hdata := refinedSievePrimeFactor_bounds S hp
    change 0 ≤ 1 - binomialSieveNu S.k p
    rw [binomialSieveNu_prime hdata.1]
    have hpPos : (0 : ℝ) < p := by exact_mod_cast hdata.1.pos
    exact sub_nonneg.mpr ((div_le_one hpPos).mpr
      (by exact_mod_cast hdata.2.1.le))
  change 0 ≤ (refinedBinomialBoundingSieve S X z).mainSum
    (brunLowerWeight (refinedEvenBrunDepth a b z))
  have hEulerNonneg' :
      0 ≤ finiteEulerProduct
        (refinedBinomialBoundingSieve S X z).prodPrimes.primeFactors
        (fun p => (refinedBinomialBoundingSieve S X z).nu p) := by
    simpa [refinedBinomialBoundingSieve] using hEulerNonneg
  linarith [hwindow.1]

/-- The corresponding refined lower and upper Brun main sums lie in the
standard half/three-halves Euler window. -/
theorem refined_brunMainSums_half_threeHalves
    {Cπ : ℝ} (hCπ : 0 < Cπ)
    (hcheb : ∀ t : ℕ, 2 ≤ t →
      (Nat.primeCounting t : ℝ) ≤ Cπ * t / Real.log t)
    {B K : ℕ} (S : BPZSection6Input B K) :
    ∃ a b : ℕ, ∀ X z : ℕ,
      let L := PrimeReciprocal.logarithmicBrunDepth a b z
      finiteEulerProduct (refinedSievePrimeProduct S z).primeFactors
            (fun p => binomialSieveNu S.k p) / 2 ≤
          (refinedBinomialBoundingSieve S X z).mainSum
            (brunLowerWeight L) ∧
        (refinedBinomialBoundingSieve S X z).mainSum
            (brunUpperWeight L) ≤
          3 * finiteEulerProduct (refinedSievePrimeProduct S z).primeFactors
            (fun p => binomialSieveNu S.k p) / 2 := by
  obtain ⟨a, b, htail⟩ :=
    exists_refined_brunTail_le_half_logarithmicDepth hCπ hcheb S
  refine ⟨a, b, ?_⟩
  intro X z
  exact boundingSieve_brunMainSums_half_threeHalves
    (refinedBinomialBoundingSieve S X z)
    (PrimeReciprocal.logarithmicBrunDepth a b z) (htail z)

/-- The discrete moment envelope times the refined Euler product is at
least one.  This gives a crude but uniform reciprocal lower bound for the
main term without invoking Mertens' theorem. -/
theorem one_le_refinedMomentEnvelope_mul_euler
    {Cπ : ℝ} (hCπ : 0 < Cπ)
    (hcheb : ∀ t : ℕ, 2 ≤ t →
      (Nat.primeCounting t : ℝ) ≤ Cπ * t / Real.log t)
    {B K z : ℕ} (S : BPZSection6Input B K) :
    1 ≤ ((4 * S.k : ℝ) ^ (2 * S.k + 1) *
          Real.exp ((6 * S.k : ℝ) * (2 * Cπ / Real.log 2) *
            (Nat.log 2 (Nat.log 2 z) + 2))) *
        finiteEulerProduct (refinedSievePrimeProduct S z).primeFactors
          (fun p => binomialSieveNu S.k p) := by
  let P := (refinedSievePrimeProduct S z).primeFactors
  have hP : ∀ p ∈ P, p.Prime ∧ S.k < p ∧ p < z := by
    intro p hp
    exact refinedSievePrimeFactor_bounds S hp
  have hmoment :=
    PrimeReciprocal.binomialMomentProduct_le_exp_log_log_two_mul_euler
      hCπ hcheb (by have := S.hk3; omega) P hP
  have hone : 1 ≤ ∏ p ∈ P, (1 + 2 * binomialSieveNu S.k p) := by
    apply Finset.one_le_prod
    intro p hp
    rw [binomialSieveNu_prime (hP p hp).1]
    exact le_add_of_nonneg_right
      (mul_nonneg (by norm_num) (div_nonneg (by positivity) (by
        exact_mod_cast (hP p hp).1.pos.le)))
  exact hone.trans (by simpa [P] using hmoment)

/-- Explicit total CRT remainder for the lower refined Brun truncation. -/
theorem refinedBinomialBoundingSieve_brunLowerErrSum_le
    {B K X z L : ℕ} (S : BPZSection6Input B K)
    (hX : S.k ≤ X / 2) (hz : 1 ≤ z) :
    (refinedBinomialBoundingSieve S X z).errSum (brunLowerWeight L) ≤
      (4 : ℝ) * (z ^ L + 1 : ℕ) * (S.k : ℝ) ^ L := by
  let s := refinedBinomialBoundingSieve S X z
  rw [BoundingSieve.errSum]
  calc
    (∑ d ∈ (refinedSievePrimeProduct S z).divisors,
        |brunLowerWeight L d| * |s.rem d|) ≤
        ∑ d ∈ (refinedSievePrimeProduct S z).divisors,
          if d.primeFactors.card ≤ L then
            4 * (S.k : ℝ) ^ L else 0 := by
      apply Finset.sum_le_sum
      intro d hdmem
      by_cases hdL : d.primeFactors.card ≤ L
      · rw [if_pos hdL]
        have hddiv := (Nat.mem_divisors.mp hdmem).1
        have hrem := refinedBinomialBoundingSieve_abs_rem_le S hX hddiv
        calc
          |brunLowerWeight L d| * |s.rem d| ≤ 1 * |s.rem d| := by
            gcongr
            exact abs_brunLowerWeight_le_one L d
          _ ≤ 4 * (S.k : ℝ) ^ d.primeFactors.card := by
            simpa [s] using hrem
          _ ≤ 4 * (S.k : ℝ) ^ L := by
            gcongr
            exact_mod_cast (show 0 < S.k by have := S.hk3; omega)
      · rw [if_neg hdL]
        have hzero : brunLowerWeight L d = 0 := by
          unfold brunLowerWeight
          rw [if_neg]
          simpa [cardDistinctFactors_eq_primeFactors_card] using hdL
        simp [hzero]
    _ = (((refinedSievePrimeProduct S z).divisors.filter fun d =>
          d.primeFactors.card ≤ L).card : ℝ) *
          (4 * (S.k : ℝ) ^ L) := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ (z ^ L + 1 : ℕ) * (4 * (S.k : ℝ) ^ L) := by
      gcongr
      exact_mod_cast card_brunSupport_le (k := 2 * S.k - 1) hz
    _ = (4 : ℝ) * (z ^ L + 1 : ℕ) * (S.k : ℝ) ^ L := by ring

/-- The even refined Brun truncation has the same error bound. -/
theorem refinedBinomialBoundingSieve_brunUpperErrSum_le
    {B K X z L : ℕ} (S : BPZSection6Input B K)
    (hX : S.k ≤ X / 2) (hz : 1 ≤ z) :
    (refinedBinomialBoundingSieve S X z).errSum (brunUpperWeight L) ≤
      (4 : ℝ) * (z ^ L + 1 : ℕ) * (S.k : ℝ) ^ L := by
  change (refinedBinomialBoundingSieve S X z).errSum
    (brunLowerWeight L) ≤ _
  exact refinedBinomialBoundingSieve_brunLowerErrSum_le S hX hz

/-- Concrete lower bound for the refined sifted cardinality at any odd
depth satisfying the half-Euler tail condition. -/
theorem refinedSiftedCandidates_card_lowerBound
    {B K X z L : ℕ} (S : BPZSection6Input B K)
    (hX : S.k ≤ X / 2) (hz : 1 ≤ z) (hL : Odd L)
    (htail :
      2 * brunSubsetTail (refinedSievePrimeProduct S z).primeFactors
          (fun p => binomialSieveNu S.k p) L ≤
        finiteEulerProduct (refinedSievePrimeProduct S z).primeFactors
          (fun p => binomialSieveNu S.k p)) :
    ((RefinedBaseCandidates S X).card : ℝ) *
          (finiteEulerProduct (refinedSievePrimeProduct S z).primeFactors
            (fun p => binomialSieveNu S.k p) / 2) -
        (4 : ℝ) * (z ^ L + 1 : ℕ) * (S.k : ℝ) ^ L ≤
      ((RefinedSiftedCandidates S X z).card : ℝ) := by
  let s := refinedBinomialBoundingSieve S X z
  have hmain :=
    (boundingSieve_brunMainSums_half_threeHalves s L htail).1
  have hbrun := refinedSiftedCandidates_brunLowerBound
    (X := X) (z := z) S hL
  have herr := refinedBinomialBoundingSieve_brunLowerErrSum_le S hX hz
    (L := L)
  have htotal : s.totalMass = (RefinedBaseCandidates S X).card := rfl
  have htotalNonneg : 0 ≤ s.totalMass := by rw [htotal]; positivity
  have hmul := mul_le_mul_of_nonneg_left hmain htotalNonneg
  rw [← htotal]
  exact (sub_le_sub hmul herr).trans hbrun

/-- The same lower bound with the progression's expected cardinality in
place of its literal total mass. -/
theorem refinedSiftedCandidates_card_lowerBound_density
    {B K X z L : ℕ} (S : BPZSection6Input B K)
    (hX : S.k ≤ X / 2) (hz : 1 ≤ z) (hL : Odd L)
    (htail :
      2 * brunSubsetTail (refinedSievePrimeProduct S z).primeFactors
          (fun p => binomialSieveNu S.k p) L ≤
        finiteEulerProduct (refinedSievePrimeProduct S z).primeFactors
          (fun p => binomialSieveNu S.k p)) :
    ((((X - X / 2 : ℕ) : ℝ) / refinementModulus S - 2) *
          (finiteEulerProduct (refinedSievePrimeProduct S z).primeFactors
            (fun p => binomialSieveNu S.k p) / 2) -
        (4 : ℝ) * (z ^ L + 1 : ℕ) * (S.k : ℝ) ^ L) ≤
      ((RefinedSiftedCandidates S X z).card : ℝ) := by
  have hbaseAbs := abs_card_RefinedBaseCandidates_sub_density S hX
  have hbase :
      ((X - X / 2 : ℕ) : ℝ) / refinementModulus S - 2 ≤
        ((RefinedBaseCandidates S X).card : ℝ) := by
    have hneg := (abs_le.mp hbaseAbs).1
    linarith
  have hEulerNonneg :
      0 ≤ finiteEulerProduct (refinedSievePrimeProduct S z).primeFactors
          (fun p => binomialSieveNu S.k p) / 2 := by
    apply div_nonneg
    · unfold finiteEulerProduct
      apply Finset.prod_nonneg
      intro p hp
      have hdata := refinedSievePrimeFactor_bounds S hp
      change 0 ≤ 1 - binomialSieveNu S.k p
      rw [binomialSieveNu_prime hdata.1]
      have hpPos : (0 : ℝ) < p := by exact_mod_cast hdata.1.pos
      exact sub_nonneg.mpr ((div_le_one hpPos).mpr
        (by exact_mod_cast hdata.2.1.le))
    · norm_num
  exact (sub_le_sub_right
      (mul_le_mul_of_nonneg_right hbase hEulerNonneg)
      ((4 : ℝ) * (z ^ L + 1 : ℕ) * (S.k : ℝ) ^ L)).trans
    (refinedSiftedCandidates_card_lowerBound S hX hz hL htail)

end CoverBPZ

end Erdos387
