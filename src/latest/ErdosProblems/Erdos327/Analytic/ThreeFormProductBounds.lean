import ErdosProblems.Erdos327.Analytic.WeightedLinearSieveCutoff
import ErdosProblems.Erdos327.Analytic.WeightedLinearSieveBridge
import ErdosProblems.Erdos327.Analytic.EulerProductBounds

/-!
# Explicit products for the two weighted three-form sieves

This file packages the two local parameter choices used by the source
and mixed three-form arguments.  It converts the exact local-mean
polynomials into finite exponential Euler-product bounds, and then
feeds them into the quantitative cutoff theorem.
-/

namespace Erdos327.Analytic

open Real Finset
open scoped BigOperators

noncomputable section

/-- The odd primes at most `X`. -/
def oddPrimesUpTo (X : ℕ) : Finset ℕ :=
  (Nat.primesLE X).erase 2

@[simp] theorem mem_oddPrimesUpTo {X p : ℕ} :
    p ∈ oddPrimesUpTo X ↔ p.Prime ∧ p ≤ X ∧ p ≠ 2 := by
  simp only [oddPrimesUpTo, mem_erase, Nat.mem_primesLE]
  aesop

instance oddPrimesUpTo_neZero (X : ℕ) (p : oddPrimesUpTo X) :
    NeZero (p : ℕ) :=
  ⟨(mem_oddPrimesUpTo.mp p.property).1.ne_zero⟩

/-- Source parameters: the first and third forms are killed below `L`. -/
def sourceQU (L p : ℕ) : ℝ :=
  if p < L then 0 else 1 / 2

/-- The middle source parameter is always `1/2`. -/
def sourceQV (_L _p : ℕ) : ℝ := 1 / 2

/-- The third source parameter is `0` below `L` and `1/4` above it. -/
def sourceQSum (L p : ℕ) : ℝ :=
  if p < L then 0 else 1 / 4

/-- Mixed first-form parameter. -/
def mixedQU (L : ℕ) (alpha : ℝ) (p : ℕ) : ℝ :=
  if p < L then 0 else alpha

/-- Mixed second-form parameter. -/
def mixedQW (L : ℕ) (beta : ℝ) (p : ℕ) : ℝ :=
  if p < L then 1 else beta

/-- Mixed linear-form parameter. -/
def mixedQLinear (L : ℕ) (s : ℝ) (p : ℕ) : ℝ :=
  if p < L then 0 else s

theorem sourceQU_nonneg_le_one (L p : ℕ) :
    0 ≤ sourceQU L p ∧ sourceQU L p ≤ 1 := by
  unfold sourceQU
  split_ifs <;> norm_num

theorem sourceQV_nonneg_le_one (L p : ℕ) :
    0 ≤ sourceQV L p ∧ sourceQV L p ≤ 1 := by
  norm_num [sourceQV]

theorem sourceQSum_nonneg_le_one (L p : ℕ) :
    0 ≤ sourceQSum L p ∧ sourceQSum L p ≤ 1 := by
  unfold sourceQSum
  split_ifs <;> norm_num

theorem mixedQU_nonneg_le_one
    {alpha : ℝ} (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (L p : ℕ) :
    0 ≤ mixedQU L alpha p ∧ mixedQU L alpha p ≤ 1 := by
  unfold mixedQU
  split_ifs <;> simp_all

theorem mixedQW_nonneg_le_one
    {beta : ℝ} (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1)
    (L p : ℕ) :
    0 ≤ mixedQW L beta p ∧ mixedQW L beta p ≤ 1 := by
  unfold mixedQW
  split_ifs <;> simp_all

theorem mixedQLinear_nonneg_le_one
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (L p : ℕ) :
    0 ≤ mixedQLinear L s p ∧ mixedQLinear L s p ≤ 1 := by
  unfold mixedQLinear
  split_ifs <;> simp_all

/-- Exact source local mean below the cutoff. -/
theorem source_localWeightMean_of_lt
    {L X : ℕ} (p : oddPrimesUpTo X) (hpL : (p : ℕ) < L) :
    localWeightMean
        (centeredRetainedFamily (P := oddPrimesUpTo X)
          (sourceQU L) (sourceQV L) (sourceQSum L)) p =
      1 - (5 / 2 : ℝ) / (p : ℝ) +
        (3 / 2 : ℝ) / (p : ℝ) ^ 2 := by
  rw [localWeightMean_centeredRetainedFamily]
  simp only [sourceQU, sourceQV, sourceQSum, if_pos hpL]
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast (mem_oddPrimesUpTo.mp p.property).1.ne_zero
  field_simp [hp0]
  ring

/-- Exact source local mean at or above the cutoff. -/
theorem source_localWeightMean_of_le
    {L X : ℕ} (p : oddPrimesUpTo X) (hpL : L ≤ (p : ℕ)) :
    localWeightMean
        (centeredRetainedFamily (P := oddPrimesUpTo X)
          (sourceQU L) (sourceQV L) (sourceQSum L)) p =
      1 - (7 / 4 : ℝ) / (p : ℝ) +
        (13 / 16 : ℝ) / (p : ℝ) ^ 2 := by
  rw [localWeightMean_centeredRetainedFamily]
  simp only [sourceQU, sourceQV, sourceQSum,
    if_neg (not_lt_of_ge hpL)]
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast (mem_oddPrimesUpTo.mp p.property).1.ne_zero
  field_simp [hp0]
  ring

/-- Exact mixed local mean below the cutoff. -/
theorem mixed_localWeightMean_of_lt
    {L X : ℕ} {alpha beta s : ℝ}
    (p : oddPrimesUpTo X) (hpL : (p : ℕ) < L) :
    localWeightMean
        (crossRetainedFamily (P := oddPrimesUpTo X)
          (mixedQU L alpha) (mixedQW L beta)
          (mixedQLinear L s)) p =
      1 - 2 / (p : ℝ) + 1 / (p : ℝ) ^ 2 := by
  rw [localWeightMean_crossRetainedFamily
    (fun q hq ↦ (mem_oddPrimesUpTo.mp hq).1)
    (fun q hq ↦ (mem_oddPrimesUpTo.mp hq).2.2)]
  simp only [mixedQU, mixedQW, mixedQLinear, if_pos hpL]
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast (mem_oddPrimesUpTo.mp p.property).1.ne_zero
  field_simp [hp0]
  ring

/-- Exact mixed local mean at or above the cutoff. -/
theorem mixed_localWeightMean_of_le
    {L X : ℕ} {alpha beta s : ℝ}
    (p : oddPrimesUpTo X) (hpL : L ≤ (p : ℕ)) :
    localWeightMean
        (crossRetainedFamily (P := oddPrimesUpTo X)
          (mixedQU L alpha) (mixedQW L beta)
          (mixedQLinear L s)) p =
      1 + (alpha + beta + s - 3) / (p : ℝ) +
        (2 - alpha - beta - s + alpha * beta * s) /
          (p : ℝ) ^ 2 := by
  rw [localWeightMean_crossRetainedFamily
    (fun q hq ↦ (mem_oddPrimesUpTo.mp hq).1)
    (fun q hq ↦ (mem_oddPrimesUpTo.mp hq).2.2)]
  simp only [mixedQU, mixedQW, mixedQLinear,
    if_neg (not_lt_of_ge hpL)]
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast (mem_oddPrimesUpTo.mp p.property).1.ne_zero
  field_simp [hp0]
  ring

/-- Reciprocal mass of the odd primes up to `X`. -/
noncomputable def oddPrimeInvSum (X : ℕ) : ℝ :=
  ∑ p ∈ oddPrimesUpTo X, 1 / (p : ℝ)

/-- Reciprocal mass of the odd primes below `L`, inside the ambient
cutoff `X`. -/
noncomputable def oddPrimeInvBelow (L X : ℕ) : ℝ :=
  ∑ p ∈ (oddPrimesUpTo X).filter (fun p ↦ p < L),
    1 / (p : ℝ)

/-- Square-reciprocal mass of the odd primes up to `X`. -/
noncomputable def oddPrimeInvSqSum (X : ℕ) : ℝ :=
  ∑ p ∈ oddPrimesUpTo X, 1 / (p : ℝ) ^ 2

theorem oddPrimeInvSum_eq_primeInvSum_sub_half
    {X : ℕ} (hX : 2 ≤ X) :
    oddPrimeInvSum X = primeInvSum X - 1 / 2 := by
  have h2 : 2 ∈ Nat.primesLE X :=
    Nat.mem_primesLE.mpr ⟨hX, Nat.prime_two⟩
  have herase := sum_erase_add (Nat.primesLE X)
    (fun p : ℕ ↦ 1 / (p : ℝ)) h2
  unfold oddPrimeInvSum oddPrimesUpTo primeInvSum
  norm_num at herase ⊢
  linarith

theorem oddPrimeInvBelow_le_oddPrimeInvSum
    {L X : ℕ} :
    oddPrimeInvBelow L X ≤ oddPrimeInvSum L := by
  unfold oddPrimeInvBelow oddPrimeInvSum
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rw [mem_filter] at hp
    rw [mem_oddPrimesUpTo] at hp ⊢
    exact ⟨hp.1.1, hp.2.le, hp.1.2.2⟩
  · intro p _ _
    positivity

theorem oddPrimeInvSum_sub_inv_le_oddPrimeInvBelow
    {L X : ℕ} (hLX : L ≤ X) :
    oddPrimeInvSum L - 1 / (L : ℝ) ≤
      oddPrimeInvBelow L X := by
  let sL := oddPrimesUpTo L
  let low := (oddPrimesUpTo X).filter (fun p ↦ p < L)
  have hsub : sL.erase L ⊆ low := by
    intro p hp
    have hpSL : p ∈ oddPrimesUpTo L := mem_of_mem_erase hp
    have hpne : p ≠ L := ne_of_mem_erase hp
    rw [mem_filter, mem_oddPrimesUpTo]
    rw [mem_oddPrimesUpTo] at hpSL
    exact ⟨⟨hpSL.1, hpSL.2.1.trans hLX, hpSL.2.2⟩,
      lt_of_le_of_ne hpSL.2.1 hpne⟩
  have heraseLe :
      (∑ p ∈ sL.erase L, 1 / (p : ℝ)) ≤
        ∑ p ∈ low, 1 / (p : ℝ) :=
    sum_le_sum_of_subset_of_nonneg hsub
      (fun _ _ _ ↦ by positivity)
  have hsplit :
      (∑ p ∈ sL, 1 / (p : ℝ)) ≤
        1 / (L : ℝ) +
          ∑ p ∈ sL.erase L, 1 / (p : ℝ) := by
    by_cases hmem : L ∈ sL
    · have hsum := sum_erase_add sL
        (fun p : ℕ ↦ 1 / (p : ℝ)) hmem
      linarith
    · simp only [Finset.erase_eq_self.mpr hmem]
      exact le_add_of_nonneg_left (by positivity)
  change (∑ p ∈ sL, 1 / (p : ℝ)) - 1 / (L : ℝ) ≤
    ∑ p ∈ low, 1 / (p : ℝ)
  linarith

theorem primeInvSum_sub_half_sub_inv_le_oddPrimeInvBelow
    {L X : ℕ} (hL : 2 ≤ L) (hLX : L ≤ X) :
    primeInvSum L - 1 / 2 - 1 / (L : ℝ) ≤
      oddPrimeInvBelow L X := by
  rw [← oddPrimeInvSum_eq_primeInvSum_sub_half hL]
  exact oddPrimeInvSum_sub_inv_le_oddPrimeInvBelow hLX

theorem oddPrimeInvSqSum_le_one (X : ℕ) :
    oddPrimeInvSqSum X ≤ 1 := by
  unfold oddPrimeInvSqSum
  simpa using sum_prime_inv_sq_le_one (oddPrimesUpTo X)
    (fun p hp ↦ (mem_oddPrimesUpTo.mp hp).1)

/-- A nonnegative local family has nonnegative normalized mean. -/
theorem localWeightMean_nonneg
    {P : Finset ℕ} [∀ p : P, NeZero (p : ℕ)]
    (w : ∀ p : P, ZMod (p : ℕ) × ZMod (p : ℕ) → ℝ)
    (hw0 : ∀ (p : P) u, 0 ≤ w p u) (p : P) :
    0 ≤ localWeightMean w p := by
  unfold localWeightMean
  exact div_nonneg (sum_nonneg fun u _ ↦ hw0 p u) (sq_nonneg _)

/-- The support-cardinality estimate used by both three-form losses
implies the `3/p` local-mean hypothesis of the cutoff theorem. -/
theorem localLossMean_le_three_div
    {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime)
    [∀ p : P, NeZero (p : ℕ)]
    (ell : ∀ p : P, ZMod (p : ℕ) × ZMod (p : ℕ) → ℝ)
    (hell1 : ∀ (p : P) u, ell p u ≤ 1)
    (hsupport : ∀ p : P,
      (residueWeightSupport (p : ℕ) (ell p)).card ≤
        3 * (p : ℕ))
    (p : P) :
    localLossMean ell p ≤ 3 / (p : ℝ) := by
  have hp0 : 0 < (p : ℝ) := by
    exact_mod_cast (hprime p p.property).pos
  unfold localLossMean
  calc
    (∑ u : ZMod (p : ℕ) × ZMod (p : ℕ), ell p u) /
          (p : ℝ) ^ 2 ≤
        ((residueWeightSupport (p : ℕ) (ell p)).card : ℝ) /
          (p : ℝ) ^ 2 := by
      exact div_le_div_of_nonneg_right
        (sum_weight_le_support_card (hell1 p)) (by positivity)
    _ ≤ (3 * (p : ℕ) : ℕ) / (p : ℝ) ^ 2 := by
      gcongr
      exact_mod_cast hsupport p
    _ = 3 / (p : ℝ) := by
      push_cast
      field_simp

/-- Finite exponent governing the source product before applying
Mertens' theorem. -/
noncomputable def sourceEulerExponent (L X : ℕ) : ℝ :=
  -(7 / 4 : ℝ) * oddPrimeInvSum X -
    (3 / 4 : ℝ) * oddPrimeInvBelow L X +
    (3 / 2 : ℝ) * oddPrimeInvSqSum X

theorem source_localWeightMean_le_exp
    {L X : ℕ} (p : oddPrimesUpTo X) :
    localWeightMean
        (centeredRetainedFamily (P := oddPrimesUpTo X)
          (sourceQU L) (sourceQV L) (sourceQSum L)) p ≤
      exp (-(7 / 4 : ℝ) / (p : ℝ) -
        (if (p : ℕ) < L then
          (3 / 4 : ℝ) / (p : ℝ) else 0) +
        (3 / 2 : ℝ) / (p : ℝ) ^ 2) := by
  by_cases hpL : (p : ℕ) < L
  · rw [source_localWeightMean_of_lt p hpL]
    simp only [if_pos hpL]
    let t := -(7 / 4 : ℝ) / (p : ℝ) -
      (3 / 4 : ℝ) / (p : ℝ) +
      (3 / 2 : ℝ) / (p : ℝ) ^ 2
    calc
      1 - (5 / 2 : ℝ) / (p : ℝ) +
          (3 / 2 : ℝ) / (p : ℝ) ^ 2 =
        1 + t := by dsimp [t]; ring
      _ ≤ exp t := by
        simpa [add_comm] using add_one_le_exp t
  · have hLp : L ≤ (p : ℕ) := Nat.le_of_not_gt hpL
    rw [source_localWeightMean_of_le p hLp]
    simp only [if_neg hpL, sub_zero]
    let t := -(7 / 4 : ℝ) / (p : ℝ) +
      (3 / 2 : ℝ) / (p : ℝ) ^ 2
    have hquad :
        (13 / 16 : ℝ) / (p : ℝ) ^ 2 ≤
          (3 / 2 : ℝ) / (p : ℝ) ^ 2 := by
      have hsq : 0 ≤ 1 / (p : ℝ) ^ 2 := by positivity
      linear_combination (11 / 16 : ℝ) * hsq
    calc
      1 - (7 / 4 : ℝ) / (p : ℝ) +
          (13 / 16 : ℝ) / (p : ℝ) ^ 2 ≤
        1 - (7 / 4 : ℝ) / (p : ℝ) +
          (3 / 2 : ℝ) / (p : ℝ) ^ 2 := by
            linarith
      _ = 1 + t := by dsimp [t]; ring
      _ ≤ exp t := by
        simpa [add_comm] using add_one_le_exp t

/-- The complete source local-mean product is bounded by the finite
Euler exponent with linear coefficients `-7/4` and `-3/4`. -/
theorem source_localMeanProduct_le_exp
    (L X : ℕ) :
    (∏ p : oddPrimesUpTo X,
        localWeightMean
          (centeredRetainedFamily (P := oddPrimesUpTo X)
            (sourceQU L) (sourceQV L) (sourceQSum L)) p) ≤
      exp (sourceEulerExponent L X) := by
  let w := centeredRetainedFamily (P := oddPrimesUpTo X)
    (sourceQU L) (sourceQV L) (sourceQSum L)
  have hw0 : ∀ (p : oddPrimesUpTo X) u, 0 ≤ w p u := by
    intro p u
    exact (centeredLocalWeight_nonneg_le_one
      (sourceQU L p) (sourceQV L p) (sourceQSum L p)
      (sourceQU_nonneg_le_one L p).1
      (sourceQU_nonneg_le_one L p).2
      (sourceQV_nonneg_le_one L p).1
      (sourceQV_nonneg_le_one L p).2
      (sourceQSum_nonneg_le_one L p).1
      (sourceQSum_nonneg_le_one L p).2 u).1
  calc
    (∏ p : oddPrimesUpTo X, localWeightMean w p) ≤
      ∏ p : oddPrimesUpTo X,
        exp (-(7 / 4 : ℝ) / (p : ℝ) -
          (if (p : ℕ) < L then
            (3 / 4 : ℝ) / (p : ℝ) else 0) +
          (3 / 2 : ℝ) / (p : ℝ) ^ 2) := by
      apply prod_le_prod
      · intro p hp
        exact localWeightMean_nonneg w hw0 p
      · intro p hp
        exact source_localWeightMean_le_exp (L := L) p
    _ = exp (∑ p : oddPrimesUpTo X,
        (-(7 / 4 : ℝ) / (p : ℝ) -
          (if (p : ℕ) < L then
            (3 / 4 : ℝ) / (p : ℝ) else 0) +
          (3 / 2 : ℝ) / (p : ℝ) ^ 2)) := by
      rw [exp_sum]
    _ = exp (sourceEulerExponent L X) := by
      congr 1
      rw [show
        (∑ p : oddPrimesUpTo X,
          (-(7 / 4 : ℝ) / (p : ℝ) -
            (if (p : ℕ) < L then
              (3 / 4 : ℝ) / (p : ℝ) else 0) +
            (3 / 2 : ℝ) / (p : ℝ) ^ 2)) =
          ∑ p ∈ oddPrimesUpTo X,
            (-(7 / 4 : ℝ) / (p : ℝ) -
              (if p < L then
                (3 / 4 : ℝ) / (p : ℝ) else 0) +
              (3 / 2 : ℝ) / (p : ℝ) ^ 2) by
        simpa using sum_coe_sort (oddPrimesUpTo X)
          (fun p : ℕ ↦
            (-(7 / 4 : ℝ) / (p : ℝ) -
              (if p < L then
                (3 / 4 : ℝ) / (p : ℝ) else 0) +
              (3 / 2 : ℝ) / (p : ℝ) ^ 2))]
      unfold sourceEulerExponent oddPrimeInvSum oddPrimeInvBelow
        oddPrimeInvSqSum
      rw [sum_add_distrib, sum_sub_distrib, ← sum_filter]
      simp_rw [div_eq_mul_inv]
      rw [← mul_sum, ← mul_sum, ← mul_sum]
      ring_nf

/-- Remove the odd-prime and strict-cutoff notation from the source
exponent.  The constant only pays for `p = 2`, the possible endpoint
prime `p = L`, and the square-reciprocal reserve. -/
theorem sourceEulerExponent_le_primeInvSum
    {L X : ℕ} (hL : 2 ≤ L) (hLX : L ≤ X) :
    sourceEulerExponent L X ≤
      -(7 / 4 : ℝ) * primeInvSum X -
        (3 / 4 : ℝ) * primeInvSum L +
        11 / 4 + 3 / (4 * (L : ℝ)) := by
  have hX : 2 ≤ X := hL.trans hLX
  have hall := oddPrimeInvSum_eq_primeInvSum_sub_half hX
  have hlow :=
    primeInvSum_sub_half_sub_inv_le_oddPrimeInvBelow hL hLX
  have hsq := oddPrimeInvSqSum_le_one X
  unfold sourceEulerExponent
  rw [hall]
  ring_nf at hlow ⊢
  linarith

theorem source_localMeanProduct_le_exp_primeInvSum
    {L X : ℕ} (hL : 2 ≤ L) (hLX : L ≤ X) :
    (∏ p : oddPrimesUpTo X,
        localWeightMean
          (centeredRetainedFamily (P := oddPrimesUpTo X)
            (sourceQU L) (sourceQV L) (sourceQSum L)) p) ≤
      exp (-(7 / 4 : ℝ) * primeInvSum X -
        (3 / 4 : ℝ) * primeInvSum L +
        11 / 4 + 3 / (4 * (L : ℝ))) := by
  exact (source_localMeanProduct_le_exp L X).trans
    (exp_le_exp.mpr (sourceEulerExponent_le_primeInvSum hL hLX))

/-- Center and error radius in the explicit reciprocal-prime Mertens
estimate. -/
noncomputable def primeInvMertensCenter (N : ℕ) : ℝ :=
  log (log N) + Mertens.Weight.M (f := Mertens.Weight.prime)

noncomputable def primeInvMertensError (N : ℕ) : ℝ :=
  (log 4 + 3) / log N

/-- A sign-uniform Mertens envelope for a scalar multiple of the
reciprocal-prime sum. -/
theorem mul_primeInvSum_le_mertensEnvelope
    {N : ℕ} (hN : 2 ≤ N) (c : ℝ) :
    c * primeInvSum N ≤
      c * primeInvMertensCenter N +
        |c| * primeInvMertensError N := by
  by_cases hc : 0 ≤ c
  · have h := mul_le_mul_of_nonneg_left (primeInvSum_le hN) hc
    rw [abs_of_nonneg hc]
    unfold primeInvMertensCenter primeInvMertensError
    calc
      c * primeInvSum N ≤
          c * (log (log N) +
            Mertens.Weight.M (f := Mertens.Weight.prime) +
            (log 4 + 3) / log N) := h
      _ = _ := by ring
  · have hc' : c ≤ 0 := le_of_lt (lt_of_not_ge hc)
    have h := mul_le_mul_of_nonpos_left (primeInvSum_ge hN) hc'
    rw [abs_of_nonpos hc']
    unfold primeInvMertensCenter primeInvMertensError
    calc
      c * primeInvSum N ≤
          c * (log (log N) +
            Mertens.Weight.M (f := Mertens.Weight.prime) -
            (log 4 + 3) / log N) := h
      _ = _ := by ring

/-- Explicit Mertens envelope displaying the source exponents
`-7/4` at `X` and `-3/4` at `L`.  Exponentiating this formula is the
Lean-friendly version of
`(log X)^(-7/4) * (log L)^(-3/4)`. -/
noncomputable def sourceMertensEnvelope (L X : ℕ) : ℝ :=
  -(7 / 4 : ℝ) * primeInvMertensCenter X +
    (7 / 4 : ℝ) * primeInvMertensError X -
    (3 / 4 : ℝ) * primeInvMertensCenter L +
    (3 / 4 : ℝ) * primeInvMertensError L +
    11 / 4 + 3 / (4 * (L : ℝ))

theorem source_localMeanProduct_le_mertens
    {L X : ℕ} (hL : 2 ≤ L) (hLX : L ≤ X) :
    (∏ p : oddPrimesUpTo X,
        localWeightMean
          (centeredRetainedFamily (P := oddPrimesUpTo X)
            (sourceQU L) (sourceQV L) (sourceQSum L)) p) ≤
      exp (sourceMertensEnvelope L X) := by
  have hX : 2 ≤ X := hL.trans hLX
  have hMX := mul_primeInvSum_le_mertensEnvelope
    hX (-(7 / 4 : ℝ))
  have hML := mul_primeInvSum_le_mertensEnvelope
    hL (-(3 / 4 : ℝ))
  refine (source_localMeanProduct_le_exp_primeInvSum hL hLX).trans ?_
  apply exp_le_exp.mpr
  unfold sourceMertensEnvelope
  norm_num at hMX hML ⊢
  linarith

end

end Erdos327.Analytic
