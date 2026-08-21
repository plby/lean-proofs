import BoundedGaps.PrimeNumberTheorem.Analytic.PrimeCounting
import ErdosProblems.Erdos697.Erdos697PrimeHarmonic

/-!
# Prime-counting and Mertens estimates for Erdős problem 69

This file packages the two elementary consequences of the prime number
theorem used in Section 5 of Tao--Teräväinen's proof:

* a dyadic interval contains `≫ P / log P` primes;
* the reciprocal-prime mass of `(L,U]` differs from
  `log (log U) - log (log L)` by a fixed absolute constant.

The second result uses the bounded-error reciprocal-prime Mertens theorem
already proved in `Erdos697PrimeHarmonic`.  In particular, none of the
statements below assumes a prime-distribution hypothesis.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos69.PrimeEstimates

noncomputable section

/-- The primes in the half-open interval `(L,U]`. -/
def primesIn (L U : ℕ) : Finset ℕ :=
  (Finset.Ioc L U).filter Nat.Prime

@[simp] theorem mem_primesIn {L U p : ℕ} :
    p ∈ primesIn L U ↔ L < p ∧ p ≤ U ∧ p.Prime := by
  simp [primesIn, and_assoc]

/-- The prime count of `(L,U]` is the difference of the two usual prime
counting functions. -/
theorem card_primesIn_eq_sub {L U : ℕ} (hLU : L ≤ U) :
    (primesIn L U).card = Nat.primeCounting U - Nat.primeCounting L := by
  classical
  have hsplit : Nat.primesLE U = Nat.primesLE L ∪ primesIn L U := by
    ext p
    simp only [Nat.mem_primesLE, Finset.mem_union, mem_primesIn]
    constructor
    · intro hp
      by_cases hpL : p ≤ L
      · exact Or.inl ⟨hpL, hp.2⟩
      · exact Or.inr ⟨by omega, hp.1, hp.2⟩
    · rintro (hp | hp)
      · exact ⟨hp.1.trans hLU, hp.2⟩
      · exact ⟨hp.2.1, hp.2.2⟩
  have hdisj : Disjoint (Nat.primesLE L) (primesIn L U) := by
    apply Finset.disjoint_left.mpr
    intro p hpL hpI
    have hpLE := (Nat.mem_primesLE.mp hpL).1
    have hpLT := (mem_primesIn.mp hpI).1
    omega
  have hcard := congrArg Finset.card hsplit
  rw [Finset.card_union_of_disjoint hdisj,
    Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]
      at hcard
  omega

/-- A fixed-error form of the prime number theorem, convenient for taking
differences of prime counts. -/
theorem eventually_primeCounting_tenth_bounds :
    ∀ᶠ x : ℕ in atTop,
      (9 / 10 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) ≤
          (Nat.primeCounting x : ℝ) ∧
      (Nat.primeCounting x : ℝ) ≤
          (11 / 10 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) := by
  have hpnt :=
    BoundedGaps.PrimeNumberTheorem.primeCounting_natCast_isEquivalent
  have herr := hpnt.isLittleO.def (show (0 : ℝ) < 1 / 10 by norm_num)
  have hmainPos : ∀ᶠ x : ℕ in atTop,
      0 ≤ (x : ℝ) / Real.log (x : ℝ) := by
    filter_upwards [eventually_ge_atTop 3] with x hx
    positivity
  filter_upwards [herr, hmainPos] with x hx hpos
  simp only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg hpos] at hx
  constructor <;> linarith [le_abs_self
    ((Nat.primeCounting x : ℝ) - (x : ℝ) / Real.log (x : ℝ)),
    neg_abs_le
      ((Nat.primeCounting x : ℝ) - (x : ℝ) / Real.log (x : ℝ))]

/-- The natural-number map `P ↦ 2P` tends to infinity. -/
private theorem tendsto_two_mul_atTop :
    Tendsto (fun P : ℕ ↦ 2 * P) atTop atTop := by
  refine Filter.tendsto_atTop_mono' atTop ?_ Filter.tendsto_id
  filter_upwards with P
  simpa only [id_eq] using (show P ≤ 2 * P by omega)

/-- The actual dyadic prime-count lower bound used to supply the prime set
for the affine-cube argument.  The constant is deliberately inessential;
the important point is the uniform `P / log P` scale on `(P,2P]`. -/
theorem eventually_dyadic_prime_count_lower :
    ∀ᶠ P : ℕ in atTop,
      (1 / 10 : ℝ) * ((P : ℝ) / Real.log (P : ℝ)) ≤
        ((primesIn P (2 * P)).card : ℝ) := by
  have hpntP := eventually_primeCounting_tenth_bounds
  have hpntTwo := tendsto_two_mul_atTop.eventually
    eventually_primeCounting_tenth_bounds
  filter_upwards [hpntP, hpntTwo, eventually_ge_atTop (4 : ℕ)]
      with P hpntP hpntTwo hP
  have hPone : (1 : ℝ) < P := by
    exact_mod_cast (show 1 < P by omega)
  have hPpos : (0 : ℝ) < P := by positivity
  have hlogP : 0 < Real.log (P : ℝ) := Real.log_pos hPone
  have htwoPone : (1 : ℝ) < (2 * P : ℕ) := by
    exact_mod_cast (show 1 < 2 * P by omega)
  have hlogTwoP : 0 < Real.log ((2 * P : ℕ) : ℝ) :=
    Real.log_pos htwoPone
  have hlogFourLe : Real.log (4 : ℝ) ≤ Real.log (P : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; norm_num)
      (by simp only [Set.mem_Ioi]; positivity)
      (by exact_mod_cast hP)
  have hlogTwoLeHalf : Real.log (2 : ℝ) ≤ Real.log (P : ℝ) / 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at hlogFourLe
    norm_num at hlogFourLe ⊢
    linarith
  have hlogTwoPLe :
      Real.log ((2 * P : ℕ) : ℝ) ≤ (3 / 2 : ℝ) * Real.log (P : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hPpos.ne']
    linarith
  have hfraction :
      (4 / 3 : ℝ) * (P : ℝ) / Real.log (P : ℝ) ≤
        ((2 * P : ℕ) : ℝ) / Real.log ((2 * P : ℕ) : ℝ) := by
    have hcast : ((2 * P : ℕ) : ℝ) = 2 * (P : ℝ) := by norm_num
    rw [hcast] at hlogTwoP hlogTwoPLe ⊢
    rw [div_le_div_iff₀ hlogP hlogTwoP]
    have hmul := mul_le_mul_of_nonneg_left hlogTwoPLe hPpos.le
    nlinarith
  have hlowerTwo :
      (6 / 5 : ℝ) * ((P : ℝ) / Real.log (P : ℝ)) ≤
        (Nat.primeCounting (2 * P) : ℝ) := by
    calc
      (6 / 5 : ℝ) * ((P : ℝ) / Real.log (P : ℝ)) =
          (9 / 10 : ℝ) *
            ((4 / 3 : ℝ) * (P : ℝ) / Real.log (P : ℝ)) := by ring
      _ ≤ (9 / 10 : ℝ) *
          (((2 * P : ℕ) : ℝ) / Real.log ((2 * P : ℕ) : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hfraction (by norm_num)
      _ ≤ (Nat.primeCounting (2 * P) : ℝ) := hpntTwo.1
  have hcountMono : Nat.primeCounting P ≤ Nat.primeCounting (2 * P) :=
    Nat.monotone_primeCounting (by omega)
  rw [card_primesIn_eq_sub (show P ≤ 2 * P by omega),
    Nat.cast_sub hcountMono]
  have hscaleNonneg : 0 ≤ (P : ℝ) / Real.log (P : ℝ) := by positivity
  nlinarith [hpntP.2]

/-- Reciprocal-prime mass up to a natural endpoint. -/
def reciprocalPrimeSum (x : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE x, (1 : ℝ) / p

/-- Reciprocal-prime mass in `(L,U]`. -/
def reciprocalPrimeMass (L U : ℕ) : ℝ :=
  ∑ p ∈ primesIn L U, (1 : ℝ) / p

theorem reciprocalPrimeSum_eq_primeHarmonic (x : ℕ) :
    reciprocalPrimeSum x = Erdos697.PrimeHarmonic.sum x := by
  rfl

/-- Exact subtraction identity for reciprocal-prime windows. -/
theorem reciprocalPrimeMass_eq_sub {L U : ℕ} (hLU : L ≤ U) :
    reciprocalPrimeMass L U = reciprocalPrimeSum U - reciprocalPrimeSum L := by
  classical
  unfold reciprocalPrimeMass reciprocalPrimeSum
  have hsplit : Nat.primesLE U = Nat.primesLE L ∪ primesIn L U := by
    ext p
    simp only [Nat.mem_primesLE, Finset.mem_union, mem_primesIn]
    constructor
    · intro hp
      by_cases hpL : p ≤ L
      · exact Or.inl ⟨hpL, hp.2⟩
      · exact Or.inr ⟨by omega, hp.1, hp.2⟩
    · rintro (hp | hp)
      · exact ⟨hp.1.trans hLU, hp.2⟩
      · exact ⟨hp.2.1, hp.2.2⟩
  have hdisj : Disjoint (Nat.primesLE L) (primesIn L U) := by
    apply Finset.disjoint_left.mpr
    intro p hpL hpI
    have hpLE := (Nat.mem_primesLE.mp hpL).1
    have hpLT := (mem_primesIn.mp hpI).1
    omega
  rw [hsplit, Finset.sum_union hdisj]
  ring

theorem reciprocalPrimeMass_nonneg (L U : ℕ) :
    0 ≤ reciprocalPrimeMass L U := by
  unfold reciprocalPrimeMass
  exact Finset.sum_nonneg fun p _ ↦ by positivity

/-- Mertens' theorem for reciprocal primes, with one absolute error constant
valid at every natural endpoint at least two. -/
theorem exists_uniform_abs_reciprocalPrimeSum_sub_log_log :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ, 2 ≤ x →
      |reciprocalPrimeSum x - Real.log (Real.log (x : ℝ))| ≤ C := by
  simpa only [reciprocalPrimeSum_eq_primeHarmonic] using
    Erdos697.PrimeHarmonic.exists_uniform_abs_sum_sub_log_log

/-- Window form of Mertens' theorem.  Its error is at most twice the
endpoint error. -/
theorem abs_reciprocalPrimeMass_sub_log_log_diff_le
    {C : ℝ}
    (hMertens : ∀ x : ℕ, 2 ≤ x →
      |reciprocalPrimeSum x - Real.log (Real.log (x : ℝ))| ≤ C)
    {L U : ℕ} (hL : 2 ≤ L) (hLU : L ≤ U) :
    |reciprocalPrimeMass L U -
        (Real.log (Real.log (U : ℝ)) - Real.log (Real.log (L : ℝ)))| ≤
      2 * C := by
  rw [reciprocalPrimeMass_eq_sub hLU]
  have hU : 2 ≤ U := hL.trans hLU
  have hrearrange :
      reciprocalPrimeSum U - reciprocalPrimeSum L -
          (Real.log (Real.log (U : ℝ)) - Real.log (Real.log (L : ℝ))) =
        (reciprocalPrimeSum U - Real.log (Real.log (U : ℝ))) -
          (reciprocalPrimeSum L - Real.log (Real.log (L : ℝ))) := by ring
  rw [hrearrange]
  calc
    |(reciprocalPrimeSum U - Real.log (Real.log (U : ℝ))) -
        (reciprocalPrimeSum L - Real.log (Real.log (L : ℝ)))| ≤
      |reciprocalPrimeSum U - Real.log (Real.log (U : ℝ))| +
        |reciprocalPrimeSum L - Real.log (Real.log (L : ℝ))| :=
          abs_sub _ _
    _ ≤ C + C := add_le_add (hMertens U hU) (hMertens L hL)
    _ = 2 * C := by ring

/-- Lower half of the window Mertens estimate. -/
theorem log_log_diff_sub_two_mul_le_reciprocalPrimeMass
    {C : ℝ}
    (hMertens : ∀ x : ℕ, 2 ≤ x →
      |reciprocalPrimeSum x - Real.log (Real.log (x : ℝ))| ≤ C)
    {L U : ℕ} (hL : 2 ≤ L) (hLU : L ≤ U) :
    Real.log (Real.log (U : ℝ)) - Real.log (Real.log (L : ℝ)) - 2 * C ≤
      reciprocalPrimeMass L U := by
  have h := abs_reciprocalPrimeMass_sub_log_log_diff_le
    hMertens hL hLU
  linarith [neg_abs_le
    (reciprocalPrimeMass L U -
      (Real.log (Real.log (U : ℝ)) - Real.log (Real.log (L : ℝ))))]

/-- Upper half of the window Mertens estimate. -/
theorem reciprocalPrimeMass_le_log_log_diff_add_two_mul
    {C : ℝ}
    (hMertens : ∀ x : ℕ, 2 ≤ x →
      |reciprocalPrimeSum x - Real.log (Real.log (x : ℝ))| ≤ C)
    {L U : ℕ} (hL : 2 ≤ L) (hLU : L ≤ U) :
    reciprocalPrimeMass L U ≤
      Real.log (Real.log (U : ℝ)) - Real.log (Real.log (L : ℝ)) + 2 * C := by
  have h := abs_reciprocalPrimeMass_sub_log_log_diff_le
    hMertens hL hLU
  linarith [le_abs_self
    (reciprocalPrimeMass L U -
      (Real.log (Real.log (U : ℝ)) - Real.log (Real.log (L : ℝ))))]

end

end Erdos69.PrimeEstimates
