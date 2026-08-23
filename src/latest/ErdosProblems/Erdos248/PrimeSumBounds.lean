import ErdosProblems.Erdos248.Scales
import ErdosProblems.Erdos697.Erdos697PrimeHarmonic
import BoundedGaps.Arithmetic.SquarefreeReciprocalCoefficient

/-!
# Erdős Problem 248: coarse prime-sum bounds at the chosen scales

This file packages the elementary analytic estimates used after splitting the
prime divisors of a shift into ranges.  The constants are deliberately coarse:
the only important points are that the reciprocal mass of the far range is
linear in the shift, the normalized logarithmic second moment is uniform, and
the reciprocal-square tails are summable.
-/

noncomputable section

open scoped BigOperators

namespace Erdos248

/-- Primes in the half-open-on-the-left range `lo < p <= hi`. -/
def primesBetween (lo hi : ℕ) : Finset ℕ :=
  (Finset.Icc (lo + 1) hi).filter Nat.Prime

/-- The medium primes for the `k`-th near coordinate. -/
def mediumPrimes (K k : ℕ) : Finset ℕ :=
  primesBetween (tinyCutoff K) (shiftRadius K k)

/-- Primes between the `k`-th near radius and the largest radius. -/
def largePrimes (K k : ℕ) : Finset ℕ :=
  primesBetween (shiftRadius K k) (shiftRadius K 1)

/-- The primes relevant to a far shift. -/
def farPrimes (K k : ℕ) : Finset ℕ :=
  primesBetween (max (tinyCutoff K) k) (shiftRadius K 1)

@[simp] theorem mem_primesBetween {lo hi p : ℕ} :
    p ∈ primesBetween lo hi ↔ lo < p ∧ p ≤ hi ∧ p.Prime := by
  rw [primesBetween, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hlower, hupper⟩, hp⟩
    exact ⟨by omega, hupper, hp⟩
  · rintro ⟨hlower, hupper, hp⟩
    exact ⟨⟨by omega, hupper⟩, hp⟩

theorem primesBetween_subset_primesLE (lo hi : ℕ) :
    primesBetween lo hi ⊆ Nat.primesLE hi := by
  intro p hp
  rw [Nat.mem_primesLE]
  exact ⟨(mem_primesBetween.mp hp).2.1, (mem_primesBetween.mp hp).2.2⟩

theorem sum_primesBetween_nonneg (lo hi : ℕ) (f : ℕ → ℝ)
    (hf : ∀ p ∈ primesBetween lo hi, 0 ≤ f p) :
    0 ≤ ∑ p ∈ primesBetween lo hi, f p := by
  exact Finset.sum_nonneg hf

/-! ## The ordinary reciprocal-prime sum -/

/-- A fixed nonnegative error constant in reciprocal-prime Mertens. -/
def reciprocalPrimeMertensBound : ℝ :=
  Classical.choose Erdos697.PrimeHarmonic.exists_uniform_abs_sum_sub_log_log

theorem reciprocalPrimeMertensBound_nonneg :
    0 ≤ reciprocalPrimeMertensBound :=
  (Classical.choose_spec
    Erdos697.PrimeHarmonic.exists_uniform_abs_sum_sub_log_log).1

theorem abs_primeReciprocalSum_sub_logLog_le {x : ℕ} (hx : 2 ≤ x) :
    |Erdos697.PrimeHarmonic.sum x - Real.log (Real.log (x : ℝ))| ≤
      reciprocalPrimeMertensBound :=
  (Classical.choose_spec
    Erdos697.PrimeHarmonic.exists_uniform_abs_sum_sub_log_log).2 x hx

/-- A generous numerical coefficient for the scale logarithm, plus the fixed
Mertens error. -/
def farPrimeReciprocalConstant : ℝ :=
  10000 + reciprocalPrimeMertensBound

theorem farPrimeReciprocalConstant_nonneg :
    0 ≤ farPrimeReciprocalConstant := by
  unfold farPrimeReciprocalConstant
  exact add_nonneg (by norm_num) reciprocalPrimeMertensBound_nonneg

/-- At the largest radius the iterated logarithm costs at most `10000 K`.
The constant is intentionally loose so the proof only needs `log x <= x`. -/
theorem log_log_largestRadius_le {K : ℕ} (_hK : 0 < K) :
    Real.log (Real.log (shiftRadius K 1 : ℝ)) ≤ 10000 * (K : ℝ) := by
  let e : ℕ := 100 ^ (100 * K - 1)
  have hePos : 0 < e := by
    dsimp [e]
    positivity
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogTwoLe : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlogLogTwo : Real.log (Real.log (2 : ℝ)) ≤ 0 :=
    Real.log_nonpos hlogTwo.le hlogTwoLe
  have hlogHundred : Real.log (100 : ℝ) ≤ 100 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 100)
    norm_num at h ⊢
    linarith
  have heCastPos : (0 : ℝ) < e := by exact_mod_cast hePos
  have heFormula :
      Real.log (e : ℝ) = ((100 * K - 1 : ℕ) : ℝ) * Real.log 100 := by
    dsimp [e]
    push_cast
    rw [Real.log_pow]
  have heBound : Real.log (e : ℝ) ≤ 10000 * (K : ℝ) := by
    rw [heFormula]
    have hexp : (((100 * K - 1 : ℕ) : ℝ)) ≤ 100 * (K : ℝ) := by
      exact_mod_cast (Nat.sub_le (100 * K) 1)
    have hexpNonneg : (0 : ℝ) ≤ ((100 * K - 1 : ℕ) : ℝ) := by positivity
    calc
      (((100 * K - 1 : ℕ) : ℝ)) * Real.log 100 ≤
          (((100 * K - 1 : ℕ) : ℝ)) * 100 :=
        mul_le_mul_of_nonneg_left hlogHundred hexpNonneg
      _ ≤ (100 * (K : ℝ)) * 100 :=
        mul_le_mul_of_nonneg_right hexp (by norm_num)
      _ = 10000 * (K : ℝ) := by ring
  have hlogRadius :
      Real.log (shiftRadius K 1 : ℝ) = (e : ℝ) * Real.log 2 := by
    change Real.log (((2 ^ e : ℕ) : ℝ)) = _
    push_cast
    rw [Real.log_pow]
  rw [hlogRadius, Real.log_mul heCastPos.ne' hlogTwo.ne']
  linarith

theorem primeReciprocalSum_le_logLog_add_bound {x : ℕ} (hx : 2 ≤ x) :
    Erdos697.PrimeHarmonic.sum x ≤
      Real.log (Real.log (x : ℝ)) + reciprocalPrimeMertensBound := by
  have h := (abs_le.mp (abs_primeReciprocalSum_sub_logLog_le hx)).2
  linarith

/-- Reciprocal mass in the far range.  In its intended use `K <= k`, so the
scale cost `O(K)` is absorbed by a constant times the shift. -/
theorem sum_farPrimes_inv_le {K k : ℕ} (hK : 0 < K) (hKk : K ≤ k) :
    (∑ p ∈ farPrimes K k, (1 : ℝ) / p) ≤
      farPrimeReciprocalConstant * (k : ℝ) := by
  have hRtwo : 2 ≤ shiftRadius K 1 := (one_lt_shiftRadius K 1)
  have hsubset : farPrimes K k ⊆ Nat.primesLE (shiftRadius K 1) :=
    primesBetween_subset_primesLE _ _
  have hsum :
      (∑ p ∈ farPrimes K k, (1 : ℝ) / p) ≤
        Erdos697.PrimeHarmonic.sum (shiftRadius K 1) := by
    unfold Erdos697.PrimeHarmonic.sum
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro p hp hpnot
    positivity
  calc
    (∑ p ∈ farPrimes K k, (1 : ℝ) / p) ≤
        Erdos697.PrimeHarmonic.sum (shiftRadius K 1) := hsum
    _ ≤ Real.log (Real.log (shiftRadius K 1 : ℝ)) +
          reciprocalPrimeMertensBound :=
      primeReciprocalSum_le_logLog_add_bound hRtwo
    _ ≤ 10000 * (K : ℝ) + reciprocalPrimeMertensBound := by
      gcongr
      exact log_log_largestRadius_le hK
    _ ≤ farPrimeReciprocalConstant * (k : ℝ) := by
      have hKkR : (K : ℝ) ≤ k := by exact_mod_cast hKk
      have hkOne : (1 : ℝ) ≤ k := by exact_mod_cast hK.trans_le hKk
      unfold farPrimeReciprocalConstant
      nlinarith [reciprocalPrimeMertensBound_nonneg]

/-- The reciprocal-prime mass of a literal interval is the difference of
the two initial Mertens sums. -/
theorem sum_primesBetween_inv_eq_sub {lo hi : ℕ} (hlohi : lo ≤ hi) :
    (∑ p ∈ primesBetween lo hi, (1 : ℝ) / p) =
      Erdos697.PrimeHarmonic.sum hi - Erdos697.PrimeHarmonic.sum lo := by
  have hset : primesBetween lo hi = Nat.primesLE hi \ Nat.primesLE lo := by
    ext p
    simp only [mem_primesBetween, Finset.mem_sdiff, Nat.mem_primesLE]
    constructor
    · rintro ⟨hlop, hphi, hp⟩
      exact ⟨⟨hphi, hp⟩, by omega⟩
    · rintro ⟨⟨hphi, hp⟩, hnot⟩
      have hnle : ¬p ≤ lo := by
        intro hplo
        exact hnot ⟨hplo, hp⟩
      exact ⟨by omega, hphi, hp⟩
  rw [hset]
  unfold Erdos697.PrimeHarmonic.sum
  rw [eq_sub_iff_add_eq]
  exact Finset.sum_sdiff (Nat.primesLE_mono hlohi)

theorem primeReciprocalSum_logLog_sub_bound {x : ℕ} (hx : 2 ≤ x) :
    Real.log (Real.log (x : ℝ)) - reciprocalPrimeMertensBound ≤
      Erdos697.PrimeHarmonic.sum x := by
  have h := (abs_le.mp (abs_primeReciprocalSum_sub_logLog_le hx)).1
  linarith

/-- The difference of the iterated logarithms at the largest and `k`-th
near radii is at most `100 k`. -/
theorem log_log_largestRadius_sub_log_log_shiftRadius_le
    {K k : ℕ} (hk1 : 1 ≤ k) (hkK : k ≤ K) :
    Real.log (Real.log (shiftRadius K 1 : ℝ)) -
        Real.log (Real.log (shiftRadius K k : ℝ)) ≤ 100 * (k : ℝ) := by
  let e₁ : ℕ := 100 ^ (100 * K - 1)
  let eₖ : ℕ := 100 ^ (100 * K - k)
  have he₁Pos : 0 < e₁ := by dsimp [e₁]; positivity
  have heₖPos : 0 < eₖ := by dsimp [eₖ]; positivity
  have he₁CastPos : (0 : ℝ) < e₁ := by exact_mod_cast he₁Pos
  have heₖCastPos : (0 : ℝ) < eₖ := by exact_mod_cast heₖPos
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogOne :
      Real.log (shiftRadius K 1 : ℝ) = (e₁ : ℝ) * Real.log 2 := by
    change Real.log (((2 ^ e₁ : ℕ) : ℝ)) = _
    push_cast
    rw [Real.log_pow]
  have hlogK :
      Real.log (shiftRadius K k : ℝ) = (eₖ : ℝ) * Real.log 2 := by
    change Real.log (((2 ^ eₖ : ℕ) : ℝ)) = _
    push_cast
    rw [Real.log_pow]
  have he₁Log :
      Real.log (e₁ : ℝ) = ((100 * K - 1 : ℕ) : ℝ) * Real.log 100 := by
    dsimp [e₁]
    push_cast
    rw [Real.log_pow]
  have heₖLog :
      Real.log (eₖ : ℝ) = ((100 * K - k : ℕ) : ℝ) * Real.log 100 := by
    dsimp [eₖ]
    push_cast
    rw [Real.log_pow]
  have hexponents : 100 * K - 1 = (100 * K - k) + (k - 1) := by
    omega
  have hlogHundred : Real.log (100 : ℝ) ≤ 100 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 100)
    norm_num at h ⊢
    linarith
  rw [hlogOne, hlogK, Real.log_mul he₁CastPos.ne' hlogTwo.ne',
    Real.log_mul heₖCastPos.ne' hlogTwo.ne', he₁Log, heₖLog,
    hexponents]
  push_cast
  have hkSubNonneg : (0 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by positivity
  have hkSubLe : ((k - 1 : ℕ) : ℝ) ≤ k := by
    exact_mod_cast Nat.sub_le k 1
  nlinarith [mul_le_mul_of_nonneg_left hlogHundred hkSubNonneg]

/-- Uniform coefficient for the near-large reciprocal-prime range. -/
def largePrimeReciprocalConstant : ℝ :=
  100 + 2 * reciprocalPrimeMertensBound

theorem largePrimeReciprocalConstant_nonneg :
    0 ≤ largePrimeReciprocalConstant := by
  unfold largePrimeReciprocalConstant
  exact add_nonneg (by norm_num)
    (mul_nonneg (by norm_num) reciprocalPrimeMertensBound_nonneg)

/-- The reciprocal mass between the `k`-th and largest near radii is `O(k)`
with one fixed constant. -/
theorem sum_largePrimes_inv_le {K k : ℕ} (hk1 : 1 ≤ k) (hkK : k ≤ K) :
    (∑ p ∈ largePrimes K k, (1 : ℝ) / p) ≤
      largePrimeReciprocalConstant * (k : ℝ) := by
  have hkrange : shiftRadius K k ≤ shiftRadius K 1 :=
    by
      unfold shiftRadius
      apply Nat.pow_le_pow_right (by norm_num)
      apply Nat.pow_le_pow_right (by norm_num)
      omega
  have hRkTwo : 2 ≤ shiftRadius K k := (one_lt_shiftRadius K k)
  have hR1Two : 2 ≤ shiftRadius K 1 := (one_lt_shiftRadius K 1)
  rw [largePrimes, sum_primesBetween_inv_eq_sub hkrange]
  calc
    Erdos697.PrimeHarmonic.sum (shiftRadius K 1) -
        Erdos697.PrimeHarmonic.sum (shiftRadius K k) ≤
      (Real.log (Real.log (shiftRadius K 1 : ℝ)) +
          reciprocalPrimeMertensBound) -
        (Real.log (Real.log (shiftRadius K k : ℝ)) -
          reciprocalPrimeMertensBound) := by
      linarith [primeReciprocalSum_le_logLog_add_bound hR1Two,
        primeReciprocalSum_logLog_sub_bound hRkTwo]
    _ ≤ 100 * (k : ℝ) + 2 * reciprocalPrimeMertensBound := by
      linarith [log_log_largestRadius_sub_log_log_shiftRadius_le hk1 hkK]
    _ ≤ largePrimeReciprocalConstant * (k : ℝ) := by
      have hkOneR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      unfold largePrimeReciprocalConstant
      nlinarith [reciprocalPrimeMertensBound_nonneg]

/-! ## The normalized logarithmic second moment -/

/-- A nonnegative version of the bounded-error constant supplied by the
logarithmically weighted prime Mertens theorem. -/
def primeLogMertensBound : ℝ :=
  max 0 (Classical.choose
    BoundedGaps.Maynard.exists_uniform_abs_primeLogHarmonicSum_sub_log)

theorem primeLogMertensBound_nonneg : 0 ≤ primeLogMertensBound :=
  le_max_left _ _

theorem primeLogHarmonicSum_le (x : ℕ) :
    BoundedGaps.Maynard.primeLogHarmonicSum x ≤
      Real.log (x : ℝ) + primeLogMertensBound := by
  have h := (abs_le.mp ((Classical.choose_spec
    BoundedGaps.Maynard.exists_uniform_abs_primeLogHarmonicSum_sub_log) x)).2
  unfold primeLogMertensBound
  linarith [le_max_right (0 : ℝ) (Classical.choose
    BoundedGaps.Maynard.exists_uniform_abs_primeLogHarmonicSum_sub_log)]

/-- Uniform constant for normalized `log^2(p) / p` sums. -/
def normalizedPrimeLogSquareConstant : ℝ :=
  1 + primeLogMertensBound / Real.log 2

theorem normalizedPrimeLogSquareConstant_nonneg :
    0 ≤ normalizedPrimeLogSquareConstant := by
  unfold normalizedPrimeLogSquareConstant
  exact add_nonneg (by norm_num)
    (div_nonneg primeLogMertensBound_nonneg
      (Real.log_pos (by norm_num)).le)

private theorem normalized_log_sq_div_le_log_div
    {p R : ℕ} (hp : p.Prime) (hpR : p ≤ R) (hR : 1 < R) :
    (Real.log (p : ℝ) / Real.log (R : ℝ)) ^ 2 / (p : ℝ) ≤
      (1 / Real.log (R : ℝ)) * (Real.log (p : ℝ) / (p : ℝ)) := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlogp : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hRPos : (0 : ℝ) < R := by
    exact_mod_cast (show 0 < R by omega)
  have hlogR : 0 < Real.log (R : ℝ) :=
    Real.log_pos (by exact_mod_cast hR)
  have hlogle : Real.log (p : ℝ) ≤ Real.log (R : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (by simpa only [Set.mem_Ioi] using hpPos)
      (by simpa only [Set.mem_Ioi] using hRPos)
      (by exact_mod_cast hpR)
  have hsq : Real.log (p : ℝ) ^ 2 ≤
      Real.log (p : ℝ) * Real.log (R : ℝ) := by
    nlinarith
  rw [show (1 / Real.log (R : ℝ)) *
      (Real.log (p : ℝ) / (p : ℝ)) =
      ((1 / Real.log (R : ℝ)) * Real.log (p : ℝ)) / (p : ℝ) by ring]
  apply (div_le_div_iff_of_pos_right hpPos).2
  have hdenSq : 0 ≤ Real.log (R : ℝ) ^ 2 := sq_nonneg _
  rw [show (Real.log (p : ℝ) / Real.log (R : ℝ)) ^ 2 =
      Real.log (p : ℝ) ^ 2 / Real.log (R : ℝ) ^ 2 by ring]
  rw [show (1 / Real.log (R : ℝ)) * Real.log (p : ℝ) =
      (Real.log (p : ℝ) * Real.log (R : ℝ)) /
        Real.log (R : ℝ) ^ 2 by field_simp]
  exact div_le_div_of_nonneg_right hsq hdenSq

/-- Every prime interval ending at `R` has uniformly bounded normalized
logarithmic second moment. -/
theorem sum_primesBetween_normalized_log_sq_le {lo R : ℕ} (hR : 1 < R) :
    (∑ p ∈ primesBetween lo R,
        (Real.log (p : ℝ) / Real.log (R : ℝ)) ^ 2 / (p : ℝ)) ≤
      normalizedPrimeLogSquareConstant := by
  have hlogR : 0 < Real.log (R : ℝ) :=
    Real.log_pos (by exact_mod_cast hR)
  calc
    (∑ p ∈ primesBetween lo R,
        (Real.log (p : ℝ) / Real.log (R : ℝ)) ^ 2 / (p : ℝ)) ≤
        ∑ p ∈ primesBetween lo R,
          (1 / Real.log (R : ℝ)) *
            (Real.log (p : ℝ) / (p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact normalized_log_sq_div_le_log_div
        (mem_primesBetween.mp hp).2.2 (mem_primesBetween.mp hp).2.1 hR
    _ = (1 / Real.log (R : ℝ)) *
        (∑ p ∈ primesBetween lo R, Real.log (p : ℝ) / (p : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ (1 / Real.log (R : ℝ)) *
        BoundedGaps.Maynard.primeLogHarmonicSum R := by
      apply mul_le_mul_of_nonneg_left
      · unfold BoundedGaps.Maynard.primeLogHarmonicSum
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (primesBetween_subset_primesLE lo R)
        intro p hp hpnot
        have hpPrime := Nat.prime_of_mem_primesLE hp
        positivity
      · positivity
    _ ≤ (1 / Real.log (R : ℝ)) *
        (Real.log (R : ℝ) + primeLogMertensBound) := by
      gcongr
      exact primeLogHarmonicSum_le R
    _ = 1 + primeLogMertensBound / Real.log (R : ℝ) := by
      field_simp
    _ ≤ 1 + primeLogMertensBound / Real.log 2 := by
      have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
      have htwoRNat : 2 ≤ R := by omega
      have htwoR : (2 : ℝ) ≤ R := by exact_mod_cast htwoRNat
      have hlogTwoR : Real.log (2 : ℝ) ≤ Real.log (R : ℝ) :=
        Real.strictMonoOn_log.monotoneOn
          (by simp only [Set.mem_Ioi]; norm_num)
          (by simp only [Set.mem_Ioi]; positivity) htwoR
      have hquot := div_le_div_of_nonneg_left primeLogMertensBound_nonneg
        hlogTwo hlogTwoR
      linarith
    _ = normalizedPrimeLogSquareConstant := rfl

theorem sum_mediumPrimes_normalized_log_sq_le (K k : ℕ) :
    (∑ p ∈ mediumPrimes K k,
        (Real.log (p : ℝ) / Real.log (shiftRadius K k : ℝ)) ^ 2 /
          (p : ℝ)) ≤ normalizedPrimeLogSquareConstant := by
  exact sum_primesBetween_normalized_log_sq_le (one_lt_shiftRadius K k)

/-! ## Reciprocal-square tails -/

/-- Prime reciprocal squares are bounded by the full telescoping natural
number tail. -/
theorem sum_primesBetween_inv_sq_le (lo hi : ℕ) :
    (∑ p ∈ primesBetween lo hi, (1 : ℝ) / (p : ℝ) ^ 2) ≤
      2 / ((lo + 1 : ℕ) : ℝ) := by
  by_cases hlohi : lo ≤ hi
  · have hsubset : primesBetween lo hi ⊆ Finset.Ico (lo + 1) (hi + 1) := by
      intro p hp
      have hp' := mem_primesBetween.mp hp
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    calc
      (∑ p ∈ primesBetween lo hi, (1 : ℝ) / (p : ℝ) ^ 2) ≤
          ∑ p ∈ Finset.Ico (lo + 1) (hi + 1),
            (1 : ℝ) / (p : ℝ) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro p hp hpnot
        positivity
      _ ≤ 2 / ((lo + 1 : ℕ) : ℝ) :=
        BoundedGaps.Maynard.sum_Ico_one_div_nat_sq_le
          (Nat.succ_pos lo) (by omega)
  · have hempty : primesBetween lo hi = ∅ := by
      ext p
      simp only [mem_primesBetween, Finset.notMem_empty, iff_false]
      omega
    rw [hempty]
    positivity

theorem sum_mediumPrimes_inv_sq_le (K k : ℕ) :
    (∑ p ∈ mediumPrimes K k, (1 : ℝ) / (p : ℝ) ^ 2) ≤
      2 / ((tinyCutoff K + 1 : ℕ) : ℝ) :=
  sum_primesBetween_inv_sq_le _ _

theorem sum_largePrimes_inv_sq_le (K k : ℕ) :
    (∑ p ∈ largePrimes K k, (1 : ℝ) / (p : ℝ) ^ 2) ≤
      2 / ((shiftRadius K k + 1 : ℕ) : ℝ) :=
  sum_primesBetween_inv_sq_le _ _

theorem sum_farPrimes_inv_sq_le (K k : ℕ) :
    (∑ p ∈ farPrimes K k, (1 : ℝ) / (p : ℝ) ^ 2) ≤
      2 / ((max (tinyCutoff K) k + 1 : ℕ) : ℝ) :=
  sum_primesBetween_inv_sq_le _ _

/-- The finite reciprocal-square budget used in the final union bound. -/
theorem sum_Icc_one_div_sq_le_two (M : ℕ) :
    (∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ) ^ 2) ≤ 2 := by
  have hsets : Finset.Icc 1 M = Finset.Ico 1 (M + 1) := by
    ext k
    simp
  rw [hsets]
  simpa using (BoundedGaps.Maynard.sum_Ico_one_div_nat_sq_le
    (D := 1) (Q := M + 1) (by norm_num) (by omega))

end Erdos248
