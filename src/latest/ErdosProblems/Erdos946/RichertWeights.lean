/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# The pointwise Richert weight for Erdős 946

This file contains the elementary half of the weighted-sieve argument.  If
all prime factors below `y` are charged the usual Richert weight

`1 - log p / log y`,

then the total number of prime factors is at most that weight plus
`log m / log y`.  The statement is deliberately independent of the later
sieve estimate.
-/

namespace Erdos946.RichertWeights

open scoped ArithmeticFunction.Omega

private noncomputable def logNat (p : ℕ) : ℝ := Real.log (p : ℝ)

noncomputable def richertTerm (y p : ℕ) : ℝ :=
  if p < y then 1 - logNat p / logNat y else 0

/-- The Richert weight of the prime factors of `m` below `y`, counted with
multiplicity. -/
noncomputable def richertWeight (m y : ℕ) : ℝ :=
  (m.primeFactorsList.map (richertTerm y)).sum

/-- The distinct-prime version agrees with the multiplicity weight on
squarefree inputs and can be averaged by one divisibility condition. -/
noncomputable def distinctRichertWeight (m y : ℕ) : ℝ :=
  ∑ p ∈ m.primeFactors, richertTerm y p

theorem richertTerm_nonneg {y p : ℕ} (hy : 1 < y) (hp : 0 < p) :
    0 ≤ richertTerm y p := by
  unfold richertTerm logNat
  split_ifs with hpy
  · apply sub_nonneg.mpr
    apply (div_le_one (Real.log_pos (by exact_mod_cast hy))).2
    exact Real.log_le_log (by exact_mod_cast hp) (by exact_mod_cast hpy.le)
  · exact le_rfl

theorem richertTerm_le_one {y p : ℕ} (hy : 1 < y) :
    richertTerm y p ≤ 1 := by
  unfold richertTerm logNat
  split_ifs
  · exact sub_le_self _ (div_nonneg (Real.log_natCast_nonneg p)
      (Real.log_pos (by exact_mod_cast hy)).le)
  · norm_num

theorem richertTerm_eq_of_le {y p : ℕ} (hy : 1 < y) (hpy : p ≤ y) :
    richertTerm y p = 1 - Real.log (p : ℝ) / Real.log (y : ℝ) := by
  by_cases hlt : p < y
  · simp [richertTerm, logNat, hlt]
  · have heq : p = y := by omega
    subst p
    have hlog : Real.log (y : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hy)).ne'
    simp [richertTerm, logNat, hlog]

theorem richertTerm_eq_zero_of_le {y p : ℕ} (hyp : y ≤ p) :
    richertTerm y p = 0 := by
  simp [richertTerm, Nat.not_lt.mpr hyp]

theorem distinctRichertWeight_nonneg (m : ℕ) {y : ℕ} (hy : 1 < y) :
    0 ≤ distinctRichertWeight m y := by
  apply Finset.sum_nonneg
  intro p hp
  exact richertTerm_nonneg hy (Nat.prime_of_mem_primeFactors hp).pos

theorem richertWeight_eq_distinct_of_squarefree {m : ℕ} (hm : Squarefree m) (y : ℕ) :
    richertWeight m y = distinctRichertWeight m y := by
  unfold richertWeight distinctRichertWeight
  simpa only [Nat.toFinset_factors] using
    (List.sum_toFinset (richertTerm y) hm.nodup_primeFactorsList).symm

private lemma length_le_weight_add_logSum
    (l : List ℕ) {y : ℕ} (hy : 1 < y)
    (hpos : ∀ p ∈ l, 0 < p) :
    (l.length : ℝ) ≤
      (l.map (richertTerm y)).sum +
        (l.map logNat).sum / logNat y := by
  induction l with
  | nil => simp
  | cons p l ih =>
      have hp : 0 < p := hpos p (by simp)
      have hlpos : ∀ q ∈ l, 0 < q := by
        intro q hq
        exact hpos q (by simp [hq])
      have hlogy : 0 < Real.log (y : ℝ) :=
        Real.log_pos (by exact_mod_cast hy)
      have htail := ih hlpos
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one,
        List.map_cons, List.sum_cons]
      by_cases hpy : p < y
      · rw [richertTerm, if_pos hpy]
        have hsplit :
            (logNat p + (l.map logNat).sum) / logNat y =
              logNat p / logNat y + (l.map logNat).sum / logNat y := by
          ring
        rw [hsplit]
        linarith
      · rw [richertTerm, if_neg hpy]
        have hyp : y ≤ p := Nat.le_of_not_gt hpy
        have hlogle : Real.log (y : ℝ) ≤ Real.log (p : ℝ) := by
          apply Real.log_le_log (by exact_mod_cast (show 0 < y by omega))
          exact_mod_cast hyp
        have hone : (1 : ℝ) ≤
            logNat p / logNat y := by
          simp only [logNat]
          rw [le_div_iff₀ hlogy]
          simpa using hlogle
        have hsplit :
            (logNat p + (l.map logNat).sum) / logNat y =
              logNat p / logNat y + (l.map logNat).sum / logNat y := by
          ring
        rw [hsplit]
        linarith

private lemma sum_log_eq_log_prod (l : List ℕ)
    (hpos : ∀ p ∈ l, 0 < p) :
    (l.map logNat).sum =
      Real.log (l.prod : ℝ) := by
  induction l with
  | nil => simp
  | cons p l ih =>
      have hp : 0 < p := hpos p (by simp)
      have hlpos : ∀ q ∈ l, 0 < q := by
        intro q hq
        exact hpos q (by simp [hq])
      have hlPos : 0 < l.prod := by
        apply List.prod_pos
        intro q hq
        exact hlpos q hq
      simp only [List.map_cons, List.sum_cons, List.prod_cons]
      norm_num only [Nat.cast_mul]
      rw [Real.log_mul (by exact_mod_cast hp.ne')
        (by exact_mod_cast hlPos.ne')]
      rw [ih hlpos]
      rfl

private lemma sum_log_primeFactorsList {m : ℕ} (hm : m ≠ 0) :
    (m.primeFactorsList.map logNat).sum =
      Real.log (m : ℝ) := by
  have hpos : ∀ p ∈ m.primeFactorsList, 0 < p := by
    intro p hp
    exact (Nat.prime_of_mem_primeFactorsList hp).pos
  rw [sum_log_eq_log_prod m.primeFactorsList hpos,
    Nat.prod_primeFactorsList hm]

/-- Pointwise Richert inequality.  It requires no squarefreeness: repeated
prime factors occur repeatedly in `primeFactorsList` and are charged with
their multiplicity. -/
theorem cardFactors_le_richertWeight_add_log
    {m y : ℕ} (hm : m ≠ 0) (hy : 1 < y) :
    (ArithmeticFunction.cardFactors m : ℝ) ≤
      richertWeight m y + Real.log (m : ℝ) / Real.log (y : ℝ) := by
  have hpos : ∀ p ∈ m.primeFactorsList, 0 < p := by
    intro p hp
    exact (Nat.prime_of_mem_primeFactorsList hp).pos
  have h := length_le_weight_add_logSum m.primeFactorsList hy hpos
  simpa only [ArithmeticFunction.cardFactors_apply, richertWeight,
    sum_log_primeFactorsList hm, logNat] using h

/-- The numerical extraction used in the eight-form argument.  A total
Richert weight below `11`, together with logarithmic size at most `24`,
forces at most `34` prime factors. -/
theorem cardFactors_le_thirtyFour_of_weight_lt_eleven
    {m y : ℕ} (hm : m ≠ 0) (hy : 1 < y)
    (hsize : Real.log (m : ℝ) / Real.log (y : ℝ) ≤ 24)
    (hweight : richertWeight m y < 11) :
    ArithmeticFunction.cardFactors m ≤ 34 := by
  have hmain := cardFactors_le_richertWeight_add_log hm hy
  have hlt : (ArithmeticFunction.cardFactors m : ℝ) < 35 := by
    linarith
  exact Nat.le_of_lt_succ (by exact_mod_cast hlt)

/-- The deliberately loose sixteen-form constants leave room below the
collision threshold `1 + ⋯ + 16 = 136`. -/
theorem cardFactors_le_oneHundredThirty_of_weight_lt
    {m y : ℕ} (hm : m ≠ 0) (hy : 1 < y)
    (hsize : Real.log (m : ℝ) / Real.log (y : ℝ) ≤ 34)
    (hweight : richertWeight m y < 97) :
    ArithmeticFunction.cardFactors m ≤ 130 := by
  have hmain := cardFactors_le_richertWeight_add_log hm hy
  have hlt : (ArithmeticFunction.cardFactors m : ℝ) < 131 := by linarith
  exact Nat.le_of_lt_succ (by exact_mod_cast hlt)

end Erdos946.RichertWeights
