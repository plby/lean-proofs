import ErdosProblems.Erdos380.ModulusWeights

/-!
# Summed finite mixing bounds for prime products

The sums include all ordered pairs of modulus primes, even equal pairs.
This harmless enlargement bounds the distinct semiprime moduli needed for
the two-point residue estimates.
-/

open scoped BigOperators

namespace Erdos380

noncomputable section

def modulusPairSum (t : Finset ℕ) (F : ℕ → ℝ) : ℝ :=
  (∑ p ∈ t, F p) + ∑ p ∈ t, ∑ q ∈ t, F (p * q)

lemma modulusPairSum_add (t : Finset ℕ) (F G : ℕ → ℝ) :
    modulusPairSum t (fun q => F q + G q) = modulusPairSum t F + modulusPairSum t G := by
  simp only [modulusPairSum, Finset.sum_add_distrib]
  ring

lemma modulusPairSum_mul (t : Finset ℕ) (c : ℝ) (F : ℕ → ℝ) :
    modulusPairSum t (fun q => c * F q) = c * modulusPairSum t F := by
  simp only [modulusPairSum, ← Finset.mul_sum]
  ring

lemma modulusPairSum_const (t : Finset ℕ) (c : ℝ) :
    modulusPairSum t (fun _ => c) = ((t.card : ℝ) + (t.card : ℝ) ^ 2) * c := by
  simp only [modulusPairSum, Finset.sum_const, nsmul_eq_mul]
  ring

lemma modulusPairSum_mono {t : Finset ℕ} {F G : ℕ → ℝ}
    (hp : ∀ p ∈ t, F p ≤ G p) (hpq : ∀ p ∈ t, ∀ q ∈ t, F (p * q) ≤ G (p * q)) :
    modulusPairSum t F ≤ modulusPairSum t G := by
  exact add_le_add (Finset.sum_le_sum hp)
    (Finset.sum_le_sum fun p hpt => Finset.sum_le_sum fun q hqt => hpq p hpt q hqt)

lemma primeFactors_card_prime_mul_le_two {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    (p * q).primeFactors.card ≤ 2 := by
  rw [Nat.primeFactors_mul hp.ne_zero hq.ne_zero, hp.primeFactors, hq.primeFactors]
  exact (Finset.card_union_le _ _).trans (by simp)

lemma sum_primitive_tenth_moment_le (s : Finset ℕ) (P Y : ℕ)
    (hs : ∀ p ∈ s, p.Prime) (hP : ∀ p ∈ s, p ≤ P) (hne : s.Nonempty) :
    (∑ d ∈ Finset.Ioc 0 (Y ^ 2), primitiveMeanMoment s 10 d) ≤
      (((P : ℝ) ^ 5 + (Y : ℝ) ^ 4) * 120) / (s.card : ℝ) ^ 5 := by
  have h := normalized_prime_character_even_moment_unweighted_le s (Y ^ 2) P 5 hs hP hne
  norm_num only [Nat.factorial, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_pow] at h
  simpa only [primitiveMeanMoment, ← pow_mul] using h

theorem summed_divisor_tenth_moment_le (s t : Finset ℕ) (P Y : ℕ)
    (hs : ∀ p ∈ s, p.Prime) (hP : ∀ p ∈ s, p ≤ P) (hne : s.Nonempty)
    (ht : ∀ p ∈ t, p.Prime) (hY : ∀ p ∈ t, p ≤ Y)
    {W : ℝ} (hW0 : 0 ≤ W) (hW : ∀ p ∈ t, 1 / (p.totient : ℝ) ≤ W) :
    modulusPairSum t (fun q => divisorMeanMoment s 10 q / (q.totient : ℝ)) ≤
      (W * (1 + 2 * ∑ p ∈ t, 1 / (p.totient : ℝ)) + 2 * W ^ 2) *
        ((((P : ℝ) ^ 5 + (Y : ℝ) ^ 4) * 120) / (s.card : ℝ) ^ 5) := by
  simp only [modulusPairSum, divisorMeanMoment_eq]
  refine (prime_and_pair_divisor_weight_le ht hY (primitiveMeanMoment s 10)
    (primitiveMeanMoment_nonneg s 10) hW0 hW).trans ?_
  exact mul_le_mul_of_nonneg_left (sum_primitive_tenth_moment_le s P Y hs hP hne)
    (by positivity)

lemma nonprincipal_tenth_moment_div_le {q : ℕ} [NeZero q] (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) (hq : q.primeFactors.card ≤ 2) :
    nonprincipalMeanMoment s 10 q / (q.totient : ℝ) ≤
      512 * (divisorMeanMoment s 10 q / (q.totient : ℝ) +
        (2 / (s.card : ℝ)) ^ 10) := by
  have hφ : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hω : (q.primeFactors.card : ℝ) / (s.card : ℝ) ≤ 2 / (s.card : ℝ) :=
    div_le_div_of_nonneg_right (by exact_mod_cast hq) (Nat.cast_nonneg _)
  have he := pow_le_pow_left₀ (by positivity) hω 10
  have h := div_le_div_of_nonneg_right
    (nonprincipalMeanMoment_le_divisorMeanMoment (q := q) s hs 10) (Nat.cast_nonneg q.totient :
      (0 : ℝ) ≤ q.totient)
  norm_num only [Nat.reduceSub, Nat.reducePow] at h
  have halg : (512 : ℝ) * (divisorMeanMoment s 10 q +
      (q.totient : ℝ) * ((q.primeFactors.card : ℝ) / (s.card : ℝ)) ^ 10) /
        (q.totient : ℝ) =
      512 * (divisorMeanMoment s 10 q / (q.totient : ℝ) +
        ((q.primeFactors.card : ℝ) / (s.card : ℝ)) ^ 10) := by
    field_simp
  refine h.trans ?_
  calc
    _ = 512 * (divisorMeanMoment s 10 q / (q.totient : ℝ) +
        ((q.primeFactors.card : ℝ) / (s.card : ℝ)) ^ 10) := halg
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl he) (by norm_num)

theorem summed_nonprincipal_tenth_moment_le (s t : Finset ℕ) (P Y : ℕ)
    (hs : ∀ p ∈ s, p.Prime) (hP : ∀ p ∈ s, p ≤ P) (hne : s.Nonempty)
    (ht : ∀ p ∈ t, p.Prime) (hY : ∀ p ∈ t, p ≤ Y)
    {W : ℝ} (hW0 : 0 ≤ W) (hW : ∀ p ∈ t, 1 / (p.totient : ℝ) ≤ W) :
    modulusPairSum t (fun q => nonprincipalMeanMoment s 10 q / (q.totient : ℝ)) ≤
      512 * ((W * (1 + 2 * ∑ p ∈ t, 1 / (p.totient : ℝ)) + 2 * W ^ 2) *
        ((((P : ℝ) ^ 5 + (Y : ℝ) ^ 4) * 120) / (s.card : ℝ) ^ 5) +
        ((t.card : ℝ) + (t.card : ℝ) ^ 2) * (2 / (s.card : ℝ)) ^ 10) := by
  have hpoint {q : ℕ} (hq0 : q ≠ 0) (hq : q.primeFactors.card ≤ 2) :=
    @nonprincipal_tenth_moment_div_le q ⟨hq0⟩ s hs hq
  have hmono : modulusPairSum t (fun q => nonprincipalMeanMoment s 10 q / q.totient) ≤
      modulusPairSum t (fun q => 512 *
        (divisorMeanMoment s 10 q / q.totient + (2 / (s.card : ℝ)) ^ 10)) := by
    apply modulusPairSum_mono
    · intro p hp
      exact hpoint (ht p hp).ne_zero (by simp [(ht p hp).primeFactors])
    · intro p hp q hq
      exact hpoint (mul_ne_zero (ht p hp).ne_zero (ht q hq).ne_zero)
        (primeFactors_card_prime_mul_le_two (ht p hp) (ht q hq))
  rw [modulusPairSum_mul, modulusPairSum_add, modulusPairSum_const] at hmono
  refine hmono.trans ?_
  have hsum := summed_divisor_tenth_moment_le s t P Y hs hP hne ht hY hW0 hW
  gcongr

lemma modulusPairSum_finset_sum {ι : Type*} (a : Finset ι) (t : Finset ℕ)
    (F : ι → ℕ → ℝ) :
    modulusPairSum t (fun q => ∑ i ∈ a, F i q) = ∑ i ∈ a, modulusPairSum t (F i) := by
  classical
  induction a using Finset.induction_on with
  | empty => simp [modulusPairSum]
  | @insert i a hi ih =>
    simp only [Finset.sum_insert hi, modulusPairSum_add, ih]

lemma modulusPairSum_reciprocal_totient_le (t : Finset ℕ) :
    modulusPairSum t (fun q => 1 / (q.totient : ℝ)) ≤
      (∑ p ∈ t, 1 / (p.totient : ℝ)) + (∑ p ∈ t, 1 / (p.totient : ℝ)) ^ 2 := by
  unfold modulusPairSum
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ p ∈ t, ∑ q ∈ t, (1 / (p.totient : ℝ)) * (1 / (q.totient : ℝ)) :=
      Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => reciprocal_totient_mul_le p q
    _ = _ := by simp_rw [← Finset.mul_sum, ← Finset.sum_mul]; ring

lemma summed_principal_correction_le (s t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) :
    modulusPairSum t (fun q => ((q.primeFactors.card : ℝ) / (s.card : ℝ)) / q.totient) ≤
      (2 / (s.card : ℝ)) *
        ((∑ p ∈ t, 1 / (p.totient : ℝ)) + (∑ p ∈ t, 1 / (p.totient : ℝ)) ^ 2) := by
  have hpoint {q : ℕ} (hq : q.primeFactors.card ≤ 2) :
      ((q.primeFactors.card : ℝ) / (s.card : ℝ)) / q.totient ≤
        (2 / (s.card : ℝ)) * (1 / (q.totient : ℝ)) := by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right (by exact_mod_cast hq) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hmono : modulusPairSum t
      (fun q => ((q.primeFactors.card : ℝ) / (s.card : ℝ)) / q.totient) ≤
        modulusPairSum t (fun q => (2 / (s.card : ℝ)) * (1 / (q.totient : ℝ))) := by
    apply modulusPairSum_mono
    · intro p hp
      exact hpoint (by simp [(ht p hp).primeFactors])
    · intro p hp q hq
      exact hpoint (primeFactors_card_prime_mul_le_two (ht p hp) (ht q hq))
  rw [modulusPairSum_mul] at hmono
  exact hmono.trans (mul_le_mul_of_nonneg_left (modulusPairSum_reciprocal_totient_le t)
    (by positivity))

/-- An explicit majorant for every reduced-residue bias of the ten-fold product. -/
def tenPrimeResidueError (s : Fin 10 → Finset ℕ) (q : ℕ) : ℝ :=
  ((∑ i, (q.primeFactors.card : ℝ) / ((s i).card : ℝ)) +
    ∑ i, nonprincipalMeanMoment (s i) 10 q) / (q.totient : ℝ)

lemma tenPrimeResidueError_nonneg (s : Fin 10 → Finset ℕ) (q : ℕ) :
    0 ≤ tenPrimeResidueError s q := by
  unfold tenPrimeResidueError nonprincipalMeanMoment
  positivity

theorem ten_prime_residue_bias_le (s : Fin 10 → Finset ℕ)
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a)
    (hs : ∀ i p, p ∈ s i → p.Prime) (hne : ∀ i, (s i).Nonempty) :
    ‖(tupleResidueProbability s q a : ℂ) - 1 / (q.totient : ℂ)‖ ≤
      tenPrimeResidueError s q := by
  classical
  have h := ten_prime_residue_uniform_error_le s ha hs hne
  have heq : (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      ∑ i, ‖primeCharacterMean (s i) χ‖ ^ 10) =
        ∑ i, nonprincipalMeanMoment (s i) 10 q := Finset.sum_comm
  rwa [heq] at h

lemma tenPrimeResidueError_eq_sum (s : Fin 10 → Finset ℕ) (q : ℕ) :
    tenPrimeResidueError s q =
      ∑ i, (((q.primeFactors.card : ℝ) / ((s i).card : ℝ)) / q.totient +
        nonprincipalMeanMoment (s i) 10 q / q.totient) := by
  simp only [tenPrimeResidueError, add_div, Finset.sum_div, Finset.sum_add_distrib]

/-- Explicit finite mixing estimate for all prime and semiprime moduli in `t`.
Every analytic quantity on the right is a finite prime count or finite sum. -/
theorem ten_prime_product_mixing_bound (s : Fin 10 → Finset ℕ) (t : Finset ℕ)
    (P : Fin 10 → ℕ) (Y : ℕ)
    (hs : ∀ i p, p ∈ s i → p.Prime) (hP : ∀ i p, p ∈ s i → p ≤ P i)
    (hne : ∀ i, (s i).Nonempty) (ht : ∀ p ∈ t, p.Prime) (hY : ∀ p ∈ t, p ≤ Y)
    {W : ℝ} (hW0 : 0 ≤ W) (hW : ∀ p ∈ t, 1 / (p.totient : ℝ) ≤ W) :
    modulusPairSum t (tenPrimeResidueError s) ≤
      ∑ i, ((2 / ((s i).card : ℝ)) *
        ((∑ p ∈ t, 1 / (p.totient : ℝ)) + (∑ p ∈ t, 1 / (p.totient : ℝ)) ^ 2) +
        512 * ((W * (1 + 2 * ∑ p ∈ t, 1 / (p.totient : ℝ)) + 2 * W ^ 2) *
          ((((P i : ℝ) ^ 5 + (Y : ℝ) ^ 4) * 120) / ((s i).card : ℝ) ^ 5) +
          ((t.card : ℝ) + (t.card : ℝ) ^ 2) * (2 / ((s i).card : ℝ)) ^ 10)) := by
  change modulusPairSum t (fun q => tenPrimeResidueError s q) ≤ _
  simp only [tenPrimeResidueError_eq_sum, modulusPairSum_finset_sum, modulusPairSum_add]
  apply Finset.sum_le_sum
  intro i _hi
  exact add_le_add (summed_principal_correction_le (s i) t ht)
    (summed_nonprincipal_tenth_moment_le (s i) t (P i) Y
      (hs i) (hP i) (hne i) ht hY hW0 hW)

end

end Erdos380
