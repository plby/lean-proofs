import ErdosProblems.Erdos380.CharacterTransfer

/-!
# Primitive-conductor reduction for prime moments

This finite reduction keeps both the divisor weights and the error caused
by primes dividing a larger modulus.
-/

open scoped BigOperators
open BoundedGaps.Maynard

namespace Erdos380

noncomputable section

local instance conductorCharacterDecidableEq (q : ℕ) : DecidableEq (DirichletCharacter ℂ q) :=
  Classical.decEq _

def primitiveMeanMoment (s : Finset ℕ) (k q : ℕ) : ℝ :=
  ∑ χ : primitiveCharacters q, ‖primeCharacterMean s χ.val‖ ^ k

def nonprincipalMeanMoment (s : Finset ℕ) (k q : ℕ) : ℝ :=
  ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), ‖primeCharacterMean s χ‖ ^ k

def divisorMeanMoment (s : Finset ℕ) (k q : ℕ) : ℝ :=
  ∑ d : q.divisors, if d.val = 1 then 0 else primitiveMeanMoment s k d.val

lemma primitiveMeanMoment_nonneg (s : Finset ℕ) (k q : ℕ) :
    0 ≤ primitiveMeanMoment s k q := Finset.sum_nonneg fun _ _ => by positivity

lemma nonprincipalMeanMoment_eq_sum_indicator (s : Finset ℕ) (k q : ℕ) :
    nonprincipalMeanMoment s k q =
      ∑ χ : DirichletCharacter ℂ q, if χ = 1 then 0 else ‖primeCharacterMean s χ‖ ^ k := by
  classical
  have h := Finset.sum_erase_add Finset.univ
    (fun χ : DirichletCharacter ℂ q => if χ = 1 then 0 else ‖primeCharacterMean s χ‖ ^ k)
    (Finset.mem_univ 1)
  calc
    _ = ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        if χ = 1 then 0 else ‖primeCharacterMean s χ‖ ^ k := by
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [if_neg (Finset.mem_erase.mp hχ).1]
    _ = _ := by simpa only [ite_true, if_pos rfl, add_zero] using h

lemma primeCharacterMean_changeLevel_pow_le {d q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ d) (hd : d ∣ q) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) (k : ℕ) :
    ‖primeCharacterMean s (DirichletCharacter.changeLevel hd χ)‖ ^ k ≤
      2 ^ (k - 1) * (‖primeCharacterMean s χ‖ ^ k +
        ((q.primeFactors.card : ℝ) / (s.card : ℝ)) ^ k) := by
  have he := primeCharacterMean_changeLevel_sub_le χ hd s hs
  have hn : ‖primeCharacterMean s (DirichletCharacter.changeLevel hd χ)‖ ≤
      ‖primeCharacterMean s χ‖ + (q.primeFactors.card : ℝ) / (s.card : ℝ) := by
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (primeCharacterMean s (DirichletCharacter.changeLevel hd χ))
      (primeCharacterMean s χ) 0
    simp only [sub_zero] at htri
    linarith
  exact (pow_le_pow_left₀ (norm_nonneg _) hn k).trans
    (add_pow_le (norm_nonneg _) (by positivity) k)

lemma conductor_fiber_moment_le {q : ℕ} [NeZero q] (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) (k : ℕ) (d : q.divisors) :
    (∑ χ : primitiveCharacters d.val,
      if DirichletCharacter.changeLevel (Nat.dvd_of_mem_divisors d.property) χ.val = 1 then 0
      else ‖primeCharacterMean s
        (DirichletCharacter.changeLevel (Nat.dvd_of_mem_divisors d.property) χ.val)‖ ^ k) ≤
      2 ^ (k - 1) * ((if d.val = 1 then 0 else primitiveMeanMoment s k d.val) +
        (Fintype.card (primitiveCharacters d.val) : ℝ) *
          ((q.primeFactors.card : ℝ) / (s.card : ℝ)) ^ k) := by
  classical
  by_cases hd1 : d.val = 1
  · have heq (χ : primitiveCharacters d.val) :
        DirichletCharacter.changeLevel (Nat.dvd_of_mem_divisors d.property) χ.val = 1 := by
      rw [χ.val.level_one' hd1, map_one]
    simp only [heq, if_true, Finset.sum_const_zero, hd1]
    positivity
  · calc
      _ ≤ ∑ χ : primitiveCharacters d.val,
          ‖primeCharacterMean s
            (DirichletCharacter.changeLevel (Nat.dvd_of_mem_divisors d.property) χ.val)‖ ^ k := by
        apply Finset.sum_le_sum
        intro χ _hχ
        split_ifs
        · positivity
        · exact le_rfl
      _ ≤ ∑ χ : primitiveCharacters d.val,
          2 ^ (k - 1) * (‖primeCharacterMean s χ.val‖ ^ k +
            ((q.primeFactors.card : ℝ) / (s.card : ℝ)) ^ k) := by
        exact Finset.sum_le_sum fun χ _ => primeCharacterMean_changeLevel_pow_le
          χ.val (Nat.dvd_of_mem_divisors d.property) s hs k
      _ = _ := by
        simp [hd1, ← Finset.mul_sum, Finset.sum_add_distrib, primitiveMeanMoment]

/-- All nonprincipal characters are controlled by primitive moments at
nontrivial divisors, plus an explicit divisibility correction. -/
theorem nonprincipalMeanMoment_le_divisorMeanMoment {q : ℕ} [NeZero q]
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (k : ℕ) :
    nonprincipalMeanMoment s k q ≤
      2 ^ (k - 1) * (divisorMeanMoment s k q + (q.totient : ℝ) *
        ((q.primeFactors.card : ℝ) / (s.card : ℝ)) ^ k) := by
  classical
  rw [nonprincipalMeanMoment_eq_sum_indicator,
    sum_characters_eq_sum_divisor_primitive (NeZero.pos q)]
  refine (Finset.sum_le_sum (fun d _ => conductor_fiber_moment_le s hs k d)).trans_eq ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  rw [← Finset.sum_mul]
  have hcard : (∑ d : q.divisors, (Fintype.card (primitiveCharacters d.val) : ℝ)) =
      (q.totient : ℝ) := by
    exact_mod_cast (totient_eq_sum_primitive_cards (NeZero.pos q)).symm
  rw [hcard]
  rfl

end

end Erdos380
