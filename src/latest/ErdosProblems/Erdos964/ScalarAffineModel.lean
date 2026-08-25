import ErdosProblems.Erdos964.ScalarPrimeSupport
import ErdosProblems.Erdos964.ScalarSieveCandidate
import ErdosProblems.Erdos964.ScalarAffineS1Saving

/-!
# The concrete scalar affine sieve

The sieve record stores the actual affine products with their fiber
multiplicities. Its first-moment estimate is now unconditional: the only
remaining first-moment input is the asymptotic evaluation of the explicit
squarefree sum at the fixed normalization modulus.
-/

namespace Erdos964

open scoped BigOperators

noncomputable def scalarTripleSieve (A B : Fin 3 → ℕ) (N P : ℕ)
    (hP : Squarefree P) (hgood : ∀ p, p.Prime → p ∣ P → 3 < p) : BoundingSieve where
  support := (Finset.Ico N (2 * N)).image (fun n => ∏ i, (A i * n + B i))
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights x := ((Finset.Ico N (2 * N)).filter (fun n => (∏ i, (A i * n + B i)) = x)).card
  weights_nonneg _ := Nat.cast_nonneg _
  totalMass := N
  nu := ArithmeticFunction.prodPrimeFactors (fun p => (3 : ℝ) / p)
  nu_mult := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  nu_pos_of_prime p hp _ := by
    rw [ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors,
      Finset.prod_singleton]
    exact div_pos (by norm_num) (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime p hp hpP := by
    rw [ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors,
      Finset.prod_singleton]
    exact (div_lt_one (by exact_mod_cast hp.pos)).mpr (by exact_mod_cast hgood p hp hpP)

theorem scalarTripleSieve_density (A B : Fin 3 → ℕ) (N P : ℕ)
    (hP : Squarefree P) (hgood : ∀ p, p.Prime → p ∣ P → 3 < p)
    (p : ℕ) (hp : p.Prime) : (scalarTripleSieve A B N P hP hgood).nu p = (3 : ℝ) / p := by
  change ArithmeticFunction.prodPrimeFactors (fun q => (3 : ℝ) / q) p = _
  rw [ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors, Finset.prod_singleton]

/-- The second-density kernel uses the same finite prime support. Its
unused support data are retained; no semiprime counting approximation is
asserted by this definition. -/
noncomputable def scalarSecondDensitySieve (s : BoundingSieve)
    (hgood : ∀ p, p.Prime → p ∣ s.prodPrimes → 3 < p) : BoundingSieve :=
  { s with
    nu := ArithmeticFunction.prodPrimeFactors (fun p => (2 : ℝ) / ((p : ℝ) - 1))
    nu_mult := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
    nu_pos_of_prime := by
      intro p hp hpP
      rw [ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors,
        Finset.prod_singleton]
      have hp3 : (3 : ℝ) < p := by exact_mod_cast hgood p hp hpP
      exact div_pos (by norm_num) (by linarith)
    nu_lt_one_of_prime := by
      intro p hp hpP
      rw [ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors,
        Finset.prod_singleton]
      have hp3 : (3 : ℝ) < p := by exact_mod_cast hgood p hp hpP
      exact (div_lt_one (by linarith : (0 : ℝ) < p - 1)).mpr (by linarith) }

theorem scalarSecondDensitySieve_density (s : BoundingSieve)
    (hgood : ∀ p, p.Prime → p ∣ s.prodPrimes → 3 < p) (p : ℕ) (hp : p.Prime) :
    (scalarSecondDensitySieve s hgood).nu p = (2 : ℝ) / ((p : ℝ) - 1) := by
  change ArithmeticFunction.prodPrimeFactors (fun q => (2 : ℝ) / ((q : ℝ) - 1)) p = _
  rw [ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors, Finset.prod_singleton]

noncomputable def normalizedScalarTripleSieve (A B : Fin 3 → ℕ)
    (hA : ∀ i, 0 < A i) (hne : ∀ i j, i ≠ j → A i * B j ≠ A j * B i)
    (hadm : ∀ p, p.Prime → ∃ n : ℕ, ∀ i, ¬ p ∣ A i * n + B i)
    (v N R : ℕ) : BoundingSieve :=
  scalarTripleSieve (fun i => A i * affineNormalizationModulus A B) (fun i => A i * v + B i)
    N (scalarSievePrimeProduct (affineNormalizationModulus A B) R)
    (scalarSievePrimeProduct_squarefree _ _)
    (scalarSievePrimeProduct_good A B hA hne hadm R)

noncomputable def scalarCandidateFirstMain (M R : ℕ) : ℝ :=
  ∑ r ∈ (Finset.Ico 1 R).filter (fun r => Squarefree r ∧ r.Coprime M),
    dimensionSelbergWeight 3 r * (scalarLinearY R r) ^ 2

theorem scalarCandidateFirstMain_eq_divisor_sum (M R : ℕ) :
    scalarCandidateFirstMain M R =
      ∑ r ∈ (scalarSievePrimeProduct M R).divisors,
        dimensionSelbergWeight 3 r * (scalarLinearY R r) ^ 2 := by
  symm
  apply sum_scalarSievePrimeProduct_divisors_eq_fixed_modulus_sum
  intro u hu
  rw [scalarLinearY_eq_zero_of_radius R u hu]
  ring

theorem exists_normalizedScalarCandidateS1_logSaving (a : ℕ) (α : ℝ)
    (hα : 0 < α) (hαhalf : α < 1 / 2) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ (A B : Fin 3 → ℕ) (hA : ∀ i, 0 < A i)
        (hne : ∀ i j, i ≠ j → A i * B j ≠ A j * B i)
        (hadm : ∀ p, p.Prime → ∃ n : ℕ, ∀ i, ¬ p ∣ A i * n + B i) (v R : ℕ),
      1 ≤ R → (R : ℝ) ≤ Real.rpow (N : ℝ) α →
      let s := normalizedScalarTripleSieve A B hA hne hadm v N R
      |(∑ n ∈ Finset.Ico N (2 * N),
          scalarAffineWeight (fun i => A i * affineNormalizationModulus A B)
            (fun i => A i * v + B i) s.prodPrimes
            (scalarSelbergCoefficient s (scalarLinearY R)) n) -
          (N : ℝ) * scalarCandidateFirstMain (affineNormalizationModulus A B) R| ≤
        (N : ℝ) / (Real.log N) ^ a := by
  obtain ⟨N₀, hN₀, hbound⟩ := exists_scalarAffineS1_logSaving a α hα hαhalf
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN A B hA hne hadm v R hRone hR
  let s := normalizedScalarTripleSieve A B hA hne hadm v N R
  have hsM : s.prodPrimes.Coprime (affineNormalizationModulus A B) :=
    scalarSievePrimeProduct_coprime _ _
  have hs : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (3 : ℝ) / p := by
    intro p hp _
    exact scalarTripleSieve_density _ _ _ _ _ _ p hp
  have h := hbound N hN A B v R s hsM hs hRone hR (scalarLinearY R)
    (abs_scalarLinearY_le R) (scalarLinearY_eq_zero_of_radius R)
  rw [scalarCandidateFirstMain_eq_divisor_sum]
  exact h

end Erdos964
