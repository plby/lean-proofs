import ErdosProblems.Erdos157.PrimeDegreeCounts

/-! Separating ordinary primes from the proper prime-power contribution. -/

namespace Erdos157.Elementary.PolynomialCharacters

open Polynomial

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K]

noncomputable def primeCharacterSum (g : K[X]) (χ : MulChar (AdjoinRoot g) ℂ) (n : ℕ) : ℂ :=
  ∑ p : PrimeDegree K n, χ (AdjoinRoot.mk g p.1.1)

noncomputable def properPrimePowerSum (g : K[X]) (χ : MulChar (AdjoinRoot g) ℂ) (n : ℕ) : ℂ :=
  ∑ i : ProperPrimePowerFiber (K := K) n, primePowerWeight g χ i.1.1

/-- The exponent-one fiber is exactly the ordinary primes of the target degree. -/
noncomputable def primeDegreeEquivExponentOne (n : ℕ) :
    PrimeDegree K n ≃ {i : PrimePowerFiber (K := K) n // i.1.2 = 0} where
  toFun p := ⟨⟨(primeDegreeToPrime K p, 0), by
    simpa only [primePowerDegree, zero_add, mul_one] using primeDegreeToPrime_natDegree K p⟩, rfl⟩
  invFun i := ⟨MonicDegreeEq.mk i.1.1.1.1 i.1.1.1.2.1 (by
    have h := i.1.2
    have hk := i.2
    simpa only [primePowerDegree, hk, zero_add, mul_one] using h), i.1.1.1.2.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact i.2.symm

theorem sum_exponentOne (g : K[X]) (χ : MulChar (AdjoinRoot g) ℂ) (n : ℕ) :
    (∑ i : {i : PrimePowerFiber (K := K) n // i.1.2 = 0}, primePowerWeight g χ i.1.1) =
      (n : ℂ) * primeCharacterSum g χ n := by
  have h := Equiv.sum_comp (primeDegreeEquivExponentOne (K := K) n)
    (fun i => primePowerWeight g χ i.1.1)
  rw [← h]
  simp only [primeDegreeEquivExponentOne, Equiv.coe_fn_mk, primePowerWeight,
    zero_add, pow_one, primeDegreeToPrime, primeCharacterSum, MonicDegreeEq.natDegree,
    Finset.mul_sum]

theorem primePowerCoefficient_split (g : K[X]) (χ : MulChar (AdjoinRoot g) ℂ) (n : ℕ) :
    primePowerCoefficient g χ n = (n : ℂ) * primeCharacterSum g χ n + properPrimePowerSum g χ n := by
  classical
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun i : PrimePowerFiber (K := K) n => i.1.2 = 0)
    (fun i => primePowerWeight g χ i.1)
  let e : {i : PrimePowerFiber (K := K) n // ¬i.1.2 = 0} ≃ ProperPrimePowerFiber (K := K) n :=
    Equiv.subtypeEquivRight (fun i => Nat.pos_iff_ne_zero.symm)
  have he := Equiv.sum_comp e (fun i => primePowerWeight g χ i.1.1)
  rw [sum_exponentOne] at hsplit
  have hproper : (∑ i : {i : PrimePowerFiber (K := K) n // ¬i.1.2 = 0}, primePowerWeight g χ i.1.1) =
      properPrimePowerSum g χ n := by
    calc
      _ = ∑ i : {i : PrimePowerFiber (K := K) n // ¬i.1.2 = 0},
          primePowerWeight g χ (e i).1.1 := by
        apply Finset.sum_congr rfl
        intro i _
        rfl
      _ = _ := he
  rw [hproper] at hsplit
  change (∑' i : PrimePowerFiber (K := K) n, primePowerWeight g χ i.1) = _
  rw [tsum_fintype]
  exact hsplit.symm

theorem norm_properPrimePowerSum_le (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (n : ℕ) :
    ‖properPrimePowerSum g χ n‖ ≤
      (n : ℝ) * (n / 2 + 1 : ℕ) * (Fintype.card K : ℝ) ^ (n / 2) := by
  let : Finite (AdjoinRoot g) :=
    Finite.of_injective (AdjoinRoot.powerBasisAux' hg).equivFun
      (AdjoinRoot.powerBasisAux' hg).equivFun.injective
  have hterm : ∀ i : ProperPrimePowerFiber (K := K) n, ‖primePowerWeight g χ i.1.1‖ ≤ n := by
    intro i
    rw [primePowerWeight, norm_mul, Complex.norm_natCast, norm_pow]
    calc
      _ ≤ (i.1.1.1.1.natDegree : ℝ) :=
        mul_le_of_le_one_right (by positivity)
          (pow_le_one₀ (norm_nonneg _) (character_norm_le_one χ _))
      _ ≤ _ := by exact_mod_cast primePowerFiber_degree_le i.1
  calc
    _ ≤ ∑ i : ProperPrimePowerFiber (K := K) n, ‖primePowerWeight g χ i.1.1‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ProperPrimePowerFiber (K := K) n, (n : ℝ) :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = (Fintype.card (ProperPrimePowerFiber (K := K) n) : ℝ) * n := by simp
    _ ≤ (((n / 2 + 1) * Fintype.card K ^ (n / 2) : ℕ) : ℝ) * n := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_properPrimePowerFiber_le (K := K) n
    _ = _ := by push_cast; ring

/-- Removing higher powers leaves an explicit nonprincipal prime-character bound. -/
theorem norm_nat_mul_primeCharacterSum_le (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (hχ : χ ≠ 1) (hχ2 : χ ^ 2 ≠ 1)
    (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * ‖primeCharacterSum g χ n‖ ≤
      (g.natDegree : ℝ) * (Fintype.card K : ℝ) ^ n *
        Real.exp (-(n : ℝ) / (100 * (g.natDegree : ℝ))) +
      (n : ℝ) * (n / 2 + 1 : ℕ) * (Fintype.card K : ℝ) ^ (n / 2) := by
  have heq : (n : ℂ) * primeCharacterSum g χ n =
      primePowerCoefficient g χ n - properPrimePowerSum g χ n := by
    rw [primePowerCoefficient_split]
    ring
  calc
    _ = ‖(n : ℂ) * primeCharacterSum g χ n‖ := by rw [norm_mul, Complex.norm_natCast]
    _ = ‖primePowerCoefficient g χ n - properPrimePowerSum g χ n‖ := congrArg norm heq
    _ ≤ ‖primePowerCoefficient g χ n‖ + ‖properPrimePowerSum g χ n‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add (norm_primePowerCoefficient_le g hg χ hχ hχ2 n hn)
      (norm_properPrimePowerSum_le g hg χ n)

end Erdos157.Elementary.PolynomialCharacters
