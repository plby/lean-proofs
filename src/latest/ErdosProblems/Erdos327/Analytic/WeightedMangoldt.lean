import ErdosProblems.Erdos327.Analytic.PrimeWeight
import Mathlib.NumberTheory.LSeries.PrimesInAP

namespace Erdos327.Analytic

open Finset Real
open scoped ArithmeticFunction

/-- The normalized non-prime prime-power contribution to the weighted
von Mangoldt moment.  Prime contributions are excluded because their
normalized sum diverges; they are controlled separately by Chebyshev's
bound. -/
noncomputable def weightedNonprimeMangoldtTerm
    (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  (if n.Prime then 0 else
    factorWeight w n * ArithmeticFunction.vonMangoldt n) / n

/-- The convergent tail sampled at prime powers of exponent at least
two. -/
noncomputable def weightedPrimePowerTail
    (w : ℕ → ℝ) (pk : Nat.Primes × ℕ) : ℝ :=
  weightedNonprimeMangoldtTerm w (pk.1 ^ (pk.2 + 2))

/-- The same prime-power sampling with exponent `k + 1`; its `k = 0`
slice is zero because prime inputs were removed. -/
noncomputable def weightedPrimePowerAll
    (w : ℕ → ℝ) (pk : Nat.Primes × ℕ) : ℝ :=
  weightedNonprimeMangoldtTerm w (pk.1 ^ (pk.2 + 1))

theorem weightedNonprimeMangoldtTerm_nonneg
    {w : ℕ → ℝ} (hw0 : ∀ p, 0 ≤ w p) (n : ℕ) :
    0 ≤ weightedNonprimeMangoldtTerm w n := by
  unfold weightedNonprimeMangoldtTerm
  split_ifs
  · positivity
  · exact div_nonneg
      (mul_nonneg (factorWeight_nonneg hw0 n)
        ArithmeticFunction.vonMangoldt_nonneg)
      (Nat.cast_nonneg n)

/-- The exceptional bound at `2` and the uniform `5/2` bound elsewhere
give the strict local ratio `w(p)/p ≤ 5/6` at every prime. -/
theorem primeWeight_div_le_five_six
    {w : ℕ → ℝ} (hw0 : ∀ p, 0 ≤ w p)
    (hw : ∀ p, w p ≤ 5 / 2) (hw2 : w 2 ≤ 1)
    (p : Nat.Primes) :
    0 ≤ w p / (p : ℝ) ∧ w p / (p : ℝ) ≤ 5 / 6 := by
  have hpcast : (0 : ℝ) < p := by
    exact_mod_cast p.prop.pos
  refine ⟨div_nonneg (hw0 p) hpcast.le, ?_⟩
  by_cases hp2 : (p : ℕ) = 2
  · rw [hp2]
    norm_num
    linarith
  · have hp3 : 3 ≤ (p : ℕ) := by
      have := p.prop.two_le
      omega
    have hp3' : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    apply (div_le_div_iff₀ hpcast (by norm_num : (0 : ℝ) < 6)).2
    nlinarith [hw p]

/-- A summable product majorant for the weighted prime-power tail. -/
noncomputable def weightedPrimePowerMajorant
    (pk : Nat.Primes × ℕ) : ℝ :=
  (25 / 4) *
    (log (pk.1 : ℝ) / (pk.1 : ℝ) ^ 2) *
      (5 / 6 : ℝ) ^ pk.2

theorem weightedPrimePowerTail_le_majorant
    {w : ℕ → ℝ} (hw0 : ∀ p, 0 ≤ w p)
    (hw : ∀ p, w p ≤ 5 / 2) (hw2 : w 2 ≤ 1)
    (pk : Nat.Primes × ℕ) :
    weightedPrimePowerTail w pk ≤ weightedPrimePowerMajorant pk := by
  rcases pk with ⟨p, k⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
  have hlog0 : 0 ≤ log (p : ℝ) :=
    log_nonneg (by exact_mod_cast p.prop.one_le)
  have hratio := primeWeight_div_le_five_six hw0 hw hw2 p
  have hwB : w p ≤ 5 / 2 := hw p
  have hw0p : 0 ≤ w p := hw0 p
  have hratioB :
      w p / (p : ℝ) ≤ (5 / 2 : ℝ) / p :=
    div_le_div_of_nonneg_right hwB hp0.le
  change weightedNonprimeMangoldtTerm w (p ^ (k + 2)) ≤ _
  calc
    weightedNonprimeMangoldtTerm w (p ^ (k + 2)) =
        log (p : ℝ) * (w p / (p : ℝ)) ^ (k + 2) := by
      simp only [weightedNonprimeMangoldtTerm,
        Nat.Prime.not_prime_pow (by omega : 2 ≤ k + 2),
        ↓reduceIte, factorWeight_primePow p.prop,
        ArithmeticFunction.vonMangoldt_apply_pow (by omega : k + 2 ≠ 0),
        ArithmeticFunction.vonMangoldt_apply_prime p.prop, Nat.cast_pow,
        div_pow]
      ring
    _ = log (p : ℝ) *
        ((w p / (p : ℝ)) ^ k * (w p / (p : ℝ)) ^ 2) := by
      rw [pow_add]
    _ ≤ log (p : ℝ) *
        ((5 / 6 : ℝ) ^ k * (((5 / 2 : ℝ) / p) ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hlog0
      exact mul_le_mul
        (pow_le_pow_left₀ hratio.1 hratio.2 k)
        (pow_le_pow_left₀ hratio.1 hratioB 2)
        (pow_nonneg hratio.1 2)
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 6) k)
    _ = weightedPrimePowerMajorant (p, k) := by
      unfold weightedPrimePowerMajorant
      field_simp
      ring

theorem weightedPrimePowerMajorant_nonneg
    (pk : Nat.Primes × ℕ) :
    0 ≤ weightedPrimePowerMajorant pk := by
  unfold weightedPrimePowerMajorant
  positivity [log_nonneg (by
    exact_mod_cast pk.1.prop.one_le :
      (1 : ℝ) ≤ (pk.1 : ℝ))]

/-- The prime coefficient `log p / p²` is summable. -/
theorem summable_prime_log_div_sq :
    Summable (fun p : Nat.Primes ↦ log (p : ℝ) / (p : ℝ) ^ 2) := by
  have hpseries :
      Summable (fun p : Nat.Primes ↦
        (p : ℝ) ^ (-3 / 2 : ℝ)) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  apply Summable.of_nonneg_of_le
    (fun (p : Nat.Primes) ↦ div_nonneg
      (log_nonneg (by
        exact_mod_cast p.prop.one_le :
          (1 : ℝ) ≤ (p : ℝ)))
      (sq_nonneg (p : ℝ)))
    (fun (p : Nat.Primes) ↦ ?_)
    (hpseries.mul_left 2)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
  calc
    log (p : ℝ) / (p : ℝ) ^ 2 =
        log (p : ℝ) * (p : ℝ)⁻¹ ^ 2 := by
      field_simp
    _ ≤ ((p : ℝ) ^ (1 / 2 : ℝ) / (1 / 2)) *
        (p : ℝ)⁻¹ ^ 2 := by
      gcongr
      exact Real.log_le_rpow_div hp0.le (by norm_num)
    _ = 2 * (p : ℝ) ^ (-3 / 2 : ℝ) := by
      rw [div_eq_mul_inv, ← Real.rpow_natCast,
        Real.inv_rpow hp0.le, ← Real.rpow_neg hp0.le]
      rw [show (1 / 2 : ℝ)⁻¹ = 2 by norm_num]
      ring_nf
      rw [← Real.rpow_add hp0]
      norm_num

theorem summable_weightedPrimePowerMajorant :
    Summable weightedPrimePowerMajorant := by
  have hk :
      Summable (fun k : ℕ ↦ (5 / 6 : ℝ) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  rw [summable_prod_of_nonneg weightedPrimePowerMajorant_nonneg]
  refine ⟨?_, ?_⟩
  · intro p
    exact hk.mul_left
      ((25 / 4) * (log (p : ℝ) / (p : ℝ) ^ 2))
  · have hp := summable_prime_log_div_sq
    have hgeom :
        ∑' k : ℕ, (5 / 6 : ℝ) ^ k = 6 := by
      rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num
    have heq :
        (fun p : Nat.Primes ↦
          ∑' k : ℕ, weightedPrimePowerMajorant (p, k)) =
        fun p : Nat.Primes ↦
          (75 / 2 : ℝ) * (log (p : ℝ) / (p : ℝ) ^ 2) := by
      funext p
      simp only [weightedPrimePowerMajorant, tsum_mul_left, hgeom]
      ring
    rw [heq]
    exact hp.mul_left (75 / 2 : ℝ)

theorem summable_weightedPrimePowerTail
    {w : ℕ → ℝ} (hw0 : ∀ p, 0 ≤ w p)
    (hw : ∀ p, w p ≤ 5 / 2) (hw2 : w 2 ≤ 1) :
    Summable (weightedPrimePowerTail w) :=
  summable_weightedPrimePowerMajorant.of_nonneg_of_le
    (fun _pk ↦ weightedNonprimeMangoldtTerm_nonneg hw0 _)
    (weightedPrimePowerTail_le_majorant hw0 hw hw2)

/-- The normalized weighted von Mangoldt contribution from non-prime
prime powers is summable. -/
theorem summable_weightedNonprimeMangoldtTerm
    {w : ℕ → ℝ} (hw0 : ∀ p, 0 ≤ w p)
    (hw : ∀ p, w p ≤ 5 / 2) (hw2 : w 2 ≤ 1) :
    Summable (weightedNonprimeMangoldtTerm w) := by
  have hprime (p : Nat.Primes) :
      weightedNonprimeMangoldtTerm w p = 0 := by
    simp [weightedNonprimeMangoldtTerm, p.prop]
  refine (summable_subtype_iff_indicator
    (s := {n : ℕ | IsPrimePow n}).mp ?_).congr
      fun n ↦ Set.indicator_apply_eq_self.mpr
        fun (hn : ¬ IsPrimePow n) ↦ ?_
  swap
  · simp [weightedNonprimeMangoldtTerm,
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn]
  have hequiv :
      weightedNonprimeMangoldtTerm w ∘
          Subtype.val (p := fun n : ℕ ↦ n ∈ {n | IsPrimePow n}) =
        weightedPrimePowerAll w ∘ ⇑Nat.Primes.prodNatEquiv.symm := by
    refine (Equiv.eq_comp_symm Nat.Primes.prodNatEquiv
      (weightedNonprimeMangoldtTerm w ∘ Subtype.val)
      (weightedPrimePowerAll w)).mpr ?_
    ext n
    simp only [Function.comp_apply, weightedPrimePowerAll]
    congr
  rw [hequiv]
  refine (Nat.Primes.prodNatEquiv.symm.summable_iff
    (f := weightedPrimePowerAll w)).mpr ?_
  have hzero (p : Nat.Primes) :
      weightedPrimePowerAll w (p, 0) = 0 := by
    simpa [weightedPrimePowerAll] using hprime p
  have hshift :
      weightedPrimePowerTail w =
        weightedPrimePowerAll w ∘
          (Prod.map _root_.id (· + 1)) := by
    ext pk
    simp [weightedPrimePowerTail, weightedPrimePowerAll]
  refine (Function.Injective.summable_iff ?_ fun u hu ↦ ?_).mp <|
    hshift ▸ summable_weightedPrimePowerTail hw0 hw hw2
  · exact Function.Injective.prodMap
      (fun ⦃a₁ a₂⦄ h ↦ h) (add_left_injective 1)
  · simp only [Set.range_prodMap, Set.range_id, Set.mem_prod,
      Set.mem_univ, Set.mem_range, Nat.exists_add_one_eq,
      true_and, not_lt, nonpos_iff_eq_zero] at hu
    rw [← hzero u.1, ← hu]

/-- The finite constant contributed by non-prime prime powers. -/
noncomputable def weightedMangoldtTailConstant
    (w : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ, weightedNonprimeMangoldtTerm w n

theorem weightedMangoldtTailConstant_nonneg
    {w : ℕ → ℝ} (hw0 : ∀ p, 0 ≤ w p) :
    0 ≤ weightedMangoldtTailConstant w := by
  unfold weightedMangoldtTailConstant
  exact tsum_nonneg fun n ↦
    weightedNonprimeMangoldtTerm_nonneg hw0 n

/-- Every finite portion of the normalized non-prime tail is bounded
by its total mass. -/
theorem sum_weightedNonprimeMangoldtTerm_le_tailConstant
    {w : ℕ → ℝ} (hw0 : ∀ p, 0 ≤ w p)
    (hw : ∀ p, w p ≤ 5 / 2) (hw2 : w 2 ≤ 1)
    (s : Finset ℕ) :
    (∑ n ∈ s, weightedNonprimeMangoldtTerm w n) ≤
      weightedMangoldtTailConstant w := by
  exact (summable_weightedNonprimeMangoldtTerm hw0 hw hw2).sum_le_tsum
    s (fun n _ ↦ weightedNonprimeMangoldtTerm_nonneg hw0 n)

/-- Prime inputs contribute at most `5/2` times Chebyshev's `ψ`
function. -/
theorem factorWeight_prime_vonMangoldt_le
    {w : ℕ → ℝ} (hw : ∀ p, w p ≤ 5 / 2) (X : ℕ) :
    (∑ d ∈ (Icc 1 X).filter Nat.Prime,
      factorWeight w d * ArithmeticFunction.vonMangoldt d) ≤
        (5 / 2) * (log 4 + 4) * X := by
  calc
    (∑ d ∈ (Icc 1 X).filter Nat.Prime,
        factorWeight w d * ArithmeticFunction.vonMangoldt d) ≤
        ∑ d ∈ (Icc 1 X).filter Nat.Prime,
          (5 / 2) * ArithmeticFunction.vonMangoldt d := by
      apply sum_le_sum
      intro d hd
      have hdprime : d.Prime := (mem_filter.mp hd).2
      rw [factorWeight_prime hdprime]
      exact mul_le_mul_of_nonneg_right (hw d)
        ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ ∑ d ∈ Icc 1 X,
          (5 / 2) * ArithmeticFunction.vonMangoldt d := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro d _ _
      exact mul_nonneg (by norm_num)
        (@ArithmeticFunction.vonMangoldt_nonneg d)
    _ = (5 / 2) * Chebyshev.psi X := by
      rw [← mul_sum]
      congr 1
      simp [Chebyshev.psi, ← Icc_succ_left_eq_Ioc]
    _ ≤ (5 / 2) * ((log 4 + 4) * X) := by
      gcongr
      exact Chebyshev.psi_le_const_mul_self (by positivity)
    _ = (5 / 2) * (log 4 + 4) * X := by ring

/-- The non-prime prime-power portion of the unnormalized moment is at
most `X` times the convergent normalized tail. -/
theorem factorWeight_nonprime_vonMangoldt_le
    {w : ℕ → ℝ} (hw0 : ∀ p, 0 ≤ w p)
    (hw : ∀ p, w p ≤ 5 / 2) (hw2 : w 2 ≤ 1)
    (X : ℕ) :
    (∑ d ∈ (Icc 1 X).filter (fun d ↦ ¬d.Prime),
      factorWeight w d * ArithmeticFunction.vonMangoldt d) ≤
        weightedMangoldtTailConstant w * X := by
  calc
    (∑ d ∈ (Icc 1 X).filter (fun d ↦ ¬d.Prime),
        factorWeight w d * ArithmeticFunction.vonMangoldt d) ≤
        ∑ d ∈ (Icc 1 X).filter (fun d ↦ ¬d.Prime),
          X * weightedNonprimeMangoldtTerm w d := by
      apply sum_le_sum
      intro d hd
      have hdIcc := (mem_filter.mp hd).1
      have hdnotprime := (mem_filter.mp hd).2
      have hdpos : (0 : ℝ) < d := by
        exact_mod_cast (mem_Icc.mp hdIcc).1
      have hterm :
          factorWeight w d * ArithmeticFunction.vonMangoldt d =
            d * weightedNonprimeMangoldtTerm w d := by
        rw [weightedNonprimeMangoldtTerm, if_neg hdnotprime]
        field_simp
      rw [hterm]
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast (mem_Icc.mp hdIcc).2)
        (weightedNonprimeMangoldtTerm_nonneg hw0 d)
    _ = X * ∑ d ∈ (Icc 1 X).filter (fun d ↦ ¬d.Prime),
          weightedNonprimeMangoldtTerm w d := by
      rw [mul_sum]
    _ ≤ X * weightedMangoldtTailConstant w := by
      exact mul_le_mul_of_nonneg_left
        (sum_weightedNonprimeMangoldtTerm_le_tailConstant
          hw0 hw hw2 _) (Nat.cast_nonneg X)
    _ = weightedMangoldtTailConstant w * X := by ring

/-- A finite explicit-plus-defined constant for the complete weighted
von Mangoldt moment. -/
noncomputable def weightedMangoldtConstant
    (w : ℕ → ℝ) : ℝ :=
  (5 / 2) * (log 4 + 4) + weightedMangoldtTailConstant w

theorem weightedMangoldtConstant_nonneg
    {w : ℕ → ℝ} (hw0 : ∀ p, 0 ≤ w p) :
    0 ≤ weightedMangoldtConstant w := by
  unfold weightedMangoldtConstant
  positivity [weightedMangoldtTailConstant_nonneg hw0]

/-- Uniform linear bound for the weighted von Mangoldt moment under
the local constraints `0 ≤ w(p) ≤ 5/2` and `w(2) ≤ 1`. -/
theorem factorWeight_vonMangoldt_le_five_halves
    {w : ℕ → ℝ} (hw0 : ∀ p, 0 ≤ w p)
    (hw : ∀ p, w p ≤ 5 / 2) (hw2 : w 2 ≤ 1)
    (X : ℕ) :
    (∑ d ∈ Icc 1 X,
      factorWeight w d * ArithmeticFunction.vonMangoldt d) ≤
        weightedMangoldtConstant w * X := by
  rw [← sum_filter_add_sum_filter_not (Icc 1 X)
    Nat.Prime (fun d ↦
      factorWeight w d * ArithmeticFunction.vonMangoldt d)]
  calc
    (∑ d ∈ (Icc 1 X).filter Nat.Prime,
        factorWeight w d * ArithmeticFunction.vonMangoldt d) +
      ∑ d ∈ (Icc 1 X).filter (fun d ↦ ¬d.Prime),
        factorWeight w d * ArithmeticFunction.vonMangoldt d ≤
        ((5 / 2) * (log 4 + 4)) * X +
          weightedMangoldtTailConstant w * X :=
      add_le_add (factorWeight_prime_vonMangoldt_le hw X)
        (factorWeight_nonprime_vonMangoldt_le hw0 hw hw2 X)
    _ = weightedMangoldtConstant w * X := by
      unfold weightedMangoldtConstant
      ring

/-- Finite-Euler-product Halberstam--Richert bound for factor weights
whose local values lie in `[0, 5/2]`, with the value at `2` at most
one. -/
theorem factorWeight_partialSum_le_eulerProduct_five_halves
    {w : ℕ → ℝ} (hw0 : ∀ p, 0 ≤ w p)
    (hw : ∀ p, w p ≤ 5 / 2) (hw2 : w 2 ≤ 1)
    {Y : ℕ} (hY : 2 ≤ Y) :
    partialSum (factorWeight w) Y ≤
      ((weightedMangoldtConstant w + 1) * Y / log Y) *
        Y.factorial.factorization.prod (fun p e ↦
          ∑ k ∈ range (e + 1), ((w p) / p) ^ k) := by
  have h := partialSum_le_eulerProduct
    (g := factorWeight w) (C := weightedMangoldtConstant w)
    (factorWeight_nonneg hw0)
    (factorWeight_one w)
    (factorWeight_isMultiplicative w).2
    factorWeight_submultiplicative
    (weightedMangoldtConstant_nonneg hw0)
    (factorWeight_vonMangoldt_le_five_halves hw0 hw hw2)
    hY
  rw [factorWeight_eulerProduct_eq] at h
  exact h

end Erdos327.Analytic
