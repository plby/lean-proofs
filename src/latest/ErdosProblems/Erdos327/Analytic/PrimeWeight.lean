import ErdosProblems.Erdos327.Analytic.MeanValue

namespace Erdos327.Analytic

open Finset Real

/-- The completely multiplicative weight obtained by assigning a real
weight to every prime factor, counted with multiplicity. -/
noncomputable def factorWeight (w : ℕ → ℝ) :
    ArithmeticFunction ℝ where
  toFun n :=
    if n = 0 then 0 else (n.primeFactorsList.map w).prod
  map_zero' := by simp

@[simp] theorem factorWeight_zero (w : ℕ → ℝ) :
    factorWeight w 0 = 0 := by
  simp [factorWeight]

theorem factorWeight_apply {w : ℕ → ℝ} {n : ℕ} (hn : n ≠ 0) :
    factorWeight w n = (n.primeFactorsList.map w).prod := by
  simp [factorWeight, hn]

@[simp] theorem factorWeight_one (w : ℕ → ℝ) :
    factorWeight w 1 = 1 := by
  simp [factorWeight]

theorem factorWeight_mul {w : ℕ → ℝ} {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    factorWeight w (a * b) =
      factorWeight w a * factorWeight w b := by
  rw [factorWeight_apply (Nat.mul_ne_zero ha hb),
    factorWeight_apply ha, factorWeight_apply hb]
  simpa [List.map_append, List.prod_append] using
    ((Nat.perm_primeFactorsList_mul ha hb).map w).prod_eq

theorem factorWeight_isMultiplicative (w : ℕ → ℝ) :
    (factorWeight w).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨factorWeight_one w, ?_⟩
  intro a b ha hb _
  exact factorWeight_mul ha hb

theorem factorWeight_nonneg {w : ℕ → ℝ}
    (hw : ∀ p, 0 ≤ w p) (n : ℕ) :
    0 ≤ factorWeight w n := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [factorWeight_apply hn]
  apply List.prod_nonneg
  intro x hx
  rcases List.mem_map.mp hx with ⟨p, _hp, rfl⟩
  exact hw p

theorem factorWeight_le_one {w : ℕ → ℝ}
    (hw0 : ∀ p, 0 ≤ w p) (hw1 : ∀ p, w p ≤ 1)
    (n : ℕ) :
    factorWeight w n ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [factorWeight_apply hn]
  induction n.primeFactorsList with
  | nil => simp
  | cons p l ih =>
      simp only [List.map_cons, List.prod_cons]
      have hp0 : 0 ≤ w p := hw0 p
      have hl0 : 0 ≤ (l.map w).prod := by
        apply List.prod_nonneg
        intro x hx
        rcases List.mem_map.mp hx with ⟨q, _hq, rfl⟩
        exact hw0 q
      nlinarith [hw1 p]

theorem factorWeight_mul_all {w : ℕ → ℝ} (a b : ℕ) :
    factorWeight w (a * b) =
      factorWeight w a * factorWeight w b := by
  by_cases ha : a = 0
  · subst a
    simp
  by_cases hb : b = 0
  · subst b
    simp
  exact factorWeight_mul ha hb

theorem factorWeight_submultiplicative {w : ℕ → ℝ} (a b : ℕ) :
    factorWeight w (a * b) ≤
      factorWeight w a * factorWeight w b :=
  (factorWeight_mul_all a b).le

theorem factorWeight_primePow {w : ℕ → ℝ}
    {p k : ℕ} (hp : p.Prime) :
    factorWeight w (p ^ k) = (w p) ^ k := by
  rw [factorWeight_apply (pow_ne_zero k hp.ne_zero),
    hp.primeFactorsList_pow, List.map_replicate, List.prod_replicate]

theorem factorWeight_prime {w : ℕ → ℝ}
    {p : ℕ} (hp : p.Prime) :
    factorWeight w p = w p := by
  simpa using factorWeight_primePow (w := w) hp (k := 1)

theorem harmonicArithmetic_factorWeight_primePow
    {w : ℕ → ℝ} {p k : ℕ} (hp : p.Prime) :
    harmonicArithmetic (factorWeight w) (p ^ k) =
      ((w p) / p) ^ k := by
  rw [harmonicArithmetic_apply (pow_ne_zero k hp.ne_zero),
    factorWeight_primePow hp]
  push_cast
  rw [div_pow]

theorem factorWeight_eulerProduct_eq (w : ℕ → ℝ) (Y : ℕ) :
    Y.factorial.factorization.prod (fun p e ↦
      ∑ k ∈ range (e + 1),
        harmonicArithmetic (factorWeight w) (p ^ k)) =
    Y.factorial.factorization.prod (fun p e ↦
      ∑ k ∈ range (e + 1), ((w p) / p) ^ k) := by
  apply Finsupp.prod_congr
  intro p hp
  apply sum_congr rfl
  intro k _
  exact harmonicArithmetic_factorWeight_primePow
    (Nat.prime_of_mem_primeFactors
      (by simpa [Nat.support_factorization] using hp))

/-- If every local prime weight lies in `[0,1]`, the von Mangoldt moment
has a uniform linear bound supplied by Chebyshev's theorem. -/
theorem factorWeight_vonMangoldt_le
    {w : ℕ → ℝ}
    (hw0 : ∀ p, 0 ≤ w p) (hw1 : ∀ p, w p ≤ 1)
    (X : ℕ) :
    (∑ d ∈ Icc 1 X,
      factorWeight w d * ArithmeticFunction.vonMangoldt d)
      ≤ (log 4 + 4) * X := by
  calc
    (∑ d ∈ Icc 1 X,
        factorWeight w d * ArithmeticFunction.vonMangoldt d)
        ≤ ∑ d ∈ Icc 1 X,
            ArithmeticFunction.vonMangoldt d := by
          apply sum_le_sum
          intro d _
          simpa using mul_le_of_le_one_left
            ArithmeticFunction.vonMangoldt_nonneg
            (factorWeight_le_one hw0 hw1 d)
    _ = Chebyshev.psi X := by
      simp [Chebyshev.psi, ← Icc_succ_left_eq_Ioc]
    _ ≤ (log 4 + 4) * X :=
      Chebyshev.psi_le_const_mul_self (by positivity)

/-- A fully proved finite-Euler-product mean-value bound for any
completely multiplicative prime-factor weight with local values in
`[0,1]`.  This directly covers both residual sums in the paper. -/
theorem factorWeight_partialSum_le_eulerProduct
    {w : ℕ → ℝ}
    (hw0 : ∀ p, 0 ≤ w p) (hw1 : ∀ p, w p ≤ 1)
    {Y : ℕ} (hY : 2 ≤ Y) :
    partialSum (factorWeight w) Y ≤
      ((log 4 + 5) * Y / log Y) *
        Y.factorial.factorization.prod (fun p e ↦
          ∑ k ∈ range (e + 1), ((w p) / p) ^ k) := by
  have h := partialSum_le_eulerProduct
    (g := factorWeight w) (C := log 4 + 4)
    (factorWeight_nonneg hw0)
    (factorWeight_one w)
    (factorWeight_isMultiplicative w).2
    factorWeight_submultiplicative
    (by positivity)
    (factorWeight_vonMangoldt_le hw0 hw1)
    hY
  rw [factorWeight_eulerProduct_eq] at h
  have hc : (log 4 + 4) + 1 = log 4 + 5 := by ring
  simpa only [hc] using h

end Erdos327.Analytic
