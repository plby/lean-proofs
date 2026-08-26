import ErdosProblems.Erdos327.Analytic.Mertens

namespace Erdos327.Analytic

open Finset Real

/-- The partial sum of a nonnegative arithmetic weight.  We use `Icc 1 Y`
so that all logarithms and reciprocals below are taken at positive
integers. -/
noncomputable def partialSum (g : ℕ → ℝ) (Y : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 Y, g n

/-- The harmonic partial sum associated to an arithmetic weight. -/
noncomputable def harmonicSum (g : ℕ → ℝ) (Y : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 Y, g n / n

/-- The arithmetic function `n ↦ g(n) / n`, with the conventional value
zero at `n = 0`. -/
noncomputable def harmonicArithmetic (g : ℕ → ℝ) :
    ArithmeticFunction ℝ where
  toFun n := if n = 0 then 0 else g n / n
  map_zero' := by simp

@[simp] theorem harmonicArithmetic_zero (g : ℕ → ℝ) :
    harmonicArithmetic g 0 = 0 := by
  simp [harmonicArithmetic]

theorem harmonicArithmetic_apply {g : ℕ → ℝ}
    {n : ℕ} (hn : n ≠ 0) :
    harmonicArithmetic g n = g n / n := by
  simp [harmonicArithmetic, hn]

theorem harmonicArithmetic_isMultiplicative
    {g : ℕ → ℝ} (hg1 : g 1 = 1)
    (hgMul : ∀ {a b : ℕ}, Nat.Coprime a b →
      g (a * b) = g a * g b) :
    (harmonicArithmetic g).IsMultiplicative := by
  refine ⟨by simp [harmonicArithmetic, hg1], ?_⟩
  intro a b hab
  by_cases ha : a = 0
  · subst a
    simp [harmonicArithmetic]
  by_cases hb : b = 0
  · subst b
    simp [harmonicArithmetic]
  have hab0 : a * b ≠ 0 := Nat.mul_ne_zero ha hb
  simp only [harmonicArithmetic_apply hab0,
    harmonicArithmetic_apply ha, harmonicArithmetic_apply hb,
    hgMul hab]
  push_cast
  field_simp

/-- Positive factor pairs whose product is at most `Y`. -/
def hyperbola (Y : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 Y) ×ˢ (Icc 1 Y)).filter fun x ↦ x.1 * x.2 ≤ Y

@[simp] theorem mem_hyperbola {Y : ℕ} {x : ℕ × ℕ} :
    x ∈ hyperbola Y ↔
      1 ≤ x.1 ∧ 1 ≤ x.2 ∧ x.1 * x.2 ≤ Y := by
  simp only [hyperbola, mem_filter, mem_product, mem_Icc]
  constructor
  · rintro ⟨⟨⟨hx1, _hxY1⟩, ⟨hx2, _hxY2⟩⟩, hmul⟩
    exact ⟨hx1, hx2, hmul⟩
  · rintro ⟨hx1, hx2, hmul⟩
    exact ⟨⟨⟨hx1, le_trans (Nat.le_mul_of_pos_right _ hx2) hmul⟩,
      ⟨hx2, le_trans (Nat.le_mul_of_pos_left _ hx1) hmul⟩⟩, hmul⟩

/-- Regroup a sum over positive integers and their divisor pairs as a
sum over the integer hyperbola. -/
theorem sum_divisorPairs_eq_sum_hyperbola
    (f : ℕ × ℕ → ℝ) (Y : ℕ) :
    (∑ n ∈ Icc 1 Y, ∑ x ∈ n.divisorsAntidiagonal, f x) =
      ∑ x ∈ hyperbola Y, f x := by
  rw [Finset.sum_sigma']
  apply Finset.sum_bij (fun x _ ↦ x.2)
  · intro x hx
    rw [mem_sigma] at hx
    rw [mem_hyperbola]
    have hpair := Nat.mem_divisorsAntidiagonal.mp hx.2
    have hn := mem_Icc.mp hx.1
    have hprodne : x.2.1 * x.2.2 ≠ 0 := by
      intro hzero
      apply hpair.2
      rw [← hpair.1, hzero]
    exact ⟨Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero_iff.mp hprodne).1,
      Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero_iff.mp hprodne).2,
      by simpa [hpair.1] using hn.2⟩
  · intro x₁ hx₁ x₂ hx₂ heq
    rw [mem_sigma] at hx₁ hx₂
    have h₁ := (Nat.mem_divisorsAntidiagonal.mp hx₁.2).1
    have h₂ := (Nat.mem_divisorsAntidiagonal.mp hx₂.2).1
    apply Sigma.ext
    · exact h₁.symm.trans
        ((congrArg (fun z : ℕ × ℕ ↦ z.1 * z.2) heq).trans h₂)
    · exact heq_of_eq heq
  · intro x hx
    have hx' := mem_hyperbola.mp hx
    refine ⟨⟨x.1 * x.2, x⟩, ?_, rfl⟩
    rw [mem_sigma]
    have hmulne := Nat.mul_ne_zero
      (Nat.one_le_iff_ne_zero.mp hx'.1)
      (Nat.one_le_iff_ne_zero.mp hx'.2.1)
    exact ⟨mem_Icc.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr hmulne, hx'.2.2⟩,
      Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, hmulne⟩⟩
  · intro x hx
    rfl

/-- Regroup the hyperbola by its second coordinate. -/
theorem sum_hyperbola_eq_nested
    (f : ℕ → ℕ → ℝ) (Y : ℕ) :
    (∑ x ∈ hyperbola Y, f x.1 x.2) =
      ∑ m ∈ Icc 1 Y, ∑ d ∈ Icc 1 (Y / m), f d m := by
  rw [Finset.sum_sigma']
  symm
  apply Finset.sum_bij (fun x _ ↦ (x.2, x.1))
  · intro x hx
    rw [mem_sigma] at hx
    have hm := mem_Icc.mp hx.1
    have hd := mem_Icc.mp hx.2
    rw [mem_hyperbola]
    exact ⟨hd.1, hm.1, (Nat.le_div_iff_mul_le hm.1).mp hd.2⟩
  · intro x₁ hx₁ x₂ hx₂ heq
    cases x₁
    cases x₂
    simp_all
  · intro x hx
    have hx' := mem_hyperbola.mp hx
    refine ⟨⟨x.2, x.1⟩, ?_, by simp⟩
    rw [mem_sigma]
    exact ⟨mem_Icc.mpr ⟨hx'.2.1,
      le_trans (Nat.le_mul_of_pos_left _ hx'.1) hx'.2.2⟩,
      mem_Icc.mpr ⟨hx'.1,
        (Nat.le_div_iff_mul_le hx'.2.1).mpr hx'.2.2⟩⟩
  · intro x hx
    rfl

theorem harmonicSum_nonneg {g : ℕ → ℝ}
    (hg : ∀ n, 0 ≤ g n) (Y : ℕ) :
    0 ≤ harmonicSum g Y := by
  unfold harmonicSum
  apply sum_nonneg
  intro n _
  exact div_nonneg (hg n) (by positivity)

/-- Every positive `n ≤ Y` divides `Y!`, so its harmonic weight occurs
in the full divisor sum of `Y!`. -/
theorem harmonicSum_le_factorialDivisorSum
    {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) (Y : ℕ) :
    harmonicSum g Y ≤
      ∑ d ∈ Y.factorial.divisors, harmonicArithmetic g d := by
  unfold harmonicSum
  calc
    (∑ n ∈ Icc 1 Y, g n / n)
        = ∑ n ∈ Icc 1 Y, harmonicArithmetic g n := by
          apply sum_congr rfl
          intro n hn
          exact (harmonicArithmetic_apply
            (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hn).1)).symm
    _ ≤ ∑ d ∈ Y.factorial.divisors, harmonicArithmetic g d := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro n hn
        rw [Nat.mem_divisors]
        exact ⟨Nat.dvd_factorial (mem_Icc.mp hn).1 (mem_Icc.mp hn).2,
          Nat.factorial_ne_zero Y⟩
      · intro n hnfac _
        have hnpos : 0 < n := Nat.pos_of_dvd_of_pos
          (Nat.dvd_of_mem_divisors hnfac) (Nat.factorial_pos Y)
        rw [harmonicArithmetic_apply hnpos.ne']
        exact div_nonneg (hg n) (by positivity)

/-- The divisor sum of a multiplicative arithmetic function over `Y!`
is a finite Euler product. -/
theorem factorialDivisorSum_eq_eulerProduct
    {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative)
    (Y : ℕ) :
    (∑ d ∈ Y.factorial.divisors, f d) =
      Y.factorial.factorization.prod fun p e ↦
        ∑ k ∈ range (e + 1), f (p ^ k) := by
  rw [← ArithmeticFunction.coe_mul_zeta_apply,
    (hf.mul ArithmeticFunction.isMultiplicative_zeta.natCast).multiplicative_factorization
      (f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ))
      (Nat.factorial_ne_zero Y)]
  apply Finsupp.prod_congr
  intro p hp
  rw [ArithmeticFunction.coe_mul_zeta_apply,
    Nat.sum_divisors_prime_pow
      (Nat.prime_of_mem_primeFactors
        (by simpa [Nat.support_factorization] using hp))]

/-- Finite Euler-product majorant for the harmonic sum. -/
theorem harmonicSum_le_eulerProduct
    {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n)
    (hg1 : g 1 = 1)
    (hgMul : ∀ {a b : ℕ}, Nat.Coprime a b →
      g (a * b) = g a * g b)
    (Y : ℕ) :
    harmonicSum g Y ≤
      Y.factorial.factorization.prod fun p e ↦
        ∑ k ∈ range (e + 1), harmonicArithmetic g (p ^ k) := by
  calc
    harmonicSum g Y
        ≤ ∑ d ∈ Y.factorial.divisors, harmonicArithmetic g d :=
      harmonicSum_le_factorialDivisorSum hg Y
    _ = _ := factorialDivisorSum_eq_eulerProduct
      (harmonicArithmetic_isMultiplicative hg1 hgMul) Y

/-- A pointwise submultiplicative majorant turns the von Mangoldt divisor
identity into an upper bound for `g(n) log n`. -/
theorem mul_log_le_sum_divisorPairs
    {g : ℕ → ℝ} (hgMul : ∀ a b, g (a * b) ≤ g a * g b)
    {n : ℕ} (_hn : n ≠ 0) :
    g n * log n ≤
      ∑ x ∈ n.divisorsAntidiagonal,
        g x.1 * g x.2 * ArithmeticFunction.vonMangoldt x.1 := by
  rw [← ArithmeticFunction.vonMangoldt_sum, mul_sum,
    Nat.sum_divisorsAntidiagonal
      (fun d m ↦ g d * g m * ArithmeticFunction.vonMangoldt d)]
  apply sum_le_sum
  intro d hd
  have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hfactor : d * (n / d) = n := Nat.mul_div_cancel' hdvd
  have hmul := hgMul d (n / d)
  rw [hfactor] at hmul
  exact mul_le_mul_of_nonneg_right hmul
    ArithmeticFunction.vonMangoldt_nonneg

/-- The convolution step of the completely submultiplicative
Halberstam--Richert estimate. -/
theorem logMoment_le_harmonic
    {g : ℕ → ℝ} {C : ℝ}
    (hg : ∀ n, 0 ≤ g n)
    (hgMul : ∀ a b, g (a * b) ≤ g a * g b)
    (hC : 0 ≤ C)
    (hMangoldt :
      ∀ X : ℕ,
        (∑ d ∈ Icc 1 X,
          g d * ArithmeticFunction.vonMangoldt d) ≤ C * X)
    (Y : ℕ) :
    (∑ n ∈ Icc 1 Y, g n * log n)
      ≤ C * Y * harmonicSum g Y := by
  calc
    (∑ n ∈ Icc 1 Y, g n * log n)
        ≤ ∑ n ∈ Icc 1 Y,
            ∑ x ∈ n.divisorsAntidiagonal,
              g x.1 * g x.2 *
                ArithmeticFunction.vonMangoldt x.1 := by
          apply sum_le_sum
          intro n hn
          exact mul_log_le_sum_divisorPairs hgMul
            (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hn).1)
    _ = ∑ x ∈ hyperbola Y,
          g x.1 * g x.2 *
            ArithmeticFunction.vonMangoldt x.1 :=
      sum_divisorPairs_eq_sum_hyperbola _ _
    _ = ∑ m ∈ Icc 1 Y,
          ∑ d ∈ Icc 1 (Y / m),
            g d * g m * ArithmeticFunction.vonMangoldt d := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        sum_hyperbola_eq_nested
          (fun d m ↦
            g d * g m * ArithmeticFunction.vonMangoldt d) Y
    _ = ∑ m ∈ Icc 1 Y,
          g m * (∑ d ∈ Icc 1 (Y / m),
            g d * ArithmeticFunction.vonMangoldt d) := by
      apply sum_congr rfl
      intro m _
      rw [mul_sum]
      apply sum_congr rfl
      intro d _
      ring
    _ ≤ ∑ m ∈ Icc 1 Y, g m * (C * (Y / m : ℕ)) := by
      apply sum_le_sum
      intro m _
      exact mul_le_mul_of_nonneg_left (hMangoldt (Y / m)) (hg m)
    _ ≤ ∑ m ∈ Icc 1 Y, C * Y * (g m / m) := by
      apply sum_le_sum
      intro m _
      calc
        g m * (C * (Y / m : ℕ))
            ≤ g m * (C * ((Y : ℝ) / m)) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left
                  (Nat.cast_div_le (α := ℝ) (m := Y) (n := m)) hC)
                (hg m)
        _ = C * Y * (g m / m) := by ring
    _ = C * Y * harmonicSum g Y := by
      unfold harmonicSum
      rw [mul_sum]

/-- The elementary final step in the Halberstam--Richert argument.

Once the logarithmically weighted moment is at most
`C * Y * harmonicSum g Y`, the unweighted moment loses only one further
copy of `Y * harmonicSum g Y`.  No multiplicativity is used in this step.
-/
theorem partialSum_le_of_logMoment
    {g : ℕ → ℝ} {C : ℝ} (hg : ∀ n, 0 ≤ g n)
    {Y : ℕ} (hY : 2 ≤ Y)
    (hlog :
      (∑ n ∈ Icc 1 Y, g n * log n)
        ≤ C * Y * harmonicSum g Y) :
    partialSum g Y
      ≤ ((C + 1) * Y / log Y) * harmonicSum g Y := by
  have hlogY : 0 < log (Y : ℝ) := log_pos (by norm_num; omega)
  have htail :
      (∑ n ∈ Icc 1 Y, g n * (log Y - log n))
        ≤ (Y : ℝ) * harmonicSum g Y := by
    unfold harmonicSum
    calc
      (∑ n ∈ Icc 1 Y, g n * (log Y - log n))
          ≤ ∑ n ∈ Icc 1 Y, g n * ((Y : ℝ) / n) := by
            apply sum_le_sum
            intro n hn
            have hn' := mem_Icc.mp hn
            have hnpos : (0 : ℝ) < n := by
              exact_mod_cast hn'.1
            have hYpos : (0 : ℝ) < Y := by
              exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hY)
            have hratio : 0 < (Y : ℝ) / n := div_pos hYpos hnpos
            have hlogeq :
                log (Y : ℝ) - log (n : ℝ) =
                  log ((Y : ℝ) / n) := by
              rw [log_div hYpos.ne' hnpos.ne']
            rw [hlogeq]
            exact mul_le_mul_of_nonneg_left
              ((log_le_sub_one_of_pos hratio).trans
                (sub_le_self _ zero_le_one))
              (hg n)
      _ = (Y : ℝ) * ∑ n ∈ Icc 1 Y, g n / n := by
            rw [mul_sum]
            apply sum_congr rfl
            intro n _
            ring
  have hdecomp :
      partialSum g Y * log Y =
        (∑ n ∈ Icc 1 Y, g n * log n) +
        ∑ n ∈ Icc 1 Y, g n * (log Y - log n) := by
    unfold partialSum
    rw [sum_mul, ← sum_add_distrib]
    apply sum_congr rfl
    intro n _
    ring
  have hmoment :
      partialSum g Y * log Y
        ≤ (C + 1) * (Y : ℝ) * harmonicSum g Y := by
    rw [hdecomp]
    calc
      _ ≤ C * Y * harmonicSum g Y +
          Y * harmonicSum g Y := add_le_add hlog htail
      _ = (C + 1) * Y * harmonicSum g Y := by ring
  calc
    partialSum g Y
        ≤ ((C + 1) * Y * harmonicSum g Y) / log Y :=
      (le_div_iff₀ hlogY).2 hmoment
    _ = ((C + 1) * Y / log Y) * harmonicSum g Y := by ring

/-- A completely submultiplicative Halberstam--Richert bound with the
prime-power bookkeeping compressed into a von Mangoldt moment hypothesis.
The remaining specialization proves that hypothesis for the three cutoff
weights used in the Erdős 327 construction. -/
theorem partialSum_le_of_vonMangoldtMoment
    {g : ℕ → ℝ} {C : ℝ}
    (hg : ∀ n, 0 ≤ g n)
    (hgMul : ∀ a b, g (a * b) ≤ g a * g b)
    (hC : 0 ≤ C)
    (hMangoldt :
      ∀ X : ℕ,
        (∑ d ∈ Icc 1 X,
          g d * ArithmeticFunction.vonMangoldt d) ≤ C * X)
    {Y : ℕ} (hY : 2 ≤ Y) :
    partialSum g Y
      ≤ ((C + 1) * Y / log Y) * harmonicSum g Y :=
  partialSum_le_of_logMoment hg hY
    (logMoment_le_harmonic hg hgMul hC hMangoldt Y)

/-- Finite-Euler-product form of the completely submultiplicative
Halberstam--Richert estimate. -/
theorem partialSum_le_eulerProduct
    {g : ℕ → ℝ} {C : ℝ}
    (hg : ∀ n, 0 ≤ g n)
    (hg1 : g 1 = 1)
    (hgCoprime : ∀ {a b : ℕ}, Nat.Coprime a b →
      g (a * b) = g a * g b)
    (hgMul : ∀ a b, g (a * b) ≤ g a * g b)
    (hC : 0 ≤ C)
    (hMangoldt :
      ∀ X : ℕ,
        (∑ d ∈ Icc 1 X,
          g d * ArithmeticFunction.vonMangoldt d) ≤ C * X)
    {Y : ℕ} (hY : 2 ≤ Y) :
    partialSum g Y ≤
      ((C + 1) * Y / log Y) *
        Y.factorial.factorization.prod (fun p e ↦
          ∑ k ∈ range (e + 1), harmonicArithmetic g (p ^ k)) := by
  calc
    partialSum g Y
        ≤ ((C + 1) * Y / log Y) * harmonicSum g Y :=
      partialSum_le_of_vonMangoldtMoment hg hgMul hC hMangoldt hY
    _ ≤ _ := by
      gcongr
      exact harmonicSum_le_eulerProduct hg hg1 hgCoprime Y

end Erdos327.Analytic
