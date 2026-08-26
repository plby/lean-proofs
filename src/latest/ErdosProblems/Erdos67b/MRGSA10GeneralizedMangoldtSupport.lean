import ErdosProblems.Erdos67b.MRGSA9GeneralizedMangoldt

/-!
# Prime-power support of generalized Mangoldt coefficients

For a multiplicative arithmetic function `a`, its logarithmic derivative
`(a · log) * a⁻¹` is supported on prime powers.  This is the structural fact
needed before estimating the two generalized-Mangoldt factors in the finite
GS A.10 identity.  The proof is purely finite Dirichlet-convolution algebra.
-/

open scoped BigOperators

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- Restriction of an arithmetic function to positive prime powers. -/
def gsPrimePowerPart (u : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n ↦ if IsPrimePow n then u n else 0, by simp [not_isPrimePow_zero]⟩

@[simp] theorem gsPrimePowerPart_apply (u : ArithmeticFunction ℂ) (n : ℕ) :
    gsPrimePowerPart u n = if IsPrimePow n then u n else 0 := rfl

@[simp] theorem gsPrimePowerPart_one (u : ArithmeticFunction ℂ) :
    gsPrimePowerPart u 1 = 0 := by
  simp [gsPrimePowerPart, not_isPrimePow_one]

/-- On a prime power, restriction to prime powers changes nothing, apart
from the exponent-zero case where both sides vanish for a generalized
Mangoldt coefficient. -/
theorem gsPrimePowerPart_gsGeneralizedMangoldt_apply_prime_pow
    (a : ArithmeticFunction ℂ) (ha : Invertible (a 1))
    (p k : ℕ) (hp : p.Prime) :
    gsPrimePowerPart (gsGeneralizedMangoldt a ha) (p ^ k) =
      gsGeneralizedMangoldt a ha (p ^ k) := by
  by_cases hk : k = 0
  · subst k
    simp [gsPrimePowerPart, gsGeneralizedMangoldt_one]
  · rw [gsPrimePowerPart_apply, if_pos]
    exact hp.isPrimePow.pow hk

private theorem gsPrimePowerPart_mul_self_apply_prime_pow
    (a : ArithmeticFunction ℂ) (ha : Invertible (a 1))
    (p k : ℕ) (hp : p.Prime) :
    (gsPrimePowerPart (gsGeneralizedMangoldt a ha) * a) (p ^ k) =
      gsLogWeighted a (p ^ k) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y ↦
      gsPrimePowerPart (gsGeneralizedMangoldt a ha) x * a y)]
  have hconv := congrFun
    (congrArg DFunLike.coe (gsGeneralizedMangoldt_mul_self a ha)) (p ^ k)
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y ↦
      gsGeneralizedMangoldt a ha x * a y)] at hconv
  rw [← hconv]
  apply Finset.sum_congr rfl
  intro d hd
  have hdvd : d ∣ p ^ k := (Nat.mem_divisors.mp hd).1
  rcases (Nat.dvd_prime_pow hp).mp hdvd with ⟨j, hj, rfl⟩
  rw [gsPrimePowerPart_gsGeneralizedMangoldt_apply_prime_pow a ha p j hp]

private theorem gsPrimePowerPart_mul_self_apply_coprime
    (a : ArithmeticFunction ℂ) (ha : Invertible (a 1))
    (haMult : a.IsMultiplicative)
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n) (hmn : m.Coprime n)
    (hleft :
      (gsPrimePowerPart (gsGeneralizedMangoldt a ha) * a) m =
        gsLogWeighted a m)
    (hright :
      (gsPrimePowerPart (gsGeneralizedMangoldt a ha) * a) n =
        gsLogWeighted a n) :
    (gsPrimePowerPart (gsGeneralizedMangoldt a ha) * a) (m * n) =
      gsLogWeighted a (m * n) := by
  classical
  let u := gsPrimePowerPart (gsGeneralizedMangoldt a ha)
  have hm0 : m ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_one hm)
  have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_one hn)
  have hmn0 : m * n ≠ 0 := mul_ne_zero hm0 hn0
  have hfilter (r : ℕ) (hr0 : r ≠ 0) :
      ∑ d ∈ r.divisors, u d * a (r / d) =
        ∑ d ∈ r.divisors.filter IsPrimePow, u d * a (r / d) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hpp : IsPrimePow d
    · simp [hpp]
    · simp [hpp, u, gsPrimePowerPart]
  have hquotLeft {d : ℕ} (hd : d ∈ m.divisors) :
      (m * n) / d = (m / d) * n := by
    rw [mul_comm m n, Nat.mul_div_assoc n (Nat.mem_divisors.mp hd).1,
      mul_comm]
  have hquotRight {d : ℕ} (hd : d ∈ n.divisors) :
      (m * n) / d = m * (n / d) := by
    rw [Nat.mul_div_assoc m (Nat.mem_divisors.mp hd).1]
  have hcopLeft {d : ℕ} (hd : d ∈ m.divisors) :
      (m / d).Coprime n :=
    hmn.of_dvd_left (Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hd).1)
  have hcopRight {d : ℕ} (hd : d ∈ n.divisors) :
      m.Coprime (n / d) :=
    hmn.of_dvd_right (Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hd).1)
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y ↦ u x * a y),
    hfilter (m * n) hmn0, Nat.mul_divisors_filter_prime_pow hmn,
    Finset.filter_union,
    Finset.sum_union (Nat.disjoint_divisors_filter_isPrimePow hmn)]
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y ↦ u x * a y),
    hfilter m hm0] at hleft
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y ↦ u x * a y),
    hfilter n hn0] at hright
  have hsumLeft :
      ∑ d ∈ m.divisors.filter IsPrimePow, u d * a ((m * n) / d) =
        gsLogWeighted a m * a n := by
    calc
      _ = ∑ d ∈ m.divisors.filter IsPrimePow,
          (u d * a (m / d)) * a n := by
        apply Finset.sum_congr rfl
        intro d hd
        have hd' : d ∈ m.divisors := (Finset.mem_filter.mp hd).1
        rw [hquotLeft hd', haMult.map_mul_of_coprime (hcopLeft hd')]
        ring
      _ = (∑ d ∈ m.divisors.filter IsPrimePow,
          u d * a (m / d)) * a n := by rw [Finset.sum_mul]
      _ = gsLogWeighted a m * a n := by rw [hleft]
  have hsumRight :
      ∑ d ∈ n.divisors.filter IsPrimePow, u d * a ((m * n) / d) =
        a m * gsLogWeighted a n := by
    calc
      _ = ∑ d ∈ n.divisors.filter IsPrimePow,
          a m * (u d * a (n / d)) := by
        apply Finset.sum_congr rfl
        intro d hd
        have hd' : d ∈ n.divisors := (Finset.mem_filter.mp hd).1
        rw [hquotRight hd', haMult.map_mul_of_coprime (hcopRight hd')]
        ring
      _ = a m * (∑ d ∈ n.divisors.filter IsPrimePow,
          u d * a (n / d)) := by rw [Finset.mul_sum]
      _ = a m * gsLogWeighted a n := by rw [hright]
  rw [hsumLeft, hsumRight]
  rw [gsLogWeighted_apply, gsLogWeighted_apply, gsLogWeighted_apply,
    haMult.map_mul_of_coprime hmn, Nat.cast_mul,
    Real.log_mul (by exact_mod_cast hm0) (by exact_mod_cast hn0)]
  push_cast
  ring

/-- The prime-power restriction of a generalized Mangoldt coefficient has
the same convolution with the original multiplicative function. -/
theorem gsPrimePowerPart_gsGeneralizedMangoldt_mul_self
    (a : ArithmeticFunction ℂ) (ha : Invertible (a 1))
    (haMult : a.IsMultiplicative) :
    gsPrimePowerPart (gsGeneralizedMangoldt a ha) * a = gsLogWeighted a := by
  ext n
  induction n using Nat.recOnPrimeCoprime with
  | zero => simp [gsPrimePowerPart, gsLogWeighted]
  | prime_pow p k hp =>
      exact gsPrimePowerPart_mul_self_apply_prime_pow a ha p k hp
  | coprime m n hm hn hmn hleft hright =>
      exact gsPrimePowerPart_mul_self_apply_coprime
        a ha haMult hm hn hmn hleft hright

/-- A generalized Mangoldt coefficient of a multiplicative arithmetic
function vanishes away from positive prime powers. -/
theorem gsGeneralizedMangoldt_eq_zero_of_not_isPrimePow
    (a : ArithmeticFunction ℂ) (ha : Invertible (a 1))
    (haMult : a.IsMultiplicative) {n : ℕ} (hn : ¬ IsPrimePow n) :
    gsGeneralizedMangoldt a ha n = 0 := by
  have hmul := gsPrimePowerPart_gsGeneralizedMangoldt_mul_self a ha haMult
  have heq : gsPrimePowerPart (gsGeneralizedMangoldt a ha) =
      gsGeneralizedMangoldt a ha := by
    calc
      gsPrimePowerPart (gsGeneralizedMangoldt a ha) =
          gsPrimePowerPart (gsGeneralizedMangoldt a ha) * 1 := by rw [mul_one]
      _ = gsPrimePowerPart (gsGeneralizedMangoldt a ha) *
          (a * ArithmeticFunction.dirichletInverse a ha) := by
            rw [ArithmeticFunction.self_mul_dirichletInverse]
      _ = (gsPrimePowerPart (gsGeneralizedMangoldt a ha) * a) *
          ArithmeticFunction.dirichletInverse a ha := by rw [mul_assoc]
      _ = gsLogWeighted a * ArithmeticFunction.dirichletInverse a ha := by
            rw [hmul]
      _ = gsGeneralizedMangoldt a ha := rfl
  have happ := congrFun (congrArg DFunLike.coe heq) n
  simpa [gsPrimePowerPart, hn] using happ.symm

end

end Erdos67b.MRHalaszBands
