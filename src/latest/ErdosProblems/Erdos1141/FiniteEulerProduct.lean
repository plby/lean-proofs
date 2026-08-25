import ErdosProblems.Erdos1141.QuadraticCoefficients
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# A finite Rankin inequality for quadratic divisor coefficients

Only primes below the summation endpoint enter the Euler product.  Thus
the inequality does not require convergence of `ζ(s)L(s,χ)` in the half
plane where Rankin's parameter will be chosen.
-/

namespace Pollack17

open scoped BigOperators

variable {m : ℕ}

noncomputable def weightedDivisorCoefficient (χ : DirichletCharacter ℂ m)
    (s : ℝ) (n : ℕ) : ℝ := divisorCoefficient χ n * (n : ℝ) ^ (-s)

theorem weightedDivisorCoefficient_nonneg (χ : DirichletCharacter ℂ m)
    (hχ : MulChar.IsQuadratic χ) (s : ℝ) (n : ℕ) :
    0 ≤ weightedDivisorCoefficient χ s n :=
  mul_nonneg (divisorCoefficient_nonneg χ hχ n)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

@[simp] theorem weightedDivisorCoefficient_one (χ : DirichletCharacter ℂ m)
    (s : ℝ) : weightedDivisorCoefficient χ s 1 = 1 := by
  simp [weightedDivisorCoefficient]

theorem weightedDivisorCoefficient_mul (χ : DirichletCharacter ℂ m)
    (hχ : MulChar.IsQuadratic χ) (s : ℝ) {a b : ℕ} (hab : a.Coprime b) :
    weightedDivisorCoefficient χ s (a * b) =
      weightedDivisorCoefficient χ s a * weightedDivisorCoefficient χ s b := by
  simp only [weightedDivisorCoefficient, divisorCoefficient_mul χ hχ hab,
    Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
  ring

theorem weightedDivisorCoefficient_prime_pow (χ : DirichletCharacter ℂ m)
    (s : ℝ) (p e : ℕ) :
    weightedDivisorCoefficient χ s (p ^ e) =
      divisorCoefficient χ (p ^ e) * ((p : ℝ) ^ (-s)) ^ e := by
  unfold weightedDivisorCoefficient
  rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg p),
    mul_comm (e : ℝ), Real.rpow_mul_natCast (Nat.cast_nonneg p)]

theorem summable_norm_weightedDivisorCoefficient_prime_pow
    (χ : DirichletCharacter ℂ m) (hχ : MulChar.IsQuadratic χ)
    {s : ℝ} (hs : 0 < s) {p : ℕ} (hp : p.Prime) :
    Summable (fun e : ℕ => ‖weightedDivisorCoefficient χ s (p ^ e)‖) := by
  have hu0 : 0 ≤ (p : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hu1 : (p : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (neg_neg_of_pos hs)
  apply (summable_divisorCoefficient_prime_pow χ hχ hp hu0 hu1).congr
  intro e
  rw [Real.norm_eq_abs,
    abs_of_nonneg (weightedDivisorCoefficient_nonneg χ hχ s _),
    weightedDivisorCoefficient_prime_pow]

/-- Rankin's inequality with all local factors left explicit. -/
theorem sum_divisorCoefficient_le_finiteEulerProduct
    (χ : DirichletCharacter ℂ m) (hχ : MulChar.IsQuadratic χ)
    {s : ℝ} (hs : 0 < s) (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, divisorCoefficient χ n) ≤
      (X : ℝ) ^ s *
        ∏ p ∈ (X + 1).primesBelow,
          ∑' e : ℕ, divisorCoefficient χ (p ^ e) * ((p : ℝ) ^ (-s)) ^ e := by
  classical
  let f := weightedDivisorCoefficient χ s
  have hf0 (n : ℕ) : 0 ≤ f n := weightedDivisorCoefficient_nonneg χ hχ s n
  have hEuler := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (weightedDivisorCoefficient_one χ s)
    (fun {_ _} hab => weightedDivisorCoefficient_mul χ hχ s hab)
    (fun {_} hp => summable_norm_weightedDivisorCoefficient_prime_pow χ hχ hs hp)
    (X + 1)
  let terms : Finset (X + 1).smoothNumbers := (Finset.Icc 1 X).attach.map
    { toFun := fun n => ⟨n.1, Nat.mem_smoothNumbers_of_lt
        (Finset.mem_Icc.mp n.2).1 (Nat.lt_succ_of_le (Finset.mem_Icc.mp n.2).2)⟩
      inj' := by
        intro a b h
        exact Subtype.ext (congrArg (fun z : (X + 1).smoothNumbers => (z : ℕ)) h) }
  have hterms : (∑ z ∈ terms, f z) = ∑ n ∈ Finset.Icc 1 X, f n := by
    simp only [terms, Finset.sum_map]
    change (∑ z ∈ (Finset.Icc 1 X).attach, f z.1) = _
    exact Finset.sum_attach _ _
  have hsum : (∑ n ∈ Finset.Icc 1 X, f n) ≤
      ∏ p ∈ (X + 1).primesBelow, ∑' e : ℕ, f (p ^ e) := by
    rw [← hterms]
    exact (hEuler.2.summable.sum_le_tsum terms (fun n _ => hf0 n)).trans_eq
      hEuler.2.tsum_eq
  have hpoint (n : ℕ) (hn : n ∈ Finset.Icc 1 X) :
      divisorCoefficient χ n ≤ (X : ℝ) ^ s * f n := by
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hpow : (n : ℝ) ^ s ≤ (X : ℝ) ^ s :=
      Real.rpow_le_rpow hn0.le (by exact_mod_cast (Finset.mem_Icc.mp hn).2) hs.le
    calc
      divisorCoefficient χ n = (n : ℝ) ^ s * f n := by
        dsimp [f, weightedDivisorCoefficient]
        rw [mul_left_comm, ← Real.rpow_add hn0]
        simp
      _ ≤ (X : ℝ) ^ s * f n := mul_le_mul_of_nonneg_right hpow (hf0 n)
  calc
    (∑ n ∈ Finset.Icc 1 X, divisorCoefficient χ n) ≤
        ∑ n ∈ Finset.Icc 1 X, (X : ℝ) ^ s * f n :=
      Finset.sum_le_sum hpoint
    _ = (X : ℝ) ^ s * ∑ n ∈ Finset.Icc 1 X, f n := by rw [Finset.mul_sum]
    _ ≤ (X : ℝ) ^ s *
        ∏ p ∈ (X + 1).primesBelow, ∑' e : ℕ, f (p ^ e) :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := by simp only [f, weightedDivisorCoefficient_prime_pow]

end Pollack17
