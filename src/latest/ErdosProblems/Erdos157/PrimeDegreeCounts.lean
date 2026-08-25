import ErdosProblems.Erdos157.PrimePowerEstimate

/-! Finite degree classes and a coarse count of proper prime powers. -/

namespace Erdos157.Elementary.PolynomialCharacters

open Polynomial

variable (K : Type*) [Field K] [DecidableEq K]

abbrev PrimeDegree (n : ℕ) := {p : MonicDegreeEq K n // Irreducible p.1}

noncomputable instance primeDegreeFintype [Fintype K] (n : ℕ) : Fintype (PrimeDegree K n) :=
  Fintype.ofFinite _

def primeDegreeToPrime {n : ℕ} (p : PrimeDegree K n) : PrimePolynomial K :=
  ⟨p.1.1, p.1.monic, p.2⟩

theorem primeDegreeToPrime_injective (n : ℕ) : Function.Injective (primeDegreeToPrime K (n := n)) := by
  intro p q h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun p : PrimePolynomial K => p.1) h

theorem primeDegreeToPrime_natDegree {n : ℕ} (p : PrimeDegree K n) :
    (primeDegreeToPrime K p).1.natDegree = n := p.1.natDegree

theorem card_primeDegree_le [Fintype K] (n : ℕ) :
    Fintype.card (PrimeDegree K n) ≤ Fintype.card K ^ n := by
  exact (Fintype.card_subtype_le (fun p : MonicDegreeEq K n => Irreducible p.1)).trans_eq
    (card_monic n)

abbrev PrimesAtMost (N : ℕ) := Σ d : Fin (N + 1), PrimeDegree K d.1

theorem card_primesAtMost_le [Fintype K] (N : ℕ) :
    Fintype.card (PrimesAtMost K N) ≤ (N + 1) * Fintype.card K ^ N := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _d : Fin (N + 1), Fintype.card K ^ N := by
      apply Finset.sum_le_sum
      intro d _
      exact (card_primeDegree_le K d.1).trans
        (Nat.pow_le_pow_right (Fintype.card_pos (α := K)) (by omega))
    _ = _ := by simp

def primeToBounded (N : ℕ) (p : PrimePolynomial K) (hp : p.1.natDegree ≤ N) : PrimesAtMost K N :=
  ⟨⟨p.1.natDegree, by omega⟩, ⟨MonicDegreeEq.mk p.1 p.2.1 rfl, p.2.2⟩⟩

theorem primeToBounded_injective (N : ℕ) :
    Function.Injective (fun p : {p : PrimePolynomial K // p.1.natDegree ≤ N} =>
      primeToBounded K N p.1 p.2) := by
  intro p q h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun p : PrimesAtMost K N => p.2.1.1) h

variable {K}

abbrev PrimePowerFiber (n : ℕ) := {i : PrimePolynomial K × ℕ // primePowerDegree i = n}
abbrev ProperPrimePowerFiber (n : ℕ) := {i : PrimePowerFiber (K := K) n // 0 < i.1.2}

theorem primePowerFiber_degree_le {n : ℕ} (i : PrimePowerFiber (K := K) n) :
    i.1.1.1.natDegree ≤ n := by
  have h := Nat.mul_le_mul_left i.1.1.1.natDegree (by omega : 1 ≤ i.1.2 + 1)
  simpa only [Nat.mul_one, ← i.2, primePowerDegree] using h

theorem properPrimePowerFiber_degree_le {n : ℕ} (i : ProperPrimePowerFiber (K := K) n) :
    i.1.1.1.1.natDegree ≤ n / 2 := by
  have h := Nat.mul_le_mul_left i.1.1.1.1.natDegree (by have := i.2; omega : 2 ≤ i.1.1.2 + 1)
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
  simpa only [← i.1.2, primePowerDegree] using h

/-- Once the prime and total degree are fixed, the exponent is unique. -/
theorem primePowerFiber_prime_injective (n : ℕ) :
    Function.Injective (fun i : PrimePowerFiber (K := K) n => i.1.1) := by
  intro i j hij
  change i.1.1 = j.1.1 at hij
  apply Subtype.ext
  apply Prod.ext hij
  have hi : i.1.1.1.natDegree * (i.1.2 + 1) = n := i.2
  have hj : j.1.1.1.natDegree * (j.1.2 + 1) = n := j.2
  have hdegree := congrArg (fun p : PrimePolynomial K => p.1.natDegree) hij
  rw [hdegree] at hi
  have hd : j.1.1.1.natDegree ≠ 0 := ne_of_gt (primePolynomial_degree_pos j.1.1)
  have heq := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd) (hi.trans hj.symm)
  omega

noncomputable instance primePowerFiberFintype [Fintype K] (n : ℕ) :
    Fintype (PrimePowerFiber (K := K) n) := by
  let f : PrimePowerFiber (K := K) n → PrimesAtMost K n :=
    fun i => primeToBounded K n i.1.1 (primePowerFiber_degree_le i)
  have hf : Function.Injective f := by
    intro i j h
    apply primePowerFiber_prime_injective n
    apply Subtype.ext
    exact congrArg (fun p : PrimesAtMost K n => p.2.1.1) h
  let : Finite (PrimePowerFiber (K := K) n) := Finite.of_injective f hf
  exact Fintype.ofFinite _

noncomputable instance properPrimePowerFiberFintype [Fintype K] (n : ℕ) :
    Fintype (ProperPrimePowerFiber (K := K) n) := Fintype.ofFinite _

theorem card_properPrimePowerFiber_le [Fintype K] (n : ℕ) :
    Fintype.card (ProperPrimePowerFiber (K := K) n) ≤
      (n / 2 + 1) * Fintype.card K ^ (n / 2) := by
  let f : ProperPrimePowerFiber (K := K) n → PrimesAtMost K (n / 2) :=
    fun i => primeToBounded K (n / 2) i.1.1.1 (properPrimePowerFiber_degree_le i)
  have hf : Function.Injective f := by
    intro i j h
    apply Subtype.ext
    apply primePowerFiber_prime_injective n
    apply Subtype.ext
    exact congrArg (fun p : PrimesAtMost K (n / 2) => p.2.1.1) h
  exact (Fintype.card_le_of_injective f hf).trans (card_primesAtMost_le K (n / 2))

end Erdos157.Elementary.PolynomialCharacters
