import ErdosProblems.Erdos144.PrimeBlocks

namespace Erdos144.PrimeBlockModel

open Erdos144.PrimeBlocks

/-- The subtype of primes belonging to logarithmic block `i`. -/
noncomputable abbrev blockPrime (K i : ℕ) : Type :=
  {p : ℕ // p ∈ logBlock K i}

/-- The family of prime subtypes over a finite set of block indices. -/
noncomputable abbrev κ (K : ℕ) (I : Finset ℕ) (i : ↑I) : Type := blockPrime K i.1

/-- A coordinate consists of a block index and a prime in that block. -/
noncomputable abbrev PrimeIndex (K : ℕ) (I : Finset ℕ) := Sigma (κ K I)

/-- Forget the block coordinate and retain its prime. -/
def primeValue {K : ℕ} {I : Finset ℕ} (z : PrimeIndex K I) : ℕ :=
  z.2.1

@[simp] lemma primeValue_mk {K : ℕ} {I : Finset ℕ} (i : ↑I) (p : κ K I i) :
    primeValue (Sigma.mk i p) = p.1 := rfl

theorem primeValue_injective {K : ℕ} {I : Finset ℕ} (hK : 0 < K) :
    Function.Injective (@primeValue K I) := by
  rintro ⟨i, p⟩ ⟨j, q⟩ hpq
  change p.1 = q.1 at hpq
  have hpj : p.1 ∈ logBlock K j.1 := by
    rw [hpq]
    exact q.2
  have hij : i.1 = j.1 :=
    eq_of_mem_logBlock_of_mem_logBlock hK p.2 hpj
  have hij' : i = j := Subtype.ext hij
  subst j
  have hpq' : p = q := Subtype.ext hpq
  subst q
  rfl

theorem primeValue_prime {K : ℕ} {I : Finset ℕ} (z : PrimeIndex K I) :
    Nat.Prime (primeValue z) := by
  rcases z with ⟨i, p⟩
  exact (Finset.mem_filter.mp p.2).2

theorem primeValue_ne_zero {K : ℕ} {I : Finset ℕ} (z : PrimeIndex K I) :
    primeValue z ≠ 0 :=
  (primeValue_prime z).ne_zero

instance primeValue_neZero {K : ℕ} {I : Finset ℕ} (z : PrimeIndex K I) :
    NeZero (primeValue z) :=
  ⟨primeValue_ne_zero z⟩

theorem primeValue_pairwise_coprime {K : ℕ} {I : Finset ℕ} (hK : 0 < K) :
    Pairwise (Function.onFun Nat.Coprime (@primeValue K I)) := by
  intro x y hxy
  have hx := primeValue_prime x
  have hy := primeValue_prime y
  exact hx.coprime_iff_not_dvd.mpr fun hd ↦
    hxy (primeValue_injective hK ((Nat.prime_dvd_prime_iff_eq hx hy).mp hd))

end Erdos144.PrimeBlockModel
