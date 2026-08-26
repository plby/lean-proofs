/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos946.AffineSieve
import ErdosProblems.Erdos851.ConcreteBetaCardinality

/-!
# Finite Rosser bounds for a family of affine forms

This module connects the exact CRT remainder formula in `AffineSieve` to
the reusable finite combinatorial sieve.  The only estimate on a remainder
is the elementary inequality

`(# forms) ^ omega(d) <= product of the prime factors of d = d`,

valid because all sieving primes are larger than the number of forms.
The stopping parameter is left variable; this is needed by the weighted
dimension-eight sieve in Erdős 946.
-/

open scoped BigOperators

namespace Erdos946.AffineSieve

open Erdos851
open Erdos851.FiniteCombinatorialSieve
open Erdos851.FiniteSieveApplication
open List

noncomputable section

/-- Pre-sieving by `z!` preserves distinct affine roots at every prime
strictly above `z`. -/
theorem preSieved_localNu_eq_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι → ℕ} (hadm : Admissible a b) {z p : ℕ}
    (haPos : ∀ i, 0 < a i) (haLe : ∀ i, a i ≤ z)
    (hp : p.Prime) (hzp : z < p)
    (hdet : ∀ i j, i ≠ j →
      ¬a i * b j ≡ a j * b i [MOD p]) :
    localNu (preSievedSlope a z) (preSievedConstant a b hadm z) p =
      Fintype.card ι := by
  apply Erdos946.AffineSieve.localNu_eq_card hp
    (preSievedSlope_coprime_of_lt haPos haLe hp hzp)
  intro i j hij hcross
  have hfac : z.factorial.Coprime p := by
    apply Nat.Coprime.symm
    exact hp.coprime_iff_not_dvd.mpr fun hpd ↦
      (not_lt_of_ge (hp.dvd_factorial.mp hpd)) hzp
  have hscaled : z.factorial * (a i * b j) ≡
      z.factorial * (a j * b i) [MOD p] := by
    let r := preSieveResidue hadm z
    have hcross' :
        (a i * z.factorial) * (a j * r + b j) ≡
          (a j * z.factorial) * (a i * r + b i) [MOD p] := by
      simpa [preSievedSlope, preSievedConstant, r] using hcross
    apply Nat.ModEq.add_left_cancel' (z.factorial * (a i * a j * r))
    calc
      z.factorial * (a i * a j * r) + z.factorial * (a i * b j) =
          (a i * z.factorial) * (a j * r + b j) := by ring
      _ ≡ (a j * z.factorial) * (a i * r + b i) [MOD p] := hcross'
      _ = z.factorial * (a i * a j * r) + z.factorial * (a j * b i) := by ring
  exact hdet i j hij
    (Nat.ModEq.cancel_left_of_coprime hfac.symm.gcd_eq_one hscaled)

/-- If every prime divisor of a squarefree `d` is larger than the size of
the affine family, the exact number of CRT classes is at most `d`. -/
theorem nuClasses_le_self_of_large_primeFactors
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι → ℕ} {d z : ℕ} (hd : Squarefree d)
    (hlarge : ∀ p ∈ d.primeFactors, z < p)
    (hcard : Fintype.card ι ≤ z)
    (hcop : ∀ p ∈ d.primeFactors, ∀ i, (a i).Coprime p) :
    nuClasses a b d ≤ d := by
  calc
    nuClasses a b d ≤ (Fintype.card ι) ^ d.primeFactors.card :=
      nuClasses_le_card_pow_primeFactors hd hcop
    _ ≤ z ^ d.primeFactors.card :=
      Nat.pow_le_pow_left hcard d.primeFactors.card
    _ ≤ ∏ p ∈ d.primeFactors, p := by
      apply Finset.pow_card_le_prod
      intro p hp
      exact (hlarge p hp).le
    _ = d := Nat.prod_primeFactors_of_squarefree hd

/-- The Rosser lower and upper main terms bound the exact number of
survivors for an arbitrary finite affine family.  Both the Rosser beta
parameter and the level exponent are explicit. -/
theorem boundingSieve_cardinality_between_mainTerms
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {a b : ι → ℕ} {X z y beta S : ℕ}
    (hcard : Fintype.card ι ≤ z)
    (hz : 2 ≤ z) (hzy : z ≤ y) (hbeta : 1 ≤ beta) (hS : 1 ≤ S)
    (hcop : ∀ p : ℕ, p.Prime →
      p ∣ Erdos387.sievePrimeProduct z (y + 1) → ∀ i, (a i).Coprime p) :
    let P := Erdos851.ascendingSievePrimes z y
    let D := y ^ S
    let stop := rosserStoppingPredicate beta D
    (X : ℝ) * lowerMainTerm stop (fun p ↦ affineNu a b p) P -
          (D : ℝ) ^ 2 ≤
        ((siftedCandidates a b X z (y + 1)).card : ℝ) ∧
      ((siftedCandidates a b X z (y + 1)).card : ℝ) ≤
        (X : ℝ) * upperMainTerm stop (fun p ↦ affineNu a b p) P +
          (D : ℝ) ^ 2 := by
  classical
  dsimp only
  let P := Erdos851.ascendingSievePrimes z y
  let D := y ^ S
  let stop := rosserStoppingPredicate beta D
  let sieve := boundingSieve a b X z (y + 1) hcard hcop
  have hprod : P.prod = sieve.prodPrimes := by
    change P.prod = Erdos387.sievePrimeProduct z (y + 1)
    exact Erdos851.ascendingSievePrimes_prod z y
  have hsort : P.Pairwise (· ≤ ·) :=
    Erdos851.ascendingSievePrimes_pairwise z y
  have hnodup : P.Nodup := Erdos851.ascendingSievePrimes_nodup z y
  have hprime : ∀ p ∈ P, p.Prime :=
    Erdos851.ascendingSievePrimes_prime
  have hD : 1 ≤ D := by
    dsimp [D]
    exact one_le_pow₀ (by omega)
  have hlevel : ∀ p ∈ P, p ≤ D := by
    intro p hp
    have hpy : p ≤ y :=
      (Erdos851.mem_sievePrimes.mp
        (Erdos851.mem_ascendingSievePrimes.mp hp)).2.1
    exact hpy.trans (le_self_pow (by omega : 1 ≤ y) (by omega))
  have hrem : ∀ d : ℕ, d ∣ sieve.prodPrimes → d ≤ D →
      |sieve.rem d| ≤ (d : ℝ) := by
    intro d hd _hdD
    have hsq : Squarefree d :=
      Squarefree.squarefree_of_dvd hd sieve.prodPrimes_squarefree
    have hlarge : ∀ p ∈ d.primeFactors, z < p := by
      intro p hp
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpDivD : p ∣ d := Nat.dvd_of_mem_primeFactors hp
      have hd' : d ∣ Erdos387.sievePrimeProduct z (y + 1) := by
        change d ∣ sieve.prodPrimes
        exact hd
      have hpDivProd : p ∣ Erdos387.sievePrimeProduct z (y + 1) := by
        exact hpDivD.trans hd'
      exact (Erdos387.mem_sievePrimes.mp
        (Erdos387.prime_mem_sievePrimes_of_dvd_product hpPrime hpDivProd)).2.1
    have hcopD : ∀ p ∈ d.primeFactors, ∀ i, (a i).Coprime p := by
      intro p hp i
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpDivD : p ∣ d := Nat.dvd_of_mem_primeFactors hp
      have hd' : d ∣ Erdos387.sievePrimeProduct z (y + 1) := by
        change d ∣ sieve.prodPrimes
        exact hd
      have hpDivProd : p ∣ Erdos387.sievePrimeProduct z (y + 1) := by
        exact hpDivD.trans hd'
      exact hcop p hpPrime hpDivProd i
    exact (boundingSieve_abs_rem_le_nuClasses hd).trans
      (by exact_mod_cast
        nuClasses_le_self_of_large_primeFactors hsq hlarge hcard hcopD)
  have hlower := boundingSieve_lowerMain_sub_sq_le_siftedSum
    sieve P stop D hprod hsort hnodup hprime
    (by
      intro chain hchain hadm
      apply prod_le_of_lowerAdmissible_rosserStoppingPredicate
        hbeta hD
        (hsort.sublist (List.mem_sublists.mp hchain))
        (by
          intro p hp
          exact (hprime p
            ((List.mem_sublists.mp hchain).subset hp)).one_le)
        (by
          intro p hp
          exact hlevel p ((List.mem_sublists.mp hchain).subset hp)) hadm)
    hrem
  have hupper := boundingSieve_siftedSum_le_upperMain_add_sq
    sieve P stop D hprod hsort hnodup hprime
    (by
      intro chain hchain hadm
      apply prod_le_of_upperAdmissible_rosserStoppingPredicate
        hbeta hD
        (hsort.sublist (List.mem_sublists.mp hchain))
        (by
          intro p hp
          exact (hprime p
            ((List.mem_sublists.mp hchain).subset hp)).one_le)
        hadm)
    hrem
  change
    sieve.totalMass * lowerMainTerm stop (fun p ↦ sieve.nu p) P -
        (D : ℝ) ^ 2 ≤ _ at hlower
  change _ ≤
      sieve.totalMass * upperMainTerm stop (fun p ↦ sieve.nu p) P +
        (D : ℝ) ^ 2 at hupper
  rw [show sieve.totalMass = (X : ℝ) by exact boundingSieve_totalMass,
    show sieve.siftedSum =
        ((siftedCandidates a b X z (y + 1)).card : ℝ) by
      exact boundingSieve_siftedSum] at hlower hupper
  exact ⟨hlower, hupper⟩

end

end Erdos946.AffineSieve
