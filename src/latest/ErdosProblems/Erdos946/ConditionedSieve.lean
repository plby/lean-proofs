/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos946.EightAffineCardinality

/-!
# Conditioning the affine sieve on one additional prime

The larger prime is not among the small sieving primes.  Dividing its
indicator weight by sixteen leaves the same local densities and the same
`d` bound on the normalized remainder.
-/

open scoped BigOperators

namespace Erdos946.AffineSieve

open Erdos851 Erdos851.FiniteCombinatorialSieve Erdos851.FiniteSieveApplication

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem nuClasses_mul_of_coprime (a b : ι → ℕ) {m n : ℕ}
    (h : m.Coprime n) :
    nuClasses a b (m * n) = nuClasses a b m * nuClasses a b n := by
  unfold nuClasses
  rw [h.primeFactors_mul, Finset.prod_union h.disjoint_primeFactors]

theorem nuClasses_prime_mul (a b : ι → ℕ) {p d : ℕ}
    (hp : p.Prime) (hpd : p.Coprime d) :
    nuClasses a b (p * d) = localNu a b p * nuClasses a b d := by
  rw [nuClasses_mul_of_coprime a b hpd]
  simp [nuClasses, hp.primeFactors]

/-- The dyadic residue estimate is valid for any squarefree modulus, not
only a divisor of one particular small-prime product. -/
theorem abs_card_divisibleCandidates_sub_density_of_squarefree
    {a b : ι → ℕ} {X d : ℕ} (hd : Squarefree d) :
    |((divisibleCandidates a b X d).card : ℝ) -
        (nuClasses a b d : ℝ) * X / d| ≤ nuClasses a b d := by
  have heq : divisibleCandidates a b X d =
      Erdos387.modularPreimageIoc X (2 * X) d (assignmentResidues a b d) := by
    ext n
    simp only [divisibleCandidates, Erdos387.modularPreimageIoc,
      Finset.mem_filter, Finset.mem_Ioc]
    exact and_congr_right fun _ ↦ squarefree_dvd_affineProduct_iff_mod_mem hd
  rw [heq, ← card_assignmentResidues a b d]
  exact Erdos851.ShiftSieve.abs_card_modularPreimageIoc_dyadic_sub_density
    (Nat.pos_of_ne_zero hd.ne_zero) _ (fun _ hr ↦ assignmentResidues_lt hd hr)

private theorem sum_fiber_counts_filter (I : Finset ℕ) (f : ℕ → ℕ)
    (P : ℕ → Prop) [DecidablePred P] :
    (∑ q ∈ I.image f,
      if P q then ((I.filter fun n ↦ f n = q).card : ℝ) else 0) =
      ((I.filter fun n ↦ P (f n)).card : ℝ) := by
  classical
  rw [← Finset.sum_filter]
  have hcount :
      (∑ q ∈ (I.image f).filter P, (I.filter fun n ↦ f n = q).card) =
        (I.filter fun n ↦ P (f n)).card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_image]
    aesop
  rw [← Nat.cast_sum, hcount]

variable [Nonempty ι]

/-- Sieve with the large-prime divisibility indicator scaled by `1/16`. -/
def conditionedBoundingSieve (a b : ι → ℕ) (X z Y p : ℕ)
    (hz : Fintype.card ι ≤ z)
    (hcop : ∀ q : ℕ, q.Prime →
      q ∣ Erdos387.sievePrimeProduct z Y → ∀ i, (a i).Coprime q) :
    BoundingSieve :=
  { boundingSieve a b X z Y hz hcop with
    weights := fun q ↦ if p ∣ q then
      (boundingSieve a b X z Y hz hcop).weights q / 16 else 0
    weights_nonneg := by
      intro q
      split
      · exact div_nonneg (BoundingSieve.weights_nonneg _ _) (by norm_num)
      · exact le_rfl
    totalMass := (X : ℝ) / p }

def conditionedCandidates (a b : ι → ℕ) (X z Y p : ℕ) : Finset ℕ :=
  (siftedCandidates a b X z Y).filter fun n ↦ p ∣ affineProduct a b n

theorem conditionedBoundingSieve_multSum
    {a b : ι → ℕ} {X z Y p d : ℕ} {hz : Fintype.card ι ≤ z}
    {hcop : ∀ q : ℕ, q.Prime →
      q ∣ Erdos387.sievePrimeProduct z Y → ∀ i, (a i).Coprime q}
    (hpd : p.Coprime d) :
    (conditionedBoundingSieve a b X z Y p hz hcop).multSum d =
      ((divisibleCandidates a b X (p * d)).card : ℝ) / 16 := by
  let s := boundingSieve a b X z Y hz hcop
  have heq : (conditionedBoundingSieve a b X z Y p hz hcop).multSum d =
      s.multSum (p * d) / 16 := by
    change (∑ q ∈ s.support,
      if d ∣ q then (if p ∣ q then s.weights q / 16 else 0) else 0) = _
    rw [BoundingSieve.multSum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro q _
    have hiff : p * d ∣ q ↔ p ∣ q ∧ d ∣ q :=
      ⟨fun h ↦ ⟨dvd_trans (dvd_mul_right _ _) h,
        dvd_trans (dvd_mul_left _ _) h⟩,
       fun h ↦ hpd.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
    by_cases hdq : d ∣ q <;> by_cases hpq : p ∣ q <;> simp [hiff, hdq, hpq]
  rw [heq]
  congr 1
  exact boundingSieve_multSum

theorem conditionedBoundingSieve_siftedSum
    {a b : ι → ℕ} {X z Y p : ℕ} {hz : Fintype.card ι ≤ z}
    {hcop : ∀ q : ℕ, q.Prime →
      q ∣ Erdos387.sievePrimeProduct z Y → ∀ i, (a i).Coprime q} :
    (conditionedBoundingSieve a b X z Y p hz hcop).siftedSum =
      ((conditionedCandidates a b X z Y p).card : ℝ) / 16 := by
  classical
  let I := Finset.Ioc X (2 * X)
  let f := affineProduct a b
  let P := fun q ↦ (Erdos387.sievePrimeProduct z Y).Coprime q ∧ p ∣ q
  have hterm (q : ℕ) :
      (if (Erdos387.sievePrimeProduct z Y).Coprime q then
        (if p ∣ q then ((I.filter fun n ↦ f n = q).card : ℝ) / 16 else 0)
       else 0) =
      (if P q then ((I.filter fun n ↦ f n = q).card : ℝ) else 0) / 16 := by
    dsimp [P]
    split <;> split <;> simp_all
  change (∑ q ∈ I.image f,
    if (Erdos387.sievePrimeProduct z Y).Coprime q then
      (if p ∣ q then ((I.filter fun n ↦ f n = q).card : ℝ) / 16 else 0)
    else 0) = _
  simp_rw [hterm]
  rw [← Finset.sum_div, sum_fiber_counts_filter]
  have hsets : I.filter (fun n ↦ P (f n)) =
      conditionedCandidates a b X z Y p := by
    ext n
    simp [I, f, P, conditionedCandidates, siftedCandidates, and_assoc]
  rw [hsets]

theorem conditionedBoundingSieve_abs_rem_le_nuClasses
    {a b : ι → ℕ} {X z Y p d : ℕ} {hz : Fintype.card ι ≤ z}
    {hcop : ∀ q : ℕ, q.Prime →
      q ∣ Erdos387.sievePrimeProduct z Y → ∀ i, (a i).Coprime q}
    (hp : p.Prime) (hpd : p.Coprime d) (hd : Squarefree d)
    (hlocal : localNu a b p = 16) :
    |(conditionedBoundingSieve a b X z Y p hz hcop).rem d| ≤
      (nuClasses a b d : ℝ) := by
  have hsq : Squarefree (p * d) := (Nat.squarefree_mul hpd).2 ⟨hp.squarefree, hd⟩
  have hcount := abs_card_divisibleCandidates_sub_density_of_squarefree
    (a := a) (b := b) (X := X) hsq
  rw [nuClasses_prime_mul a b hp hpd, hlocal, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_mul] at hcount
  rw [BoundingSieve.rem, conditionedBoundingSieve_multSum hpd]
  change |((divisibleCandidates a b X (p * d)).card : ℝ) / 16 -
      affineNu a b d * ((X : ℝ) / p)| ≤ _
  rw [affineNu_squarefree hd]
  have heq :
      ((divisibleCandidates a b X (p * d)).card : ℝ) / 16 -
        (nuClasses a b d : ℝ) / d * ((X : ℝ) / p) =
      (((divisibleCandidates a b X (p * d)).card : ℝ) -
        16 * (nuClasses a b d : ℝ) * X / ((p : ℝ) * d)) / 16 := by
    ring
  rw [heq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 16)]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 16)).2 (by nlinarith [hcount])

theorem prime_coprime_sievePrimeProduct_of_gt {p z y : ℕ}
    (hp : p.Prime) (hyp : y < p) :
    p.Coprime (Erdos387.sievePrimeProduct z (y + 1)) := by
  apply hp.coprime_iff_not_dvd.mpr
  intro hdiv
  have hmem := Erdos387.prime_mem_sievePrimes_of_dvd_product hp hdiv
  have hpy := (Erdos387.mem_sievePrimes.mp hmem).2.2
  omega

theorem nuClasses_le_self_of_dvd_sievePrimeProduct
    {a b : ι → ℕ} {z Y d : ℕ}
    (hcard : Fintype.card ι ≤ z)
    (hcop : ∀ q : ℕ, q.Prime →
      q ∣ Erdos387.sievePrimeProduct z Y → ∀ i, (a i).Coprime q)
    (hd : d ∣ Erdos387.sievePrimeProduct z Y) :
    nuClasses a b d ≤ d := by
  have hsq := Squarefree.squarefree_of_dvd hd
    (Erdos387.sievePrimeProduct_squarefree z Y)
  refine nuClasses_le_self_of_large_primeFactors hsq ?_ hcard ?_
  · intro q hq
    have hqPrime := Nat.prime_of_mem_primeFactors hq
    have hqDiv := (Nat.dvd_of_mem_primeFactors hq).trans hd
    exact (Erdos387.mem_sievePrimes.mp
      (Erdos387.prime_mem_sievePrimes_of_dvd_product hqPrime hqDiv)).2.1
  · intro q hq i
    exact hcop q (Nat.prime_of_mem_primeFactors hq)
      ((Nat.dvd_of_mem_primeFactors hq).trans hd) i

/-- The finite upper sieve after conditioning on a prime larger than every
sieving prime.  The factor sixteen multiplies both the main term and the
square-level error. -/
theorem conditionedCandidates_card_le_upperMainTerm
    {a b : ι → ℕ} {X z y p beta S : ℕ}
    (hcard : Fintype.card ι ≤ z) (hz : 2 ≤ z) (hzy : z ≤ y)
    (hbeta : 1 ≤ beta) (hp : p.Prime) (hyp : y < p)
    (hlocal : localNu a b p = 16)
    (hcop : ∀ q : ℕ, q.Prime →
      q ∣ Erdos387.sievePrimeProduct z (y + 1) → ∀ i, (a i).Coprime q) :
    let P := Erdos851.ascendingSievePrimes z y
    let D := y ^ S
    ((conditionedCandidates a b X z (y + 1) p).card : ℝ) ≤
      16 * (((X : ℝ) / p) *
        upperMainTerm (rosserStoppingPredicate beta D) (fun q ↦ affineNu a b q) P +
        (D : ℝ) ^ 2) := by
  classical
  dsimp only
  let P := Erdos851.ascendingSievePrimes z y
  let D := y ^ S
  let stop := rosserStoppingPredicate beta D
  let sieve := conditionedBoundingSieve a b X z (y + 1) p hcard hcop
  have hprod : P.prod = sieve.prodPrimes :=
    Erdos851.ascendingSievePrimes_prod z y
  have hsort : P.Pairwise (· ≤ ·) := Erdos851.ascendingSievePrimes_pairwise z y
  have hnodup : P.Nodup := Erdos851.ascendingSievePrimes_nodup z y
  have hprime : ∀ q ∈ P, q.Prime := Erdos851.ascendingSievePrimes_prime
  have hD : 1 ≤ D := one_le_pow₀ (by omega : 1 ≤ y)
  have hpCop := prime_coprime_sievePrimeProduct_of_gt (z := z) hp hyp
  have hrem : ∀ d : ℕ, d ∣ sieve.prodPrimes → d ≤ D →
      |sieve.rem d| ≤ (d : ℝ) := by
    intro d hd _
    have hd' : d ∣ Erdos387.sievePrimeProduct z (y + 1) := hd
    have hsq := Squarefree.squarefree_of_dvd hd sieve.prodPrimes_squarefree
    exact (conditionedBoundingSieve_abs_rem_le_nuClasses hp
      (hpCop.of_dvd_right hd') hsq hlocal).trans
        (by exact_mod_cast nuClasses_le_self_of_dvd_sievePrimeProduct hcard hcop hd')
  have hupper := boundingSieve_siftedSum_le_upperMain_add_sq
    sieve P stop D hprod hsort hnodup hprime
    (by
      intro chain hchain hadm
      apply prod_le_of_upperAdmissible_rosserStoppingPredicate hbeta hD
        (hsort.sublist (List.mem_sublists.mp hchain))
        (by
          intro q hq
          exact (hprime q ((List.mem_sublists.mp hchain).subset hq)).one_le)
        hadm)
    hrem
  change ((conditionedBoundingSieve a b X z (y + 1) p hcard hcop).siftedSum) ≤
    ((X : ℝ) / p) * upperMainTerm stop (fun q ↦ affineNu a b q) P + (D : ℝ) ^ 2
    at hupper
  rw [conditionedBoundingSieve_siftedSum] at hupper
  nlinarith

end

end Erdos946.AffineSieve
