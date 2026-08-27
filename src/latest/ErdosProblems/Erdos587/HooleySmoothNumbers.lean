import ErdosProblems.Erdos587.HooleyRestrictions

/-!
# Finite squarefree smooth numbers

The harmonic moment argument ranges over all squarefree products of
primes below a cutoff, with no restriction on the product itself.
We realize this finite set as the divisors of the prime product.
-/

open scoped BigOperators

namespace Erdos587

def deltaPrimeProduct (x : ℕ) : ℕ := ∏ p ∈ x.primesBelow, p

lemma deltaPrimeProduct_squarefree (x : ℕ) : Squarefree (deltaPrimeProduct x) := by
  unfold deltaPrimeProduct
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    (fun p hp => (Nat.mem_primesBelow.mp hp).2.squarefree)
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (Nat.mem_primesBelow.mp hp).2
    (Nat.mem_primesBelow.mp hq).2).mpr hpq

lemma primeFactors_deltaPrimeProduct (x : ℕ) :
    (deltaPrimeProduct x).primeFactors = x.primesBelow :=
  Nat.primeFactors_prod (fun _ hp => (Nat.mem_primesBelow.mp hp).2)

def deltaSmoothNumbers (x : ℕ) : Finset ℕ := (deltaPrimeProduct x).divisors

lemma mem_deltaSmoothNumbers {n x : ℕ} :
    n ∈ deltaSmoothNumbers x ↔ Squarefree n ∧ n.primeFactors ⊆ x.primesBelow := by
  constructor
  · intro hn
    have hdiv := (Nat.mem_divisors.mp hn).1
    refine ⟨(deltaPrimeProduct_squarefree x).squarefree_of_dvd hdiv, ?_⟩
    have hmono := Nat.primeFactors_mono hdiv (deltaPrimeProduct_squarefree x).ne_zero
    simpa only [primeFactors_deltaPrimeProduct] using hmono
  · rintro ⟨hn, hsub⟩
    apply Nat.mem_divisors.mpr
    refine ⟨?_, (deltaPrimeProduct_squarefree x).ne_zero⟩
    rw [← Nat.prod_primeFactors_of_squarefree hn]
    exact Finset.prod_dvd_prod_of_subset _ _ _ hsub

lemma mem_deltaSmoothNumbers_iff {n x : ℕ} :
    n ∈ deltaSmoothNumbers x ↔ Squarefree n ∧ ∀ p ∈ n.primeFactors, p < x := by
  rw [mem_deltaSmoothNumbers]
  constructor
  · rintro ⟨hn, hsub⟩
    exact ⟨hn, fun p hp => (Nat.mem_primesBelow.mp (hsub hp)).1⟩
  · rintro ⟨hn, hlt⟩
    exact ⟨hn, fun p hp => Nat.mem_primesBelow.mpr ⟨hlt p hp, Nat.prime_of_mem_primeFactors hp⟩⟩

@[simp] lemma one_mem_deltaSmoothNumbers (x : ℕ) : 1 ∈ deltaSmoothNumbers x := by
  rw [mem_deltaSmoothNumbers]
  simp

lemma deltaSmoothNumbers_mono : Monotone deltaSmoothNumbers := by
  intro x y hxy n hn
  obtain ⟨hn, hlt⟩ := mem_deltaSmoothNumbers_iff.mp hn
  exact mem_deltaSmoothNumbers_iff.mpr ⟨hn, fun p hp => (hlt p hp).trans_le hxy⟩

lemma deltaSmoothNumbers_of_dvd {m n x : ℕ} (hn : n ∈ deltaSmoothNumbers x)
    (hmn : m ∣ n) : m ∈ deltaSmoothNumbers x := by
  apply Nat.mem_divisors.mpr
  obtain ⟨hndiv, hnzero⟩ := Nat.mem_divisors.mp hn
  exact ⟨hmn.trans hndiv, hnzero⟩

/-- Extract the largest prime factor; its cofactor is smooth below that
prime, so the recursion strictly decreases its prime cutoff. -/
theorem deltaSmoothNumbers_largest_prime {n x : ℕ}
    (hn : n ∈ deltaSmoothNumbers x) (hn1 : n ≠ 1) :
    ∃ p ∈ x.primesBelow, ∃ m ∈ deltaSmoothNumbers p, n = p * m := by
  obtain ⟨hsf, hsub⟩ := mem_deltaSmoothNumbers.mp hn
  have hnonempty : n.primeFactors.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro h
    exact (Nat.primeFactors_eq_empty.mp h).elim hsf.ne_zero hn1
  let p := n.primeFactors.max' hnonempty
  have hpMem : p ∈ n.primeFactors := Finset.max'_mem _ _
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpMem
  have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hpMem
  let m := n / p
  have hnm : n = p * m := (Nat.mul_div_cancel' hpn).symm
  have hsf' : Squarefree (p * m) := hnm ▸ hsf
  have hcop : p.Coprime m := Nat.coprime_of_squarefree_mul hsf'
  have hnotdvd : ¬ p ∣ m := hp.coprime_iff_not_dvd.mp hcop
  have hmn : m ∣ n := hnm ▸ dvd_mul_left m p
  have hm : m ∈ deltaSmoothNumbers p := by
    apply mem_deltaSmoothNumbers_iff.mpr
    refine ⟨hsf'.of_mul_right, ?_⟩
    intro q hq
    have hqMem : q ∈ n.primeFactors := Nat.primeFactors_mono hmn hsf.ne_zero hq
    have hqle : q ≤ p := Finset.le_max' _ q hqMem
    have hqne : q ≠ p := by
      intro hqp
      exact hnotdvd (hqp ▸ Nat.dvd_of_mem_primeFactors hq)
    exact lt_of_le_of_ne hqle hqne
  exact ⟨p, hsub hpMem, m, hm, hnm⟩

lemma prime_not_dvd_of_mem_deltaSmoothNumbers {p m : ℕ} (hp : p.Prime)
    (hm : m ∈ deltaSmoothNumbers p) : ¬ p ∣ m := by
  obtain ⟨hsf, hlt⟩ := mem_deltaSmoothNumbers_iff.mp hm
  intro hpm
  have hpMem : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpm, hsf.ne_zero⟩
  exact (lt_irrefl p) (hlt p hpMem)

/-- The largest-prime decomposition remains an upper bound after imposing
any restriction preserved under squarefree divisibility. -/
theorem sum_deltaSmoothNumbers_filter_le_prime_decomposition (x : ℕ)
    (G : ℕ → Prop) [DecidablePred G] (hG1 : G 1)
    (hGdiv : ∀ {m n : ℕ}, Squarefree n → m ∣ n → G n → G m)
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    (∑ n ∈ (deltaSmoothNumbers x).filter G, f n) ≤
      f 1 + ∑ p ∈ x.primesBelow, ∑ m ∈ (deltaSmoothNumbers p).filter G, f (p * m) := by
  classical
  let R := (deltaSmoothNumbers x).filter G
  let D : Finset (Σ _p : ℕ, ℕ) :=
    x.primesBelow.sigma (fun p => (deltaSmoothNumbers p).filter G)
  let prod : (Σ _p : ℕ, ℕ) → ℕ := fun z => z.1 * z.2
  have hR1 : 1 ∈ R := Finset.mem_filter.mpr ⟨one_mem_deltaSmoothNumbers x, hG1⟩
  have hcover : R.erase 1 ⊆ D.image prod := by
    intro n hn
    obtain ⟨hn1, hnR⟩ := Finset.mem_erase.mp hn
    obtain ⟨hnS, hnG⟩ := Finset.mem_filter.mp hnR
    obtain ⟨p, hp, m, hm, hnm⟩ := deltaSmoothNumbers_largest_prime hnS hn1
    have hmG : G m := hGdiv (mem_deltaSmoothNumbers.mp hnS).1
      (hnm ▸ dvd_mul_left m p) hnG
    apply Finset.mem_image.mpr
    exact ⟨⟨p, m⟩, Finset.mem_sigma.mpr ⟨hp, Finset.mem_filter.mpr ⟨hm, hmG⟩⟩, hnm.symm⟩
  have hsum : (∑ n ∈ R.erase 1, f n) ≤ ∑ z ∈ D, f (prod z) := by
    calc
      _ ≤ ∑ n ∈ D.image prod, f n :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover (fun n _ _ => hf n)
      _ ≤ _ := Finset.sum_image_le_of_nonneg (fun n _ => hf n)
  change (∑ n ∈ R, f n) ≤ _
  calc
    (∑ n ∈ R, f n) = f 1 + ∑ n ∈ R.erase 1, f n := by
      rw [← Finset.sum_erase_add R f hR1]
      ring
    _ ≤ f 1 + ∑ z ∈ D, f (prod z) := add_le_add le_rfl hsum
    _ = _ := by
      dsimp only [D, prod]
      rw [Finset.sum_sigma]

end Erdos587
